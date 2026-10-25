import ConAgua.Checker.Prog
import ConAgua.Compiler.Run
import ConAgua.Compiler.Abi

/-!
# Lane `leafgen`: an unproved prototype of a better back end (mostly for leaf functions)

`lake env lean --run scripts/leafgen/LGEmit.lean OUT.s FLAGS` prints the checker's code as
`ConAgua/Checker/AsmEmit.lean` does, compiled by the prototype below. `FLAGS` is a comma-separated
subset of
* `gen`: expressions evaluated straight into a target register, temporaries in a register stack
  (the scratch registers `rax rcx rdx` plus the argument registers that hold no local), operands
  used in place (memory, immediate, `lea`), constant indices folded into the address;
* `cmp`: conditions compare operands in place (`cmp mem, imm`, `cmp reg, mem`, swapped for a
  constant left operand);
* `stk`: leaves skip their stack check; every caller checks for its own frame plus the largest
  frame of the leaves it calls;
* `base`: the base of an array (its descriptor word) is remembered in a register within a
  straight-line run.
-/

namespace L.Compiler.LG

open L L.Compiler

structure Flags where
  gen : Bool := false
  cmp : Bool := false
  stk : Bool := false
  base : Bool := false
  /-- leaves may keep locals in `rbx r12 r13` too (the trampoline saves them; unproved) -/
  regs : Bool := false
  /-- zero only the locals that may be read before they are assigned (compopt2's E2; unproved) -/
  zero : Bool := false

/-! ## The register stack -/

/-- The scratch registers of a function: `rax rcx rdx`, then the argument registers that hold no
local (and not `rsi` when it holds the tier). -/
def pool (ctx : Ctx) (regs : Bool := false) : List Reg64 :=
  [.rax, .rcx, .rdx] ++ ((([Reg64.r11, .r10, .r9, .r8, .rdi, .rsi] ++ if regs then [Reg64.rbx, .r12, .r13] else []).filter fun r =>
     !(ctx.alloc.any (·.2 == r)) && !(r == Reg64.rsi && ctx.treg.isSome)))

def mR (r : Reg64) : RegOrMem .W64 := .reg (rr r)

/-- `[b + s·i + d]` -/
def mbid (b i : Reg64) (s : Width) (d : Int) : AddrExpr := ⟨some (.reg b), some ⟨i, s⟩, .int64 (Int64.ofInt d)⟩

/-- `d := d op o`, where x64 has the two-operand form. -/
def aluOp : BinOp → RegOrMem .W64 → Operand .W64 → Option Directive
  | .add, d, o => some (i64 (.add d o))
  | .sub, d, o => some (i64 (.sub d o))
  | .and, d, o => some (i64 (.and d o))
  | .or, d, o => some (i64 (.or d o))
  | .xor, d, o => some (i64 (.xor d o))
  | .mul, .reg d, o => some (i64 (.imul none (.reg d) o))
  | _, _, _ => none

def isComm : BinOp → Bool
  | .add | .mul | .and | .or | .xor => true
  | _ => false

def isPow2 (k : Word) : Bool := k.toNat != 0 && k.toNat == 2 ^ Nat.log2 k.toNat

/-- The simple operand of `e` (a local, a global, a length, an imm32 constant). -/
def opn (ctx : Ctx) (e : Expr) : Option (Operand .W64) := simpleOp ctx e

/-- Subexpressions already in a register. -/
abbrev Kn := List (Expr × Reg64)

def opnK (ctx : Ctx) (kn : Kn) (e : Expr) : Option (Operand .W64) :=
  match kn.lookup e with
  | some r => some (oR r)
  | none => simpleOp ctx e

/-- The register of `e` if it is a local kept in one. -/
def regOf (ctx : Ctx) : Expr → Option Reg64
  | .var x => ctx.alloc.lookup x
  | _ => none

def regOfK (ctx : Ctx) (kn : Kn) (e : Expr) : Option Reg64 :=
  match kn.lookup e with
  | some r => some r
  | none => regOf ctx e

def smallK (k : Word) : Bool := k.toNat < 2 ^ 28

/-- An array descriptor: the length and base addresses of word array `a` (plain, or tiered by `rsi`
or a tier register). -/
structure Desc where
  ln : AddrExpr
  bs : AddrExpr

/-- The condition code for `cmp b, a` that is true iff `a op b`. -/
def swapCC : Cmp → CondCode
  | .eq => .z | .ne => .nz | .ult => .a | .ule => .nc | .slt => .g | .sle => .ge

mutual
/-- Code that evaluates `e` into `d`, using the registers `fr` (not `d`) as scratch. -/
partial def gen (ctx : Ctx) (kn : Kn) (e : Expr) (d : Reg64) (fr : List Reg64) : Option Program :=
  match kn.lookup e with
  | some r => some (if r == d then [] else [movRR d r])
  | none => gen0 ctx kn e d fr

/-- `gen` without the lookup of known subexpressions. -/
partial def gen0 (ctx : Ctx) (kn : Kn) : Expr → Reg64 → List Reg64 → Option Program
  | .const w, d, _ => some [movRI d w]
  | .var x, d, _ =>
    match ctx.alloc.lookup x with
    | some r => some (if r == d then [] else [movRR d r])
    | none => some [movRM d (mb .rsp (8 * x))]
  | .glob g, d, _ => some [movRM d (mb .r15 (ctx.tab.globOff g))]
  | .len8 a, d, _ => some [movRM d (mb .r15 (ctx.tab.len8 a))]
  | .len64 a, d, _ => some [movRM d (mb .r15 (ctx.tab.len64 a))]
  | .bin op a0 b0, d, fr =>
    let (a, b) := match a0, b0 with
      | .const _, .const _ => (a0, b0)
      | .const _, _ => if isComm op then (b0, a0) else (a0, b0)
      | _, _ => (a0, b0)
    match op, b with
    | .shl, .const k => (gen ctx kn a d fr).map (· ++ [i64 (.shl (mR d) (.imm8 (.int64 (Int64.ofInt (k.toNat % 64)))))])
    | .shr, .const k => (gen ctx kn a d fr).map (· ++ [i64 (.shr (mR d) (.imm8 (.int64 (Int64.ofInt (k.toNat % 64)))))])
    | .mul, .const k =>
      if isPow2 k then (gen ctx kn a d fr).map (· ++ [i64 (.shl (mR d) (.imm8 (.int64 (Int64.ofInt (Nat.log2 k.toNat)))))])
      else if fitsImm32 k then (gen ctx kn a d fr).map (· ++ [i64 (.imul none (mR d) (.imm (.int64 k.toInt64)))])
      else match fr with
        | t :: fr' => do
          let ca ← gen ctx kn a d fr
          some (ca ++ [movRI t k, i64 (.imul none (mR d) (oR t))])
        | [] => none
    | .mulhi, _ =>
      -- `rdx:rax := rax * src`
      if d == .rax && fr.contains .rdx then do
        let ca ← gen ctx kn a .rax fr
        match opnK ctx kn b with
        | some (.regOrMem m) => some (ca ++ [i64 (.mul m), movRR .rax .rdx])
        | _ =>
          match fr.filter (· != .rdx) with
          | t :: _ => do
            let cb ← gen ctx kn b t (fr.filter (· != t))
            some (ca ++ cb ++ [i64 (.mul (mR t)), movRR .rax .rdx])
          | [] => none
      else if fr.contains .rax && fr.contains .rdx then do
        let fr1 := fr.filter (· != .rax)
        let ca ← gen ctx kn a .rax fr1
        match opnK ctx kn b with
        | some (.regOrMem m) => some (ca ++ [i64 (.mul m), movRR d .rdx])
        | _ =>
          let t := d
          let cb ← gen ctx kn b t (fr1.filter (· != .rdx) ++ [.rdx])
          some (ca ++ cb ++ [i64 (.mul (mR t)), movRR d .rdx])
      else none
    | .shl, _ | .shr, _ =>
      if d != .rcx && fr.contains .rcx then do
        let ca ← gen ctx kn a d fr
        let cb ← gen ctx kn b .rcx (fr.filter (· != .rcx))
        some (ca ++ cb ++ [i64 (if op == .shl then .shl (mR d) .cl else .shr (mR d) .cl)])
      else none
    | _, _ =>
      -- lea forms
      let lea : Option Program :=
        match op, regOfK ctx kn a, b with
        | .add, some r, .const k =>
          if fitsImm32 k then some [i64 (.lea (rr d) (mb r k.toInt64.toInt))] else none
        | .sub, some r, .const k =>
          if fitsImm32 k && k.toNat != 2 ^ 63 then some [i64 (.lea (rr d) (mb r (-k.toInt64.toInt)))] else none
        | .add, some r, .var y => (ctx.alloc.lookup y).map fun s => [i64 (.lea (rr d) (mbid r s .W8 0))]
        | _, _, _ => none
      match lea with
      | some code => some code
      | none =>
      match opnK ctx kn b with
      | some ob => do
        let ca ← gen ctx kn a d fr
        let i ← aluOp op (mR d) ob
        some (ca ++ [i])
      | none =>
        match opnK ctx kn a with
        | some oa =>
          if isComm op then do
            let cb ← gen ctx kn b d fr
            let i ← aluOp op (mR d) oa
            some (cb ++ [i])
          else
            match fr with
            | t :: fr' => do
              let cb ← gen ctx kn b t (d :: fr')
              let ca ← gen ctx kn a d fr'
              let i ← aluOp op (mR d) (oR t)
              some (cb ++ ca ++ [i])
            | [] => none
        | none =>
          match fr with
          | t :: fr' => do
            let ca ← gen ctx kn a d fr
            let cb ← gen ctx kn b t fr'
            let i ← aluOp op (mR d) (oR t)
            some (ca ++ cb ++ [i])
          | [] => none
  | .ld64 a i, d, fr =>
    genLd ctx kn ⟨mb .r15 (ctx.tab.len64 a), mb .r15 (ctx.tab.base64 a)⟩ [] i d fr false
  | .ld8 a i, d, fr =>
    genLd ctx kn ⟨mb .r15 (ctx.tab.len8 a), mb .r15 (ctx.tab.base8 a)⟩ [] i d fr true
  | .ld64t a t i, d, fr =>
    if ctx.isT t then
      genLd ctx kn ⟨tdesc .rsi (ctx.tab.len64 a), tdesc .rsi (ctx.tab.base64 a)⟩ [] i d fr false
    else
      match fr with
      | s :: fr' => do
        let ct ← gen ctx kn t s fr'
        genLd ctx kn ⟨tdesc s (ctx.tab.len64 a), tdesc s (ctx.tab.base64 a)⟩ (ct ++ tierDesc s) i d fr' false
          |>.map fun c => c
      | [] => none
  | .len64t a t, d, fr =>
    if ctx.isT t then some [movRM d (tdesc .rsi (ctx.tab.len64 a))]
    else do
      let ct ← gen ctx kn t d fr
      some (ct ++ tierDesc d ++ [movRM d (tdesc d (ctx.tab.len64 a))])
  | .ldc dd i, d, fr =>
    match i with
    | .const k =>
      if k.toNat < dd.length then some [movRI d (dd.getD k.toNat 0).toUInt64] else some [jmpL errorL]
    | _ =>
      match fr with
      | t :: fr' => do
        let ci ← gen ctx kn i d fr
        some (ci ++ [i64 (.cmp (mR d) (oI dd.length)), jccL .nc errorL,
          i64 (.lea (rr t) (mb .r15 (ctx.tab.romBase + romIdx dd ctx.tab.rom))),
          i64 (.movzx (.reg (rr d)) (w' := .W8) (.mem (mbi t d .W8)))])
      | [] => none
  | .cmpw op a b, d, fr => do
    let (cc, code) ← genCmp ctx kn op a b (fr.filter (· != d) ++ [d])
    some (code ++ [i8 (.setcc cc (.reg (.low d .W8))), i64 (.movzx (.reg (rr d)) (w' := .W8) (.reg (.low d .W8)))])
  | _, _, _ => none
where
  /-- A load `A[i]` through descriptor `ds`, after `pre` (which sets up the descriptor's tier
  register, not in `fr`); bytes if `byte`. -/
  genLd (ctx : Ctx) (kn : Kn) (ds : Desc) (pre : Program) (i : Expr) (d : Reg64) (fr : List Reg64) (byte : Bool) :
      Option Program :=
    let ld (b : Reg64) (ix : Option Reg64) (off : Int) : Directive :=
      match ix with
      | some x => if byte then i64 (.movzx (.reg (rr d)) (w' := .W8) (.mem (mbid b x .W8 off)))
                  else movRM d (mbid b x .W64 (8 * off))
      | none => if byte then i64 (.movzx (.reg (rr d)) (w' := .W8) (.mem (mb b off)))
                else movRM d (mb b (8 * off))
    match i with
    | .const k =>
      if smallK k then
        some (pre ++ [i64 (.cmp (.mem ds.ln) (oI k.toNat)), jccL .be errorL, movRM d ds.bs,
          ld d none k.toNat])
      else none
    | _ =>
      match regOfK ctx kn i with
      | some r => some (pre ++ [i64 (.cmp (mR r) (.regOrMem (.mem ds.ln))), jccL .nc errorL, movRM d ds.bs, ld d (some r) 0])
      | none => do
        let ci ← gen ctx kn i d fr
        match fr with
        | t :: _ => some (pre ++ ci ++ [i64 (.cmp (mR d) (.regOrMem (.mem ds.ln))), jccL .nc errorL, movRM t ds.bs, ld t (some d) 0])
        | [] => none
  -- genCmp: flags for `a op b`, and the condition code under which it holds.
  -- genAddr: the address of word `A[i]` after its bounds check, using registers of `fr`.
  genAddr (ctx : Ctx) (kn : Kn) (ds : Desc) (i : Expr) (fr : List Reg64) : Option (Program × AddrExpr) :=
    match i, fr with
    | .const k, t :: _ =>
      if smallK k then some ([i64 (.cmp (.mem ds.ln) (oI k.toNat)), jccL .be errorL, movRM t ds.bs], mb t (8 * k.toNat))
      else none
    | _, t :: fr' =>
      match regOfK ctx kn i with
      | some r => some ([i64 (.cmp (mR r) (.regOrMem (.mem ds.ln))), jccL .nc errorL, movRM t ds.bs], mbid t r .W64 0)
      | none =>
        match fr' with
        | x :: fr'' => (gen ctx kn i x (t :: fr'')).map fun ci =>
            (ci ++ [i64 (.cmp (mR x) (.regOrMem (.mem ds.ln))), jccL .nc errorL, movRM t ds.bs], mbid t x .W64 0)
        | [] => none
    | _, [] => none
  ldOpnd (ctx : Ctx) (kn : Kn) (e : Expr) (fr : List Reg64) : Option (Program × AddrExpr) :=
    match kn.lookup e, e with
    | none, .ld64 a i => genAddr ctx kn ⟨mb .r15 (ctx.tab.len64 a), mb .r15 (ctx.tab.base64 a)⟩ i fr
    | none, .ld64t a t i =>
      if ctx.isT t then genAddr ctx kn ⟨tdesc .rsi (ctx.tab.len64 a), tdesc .rsi (ctx.tab.base64 a)⟩ i fr else none
    | _, _ => none
  genCmp (ctx : Ctx) (kn : Kn) (op : Cmp) (a b : Expr) (fr : List Reg64) : Option (CondCode × Program) :=
    let viaMem : Option (CondCode × Program) :=
      match opnK ctx kn b, opnK ctx kn a with
      | some (.imm k), _ => (ldOpnd ctx kn a fr).map fun (c, m) => (cmpCC op, c ++ [i64 (.cmp (.mem m) (.imm k))])
      | some (.regOrMem (.reg r)), _ => (ldOpnd ctx kn a fr).map fun (c, m) => (cmpCC op, c ++ [i64 (.cmp (.mem m) (oR' r))])
      | _, some (.imm k) => (ldOpnd ctx kn b fr).map fun (c, m) => (swapCC op, c ++ [i64 (.cmp (.mem m) (.imm k))])
      | _, some (.regOrMem (.reg r)) => (ldOpnd ctx kn b fr).map fun (c, m) => (swapCC op, c ++ [i64 (.cmp (.mem m) (oR' r))])
      | _, _ => none
    match viaMem with
    | some r => some r
    | none =>
    match opnK ctx kn a, opnK ctx kn b with
    | some (.regOrMem (.reg ra)), some ob => some (cmpCC op, [i64 (.cmp (.reg ra) ob)])
    | some (.regOrMem (.mem ma)), some (.imm k) => some (cmpCC op, [i64 (.cmp (.mem ma) (.imm k))])
    | some (.regOrMem (.mem ma)), some (.regOrMem (.reg rb)) => some (cmpCC op, [i64 (.cmp (.mem ma) (oR' rb))])
    | some (.imm k), some (.regOrMem m) => some (swapCC op, [i64 (.cmp m (.imm k))])
    | _, some ob =>
      match fr with
      | t :: fr' => (gen ctx kn a t fr').map fun ca => (cmpCC op, ca ++ [i64 (.cmp (mR t) ob)])
      | [] => none
    | some (.regOrMem m), none =>
      match fr with
      | t :: fr' => (gen ctx kn b t fr').map fun cb => (swapCC op, cb ++ [i64 (.cmp (mR t) (.regOrMem m))])
      | [] => none
    | some (.imm k), none =>
      match fr with
      | t :: fr' => (gen ctx kn b t fr').map fun cb => (swapCC op, cb ++ [i64 (.cmp (mR t) (.imm k))])
      | [] => none
    | none, none =>
      match fr with
      | t :: u :: fr' => do
        let ca ← gen ctx kn a t (u :: fr')
        let cb ← gen ctx kn b u fr'
        some (cmpCC op, ca ++ cb ++ [i64 (.cmp (mR t) (oR u))])
      | _ => none
  oR' (r : Reg .W64) : Operand .W64 := .regOrMem (.reg r)

end

/-! ## Common subexpressions (within one expression or condition) -/

def Expr.subs : Expr → List Expr
  | .bin op a b => .bin op a b :: (Expr.subs a ++ Expr.subs b)
  | .cmpw op a b => .cmpw op a b :: (Expr.subs a ++ Expr.subs b)
  | .ld8 x i => .ld8 x i :: Expr.subs i
  | .ld64 x i => .ld64 x i :: Expr.subs i
  | .ldc x i => .ldc x i :: Expr.subs i
  | .ld8x8 x i => .ld8x8 x i :: Expr.subs i
  | .ld64t x t i => .ld64t x t i :: (Expr.subs t ++ Expr.subs i)
  | .len64t x t => .len64t x t :: Expr.subs t
  | _ => []

/-- The first (largest) subexpression that needs code and occurs twice. -/
def cseCand (es : List Expr) : Option Expr :=
  let all := es.flatMap Expr.subs
  all.find? fun s => (all.filter (· == s)).length ≥ 2

/-- Evaluate a repeated subexpression once into a register of `fr`, then `k`. -/
def withCSE (ctx : Ctx) (es : List Expr) (fr : List Reg64) (k : Kn → List Reg64 → Option Program) :
    Option Program :=
  match cseCand es, (fr.filter fun r => r != .rax && r != .rdx).reverse ++ fr.reverse with
  | some s, t :: _ =>
    let fr' := fr.filter (· != t)
    match gen ctx [] s t fr', k [(s, t)] fr' with
    | some cs, some rest => some (cs ++ rest)
    | _, _ => k [] fr
  | _, _ => k [] fr

def genK (ctx : Ctx) (e : Expr) (d : Reg64) (fr : List Reg64) : Option Program :=
  withCSE ctx [e] (fr.filter (· != d)) fun kn fr => gen ctx kn e d fr

/-! ## Statements -/

/-- The context of the prototype: the old one plus the flags and the scratch registers. -/
structure C where
  ctx : Ctx
  fl : Flags

def C.pool (c : C) : List Reg64 := L.Compiler.LG.pool c.ctx c.fl.regs

/-- `rax := e` through the register stack, else the old way. -/
def genTop (c : C) (e : Expr) (d : Reg64) (fr : List Reg64) : Option Program :=
  if c.fl.gen then genK c.ctx e d fr else none

/-- Jump to `l` if `c` evaluates to `pol`. -/
def compileC2 (c : C) (path : Path) : Cond → Bool → Label → Program
  | .cmp op a b, pol, l =>
    let fallback := compileC c.ctx path (.cmp op a b) pol l 0
    if c.fl.cmp || c.fl.gen then
      let r := withCSE c.ctx [a, b] c.pool fun kn fr =>
        (gen0.genCmp c.ctx kn op a b fr).map fun (cc, code) => code ++ [jccL (if pol then cc else CondCode.neg cc) l]
      let _ := r
      match (if c.fl.gen then r.map (fun code => (CondCode.z, code)) else none) with
      | some (_, code) => code
      | none =>
      match gen0.genCmp c.ctx [] op a b c.pool with
      | some (cc, code) =>
        if c.fl.gen || code.length ≤ 1 then code ++ [jccL (if pol then cc else CondCode.neg cc) l] else fallback
      | none => fallback
    else fallback
  | .and p q, false, l => compileC2 c (path.ch 7) p false l ++ compileC2 c (path.ch 8) q false l
  | .and p q, true, l =>
    compileC2 c (path.ch 7) p false (c.ctx.lbl path "S") ++ compileC2 c (path.ch 8) q true l ++
      [.label (c.ctx.lbl path "S")]
  | .or p q, true, l => compileC2 c (path.ch 7) p true l ++ compileC2 c (path.ch 8) q true l
  | .or p q, false, l =>
    compileC2 c (path.ch 7) p true (c.ctx.lbl path "S") ++ compileC2 c (path.ch 8) q false l ++
      [.label (c.ctx.lbl path "S")]
  | .not p, pol, l => compileC2 c (path.ch 9) p (!pol) l

/-- `r := e` (old `valInto`), or through the register stack with scratch `fr`. -/
def valInto2 (c : C) (r : Reg64) (fr : List Reg64) (e : Expr) : Program :=
  if Expr.readsReg c.ctx.alloc r e then
    match loadInto c.ctx r e with
    | some code => code
    | none =>
      match genTop c e .rax (fr.filter (· != .rax)) with
      | some code => if fr.contains .rax then code ++ [movRR r .rax] else valInto c.ctx r e
      | none => valInto c.ctx r e
  else
  match genTop c e r (fr.filter (· != r)) with
  | some code => code
  | none => valInto c.ctx r e

def retRegs2 (c : C) (fr : List Reg64) : Nat → List Expr → Program
  | _, [] => []
  | i, e :: es => valInto2 c (resReg i) fr e ++ retRegs2 c (fr.filter (· != resReg i)) (i + 1) es

def retDirect2 (c : C) (es : List Expr) (n : Nat) : Option Program :=
  if retOk c.ctx.alloc es n then
    match es with
    | [] => some (zeroRes 0 n)
    | e0 :: rest =>
      let fr := (c.pool.filter fun r => !(List.range rest.length).any fun j => resReg (j + 1) == r)
      some (retRegs2 c c.pool 1 rest ++
        valInto2Rax c fr e0 ++ zeroRes es.length (n - es.length))
  else none
where
  valInto2Rax (c : C) (fr : List Reg64) (e : Expr) : Program :=
    match genTop c e .rax (fr.filter (· != .rax)) with
    | some code => code
    | none => compileE c.ctx e 0

def compileRegArgs2 (c : C) (fr : List Reg64) : List Reg64 → List Expr → Program
  | r :: rs, e :: es => valInto2 c r fr e ++ compileRegArgs2 c (fr.filter (· != r)) rs es
  | _, _ => []

def tailCode2 (c : C) : Stmt → Stmt → Option Program
  | .call xs f args, .ret es =>
    let ctx := c.ctx
    match ctx.tailF with
    | some F =>
      if retVars es xs && nodupB xs && xs.length == ctx.nr && decide (ctx.nr ≤ nrOf ctx.nrt ctx.tab f) &&
          decide (args.length ≤ argRegs.length) then
        some (compileRegArgs2 c c.pool argRegs args ++ burnFuel ++
          [i64 (.add (.reg (rr .rsp)) (oI (8 * F))), jmpL (fnL f)])
      else none
    | none => none
  | _, _ => none

/-- The store `A[i] := e` through descriptor `ds`. -/
def genSt (c : C) (ds : Desc) (pre : Program) (i e : Expr) (fr : List Reg64) (byte : Bool) : Option Program := do
  -- the value: an operand, or a register
  let (cv, src, fr) ← match e with
    | .const k =>
      if (byte && true) || fitsImm32 k then some ([], Sum.inl k, fr) else
      match fr with
      | v :: fr' => some ([movRI v k], Sum.inr v, fr')
      | [] => none
    | _ =>
      match regOf c.ctx e with
      | some r => some ([], Sum.inr r, fr)
      | none =>
        match fr with
        | v :: fr' => (gen c.ctx [] e v fr').map fun cv => (cv, Sum.inr v, fr')
        | [] => none
  let st (a : AddrExpr) : Directive :=
    match src, byte with
    | .inl k, false => i64 (.mov (.mem a) (.imm (.int64 k.toInt64)))
    | .inl k, true => i8 (.mov (.mem a) (.imm (.int64 (Int64.ofInt (k.toNat % 256)))))
    | .inr r, false => movMR a r
    | .inr r, true => i8 (.mov (.mem a) (.regOrMem (.reg (.low r .W8))))
  let scale := if byte then Width.W8 else .W64
  let mul : Int := if byte then 1 else 8
  match i with
  | .const k =>
    if smallK k then
      match fr with
      | t :: _ => some (cv ++ pre ++ [i64 (.cmp (.mem ds.ln) (oI k.toNat)), jccL .be errorL, movRM t ds.bs, st (mb t (mul * k.toNat))])
      | [] => none
    else none
  | _ =>
    match regOf c.ctx i with
    | some r =>
      match fr with
      | t :: _ => some (cv ++ pre ++ [i64 (.cmp (mR r) (.regOrMem (.mem ds.ln))), jccL .nc errorL, movRM t ds.bs, st (mbid t r scale 0)])
      | [] => none
    | none =>
      match fr with
      | d :: t :: fr' => do
        let ci ← gen c.ctx [] i d (t :: fr')
        some (cv ++ pre ++ ci ++ [i64 (.cmp (mR d) (.regOrMem (.mem ds.ln))), jccL .nc errorL, movRM t ds.bs, st (mbid t d scale 0)])
      | _ => none

/-- `x := e`, through the register stack. -/
def genSet (c : C) (x : Var) (e : Expr) : Option Program :=
  let ctx := c.ctx
  let dst : RegOrMem .W64 := match ctx.alloc.lookup x with
    | some r => .reg (rr r)
    | none => .mem (mb .rsp (8 * x))
  -- `x := x op b` in place
  let inPlace : Option Program :=
    match e with
    | .bin op (.var y) b =>
      if y != x then none else
      match op, b with
      | .shl, .const k => some [i64 (.shl dst (.imm8 (.int64 (Int64.ofInt (k.toNat % 64)))))]
      | .shr, .const k => some [i64 (.shr dst (.imm8 (.int64 (Int64.ofInt (k.toNat % 64)))))]
      | .mulhi, _ | .shl, _ | .shr, _ => none
      | .mul, _ => none
      | _, _ =>
        match opn ctx b with
        | some (.imm k) => (aluOp op dst (.imm k)).map ([·])
        | some (.regOrMem (.reg r)) => (aluOp op dst (oR' r)).map ([·])
        | some (.regOrMem (.mem m)) =>
          match dst with
          | .reg _ => (aluOp op dst (.regOrMem (.mem m))).map ([·])
          | .mem _ => none
        | none =>
          match c.pool with
          | t :: fr => do
            let cb ← genK ctx b t fr
            let i ← aluOp op dst (oR t)
            some (cb ++ [i])
          | [] => none
    | _ => none
  match inPlace with
  | some code => some code
  | none =>
    match ctx.alloc.lookup x with
    | some r =>
      if Expr.readsReg ctx.alloc r e then
        (genK ctx e .rax (c.pool.filter (· != .rax))).map (· ++ [movRR r .rax])
      else genK ctx e r c.pool
    | none =>
      match opn ctx e with
      | some (.imm k) => some [i64 (.mov (.mem (mb .rsp (8 * x))) (.imm k))]
      | _ => (genK ctx e .rax (c.pool.filter (· != .rax))).map (· ++ [movMR (mb .rsp (8 * x)) .rax])
where oR' (r : Reg .W64) : Operand .W64 := .regOrMem (.reg r)

def compileS2 (c : C) (path : Path) : Stmt → Program
  | .skip => []
  | .set x e =>
    let old := compileS c.ctx path (.set x e)
    if c.ctx.treg == some x || !c.fl.gen then old else (genSet c x e).getD old
  | .st8 a i e =>
    let old := compileS c.ctx path (.st8 a i e)
    if !c.fl.gen then old else
    (genSt c ⟨mb .r15 (c.ctx.tab.len8 a), mb .r15 (c.ctx.tab.base8 a)⟩ [] i e c.pool true).getD old
  | .st64 a i e =>
    let old := compileS c.ctx path (.st64 a i e)
    if !c.fl.gen then old else
    (genSt c ⟨mb .r15 (c.ctx.tab.len64 a), mb .r15 (c.ctx.tab.base64 a)⟩ [] i e c.pool false).getD old
  | .st64t a t i e =>
    let old := compileS c.ctx path (.st64t a t i e)
    if !c.fl.gen then old else
    if c.ctx.isT t then
      (genSt c ⟨tdesc .rsi (c.ctx.tab.len64 a), tdesc .rsi (c.ctx.tab.base64 a)⟩ [] i e c.pool false).getD old
    else
      match c.pool.reverse with
      | s :: _ =>
        let fr := c.pool.filter (· != s)
        (do let ct ← gen c.ctx [] t s []
            genSt c ⟨tdesc s (c.ctx.tab.len64 a), tdesc s (c.ctx.tab.base64 a)⟩ (ct ++ tierDesc s) i e fr false).getD old
      | [] => old
  | .seq s t =>
    match tailCode2 c s t with
    | some code => code
    | none => compileS2 c (path.ch 1) s ++ compileS2 c (path.ch 2) t
  | .ite cd .abort .skip => compileC2 c (path.ch 3) cd true errorL
  | .ite cd s t =>
    compileC2 c (path.ch 3) cd false (c.ctx.lbl path "E") ++ compileS2 c (path.ch 4) s ++
      [jmpL (c.ctx.lbl path "X"), .label (c.ctx.lbl path "E")] ++ compileS2 c (path.ch 5) t ++
      [.label (c.ctx.lbl path "X")]
  | .while cd s =>
    [.label (c.ctx.lbl path "H")] ++ compileC2 c (path.ch 3) cd false (c.ctx.lbl path "X") ++
      compileS2 { c with ctx := { c.ctx with brk := c.ctx.lbl path "X" } } (path.ch 6) s ++ burnFuel ++
      [jmpL (c.ctx.lbl path "H"), .label (c.ctx.lbl path "X")]
  | .ret es =>
    let ctx := c.ctx
    match (if c.fl.gen then retDirect2 c es ctx.nr else retDirect ctx es ctx.nr) with
    | some code => code ++ [jmpL ctx.retL]
    | none => compileArgs ctx 0 es ++ loadRes ctx es.length 0 ctx.nr ++ [jmpL ctx.retL]
  | .call xs f args =>
    let ctx := c.ctx
    (if args.length ≤ argRegs.length then
       (if c.fl.gen then compileRegArgs2 c c.pool argRegs args else compileRegArgs ctx argRegs args)
     else compileArgs ctx 0 args ++ [i64 (.lea (rr .rsi) (ctx.tmp 0))]) ++ burnFuel ++
      [i64 (.call (.rel (.sub (.label (fnL f)) .after_current_instruction)))] ++
      storeRes ctx.tab (xs.take (nrOf ctx.nrt ctx.tab f)) 0 ++ zeroVars (xs.drop (nrOf ctx.nrt ctx.tab f))
  | .gset g e =>
    let old := compileS c.ctx path (.gset g e)
    if !c.fl.gen then old else
    match opn c.ctx e with
    | some (.imm k) => [i64 (.mov (.mem (mb .r15 (c.ctx.tab.globOff g))) (.imm k))]
    | _ => match genK c.ctx e .rax (c.pool.filter (· != .rax)) with
      | some code => code ++ [movMR (mb .r15 (c.ctx.tab.globOff g)) .rax]
      | none => old
  | s => compileS c.ctx path s

/-! ## Base registers (flag `base`): a peephole over straight-line runs

Within a run of code between labels/jumps, `movq D(%r15...), %t` of an array base whose register
`t` has not been written since the same load is dropped (the descriptor table never changes);
`t` must be a scratch register. Applied to the generated code; unsound in general only if the
code writes the table, which compiled L code never does except globals/results (not bases). -/

def writesReg (d : Directive) (r : Reg64) : Bool :=
  match d with
  | .instr (.regular _ _ op) =>
    let w : Reg64 → Bool := fun x => x == r
    match op with
    | .mov (.reg (.low x _)) _ | .movzx (.reg (.low x _)) _ | .movsx (.reg (.low x _)) _ => w x
    | .lea (.low x _) _ | .add (.reg (.low x _)) _ | .sub (.reg (.low x _)) _ | .and (.reg (.low x _)) _
    | .or (.reg (.low x _)) _ | .xor (.reg (.low x _)) _ | .shl (.reg (.low x _)) _ | .shr (.reg (.low x _)) _
    | .imul none (.reg (.low x _)) _ | .setcc _ (.reg (.low x _)) | .cmovcc _ (.low x _) _ => w x
    | .mul _ => r == .rax || r == .rdx
    | .call _ | .ret | .jmp _ | .jcc _ _ => true
    | .pop _ | .push _ => true
    | .cmp _ _ | .test _ _ => false
    | .mov (.mem _) _ => false
    | _ => true
  | _ => true

def isBaseLoad (tab : Tab) : Directive → Option (Reg64 × AddrExpr)
  | .instr (.regular .W64 .W64 (.mov (.reg (.low t .W64)) (.regOrMem (.mem a)))) =>
    match a with
    | ⟨some (.reg .r15), _, .int64 d⟩ =>
      let d := d.toInt
      let wb := 16 + 16 * (tab.nb : Int)
      let isBase := (16 ≤ d && d < wb && (d / 8) % 2 == 0) || (wb ≤ d && d < wb + 8 * tab.nw)
      if isBase then some (t, a) else none
    | _ => none
  | _ => none

/-- `known`: register ↦ the base address it holds. -/
def basePeep (tab : Tab) (scratch : List Reg64) : Program → List (Reg64 × AddrExpr) → Program
  | [], _ => []
  | d :: ds, known =>
    match d with
    | .label _ => d :: basePeep tab scratch ds []
    | _ =>
      match isBaseLoad tab d with
      | some (t, a) =>
        if scratch.contains t && known.any (fun (r, b) => r == t && b == a) then basePeep tab scratch ds known
        else
          -- a register used as index of this address must not change: the tier register; drop
          -- knowledge of anything written
          let known := known.filter fun (r, b) => r != t && !(b.idx.any (·.reg == t))
          d :: basePeep tab scratch ds (if scratch.contains t && !(a.idx.any (·.reg == t)) then (t, a) :: known else known)
      | none =>
        match d with
        | .instr (.regular _ _ (.jcc _ l)) =>
          -- a jump to the error exits keeps the run going (they never come back)
          if l == errorL || l == exhaustedL then d :: basePeep tab scratch ds known
          else d :: basePeep tab scratch ds []
        | _ =>
          let known := known.filter fun (r, b) => !writesReg d r && !(b.idx.any fun ix => writesReg d ix.reg)
          d :: basePeep tab scratch ds known

/-! ## Functions -/

def dispOf (a : AddrExpr) : Int := match a.disp with | .int64 d => d.toInt | _ => 0
def rspSlot (a : AddrExpr) : List Int := if a.base == some (.reg .rsp) && a.idx.isNone then [dispOf a] else []

/-- The words of frame temporaries the code uses (old fallback paths: `rsp + 8 (nl + t)`). -/
def tempsUsed (nl : Nat) (code : Program) : Nat :=
  code.foldl (fun acc d =>
    let offs : List Int := match d with
      | .instr (.regular _ _ op) =>
        match op with
        | .mov (.mem a) _ | .mov _ (.regOrMem (.mem a)) | .cmp (.mem a) _ | .cmp _ (.regOrMem (.mem a))
        | .lea _ a => rspSlot a
        | .add _ (.regOrMem (.mem a)) | .sub _ (.regOrMem (.mem a)) | .and _ (.regOrMem (.mem a))
        | .or _ (.regOrMem (.mem a)) | .xor _ (.regOrMem (.mem a)) | .imul _ _ (.regOrMem (.mem a))
        | .add (.mem a) _ | .sub (.mem a) _ | .and (.mem a) _ | .or (.mem a) _ | .xor (.mem a) _
        | .shl (.mem a) _ | .shr (.mem a) _ | .mul (.mem a) =>
          rspSlot a
        | _ => []
      | _ => []
    offs.foldl (fun acc (o : Int) => if o ≥ 8 * (nl : Int) then max acc (Int.toNat (o / 8) + 1 - nl) else acc) acc) 0

structure FnInfo where
  F : Nat
  leaf : Bool
  framed : Bool

def Expr.vs : Expr → List Var
  | .var x => [x]
  | .bin _ a b | .cmpw _ a b => Expr.vs a ++ Expr.vs b
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .ld8x8 _ i => Expr.vs i
  | .ld64t _ t i => Expr.vs t ++ Expr.vs i
  | .len64t _ t => Expr.vs t
  | _ => []

def WArr.vs : WArr → List Var
  | .plain _ => []
  | .tier _ t => Expr.vs t

def Cond.vs : Cond → List Var
  | .cmp _ a b => Expr.vs a ++ Expr.vs b
  | .and p q | .or p q => Cond.vs p ++ Cond.vs q
  | .not p => Cond.vs p

/-- Definite assignment: from the defined locals `D` (`none`: unreachable), the locals read before
they are defined (accumulated in `R`) and the defined locals after the statement. -/
def da : Stmt → Option (List Var) → List Var → Option (List Var) × List Var
  | _, none, R => (none, R)
  | s, some D, R =>
    let rd (vs : List Var) (R : List Var) : List Var := R ++ vs.filter (!D.contains ·)
    match s with
    | .skip => (some D, R)
    | .set x e => (some (x :: D), rd (Expr.vs e) R)
    | .st8 _ i e | .st64 _ i e => (some D, rd (Expr.vs i ++ Expr.vs e) R)
    | .st64t _ t i e => (some D, rd (Expr.vs t ++ Expr.vs i ++ Expr.vs e) R)
    | .gset _ e => (some D, rd (Expr.vs e) R)
    | .seq a b => let (D1, R1) := da a (some D) R; da b D1 R1
    | .ite c a b =>
      let R0 := rd (Cond.vs c) R
      let (D1, R1) := da a (some D) R0
      let (D2, R2) := da b (some D) R1
      (match D1, D2 with
       | none, d => d
       | d, none => d
       | some x, some y => some (x.filter y.contains), R2)
    | .while c a =>
      let R0 := rd (Cond.vs c) R
      let (_, R1) := da a (some D) R0
      (some D, R1)
    | .brk | .abort => (none, R)
    | .ret es => (none, rd (es.flatMap Expr.vs) R)
    | .call xs _ args => (some (xs ++ D), rd (args.flatMap Expr.vs) R)
    | .copy64 d di s si n => (some D, rd (WArr.vs d ++ Expr.vs di ++ WArr.vs s ++ Expr.vs si ++ Expr.vs n) R)
    | .copy8w d di _ si n => (some D, rd (WArr.vs d ++ Expr.vs di ++ Expr.vs si ++ Expr.vs n) R)
    | .scan8 x _ i e _ => (some (x :: D), rd (Expr.vs i ++ Expr.vs e) R)

/-- Zero the locals from `j` on that `need` lists. -/
def zeroLocals2 (ctx : Ctx) (need : List Var) : Nat → Nat → Program
  | _, 0 => []
  | j, n + 1 =>
    (if need.contains j then
      [match ctx.alloc.lookup j with
       | some r => movRI r 0
       | none => i64 (.mov (.mem (mb .rsp (8 * j))) (oI 0))] else []) ++ zeroLocals2 ctx need (j + 1) n

def body (fl : Flags) (ctx : Ctx) (fd : FunDecl) : Program :=
  let c : C := { ctx, fl }
  (if fd.nparams ≤ argRegs.length then storeParams ctx 0 (argRegs.take fd.nparams)
   else copyParams 0 fd.nparams) ++
  (if fl.zero then zeroLocals2 ctx (da fd.body (some (List.range fd.nparams)) []).2 fd.nparams (fd.nlocals - fd.nparams)
   else zeroLocals ctx fd.nparams (fd.nlocals - fd.nparams)) ++
  compileS2 c 0 fd.body ++ [.label ctx.endL] ++ loadRes ctx 0 0 ctx.nr ++ [.label ctx.retL]

def allocRegs2 : List Reg64 := allocRegs ++ [.rbx, .r12, .r13]

/-- `leafAlloc` with `rbx r12 r13` as well. -/
def leafAlloc2 (fd : FunDecl) : List (Var × Reg64) :=
  if Stmt.calls fd.body || argRegs.length < fd.nparams then [] else
  let u := Stmt.uses 1 (Array.replicate fd.nlocals 0) fd.body
  let u := (List.range fd.nparams).foldl (fun a i => a.modify i (· + 1)) u
  let ranked := rankInsSort u ((List.range fd.nlocals).filter (fun x => u[x]! > 0))
  let chosen := (ranked.filter fun y => tregOf fd != some y).take allocRegs2.length
  let ps := (chosen.filter (· < fd.nparams)).map fun i => (i, argRegs.getD i .rdi)
  let free := [Reg64.r13, .r12, .rbx, .rsi, .r11, .r10, .r9, .r8, .rdi].filter fun r =>
    !ps.any (·.2 == r) && (r != .rsi || (tregOf fd).isNone)
  ps ++ (chosen.filter (fd.nparams ≤ ·)).zip free

def fnCtx2 (fl : Flags) (tab : Tab) (t : NTree) (f : FnName) (fd : FunDecl) (F : Nat) : Ctx :=
  let c := fnCtx tab t f fd
  let c := if fl.regs && c.leaf && !c.alloc.isEmpty then { c with alloc := leafAlloc2 fd } else c
  { c with tailF := if Stmt.calls fd.body then some F else none }

/-- The function's frame words (locals plus the temporaries its code uses). -/
def frameOf (fl : Flags) (tab : Tab) (t : NTree) (f : FnName) (fd : FunDecl) : Nat :=
  let ctx0 := fnCtx2 fl tab t f fd (fd.nlocals + 64)
  fd.nlocals + tempsUsed fd.nlocals (body fl ctx0 fd)

def Stmt.callees : Stmt → List FnName
  | .seq s t | .ite _ s t => Stmt.callees s ++ Stmt.callees t
  | .while _ s => Stmt.callees s
  | .call _ f _ => [f]
  | _ => []

def compileFn2 (fl : Flags) (tab : Tab) (t : NTree) (info : Std.HashMap String FnInfo) (entry : FnName)
    (f : FnName) (fd : FunDecl) : Program :=
  let I := info.getD f ⟨0, false, true⟩
  let F := I.F
  let ctx := fnCtx2 fl tab t f fd F
  let code0 := tregEntry ctx ++ body fl ctx fd
  let code := if fl.base then basePeep tab (pool ctx) code0 [] else code0
  let allInRegs := (List.range fd.nlocals).all (fun x => (ctx.alloc.lookup x).isSome)
  if ctx.leaf && allInRegs && F == fd.nlocals then [.label (fnL f)] ++ code ++ [i64 .ret]
  else if fl.stk && ctx.leaf && f != entry then
    [.label (fnL f), i64 (.sub (.reg (rr .rsp)) (oI (8 * F)))] ++ code ++
      [i64 (.add (.reg (rr .rsp)) (oI (8 * F))), i64 .ret]
  else
  let need : Nat := if fl.stk then
      (Stmt.callees fd.body).foldl (fun acc g =>
        match info.get? g with
        | some J => if J.leaf && g != entry && J.framed then max acc (8 * J.F) else acc
        | none => acc) 0
    else 0
  [.label (fnL f),
   movRR .rax .rsp, i64 (.sub (.reg (rr .rax)) (oM (mb .r15 Tab.stackLimit))),
   i64 (.cmp (.reg (rr .rax)) (oI (8 * F + 8 + need))), jccL .c exhaustedL,
   i64 (.sub (.reg (rr .rsp)) (oI (8 * F)))] ++ code ++
  [i64 (.add (.reg (rr .rsp)) (oI (8 * F))), i64 .ret]

def compileProg2 (fl0 : Flags) (tab : Tab) (p0 : Prog) (entry : FnName) (lo hi : Nat) : Program :=
  let t := Prog.nrt p0
  let p := p0.zipIdx.map fun ((f, fd), i) => (f, fd, if lo ≤ i && i < hi then fl0 else ({} : Flags))
  let fl := fl0
  let info : Std.HashMap String FnInfo := p.foldl (fun m (f, fd, fl) =>
    let F := frameOf fl tab t f fd
    let ctx := fnCtx2 fl tab t f fd F
    let allInRegs := (List.range fd.nlocals).all (fun x => (ctx.alloc.lookup x).isSome)
    m.insert f ⟨F, ctx.leaf, !(ctx.leaf && allInRegs && F == fd.nlocals)⟩) {}
  let _ := fl
  let tr := trampoline tab entry (nrOf t tab entry) (entryNp p0 entry)
  let tr := if fl0.regs then tr.flatMap (fun d =>
      if d == i64 (.push (oR .rbp)) then [d, i64 (.push (oR .rbx)), i64 (.push (oR .r12)), i64 (.push (oR .r13))]
      else if d == i64 (.pop (.reg (rr .rbp))) then [i64 (.pop (.reg (rr .r13))), i64 (.pop (.reg (rr .r12))), i64 (.pop (.reg (rr .rbx))), d]
      else [d]) else tr
  tr ++
    p.flatMap fun (f, fd, fl) => compileFn2 fl tab t info entry f fd

end L.Compiler.LG

open L.Compiler L.Checker L.Compiler.LG

def main (args : List String) : IO Unit := do
  let out := args.headD "checker.s"
  let fs := (args.getD 1 "").splitOn ","
  let fl : Flags := { gen := fs.contains "gen", cmp := fs.contains "cmp", stk := fs.contains "stk",
                      base := fs.contains "base", regs := fs.contains "regs",
                      zero := fs.contains "zero" }
  let lo := (args.getD 2 "0").toNat!
  let hi := (args.getD 3 "1000000").toNat!
  let code := compileProg2 fl checkerTab checkerProg "check" lo hi
  IO.FS.writeFile out (asmTextAbiPar checkerTab L.Arena.MODE L.Arena.PLO L.Arena.PHI L.Arena.OUT L.Arena.HDRF L.Arena.CTLF 126 L.Arena.frozenIdsL
      L.Arena.parOwnedL code ++
    s!".section .rodata\n.globl ca_nw\n.globl ca_nb\n.globl ca_diag\nca_nw: .quad {checkerTab.nw}\nca_nb: .quad {checkerTab.nb}\nca_diag: .quad -1\n")
  IO.println s!"wrote {out}: {code.length} directives"
