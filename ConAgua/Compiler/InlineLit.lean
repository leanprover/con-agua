module

public import Lean
public import ConAgua.Compiler.WFSplit
public import ConAgua.Compiler.AsmLit
public import ConAgua.Compiler.Inline
public meta import Lean
public meta import ConAgua.Compiler.WFSplit
public meta import ConAgua.Compiler.AsmLit
public meta import ConAgua.Compiler.Inline

@[expose] public section

/-!
# The inlined program as a kernel-checked literal

The kernel must not evaluate the inliner (`Compiler/Inline.lean`) over the whole program in one
check: each function's inlining evaluates its callees' declarations too, and the kernel keeps
what it evaluated (≈ 9 MB per function; all of `checkerProg` at once went past 16 GB). And the
modules that read the compiled program (`nrt_lit`, `skt_lit`, `asm_lit`, `prog_wf`) would each
evaluate it again. So the inliner's output is a literal, checked one function at a time:

* `idx_lit name : p` declares `name : NTree`, the literal of `Prog.idxTree p` (computed by
  compiled code); `idx_lit_eq name : p`, where the correctness theorem needs it,
  `name_eq : Prog.idxTree p = some name` (one kernel check over the names). The literals below
  hold for any tree.
* `inl_round_fns name : S t p lo hi` declares, for the functions `lo ≤ i < hi` of `p`,
  `name.f<i> : FunDecl`, the literal of `inlFn (envOf S t p) fdᵢ` (computed by compiled code; the
  function's own declaration term if inlining does not change it), and
  `name.f<i>_eq : inlFn (envOf S t p) fdᵢ = name.f<i>`, checked by the kernel (`inlLitBatch`
  functions per check), so that a large program's checks are spread over modules.
* `inl_round name : S t p` declares the rest and `name : Prog := [(f₀, name.f0), …]` (compiled
  code runs it as `inlRound S t p`, `name.impl`);
* `inl_round_eq name : S t p`, in a module of its own (the modules that compile the literal do not
  wait for it), `name_eq : inlRound S t p = name`, from the per-function equations by congruence
  (`inlRound_cons`), without evaluation.

The constant byte strings of the literal (`ldc`, `rom` sources, `scan8` class tables) are the
constants of the environment that hold them, so that the kernel compares names, not bytes; a
string that no constant holds is written out.
-/

namespace L.Compiler

open Lean Elab Command Meta
open Lean.Elab.Term (elabTermEnsuringType synthesizeSyntheticMVarsNoPostponing)

theorem inlRound_nil (env : Env) : ([] : Prog).map (fun x => (x.1, inlFn env x.2)) = [] := rfl

theorem inlRound_cons {env : Env} {f : FnName} {fd fd' : FunDecl} {tl tl' : Prog}
    (h : inlFn env fd = fd') (h' : tl.map (fun x => (x.1, inlFn env x.2)) = tl') :
    ((f, fd) :: tl).map (fun x => (x.1, inlFn env x.2)) = (f, fd') :: tl' := by
  simp only [List.map_cons, h, h']

meta unsafe def evalOptNTree (e : Lean.Expr) : MetaM (Option NTree) :=
  evalExpr (Option NTree) (mkApp (mkConst ``Option [0]) (mkConst ``NTree)) e

syntax (name := idxLit) "idx_lit " ident " : " term:max : command

@[command_elab idxLit] meta unsafe def elabIdxLit : CommandElab := fun stx => do
  let `(idx_lit $n:ident : $progS) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) do
    let pE ← elabTermEnsuringType progS (mkConst ``Prog)
    synthesizeSyntheticMVarsNoPostponing
    let pE ← instantiateMVars pE
    let some t ← evalOptNTree (mkApp (mkConst ``Prog.idxTree) pE) | throwError "idx_lit: a name occurs twice"
    withExporting <| addAndCompile (.defnDecl (mkDefinitionValEx name [] (mkConst ``NTree) (ntreeToExpr t) .abbrev .safe []))

/-- `idx_lit_eq name : p` (after `idx_lit name : p`): `name_eq : Prog.idxTree p = some name`, one
kernel check over the names. Only the correctness theorem needs it, not the literals. -/
syntax (name := idxLitEq) "idx_lit_eq " ident " : " term:max : command

@[command_elab idxLitEq] meta unsafe def elabIdxLitEq : CommandElab := fun stx => do
  let `(idx_lit_eq $n:ident : $progS) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) do
    let pE ← elabTermEnsuringType progS (mkConst ``Prog)
    synthesizeSyntheticMVarsNoPostponing
    let pE ← instantiateMVars pE
    let lhs := mkApp (mkConst ``Prog.idxTree) pE
    let treeTy := mkConst ``NTree
    let optTy := mkApp (mkConst ``Option [0]) treeTy
    let rhs := mkApp2 (mkConst ``Option.some [0]) treeTy (mkConst name)
    addDecl (thm (name.appendAfter "_eq") (mkApp3 (mkConst ``Eq [1]) optTy lhs rhs)
      (mkApp2 (mkConst ``Eq.refl [1]) optTy lhs) [])

/-! ## Statements as terms -/

/-- The constants of the environment that hold a byte string, by value. -/
meta unsafe def romConsts : MetaM (Std.HashMap (List UInt8) Name) := do
  let env ← getEnv
  let ty := mkApp (mkConst ``List [0]) (mkConst ``UInt8)
  let mut m : Std.HashMap (List UInt8) Name := {}
  for (n, ci) in env.constants.toList do
    if let .defnInfo d := ci then
      if d.levelParams.isEmpty && d.type == ty && !n.isInternal then
        try
          let v ← evalExpr (List UInt8) ty (mkConst n)
          if v.length ≥ 16 && !m.contains v then m := m.insert v n
        catch _ => pure ()
  return m

section
variable (rom : Std.HashMap (List UInt8) Name)

meta def wordE (w : Word) : Lean.Expr := mkApp (mkConst ``UInt64.ofNat) (mkNatLit w.toNat)

meta def bytesE (d : List UInt8) : Lean.Expr :=
  match rom.get? d with
  | some n => mkConst n
  | none => bytesToExpr d.toArray

meta def listE (ty : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc) (mkApp (mkConst ``List.nil [0]) ty)

meta def binOpE : BinOp → Lean.Expr
  | .add => mkConst ``BinOp.add | .sub => mkConst ``BinOp.sub | .mul => mkConst ``BinOp.mul
  | .and => mkConst ``BinOp.and | .or => mkConst ``BinOp.or | .xor => mkConst ``BinOp.xor
  | .shl => mkConst ``BinOp.shl | .shr => mkConst ``BinOp.shr | .mulhi => mkConst ``BinOp.mulhi

meta def cmpE : Cmp → Lean.Expr
  | .eq => mkConst ``Cmp.eq | .ne => mkConst ``Cmp.ne | .ult => mkConst ``Cmp.ult
  | .ule => mkConst ``Cmp.ule | .slt => mkConst ``Cmp.slt | .sle => mkConst ``Cmp.sle

meta def boolE (b : Bool) : Lean.Expr := if b then mkConst ``Bool.true else mkConst ``Bool.false

meta def bsrcE : BSrc → Lean.Expr
  | .arr a => mkApp (mkConst ``BSrc.arr) (mkNatLit a)
  | .rom d => mkApp (mkConst ``BSrc.rom) (bytesE rom d)

meta def exprE : Expr → Lean.Expr
  | .const w => mkApp (mkConst ``Expr.const) (wordE w)
  | .var x => mkApp (mkConst ``Expr.var) (mkNatLit x)
  | .bin op a b => mkApp3 (mkConst ``Expr.bin) (binOpE op) (exprE a) (exprE b)
  | .ld8 a i => mkApp2 (mkConst ``Expr.ld8) (mkNatLit a) (exprE i)
  | .ld64 a i => mkApp2 (mkConst ``Expr.ld64) (mkNatLit a) (exprE i)
  | .len8 a => mkApp (mkConst ``Expr.len8) (mkNatLit a)
  | .len64 a => mkApp (mkConst ``Expr.len64) (mkNatLit a)
  | .cmpw c a b => mkApp3 (mkConst ``Expr.cmpw) (cmpE c) (exprE a) (exprE b)
  | .ldc d i => mkApp2 (mkConst ``Expr.ldc) (bytesE rom d) (exprE i)
  | .glob g => mkApp (mkConst ``Expr.glob) (mkApp (mkConst ``GVar.mk) (mkNatLit g.id))
  | .ld64t a t i => mkApp3 (mkConst ``Expr.ld64t) (mkNatLit a) (exprE t) (exprE i)
  | .len64t a t => mkApp2 (mkConst ``Expr.len64t) (mkNatLit a) (exprE t)
  | .ld8x8 s i => mkApp2 (mkConst ``Expr.ld8x8) (bsrcE rom s) (exprE i)
  | .ld32t a t i => mkApp3 (mkConst ``Expr.ld32t) (mkNatLit a) (exprE t) (exprE i)
  | .ld32h a t i h => mkApp4 (mkConst ``Expr.ld32h) (mkNatLit a) (exprE t) (exprE i) (boolE h)

meta def warrE : WArr → Lean.Expr
  | .plain a => mkApp (mkConst ``WArr.plain) (mkNatLit a)
  | .tier a t => mkApp2 (mkConst ``WArr.tier) (mkNatLit a) (exprE rom t)

meta def condE : Cond → Lean.Expr
  | .cmp c a b => mkApp3 (mkConst ``Cond.cmp) (cmpE c) (exprE rom a) (exprE rom b)
  | .and p q => mkApp2 (mkConst ``Cond.and) (condE p) (condE q)
  | .or p q => mkApp2 (mkConst ``Cond.or) (condE p) (condE q)
  | .not p => mkApp (mkConst ``Cond.not) (condE p)

meta def stmtE : Stmt → Lean.Expr
  | .skip => mkConst ``Stmt.skip
  | .set x e => mkApp2 (mkConst ``Stmt.set) (mkNatLit x) (exprE rom e)
  | .st8 a i e => mkApp3 (mkConst ``Stmt.st8) (mkNatLit a) (exprE rom i) (exprE rom e)
  | .st64 a i e => mkApp3 (mkConst ``Stmt.st64) (mkNatLit a) (exprE rom i) (exprE rom e)
  | .seq s t => mkApp2 (mkConst ``Stmt.seq) (stmtE s) (stmtE t)
  | .ite c s t => mkApp3 (mkConst ``Stmt.ite) (condE rom c) (stmtE s) (stmtE t)
  | .while c s => mkApp2 (mkConst ``Stmt.while) (condE rom c) (stmtE s)
  | .brk => mkConst ``Stmt.brk
  | .ret es => mkApp (mkConst ``Stmt.ret) (listE (mkConst ``Expr) (es.map (exprE rom)))
  | .call xs f args => mkApp3 (mkConst ``Stmt.call) (listE (mkConst ``Nat) (xs.map mkNatLit)) (mkStrLit f)
      (listE (mkConst ``Expr) (args.map (exprE rom)))
  | .abort e => mkApp (mkConst ``Stmt.abort) (exprE rom e)
  | .gset g e => mkApp2 (mkConst ``Stmt.gset) (mkApp (mkConst ``GVar.mk) (mkNatLit g.id)) (exprE rom e)
  | .st64t a t i e => mkApp4 (mkConst ``Stmt.st64t) (mkNatLit a) (exprE rom t) (exprE rom i) (exprE rom e)
  | .copy64 d di s si n => mkApp5 (mkConst ``Stmt.copy64) (warrE rom d) (exprE rom di) (warrE rom s)
      (exprE rom si) (exprE rom n)
  | .copy8w d di s si n => mkApp5 (mkConst ``Stmt.copy8w) (warrE rom d) (exprE rom di) (bsrcE rom s)
      (exprE rom si) (exprE rom n)
  | .scan8 x s i e c => mkApp5 (mkConst ``Stmt.scan8) (mkNatLit x) (bsrcE rom s) (exprE rom i) (exprE rom e)
      (bytesE rom c)
  | .st32t a t i e => mkApp4 (mkConst ``Stmt.st32t) (mkNatLit a) (exprE rom t) (exprE rom i) (exprE rom e)

meta def funDeclE (fd : FunDecl) : Lean.Expr :=
  mkApp3 (mkConst ``FunDecl.mk) (mkNatLit fd.nparams) (mkNatLit fd.nlocals) (stmtE rom fd.body)
end

/-! ## The commands -/

meta register_option inlLitBatch : Nat := {
  defValue := 8
  descr := "inl_round: functions per kernel check"
}

meta unsafe def evalProg (e : Lean.Expr) : MetaM Prog := evalExpr Prog (mkConst ``Prog) e

meta def funDeclTy : Lean.Expr := mkConst ``FunDecl

/-- Declare `name.f<i>`, `name.f<i>_eq` for `lo ≤ i < hi` (those not declared yet). -/
meta unsafe def declInlFns (name : Name) (envE : Lean.Expr) (elems : Array Lean.Expr) (lo hi : Nat)
    (viaE : Lean.Expr) : MetaM Unit := do
  let hi := min hi elems.size
  let env ← getEnv
  let todo := (List.range (hi - lo)).map (· + lo) |>.filter fun i =>
    !env.contains (name ++ Name.mkSimple s!"f{i}")
  if todo.isEmpty then return
  -- `p` and its round, by compiled code (from `viaE`, a compiled term equal to `p`)
  let p ← evalProg viaE
  let some envV := envE.getAppArgs[1]? | throwError "inl_round: unexpected environment {envE}"
  let some t ← (evalExpr (Option NTree) (mkApp (mkConst ``Option [0]) (mkConst ``NTree))
    (mkApp2 (mkConst ``Option.some [0]) (mkConst ``NTree) envV) : MetaM (Option NTree)) | unreachable!
  let some sV := envE.getAppArgs[0]? | unreachable!
  let s ← evalExpr Nat (mkConst ``Nat) sV
  let q := (inlRound s t p).map (·.2)
  let rom ← romConsts
  let b := max 1 (inlLitBatch.get (← getOptions))
  let mut batch : Array (Name × Lean.Expr) := #[]
  for i in todo do
    let (_, _, fdE) ← progElem i elems[i]!
    let n := name ++ Name.mkSimple s!"f{i}"
    -- always a literal, also where the round changed nothing: the source term's L functions are
    -- `@[no_expose]`, and the whole-program checks over the literal (`ProgNrt`, `ProgSkt`,
    -- `ProgWf`, the asm parts) unfold it without `import all` of their modules
    let lit := funDeclE rom q[i]!
    withExporting <| addDecl (.defnDecl (mkDefinitionValEx n [] funDeclTy lit .abbrev .safe []))
    -- compiled code runs `n` as the inlining itself (the literal is not compiled)
    withExporting <| addAndCompile (.defnDecl (mkDefinitionValEx (n ++ `impl) [] funDeclTy (mkApp2 (mkConst ``inlFn) envE fdE)
      .opaque .safe []))
    match Compiler.implementedByAttr.setParam (← getEnv) n (n ++ `impl) with
    | .ok env => setEnv env
    | .error msg => throwError "inl_round_fns: {msg}"
    batch := batch.push (n, mkApp2 (mkConst ``inlFn) envE fdE)
    if batch.size ≥ b then
      declEqBatchTy funDeclTy (n.appendAfter "_batch") batch
      batch := #[]
  if let some (n, _) := batch.back? then declEqBatchTy funDeclTy (n.appendAfter "_batch") batch
where
  /-- `asm_lit`'s `declEqBatch` at type `ty`. -/
  declEqBatchTy (ty : Lean.Expr) (bname : Name) (eqs : Array (Name × Lean.Expr)) : MetaM Unit := do
    let tys := eqs.map fun (n, lhs) => mkApp3 (mkConst ``Eq [1]) ty lhs (mkConst n)
    let pfs := eqs.map fun (_, lhs) => mkApp2 (mkConst ``Eq.refl [1]) ty lhs
    let k := eqs.size - 1
    let mut conj := tys[k]!
    let mut pf := pfs[k]!
    let mut tails : Array Lean.Expr := #[conj]
    for j in (List.range k).reverse do
      pf := mkApp4 (mkConst ``And.intro) tys[j]! conj pfs[j]! pf
      conj := mkApp2 (mkConst ``And) tys[j]! conj
      tails := tails.push conj
    addDecl (.thmDecl { name := bname, levelParams := [], type := conj, value := pf })
    let tail (j : Nat) : Lean.Expr := tails[k - j]!
    let mut h := mkConst bname
    for j in List.range (k + 1) do
      let pj := if j == k then h else mkApp3 (mkConst ``And.left) tys[j]! (tail (j + 1)) h
      addDecl (.thmDecl { name := eqs[j]!.1.appendAfter "_eq", levelParams := [], type := tys[j]!, value := pj })
      if j < k then h := mkApp3 (mkConst ``And.right) tys[j]! (tail (j + 1)) h

/-- The terms `S`, `t`, `p` and `envOf S t p`. -/
meta def elabRoundArgs (sS tS pS : Syntax) : TermElabM (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := do
  let sE ← elabTermEnsuringType sS (mkConst ``Nat)
  let tE ← elabTermEnsuringType tS (mkConst ``NTree)
  let pE ← elabTermEnsuringType pS (mkConst ``Prog)
  synthesizeSyntheticMVarsNoPostponing
  let sE ← instantiateMVars sE
  let tE ← instantiateMVars tE
  let pE ← instantiateMVars pE
  return (sE, tE, pE, mkApp3 (mkConst ``envOf) sE tE pE)

/-- The term to evaluate `p` with: `via e`, else `p` itself. -/
meta def elabVia (pE : Lean.Expr) : Option Syntax → TermElabM Lean.Expr
  | none => pure pE
  | some v => do
    let e ← elabTermEnsuringType v (mkConst ``Prog)
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e

syntax (name := inlRoundFns) "inl_round_fns " ident " : " term:max term:max term:max (" via " term:max)? num num : command

@[command_elab inlRoundFns] meta unsafe def elabInlRoundFns : CommandElab := fun stx => do
  let `(inl_round_fns $n:ident : $sS $tS $pS $[via $v?]? $lo $hi) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000, maxHeartbeats := 0 }) do
    let (_, _, pE, envE) ← elabRoundArgs sS tS pS
    declInlFns name envE (← listElemsW pE) lo.getNat hi.getNat (← elabVia pE (v?.map (·.raw)))

syntax (name := inlRoundCmd) (docComment)? "inl_round " ident " : " term:max term:max term:max (" via " term:max)? : command

@[command_elab inlRoundCmd] meta unsafe def elabInlRound : CommandElab := fun stx => do
  let `($[$doc?:docComment]? inl_round $n:ident : $sS $tS $pS $[via $v?]?) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000, maxHeartbeats := 0 }) do
    let (sE, tE, pE, envE) ← elabRoundArgs sS tS pS
    let elems ← listElemsW pE
    declInlFns name envE elems 0 elems.size (← elabVia pE (v?.map (·.raw)))
    let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) funDeclTy
    let progT := mkConst ``Prog
    let mut lit := mkApp (mkConst ``List.nil [0]) elemTy
    for i in (List.range elems.size).reverse do
      let (_, fE, _) ← progElem i elems[i]!
      let fi := mkConst (name ++ Name.mkSimple s!"f{i}")
      lit := mkApp3 (mkConst ``List.cons [0]) elemTy (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) funDeclTy fE fi) lit
    withExporting <| addDecl (.defnDecl (mkDefinitionValEx name [] progT lit .abbrev .safe []))
    addDocString' name .missing doc?
    -- compiled code runs `name` as the round itself (the literal's functions are not compiled)
    let implN := name ++ `impl
    withExporting <| addAndCompile (.defnDecl (mkDefinitionValEx implN [] progT
      (mkApp3 (mkConst ``inlRound) sE tE (← elabVia pE (v?.map (·.raw)))) .opaque .safe []))
    match Compiler.implementedByAttr.setParam (← getEnv) name implN with
    | .ok env => setEnv env
    | .error msg => throwError "inl_round: {msg}"

/-- `inl_round_eq name : S t p` (after `inl_round name : S t p`): `name_eq : inlRound S t p = name`,
from the per-function equations by congruence (`inlRound_cons`), without evaluation. -/
syntax (name := inlRoundEqCmd) "inl_round_eq " ident " : " term:max term:max term:max : command

@[command_elab inlRoundEqCmd] meta unsafe def elabInlRoundEq : CommandElab := fun stx => do
  let `(inl_round_eq $n:ident : $sS $tS $pS) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000, maxHeartbeats := 0 }) do
    let (sE, tE, pE, envE) ← elabRoundArgs sS tS pS
    let elems ← listElemsW pE
    let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) funDeclTy
    let progT := mkConst ``Prog
    let mut lit := mkApp (mkConst ``List.nil [0]) elemTy
    let mut tl := mkApp (mkConst ``List.nil [0]) elemTy
    let mut pf := mkApp (mkConst ``inlRound_nil) envE
    for i in (List.range elems.size).reverse do
      let (_, fE, fdE) ← progElem i elems[i]!
      let fi := mkConst (name ++ Name.mkSimple s!"f{i}")
      let hi := mkConst ((name ++ Name.mkSimple s!"f{i}").appendAfter "_eq")
      pf := mkAppN (mkConst ``inlRound_cons) #[envE, fE, fdE, fi, tl, lit, hi, pf]
      lit := mkApp3 (mkConst ``List.cons [0]) elemTy (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) funDeclTy fE fi) lit
      tl := mkApp3 (mkConst ``List.cons [0]) elemTy elems[i]! tl
    let lhs := mkApp3 (mkConst ``inlRound) sE tE pE
    addDecl (.thmDecl { name := name.appendAfter "_eq", levelParams := [], type := mkApp3 (mkConst ``Eq [1]) progT lhs (mkConst name),
                        value := pf })

end L.Compiler
