import ConAgua.L.Syntax

/-!
# A text form of L programs (lane `e2e`)

The e2e lane assembles the whole checker from FunDecls that live in modules which cannot all be
imported into one Lean file (they clash on declaration names; `scripts/e2e.py` reports each clash). So the assembly goes
through text: `ConAgua/E2E/Dump.lean` prints every L function it finds in one import closure,
`scripts/e2e.py` merges the dumps and writes one program file, and `ConAgua/E2E/Main.lean` reads it
back (`parseProg`) to compile or interpret it.

Format: one item per line.
* `data K HEX` — constant byte string number `K` (the argument of `ldc`), as hex;
* `fn NAME NPARAMS NLOCALS BODY` — a function;
* `stub NAME NPARAMS CODE` — a function with no L code yet (e2e stub; `Main.lean` gives it a body).
Bodies are S-expressions over tokens: expressions `(c W)`, `(v X)`, `(b OP A B)`, `(l8 A E)`,
`(l64 A E)`, `(n8 A)`, `(n64 A)`, `(w CMP A B)`, `(ldc K E)`; conditions `(cmp CMP A B)`,
`(and P Q)`, `(or P Q)`, `(not P)`; statements `skip`, `(set X E)`, `(s8 A I E)`, `(s64 A I E)`,
`(seq S T)`, `(if C S T)`, `(while C S)`, `brk`, `(ret E…)`, `(call (X…) NAME (E…))`, `abort`.
-/

namespace L.E2E

open L

def binTok : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .and => "and" | .or => "or" | .xor => "xor"
  | .shl => "shl" | .shr => "shr" | .mulhi => "mulhi"

def cmpTok : Cmp → String
  | .eq => "eq" | .ne => "ne" | .ult => "ult" | .ule => "ule" | .slt => "slt" | .sle => "sle"

def hexOf (d : List UInt8) : String :=
  String.join (d.map fun b =>
    let h := "0123456789abcdef".toList
    String.ofList [h[(b.toNat / 16)]!, h[(b.toNat % 16)]!])

/-- Serialisation state: the constant byte strings seen so far. -/
abbrev SerM := StateM (Array (List UInt8))

def dataIdx (d : List UInt8) : SerM Nat := do
  let ds ← get
  match ds.findIdx? (· == d) with
  | some i => pure i
  | none => set (ds.push d); pure ds.size

def serB : BSrc → SerM String
  | .arr a => pure s!"(ba {a})"
  | .rom d => return s!"(br {← dataIdx d})"

mutual
partial def serE : Expr → SerM String
  | .const w => pure s!"(c {w.toNat})"
  | .var x => pure s!"(v {x})"
  | .bin op a b => return s!"(b {binTok op} {← serE a} {← serE b})"
  | .ld8 a i => return s!"(l8 {a} {← serE i})"
  | .ld64 a i => return s!"(l64 {a} {← serE i})"
  | .len8 a => pure s!"(n8 {a})"
  | .len64 a => pure s!"(n64 {a})"
  | .cmpw c a b => return s!"(w {cmpTok c} {← serE a} {← serE b})"
  | .ldc d i => return s!"(ldc {← dataIdx d} {← serE i})"
  | .glob g => pure s!"(g {g.id})"
  | .ld64t a t i => return s!"(l64t {a} {← serE t} {← serE i})"
  | .len64t a t => return s!"(n64t {a} {← serE t})"
  | .ld8x8 b i => return s!"(l8x8 {← serB b} {← serE i})"

partial def serW : WArr → SerM String
  | .plain a => pure s!"(wp {a})"
  | .tier a t => return s!"(wt {a} {← serE t})"
end

partial def serC : Cond → SerM String
  | .cmp c a b => return s!"(cmp {cmpTok c} {← serE a} {← serE b})"
  | .and p q => return s!"(and {← serC p} {← serC q})"
  | .or p q => return s!"(or {← serC p} {← serC q})"
  | .not p => return s!"(not {← serC p})"

partial def serS : Stmt → SerM String
  | .skip => pure "skip"
  | .set x e => return s!"(set {x} {← serE e})"
  | .st8 a i e => return s!"(s8 {a} {← serE i} {← serE e})"
  | .st64 a i e => return s!"(s64 {a} {← serE i} {← serE e})"
  | .seq s t => return s!"(seq {← serS s} {← serS t})"
  | .ite c s t => return s!"(if {← serC c} {← serS s} {← serS t})"
  | .while c s => return s!"(while {← serC c} {← serS s})"
  | .brk => pure "brk"
  | .ret es => return s!"(ret{String.join (← es.mapM fun e => return " " ++ (← serE e))})"
  | .call xs f args =>
    return s!"(call ({" ".intercalate (xs.map toString)}) {f} ({" ".intercalate (← args.mapM serE)}))"
  | .abort (.const 0) => pure "abort"
  | .abort e => return s!"(abort {← serE e})"
  | .gset g e => return s!"(gset {g.id} {← serE e})"
  | .st64t a t i e => return s!"(s64t {a} {← serE t} {← serE i} {← serE e})"
  | .copy64 d di s si n => return s!"(cp64 {← serW d} {← serE di} {← serW s} {← serE si} {← serE n})"
  | .copy8w d di s si n => return s!"(cp8w {← serW d} {← serE di} {← serB s} {← serE si} {← serE n})"
  | .scan8 x s i e c => return s!"(scan {x} {← serB s} {← serE i} {← serE e} {← dataIdx c})"

/-! ## Reading it back -/

inductive Tok where
  | lp | rp | atom (s : String)
  deriving Inhabited, BEq

def tokenize (s : String) : Array Tok := Id.run do
  let mut out : Array Tok := #[]
  let mut cur : String := ""
  for ch in s.toList do
    if ch == '(' || ch == ')' || ch == ' ' || ch == '\t' then
      if cur != "" then out := out.push (.atom cur); cur := ""
      if ch == '(' then out := out.push .lp
      if ch == ')' then out := out.push .rp
    else cur := cur.push ch
  if cur != "" then out := out.push (.atom cur)
  return out

structure PS where
  toks : Array Tok
  pos : Nat := 0
  data : Array (List UInt8)

abbrev P := StateT PS (Except String)

def next : P Tok := do
  let s ← get
  match s.toks[s.pos]? with
  | some t => set { s with pos := s.pos + 1 }; pure t
  | none => throw "unexpected end"

def peek : P Tok := do
  let s ← get
  pure (s.toks[s.pos]?.getD .rp)

def atom : P String := do
  match ← next with
  | .atom a => pure a
  | _ => throw "expected an atom"

def nat : P Nat := do
  let a ← atom
  match a.toNat? with
  | some n => pure n
  | none => throw s!"expected a number, got {a}"

def close : P Unit := do
  match ← next with
  | .rp => pure ()
  | _ => throw "expected )"

def open_ : P Unit := do
  match ← next with
  | .lp => pure ()
  | _ => throw "expected ("

def binOf : String → P BinOp
  | "add" => pure .add | "sub" => pure .sub | "mul" => pure .mul | "and" => pure .and
  | "or" => pure .or | "xor" => pure .xor | "shl" => pure .shl | "shr" => pure .shr
  | "mulhi" => pure .mulhi | s => throw s!"bad op {s}"

def cmpOf : String → P Cmp
  | "eq" => pure .eq | "ne" => pure .ne | "ult" => pure .ult | "ule" => pure .ule
  | "slt" => pure .slt | "sle" => pure .sle | s => throw s!"bad cmp {s}"

def parseB : P BSrc := do
  open_
  let h ← atom
  let b ← match h with
    | "ba" => do pure (.arr (← nat))
    | "br" => do let k ← nat; pure (.rom ((← get).data[k]?.getD []))
    | s => throw s!"bad source {s}"
  close
  return b

mutual
partial def parseE : P Expr := do
  open_
  let h ← atom
  let e ← match h with
    | "c" => do let w ← nat; pure (.const w.toUInt64)
    | "v" => do let x ← nat; pure (.var x)
    | "b" => do let op ← binOf (← atom); let a ← parseE; let b ← parseE; pure (.bin op a b)
    | "l8" => do let a ← nat; pure (.ld8 a (← parseE))
    | "l64" => do let a ← nat; pure (.ld64 a (← parseE))
    | "l64t" => do let a ← nat; let t ← parseE; pure (.ld64t a t (← parseE))
    | "n64t" => do let a ← nat; pure (.len64t a (← parseE))
    | "n8" => do let x ← nat; pure (.len8 x)
    | "n64" => do let x ← nat; pure (.len64 x)
    | "g" => do let x ← nat; pure (.glob ⟨x⟩)
    | "w" => do let c ← cmpOf (← atom); let a ← parseE; let b ← parseE; pure (.cmpw c a b)
    | "ldc" => do
      let k ← nat
      let d := (← get).data[k]?.getD []
      pure (.ldc d (← parseE))
    | "l8x8" => do let b ← parseB; pure (.ld8x8 b (← parseE))
    | s => throw s!"bad expr {s}"
  close
  return e

partial def parseW : P WArr := do
  open_
  let h ← atom
  let w ← match h with
    | "wp" => do pure (.plain (← nat))
    | "wt" => do let a ← nat; pure (.tier a (← parseE))
    | s => throw s!"bad block operand {s}"
  close
  return w
end

partial def parseC : P Cond := do
  open_
  let h ← atom
  let c ← match h with
    | "cmp" => do let c ← cmpOf (← atom); let a ← parseE; let b ← parseE; pure (.cmp c a b)
    | "and" => do let p ← parseC; let q ← parseC; pure (.and p q)
    | "or" => do let p ← parseC; let q ← parseC; pure (.or p q)
    | "not" => do let p ← parseC; pure (.not p)
    | s => throw s!"bad cond {s}"
  close
  return c

partial def parseList {α} (item : P α) : P (List α) := do
  open_
  let mut out := #[]
  while (← peek) != .rp do
    out := out.push (← item)
  close
  return out.toList

partial def parseS : P Stmt := do
  match ← peek with
  | .atom _ =>
    match ← atom with
    | "skip" => pure .skip
    | "brk" => pure .brk
    | "abort" => pure (.abort (.const 0))
    | s => throw s!"bad stmt {s}"
  | _ =>
    open_
    let h ← atom
    let s ← match h with
      | "set" => do let x ← nat; pure (.set x (← parseE))
      | "gset" => do let x ← nat; pure (.gset ⟨x⟩ (← parseE))
      | "abort" => do pure (.abort (← parseE))
      | "s8" => do let a ← nat; let i ← parseE; let e ← parseE; pure (.st8 a i e)
      | "s64" => do let a ← nat; let i ← parseE; let e ← parseE; pure (.st64 a i e)
      | "s64t" => do let a ← nat; let t ← parseE; let i ← parseE; let e ← parseE; pure (.st64t a t i e)
      | "seq" => do let s ← parseS; let t ← parseS; pure (.seq s t)
      | "if" => do let c ← parseC; let s ← parseS; let t ← parseS; pure (.ite c s t)
      | "while" => do let c ← parseC; pure (.while c (← parseS))
      | "ret" => do
        let mut es := #[]
        while (← peek) != .rp do es := es.push (← parseE)
        pure (.ret es.toList)
      | "call" => do
        let xs ← parseList nat
        let f ← atom
        let args ← parseList parseE
        pure (.call xs f args)
      | "cp64" => do
        let d ← parseW; let di ← parseE; let s ← parseW; let si ← parseE; let n ← parseE
        pure (.copy64 d di s si n)
      | "cp8w" => do
        let d ← parseW; let di ← parseE; let s ← parseB; let si ← parseE; let n ← parseE
        pure (.copy8w d di s si n)
      | "scan" => do
        let x ← nat; let s ← parseB; let i ← parseE; let e ← parseE; let k ← nat
        pure (.scan8 x s i e ((← get).data[k]?.getD []))
      | s => throw s!"bad stmt {s}"
    close
    return s

def unhex (s : String) : List UInt8 :=
  let v (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let cs := s.toList.toArray
  (List.range (cs.size / 2)).map fun i => (16 * v cs[2 * i]! + v cs[2 * i + 1]!).toUInt8

/-- A program file: the functions, and the stubs (name, parameter count, code). -/
structure ProgFile where
  fns : Array (FnName × FunDecl) := #[]
  stubs : Array (FnName × Nat × Nat) := #[]

def parseProgFile (text : String) : Except String ProgFile := do
  let mut data : Array (List UInt8) := #[]
  let mut pf : ProgFile := {}
  for line in text.splitOn "\n" do
    let ws := line.splitOn " "
    match ws with
    | "data" :: _ :: h :: _ => data := data.push (unhex h)
    | "fn" :: name :: np :: nl :: _ =>
      let rest := (line.drop ("fn ".length + name.length + np.length + nl.length + 3)).toString
      let (body, _) ← (parseS.run { toks := tokenize rest, data }).mapError (s!"{name}: " ++ ·)
      pf := { pf with fns := pf.fns.push (name, { nparams := np.toNat!, nlocals := nl.toNat!, body }) }
    | "stub" :: name :: np :: code :: _ =>
      pf := { pf with stubs := pf.stubs.push (name, np.toNat!, code.toNat!) }
    | _ => pure ()
  return pf

end L.E2E
