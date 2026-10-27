import ConAgua.E2E.Ser
import Lean.Elab.Command
import Lean.Meta.Eval
import Std.Do.Triple.SpecLemmas

/-!
# Dump every L function an import closure names (lane `e2e`)

`dumpBindings out` (run by `#eval` in a file `scripts/e2e.py` generates, which imports one closure
of modules) finds every binding of a function name to a `FunDecl` in the environment's `ConAgua`
modules and prints them in `Ser.lean`'s format, one `bind` line per (source, name) and one
`fn`/`data` line per distinct body:

* every constant of type `L.Prog` (each list's first binding of a name wins, as in `List.lookup`);
* every `List.lookup "f" p = some d` with a closed `d` in the type of a constant (the lookup
  hypotheses of the lanes' `…Prog p` structures and theorems: they name the FunDecl a proof
  expects under `"f"`, also for functions that no `Prog` list contains).

Output lines: `bind SOURCE NAME HASH STUB` (`STUB` is `1` when the body is a bare `abort`), and
`fn HASH NPARAMS NLOCALS BODY` with the `data` lines first.
-/

namespace L.E2E

open Lean Meta Elab Command

def isAbortBody : L.Stmt → Bool
  | .abort _ => true
  | .seq .skip t => isAbortBody t
  | .seq t .skip => isAbortBody t
  | _ => false

/-- The `(name, decl)` expressions of every `List.lookup "f" p = some d` in `e`. -/
partial def lookupsIn (e : Lean.Expr) : Array (String × Lean.Expr) := Id.run do
  let mut out := #[]
  let mut todo := #[e]
  let mut seen : Std.HashSet UInt64 := {}
  while h : todo.size > 0 do
    let x := todo.back
    todo := todo.pop
    if seen.contains x.hash then continue
    seen := seen.insert x.hash
    if x.isAppOfArity ``Eq 3 then
      let lhs := x.getArg! 1
      let rhs := x.getArg! 2
      if lhs.isAppOfArity ``List.lookup 5 && rhs.isAppOfArity ``Option.some 2 then
        if let .lit (.strVal s) := lhs.getArg! 3 then
          let d := rhs.getArg! 1
          if !d.hasLooseBVars && !d.hasFVar && !d.hasMVar then out := out.push (s, d)
    match x with
    | .app f a => todo := todo.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
    | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
    | .mdata _ b => todo := todo.push b
    | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return out

/-- `lookupsIn`, keeping the lookups whose FunDecl mentions free variables (no loose ones). -/
partial def lookupsInF (e : Lean.Expr) : Array (String × Lean.Expr) := Id.run do
  let mut out := #[]
  let mut todo := #[e]
  while h : todo.size > 0 do
    let x := todo.back
    todo := todo.pop
    if x.isAppOfArity ``Eq 3 then
      let lhs := x.getArg! 1
      let rhs := x.getArg! 2
      if lhs.isAppOfArity ``List.lookup 5 && rhs.isAppOfArity ``Option.some 2 then
        if let .lit (.strVal s) := lhs.getArg! 3 then
          let d := rhs.getArg! 1
          if !d.hasLooseBVars && d.hasFVar && !d.hasMVar then out := out.push (s, d)
    match x with
    | .app f a => todo := todo.push f |>.push a
    | .mdata _ b => todo := todo.push b
    | _ => pure ()
  return out

/-- The program's ROM (`ConAgua/Arena/Prelude.lean`). -/
def romName : Name := `L.Rom.romData
def romTy : Lean.Expr := mkApp (mkConst ``List [.zero]) (mkConst ``UInt8)

unsafe def evalFunDecl (e : Lean.Expr) : MetaM L.FunDecl :=
  Lean.Meta.evalExpr L.FunDecl (mkConst ``L.FunDecl) e

unsafe def evalProgConst (n : Name) : MetaM L.Prog := do
  match (← getEnv).evalConst L.Prog (← getOptions) n with
  | .ok p => pure p
  | .error e => throwError "eval {n}: {e}"

/-- The bindings one constant contributes (its own `Prog` value, the lookups its type states,
those parametric in the ROM), and the errors evaluating them. -/
unsafe def bindingsOf (n : Name) (ci : ConstantInfo) :
    MetaM (Array (String × String × L.FunDecl) × Array String) := do
  let env ← getEnv
  let mut binds : Array (String × String × L.FunDecl) := #[]
  let mut errs : Array String := #[]
  -- a `Prog` without code (`noncomputable`, e.g. `checkerProg.chunk<j>`) is a view of another
  if ci.type == mkConst ``L.Prog && ci matches .defnInfo _ && !isNoncomputable env n then
    try
      let p ← evalProgConst n
      let mut names : Std.HashSet String := {}
      for (f, d) in p do
        unless names.contains f do
          names := names.insert f
          binds := binds.push (s!"{n}", f, d)
    catch e => errs := errs.push s!"{n}: {← e.toMessageData.toString}"
  for (f, de) in lookupsIn ci.type do
    try
      let d ← evalFunDecl de
      binds := binds.push (s!"{n}", f, d)
    catch e => errs := errs.push s!"{n} {f}: {← e.toMessageData.toString}"
  -- lookups parametric in the ROM (`NameProg rom p`, …): instantiated at the program's ROM
  if env.contains romName then
    let found ← Meta.forallTelescope ci.type fun xs body => do
      let mut out := #[]
      let roms ← xs.filterM fun x => do return (← Meta.inferType x) == romTy
      if roms.isEmpty then return out
      for (f, de) in lookupsInF body do
        let de' := de.replaceFVars roms (roms.map fun _ => mkConst romName)
        if !de'.hasFVar then out := out.push (f, de')
      return out
    for (f, de) in found do
      try
        let d ← evalFunDecl de
        binds := binds.push (s!"{n}@rom", f, d)
      catch e => errs := errs.push s!"{n} {f}: {← e.toMessageData.toString}"
  return (binds, errs)

unsafe def dumpBindingsImpl (out : System.FilePath) : CommandElabM Unit := liftTermElabM do
  let env ← getEnv
  let mut binds : Array (String × String × L.FunDecl) := #[]
  let mut errs : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some mi := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[mi.toNat]!
    unless (`ConAgua).isPrefixOf mod do continue
    -- each constant has its own heartbeat budget (one command reads every constant of the closure)
    let (bs, es) ← withCurrHeartbeats (bindingsOf n ci)
    binds := binds ++ bs
    errs := errs ++ es
  -- distinct bodies by their text
  let mut bodies : Std.HashMap String Nat := {}
  let mut fnLines : Array String := #[]
  let mut bindLines : Array String := #[]
  let mut data : Array (List UInt8) := #[]
  for (src, f, d) in binds do
    let (txt, data') := (serS d.body).run data
    data := data'
    let key := s!"{d.nparams} {d.nlocals} {txt}"
    let h ← match bodies.get? key with
      | some h => pure h
      | none =>
        let h := bodies.size
        bodies := bodies.insert key h
        fnLines := fnLines.push s!"fn {h} {key}"
        pure h
    bindLines := bindLines.push s!"bind {src} {f} {h} {if isAbortBody d.body then 1 else 0}"
  let dataLines := (data.mapIdx fun i d => s!"data {i} {hexOf d}").toList
  let errLines := errs.toList.map ("err " ++ ·)
  IO.FS.writeFile out ("\n".intercalate (dataLines ++ fnLines.toList ++ bindLines.toList ++ errLines) ++ "\n")

@[implemented_by dumpBindingsImpl]
opaque dumpBindings (out : System.FilePath) : CommandElabM Unit

end L.E2E
