import ConAgua.E2E.Dump

/-!
# Where each L function of the checker comes from (lane `integrate`)

`scripts/checker_prog.py` generates `ConAgua/Checker/Prog.lean` (the program `checkerProg`) from the
lanes' modules. It picks, for every function name reachable from `check`, one binding found by
`ConAgua/E2E/Dump.lean` (a `Prog` constant, or a `p.lookup "f" = some d` in a constant's type), and
asks `writeSources` (run by `#eval` in a generated file that imports the sources' modules) for the
Lean term of that binding's `FunDecl`, printed with full names, and the modules the term needs.

Input lines `SOURCE NAME` (`SOURCE` as `Dump.lean` prints it, `…@rom` for the ROM-parametric
lookups); output lines `ok NAME MODULE,MODULE,… TERM` or `err NAME MESSAGE`.
-/

namespace L.Checker

open Lean Meta Elab Command

/-- The `(name, FunDecl term)` entries of a `Prog`-valued term, by weak-head reduction of the list
(first binding of a name first, as in `List.lookup`). -/
partial def progEntries (e : Lean.Expr) (acc : Array (String × Lean.Expr) := #[]) :
    MetaM (Array (String × Lean.Expr)) := do
  let e ← whnfD e
  match e.getAppFnArgs with
  | (``List.nil, _) => pure acc
  | (``List.cons, #[_, hd, tl]) =>
    let hd ← whnfD hd
    match hd.getAppFnArgs with
    | (``Prod.mk, #[_, _, s, d]) =>
      let s ← whnfD s
      match s with
      | .lit (.strVal n) => progEntries tl (acc.push (n, d))
      | _ => throwError "entry name not a literal: {s}"
    | _ => throwError "entry not a pair: {hd}"
  | _ => throwError "not a list: {e}"

/-- The FunDecl term `SOURCE` binds to `name`. -/
def sourceTerm (src name : String) : MetaM Lean.Expr := do
  let env ← getEnv
  let rom := src.endsWith "@rom"
  let c := (if rom then src.dropEnd 4 else src).toName
  let some ci := env.find? c | throwError "no constant {c}"
  if rom then
    let r ← forallTelescope ci.type fun xs body => do
      let roms ← xs.filterM fun x => do return (← inferType x) == L.E2E.romTy
      for (f, de) in L.E2E.lookupsInF body do
        if f == name then
          let de' := de.replaceFVars roms (roms.map fun _ => mkConst L.E2E.romName)
          if !de'.hasFVar then return some de'
      return none
    match r with
    | some d => pure d
    | none => throwError "no ROM lookup of {name} in {c}"
  else if ci.type == mkConst ``L.Prog then
    match (← progEntries (mkConst c)).find? (·.1 == name) with
    | some (_, d) => pure d
    | none => throwError "{name} not in {c}"
  else
    match (L.E2E.lookupsIn ci.type).find? (·.1 == name) with
    | some (_, d) => pure d
    | none => throwError "no lookup of {name} in {c}"

def writeSourcesImpl (inp out : System.FilePath) : CommandElabM Unit := liftTermElabM do
  let env ← getEnv
  let mut lines : Array String := #[]
  for l in (← IO.FS.lines inp) do
    let ws := l.splitOn " "
    let some src := ws[0]? | continue
    let some name := ws[1]? | continue
    try
      let d ← instantiateMVars (← sourceTerm src name)
      let mods := d.getUsedConstants.filterMap fun c =>
        (env.getModuleIdxFor? c).map fun i => s!"{env.header.moduleNames[i.toNat]!}"
      let mods := mods.toList.eraseDups
      let fmt ← withOptions (fun o => o.setBool `pp.fullNames true) <| ppExpr d
      let txt := (fmt.pretty 100000).replace "\n" " "
      lines := lines.push s!"ok {name} {",".intercalate mods} {txt}"
    catch e =>
      lines := lines.push s!"err {name} {(← e.toMessageData.toString).replace "\n" " "}"
  IO.FS.writeFile out ("\n".intercalate lines.toList ++ "\n")

/-- Run from a generated file (`scripts/checker_prog.py`). -/
def writeSources (inp out : System.FilePath) : CommandElabM Unit := writeSourcesImpl inp out

end L.Checker
