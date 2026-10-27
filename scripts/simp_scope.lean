import Lean
/-! `scripts/simp_scope.py`'s query: run as `lake env lean --run scripts/simp_scope.lean OUT M…`.
Reads the `.olean` of each module `M` and of everything it imports (no import into an
environment, so modules that cannot be imported together are fine; in a `module`, the public
part: what other modules can use) and writes to `OUT` one `I <module> <import>` line per import
and one `C <name> <module>` line per non-internal constant. -/
open Lean

def main (args : List String) : IO Unit := do
  let out :: mods := args | throw (IO.userError "usage: simp_scope.lean OUT MODULE…")
  initSearchPath (← findSysroot)
  let h ← IO.FS.Handle.mk out .write
  let mut todo : Array Name := mods.toArray.map (·.toName)
  let mut seen : NameSet := todo.foldl (·.insert ·) {}
  while todo.size > 0 do
    let m := todo.back!
    todo := todo.pop
    let (md, _) ← readModuleData (← findOLean m)
    for imp in md.imports do
      h.putStrLn s!"I {m} {imp.module}"
      unless seen.contains imp.module do
        seen := seen.insert imp.module
        todo := todo.push imp.module
    for n in md.constNames do
      unless n.isInternal do h.putStrLn s!"C {n} {m}"
