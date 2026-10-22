import ConAgua.Checker.Prog
import ConAgua.Arena.CoreErec
/-! Prints the call closure of `L.Arena.coreRoots` in `L.Checker.checkerProg`, sorted, one name per
line (run by `scripts/core_fns.py`, which writes it into `ConAgua/Arena/CoreErec.lean`). -/
open L
partial def L.Stmt.callsW : Stmt → List FnName
  | .seq s t => s.callsW ++ t.callsW
  | .ite _ s t => s.callsW ++ t.callsW
  | .while _ s => s.callsW
  | .call _ f _ => [f]
  | _ => []
partial def cloW (p : Prog) (todo seen : List FnName) : List FnName :=
  match todo with
  | [] => seen
  | f :: r => if f ∈ seen then cloW p r seen else
    match p.lookup f with
    | some fd => cloW p (fd.body.callsW ++ r) (f :: seen)
    | none => cloW p r (f :: seen)
#eval do
  for f in (cloW L.Checker.checkerProg L.Arena.coreRoots []).mergeSort do
    IO.println s!"FN {f}"
