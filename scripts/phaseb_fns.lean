import ConAgua.Checker.Prog

/-! Prints the call closure of `check_pending_go` in `L.Checker.checkerProg`, sorted, one name per
line (run by `scripts/phaseb_fns.py`, which writes it into `ConAgua/Checker/PhaseBReads.lean`). -/
open L
partial def L.Stmt.callsB : Stmt → List FnName
  | .seq s t => s.callsB ++ t.callsB
  | .ite _ s t => s.callsB ++ t.callsB
  | .while _ s => s.callsB
  | .call _ f _ => [f]
  | _ => []
partial def cloB (p : Prog) (todo seen : List FnName) : List FnName :=
  match todo with
  | [] => seen
  | f :: r => if f ∈ seen then cloB p r seen else
    match p.lookup f with
    | some fd => cloB p (fd.body.callsB ++ r) (f :: seen)
    | none => cloB p r (f :: seen)
#eval do
  for f in (cloB L.Checker.checkerProg ["check_pending_go"] []).mergeSort do
    IO.println s!"FN {f}"
