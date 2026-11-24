import ConAgua.Checker.Prog

/-! Prints the call closure of the challenge's preparation steps of `check_c3` (`index_to_solution`,
`cmp_restore`, `prepare_prelude`, `side_records`, `solution_of`, `build_index`) in
`L.Checker.checkerProg`, sorted, one name per line (run by `scripts/c3stage_fns.py`, which writes it
into `ConAgua/Checker/CmpStashFrame.lean`). -/
open L
partial def L.Stmt.callsC : Stmt → List FnName
  | .seq s t => s.callsC ++ t.callsC
  | .ite _ s t => s.callsC ++ t.callsC
  | .while _ s => s.callsC
  | .call _ f _ => [f]
  | _ => []
partial def cloC (p : Prog) (todo seen : List FnName) : List FnName :=
  match todo with
  | [] => seen
  | f :: r => if f ∈ seen then cloC p r seen else
    match p.lookup f with
    | some fd => cloC p (fd.body.callsC ++ r) (f :: seen)
    | none => cloC p r (f :: seen)
#eval do
  for f in (cloC L.Checker.checkerProg ["index_to_solution", "cmp_restore", "prepare_prelude", "side_records",
      "solution_of", "build_index"] []).mergeSort do
    IO.println s!"FN {f}"
