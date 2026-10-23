import ConAgua.Checker.Prog
import ConAgua.Arena.LeafFns
/-! Prints the functions of `loopFns` whose call closure in `L.Checker.checkerProg` passes
`Stmt.okW CTL leafA leafC` (calls unrestricted), sorted, one name per line (run by
`scripts/leaf_fns.py`, which writes them into `ConAgua/Arena/LeafFns.lean`). -/
open L L.Arena
partial def L.Stmt.callsL : Stmt → List FnName
  | .seq s t => s.callsL ++ t.callsL
  | .ite _ s t => s.callsL ++ t.callsL
  | .while _ s => s.callsL
  | .call _ f _ => [f]
  | _ => []
partial def cloL (p : Prog) (todo seen : List FnName) : List FnName :=
  match todo with
  | [] => seen
  | f :: r => if f ∈ seen then cloL p r seen else
    match p.lookup f with
    | some fd => cloL p (fd.body.callsL ++ r) (f :: seen)
    | none => cloL p r (f :: seen)
def allNames : List FnName := L.Checker.checkerProg.map (·.1)
def good (f : FnName) : Bool :=
  match L.Checker.checkerProg.lookup f with
  | some fd => fd.body.okW CTL leafA leafC allNames
  | none => true
#eval! do
  for f in (loopFns.filter fun f => (cloL L.Checker.checkerProg [f] []).all good).mergeSort do
    IO.println s!"FN {f}"
