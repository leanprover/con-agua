import ConAgua.Checker.Prog

/-!
# The parallel mode's owned arrays, checked against the program (lane parmode)

`parOwned` (`Arena/Freeze.lean`) lists the word arrays entry 2 gives memory in the worker region.
Here: every word array that a function in `check_b`'s call closure (in `checkerProg`) names is
frozen or owned. (Nothing proved depends on it: an array with no memory is out of bounds, an
error; the check keeps the parallel mode from failing on an array the list forgot.)
-/

namespace L.Checker

open L L.Arena

partial def parArrsE : Expr → List ArrId
  | .bin _ a b | .cmpw _ a b => parArrsE a ++ parArrsE b
  | .ld8 _ i | .ldc _ i | .ld8x8 _ i => parArrsE i
  | .ld64 a i => a :: parArrsE i
  | .len64 a => [a]
  | .ld64t a t i => a :: (tier1 a) :: parArrsE t ++ parArrsE i
  | .len64t a t => a :: (tier1 a) :: parArrsE t
  | _ => []

partial def parArrsC : Cond → List ArrId
  | .cmp _ a b => parArrsE a ++ parArrsE b
  | .and p q | .or p q => parArrsC p ++ parArrsC q
  | .not p => parArrsC p

def parWArr : WArr → List ArrId
  | .plain a => [a]
  | .tier a _ => [a, tier1 a]

partial def parArrsS : Stmt → List ArrId
  | .seq s t => parArrsS s ++ parArrsS t
  | .ite c s t => parArrsC c ++ parArrsS s ++ parArrsS t
  | .while c s => parArrsC c ++ parArrsS s
  | .set _ e | .gset _ e => parArrsE e
  | .st8 _ i e => parArrsE i ++ parArrsE e
  | .st64 a i e => a :: parArrsE i ++ parArrsE e
  | .st64t a t i e => a :: (tier1 a) :: parArrsE t ++ parArrsE i ++ parArrsE e
  | .ret es | .call _ _ es => es.flatMap parArrsE
  | .copy64 d di s si n => parWArr d ++ parWArr s ++ parArrsE di ++ parArrsE si ++ parArrsE n
  | .copy8w d di _ si n => parWArr d ++ parArrsE di ++ parArrsE si ++ parArrsE n
  | .scan8 _ _ i e _ => parArrsE i ++ parArrsE e
  | _ => []

partial def parCalls : Stmt → List FnName
  | .seq s t | .ite _ s t => parCalls s ++ parCalls t
  | .while _ s => parCalls s
  | .call _ f _ => [f]
  | _ => []

partial def parClosure (p : Prog) : List FnName → List FnName → List FnName
  | [], seen => seen
  | f :: r, seen => if f ∈ seen then parClosure p r seen else
    match p.lookup f with
    | some fd => parClosure p (parCalls fd.body ++ r) (f :: seen)
    | none => parClosure p r (f :: seen)

/-- The word arrays phase B names that are neither frozen nor owned (must be none). -/
def parMissing : List ArrId :=
  ((parClosure checkerProg ["check_b"] []).flatMap fun f =>
    match checkerProg.lookup f with | some fd => parArrsS fd.body | none => []).eraseDups.filter
    fun a => !(frozenIds.contains a) && !(parOwned.contains a)

#guard parMissing == []

end L.Checker
