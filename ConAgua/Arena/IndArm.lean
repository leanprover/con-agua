module

public import ConAgua.Arena.IndT.CheckIndDecl
public import ConAgua.Arena.DeclCheckT

@[expose] public section

/-!
# The inductive arm's contract from `checkIndDecl_refinesC` (lane `indproofs4`)

`IndArmSpec p dn` (`CheckerT.lean`) from `checkIndDecl_refinesC` (the ok half of `cid_ref`), the
front's block decoding is the stage's (`decB_decEBlk_of_decCIs`). The program facts it takes (the lookups `CidProg`, the
callees' write sets, the `AbsKeep` facts) are this theorem's hypotheses; `Checker/IndArm.lean`
discharges them at the checker's program.
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

/-- **`AbsKeep` from a write set** that leaves the walk memos alone. -/
theorem absKeep_of_closed {p : Prog} {A : List TieredArray} {C : List Word} {fs : List FnName}
    (hcl : closedA p A C fs = true) (hA : memoFreeA A = true) (hC : memoFreeC C = true)
    {f : FnName} (hf : f ∈ fs) : AbsKeep p f :=
  fun _ _ _ _ _ h => AFr.of_frame (run_memFrame hcl hf (run_of_callW h)).1 hA hC

section
variable {p : Prog}

/-- **The inductive arm's contract** from `checkIndDecl_refinesC`, under its program facts and
the contract of its returning callee (`check_block`: `BlockRefS`, the error half under
`VerdictCtxU`). -/
theorem indArmSpec_of (P : CidProg2 p) (hbr : ∀ dn, DnInj dn → BlockRefS (VerdictCtxU p) p dn)
    {fsC : List FnName} (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC) :
    ∀ dn, DnInj dn → IndArmSpec p dn := by
  intro dn hdn pins n hn m m' a vis fe env block nP o l w r _ hw hdec hb _ hT _ hfold hden hlpd _ hM hc
  subst hw
  exact checkIndDecl_refinesC P (hbr dn hdn) hclC hfC hn hc hT hfold hdec hb hden hM hlpd

end

end L.Ind
