module

public import ConAgua.Arena.CheckerT
public import ConAgua.Arena.IndT.CheckIndDecl
public import ConAgua.Arena.IndArmBridge2

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
variable {p : Prog} (hkp : KnotStageProg p) (hV : ValProg p)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p) (hLz : LzcF p)

include hkp hV hOpf hLC hLT hApd hCrk hIlpf hLz in
/-- **The inductive arm's contract** from `checkIndDecl_refinesC`, under its program facts. -/
theorem indArmSpec_of (P : CidProg p) {fs fs2 fsR fsT fsC fsH fsM fsMc : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs)
    (hfr : "block_raw_rec" ∈ fs) (hcl2 : closedA p hbFreeA hbFreeC fs2 = true)
    (hfs2 : ∀ f ∈ tailCallees, f ∈ fs2) (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (hclT : closedA p taFreeA taFreeC fsT = true)
    (hfT : ∀ f ∈ blockTaCallees, f ∈ fsT) (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC)
    (hkP : ∀ f ∈ passKeepCalleesC, AbsKeep p f) (hkt : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (hkr : AbsKeep p "block_raw_rec")
    (hfB : "check_basis_decl" ∈ fsC) (hfRc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR)
    (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true)
    (hfH : "check_block_tables" ∈ fsH) (hclM : closedA p maFreeA maFreeC fsM = true)
    (hfM : ∀ f ∈ ["check_block_pass", "check_block_tail"], f ∈ fsM)
    (hclMc : closedA p mcFreeA mcFreeC fsMc = true) (hfMc : "check_block" ∈ fsMc) :
    ∀ dn, DnInj dn → IndArmSpec p dn := by
  intro dn hdn pins n hn m m' a vis fe env block nP o l w r _ hw hdec hb _ hT _ hfold hden hlpd hM hc
  subst hw
  exact checkIndDecl_refinesC hkp hV hOpf hLC hLT hApd hCrk hIlpf hLz P hcl hfs hfr hcl2 hfs2 hclR hfR hclT hfT hclC hfC hkP
    hkt hkr hn hdn hc hT hfold (decB_decEBlk_of_decCIs hdec) hb hden hM hfB hfRc hclH hfH hclM hfM hclMc hfMc hlpd

end

end L.Ind
