module

public import ConAgua.Arena.WhnfDeltaRefine4
import ConAgua.Arena.CoreNatOp
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WhnfDeltaRefine2
import ConAgua.L.LocNF
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.KnotE
public import ConAgua.Arena.RefECore
public import ConAgua.Verdict.WhnfModels2E

@[expose] public section
/-!
# `reduce_nat`'s family: one model and one refinement for both outcomes

`reduceNatSuccE` … `reduceNatE` (`l_model … unified`, `WhnfModels2E`): the `whnf` slot through its
run (`callE`), the family's own callees through their unified models, every other callee (outside
the verdict closure) through its `Option` model. Each `…_ref` refines the twin's arm for both
outcomes (`RefE` with `CorePost`): the errors claim the twin's failures under the `whnf` slot's
claims (`KnotUpToE`); `reduce_nat_wf`'s safety net declines on two literals (`redWfT`). The ok
halves are `ReduceNatSpec'` (`reduceNat_refines`), the error half `ReduceNatE` (`reduceNatE_of`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem resW_zero : ResW [0, 0] := by unfold ResW HW; exact ⟨by decide, by decide⟩

/-- The callee's first two result words, after a run of constant frame (the caller's result). -/
theorem CorePost.relist {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {vis : Word} {fe : IFEnv}
    {MM : ModeMaps} {eb : Word}
    (hfr : MemFrame [CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP] [18, 19] m₀ m₁)
    (v : List Word × Mem) (y : Option EIdx) (a' : AState)
    (h : CorePost decOptR dn m₁ vis fe MM eb ResW v y a') :
    CorePost decOptR dn m₀ vis fe MM eb ResW ([v.1.headD 0, v.1.tail.headD 0], v.2) y a' :=
  ⟨CoreAfter.comp (KeptAll.refl _ _) (StackKept.of_const_frame hfr) h.after, h.res, h.valid⟩

section refs
variable (p : Prog) (hp : WhnfDeltaProg' p)

include hp in
/-- **`reduce_nat_succ` refines `redSuccT`, both outcomes**: the errors are the argument's head
normalization's. -/
theorem reduceNatSucc_ref (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d c b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hc : HW c) (hb : HW b) :
    RefE (KnotUpToE p n) (reduceNatSuccE p n s₀.mem mode vis d c b)
      (redSuccT (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE b)) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  sorry

include hp in
/-- **`reduce_nat_op` refines `redOpT`, both outcomes**: the errors are the operands' head
normalizations'. -/
theorem reduceNatOp_ref (hno : NatOpResultOK p) (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d c a b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hc : HW c) (ha : HW a) (hb : HW b) :
    RefE (KnotUpToE p n) (reduceNatOpE p n s₀.mem mode vis d c a b)
      (redOpT (coreKnot (decMode mode) fe id F) d.toNat (decI c) (decE a) (decE b)) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  cases n with
  | zero => rw [reduceNatOpE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [reduceNatOpE.arm1]; unfold redOpT
  refine RefE.bind_callE (s₀ := s₀) (fun _ => reduceNatOpE.k_whnf.none ..)
    ((hk n (by omega)).whnf F _ _ dn vis fe MM eb mode d a (by omega) (by omega) hS ha)
    (fun hkE => (hkE n (by omega)).whnf F _ _ dn vis fe MM eb mode d a (by omega) (by omega) hS ha)
    fun r₁ m₁ _ h1 => RefE.after_core (w := id) h1 fun M₁ hS₁ _ => ?_
  rw [reduceNatOpE.k_whnf.arm1]
  refine RefE.onlySim (fun _ => reduceNatOpE.k_raw_nat_lit.none ..) (fun _ _ h => h) fun r₂ m₂ h2 => ?_
  obtain ⟨rfl, hrun2, -, hslice2⟩ := callW_rawNatLit p hp n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb _
    hS₁ h1.resOk r₂ m₂ h2
  refine RefE.bind_right hrun2 ?_
  by_cases hf2 : r₂.headD 0 = 0
  · rw [reduceNatOpE.k_raw_nat_lit.arm1 _ _ _ _ _ _ _ _ _ hf2,
      show rawDec m₂ r₂ = none by unfold rawDec; rw [ite_eq_left hf2]]
    exact RefE.ret rfl (CorePost.ret hS₁ rfl resW_zero)
  rw [reduceNatOpE.k_raw_nat_lit.arm2 _ _ _ _ _ _ _ _ _ hf2, show rawDec m₂ r₂ = some (pv (vpool m₂)
    (r₂.tail.headD 0).toNat (r₂.tail.tail.headD 0).toNat) by unfold rawDec; rw [ite_eq_right hf2]]
  have hSP₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hS.mode4, hS.eb_mode⟩
  refine RefE.bind_callE (s₀ := ⟨m₂, Locals.init []⟩) (fun _ => reduceNatOpE.k_whnf_2.none ..)
    ((hk n (by omega)).whnf F _ _ dn vis fe M₁ eb mode d b (by omega) (by omega) hSP₂ hb)
    (fun hkE => (hkE n (by omega)).whnf F _ _ dn vis fe M₁ eb mode d b (by omega) (by omega) hSP₂ hb)
    fun r₃ m₃ _ h3 => RefE.after_core (w := id) h3 fun M₃ hS₃ hSt₃ => ?_
  rw [reduceNatOpE.k_whnf_2.arm1]
  refine RefE.onlySim (fun _ => reduceNatOpE.k_raw_nat_lit_2.none ..) (fun _ _ h => h) fun r₄ m₄ h4 => ?_
  obtain ⟨rfl, hrun4, -, hslice4⟩ := callW_rawNatLit p hp n ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb _
    hS₃ h3.resOk r₄ m₄ h4
  refine RefE.bind_right hrun4 ?_
  by_cases hf4 : r₄.headD 0 = 0
  · rw [reduceNatOpE.k_raw_nat_lit_2.arm1 _ _ _ _ _ _ _ hf4,
      show rawDec m₄ r₄ = none by unfold rawDec; rw [ite_eq_left hf4]]
    exact RefE.ret rfl (CorePost.ret hS₃ rfl resW_zero)
  rw [reduceNatOpE.k_raw_nat_lit_2.arm2 _ _ _ _ _ _ _ hf4, show rawDec m₄ r₄ = some (pv (vpool m₄)
    (r₄.tail.headD 0).toNat (r₄.tail.tail.headD 0).toNat) by unfold rawDec; rw [ite_eq_right hf4]]
  obtain ⟨hsl2', hpv2, hnorm2'⟩ := hSt₃.pool.slice (hslice2 hf2).1 (hslice2 hf2).2
  rw [← hpv2]
  refine RefE.onlySim (fun _ => reduceNatOpE.k_nat_op_result.none ..) (fun _ _ h => h) fun r₅ m₅ h5 => ?_
  rw [reduceNatOpE.k_nat_op_result.arm1]
  obtain ⟨hrun5, hP5⟩ := (CoreSpec.of_callW (hno n ⟨m₄, Locals.init []⟩ _ dn vis fe M₃ eb c _ _ _ _ hS₃ hc
    hsl2' (hslice4 hf4).1 hnorm2' (hslice4 hf4).2) h5).post
  exact RefE.ret hrun5 ⟨hP5.after, (by rw [hP5.res]; simp only [decOptR, id, List.headD_cons,
    List.tail_cons, decOpt_norm]), resW_norm _ _⟩

include hp in
/-- **`reduce_nat_wf` refines `redWfT`, both outcomes**: two literals decline (the twin's safety
net), the other errors are the operands' head normalizations'. -/
theorem reduceNatWf_ref (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d c a b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hc : HW c) (ha : HW a) (hb : HW b) :
    RefE (KnotUpToE p n) (reduceNatWfE p n s₀.mem mode vis d c a b)
      (redWfT (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE a) (decE b)) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  sorry

include hp in
/-- **`reduce_nat_k` refines `redHeadT` at a constant head, both outcomes** (`redConstT`; the
errors are `reduce_nat_succ`'s). -/
theorem reduceNatK_ref (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hf : HW f) (hb : HW b) (hg3 : tagW f = 3)
    (hsc : ¬(tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0)) :
    RefE (KnotUpToE p n) (reduceNatKE p n s₀.mem mode vis d f b)
      (redHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b)) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  have hC := hS.rel
  cases n with
  | zero => rw [reduceNatKE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  by_cases hbd : tcnt s₀.mem CONST (tierW f) ≤ idxW f
  · rw [reduceNatKE.abort1 _ _ _ _ _ _ _ _ hbd]; exact RefE.of_cls0 (by simp)
  rw [reduceNatKE.arm1 _ _ _ _ _ _ _ _ hbd]
  obtain ⟨n_, us_, hview, rfl, rfl, hnl, hul⟩ :=
    view_const_words s₀.mem a₀ hC.arena.base f hf ⟨hsc, by simpa using hbd⟩ hg3
  generalize tfld s₀.mem CONST (tierW f) (idxW f) 1 = uw at *
  unfold redHeadT redConstT
  refine RefE.bind_right (view_run _ _ _ hview) ?_
  refine RefE.onlySim (fun _ => reduceNatKE.k_pin_word.none ..) (fun _ _ h => h) fun r₁ m₁ h1 => ?_
  obtain ⟨rfl, -, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₁ m₁ h1
  refine RefE.bind_right (pinEmptyLevels_run hC.pins) ?_
  have hb₁ : ((decI uw : LsIdx) != decI (pinW s₀.mem 52)) = !decide (uw = r₁.headD 0) := by
    rw [hr₁]; simp only [bne, decI_beq _ _ hul hC.pins.lv_lt.1]; rfl
  by_cases hne : uw ≠ r₁.headD 0
  · rw [reduceNatKE.k_pin_word.arm1 _ _ _ _ _ _ _ _ _ _ hne]
    exact RefE.ite_pos (by rw [hb₁, decide_eq_false hne]; rfl) (RefE.ret rfl (CorePost.ret hC rfl resW_zero))
  rw [reduceNatKE.k_pin_word.arm2 _ _ _ _ _ _ _ _ _ _ (by simpa using hne)]
  refine RefE.ite_neg (by rw [hb₁]; simpa using hne) ?_
  exact RefE.tail_eq (reduceNatKE.k_reduce_nat_succ.none p) (fun v => reduceNatKE.k_reduce_nat_succ.arm1 p v.1 v.2)
    (fun h => h.mono (by omega)) rfl (CorePost.relist (MemFrame.refl _ _ _))
    (reduceNatSucc_ref p hp n F (by omega) (by omega) (hk.mono (by omega)) s₀ a₀ dn vis fe MM eb mode d _ b hS
      hnl hb)

include hp in
/-- **`reduce_nat_ap` refines `redHeadT` at an application head, both outcomes** (`redAppT`; the
errors are `reduce_nat_op`'s or `reduce_nat_wf`'s). -/
theorem reduceNatAp_ref (hno : NatOpResultOK p) (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hf : HW f) (hb : HW b) (hg4 : tagW f = 4)
    (hsc : ¬(tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0)) :
    RefE (KnotUpToE p n) (reduceNatApE p n s₀.mem mode vis d f b)
      (redHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b)) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  sorry

include hp in
/-- **`reduce_nat_head` refines `redHeadT`, both outcomes** (the errors are `reduce_nat_k`'s or
`reduce_nat_ap`'s). -/
theorem reduceNatHead_ref (hno : NatOpResultOK p) (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hf : HW f) (hb : HW b) :
    RefE (KnotUpToE p n) (reduceNatHeadE p n s₀.mem mode vis d f b)
      (redHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b)) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  sorry

include hp in
/-- **`reduce_nat` refines `reduceNat`, both outcomes** (the errors are `reduce_nat_head`'s). -/
theorem reduceNat_ref (hno : NatOpResultOK p) (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d e : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (he : HW e) :
    RefE (KnotUpToE p n) (reduceNatE p n s₀.mem mode vis d e)
      (reduceNat (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  sorry

end refs

/-! ## The halves -/

section halves
variable (p : Prog) (hp : WhnfDeltaProg' p)

include hp in
/-- **`reduce_nat` refines `reduceNat`** (`reduceNat_ref`'s ok half; the statement of
`reduceNat_refines`, with the fuel bound `n ≤ 2 ^ 62` the knot's `whnf` slot needs, and the
program/stub hypotheses explicit). -/
theorem reduceNat_refines' (hno : NatOpResultOK p) (n : Nat) : ReduceNatSpec' p n :=
  fun F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hS he hk =>
    RefE.coreSpec (reduceNatE_spec p hp.toWhnfDeltaProg n s₀ mode vis d e)
      (reduceNat_ref p hp hno n F hF hn2 hk s₀ a₀ dn vis fe MM eb mode d e hS he)

include hp in
@[refines ConRon.Arena.reduceNat]
theorem reduceNat_refines (n : Nat) : ReduceNatSpec' p n := by
  sorry

/-- `reduce_nat`'s error claim at fuel `N` (the ok side's `ReduceNatSpec'` shape). -/
def ReduceNatE (p : Prog) : Prop :=
  ∀ N, KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d e : Word), N ≤ F → N ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode → HW e →
    CoreSpecE p N "reduce_nat" [mode, vis, d, e]
      (reduceNat (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) s₀ a₀

include hp in
/-- **`ReduceNatE`**: `reduce_nat`'s error claim (`reduceNat_ref`'s error half), the `whnf_step`
slot body's hypothesis. -/
theorem reduceNatE_of (hnv : closedNV p L.Checker.nvFns = true) : ReduceNatE p :=
  fun N hk hkE F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he =>
    RefE.coreSpecE (reduceNatE_spec p hp.toWhnfDeltaProg N s₀ mode vis d e) hnv hkE
      (reduceNat_ref p hp (natOpResultOK_of_agree hp.natAgree) N F hF hn hk s₀ a₀ dn vis fe MM eb
        mode d e hs he)

end halves

end L.Arena
