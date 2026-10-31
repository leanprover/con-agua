import ConAgua.Arena.WhnfDeltaRefine4
import ConAgua.Arena.CoreNatOp
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
  have hC := hS.rel
  cases n with
  | zero => rw [reduceNatSuccE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [reduceNatSuccE.arm1]; unfold redSuccT
  refine RefE.bind_right (pinNatSucc_run hC.pins) ?_
  refine RefE.onlySim (fun _ => reduceNatSuccE.k_nat_lit_supported.none ..) (fun _ _ h => h) fun r₁ m₁ h1 => ?_
  rw [reduceNatSuccE.k_nat_lit_supported.arm1]
  have c1 := callW_natLitSupported p hp n s₀ a₀ dn vis fe MM eb hC r₁ m₁ h1
  refine RefE.bind_core (w := id) c1.core fun M₁ hS₁ _ => ?_
  refine RefE.onlySim (fun _ => reduceNatSuccE.k_pin_at.none ..) (fun _ _ h => h) fun r₂ m₂ h2 => ?_
  obtain ⟨rfl, -, -, hr₂⟩ := callW_pinAt p hp.pinAt n m₁ 3 r₂ m₂ h2
  have hcw : HW (pinW s₀.mem 4) := hC.pins.names_lt 3 (by decide)
  have hb₁ : ((decI c : NIdx) == decI (pinW s₀.mem 4) && decBool r₁) =
      decide (c = r₂.headD 0 ∧ r₁.headD 0 ≠ 0) := by
    rw [decI_beq _ _ hc hcw, hr₂, show (3 : Word).toNat = 3 from rfl,
      pinW_const_frame c1.2.2.2.1]
    simp only [decBool]; grind
  by_cases hgo : c = r₂.headD 0 ∧ r₁.headD 0 ≠ 0
  case neg =>
    rw [show reduceNatSuccE.k_pin_at p n mode vis d c b (r₁.headD 0) (.ok (r₂, m₂)) = .ok ([0, 0], m₂) by
      by_cases hcn : c ≠ r₂.headD 0
      · exact reduceNatSuccE.k_pin_at.arm1 _ _ _ _ _ _ _ _ _ _ hcn
      · exact reduceNatSuccE.k_pin_at.arm2 _ _ _ _ _ _ _ _ _ _ (Classical.not_not.mp hcn)
          (Classical.byContradiction fun h => hgo ⟨Classical.not_not.mp hcn, h⟩)]
    exact RefE.ite_neg (by rw [hb₁, decide_eq_false hgo]; decide) (RefE.ret rfl (CorePost.ret hS₁ rfl resW_zero))
  rw [reduceNatSuccE.k_pin_at.arm3 _ _ _ _ _ _ _ _ _ _ hgo.1 hgo.2]
  refine RefE.ite_pos (by rw [hb₁, decide_eq_true hgo]) ?_
  have hSP₁ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hS.mode4, hS.eb_mode⟩
  refine RefE.bind_callE (s₀ := ⟨m₂, Locals.init []⟩) (fun _ => reduceNatSuccE.k_whnf.none ..)
    ((hk n (by omega)).whnf F _ _ dn vis fe M₁ eb mode d b (by omega) (by omega) hSP₁ hb)
    (fun hkE => (hkE n (by omega)).whnf F _ _ dn vis fe M₁ eb mode d b (by omega) (by omega) hSP₁ hb)
    fun r₃ m₃ _ h3 => RefE.after_core (w := id) h3 fun M₃ hS₃ _ => ?_
  rw [reduceNatSuccE.k_whnf.arm1]
  refine RefE.onlySim (fun _ => reduceNatSuccE.k_raw_nat_lit.none ..) (fun _ _ h => h) fun r₄ m₄ h4 => ?_
  obtain ⟨rfl, hrun4, -, hslice4⟩ := callW_rawNatLit p hp n ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb _
    hS₃ h3.resOk r₄ m₄ h4
  refine RefE.bind_right hrun4 ?_
  by_cases hf : r₄.headD 0 = 0
  · rw [reduceNatSuccE.k_raw_nat_lit.arm1 _ _ _ _ hf, show rawDec m₄ r₄ = none by unfold rawDec; rw [ite_eq_left hf]]
    exact RefE.ret rfl (CorePost.ret hS₃ rfl resW_zero)
  rw [reduceNatSuccE.k_raw_nat_lit.arm2 _ _ _ _ hf, show rawDec m₄ r₄ = some (pv (vpool m₄)
    (r₄.tail.headD 0).toNat (r₄.tail.tail.headD 0).toNat) by unfold rawDec; rw [ite_eq_right hf]]
  refine RefE.onlySim (fun _ => reduceNatSuccE.k_nat_succ_lit.none ..) (fun _ _ h => h) fun r₅ m₅ h5 => ?_
  rw [reduceNatSuccE.k_nat_succ_lit.arm1]
  obtain ⟨hok5, hS5, hres5, hfr5, hhw5, hP5⟩ := callW_natSuccLit p hp n ⟨m₄, Locals.init []⟩ _ dn vis fe M₃ eb _ _
    hS₃ (hslice4 hf).1 r₅ m₅ h5
  refine RefE.bind_right (natAddArm_run_internE (v := 1) (by rw [AM.run_of_ok _ _ hok5, hres5])) ?_
  exact RefE.ret rfl ⟨⟨M₃, hS5, KeptAll.refl _ _, StackKept.of_nat_frame hfr5 hP5⟩,
    by simp [decOptR, decOpt], ⟨by unfold HW; simp, hhw5⟩⟩

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
  have hC := hS.rel
  have hC := hS.rel
  cases n with
  | zero => rw [reduceNatWfE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [reduceNatWfE.arm1]; unfold redWfT
  refine RefE.onlySim (fun _ => reduceNatWfE.k_nat_op_is_wf.none ..) (fun _ _ h => h) fun r₁ m₁ h1 => ?_
  rw [reduceNatWfE.k_nat_op_is_wf.arm1]
  obtain ⟨s₁', hs₁', hm₁, -, -, hwfsel, -⟩ := triple_of_callW
    (natOpIsWfL_spec p hp.natOpIsWf n ⟨s₀.mem, Locals.init []⟩ c) h1
  obtain rfl : m₁ = s₀.mem := by rw [← hs₁', hm₁]
  refine RefE.bind_right (natOpWfNames_run hC.pins) ?_
  refine RefE.onlySim (fun _ => reduceNatWfE.k_nat_lit_supported.none ..) (fun _ _ h => h) fun r₂ m₂ h2 => ?_
  refine RefE.bind_core (w := id) (callW_natLitSupported p hp n s₀ a₀ dn vis fe MM eb hC r₂ m₂ h2).core
    fun M₂ hS₂ _ => ?_
  have hb₂ : (([decI (pinW s₀.mem 22), decI (pinW s₀.mem 23), decI (pinW s₀.mem 24),
      decI (pinW s₀.mem 25), decI (pinW s₀.mem 26), decI (pinW s₀.mem 27), decI (pinW s₀.mem 28),
      decI (pinW s₀.mem 29)] : List NIdx).contains (decI c) && decBool r₂) =
      decide (r₁.headD 0 ≠ 0 ∧ r₂.headD 0 ≠ 0) := by
    rw [wfContains hC.pins c hc, ← hwfsel]; simp only [decBool]; grind
  by_cases hgo : r₁.headD 0 ≠ 0 ∧ r₂.headD 0 ≠ 0
  case neg =>
    rw [show reduceNatWfE.k_nat_lit_supported p n mode vis d a b (r₁.headD 0) (.ok (r₂, m₂)) =
        reduceNatWfE.j1 p m₂ by
      by_cases h1 : r₁.headD 0 = 0
      · exact reduceNatWfE.k_nat_lit_supported.arm3 _ _ _ _ _ _ _ _ _ _ h1
      · exact reduceNatWfE.k_nat_lit_supported.arm2 _ _ _ _ _ _ _ _ _ _ h1
          (Classical.byContradiction fun h2 => hgo ⟨h1, h2⟩), reduceNatWfE.j1]
    exact RefE.ite_neg (by rw [hb₂, decide_eq_false hgo]; decide) (RefE.ret rfl (CorePost.ret hS₂ rfl resW_zero))
  rw [reduceNatWfE.k_nat_lit_supported.arm1 _ _ _ _ _ _ _ _ _ _ hgo.1 hgo.2]
  refine RefE.ite_pos (by rw [hb₂, decide_eq_true hgo]) ?_
  have hSP₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hS.mode4, hS.eb_mode⟩
  refine RefE.bind_callE (s₀ := ⟨m₂, Locals.init []⟩) (fun _ => reduceNatWfE.k_whnf.none ..)
    ((hk n (by omega)).whnf F _ _ dn vis fe M₂ eb mode d a (by omega) (by omega) hSP₂ ha)
    (fun hkE => (hkE n (by omega)).whnf F _ _ dn vis fe M₂ eb mode d a (by omega) (by omega) hSP₂ ha)
    fun r₃ m₃ _ h3 => RefE.after_core (w := id) h3 fun M₃ hS₃ _ => ?_
  rw [reduceNatWfE.k_whnf.arm1]
  refine RefE.onlySim (fun _ => reduceNatWfE.k_raw_nat_lit.none ..) (fun _ _ h => h) fun r₄ m₄ h4 => ?_
  obtain ⟨rfl, hrun4, -, -⟩ := callW_rawNatLit p hp n ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb _
    hS₃ h3.resOk r₄ m₄ h4
  refine RefE.bind_right hrun4 ?_
  by_cases hf4 : r₄.headD 0 = 0
  · rw [reduceNatWfE.k_raw_nat_lit.arm2 _ _ _ _ _ _ _ _ hf4, reduceNatWfE.j1,
      show rawDec m₄ r₄ = none by unfold rawDec; rw [ite_eq_left hf4]]
    exact RefE.ret rfl (CorePost.ret hS₃ rfl resW_zero)
  rw [reduceNatWfE.k_raw_nat_lit.arm1 _ _ _ _ _ _ _ _ hf4, show rawDec m₄ r₄ = some (pv (vpool m₄)
    (r₄.tail.headD 0).toNat (r₄.tail.tail.headD 0).toNat) by unfold rawDec; rw [ite_eq_right hf4]]
  have hSP₄ : SlotPre ⟨m₄, Locals.init []⟩ _ dn vis fe M₃ eb mode := ⟨hS₃, hS.mode4, hS.eb_mode⟩
  refine RefE.bind_callE (s₀ := ⟨m₄, Locals.init []⟩) (fun _ => reduceNatWfE.k_whnf_2.none ..)
    ((hk n (by omega)).whnf F _ _ dn vis fe M₃ eb mode d b (by omega) (by omega) hSP₄ hb)
    (fun hkE => (hkE n (by omega)).whnf F _ _ dn vis fe M₃ eb mode d b (by omega) (by omega) hSP₄ hb)
    fun r₅ m₅ _ h5 => RefE.after_core (w := id) h5 fun M₅ hS₅ _ => ?_
  rw [reduceNatWfE.k_whnf_2.arm1]
  refine RefE.onlySim (fun _ => reduceNatWfE.k_raw_nat_lit_2.none ..) (fun _ _ h => h) fun r₆ m₆ h6 => ?_
  obtain ⟨rfl, hrun6, -, -⟩ := callW_rawNatLit p hp n ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb _
    hS₅ h5.resOk r₆ m₆ h6
  refine RefE.bind_right hrun6 ?_
  by_cases hf6 : r₆.headD 0 = 0
  · rw [reduceNatWfE.k_raw_nat_lit_2.arm1 _ _ _ hf6, reduceNatWfE.j1,
      show rawDec m₆ r₆ = none by unfold rawDec; rw [ite_eq_left hf6]]
    exact RefE.ret rfl (CorePost.ret hS₅ rfl resW_zero)
  rw [reduceNatWfE.k_raw_nat_lit_2.abort1 _ _ _ hf6, show rawDec m₆ r₆ = some (pv (vpool m₆)
    (r₆.tail.headD 0).toNat (r₆.tail.tail.headD 0).toNat) by unfold rawDec; rw [ite_eq_right hf6]]
  exact fun _ => ErrClaim.fail _ _ rfl

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
  have hC := hS.rel
  cases n with
  | zero => rw [reduceNatApE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [reduceNatApE.eq_2]
  refine RefE.abort0 (by simp) fun hbd => ?_
  obtain ⟨hviewf, hgw, hxw⟩ := view_app s₀.mem a₀ hC.arena.base f hf ⟨hsc, by simpa using hbd⟩ hg4
  generalize tfld s₀.mem APP (tierW f) (idxW f) 0 = gw at hgw hviewf ⊢
  generalize tfld s₀.mem APP (tierW f) (idxW f) 1 = xw at hxw hviewf ⊢
  unfold redHeadT redAppT
  refine RefE.bind_right (view_run _ _ _ hviewf) ?_
  refine RefE.retIf (fun g3 => by rw [decE_const_tag _ hgw]; exact beq_eq_false_iff_ne.mpr g3)
    (fun ht => by rw [decE_const_tag _ hgw] at ht; simpa using ht) (fun _ => CorePost.ret hC rfl resW_zero)
    fun g3 _ => ?_
  refine RefE.abort0 (by simp) fun hs2 => ?_
  refine RefE.abort0 (by simp) fun hb2 => ?_
  obtain ⟨n_, us_, hview, rfl, rfl, hnl, hul⟩ := view_const_words s₀.mem a₀ hC.arena.base _ hgw
    ⟨hs2, by simpa using hb2⟩ (by simpa using g3)
  generalize tfld s₀.mem CONST (tierW gw) (idxW gw) 0 = cw at *
  generalize tfld s₀.mem CONST (tierW gw) (idxW gw) 1 = uw at *
  refine RefE.bind_right (view_run _ _ _ hview) ?_
  refine RefE.onlySim (fun _ => reduceNatApE.k_pin_word.none ..) (fun _ _ h => h) fun r₁ m₁ h1 => ?_
  obtain ⟨rfl, hflag, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₁ m₁ h1
  refine RefE.bind_right (pinEmptyLevels_run hC.pins) ?_
  have hb₁ : ((decI uw : LsIdx) != decI (pinW s₀.mem 52)) = !decide (uw = r₁.headD 0) := by
    rw [hr₁]; simp only [bne, decI_beq _ _ hul hC.pins.lv_lt.1]; rfl
  by_cases hne : uw ≠ r₁.headD 0
  · rw [reduceNatApE.k_pin_word.arm1 _ _ _ _ _ _ _ _ _ _ _ hne]
    exact RefE.ite_pos (by rw [hb₁, decide_eq_false hne]; rfl) (RefE.ret rfl (CorePost.ret hC rfl resW_zero))
  rw [reduceNatApE.k_pin_word.arm2 _ _ _ _ _ _ _ _ _ _ _ (by simpa using hne)]
  refine RefE.ite_neg (by rw [hb₁]; simpa using hne) ?_
  unfold redBinT
  refine RefE.onlySim (fun _ => reduceNatApE.k_nat_bin_op_name.none ..) (fun _ _ h => h) fun r₂ m₂ h2 => ?_
  rw [reduceNatApE.k_nat_bin_op_name.arm1]
  obtain ⟨t₂, ht₂, hm₂, -, hsel2, -⟩ := triple_of_callW
    (natBinOpNameL_spec p hp.natBinOpName n ⟨s₀.mem, Locals.init []⟩ hflag cw) h2
  obtain rfl : m₂ = s₀.mem := by rw [← ht₂, hm₂]
  refine RefE.bind_right (natBinOpName_run hC.pins cw hnl) ?_
  refine RefE.onlySim (fun _ => reduceNatApE.k_nat_op_stored.none ..) (fun _ _ h => h) fun r₃ m₃ h3 => ?_
  refine RefE.bind_core (w := id) (callW_natOpStored p hp n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe
    MM eb cw hC hnl r₃ m₃ h3).core fun M₃ hS₃ _ => ?_
  have hSP₃ : SlotPre ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode := ⟨hS₃, hS.mode4, hS.eb_mode⟩
  have hbool : (natBinOpSel (pinW s₀.mem) cw && decBool r₃) = decide (r₂.headD 0 ≠ 0 ∧ r₃.headD 0 ≠ 0) := by
    rw [← hsel2]; exact bne_and_bne _ _
  by_cases hgo : r₂.headD 0 ≠ 0 ∧ r₃.headD 0 ≠ 0
  · rw [reduceNatApE.k_nat_op_stored.arm1 _ _ _ _ _ _ _ _ _ _ _ hgo]
    refine RefE.ite_pos (by rw [hbool, decide_eq_true hgo]) ?_
    exact RefE.tail_eq (reduceNatApE.k_reduce_nat_op.none p) (fun v => reduceNatApE.k_reduce_nat_op.arm1 p v.1 v.2)
      (fun h => h.mono (by omega)) rfl (CorePost.relist (MemFrame.refl _ _ _))
      (reduceNatOp_ref p hp hno n F (by omega) (by omega) (hk.mono (by omega))
        ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode d cw xw b hSP₃ hnl hxw hb)
  · rw [reduceNatApE.k_nat_op_stored.arm2 _ _ _ _ _ _ _ _ _ _ _ hgo]
    refine RefE.ite_neg (by rw [hbool, decide_eq_false hgo]; decide) ?_
    exact RefE.tail_eq (reduceNatApE.k_reduce_nat_op.none p) (fun v => reduceNatApE.k_reduce_nat_op.arm1 p v.1 v.2)
      (fun h => h.mono (by omega)) rfl (CorePost.relist (MemFrame.refl _ _ _))
      (reduceNatWf_ref p hp n F (by omega) (by omega) (hk.mono (by omega))
        ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode d cw xw b hSP₃ hnl hxw hb)

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
  have hC := hS.rel
  cases n with
  | zero => rw [reduceNatHeadE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [reduceNatHeadE.eq_2]
  refine RefE.abort0 (by simp) fun hsc => ?_
  -- the tags that only check a bound
  have simple : ∀ (c : TRec), (tagW f = 0 ∧ c = BVAR) ∨ (tagW f = 1 ∧ c = FVAR) ∨
      (tagW f = 2 ∧ c = SORT) ∨ (tagW f = 5 ∧ c = LAM) ∨ (tagW f = 6 ∧ c = FORALL) ∨
      (tagW f = 7 ∧ c = LET) ∨ (tagW f = 8 ∧ c = LIT) ∨ (tagW f = 9 ∧ c = PROJ) →
      RefE (KnotUpToE p (n + 1)) (if tcnt s₀.mem c (tierW f) ≤ idxW f then .error (Err.abort 0) else
        .ok ([0, 0], s₀.mem))
        (redHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b)) a₀
        (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
    intro c hcg
    refine RefE.abort0 (by simp) fun hbd => ?_
    obtain ⟨v, hv, hc, hp'⟩ := view_nca s₀.mem a₀ hC.arena.base f hf c ⟨hsc, by simpa using hbd⟩ hcg
    unfold redHeadT
    refine RefE.bind_right (view_run _ _ _ hv) ?_
    cases v with
    | const c us => exact absurd rfl (hc c us)
    | app g x => exact absurd rfl (hp' g x)
    | _ => exact RefE.ret rfl (CorePost.ret hC rfl resW_zero)
  have hmono : KnotUpToE p (n + 1) → KnotUpToE p n := fun h => h.mono (by omega)
  by_cases g3 : tagW f = 3
  · rw [ite_eq_left g3]
    exact RefE.tail_eq (reduceNatHeadE.k_reduce_nat_k.none p)
      (fun v => reduceNatHeadE.k_reduce_nat_k.arm1 p v.1 v.2) hmono rfl
      (CorePost.relist (MemFrame.refl _ _ _))
      (reduceNatK_ref p hp n F (by omega) (by omega) (hk.mono (by omega)) s₀ a₀ dn vis fe MM eb mode d f b
        hS hf hb g3 hsc)
  rw [ite_eq_right g3]
  by_cases g4 : tagW f = 4
  · rw [ite_eq_left g4]
    exact RefE.tail_eq (reduceNatHeadE.k_reduce_nat_k.none p)
      (fun v => reduceNatHeadE.k_reduce_nat_k.arm1 p v.1 v.2) hmono rfl
      (CorePost.relist (MemFrame.refl _ _ _))
      (reduceNatAp_ref p hp hno n F (by omega) (by omega) (hk.mono (by omega)) s₀ a₀ dn vis fe MM eb mode d
        f b hS hf hb g4 hsc)
  rw [ite_eq_right g4]
  by_cases g0 : tagW f = 0
  · rw [ite_eq_left g0]; exact simple BVAR (Or.inl ⟨g0, rfl⟩)
  rw [ite_eq_right g0]
  by_cases g1 : tagW f = 1
  · rw [ite_eq_left g1]; exact simple FVAR (Or.inr (Or.inl ⟨g1, rfl⟩))
  rw [ite_eq_right g1]
  by_cases g2 : tagW f = 2
  · rw [ite_eq_left g2]; exact simple SORT (Or.inr (Or.inr (Or.inl ⟨g2, rfl⟩)))
  rw [ite_eq_right g2]
  by_cases g5 : tagW f = 5
  · rw [ite_eq_left g5]; exact simple LAM (Or.inr (Or.inr (Or.inr (Or.inl ⟨g5, rfl⟩))))
  rw [ite_eq_right g5]
  by_cases g6 : tagW f = 6
  · rw [ite_eq_left g6]; exact simple FORALL (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g6, rfl⟩)))))
  rw [ite_eq_right g6]
  by_cases g7 : tagW f = 7
  · rw [ite_eq_left g7]
    exact simple LET (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g7, rfl⟩))))))
  rw [ite_eq_right g7]
  by_cases g8 : tagW f = 8
  · rw [ite_eq_left g8]
    exact simple LIT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g8, rfl⟩)))))))
  rw [ite_eq_right g8]
  refine RefE.abort0 (by simp) fun g9 => ?_
  exact simple PROJ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by simpa using g9, rfl⟩)))))))

include hp in
/-- **`reduce_nat` refines `reduceNat`, both outcomes** (the errors are `reduce_nat_head`'s). -/
theorem reduceNat_ref (hno : NatOpResultOK p) (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d e : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (he : HW e) :
    RefE (KnotUpToE p n) (reduceNatE p n s₀.mem mode vis d e)
      (reduceNat (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  have hC := hS.rel
  cases n with
  | zero => rw [reduceNatE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [reduceNatE.eq_2]; unfold reduceNat
  have hap : ((decE e).tag == ETag.app) = (tagW e == 4) := by
    by_cases g : tagW e = 4
    · have := (decE_tag_app e he).mpr g
      rw [beq_iff_eq.mpr this, beq_iff_eq.mpr g]
    · have : ¬ (decE e).tag = ETag.app := fun h' => g ((decE_tag_app e he).mp h')
      rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr g]
  refine RefE.retIf (fun g4 => by rw [hap]; exact beq_eq_false_iff_ne.mpr g4) (fun h => by simpa [hap] using h)
    (fun _ => CorePost.ret hC rfl resW_zero) fun g4 _ => ?_
  refine RefE.abort0 (by simp) fun hsc => ?_
  refine RefE.abort0 (by simp) fun hbd => ?_
  obtain ⟨hview, hfw, hbw⟩ := view_app s₀.mem a₀ hC.arena.base e he ⟨hsc, by simpa using hbd⟩
    (by simpa using g4)
  refine RefE.bind_right (view_run _ _ _ hview) ?_
  exact RefE.tail_eq (reduceNatE.k_reduce_nat_head.none p)
    (fun v => reduceNatE.k_reduce_nat_head.arm1 p v.1 v.2) (fun h => h.mono (by omega)) rfl
    (CorePost.relist (MemFrame.refl _ _ _))
    (reduceNatHead_ref p hp hno n F (by omega) (by omega) (hk.mono (by omega)) s₀ a₀ dn vis fe MM eb mode d
      _ _ hS hfw hbw)

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
theorem reduceNat_refines (n : Nat) : ReduceNatSpec' p n :=
  reduceNat_refines' p hp (natOpResultOK_of_agree hp.natAgree) n

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
