import ConAgua.Verdict.WhnfModels2E
import ConAgua.Arena.WhnfDeltaRefine4
import ConAgua.Arena.KnotE
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

theorem resW_00 : ResW [0, 0] := by unfold ResW HW; exact ⟨by decide, by decide⟩

/-! ## The twin's failing runs of the arms -/

section redruns
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat)

theorem redSucc_err (c : NIdx) (b : EIdx) (s s₁ : AState) (m : Mem)
    (hP : PinsFull m s.pins) (sup : Bool) (hs : (natLitSupported fe).run s = .ok (sup, s₁))
    (hc : (c == decI (pinW m 4) && sup) = true) (ce : CheckError)
    (hw : (r.whnf depth b).run s₁ = .error ce) :
    (redSuccT r fe depth c b).run s = .error ce := by
  simp only [redSuccT, StateT.run_bind, pinNatSucc_run hP, except_ok_bind, hs, hc, ite_true, hw]; rfl

theorem redOp_err_a (c : NIdx) (a b : EIdx) (s : AState) (ce : CheckError)
    (hw : (r.whnf depth a).run s = .error ce) : (redOpT r depth c a b).run s = .error ce := by
  simp only [redOpT, StateT.run_bind, hw]; rfl

theorem redOp_err_b (c : NIdx) (a b : EIdx) (s s₁ s₂ : AState) (wa : EIdx) (N : Nat)
    (hw : (r.whnf depth a).run s = .ok (wa, s₁)) (hr : (rawNatLit? wa).run s₁ = .ok (some N, s₂))
    (ce : CheckError) (hw2 : (r.whnf depth b).run s₂ = .error ce) :
    (redOpT r depth c a b).run s = .error ce := by
  simp only [redOpT, StateT.run_bind, hw, except_ok_bind, hr, hw2]; rfl

theorem redWf_err_a (c : NIdx) (a b : EIdx) (s s₁ : AState) (wf : List NIdx)
    (hwf : natOpWfNames.run s = .ok (wf, s)) (sup : Bool)
    (hs : (natLitSupported fe).run s = .ok (sup, s₁)) (hc : (wf.contains c && sup) = true)
    (ce : CheckError) (hw : (r.whnf depth a).run s₁ = .error ce) :
    (redWfT r fe depth c a b).run s = .error ce := by
  simp only [redWfT, StateT.run_bind, hwf, except_ok_bind, hs, hc, ite_true, hw]; rfl

theorem redWf_err_b (c : NIdx) (a b : EIdx) (s s₁ s₂ s₃ : AState) (wf : List NIdx)
    (hwf : natOpWfNames.run s = .ok (wf, s)) (sup : Bool)
    (hs : (natLitSupported fe).run s = .ok (sup, s₁)) (hc : (wf.contains c && sup) = true)
    (wa : EIdx) (N : Nat) (hw : (r.whnf depth a).run s₁ = .ok (wa, s₂))
    (hr : (rawNatLit? wa).run s₂ = .ok (some N, s₃)) (ce : CheckError)
    (hw2 : (r.whnf depth b).run s₃ = .error ce) :
    (redWfT r fe depth c a b).run s = .error ce := by
  simp only [redWfT, StateT.run_bind, hwf, except_ok_bind, hs, hc, ite_true, hw, hr, hw2]; rfl

theorem redWf_fail (c : NIdx) (a b : EIdx) (s s₁ s₂ s₃ s₄ s₅ : AState) (wf : List NIdx)
    (hwf : natOpWfNames.run s = .ok (wf, s)) (sup : Bool)
    (hs : (natLitSupported fe).run s = .ok (sup, s₁)) (hc : (wf.contains c && sup) = true)
    (wa wb : EIdx) (N N₂ : Nat) (hw : (r.whnf depth a).run s₁ = .ok (wa, s₂))
    (hr : (rawNatLit? wa).run s₂ = .ok (some N, s₃))
    (hw2 : (r.whnf depth b).run s₃ = .ok (wb, s₄))
    (hr2 : (rawNatLit? wb).run s₄ = .ok (some N₂, s₅)) :
    (redWfT r fe depth c a b).run s = .error (.notImplemented "native Nat computation on literals") := by
  simp only [redWfT, StateT.run_bind, hwf, except_ok_bind, hs, hc, ite_true, hw, hr, hw2, hr2]; rfl

end redruns

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
  rw [reduceNatSuccE.arm1]
  rcases h1 : callW p n "nat_lit_supported" [vis] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, reduceNatSuccE.k_nat_lit_supported.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, reduceNatSuccE.k_nat_lit_supported.arm1]
  obtain ⟨hok1, hS1, hres1, hfr1, -⟩ := callW_natLitSupported p hp n s₀ a₀ dn vis fe MM eb hC r₁ m₁ h1
  rcases h2 : callW p n "pin_at" [3] m₁ with _ | ⟨r₂, m₂⟩
  · rw [liftE_none, reduceNatSuccE.k_pin_at.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm2, -, -, hr₂⟩ := callW_pinAt p hp.pinAt n m₁ 3 r₂ m₂ h2
  subst m₂
  simp only [show (3 : Word).toNat = 3 from rfl] at hr₂
  have hr₂' : r₂.headD 0 = pinW s₀.mem 4 := by rw [hr₂, pinW_const_frame hfr1]
  -- the twin's `natLitSupported`
  have hsup : (natLitSupported fe).run a₀ = .ok (decBool r₁, AM.st (natLitSupported fe) a₀) := by
    have := AM.run_of_ok _ _ hok1
    rw [hres1] at this
    exact this
  generalize AM.st (natLitSupported fe) a₀ = a₁ at hsup hS1
  have hcw : HW (pinW s₀.mem 4) := hC.pins.names_lt 3 (by decide)
  have hskip : (c ≠ r₂.headD 0 ∨ r₁.headD 0 = 0) →
      ((decI c : NIdx) == decI (pinW s₀.mem 4) && decBool r₁) = false := by
    intro hh
    rw [decI_beq _ _ hc hcw]
    rcases hh with hh | hh
    · rw [hr₂'] at hh
      have : decide (c = pinW s₀.mem 4) = false := decide_eq_false hh
      rw [this]; rfl
    · have : decBool r₁ = false := by simp only [decBool, hh]; rfl
      rw [this]; simp
  have hAfter1 : CoreAfter dn s₀.mem m₁ a₁ vis fe MM eb :=
    ⟨MM, hS1, KeptAll.refl _ _, StackKept.of_const_frame hfr1⟩
  by_cases hcn : c ≠ r₂.headD 0
  · rw [reduceNatSuccE.k_pin_at.arm1 _ _ _ _ _ _ _ _ _ _ hcn]
    exact RefE.ret (redSucc_run_skip _ fe d.toNat (decI c) (decE b) a₀ a₁ s₀.mem hC.pins _ hsup
      (hskip (Or.inl hcn))) ⟨hAfter1, rfl, resW_00⟩
  have hcn' : c = r₂.headD 0 := Classical.not_not.mp hcn
  by_cases hs0 : r₁.headD 0 = 0
  · rw [reduceNatSuccE.k_pin_at.arm2 _ _ _ _ _ _ _ _ _ _ hcn' hs0]
    exact RefE.ret (redSucc_run_skip _ fe d.toNat (decI c) (decE b) a₀ a₁ s₀.mem hC.pins _ hsup
      (hskip (Or.inr hs0))) ⟨hAfter1, rfl, resW_00⟩
  rw [reduceNatSuccE.k_pin_at.arm3 _ _ _ _ _ _ _ _ _ _ hcn' hs0]
  have hcond : ((decI c : NIdx) == decI (pinW s₀.mem 4) && decBool r₁) = true := by
    rw [decI_beq _ _ hc hcw]
    have h1 : c = pinW s₀.mem 4 := by rw [← hr₂']; exact hcn'
    have h2 : decBool r₁ = true := by simp only [decBool, bne_iff_ne, ne_eq]; exact hs0
    rw [h2]; simp [h1]
  -- `whnf`
  have hSP1 : SlotPre ⟨m₁, Locals.init []⟩ a₁ dn vis fe MM eb mode := ⟨hS1, hS.mode4, hS.eb_mode⟩
  rcases h3 : callE p n "whnf" [mode, vis, d, b] m₁ with e3 | ⟨r₃, m₃⟩
  · rw [reduceNatSuccE.k_whnf.none]
    exact fun hkE => ErrClaim.of_run_err (fun ce h' => redSucc_err _ _ _ _ _ _ _ _ hC.pins _ hsup hcond ce h')
      (CoreSpecE.of_callE ((hkE n (by omega)).whnf F ⟨m₁, Locals.init []⟩ a₁ dn vis fe MM eb mode d b
        (by omega) (by omega) hSP1 hb) h3)
  rw [reduceNatSuccE.k_whnf.arm1]
  have hkn : KnotOK p n := hk n (by omega)
  obtain ⟨hok3, ⟨M', hS3, hK3, hSt3⟩, hres3, hrw3⟩ := CoreSpec.of_callW
    (hkn.whnf F ⟨m₁, Locals.init []⟩ a₁ dn vis fe MM eb mode d b (by omega) (by omega) hSP1 hb)
    (callW_of_callE h3)
  rcases h4 : callW p n "raw_nat_lit" [r₃.headD 0] m₃ with _ | ⟨r₄, m₄⟩
  · rw [liftE_none, reduceNatSuccE.k_raw_nat_lit.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE b)) a₁ = a₂ at hrun3 hS3
  obtain ⟨hm4, hrun4, hres4, hslice4⟩ := callW_rawNatLit p hp n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M' eb _
    hS3 hrw3 r₄ m₄ h4
  subst m₄
  have hStK1 := StackKept.of_const_frame hfr1
  by_cases hf : r₄.headD 0 = 0
  · rw [reduceNatSuccE.k_raw_nat_lit.arm1 _ _ _ _ hf]
    have hnone : rawDec m₃ r₄ = none := by unfold rawDec; rw [ite_eq_left hf]
    rw [hnone] at hrun4
    exact RefE.ret (redSucc_run_none _ fe d.toNat (decI c) (decE b) a₀ a₁ a₂ a₂ s₀.mem hC.pins _ hsup
      hcond (decE (r₃.headD 0)) (by rw [hrun3]; rfl) hrun4) ⟨⟨M', hS3, hK3, hStK1.trans hSt3⟩, rfl, resW_00⟩
  rw [reduceNatSuccE.k_raw_nat_lit.arm2 _ _ _ _ hf]
  obtain ⟨hsl, hnorm⟩ := hslice4 hf
  rcases h5 : callW p n "nat_succ_lit" [r₄.tail.headD 0, r₄.tail.tail.headD 0] m₃ with _ | ⟨r₅, m₅⟩
  · rw [liftE_none, reduceNatSuccE.k_nat_succ_lit.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, reduceNatSuccE.k_nat_succ_lit.arm1]
  obtain ⟨hok5, hS5, hres5, hfr5, hhw5, hP5⟩ := callW_natSuccLit p hp n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M' eb _ _
    hS3 hsl r₅ m₅ h5
  have hsome : rawDec m₃ r₄ = some (pv (vpool m₃) (r₄.tail.headD 0).toNat
      (r₄.tail.tail.headD 0).toNat) := by unfold rawDec; rw [ite_eq_right hf]
  rw [hsome] at hrun4
  have hi := natAddArm_run_internE (u := pv (vpool m₃) (r₄.tail.headD 0).toNat
      (r₄.tail.tail.headD 0).toNat) (v := 1) (by rw [AM.run_of_ok _ _ hok5, hres5])
  exact RefE.ret (redSucc_run_some _ fe d.toNat (decI c) (decE b) a₀ a₁ a₂ a₂ _ s₀.mem hC.pins _ hsup
    hcond (decE (r₃.headD 0)) (by rw [hrun3]; rfl) _ hrun4 _ hi)
    ⟨⟨M', hS5, hK3, (hStK1.trans hSt3).trans (StackKept.of_nat_frame hfr5 hP5)⟩,
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
  rw [reduceNatOpE.arm1]
  have hkn : KnotOK p n := hk n (by omega)
  -- first `whnf`
  rcases h1 : callE p n "whnf" [mode, vis, d, a] s₀.mem with e1 | ⟨r₁, m₁⟩
  · rw [reduceNatOpE.k_whnf.none]
    exact fun hkE => ErrClaim.of_run_err (fun ce h' => redOp_err_a (ce := ce) (hw := h') ..)
      (CoreSpecE.of_callE ((hkE n (by omega)).whnf F s₀ a₀ dn vis fe MM eb mode d a (by omega)
        (by omega) hS ha) h1)
  rw [reduceNatOpE.k_whnf.arm1]
  obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW
    (hkn.whnf F s₀ a₀ dn vis fe MM eb mode d a (by omega) (by omega) hS ha) (callW_of_callE h1)
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE a)) a₀ = a₁ at hrun1 hS₁
  rcases h2 : callW p n "raw_nat_lit" [r₁.headD 0] m₁ with _ | ⟨r₂, m₂⟩
  · rw [liftE_none, reduceNatOpE.k_raw_nat_lit.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm2, hrun2, hres2, hslice2⟩ := callW_rawNatLit p hp n ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb _
    hS₁ hrw1 r₂ m₂ h2
  subst m₂
  by_cases hf2 : r₂.headD 0 = 0
  · rw [reduceNatOpE.k_raw_nat_lit.arm1 _ _ _ _ _ _ _ _ _ hf2]
    have hnone : rawDec m₁ r₂ = none := by unfold rawDec; rw [ite_eq_left hf2]
    rw [hnone] at hrun2
    exact RefE.ret (redOp_run_none1 _ d.toNat (decI c) (decE a) (decE b) a₀ a₁ a₁ _
      (by rw [hrun1]; rfl) hrun2) ⟨⟨M₁, hS₁, hK₁, hSt₁⟩, rfl, resW_00⟩
  rw [reduceNatOpE.k_raw_nat_lit.arm2 _ _ _ _ _ _ _ _ _ hf2]
  obtain ⟨hsl2, hnorm2⟩ := hslice2 hf2
  have hsome2 : rawDec m₁ r₂ = some (pv (vpool m₁) (r₂.tail.headD 0).toNat
      (r₂.tail.tail.headD 0).toNat) := by unfold rawDec; rw [ite_eq_right hf2]
  rw [hsome2] at hrun2
  -- second `whnf`
  have hSP₂ : SlotPre ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode := ⟨hS₁, hS.mode4, hS.eb_mode⟩
  rcases h3 : callE p n "whnf" [mode, vis, d, b] m₁ with e3 | ⟨r₃, m₃⟩
  · rw [reduceNatOpE.k_whnf_2.none]
    exact fun hkE => ErrClaim.of_run_err (fun ce h' => redOp_err_b (hw := by rw [hrun1]; rfl)
        (hr := hrun2) (ce := ce) (hw2 := h') ..)
      (CoreSpecE.of_callE ((hkE n (by omega)).whnf F ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode d
        b (by omega) (by omega) hSP₂ hb) h3)
  rw [reduceNatOpE.k_whnf_2.arm1]
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := CoreSpec.of_callW
    (hkn.whnf F ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode d b (by omega) (by omega) hSP₂ hb)
    (callW_of_callE h3)
  have hgrow : PoolGrew m₁ m₃ := hSt₃.pool
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE b)) a₁ = a₂ at hrun3 hS₃
  rcases h4 : callW p n "raw_nat_lit" [r₃.headD 0] m₃ with _ | ⟨r₄, m₄⟩
  · rw [liftE_none, reduceNatOpE.k_raw_nat_lit_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm4, hrun4, hres4, hslice4⟩ := callW_rawNatLit p hp n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb _
    hS₃ hrw3 r₄ m₄ h4
  subst m₄
  by_cases hf4 : r₄.headD 0 = 0
  · rw [reduceNatOpE.k_raw_nat_lit_2.arm1 _ _ _ _ _ _ _ hf4]
    have hnone : rawDec m₃ r₄ = none := by unfold rawDec; rw [ite_eq_left hf4]
    rw [hnone] at hrun4
    exact RefE.ret (redOp_run_none2 _ d.toNat (decI c) (decE a) (decE b) a₀ a₁ a₁ a₂ a₂ _ _ _
      (by rw [hrun1]; rfl) hrun2 (by rw [hrun3]; rfl) hrun4)
      ⟨⟨M₃, hS₃, hK₁.trans hK₃, hSt₁.trans hSt₃⟩, rfl, resW_00⟩
  rw [reduceNatOpE.k_raw_nat_lit_2.arm2 _ _ _ _ _ _ _ hf4]
  obtain ⟨hsl4, hnorm4⟩ := hslice4 hf4
  have hsome4 : rawDec m₃ r₄ = some (pv (vpool m₃) (r₄.tail.headD 0).toNat
      (r₄.tail.tail.headD 0).toNat) := by unfold rawDec; rw [ite_eq_right hf4]
  rw [hsome4] at hrun4
  obtain ⟨hsl2', hpv2, hnorm2'⟩ := hgrow.slice hsl2 hnorm2
  rcases h5 : callW p n "nat_op_result" [c, r₂.tail.headD 0, r₂.tail.tail.headD 0, r₄.tail.headD 0,
      r₄.tail.tail.headD 0] m₃ with _ | ⟨r₅, m₅⟩
  · rw [liftE_none, reduceNatOpE.k_nat_op_result.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, reduceNatOpE.k_nat_op_result.arm1]
  obtain ⟨hok5, ⟨M₅, hS₅, hK₅, hSt₅⟩, hres5, hrw5⟩ := CoreSpec.of_callW
    (hno n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb c _ _ _ _ hS₃ hc hsl2' hsl4 hnorm2' hnorm4) h5
  have hres5' := AM.run_of_ok _ _ hok5
  rw [hres5] at hres5'
  dsimp only at hres5' hS₅
  rw [hpv2] at hres5' hS₅
  exact RefE.ret (redOp_run_some _ d.toNat (decI c) (decE a) (decE b) a₀ a₁ a₁ a₂ a₂ _ _ _ _ _ _
    (by rw [hrun1]; rfl) hrun2 (by rw [hrun3]; rfl) hrun4 hres5')
    ⟨⟨M₅, hS₅, (hK₁.trans hK₃).trans hK₅, (hSt₁.trans hSt₃).trans hSt₅⟩,
      by dsimp only; simp only [decOptR, List.headD_cons, List.tail_cons, decOpt_norm],
      resW_norm _ _⟩

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
  cases n with
  | zero => rw [reduceNatWfE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [reduceNatWfE.arm1]
  have hkn : KnotOK p n := hk n (by omega)
  rcases h1 : callW p n "nat_op_is_wf" [c] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, reduceNatWfE.k_nat_op_is_wf.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, reduceNatWfE.k_nat_op_is_wf.arm1]
  obtain ⟨s₁', hs₁', hm₁, -, -, hwfsel, -⟩ := triple_of_callW
    (natOpIsWfL_spec p hp.natOpIsWf n ⟨s₀.mem, Locals.init []⟩ c) h1
  have hm1 : m₁ = s₀.mem := by rw [← hs₁', hm₁]
  subst hm1
  rcases h2 : callW p n "nat_lit_supported" [vis] s₀.mem with _ | ⟨r₂, m₂⟩
  · rw [liftE_none, reduceNatWfE.k_nat_lit_supported.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hok2, hS2, hres2, hfr2, hrh2⟩ := callW_natLitSupported p hp n s₀ a₀ dn vis fe MM eb hC r₂ m₂ h2
  have hsup : (natLitSupported fe).run a₀ = .ok (decBool r₂, AM.st (natLitSupported fe) a₀) := by
    have := AM.run_of_ok _ _ hok2
    rw [hres2] at this
    exact this
  generalize AM.st (natLitSupported fe) a₀ = a₁ at hsup hS2
  have hwf := natOpWfNames_run hC.pins
  have hcont := wfContains hC.pins c hc
  by_cases hgo : r₁.headD 0 ≠ 0 ∧ r₂.headD 0 ≠ 0
  case neg =>
    rw [show reduceNatWfE.k_nat_lit_supported p n mode vis d a b (r₁.headD 0) (.ok (r₂, m₂)) =
        reduceNatWfE.j1 p m₂ by
      by_cases h1 : r₁.headD 0 = 0
      · exact reduceNatWfE.k_nat_lit_supported.arm3 _ _ _ _ _ _ _ _ _ _ h1
      · exact reduceNatWfE.k_nat_lit_supported.arm2 _ _ _ _ _ _ _ _ _ _ h1
          (Classical.byContradiction fun h2 => hgo ⟨h1, h2⟩), reduceNatWfE.j1]
    have hskip : (([decI (pinW s₀.mem 22), decI (pinW s₀.mem 23), decI (pinW s₀.mem 24),
        decI (pinW s₀.mem 25), decI (pinW s₀.mem 26), decI (pinW s₀.mem 27), decI (pinW s₀.mem 28),
        decI (pinW s₀.mem 29)] : List NIdx).contains (decI c) && decBool r₂) = false := by
      rw [hcont]
      by_cases h1 : r₁.headD 0 = 0
      · have : natOpWfSel (pinW s₀.mem) c = false := by
          rw [← hwfsel, h1]; rfl
        rw [this]; rfl
      · have h2 : r₂.headD 0 = 0 := Classical.byContradiction fun h2 => hgo ⟨h1, h2⟩
        have : decBool r₂ = false := by simp only [decBool, h2]; rfl
        rw [this]; simp
    exact RefE.ret (redWf_run_skip _ fe d.toNat (decI c) (decE a) (decE b) a₀ a₁ _ hwf _ hsup hskip)
      ⟨⟨MM, hS2, KeptAll.refl _ _, StackKept.of_const_frame hfr2⟩, rfl, resW_00⟩
  rw [reduceNatWfE.k_nat_lit_supported.arm1 _ _ _ _ _ _ _ _ _ _ hgo.1 hgo.2]
  have hbool : (([decI (pinW s₀.mem 22), decI (pinW s₀.mem 23),
      decI (pinW s₀.mem 24), decI (pinW s₀.mem 25), decI (pinW s₀.mem 26), decI (pinW s₀.mem 27),
      decI (pinW s₀.mem 28), decI (pinW s₀.mem 29)] : List NIdx).contains (decI c) && decBool r₂) = true := by
    rw [hcont]
    have h1 : natOpWfSel (pinW s₀.mem) c = true := by rw [← hwfsel]; simpa using hgo.1
    have h2 : decBool r₂ = true := by simp only [decBool, bne_iff_ne, ne_eq]; exact hgo.2
    rw [h1, h2]; rfl
  have hSP1 : SlotPre ⟨m₂, Locals.init []⟩ a₁ dn vis fe MM eb mode := ⟨hS2, hS.mode4, hS.eb_mode⟩
  rcases h3 : callE p n "whnf" [mode, vis, d, a] m₂ with e3 | ⟨r₃, m₃⟩
  · rw [reduceNatWfE.k_whnf.none]
    exact fun hkE => ErrClaim.of_run_err
      (fun ce h' => redWf_err_a _ _ _ _ _ _ a₀ a₁ _ hwf _ hsup hbool ce h')
      (CoreSpecE.of_callE ((hkE n (by omega)).whnf F ⟨m₂, Locals.init []⟩ a₁ dn vis fe MM eb mode d a
        (by omega) (by omega) hSP1 ha) h3)
  rw [reduceNatWfE.k_whnf.arm1]
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := CoreSpec.of_callW
    (hkn.whnf F ⟨m₂, Locals.init []⟩ a₁ dn vis fe MM eb mode d a (by omega) (by omega) hSP1 ha)
    (callW_of_callE h3)
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE a)) a₁ = a₂ at hrun3 hS₃
  rcases h4 : callW p n "raw_nat_lit" [r₃.headD 0] m₃ with _ | ⟨r₄, m₄⟩
  · rw [liftE_none, reduceNatWfE.k_raw_nat_lit.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm4, hrun4, hres4, hslice4⟩ := callW_rawNatLit p hp n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb _
    hS₃ hrw3 r₄ m₄ h4
  subst m₄
  have hStK := StackKept.of_const_frame hfr2
  by_cases hf4 : r₄.headD 0 = 0
  · rw [reduceNatWfE.k_raw_nat_lit.arm2 _ _ _ _ _ _ _ _ hf4, reduceNatWfE.j1]
    have hnone : rawDec m₃ r₄ = none := by unfold rawDec; rw [ite_eq_left hf4]
    rw [hnone] at hrun4
    exact RefE.ret (redWf_run_none1 _ fe d.toNat (decI c) (decE a) (decE b) a₀ a₁ a₂ a₂ _ hwf _ hsup
      hbool _ (by rw [hrun3]; rfl) hrun4) ⟨⟨M₃, hS₃, hK₃, hStK.trans hSt₃⟩, rfl, resW_00⟩
  rw [reduceNatWfE.k_raw_nat_lit.arm1 _ _ _ _ _ _ _ _ hf4]
  have hsome4 : rawDec m₃ r₄ = some (pv (vpool m₃) (r₄.tail.headD 0).toNat
      (r₄.tail.tail.headD 0).toNat) := by unfold rawDec; rw [ite_eq_right hf4]
  rw [hsome4] at hrun4
  have hSP3 : SlotPre ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb mode := ⟨hS₃, hS.mode4, hS.eb_mode⟩
  rcases h5 : callE p n "whnf" [mode, vis, d, b] m₃ with e5 | ⟨r₅, m₅⟩
  · rw [reduceNatWfE.k_whnf_2.none]
    exact fun hkE => ErrClaim.of_run_err (fun ce h' => redWf_err_b _ _ _ _ _ _ a₀ a₁ a₂ a₂ _ hwf _ hsup
        hbool (decE (r₃.headD 0)) _ (by rw [hrun3]; rfl) hrun4 ce h')
      (CoreSpecE.of_callE ((hkE n (by omega)).whnf F ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb mode d b
        (by omega) (by omega) hSP3 hb) h5)
  rw [reduceNatWfE.k_whnf_2.arm1]
  obtain ⟨hok5, ⟨M₅, hS₅, hK₅, hSt₅⟩, hres5, hrw5⟩ := CoreSpec.of_callW
    (hkn.whnf F ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb mode d b (by omega) (by omega) hSP3 hb)
    (callW_of_callE h5)
  have hrun5 := AM.run_of_ok _ _ hok5
  rw [hres5] at hrun5
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE b)) a₂ = a₃ at hrun5 hS₅
  rcases h6 : callW p n "raw_nat_lit" [r₅.headD 0] m₅ with _ | ⟨r₆, m₆⟩
  · rw [liftE_none, reduceNatWfE.k_raw_nat_lit_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm6, hrun6, hres6, hslice6⟩ := callW_rawNatLit p hp n ⟨m₅, Locals.init []⟩ a₃ dn vis fe M₅ eb _
    hS₅ hrw5 r₆ m₆ h6
  subst m₆
  by_cases hf6 : r₆.headD 0 = 0
  · rw [reduceNatWfE.k_raw_nat_lit_2.arm1 _ _ _ hf6, reduceNatWfE.j1]
    have hnone : rawDec m₅ r₆ = none := by unfold rawDec; rw [ite_eq_left hf6]
    rw [hnone] at hrun6
    exact RefE.ret (redWf_run_none2 _ fe d.toNat (decI c) (decE a) (decE b) a₀ a₁ a₂ a₂ a₃ a₃ _ hwf _
      hsup hbool _ _ _ (by rw [hrun3]; rfl) hrun4 (by rw [hrun5]; rfl) hrun6)
      ⟨⟨M₅, hS₅, hK₃.trans hK₅, (hStK.trans hSt₃).trans hSt₅⟩, rfl, resW_00⟩
  rw [reduceNatWfE.k_raw_nat_lit_2.abort1 _ _ _ hf6]
  have hsome6 : rawDec m₅ r₆ = some (pv (vpool m₅) (r₆.tail.headD 0).toNat
      (r₆.tail.tail.headD 0).toNat) := by unfold rawDec; rw [ite_eq_right hf6]
  rw [hsome6] at hrun6
  exact fun _ => ErrClaim.of_run_eqW (a' := a₀)
    (T' := (ConRon.Arena.fail (.notImplemented "native Nat computation on literals") : AM (Option EIdx)))
    (by rw [redWf_fail _ _ _ _ _ _ a₀ a₁ a₂ a₂ a₃ a₃ _ hwf _ hsup hbool _ _ _ _ (by rw [hrun3]; rfl)
          hrun4 (by rw [hrun5]; rfl) hrun6]; rfl)
    (ErrClaim.fail _ _ rfl)

end refs

end L.Arena
