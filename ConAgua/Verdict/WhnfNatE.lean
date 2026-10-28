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

theorem resW_zero : ResW [0, 0] := by unfold ResW HW; exact ⟨by decide, by decide⟩

/-- The callee's first two result words, after a run of constant frame (the caller's result). -/
theorem CorePost.relist {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {vis : Word} {fe : IFEnv}
    {MM : ModeMaps} {eb : Word}
    (hfr : MemFrame [CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP] [18, 19] m₀ m₁)
    (v : List Word × Mem) (y : Option EIdx) (a' : AState)
    (h : CorePost decOptR dn m₁ vis fe MM eb ResW v y a') :
    CorePost decOptR dn m₀ vis fe MM eb ResW ([v.1.headD 0, v.1.tail.headD 0], v.2) y a' :=
  ⟨CoreAfter.comp (KeptAll.refl _ _) (StackKept.of_const_frame hfr) h.after, h.res, h.valid⟩

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
      (hskip (Or.inl hcn))) ⟨hAfter1, rfl, resW_zero⟩
  have hcn' : c = r₂.headD 0 := Classical.not_not.mp hcn
  by_cases hs0 : r₁.headD 0 = 0
  · rw [reduceNatSuccE.k_pin_at.arm2 _ _ _ _ _ _ _ _ _ _ hcn' hs0]
    exact RefE.ret (redSucc_run_skip _ fe d.toNat (decI c) (decE b) a₀ a₁ s₀.mem hC.pins _ hsup
      (hskip (Or.inr hs0))) ⟨hAfter1, rfl, resW_zero⟩
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
      hcond (decE (r₃.headD 0)) (by rw [hrun3]; rfl) hrun4) ⟨⟨M', hS3, hK3, hStK1.trans hSt3⟩, rfl, resW_zero⟩
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
      (by rw [hrun1]; rfl) hrun2) ⟨⟨M₁, hS₁, hK₁, hSt₁⟩, rfl, resW_zero⟩
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
      ⟨⟨M₃, hS₃, hK₁.trans hK₃, hSt₁.trans hSt₃⟩, rfl, resW_zero⟩
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
      ⟨⟨MM, hS2, KeptAll.refl _ _, StackKept.of_const_frame hfr2⟩, rfl, resW_zero⟩
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
      hbool _ (by rw [hrun3]; rfl) hrun4) ⟨⟨M₃, hS₃, hK₃, hStK.trans hSt₃⟩, rfl, resW_zero⟩
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
      ⟨⟨M₅, hS₅, hK₃.trans hK₅, (hStK.trans hSt₃).trans hSt₅⟩, rfl, resW_zero⟩
  rw [reduceNatWfE.k_raw_nat_lit_2.abort1 _ _ _ hf6]
  have hsome6 : rawDec m₅ r₆ = some (pv (vpool m₅) (r₆.tail.headD 0).toNat
      (r₆.tail.tail.headD 0).toNat) := by unfold rawDec; rw [ite_eq_right hf6]
  rw [hsome6] at hrun6
  exact fun _ => ErrClaim.of_run_eqW (a' := a₀)
    (T' := (ConRon.Arena.fail (.notImplemented "native Nat computation on literals") : AM (Option EIdx)))
    (by rw [redWf_fail _ _ _ _ _ _ a₀ a₁ a₂ a₂ a₃ a₃ _ hwf _ hsup hbool _ _ _ _ (by rw [hrun3]; rfl)
          hrun4 (by rw [hrun5]; rfl) hrun6]; rfl)
    (ErrClaim.fail _ _ rfl)

include hp in
/-- **`reduce_nat_k` refines `redHeadT` at a constant head, both outcomes** (`redConstT`; the
errors are `reduce_nat_succ`'s). -/
theorem reduceNatK_ref (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hf : HW f) (hb : HW b) (hg3 : f >>> 28 = 3)
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
  obtain ⟨n_, us_, hview, hn, hu, hnl, hul⟩ :=
    view_const_words s₀.mem a₀ hC.arena.1 f hf ⟨hsc, by simpa using hbd⟩ hg3
  have hcg := redHead_const (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b) a₀ n_ us_ hview
  subst hn hu
  rcases h1 : callW p n "pin_word" [52] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, reduceNatKE.k_pin_word.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm1, -, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₁ m₁ h1
  subst m₁
  simp only [show (52 : Word).toNat = 52 from rfl] at hr₁
  have hel := pinEmptyLevels_run hC.pins
  have hbne : ∀ v w : Word, HW v → HW w → ((decI v : LsIdx) != decI w) = !decide (v = w) := by
    intro v w hv hw; simp only [bne, decI_beq v w hv hw]
  by_cases hne : tfld s₀.mem CONST (tierW f) (idxW f) 1 ≠ r₁.headD 0
  · rw [reduceNatKE.k_pin_word.arm1 _ _ _ _ _ _ _ _ _ _ hne]
    have hz := redConst_ne (coreKnot (decMode mode) fe id F) fe d.toNat
      (decI (tfld s₀.mem CONST (tierW f) (idxW f) 0)) (decI (tfld s₀.mem CONST (tierW f) (idxW f) 1)) _
      (decE b) a₀ hel (by
      rw [hbne _ _ hul hC.pins.lv_lt.1]
      have : tfld s₀.mem CONST (tierW f) (idxW f) 1 ≠ pinW s₀.mem 52 := by rw [← hr₁]; exact hne
      simp [this])
    exact RefE.ret (hcg.trans hz) ⟨⟨MM, hC, KeptAll.refl _ _, StackKept.refl _⟩, rfl, resW_zero⟩
  rw [reduceNatKE.k_pin_word.arm2 _ _ _ _ _ _ _ _ _ _ (by simpa using hne)]
  have hne' : tfld s₀.mem CONST (tierW f) (idxW f) 1 = pinW s₀.mem 52 := by
    rw [← hr₁]; simpa using hne
  have hcongr := redConst_eq (coreKnot (decMode mode) fe id F) fe d.toNat
      (decI (tfld s₀.mem CONST (tierW f) (idxW f) 0)) (decI (tfld s₀.mem CONST (tierW f) (idxW f) 1)) _
      (decE b) a₀ hel (by
    rw [hbne _ _ hul hC.pins.lv_lt.1]; simp [hne'])
  exact RefE.tail_eq (reduceNatKE.k_reduce_nat_succ.none p) (fun v => reduceNatKE.k_reduce_nat_succ.arm1 p v.1 v.2)
    (fun h => h.mono (by omega)) (hcg.trans hcongr)
    (CorePost.relist (MemFrame.refl _ _ _))
    (reduceNatSucc_ref p hp n F (by omega) (by omega) (hk.mono (by omega)) s₀ a₀ dn vis fe MM eb mode d _ b hS
      hnl hb)

include hp in
/-- **`reduce_nat_ap` refines `redHeadT` at an application head, both outcomes** (`redAppT`; the
errors are `reduce_nat_op`'s or `reduce_nat_wf`'s). -/
theorem reduceNatAp_ref (hno : NatOpResultOK p) (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hf : HW f) (hb : HW b) (hg4 : f >>> 28 = 4)
    (hsc : ¬(tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0)) :
    RefE (KnotUpToE p n) (reduceNatApE p n s₀.mem mode vis d f b)
      (redHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b)) a₀
      (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  have hC := hS.rel
  cases n with
  | zero => rw [reduceNatApE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [reduceNatApE.eq_2]
  by_cases hbd : tcnt s₀.mem APP (tierW f) ≤ idxW f
  · rw [ite_eq_left hbd]; exact RefE.of_cls0 (by simp)
  rw [ite_eq_right hbd]
  obtain ⟨hviewf, hgw, hxw⟩ := view_app s₀.mem a₀ hC.arena.1 f hf ⟨hsc, by simpa using hbd⟩ hg4
  have hcg0 := redHead_app (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b) _ _ a₀ hviewf
  generalize tfld s₀.mem APP (tierW f) (idxW f) 0 = gw at hgw hviewf hcg0 ⊢
  generalize tfld s₀.mem APP (tierW f) (idxW f) 1 = xw at hxw hviewf hcg0 ⊢
  have hCA : CoreAfter dn s₀.mem s₀.mem a₀ vis fe MM eb := ⟨MM, hC, KeptAll.refl _ _, StackKept.refl _⟩
  by_cases g3 : gw >>> 28 ≠ 3
  · rw [ite_eq_left g3]
    have ht : ((decE (gw)).tag == ETag.const) = false := by
      rw [decE_const_tag _ hgw]; exact beq_eq_false_iff_ne.mpr g3
    exact RefE.ret (hcg0.trans (redApp_notconst _ fe d.toNat (decE gw) (decE xw) (decE b) a₀ ht))
      ⟨hCA, rfl, resW_zero⟩
  rw [ite_eq_right g3]
  have g3' : gw >>> 28 = 3 := by simpa using g3
  have ht : ((decE (gw)).tag == ETag.const) = true := by
    rw [decE_const_tag _ hgw]; exact beq_iff_eq.mpr g3'
  by_cases hs2 : tierW (gw) ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [ite_eq_left hs2]; exact RefE.of_cls0 (by simp)
  rw [ite_eq_right hs2]
  by_cases hb2 : tcnt s₀.mem CONST (tierW (gw)) ≤ idxW (gw)
  · rw [ite_eq_left hb2]; exact RefE.of_cls0 (by simp)
  rw [ite_eq_right hb2]
  obtain ⟨n_, us_, hview, hn, hu, hnl, hul⟩ := view_const_words s₀.mem a₀ hC.arena.1 _ hgw
    ⟨hs2, by simpa using hb2⟩ g3'
  subst hn hu
  generalize tfld s₀.mem CONST (tierW gw) (idxW gw) 0 = cw at *
  generalize tfld s₀.mem CONST (tierW gw) (idxW gw) 1 = uw at *
  rcases h1 : callW p n "pin_word" [52] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, reduceNatApE.k_pin_word.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm1, hflag, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₁ m₁ h1
  subst m₁
  simp only [show (52 : Word).toNat = 52 from rfl] at hr₁
  have hel := pinEmptyLevels_run hC.pins
  have hbne : ∀ v w : Word, HW v → HW w → ((decI v : LsIdx) != decI w) = !decide (v = w) := by
    intro v w hv hw; simp only [bne, decI_beq v w hv hw]
  by_cases hne : uw ≠ r₁.headD 0
  · rw [reduceNatApE.k_pin_word.arm1 _ _ _ _ _ _ _ _ _ _ _ hne]
    have hz := redApp_ne (coreKnot (decMode mode) fe id F) fe d.toNat (decE gw) (decE xw) (decE b) a₀
      (decI cw) (decI uw) (decI (pinW s₀.mem 52)) ht hview hel (by
        rw [hbne _ _ hul hC.pins.lv_lt.1]
        have : uw ≠ pinW s₀.mem 52 := by rw [← hr₁]; exact hne
        simp [this])
    exact RefE.ret (hcg0.trans hz) ⟨hCA, rfl, resW_zero⟩
  rw [reduceNatApE.k_pin_word.arm2 _ _ _ _ _ _ _ _ _ _ _ (by simpa using hne)]
  have hne' : uw = pinW s₀.mem 52 := by rw [← hr₁]; simpa using hne
  have hcongrApp := redApp_eq (coreKnot (decMode mode) fe id F) fe d.toNat (decE gw) (decE xw) (decE b) a₀
    (decI cw) (decI uw) (decI (pinW s₀.mem 52)) ht hview hel
    (by rw [hbne _ _ hul hC.pins.lv_lt.1]; simp [hne'])
  -- `nat_bin_op_name`
  rcases h2 : callW p n "nat_bin_op_name" [cw] s₀.mem with _ | ⟨r₂, m₂⟩
  · rw [liftE_none, reduceNatApE.k_nat_bin_op_name.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, reduceNatApE.k_nat_bin_op_name.arm1]
  obtain ⟨t₂, ht₂, hm₂, -, hsel2, -⟩ := triple_of_callW
    (natBinOpNameL_spec p hp.natBinOpName n ⟨s₀.mem, Locals.init []⟩ hflag cw) h2
  have hm2 : m₂ = s₀.mem := by rw [← ht₂, hm₂]
  subst hm2
  rcases h3 : callW p n "nat_op_stored" [vis, cw] s₀.mem with _ | ⟨r₃, m₃⟩
  · rw [liftE_none, reduceNatApE.k_nat_op_stored.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hok3, hS3, hres3, hfr3, hrh3⟩ := callW_natOpStored p hp n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe
    MM eb cw hC hnl r₃ m₃ h3
  obtain ⟨b3, hb3⟩ := natOpStored_run_pure fe (decI cw) a₀
  have hst3 : AM.st (natOpStored fe (decI cw)) a₀ = a₀ := (AM.of_run_ok _ _ _ _ hb3).2.1
  have hbb3 : b3 = decBool r₃ := by
    have := (AM.of_run_ok _ _ _ _ hb3).2.2
    rw [hres3] at this; exact this.symm
  rw [hst3] at hS3
  have hbin : (natBinOpName (decI cw)).run a₀ = .ok (natBinOpSel (pinW s₀.mem ) cw, a₀) :=
    natBinOpName_run hC.pins cw hnl
  have hSP3 : SlotPre ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb mode := ⟨hS3, hS.mode4, hS.eb_mode⟩
  have hbool : (natBinOpSel (pinW s₀.mem) cw && decBool r₃) = decide (r₂.headD 0 ≠ 0 ∧ r₃.headD 0 ≠ 0) := by
    rw [← hsel2]; exact bne_and_bne _ _
  have hredbin := redBin_run (coreKnot (decMode mode) fe id F) fe d.toNat (decI cw) (decE xw) (decE b) a₀
    (natBinOpSel (pinW s₀.mem) cw) (decBool r₃) hbin (by rw [hb3, hbb3])
  by_cases hgo : r₂.headD 0 ≠ 0 ∧ r₃.headD 0 ≠ 0
  · rw [reduceNatApE.k_nat_op_stored.arm1 _ _ _ _ _ _ _ _ _ _ _ hgo]
    exact RefE.tail_eq (reduceNatApE.k_reduce_nat_op.none p) (fun v => reduceNatApE.k_reduce_nat_op.arm1 p v.1 v.2)
      (fun h => h.mono (by omega))
      (by rw [hcg0, hcongrApp, hredbin, hbool, decide_eq_true hgo]; rfl) (CorePost.relist hfr3)
      (reduceNatOp_ref p hp hno n F (by omega) (by omega) (hk.mono (by omega))
        ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb mode d cw xw b hSP3 hnl hxw hb)
  · rw [reduceNatApE.k_nat_op_stored.arm2 _ _ _ _ _ _ _ _ _ _ _ hgo]
    exact RefE.tail_eq (reduceNatApE.k_reduce_nat_op.none p) (fun v => reduceNatApE.k_reduce_nat_op.arm1 p v.1 v.2)
      (fun h => h.mono (by omega))
      (by rw [hcg0, hcongrApp, hredbin, hbool, decide_eq_false hgo]; rfl) (CorePost.relist hfr3)
      (reduceNatWf_ref p hp n F (by omega) (by omega) (hk.mono (by omega))
        ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb mode d cw xw b hSP3 hnl hxw hb)

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
  by_cases hsc : tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [ite_eq_left hsc]; exact RefE.of_cls0 (by simp)
  rw [ite_eq_right hsc]
  -- the tags that only check a bound
  have simple : ∀ (c : TRec), (f >>> 28 = 0 ∧ c = BVAR) ∨ (f >>> 28 = 1 ∧ c = FVAR) ∨
      (f >>> 28 = 2 ∧ c = SORT) ∨ (f >>> 28 = 5 ∧ c = LAM) ∨ (f >>> 28 = 6 ∧ c = FORALL) ∨
      (f >>> 28 = 7 ∧ c = LET) ∨ (f >>> 28 = 8 ∧ c = LIT) ∨ (f >>> 28 = 9 ∧ c = PROJ) →
      RefE (KnotUpToE p (n + 1)) (if tcnt s₀.mem c (tierW f) ≤ idxW f then .error (Err.abort 0) else
        .ok ([0, 0], s₀.mem))
        (redHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b)) a₀
        (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
    intro c hcg
    by_cases hbd : tcnt s₀.mem c (tierW f) ≤ idxW f
    · rw [ite_eq_left hbd]; exact RefE.of_cls0 (by simp)
    rw [ite_eq_right hbd]
    obtain ⟨v, hv, hc, hp'⟩ := view_nca s₀.mem a₀ hC.arena.1 f hf c ⟨hsc, by simpa using hbd⟩ hcg
    exact RefE.ret (redHead_other _ fe d.toNat _ (decE b) a₀ v hv hc hp')
      ⟨⟨MM, hC, KeptAll.refl _ _, StackKept.refl _⟩, rfl, resW_zero⟩
  have hmono : KnotUpToE p (n + 1) → KnotUpToE p n := fun h => h.mono (by omega)
  by_cases g3 : f >>> 28 = 3
  · rw [ite_eq_left g3]
    exact RefE.tail_eq (reduceNatHeadE.k_reduce_nat_k.none p)
      (fun v => reduceNatHeadE.k_reduce_nat_k.arm1 p v.1 v.2) hmono rfl
      (CorePost.relist (MemFrame.refl _ _ _))
      (reduceNatK_ref p hp n F (by omega) (by omega) (hk.mono (by omega)) s₀ a₀ dn vis fe MM eb mode d f b
        hS hf hb g3 hsc)
  rw [ite_eq_right g3]
  by_cases g4 : f >>> 28 = 4
  · rw [ite_eq_left g4]
    exact RefE.tail_eq (reduceNatHeadE.k_reduce_nat_k.none p)
      (fun v => reduceNatHeadE.k_reduce_nat_k.arm1 p v.1 v.2) hmono rfl
      (CorePost.relist (MemFrame.refl _ _ _))
      (reduceNatAp_ref p hp hno n F (by omega) (by omega) (hk.mono (by omega)) s₀ a₀ dn vis fe MM eb mode d
        f b hS hf hb g4 hsc)
  rw [ite_eq_right g4]
  by_cases g0 : f >>> 28 = 0
  · rw [ite_eq_left g0]; exact simple BVAR (Or.inl ⟨g0, rfl⟩)
  rw [ite_eq_right g0]
  by_cases g1 : f >>> 28 = 1
  · rw [ite_eq_left g1]; exact simple FVAR (Or.inr (Or.inl ⟨g1, rfl⟩))
  rw [ite_eq_right g1]
  by_cases g2 : f >>> 28 = 2
  · rw [ite_eq_left g2]; exact simple SORT (Or.inr (Or.inr (Or.inl ⟨g2, rfl⟩)))
  rw [ite_eq_right g2]
  by_cases g5 : f >>> 28 = 5
  · rw [ite_eq_left g5]; exact simple LAM (Or.inr (Or.inr (Or.inr (Or.inl ⟨g5, rfl⟩))))
  rw [ite_eq_right g5]
  by_cases g6 : f >>> 28 = 6
  · rw [ite_eq_left g6]; exact simple FORALL (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g6, rfl⟩)))))
  rw [ite_eq_right g6]
  by_cases g7 : f >>> 28 = 7
  · rw [ite_eq_left g7]
    exact simple LET (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g7, rfl⟩))))))
  rw [ite_eq_right g7]
  by_cases g8 : f >>> 28 = 8
  · rw [ite_eq_left g8]
    exact simple LIT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g8, rfl⟩)))))))
  rw [ite_eq_right g8]
  by_cases g9 : f >>> 28 ≠ 9
  · rw [ite_eq_left g9]; exact RefE.of_cls0 (by simp)
  rw [ite_eq_right g9]
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
  rw [reduceNatE.eq_2]
  have hap : ((decE e).tag == ETag.app) = (e >>> 28 == 4) := by
    by_cases g : e >>> 28 = 4
    · have := (decE_tag_app e he).mpr g
      rw [beq_iff_eq.mpr this, beq_iff_eq.mpr g]
    · have : ¬ (decE e).tag = ETag.app := fun h' => g ((decE_tag_app e he).mp h')
      rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr g]
  by_cases g4 : e >>> 28 ≠ 4
  · rw [ite_eq_left g4]
    exact RefE.ret (reduceNat_notapp _ fe d.toNat (decE e) a₀ (by rw [hap]; exact beq_eq_false_iff_ne.mpr g4))
      ⟨⟨MM, hC, KeptAll.refl _ _, StackKept.refl _⟩, rfl, resW_zero⟩
  rw [ite_eq_right g4]
  have g4' : e >>> 28 = 4 := by simpa using g4
  by_cases hsc : tierW e ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [ite_eq_left hsc]; exact RefE.of_cls0 (by simp)
  rw [ite_eq_right hsc]
  by_cases hbd : tcnt s₀.mem APP (tierW e) ≤ idxW e
  · rw [ite_eq_left hbd]; exact RefE.of_cls0 (by simp)
  rw [ite_eq_right hbd]
  obtain ⟨hview, hfw, hbw⟩ := view_app s₀.mem a₀ hC.arena.1 e he ⟨hsc, by simpa using hbd⟩ g4'
  exact RefE.tail_eq (reduceNatE.k_reduce_nat_head.none p)
    (fun v => reduceNatE.k_reduce_nat_head.arm1 p v.1 v.2) (fun h => h.mono (by omega))
    (reduceNat_head_eq _ fe d.toNat (decE e) _ _ a₀ (by rw [hap]; exact beq_iff_eq.mpr g4') hview)
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
