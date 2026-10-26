import ConAgua.Verdict.WhnfModels2E
import ConAgua.Verdict.WhnfSlotE

/-!
# `reduce_nat`'s family's verdict claims (lane `verdicts-b`, helper `k2`)

`reduce_nat_wf`'s safety net declines on two literals (the twin's `redWfT`); everything else
propagates the `whnf` slot's claims (`KnotUpToE`) through `reduce_nat_succ`, `reduce_nat_op`,
`reduce_nat_k`, `reduce_nat_ap`, `reduce_nat_head`, `reduce_nat` (`ReduceNatE`). Every other callee is
outside the verdict closure.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace L.Arena

theorem whnfNatE_nv : ∀ f ∈ ["nat_op_is_wf", "nat_lit_supported", "raw_nat_lit", "pin_at",
    "nat_succ_lit", "nat_op_result", "pin_word", "nat_bin_op_name", "nat_op_stored"],
    f ∈ L.Checker.nvFns := by
  decide +kernel

/-! ## The twin's failing runs of the arms -/

section redruns
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat)

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

theorem redOp_err_a (c : NIdx) (a b : EIdx) (s : AState) (ce : CheckError)
    (hw : (r.whnf depth a).run s = .error ce) : (redOpT r depth c a b).run s = .error ce := by
  simp only [redOpT, StateT.run_bind, hw]; rfl

theorem redOp_err_b (c : NIdx) (a b : EIdx) (s s₁ s₂ : AState) (wa : EIdx) (N : Nat)
    (hw : (r.whnf depth a).run s = .ok (wa, s₁)) (hr : (rawNatLit? wa).run s₁ = .ok (some N, s₂))
    (ce : CheckError) (hw2 : (r.whnf depth b).run s₂ = .error ce) :
    (redOpT r depth c a b).run s = .error ce := by
  simp only [redOpT, StateT.run_bind, hw, except_ok_bind, hr, hw2]; rfl

theorem redSucc_err (c : NIdx) (b : EIdx) (s s₁ : AState) (m : Mem)
    (hP : PinsFull m s.pins) (sup : Bool) (hs : (natLitSupported fe).run s = .ok (sup, s₁))
    (hc : (c == decI (pinW m 4) && sup) = true) (ce : CheckError)
    (hw : (r.whnf depth b).run s₁ = .error ce) :
    (redSuccT r fe depth c b).run s = .error ce := by
  simp only [redSuccT, StateT.run_bind, pinNatSucc_run hP, except_ok_bind, hs, hc, ite_true, hw]; rfl

end redruns

section wf
variable (p : Prog) (hp : WhnfDeltaProg' p) (hnv : closedNV p L.Checker.nvFns = true)

include hp hnv in
/-- **`reduce_nat_wf`'s verdicts**: two literals decline (`redWfT`'s safety net); the operands'
head normalizations' are the `whnf` slot's. -/
theorem callE_reduceNatWf (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d c a b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hc : HW c) (ha : HW a) (hb : HW b) (er : Err)
    (h : callE p n "reduce_nat_wf" [mode, vis, d, c, a, b] s₀.mem = .error er) :
    ErrClaim (redWfT (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE a) (decE b)) a₀
      er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hC := hS.rel
  cases n with
  | zero => exact ErrClaim.of_callE_zero h
  | succ n =>
  have hW := triple_of_callE_err (reduceNatWf_specE p hp.reduceNatWf (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d c a b) h (Err.code_ne_of_cls hk0)
  simp only [reduceNatWfE] at hW
  have hkn : KnotOK p n := hk n (by omega)
  have hknE : KnotOKE p n := hkE n (by omega)
  cases h1 : callE p n "nat_op_is_wf" [c] s₀.mem with
  | error e1 =>
    rw [h1, reduceNatWfE.k_nat_op_is_wf.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfNatE_nv "nat_op_is_wf" (by simp)) h1
  | ok q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  simp only [reduceNatWfE.k_nat_op_is_wf] at hW
  obtain ⟨s₁', hs₁', hm₁, -, -, hwfsel, -⟩ := triple_of_callE
    (natOpIsWfL_spec p hp.natOpIsWf n ⟨s₀.mem, Locals.init []⟩ c) h1
  have hm1 : m₁ = s₀.mem := by rw [← hs₁', hm₁]
  subst hm1
  cases h2 : callE p n "nat_lit_supported" [vis] s₀.mem with
  | error e2 =>
    rw [h2, reduceNatWfE.k_nat_lit_supported.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfNatE_nv "nat_lit_supported" (by simp)) h2
  | ok q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  simp only [reduceNatWfE.k_nat_lit_supported] at hW
  obtain ⟨hok2, hS2, hres2, hfr2, hrh2⟩ := callW_natLitSupported p hp n s₀ a₀ dn vis fe MM eb hC r₂ m₂
    (callW_of_callE h2)
  have hsup : (natLitSupported fe).run a₀ = .ok (decBool r₂, AM.st (natLitSupported fe) a₀) := by
    have := AM.run_of_ok _ _ hok2
    rw [hres2] at this
    exact this
  generalize AM.st (natLitSupported fe) a₀ = a₁ at hsup hS2
  have hwf := natOpWfNames_run hC.pins
  have hcont := wfContains hC.pins c hc
  have hbool : ∀ (hh : r₁.headD 0 ≠ 0 ∧ r₂.headD 0 ≠ 0), (([decI (pinW s₀.mem 22), decI (pinW s₀.mem 23),
      decI (pinW s₀.mem 24), decI (pinW s₀.mem 25), decI (pinW s₀.mem 26), decI (pinW s₀.mem 27),
      decI (pinW s₀.mem 28), decI (pinW s₀.mem 29)] : List NIdx).contains (decI c) && decBool r₂) = true := by
    intro hh
    rw [hcont]
    have h1 : natOpWfSel (pinW s₀.mem) c = true := by rw [← hwfsel]; simpa using hh.1
    have h2 : decBool r₂ = true := by simp only [decBool, bne_iff_ne, ne_eq]; exact hh.2
    rw [h1, h2]; rfl
  by_cases hg1 : r₁.headD 0 = 0
  · rw [if_neg (fun h => h hg1)] at hW; cases hW
  rw [if_pos hg1] at hW
  by_cases hg2 : r₂.headD 0 = 0
  · rw [if_neg (fun h => h hg2)] at hW; cases hW
  rw [if_pos hg2] at hW
  have hgo : r₁.headD 0 ≠ 0 ∧ r₂.headD 0 ≠ 0 := ⟨hg1, hg2⟩
  have hSP1 : SlotPre ⟨m₂, Locals.init []⟩ a₁ dn vis fe MM eb mode := ⟨hS2, hS.mode4, hS.eb_mode⟩
  cases h3 : callE p n "whnf" [mode, vis, d, a] m₂ with
  | error e3 =>
    rw [h3, reduceNatWfE.k_whnf.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => redWf_err_a _ _ _ _ _ _ a₀ a₁ _ hwf _ hsup (hbool hgo) ce h')
      (CoreSpecE.of_callE (hknE.whnf F ⟨m₂, Locals.init []⟩ a₁ dn vis fe MM eb mode d a (by omega)
        (by omega) hSP1 ha) h3)
  | ok q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  simp only [reduceNatWfE.k_whnf] at hW
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := CoreSpec.of_callW
    (hkn.whnf F ⟨m₂, Locals.init []⟩ a₁ dn vis fe MM eb mode d a (by omega) (by omega) hSP1 ha)
    (callW_of_callE h3)
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE a)) a₁ = a₂ at hrun3 hS₃
  cases h4 : callE p n "raw_nat_lit" [r₃.headD 0] m₃ with
  | error e4 =>
    rw [h4, reduceNatWfE.k_raw_nat_lit.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfNatE_nv "raw_nat_lit" (by simp)) h4
  | ok q₄ =>
  obtain ⟨r₄, m₄⟩ := q₄
  rw [h4] at hW
  simp only [reduceNatWfE.k_raw_nat_lit] at hW
  obtain ⟨hm4, hrun4, hres4, hslice4⟩ := callW_rawNatLit p hp n ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb _
    hS₃ hrw3 r₄ m₄ (callW_of_callE h4)
  subst m₄
  by_cases hf4 : r₄.headD 0 = 0
  · rw [if_neg (fun h => h hf4)] at hW; cases hW
  rw [if_pos hf4] at hW
  have hsome4 : rawDec m₃ r₄ = some (pv (vpool m₃) (r₄.tail.headD 0).toNat
      (r₄.tail.tail.headD 0).toNat) := by unfold rawDec; rw [if_neg hf4]
  rw [hsome4] at hrun4
  have hSP3 : SlotPre ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb mode := ⟨hS₃, hS.mode4, hS.eb_mode⟩
  cases h5 : callE p n "whnf" [mode, vis, d, b] m₃ with
  | error e5 =>
    rw [h5, reduceNatWfE.k_whnf_2.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => redWf_err_b _ _ _ _ _ _ a₀ a₁ a₂ a₂ _ hwf _ hsup (hbool hgo)
        (decE (r₃.headD 0)) _ (by rw [hrun3]; rfl) hrun4 ce h')
      (CoreSpecE.of_callE (hknE.whnf F ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb mode d b (by omega)
        (by omega) hSP3 hb) h5)
  | ok q₅ =>
  obtain ⟨r₅, m₅⟩ := q₅
  rw [h5] at hW
  simp only [reduceNatWfE.k_whnf_2] at hW
  obtain ⟨hok5, ⟨M₅, hS₅, hK₅, hSt₅⟩, hres5, hrw5⟩ := CoreSpec.of_callW
    (hkn.whnf F ⟨m₃, Locals.init []⟩ a₂ dn vis fe M₃ eb mode d b (by omega) (by omega) hSP3 hb)
    (callW_of_callE h5)
  have hrun5 := AM.run_of_ok _ _ hok5
  rw [hres5] at hrun5
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE b)) a₂ = a₃ at hrun5 hS₅
  cases h6 : callE p n "raw_nat_lit" [r₅.headD 0] m₅ with
  | error e6 =>
    rw [h6, reduceNatWfE.k_raw_nat_lit_2.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfNatE_nv "raw_nat_lit" (by simp)) h6
  | ok q₆ =>
  obtain ⟨r₆, m₆⟩ := q₆
  rw [h6] at hW
  simp only [reduceNatWfE.k_raw_nat_lit_2] at hW
  obtain ⟨hm6, hrun6, hres6, hslice6⟩ := callW_rawNatLit p hp n ⟨m₅, Locals.init []⟩ a₃ dn vis fe M₅ eb _
    hS₅ hrw5 r₆ m₆ (callW_of_callE h6)
  subst m₆
  by_cases hf6 : r₆.headD 0 = 0
  · rw [if_neg (fun h => h hf6)] at hW; cases hW
  rw [if_pos hf6] at hW
  cases hW
  have hsome6 : rawDec m₅ r₆ = some (pv (vpool m₅) (r₆.tail.headD 0).toNat
      (r₆.tail.tail.headD 0).toNat) := by unfold rawDec; rw [if_neg hf6]
  rw [hsome6] at hrun6
  refine ErrClaim.of_run_eq' (a' := a₀)
    (T' := (ConRon.Arena.fail (.notImplemented "native Nat computation on literals") : AM (Option EIdx)))
    ?_ (ErrClaim.fail _ _ rfl)
  rw [redWf_fail _ _ _ _ _ _ a₀ a₁ a₂ a₂ a₃ a₃ _ hwf _ hsup (hbool hgo)
      (decE (r₃.headD 0)) (decE (r₅.headD 0)) _ _ (by rw [hrun3]; rfl) hrun4 (by rw [hrun5]; rfl) hrun6]
  rfl

end wf

section opsucc
variable (p : Prog) (hp : WhnfDeltaProg' p) (hnv : closedNV p L.Checker.nvFns = true)

include hp hnv in
/-- **`reduce_nat_op`'s verdicts** are the operands' head normalizations'. -/
theorem callE_reduceNatOp (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d c a b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode) (ha : HW a)
    (hb : HW b) (er : Err)
    (h : callE p n "reduce_nat_op" [mode, vis, d, c, a, b] s₀.mem = .error er) :
    ErrClaim (redOpT (coreKnot (decMode mode) fe id F) d.toNat (decI c) (decE a) (decE b)) a₀ er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  cases n with
  | zero => exact ErrClaim.of_callE_zero h
  | succ n =>
  have hW := triple_of_callE_err (reduceNatOp_specE p hp.reduceNatOp (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d c a b) h (Err.code_ne_of_cls hk0)
  simp only [reduceNatOpE] at hW
  have hkn : KnotOK p n := hk n (by omega)
  have hknE : KnotOKE p n := hkE n (by omega)
  cases h1 : callE p n "whnf" [mode, vis, d, a] s₀.mem with
  | error e1 =>
    rw [h1, reduceNatOpE.k_whnf.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => redOp_err_a (ce := ce) (hw := h') ..)
      (CoreSpecE.of_callE (hknE.whnf F s₀ a₀ dn vis fe MM eb mode d a (by omega) (by omega) hS ha) h1)
  | ok q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  simp only [reduceNatOpE.k_whnf] at hW
  obtain ⟨hok1, ⟨M₁, hS₁, -, -⟩, hres1, hrw1⟩ := CoreSpec.of_callW
    (hkn.whnf F s₀ a₀ dn vis fe MM eb mode d a (by omega) (by omega) hS ha) (callW_of_callE h1)
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE a)) a₀ = a₁ at hrun1 hS₁
  cases h2 : callE p n "raw_nat_lit" [r₁.headD 0] m₁ with
  | error e2 =>
    rw [h2, reduceNatOpE.k_raw_nat_lit.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfNatE_nv "raw_nat_lit" (by simp)) h2
  | ok q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  simp only [reduceNatOpE.k_raw_nat_lit] at hW
  obtain ⟨hm2, hrun2, -, -⟩ := callW_rawNatLit p hp n ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb _
    hS₁ hrw1 r₂ m₂ (callW_of_callE h2)
  subst m₂
  by_cases hf2 : r₂.headD 0 = 0
  · rw [if_pos hf2] at hW; cases hW
  rw [if_neg hf2] at hW
  have hsome2 : rawDec m₁ r₂ = some (pv (vpool m₁) (r₂.tail.headD 0).toNat
      (r₂.tail.tail.headD 0).toNat) := by unfold rawDec; rw [if_neg hf2]
  rw [hsome2] at hrun2
  have hSP1 : SlotPre ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode := ⟨hS₁, hS.mode4, hS.eb_mode⟩
  cases h3 : callE p n "whnf" [mode, vis, d, b] m₁ with
  | error e3 =>
    rw [h3, reduceNatOpE.k_whnf_2.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => redOp_err_b (hw := by rw [hrun1]; rfl) (hr := hrun2)
        (ce := ce) (hw2 := h') ..)
      (CoreSpecE.of_callE (hknE.whnf F ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode d b (by omega)
        (by omega) hSP1 hb) h3)
  | ok q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  simp only [reduceNatOpE.k_whnf_2] at hW
  cases h4 : callE p n "raw_nat_lit" [r₃.headD 0] m₃ with
  | error e4 =>
    rw [h4, reduceNatOpE.k_raw_nat_lit_2.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfNatE_nv "raw_nat_lit" (by simp)) h4
  | ok q₄ =>
  obtain ⟨r₄, m₄⟩ := q₄
  rw [h4] at hW
  simp only [reduceNatOpE.k_raw_nat_lit_2] at hW
  split at hW
  · cases hW
  exact ErrClaim.of_callE_nv hnv (whnfNatE_nv "nat_op_result" (by simp))
    (err_of_k (by intro q e; simp [reduceNatOpE.k_nat_op_result]) (fun _ => rfl) hW)

include hp hnv in
/-- **`reduce_nat_succ`'s verdicts** are the argument's head normalization's. -/
theorem callE_reduceNatSucc (n F : Nat) (hF : n ≤ F) (hn2 : n ≤ 2 ^ 62)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d c b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode) (hc : HW c) (hb : HW b)
    (er : Err) (h : callE p n "reduce_nat_succ" [mode, vis, d, c, b] s₀.mem = .error er) :
    ErrClaim (redSuccT (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decE b)) a₀ er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hC := hS.rel
  cases n with
  | zero => exact ErrClaim.of_callE_zero h
  | succ n =>
  have hW := triple_of_callE_err (reduceNatSucc_specE p hp.reduceNatSucc (n + 1)
    ⟨s₀.mem, Locals.init []⟩ mode vis d c b) h (Err.code_ne_of_cls hk0)
  simp only [reduceNatSuccE] at hW
  cases h1 : callE p n "nat_lit_supported" [vis] s₀.mem with
  | error e1 =>
    rw [h1, reduceNatSuccE.k_nat_lit_supported.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfNatE_nv "nat_lit_supported" (by simp)) h1
  | ok q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  simp only [reduceNatSuccE.k_nat_lit_supported] at hW
  obtain ⟨hok1, hS1, hres1, hfr1, -⟩ := callW_natLitSupported p hp n s₀ a₀ dn vis fe MM eb hC r₁ m₁
    (callW_of_callE h1)
  cases h2 : callE p n "pin_at" [3] m₁ with
  | error e2 =>
    rw [h2, reduceNatSuccE.k_pin_at.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfNatE_nv "pin_at" (by simp)) h2
  | ok q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  simp only [reduceNatSuccE.k_pin_at] at hW
  obtain ⟨hm2, -, -, hr₂⟩ := callW_pinAt p hp.pinAt n m₁ 3 r₂ m₂ (callW_of_callE h2)
  subst m₂
  simp only [show (3 : Word).toNat = 3 from rfl] at hr₂
  have hr₂' : r₂.headD 0 = pinW s₀.mem 4 := by rw [hr₂, pinW_const_frame hfr1]
  have hsup : (natLitSupported fe).run a₀ = .ok (decBool r₁, AM.st (natLitSupported fe) a₀) := by
    have := AM.run_of_ok _ _ hok1
    rw [hres1] at this
    exact this
  generalize AM.st (natLitSupported fe) a₀ = a₁ at hsup hS1
  have hcw : HW (pinW s₀.mem 4) := hC.pins.names_lt 3 (by decide)
  by_cases hcn : c ≠ r₂.headD 0
  · rw [if_pos hcn] at hW; cases hW
  rw [if_neg hcn] at hW
  by_cases hs0 : r₁.headD 0 = 0
  · rw [if_pos hs0] at hW; cases hW
  rw [if_neg hs0] at hW
  have hcond : ((decI c : NIdx) == decI (pinW s₀.mem 4) && decBool r₁) = true := by
    rw [decI_beq _ _ hc hcw]
    have h1 : c = pinW s₀.mem 4 := by rw [← hr₂']; simpa using hcn
    have h2 : decBool r₁ = true := by simp only [decBool, bne_iff_ne, ne_eq]; exact hs0
    rw [h2]; simp [h1]
  have hSP1 : SlotPre ⟨m₁, Locals.init []⟩ a₁ dn vis fe MM eb mode := ⟨hS1, hS.mode4, hS.eb_mode⟩
  cases h3 : callE p n "whnf" [mode, vis, d, b] m₁ with
  | error e3 =>
    rw [h3, reduceNatSuccE.k_whnf.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => redSucc_err _ _ _ _ _ _ _ _ hC.pins _ hsup hcond ce h')
      (CoreSpecE.of_callE ((hkE n (by omega)).whnf F ⟨m₁, Locals.init []⟩ a₁ dn vis fe MM eb mode d b
        (by omega) (by omega) hSP1 hb) h3)
  | ok q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  simp only [reduceNatSuccE.k_whnf] at hW
  cases h4 : callE p n "raw_nat_lit" [r₃.headD 0] m₃ with
  | error e4 =>
    rw [h4, reduceNatSuccE.k_raw_nat_lit.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfNatE_nv "raw_nat_lit" (by simp)) h4
  | ok q₄ =>
  obtain ⟨r₄, m₄⟩ := q₄
  rw [h4] at hW
  simp only [reduceNatSuccE.k_raw_nat_lit] at hW
  split at hW
  · cases hW
  exact ErrClaim.of_callE_nv hnv (whnfNatE_nv "nat_succ_lit" (by simp))
    (err_of_k (by intro q e; simp [reduceNatSuccE.k_nat_succ_lit]) (fun _ => rfl) hW)

end opsucc

section head
variable (p : Prog) (hp : WhnfDeltaProg' p) (hnv : closedNV p L.Checker.nvFns = true)

theorem hbne_dec (v w : Word) (hv : HW v) (hw : HW w) :
    ((decI v : LsIdx) != decI w) = !decide (v = w) := by
  simp only [bne, decI_beq v w hv hw]

include hp hnv in
/-- **`reduce_nat_k`'s verdicts** are `reduce_nat_succ`'s (at a constant head). -/
theorem callE_reduceNatK (N F : Nat) (hF : N ≤ F) (hn2 : N ≤ 2 ^ 62)
    (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hf : HW f) (hb : HW b) (hg3 : f >>> 28 = 3) (hsc : ¬(tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0))
    (er : Err) (h : callE p N "reduce_nat_k" [mode, vis, d, f, b] s₀.mem = .error er) :
    ErrClaim (redHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b)) a₀ er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hC := hS.rel
  cases N with
  | zero => exact ErrClaim.of_callE_zero h
  | succ n =>
  have hW := triple_of_callE_err (reduceNatK_specE p hp.reduceNatK (n + 1)
    ⟨s₀.mem, Locals.init []⟩ mode vis d f b) h (Err.code_ne_of_cls hk0)
  simp only [reduceNatKE] at hW
  by_cases hbd : tcnt s₀.mem CONST (tierW f) ≤ idxW f
  · rw [if_pos hbd] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg hbd] at hW
  obtain ⟨n_, us_, hview, hn, hu, hnl, hul⟩ :=
    view_const_words s₀.mem a₀ hC.arena.1 f hf ⟨hsc, by simpa using hbd⟩ hg3
  subst hn hu
  cases h1 : callE p n "pin_word" [52] s₀.mem with
  | error e1 =>
    rw [h1, reduceNatKE.k_pin_word.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfNatE_nv "pin_word" (by simp)) h1
  | ok q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  simp only [reduceNatKE.k_pin_word] at hW
  obtain ⟨hm1, -, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₁ m₁ (callW_of_callE h1)
  subst m₁
  simp only [show (52 : Word).toNat = 52 from rfl] at hr₁
  have hel : emptyLevels.run a₀ = .ok (decI (pinW s₀.mem 52), a₀) := pinEmptyLevels_run hC.pins
  by_cases hne : tfld s₀.mem CONST (tierW f) (idxW f) 1 ≠ r₁.headD 0
  · rw [if_pos hne] at hW; cases hW
  rw [if_neg hne] at hW
  have hne' : tfld s₀.mem CONST (tierW f) (idxW f) 1 = pinW s₀.mem 52 := by
    rw [← hr₁]; simpa using hne
  have hcongr := redConst_eq (coreKnot (decMode mode) fe id F) fe d.toNat
    (decI (tfld s₀.mem CONST (tierW f) (idxW f) 0)) (decI (tfld s₀.mem CONST (tierW f) (idxW f) 1))
    (decI (pinW s₀.mem 52)) (decE b) a₀ hel (by rw [hbne_dec _ _ hul hC.pins.lv_lt.1]; simp [hne'])
  have hcg := redHead_const (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b) a₀ _ _ hview
  refine ErrClaim.of_run_eq' (hcg.trans hcongr) ?_
  exact callE_reduceNatSucc p hp hnv n F (by omega) (by omega) (hk.mono (by omega)) (hkE.mono (by omega))
    s₀ a₀ dn vis fe MM eb mode d _ b hS hnl hb er
    (err_of_k (by intro q e; simp [reduceNatKE.k_reduce_nat_succ]) (fun _ => rfl) hW)

include hp hnv in
/-- **`reduce_nat_ap`'s verdicts** are `reduce_nat_op`'s or `reduce_nat_wf`'s (at a binary
application of a constant). -/
theorem callE_reduceNatAp (N F : Nat) (hF : N ≤ F) (hn2 : N ≤ 2 ^ 62)
    (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode) (hf : HW f) (hb : HW b)
    (hg4 : f >>> 28 = 4) (hsc : ¬(tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0))
    (er : Err) (h : callE p N "reduce_nat_ap" [mode, vis, d, f, b] s₀.mem = .error er) :
    ErrClaim (redHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b)) a₀ er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hC := hS.rel
  cases N with
  | zero => exact ErrClaim.of_callE_zero h
  | succ n =>
  have hW := triple_of_callE_err (reduceNatAp_specE p hp.reduceNatAp (n + 1)
    ⟨s₀.mem, Locals.init []⟩ mode vis d f b) h (Err.code_ne_of_cls hk0)
  simp only [reduceNatApE] at hW
  by_cases hbd : tcnt s₀.mem APP (tierW f) ≤ idxW f
  · rw [if_pos hbd] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg hbd] at hW
  obtain ⟨hviewf, hgw, hxw⟩ := view_app s₀.mem a₀ hC.arena.1 f hf ⟨hsc, by simpa using hbd⟩ hg4
  have hcgH := redHead_app (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b) _ _ a₀ hviewf
  refine ErrClaim.of_run_eq' hcgH ?_
  generalize tfld s₀.mem APP (tierW f) (idxW f) 0 = gw at hW hgw hviewf
  generalize tfld s₀.mem APP (tierW f) (idxW f) 1 = xw at hW hxw hviewf
  by_cases g3 : gw >>> 28 ≠ 3
  · rw [if_pos g3] at hW; cases hW
  rw [if_neg g3] at hW
  have g3' : gw >>> 28 = 3 := by simpa using g3
  have ht : ((decE (gw)).tag == ETag.const) = true := by
    rw [decE_const_tag _ hgw]; exact beq_iff_eq.mpr g3'
  by_cases hs2 : tierW (gw) ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos hs2] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg hs2] at hW
  by_cases hb2 : tcnt s₀.mem CONST (tierW (gw)) ≤ idxW (gw)
  · rw [if_pos hb2] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg hb2] at hW
  obtain ⟨n_, us_, hview, hn, hu, hnl, hul⟩ := view_const_words s₀.mem a₀ hC.arena.1 _ hgw
    ⟨hs2, by simpa using hb2⟩ g3'
  subst hn hu
  generalize tfld s₀.mem CONST (tierW gw) (idxW gw) 0 = cw at *
  generalize tfld s₀.mem CONST (tierW gw) (idxW gw) 1 = uw at *
  cases h1 : callE p n "pin_word" [52] s₀.mem with
  | error e1 =>
    rw [h1, reduceNatApE.k_pin_word.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfNatE_nv "pin_word" (by simp)) h1
  | ok q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  simp only [reduceNatApE.k_pin_word] at hW
  obtain ⟨hm1, hflag, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₁ m₁ (callW_of_callE h1)
  subst m₁
  simp only [show (52 : Word).toNat = 52 from rfl] at hr₁
  have hel : emptyLevels.run a₀ = .ok (decI (pinW s₀.mem 52), a₀) := pinEmptyLevels_run hC.pins
  by_cases hne : uw ≠ r₁.headD 0
  · rw [if_pos hne] at hW; cases hW
  rw [if_neg hne] at hW
  have hne' : uw = pinW s₀.mem 52 := by rw [← hr₁]; simpa using hne
  have hcongrApp := redApp_eq (coreKnot (decMode mode) fe id F) fe d.toNat (decE gw) (decE xw) (decE b) a₀
    (decI cw) (decI uw) (decI (pinW s₀.mem 52)) ht hview hel
    (by rw [hbne_dec _ _ hul hC.pins.lv_lt.1]; simp [hne'])
  cases h2 : callE p n "nat_bin_op_name" [cw] s₀.mem with
  | error e2 =>
    rw [h2, reduceNatApE.k_nat_bin_op_name.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfNatE_nv "nat_bin_op_name" (by simp)) h2
  | ok q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  simp only [reduceNatApE.k_nat_bin_op_name] at hW
  obtain ⟨t₂, ht₂, hm₂, -, hsel2, -⟩ := triple_of_callE
    (natBinOpNameL_spec p hp.natBinOpName n ⟨s₀.mem, Locals.init []⟩ hflag cw) h2
  have hm2 : m₂ = s₀.mem := by rw [← ht₂, hm₂]
  subst hm2
  cases h3 : callE p n "nat_op_stored" [vis, cw] s₀.mem with
  | error e3 =>
    rw [h3, reduceNatApE.k_nat_op_stored.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfNatE_nv "nat_op_stored" (by simp)) h3
  | ok q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  simp only [reduceNatApE.k_nat_op_stored] at hW
  obtain ⟨hok3, hS3, hres3, hfr3, hrh3⟩ := callW_natOpStored p hp n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis
    fe MM eb cw hC hnl r₃ m₃ (callW_of_callE h3)
  obtain ⟨b3, hb3⟩ := natOpStored_run_pure fe (decI cw) a₀
  have hst3 : AM.st (natOpStored fe (decI cw)) a₀ = a₀ := (AM.of_run_ok _ _ _ _ hb3).2.1
  have hbb3 : b3 = decBool r₃ := by
    have := (AM.of_run_ok _ _ _ _ hb3).2.2
    rw [hres3] at this; exact this.symm
  rw [hst3] at hS3
  have hbin : (natBinOpName (decI cw)).run a₀ = .ok (natBinOpSel (pinW s₀.mem ) cw, a₀) :=
    natBinOpName_run hC.pins cw hnl
  have hSP3 : SlotPre ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb mode := ⟨hS3, hS.mode4, hS.eb_mode⟩
  have hbool : (natBinOpSel (pinW s₀.mem) cw && decBool r₃) =
      decide (r₂.headD 0 ≠ 0 ∧ r₃.headD 0 ≠ 0) := by
    rw [← hsel2]; exact bne_and_bne _ _
  have hredbin := redBin_run (coreKnot (decMode mode) fe id F) fe d.toNat (decI cw) (decE xw) (decE b) a₀
    (natBinOpSel (pinW s₀.mem) cw) (decBool r₃) hbin (by rw [hb3, hbb3])
  by_cases hgo : r₂.headD 0 ≠ 0 ∧ r₃.headD 0 ≠ 0
  · rw [if_pos hgo] at hW
    have hcg : (redAppT (coreKnot (decMode mode) fe id F) fe d.toNat (decE gw) (decE xw) (decE b)).run a₀ =
        (redOpT (coreKnot (decMode mode) fe id F) d.toNat (decI cw) (decE xw) (decE b)).run a₀ := by
      rw [hcongrApp, hredbin, hbool, decide_eq_true hgo]; rfl
    exact ErrClaim.of_run_eq' hcg (callE_reduceNatOp p hp hnv n F (by omega) (by omega)
      (hk.mono (by omega)) (hkE.mono (by omega)) ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb mode d cw xw b
      hSP3 hxw hb er (err_of_k (by intro q e; simp [reduceNatApE.k_reduce_nat_op]) (fun _ => rfl) hW))
  · rw [if_neg hgo] at hW
    have hcg : (redAppT (coreKnot (decMode mode) fe id F) fe d.toNat (decE gw) (decE xw) (decE b)).run a₀ =
        (redWfT (coreKnot (decMode mode) fe id F) fe d.toNat (decI cw) (decE xw) (decE b)).run a₀ := by
      rw [hcongrApp, hredbin, hbool, decide_eq_false hgo]; rfl
    exact ErrClaim.of_run_eq' hcg (callE_reduceNatWf p hp hnv n F (by omega) (by omega)
      (hk.mono (by omega)) (hkE.mono (by omega)) ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb mode d cw xw b
      hSP3 hnl hxw hb er (err_of_k (by intro q e; simp [reduceNatApE.k_reduce_nat_op]) (fun _ => rfl) hW))

include hp hnv in
/-- **`reduce_nat_head`'s verdicts**: `reduce_nat_k`'s and `reduce_nat_ap`'s. -/
theorem callE_reduceNatHead (N F : Nat) (hF : N ≤ F) (hn2 : N ≤ 2 ^ 62)
    (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode) (hf : HW f) (hb : HW b)
    (er : Err) (h : callE p N "reduce_nat_head" [mode, vis, d, f, b] s₀.mem = .error er) :
    ErrClaim (redHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b)) a₀ er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  cases N with
  | zero => exact ErrClaim.of_callE_zero h
  | succ n =>
  have hW := triple_of_callE_err (reduceNatHead_specE p hp.reduceNatHead (n + 1)
    ⟨s₀.mem, Locals.init []⟩ mode vis d f b) h (Err.code_ne_of_cls hk0)
  simp only [reduceNatHeadE] at hW
  by_cases hsc : tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos hsc] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg hsc] at hW
  by_cases g3 : f >>> 28 = 3
  · rw [if_pos g3] at hW
    exact callE_reduceNatK p hp hnv n F (by omega) (by omega) (hk.mono (by omega)) (hkE.mono (by omega))
      s₀ a₀ dn vis fe MM eb mode d f b hS hf hb g3 hsc er
      (err_of_k (by intro q e; simp [reduceNatHeadE.k_reduce_nat_k]) (fun _ => rfl) hW)
  rw [if_neg g3] at hW
  by_cases g4 : f >>> 28 = 4
  · rw [if_pos g4] at hW
    exact callE_reduceNatAp p hp hnv n F (by omega) (by omega) (hk.mono (by omega)) (hkE.mono (by omega))
      s₀ a₀ dn vis fe MM eb mode d f b hS hf hb g4 hsc er
      (err_of_k (by intro q e; simp [reduceNatHeadE.k_reduce_nat_k]) (fun _ => rfl) hW)
  rw [if_neg g4] at hW
  repeat' split at hW
  all_goals (cases hW <;> exact ErrClaim.of_cls0 rfl)

include hp hnv in
/-- **`reduce_nat`'s verdicts** (`reduceNat`): `reduce_nat_head`'s. -/
theorem callE_reduceNat (N F : Nat) (hF : N ≤ F) (hn2 : N ≤ 2 ^ 62)
    (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d e : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e)
    (er : Err) (h : callE p N "reduce_nat" [mode, vis, d, e] s₀.mem = .error er) :
    ErrClaim (reduceNat (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) a₀ er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hC := hS.rel
  cases N with
  | zero => exact ErrClaim.of_callE_zero h
  | succ n =>
  have hW := triple_of_callE_err (reduceNat_specE p hp.reduceNat (n + 1)
    ⟨s₀.mem, Locals.init []⟩ mode vis d e) h (Err.code_ne_of_cls hk0)
  simp only [reduceNatE] at hW
  by_cases g4 : e >>> 28 ≠ 4
  · rw [if_pos g4] at hW; cases hW
  rw [if_neg g4] at hW
  have g4' : e >>> 28 = 4 := by simpa using g4
  have hap : ((decE e).tag == ETag.app) = true := beq_iff_eq.mpr ((decE_tag_app e he).mpr g4')
  by_cases hsc : tierW e ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos hsc] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg hsc] at hW
  by_cases hbd : tcnt s₀.mem APP (tierW e) ≤ idxW e
  · rw [if_pos hbd] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg hbd] at hW
  obtain ⟨hview, hfw, hbw⟩ := view_app s₀.mem a₀ hC.arena.1 e he ⟨hsc, by simpa using hbd⟩ g4'
  refine ErrClaim.of_run_eq' (reduceNat_head_eq (coreKnot (decMode mode) fe id F) fe d.toNat (decE e) _ _ a₀
    hap hview) ?_
  exact callE_reduceNatHead p hp hnv n F (by omega) (by omega) (hk.mono (by omega)) (hkE.mono (by omega))
    s₀ a₀ dn vis fe MM eb mode d _ _ hS hfw hbw er
    (err_of_k (by intro q e; simp [reduceNatE.k_reduce_nat_head]) (fun _ => rfl) hW)

include hp hnv in
/-- **`ReduceNatE`**: `reduce_nat`'s error claim, the `whnf_step` slot body's hypothesis. -/
theorem reduceNatE_of : ReduceNatE p :=
  fun N hk hkE F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he =>
    CoreSpecE.of_runs fun er h =>
      callE_reduceNat p hp hnv N F hF hn hk hkE s₀ a₀ dn vis fe MM eb
        mode d e hs he er h

end head

end L.Arena
