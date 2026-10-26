import ConAgua.Verdict.WhnfM2CE

/-!
# `proof_irrel`'s verdict claims (lane `verdicts-b`, helper `k2`)

`proof_irrel_half`'s level comparison out of fuel declines (the twin's `liftFueled`); its other
claims are the `infer_io` and `whnf` slots'. The twin's `proofIrrel` is its two halves in
continuation style (`proofIrrel_eq_halves`, `piHalfT`); `proofIrrelE_of`: `ProofIrrelE`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace L.Arena

theorem whnfPirrE_nv : ∀ f ∈ ["pin_word", "lvl_eq_c"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-- One half of the twin's `proofIrrel`, in continuation style. -/
def piHalfT (r : CoreFnsA) (depth : Nat) (x : EIdx) (k : Bool → AM Bool) : AM Bool := do
  let ta ← r.inferIO depth x
  let hh ← r.whnf depth (← r.inferIO depth ta)
  if hh.tag == ETag.sort then
    match ← view hh with
    | .sort uT => do
      let z ← zeroLevel
      let ok ← liftFueled "level comparison" (← lvlEq? uT z)
      k ok
    | _ => pure false
  else pure false

theorem proofIrrel_eq_halves (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    proofIrrel r fe depth a b =
      piHalfT r depth a (fun okA => piHalfT r depth b (fun okB => pure (okA && okB))) := rfl

theorem piHalfT_run {r : CoreFnsA} {d : Nat} {x : EIdx} {a a' : AState} {w : Word}
    (h : PiHalfRun r d x a w a') (hw : w ≠ 0) (k : Bool → AM Bool) :
    (piHalfT r d x k).run a = (k (decide (w ≠ 1))).run a' := by
  obtain ⟨ta, tta, hh, a1, a2, a3, h1, h2, h3, h4⟩ := h
  rcases h4 with ⟨h0, -⟩ | ⟨-, ht, uT, z, a4, hv, hz, hl, rfl⟩
  · exact absurd h0 hw
  have hv' : (view hh).run a3 = .ok (.sort uT, a3) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  simp only [piHalfT, StateT.run_bind, h1, h2, h3, except_ok_bind, ht, beq_self_eq_true, ↓reduceIte,
    hv', hz, hl]
  simp [liftFueled, StateT.run_pure]

section halfErr
variable (r : CoreFnsA) (d : Nat) (x : EIdx) (k : Bool → AM Bool)

theorem half_err_io1 (a : AState) (ce : CheckError) (h1 : (r.inferIO d x).run a = .error ce) :
    (piHalfT r d x k).run a = .error ce := by
  simp only [piHalfT, StateT.run_bind, h1]; rfl

theorem half_err_io2 (a a1 : AState) (ta : EIdx) (h1 : (r.inferIO d x).run a = .ok (ta, a1))
    (ce : CheckError) (h2 : (r.inferIO d ta).run a1 = .error ce) :
    (piHalfT r d x k).run a = .error ce := by
  simp only [piHalfT, StateT.run_bind, h1, except_ok_bind, h2]; rfl

theorem half_err_whnf (a a1 a2 : AState) (ta tta : EIdx) (h1 : (r.inferIO d x).run a = .ok (ta, a1))
    (h2 : (r.inferIO d ta).run a1 = .ok (tta, a2)) (ce : CheckError)
    (h3 : (r.whnf d tta).run a2 = .error ce) :
    (piHalfT r d x k).run a = .error ce := by
  simp only [piHalfT, StateT.run_bind, h1, except_ok_bind, h2, h3]; rfl

theorem half_fail (a a1 a2 a3 a4 : AState) (ta tta hh : EIdx) (uT z : LIdx)
    (h1 : (r.inferIO d x).run a = .ok (ta, a1))
    (h2 : (r.inferIO d ta).run a1 = .ok (tta, a2)) (h3 : (r.whnf d tta).run a2 = .ok (hh, a3))
    (ht : hh.tag = ETag.sort) (hv : a3.store.view hh = some (.sort uT))
    (hz : zeroLevel.run a3 = .ok (z, a3)) (hl : (lvlEq? uT z).run a3 = .ok (none, a4)) :
    (piHalfT r d x k).run a =
      (ConRon.Arena.fail (.notImplemented "resource limit: fuel exhausted: level comparison") :
        AM Bool).run a4 := by
  have hv' : (view hh).run a3 = .ok (.sort uT, a3) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  simp only [piHalfT, StateT.run_bind, h1, h2, h3, except_ok_bind, ht, beq_self_eq_true, ↓reduceIte,
    hv', hz, hl]
  simp [liftFueled]; rfl

end halfErr

section half
variable (p : Prog) (hp : IotaProg4 p) (hld : LvlDen) (hnv : closedNV p L.Checker.nvFns = true)
include hp hld hnv

/-- **`proof_irrel_half`'s verdicts**: the level comparison out of fuel declines; the rest are the
slots'. -/
theorem pihE_ok (n F : Nat) (hknot : KnotUpTo p n) (hkE : KnotUpToE p n) (hnF : n ≤ F)
    (hn62 : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d x : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hx : HW x)
    (m : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (er : Err)
    (h : callE p (n + 1) "proof_irrel_half" [mode, vis, d, x] m = .error er) (k : Bool → AM Bool) :
    ErrClaim (piHalfT (coreKnot (decMode mode) fe id F) d.toNat (decE x) k) a er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (pihE_spec p hp.proofIrrelHalf (n + 1) ⟨m, Locals.init []⟩
    mode vis d x) h (Err.code_ne_of_cls hk0)
  simp only [pihE] at hW
  cases c1 : callE p n "infer_io" [mode, vis, d, x] m with
  | error e1 =>
    rw [c1, pihE.k_infer_io.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => half_err_io1 _ _ _ k a ce h')
      (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).inferIO F ⟨m, Locals.init []⟩ a dn vis fe M eb mode d
        x hnF hn62 ⟨hS, hm4, hebm⟩ hx) c1)
  | ok q =>
  obtain ⟨r1, m1⟩ := q
  rw [c1] at hW
  simp only [pihE.k_infer_io] at hW
  obtain ⟨hrun1, ⟨M1, hS1, -, -⟩, hr1⟩ := CoreSpec.run
    ((hknot n (Nat.le_refl _)).inferIO F ⟨m, Locals.init []⟩ a dn vis fe M eb mode d x hnF hn62
      ⟨hS, hm4, hebm⟩ hx) (callW_of_callE c1)
  cases c2 : callE p n "infer_io" [mode, vis, d, r1.headD 0] m1 with
  | error e2 =>
    rw [c2, pihE.k_infer_io_2.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => half_err_io2 _ _ _ k a _ _ hrun1 ce h')
      (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).inferIO F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d
        _ hnF hn62 ⟨hS1, hm4, hebm⟩ hr1) c2)
  | ok q =>
  obtain ⟨r2, m2⟩ := q
  rw [c2] at hW
  simp only [pihE.k_infer_io_2] at hW
  obtain ⟨hrun2, ⟨M2, hS2, -, -⟩, hr2⟩ := CoreSpec.run
    ((hknot n (Nat.le_refl _)).inferIO F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d _ hnF hn62
      ⟨hS1, hm4, hebm⟩ hr1) (callW_of_callE c2)
  cases c3 : callE p n "whnf" [mode, vis, d, r2.headD 0] m2 with
  | error e3 =>
    rw [c3, pihE.k_whnf.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => half_err_whnf _ _ _ k a _ _ _ _ hrun1 hrun2 ce h')
      (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).whnf F ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d
        _ hnF hn62 ⟨hS2, hm4, hebm⟩ hr2) c3)
  | ok q =>
  obtain ⟨r3, m3⟩ := q
  rw [c3] at hW
  simp only [pihE.k_whnf] at hW
  obtain ⟨hrun3, ⟨M3, hS3, -, -⟩, hr3⟩ := CoreSpec.run
    ((hknot n (Nat.le_refl _)).whnf F ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d _ hnF hn62
      ⟨hS2, hm4, hebm⟩ hr2) (callW_of_callE c3)
  by_cases h2 : r3.headD 0 >>> 28 ≠ 2
  · rw [if_pos h2] at hW; cases hW
  rw [if_neg h2] at hW
  have h2' : r3.headD 0 >>> 28 = 2 := by simpa using h2
  by_cases hv1 : tierW (r3.headD 0) ≠ 0 ∧ rdW (m3.arr64 CTL) 1 = 0
  · rw [if_pos hv1] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg hv1] at hW
  by_cases hv2 : tcnt m3 SORT (tierW (r3.headD 0)) ≤ idxW (r3.headD 0)
  · rw [if_pos hv2] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg hv2] at hW
  obtain ⟨hvw, hn32⟩ := view_sort_f m3 (AM.st _ _) hS3.arena.1 (r3.headD 0) hr3
    ⟨hv1, UInt64.not_le.mp hv2⟩ h2'
  generalize tfld m3 SORT (tierW (r3.headD 0)) (idxW (r3.headD 0)) 0 = uw at hvw hn32 hW
  cases c4 : callE p n "pin_word" [53] m3 with
  | error e4 =>
    rw [c4, pihE.k_pin_word.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfPirrE_nv "pin_word" (by simp)) c4
  | ok q =>
  obtain ⟨r4, m4⟩ := q
  rw [c4] at hW
  simp only [pihE.k_pin_word] at hW
  obtain ⟨t4, ht4, hloc4, hpw⟩ := triple_of_callE
    (pinWord_specM p hp.pinw n ⟨m3, Locals.init []⟩ 53) c4
  have hpw' : pinWordM m3 53 = some (r4, m4) := by simpa [ht4] using hpw
  obtain ⟨-, hpw'⟩ := of_ite_none hpw'
  obtain ⟨hr4, rfl⟩ := Prod.mk.inj (Option.some.inj hpw')
  have hP := hS3.pins
  have hr4' : r4.headD 0 = pinW m3 53 := by
    rw [← hr4]; simp [rdW, pinW]
  obtain ⟨a3, ha3⟩ : ∃ a3, a3 = AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat
      (decE (r2.headD 0))) (AM.st ((coreKnot (decMode mode) fe id F).inferIO d.toNat
      (decE (r1.headD 0))) (AM.st ((coreKnot (decMode mode) fe id F).inferIO d.toNat (decE x)) a)) :=
    ⟨_, rfl⟩
  rw [← ha3] at hrun3 hvw hS3 hP
  cases c5 : callE p n "lvl_eq_c" [uw, r4.headD 0] m3 with
  | error e5 =>
    rw [c5, pihE.k_lvl_eq_c.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfPirrE_nv "lvl_eq_c" (by simp)) c5
  | ok q =>
  obtain ⟨r5, m5⟩ := q
  rw [c5] at hW
  simp only [pihE.k_lvl_eq_c] at hW
  by_cases hw0 : ¬ r5.headD 0 = 0
  · rw [if_neg hw0] at hW; cases hW
  have hw0 := Classical.not_not.mp hw0
  rw [if_pos hw0] at hW
  cases hW
  rcases Nat.lt_or_ge n 2 with hsm | hbig
  · have := lvlEqC_small p hp.lvl.c n hsm [uw, r4.headD 0] m3
    rw [callW_of_callE c5] at this; cases this
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  obtain ⟨hdn1, hdn2⟩ := hld _ _ _ _ _ _ _ hS3
  obtain ⟨lu, hdu⟩ := hdn1 _ _ hvw
  have hzl : a3.pins.zeroLevel = decI (r4.headD 0) := by rw [hP.zeroLevel, hr4']
  obtain ⟨lz, hdz⟩ := hdn2
  rw [hzl] at hdz
  have hz32 : HW (r4.headD 0) := by rw [hr4']; exact hP.lv_lt.2.1
  obtain ⟨hrunL, -, -⟩ := CoreSpec.run
    (lvlEqC_refines p hp.lvl n' ⟨m3, Locals.init []⟩ a3 dn vis fe M3 eb hS3 uw (r4.headD 0)
      hn32 hz32 lu lz hdu hdz) (callW_of_callE c5)
  have hdo : decO (r5.headD 0) = none := by rw [hw0]; rfl
  simp only [hdo] at hrunL
  have hz : zeroLevel.run a3 = .ok (decI (r4.headD 0), a3) := by
    rw [hr4']; exact pinZeroLevel_run hP
  have htag : (decE (r3.headD 0)).tag = ETag.sort := (decE_tag_eq _ hr3 2 (by decide)).mpr h2'
  have hrun3' : (((coreKnot (decMode mode) fe id F).whnf d.toNat (decE (r2.headD 0))).run
      (AM.st ((coreKnot (decMode mode) fe id F).inferIO d.toNat (decE (r1.headD 0)))
        (AM.st ((coreKnot (decMode mode) fe id F).inferIO d.toNat (decE x)) a))) =
      .ok (decE (r3.headD 0), a3) := hrun3
  refine ErrClaim.of_run_eq' (half_fail _ _ _ k a _ _ a3 _ _ _ _ _ _ hrun1 hrun2 hrun3' htag hvw hz hrunL)
    (ErrClaim.fail _ _ rfl)

/-- **`ProofIrrelE`**: `proof_irrel`'s verdicts are its halves'. -/
theorem proofIrrelE_of : ProofIrrelE p := by
  intro n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d a b hS hm4 hebm ha hb
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (pirrE_spec p hp.proofIrrel (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hk0)
  simp only [pirrE] at hW
  rw [proofIrrel_eq_halves]
  cases n with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "proof_irrel_half" [mode, vis, d, a] s₀.mem
    rw [he', pirrE.k_proof_irrel_half.none] at hW; cases hW; exact absurd h0 hk0
  | succ n' =>
  cases c1 : callE p (n' + 1) "proof_irrel_half" [mode, vis, d, a] s₀.mem with
  | error e1 =>
    rw [c1, pirrE.k_proof_irrel_half.none] at hW; cases hW
    exact pihE_ok p hp hld hnv n' F (hk.mono (Nat.le_succ n')) (hkE.mono (Nat.le_succ n')) (by omega)
      (by omega) dn vis fe eb mode d a hm4 hebm ha s₀.mem a₀ MM hS _ c1 _
  | ok q =>
  obtain ⟨ra, m1⟩ := q
  rw [c1] at hW
  simp only [pirrE.k_proof_irrel_half] at hW
  obtain ⟨t1, ht1, -, hpa⟩ := triple_of_callE
    (proofIrrelHalf_spec p hp.proofIrrelHalf n' ⟨s₀.mem, Locals.init []⟩ mode vis d a) c1
  rw [ht1] at hpa
  obtain ⟨a1, hA1, ⟨M1, hS1, -, -⟩, -⟩ := pihW_ok p hp hld n' F (hk.mono (Nat.le_succ n')) (by omega)
    (by omega) dn vis fe eb mode d a hm4 hebm ha s₀.mem a₀ MM hS (ra.headD 0) m1 hpa
  by_cases hwa : ra.headD 0 = 0
  · rw [if_pos hwa] at hW; cases hW
  rw [if_neg hwa] at hW
  have hW' := err_of_k (by intro q e; simp only [pirrE.k_proof_irrel_half_2]; split <;> simp)
    (fun _ => rfl) hW
  refine ErrClaim.of_run_eq' (piHalfT_run hA1 hwa _) ?_
  exact pihE_ok p hp hld hnv n' F (hk.mono (Nat.le_succ n')) (hkE.mono (Nat.le_succ n')) (by omega)
    (by omega) dn vis fe eb mode d b hm4 hebm hb m1 a1 M1 hS1 _ hW' _

end half

end L.Arena
