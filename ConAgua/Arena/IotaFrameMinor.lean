module

public import ConAgua.Arena.IotaFrameFrame
import ConAgua.Arena.RecClassSpec.CloseLams
import ConAgua.L.WordOff

@[expose] public section

/-!
# `is_minor_at` refines `isMinorAt` (lane ronsync8)
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

/-- **`is_minor_at` refines `isMinorAt`**. -/
@[refines ConRon.Arena.isMinorAt]
theorem isMinorAt_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (preO preL mot q : Word) (pre : List EIdx) (hq : q.toNat < 2 ^ 32) :
    RelW (fun m args => callW p n "is_minor_at" args m) [preO, preL, mot, q]
      (fun m a => StageR vis fe m a ∧ decHL m preO.toNat preL.toNat = some pre ∧
        preO.toNat + preL.toNat ≤ iwTop m)
      (isMinorAt pre mot.toNat q.toNat) (KeepPost vis fe decW0B) := by
  intro m m' a r hc ⟨hS, hpre, htop⟩
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (isMinorAt_specW p P.is_minor_at n _ preO preL mot q) hc
  rcases n with _ | n
  · simp [isMinorAtW] at hW
  simp only [isMinorAtW] at hW
  rcases n with _ | n
  · simp [isMinorAtW.k_expr_get_d, callW_zero] at hW
  -- `expr_get_d`
  rcases h1 : callW p (n + 1) "expr_get_d" [preO, preL, q] m with _ | ⟨r1, m1⟩
  · rw [h1] at hW; simp [isMinorAtW.k_expr_get_d] at hW
  rw [h1] at hW
  obtain ⟨s1, hs1, -, hok1, hS1, hg1, hx1, hd1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (exprGetD_refines p P.bvar_find P.bvar_push P.intern_bvar P.expr_get_d n ⟨m, Locals.init []⟩ a
      (fun _ => none) vis fe preO preL q pre hS hpre (by have := iwTop_lt' m; omega)) h1
  simp only at hs1 hS1 hg1
  subst hs1
  unfold isMinorAt
  rw [StateT.run_bind, AM.run_of_ok _ _ hok1, except_ok_bind]
  generalize AM.res (ConRon.Arena.exprGetD pre q.toNat) a = x1 at hd1 ⊢
  generalize AM.st (ConRon.Arena.exprGetD pre q.toNat) a = a1 at hS1 ⊢
  simp only [isMinorAtW.k_expr_get_d] at hW
  -- `pi_tele`
  rcases h2 : callW p (n + 1) "pi_tele" [r1.headD 0] s1.mem with _ | ⟨r2, m2⟩
  · rw [h2] at hW; simp [isMinorAtW.k_pi_tele] at hW
  rw [h2] at hW
  obtain ⟨x2, a2, hrun2, hS2, hg2, hn2, hh2, hb2, hc2⟩ :=
    piTele_rel P.pi_tele P.e_view (n + 1) vis fe (r1.headD 0) hx1 _ _ a1 r2 h2 hS1
  rw [decE_eq, hd1] at hrun2
  rw [StateT.run_bind, hrun2, except_ok_bind]
  simp only [isMinorAtW.k_pi_tele] at hW
  -- `get_app_fn_f`
  rcases h3 : callW p (n + 1) "get_app_fn_f" [CWF, r2.tail.headD 0] m2 with _ | ⟨r3, m3⟩
  · rw [h3] at hW; simp [isMinorAtW.k_get_app_fn_f] at hW
  rw [h3] at hW
  obtain ⟨s3, hs3, -, hg3'⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩) (gafF_spec0 p P.gaf _ _ _) h3
  rw [hs3] at hg3'
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3, hd3⟩ := gafF_ok vis fe CWF _ hh2 m2 m3 a2 r3 hg3' hS2
  rw [CWF_eq, ← decE_eq, hb2] at hrun3
  rw [StateT.run_bind, hrun3, except_ok_bind]
  simp only [isMinorAtW.k_get_app_fn_f] at hW
  dsimp only
  have tb : ((decE (r3.headD 0)).tag == ETag.bvar) = decide (tagW (r3.headD 0) = 0) :=
    decE_tag_beq _ hx3 0 (by decide)
  rw [← hd3, ← decE_eq, tb]
  have hg := hg1.trans (hg2.trans hg3)
  by_cases g0 : tagW (r3.headD 0) ≠ 0
  · rw [ite_eq_left g0] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨false, a3, by rw [ite_eq_right (by simpa using g0)]; rfl, hS3, hg, by simp, by simp⟩
  rw [ite_eq_right g0] at hW
  have g0 : tagW (r3.headD 0) = 0 := Classical.not_not.mp g0
  rcases h4 : callW p (n + 1) "e_view" [r3.headD 0] m3 with _ | ⟨r4, m4⟩
  · rw [h4] at hW; simp [isMinorAtW.k_e_view] at hW
  rw [h4] at hW
  obtain ⟨rfl, hv4⟩ := eView_bvar P.e_view hS3.check.arena.base g0 h4
  rw [ite_eq_left (by simpa using g0), StateT.run_bind, viewBVar_run', hv4, except_ok_bind]
  dsimp only
  simp only [isMinorAtW.k_e_view] at hW
  by_cases c1 : mot < q
  · rw [ite_eq_left c1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have c1' : mot.toNat < q.toNat := UInt64.lt_iff_toNat_lt.mp c1
    rw [ite_eq_left c1']
    have hq1 : (1 : Word) ≤ q := by rw [UInt64.le_iff_toNat_le]; simp; omega
    have hs1 : (q - 1).toNat = q.toNat - 1 := by rw [UInt64.toNat_sub_of_le _ _ hq1]; simp
    have hm1 : mot ≤ q - 1 := by rw [UInt64.le_iff_toNat_le, hs1]; omega
    have hs2 : (q - 1 - mot).toNat = q.toNat - 1 - mot.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ hm1, hs1]
    have hx2 : x2.1 < coreWalkFuel := by rw [← hn2]; exact hc2
    have e : (r2.headD 0 + (q - 1 - mot)).toNat = x2.1 + (q.toNat - 1 - mot.toNat) := by
      rw [UInt64.toNat_add, hs2, hn2]
      exact Nat.mod_eq_of_lt (by simp only [coreWalkFuel] at hx2; omega)
    refine ⟨_, a3, rfl, hS3, hg, ?_, ?_⟩
    · by_cases h : r4.tail.headD 0 = r2.headD 0 + (q - 1 - mot)
      · rw [ite_eq_left h]
        have : (r4.tail.headD 0).toNat = x2.1 + (q.toNat - 1 - mot.toNat) := by rw [h, e]
        rw [this, beq_self_eq_true]; rfl
      · rw [ite_eq_right h]
        have : (r4.tail.headD 0).toNat ≠ x2.1 + (q.toNat - 1 - mot.toNat) := by
          rw [← e]; exact fun h' => h (UInt64.toNat_inj.mp h')
        rw [beq_eq_false_iff_ne.mpr this]; rfl
    · split <;> simp
  · rw [ite_eq_right c1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have c1' : ¬ mot.toNat < q.toNat := fun h => c1 (UInt64.lt_iff_toNat_lt.mpr h)
    rw [ite_eq_right c1']
    exact ⟨false, a3, rfl, hS3, hg, by simp, by simp⟩

end L.Ind
