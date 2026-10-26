import ConAgua.Arena.WhnfM2CRefine4

/-!
# `major_to_ctor`: the dispatch (`m2c_arms`), the family (`m2c_ctor`), the header (`m2c_head`)
and `major_to_ctor` itself
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Record words -/

/-- A rule record's `ctor`, `k` and `eta` words. -/
theorem decRule_words (a : Array Word) (q : Nat) (rl : IRecRule) (h : decRule a q = some rl) :
    (∃ w, a[q]? = some w ∧ w.toNat < 2 ^ 32 ∧ rl.ctor = decI w) ∧
    (∃ w, a[q + 9]? = some w ∧ rl.k = (w != 0)) ∧ ∃ w, a[q + 10]? = some w ∧ rl.eta = (w != 0) := by
  simp only [decRule, hd?, nat?, bool?, Option.bind_eq_bind] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨x, ⟨y, hy, rfl⟩, h⟩ := h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at h
    grind
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at h
    grind
  · simp at h

/-- A constructor record's kind, level-parameter count, type and parameter count words. -/
theorem decCI_ctor_words (b : Array Word) (dn : NIdx → Option ConLeche.Name) (q : Nat)
    (cv : IConstantVal) (nP nF : Nat) (h : decCI b dn q = some (.ctorInfo cv nP nF)) :
    (∃ w, b[q]? = some w ∧ w = 4) ∧ (∃ w, b[q + 3]? = some w ∧ cv.levelParams.length = w.toNat) ∧
    (∃ w, b[q + 4]? = some w ∧ w.toNat < 2 ^ 32 ∧ cv.type = decI w) ∧
    (∃ w, b[q + 5]? = some w ∧ nP = w.toNat) := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  match k, h with
  | 0, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 1, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 2, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 3, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 5, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 6, h => simp_all []
  | (_ + 7), h => simp_all
  | 4, h =>
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv', hcv, np', hnp, nf', -, h3⟩ := h
    simp only [IConstantInfo.ctorInfo.injEq] at h3
    obtain ⟨rfl, rfl, rfl⟩ := h3
    obtain ⟨w0, e0, k0⟩ := nat?_some hk
    obtain ⟨w5, e5, rfl⟩ := nat?_some hnp
    simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff] at hcv
    obtain ⟨nm, -, ls, hls, ty, hty, hc⟩ := hcv
    cases hc
    obtain ⟨o, c, -, hc3, hs⟩ := hlist?_slice hls
    obtain ⟨w4, e4, l4, rfl⟩ := hd?_eq hty
    refine ⟨⟨w0, e0, UInt64.toNat_inj.mp (by rw [k0]; rfl)⟩, ⟨c, by simpa [Nat.add_assoc] using hc3,
      hslice?_length hs⟩, ⟨w4, by simpa [Nat.add_assoc] using e4, l4, rfl⟩, ⟨w5, e5, rfl⟩⟩

/-- The kind word of a decoded record says whether it is an inductive or a constructor. -/
theorem decCI_kind34 (b : Array Word) (dn : NIdx → Option ConLeche.Name) (q : Nat)
    (ci : IConstantInfo) (h : decCI b dn q = some ci) :
    ∃ w, b[q]? = some w ∧ ((∃ cv caps, ci = .indInfo cv caps) ↔ w = 3) ∧
      ((∃ cv nP nF, ci = .ctorInfo cv nP nF) ↔ w = 4) := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  obtain ⟨w, ew, kw⟩ := nat?_some hk
  have e3 : w = 3 ↔ k = 3 :=
    ⟨fun e => by rw [← kw, e]; rfl, fun e => UInt64.toNat_inj.mp (by rw [kw, e]; rfl)⟩
  have e4 : w = 4 ↔ k = 4 :=
    ⟨fun e => by rw [← kw, e]; rfl, fun e => UInt64.toNat_inj.mp (by rw [kw, e]; rfl)⟩
  refine ⟨w, ew, ?_⟩
  rw [e3, e4]
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  all_goals grind

/-- A word at `q + k` of a record, as `rdW`. -/
theorem rdW_rec {b : Array Word} {q : Word} {k : Nat} {w : Word} (hb : b[q.toNat + k]? = some w)
    (hk : k < 2 ^ 32) (hsz : b.size < 2 ^ 63) : rdW b (q + k.toUInt64) = w :=
  rdW_off' hb (by simp; omega) hsz

section top
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hpi : ProofIrrelOKM p)
  (hE : ErecKeptKnot p) (hcc : ProjCallees p)
include hp hc hpi hE hcc

/-- **`m2c_arms` refines `m2cArmsT`.** -/
theorem m2cArms_ok (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ro cvjP T indP major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hT : HW T) (hmaj : HW major) (rl : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat)
    (cvT : IConstantVal) (caps : IIndCaps) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hrl : decRule (m.arr64 EREC) ro.toNat = some rl)
    (hcj : decCI (m.arr64 EREC) dn cvjP.toNat = some (.ctorInfo cvj cnP cnF))
    (hci : decCI (m.arr64 EREC) dn indP.toNat = some (.indInfo cvT caps))
    (hfe : ∃ c, fe.find? c = some (.indInfo cvT caps)) (r : List Word) (m' : Mem)
    (h : callW p (N + 1) "m2c_arms" [mode, vis, d, ro, cvjP, T, indP, major] m = some (r, m')) :
    GrowRef (m2cArmsT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rl cvj cnP (decI T)
      cvT caps (decE major)) a decH dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (m2cArms_spec p hp.arms N _ mode vis d ro cvjP T indP major) h
  dsimp only at hW
  rw [hs'] at hW
  simp only [m2cArmsW] at hW
  have hsz := hS.erec
  obtain ⟨⟨w0, e0, l0, hctor⟩, ⟨w9, e9, hkk⟩, ⟨w10, e10, heta⟩⟩ := decRule_words _ _ _ hrl
  obtain ⟨-, ⟨w3, e3, hlp⟩, -, ⟨w5, e5, hnp⟩⟩ := decCI_ctor_words _ dn _ cvj cnP cnF hcj
  have r0 : rdW (m.arr64 EREC) ro = w0 := by simp only [rdW, e0]; rfl
  have r9 : rdW (m.arr64 EREC) (ro + 9) = w9 := rdW_rec (k := 9) e9 (by decide) (by omega)
  have r10 : rdW (m.arr64 EREC) (ro + 10) = w10 := rdW_rec (k := 10) e10 (by decide) (by omega)
  have r3 : rdW (m.arr64 EREC) (cvjP + 3) = w3 := rdW_rec (k := 3) e3 (by decide) (by omega)
  have r5 : rdW (m.arr64 EREC) (cvjP + 5) = w5 := rdW_rec (k := 5) e5 (by decide) (by omega)
  rw [r0, r9, r10, r3, r5] at hW
  cases N with
  | zero => simp [callW_zero] at hW
  | succ N' =>
  by_cases g9 : w9 ≠ 0
  · rw [ite_eq_left g9] at hW
    rcases c1 : callW p (N' + 1) "m2c_k" [mode, vis, d, T, major, w0, w3, w5] m with _ | ⟨r1, m1⟩ <;>
      simp only [c1, reduceCtorEq] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    have hK := m2cK_ok p hp hc hpi hE N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
      mode d T major w0 w3 w5 hm4 hebm hT hmaj l0 m a M hS r1 m1 c1
    have hk' : rl.k = true := by rw [hkk]; simpa using g9
    have : m2cArmsT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rl cvj cnP (decI T)
        cvT caps (decE major) = m2cKT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
          (decI w0) w3.toNat w5.toNat (decI T) (decE major) := by
      simp only [m2cArmsT, hk', ↓reduceIte, hctor, hlp, hnp]
    obtain ⟨ok1, hA1, res1, hr1⟩ := hK
    rw [this]
    exact ⟨ok1, hA1, by rw [res1]; unfold decH; rw [hr], by unfold ResH at hr1 ⊢; rw [← hr]; exact hr1⟩
  rw [ite_eq_right g9] at hW
  have hk' : rl.k = false := by rw [hkk]; simpa using g9
  by_cases g10 : w10 ≠ 0
  · rw [ite_eq_left g10] at hW
    rcases c1 : callW p (N' + 1) "m2c_eta" [mode, vis, d, T, indP, major] m with _ | ⟨r1, m1⟩ <;>
      simp only [c1, reduceCtorEq] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    obtain ⟨ok1, hA1, res1, hr1⟩ := m2cEta_ok p hp hc hE hcc N' F (hk.mono (Nat.le_succ _)) (by omega)
      (by omega) dn vis fe eb mode d T indP major hm4 hebm hT hmaj cvT caps m a M hS hci hfe r1 m1 c1
    have he' : rl.eta = true := by rw [heta]; simpa using g10
    have : m2cArmsT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rl cvj cnP (decI T)
        cvT caps (decE major) = m2cEtaT (coreKnot (decMode mode) fe id F) fe d.toNat (decI T) cvT caps
          (decE major) := by
      simp only [m2cArmsT, hk', he', Bool.false_eq_true, ↓reduceIte]
    rw [this]
    exact ⟨ok1, hA1, by rw [res1]; unfold decH; rw [hr], by unfold ResH at hr1 ⊢; rw [← hr]; exact hr1⟩
  rw [ite_eq_right g10] at hW
  have he' : rl.eta = false := by rw [heta]; simpa using g10
  rcases c1 : callW p (N' + 1) "m2c_and" [mode, vis, d, T, major, w0, w3, w5] m with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨hr, rfl⟩ := ret_eq hW
  obtain ⟨ok1, hA1, res1, hr1⟩ := m2cAnd_ok p hp hc hpi hE hcc N' F (hk.mono (Nat.le_succ _)) (by omega)
    (by omega) dn vis fe eb mode d T major w0 w3 w5 hm4 hebm hT hmaj l0 m a M hS r1 m1 c1
  have : m2cArmsT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rl cvj cnP (decI T)
      cvT caps (decE major) = m2cAndT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
        (decI w0) w3.toNat w5.toNat (decI T) (decE major) := by
    simp only [m2cArmsT, hk', he', Bool.false_eq_true, ↓reduceIte, hctor, hlp, hnp]
  rw [this]
  exact ⟨ok1, hA1, by rw [res1]; unfold decH; rw [hr], by unfold ResH at hr1 ⊢; rw [← hr]; exact hr1⟩

/-- **`m2c_ctor` refines `m2cCtorT`.** -/
theorem m2cCtor_ok (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ro cvjP major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hmaj : HW major) (rl : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (hrl : decRule (m.arr64 EREC) ro.toNat = some rl)
    (hcj : decCI (m.arr64 EREC) dn cvjP.toNat = some (.ctorInfo cvj cnP cnF)) (r : List Word)
    (m' : Mem)
    (h : callW p (N + 1) "m2c_ctor" [mode, vis, d, ro, cvjP, major] m = some (r, m')) :
    GrowRef (m2cCtorT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rl cvj cnP
      (decE major)) a decH dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (m2cCtor_spec p hp.ctor N _ mode vis d ro cvjP major) h
  dsimp only at hW
  rw [hs'] at hW
  simp only [m2cCtorW] at hW
  have hsz := hS.erec
  obtain ⟨-, -, ⟨w4, e4, l4, hty⟩, -⟩ := decCI_ctor_words _ dn _ cvj cnP cnF hcj
  have r4 : rdW (m.arr64 EREC) (cvjP + 4) = w4 := rdW_rec (k := 4) e4 (by decide) (by omega)
  rw [r4] at hW
  have hA0 : CoreAfterG dn m m a vis fe M eb :=
    CoreAfter.toG ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩
  have hR := hS.arena.1
  rcases c1 : callW p N "pi_result" [w4] m with _ | ⟨r1, m1⟩ <;> simp only [c1, reduceCtorEq] at hW
  obtain ⟨t1, ht1, hm1, -, hh1, hpr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (piResult_refines' p hp.spine.pires N _ a hR w4 l4) c1
  have hm1' : m1 = m := ht1.symm.trans hm1
  rw [hm1'] at hW
  have hpr' : (piResult coreWalkFuel cvj.type).run a = .ok (decE (r1.headD 0), a) := by
    rw [hty]; exact hpr
  rcases c2 : callW p N "get_app_fn" [r1.headD 0] m with _ | ⟨r2, m2⟩ <;>
    simp only [c2, reduceCtorEq] at hW
  obtain ⟨t2, ht2, hm2, -, hh2, hga⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (getAppFn_refines' p hp.spine.fn N _ a hR (r1.headD 0) hh1) c2
  have hm2' : m2 = m := ht2.symm.trans hm2
  rw [hm2'] at hW
  by_cases g2 : r2.headD 0 >>> 28 ≠ 3
  · rw [ite_eq_left g2] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA0 (decH_of _ _ hr) (resH_of_m2c _ _ hr hmaj)
    have ht : ((decE (r2.headD 0)).tag == ETag.const) = false := by
      rw [decE_const_tag _ hh2]; simpa using g2
    simp only [m2cCtorT, StateT.run_bind, hpr', except_ok_bind, hga, ht]; rfl
  rw [ite_eq_right g2] at hW
  have g2' : r2.headD 0 >>> 28 = 3 := by simpa using g2
  have ht : ((decE (r2.headD 0)).tag == ETag.const) = true := by
    rw [decE_const_tag _ hh2]; simpa using g2'
  rcases c3 : callW p N "m2c_const_view" [r2.headD 0] m with _ | ⟨r3, m3⟩ <;>
    simp only [c3, reduceCtorEq] at hW
  obtain ⟨t3, ht3, -, hm3, hcv⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (m2cConstView_spec p hp.constView N _ (r2.headD 0)) c3
  have hm3' : m3 = m := ht3.symm.trans hm3
  rw [hm3'] at hW
  simp only [cvwW] at hcv
  obtain ⟨v1, hcv⟩ := of_ite_none hcv
  obtain ⟨v2, hcv⟩ := of_ite_none hcv
  have hr3 := (Option.some.inj hcv).symm
  obtain ⟨hvw, hn32, -⟩ := view_const_f m a hR (r2.headD 0) hh2 ⟨v1, UInt64.not_le.mp v2⟩ g2'
  have hn0 : tfld m CONST (tierW (r2.headD 0)) (idxW (r2.headD 0)) 0 = r3.headD 0 := by
    rw [hr3]; rfl
  rw [hn0] at hvw hn32
  rcases c4 : callW p N "env_find" [r3.headD 0, vis] m with _ | ⟨r4, m4⟩ <;>
    simp only [c4, reduceCtorEq] at hW
  obtain ⟨hm4', hfind, hfound⟩ := callW_envFindI p hp.toIotaProg' N m vis _ hS.env hn32 r4 m4 c4
  rw [hm4'] at hW
  have hview := view_run _ _ _ hvw
  by_cases g4 : r4.headD 0 = 0
  · rw [ite_eq_left g4] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA0 (decH_of _ _ hr) (resH_of_m2c _ _ hr hmaj)
    have hn : fe.find? (decI (r3.headD 0)) = none := by rw [hfind]; simp only [decFound, g4, ↓reduceIte]
    simp only [m2cCtorT, StateT.run_bind, hpr', except_ok_bind, hga, ht, ↓reduceIte, hview, hn]; rfl
  rw [ite_eq_right g4] at hW
  obtain ⟨ci, hci⟩ := hfound g4
  have hciE := (erecP_ext m).decCI hci
  have hfind' : fe.find? (decI (r3.headD 0)) = some ci := by
    rw [hfind]; simp only [decFound, g4, ↓reduceIte]; exact hci
  obtain ⟨wk, ewk, hind, -⟩ := decCI_kind34 _ dn _ ci hciE
  have rk : rdW (m.arr64 EREC) (r4.tail.headD 0) = wk := by simp only [rdW, ewk]; rfl
  rw [rk] at hW
  by_cases g5 : wk ≠ 3
  · rw [ite_eq_left g5] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA0 (decH_of _ _ hr) (resH_of_m2c _ _ hr hmaj)
    simp only [m2cCtorT, StateT.run_bind, hpr', except_ok_bind, hga, ht, ↓reduceIte, hview, hfind']
    cases ci with
    | indInfo cv caps => exact absurd (hind.mp ⟨cv, caps, rfl⟩) g5
    | _ => rfl
  rw [ite_eq_right g5] at hW
  obtain ⟨cvT, caps, rfl⟩ := hind.mpr (by simpa using g5)
  rcases c5 : callW p N "m2c_arms" [mode, vis, d, ro, cvjP, r3.headD 0, r4.tail.headD 0, major] m with _ | ⟨r5, m5⟩ <;>
    simp only [c5, reduceCtorEq] at hW
  obtain ⟨hr, rfl⟩ := ret_eq hW
  cases N with
  | zero => rw [callW_zero] at c5; cases c5
  | succ N' =>
  obtain ⟨ok5, hA5, res5, hr5⟩ := m2cArms_ok p hp hc hpi hE hcc N' F (hk.mono (Nat.le_succ _)) (by omega)
    (by omega) dn vis fe eb mode d ro cvjP _ _ major hm4 hebm hn32 hmaj rl cvj cnP cnF cvT caps m a M
    hS hrl hcj hciE ⟨_, hfind'⟩ r5 m5 c5
  have hrun5 := AM.run_of_ok _ _ ok5
  rw [res5] at hrun5
  refine GrowRef.of_run (v := decH r5) ?_ hA5 (by unfold decH; rw [hr])
    (by unfold ResH at hr5 ⊢; rw [← hr]; exact hr5)
  simp only [m2cCtorT, StateT.run_bind, hpr', except_ok_bind, hga, ht, ↓reduceIte, hview, hfind']
  exact hrun5

/-- **`m2c_head` refines `m2cHeadT`.** -/
theorem m2cHead_ok (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ro rc major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hmaj : HW major) (rules : List IRecRule) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hr : decRules (m.arr64 EREC) ro.toNat rc.toNat = some rules)
    (r : List Word) (m' : Mem)
    (h : callW p (N + 1) "m2c_head" [mode, vis, d, ro, rc, major] m = some (r, m')) :
    GrowRef (m2cHeadT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rules
      (decE major)) a decH dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (m2cHead_spec p hp.head N _ mode vis d ro rc major) h
  dsimp only at hW
  rw [hs'] at hW
  simp only [m2cHeadW] at hW
  cases N with
  | zero => simp [callW_zero] at hW
  | succ N' =>
  rcases c1 : callW p (N' + 1) "is_ctor_app" [vis, major] m with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, -⟩ := CoreSpec.run
    (isCtorApp_refines p hp.toIotaProg' N' ⟨m, Locals.init []⟩ a dn vis fe M eb major hS hmaj) c1
  have e1 : m1.arr64 EREC = m.arr64 EREC := hE _ _ _ _ _ _ (by simp) c1
  have hA1 : CoreAfterG dn m m1 (AM.st (isCtorApp fe (decE major)) a) vis fe M eb :=
    CoreAfter.toG ⟨M1, hS1, hK1, hSt1⟩
  by_cases g1 : r1.headD 0 ≠ 0
  · rw [ite_eq_left g1] at hW
    obtain ⟨hr', rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA1 (decH_of _ _ hr') (resH_of_m2c _ _ hr' hmaj)
    rw [decBool_t_m2c (by simpa using g1)] at hrun1
    simp only [m2cHeadT, StateT.run_bind, hrun1, except_ok_bind, ↓reduceIte]; rfl
  rw [ite_eq_right g1] at hW
  rw [decBool_f_m2c (by simpa using g1)] at hrun1
  have hstep : (m2cHeadT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rules
      (decE major)).run a = (match rules with
        | [rl] =>
          match fe.find? rl.ctor with
          | some (.ctorInfo cvj cnP _cnF) =>
            m2cCtorT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rl cvj cnP
              (decE major)
          | _ => pure (decE major)
        | _ => pure (decE major)).run (AM.st (isCtorApp fe (decE major)) a) := by
    simp only [m2cHeadT, StateT.run_bind, hrun1, except_ok_bind, Bool.false_eq_true, ↓reduceIte]
    rfl
  obtain ⟨hlen, hget⟩ := decRules_get _ _ _ _ hr
  by_cases g2 : rc ≠ 1
  · rw [ite_eq_left g2] at hW
    obtain ⟨hr', rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA1 (decH_of _ _ hr') (resH_of_m2c _ _ hr' hmaj)
    rw [hstep]
    match rules, hlen with
    | [], _ => rfl
    | [_], hl => exact absurd (UInt64.toNat_inj.mp (by simpa using hl.symm)) g2
    | _ :: _ :: _, _ => rfl
  rw [ite_eq_right g2] at hW
  have g2' : rc = 1 := by simpa using g2
  subst g2'
  obtain ⟨rl, rfl⟩ : ∃ rl, rules = [rl] := by
    match rules, hlen with
    | [x], _ => exact ⟨x, rfl⟩
  have hrl : decRule (m.arr64 EREC) ro.toNat = some rl := by
    have := hget 0 (by decide); simpa using this
  obtain ⟨⟨w0, e0, l0, hctor⟩, -, -⟩ := decRule_words _ _ _ hrl
  have r0 : rdW (m1.arr64 EREC) ro = w0 := by rw [e1]; simp only [rdW, e0]; rfl
  rw [r0] at hW
  rcases c2 : callW p (N' + 1) "env_find" [w0, vis] m1 with _ | ⟨r2, m2⟩ <;>
    simp only [c2, reduceCtorEq] at hW
  obtain ⟨hm2, hfind, hfound⟩ := callW_envFindI p hp.toIotaProg' (N' + 1) m1 vis _ hS1.env l0 r2 m2 c2
  rw [hm2] at hW
  by_cases g3 : r2.headD 0 = 0
  · rw [ite_eq_left g3] at hW
    obtain ⟨hr', rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA1 (decH_of _ _ hr') (resH_of_m2c _ _ hr' hmaj)
    have hn : fe.find? rl.ctor = none := by
      rw [hctor, hfind]; simp only [decFound, g3, ↓reduceIte]
    rw [hstep]; simp only [hn]; rfl
  rw [ite_eq_right g3] at hW
  obtain ⟨ci, hci⟩ := hfound g3
  have hciE := (erecP_ext m1).decCI hci
  have hfind' : fe.find? rl.ctor = some ci := by
    rw [hctor, hfind]; simp only [decFound, g3, ↓reduceIte]; exact hci
  obtain ⟨wk, ewk, -, hctr⟩ := decCI_kind34 _ dn _ ci hciE
  have rk : rdW (m1.arr64 EREC) (r2.tail.headD 0) = wk := by simp only [rdW, ewk]; rfl
  rw [rk] at hW
  by_cases g4 : wk ≠ 4
  · rw [ite_eq_left g4] at hW
    obtain ⟨hr', rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA1 (decH_of _ _ hr') (resH_of_m2c _ _ hr' hmaj)
    rw [hstep]; simp only [hfind']
    cases ci with
    | ctorInfo cv nP nF => exact absurd (hctr.mp ⟨cv, nP, nF, rfl⟩) g4
    | _ => rfl
  rw [ite_eq_right g4] at hW
  obtain ⟨cvj, cnP, cnF, rfl⟩ := hctr.mpr (by simpa using g4)
  rcases c3 : callW p (N' + 1) "m2c_ctor" [mode, vis, d, ro, r2.tail.headD 0, major] m1 with _ | ⟨r3, m3⟩ <;>
    simp only [c3, reduceCtorEq] at hW
  obtain ⟨hr', rfl⟩ := ret_eq hW
  obtain ⟨ok3, hA3, res3, hr3⟩ := m2cCtor_ok p hp hc hpi hE hcc N' F (hk.mono (Nat.le_succ _)) (by omega)
    (by omega) dn vis fe eb mode d ro _ major hm4 hebm hmaj rl cvj cnP cnF m1 _ M1 hS1
    (by rw [e1]; exact hrl) hciE r3 m3 c3
  have hrun3 := AM.run_of_ok _ _ ok3
  rw [res3] at hrun3
  refine GrowRef.of_run (v := decH r3) ?_ (CoreAfterG.compK hK1 hSt1.toGrew hA3)
    (by unfold decH; rw [hr']) (by unfold ResH at hr3 ⊢; rw [← hr']; exact hr3)
  rw [hstep]; simp only [hfind']; exact hrun3

/-- **`major_to_ctor` refines `majorToCtor`** (the callees' specs as hypotheses). -/
theorem majorToCtor_refines' : MajorToCtorOK p := by
  intro n hk F hnF s₀ a₀ dn vis fe MM eb mode d rec ro rc major rules hn62 hS hm4 hebm hmaj hr
  refine triple_post (majorToCtor_spec p hp.majorToCtor n s₀ mode vis d rec ro rc major) fun r s'
    ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  simp only [mtcW] at hW
  cases n with
  | zero => rw [callW_zero] at hW; cases hW
  | succ N =>
  rcases c1 : callW p (N + 1) "m2c_head" [mode, vis, d, ro, rc, major] s₀.mem with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨ok1, ⟨M1, hS1, hK1, hg1⟩, res1, hr1⟩ := m2cHead_ok p hp hc hpi hE hcc N F
    (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode d ro rc major hm4 hebm hmaj rules
    s₀.mem a₀ MM hS hr r1 m1 c1
  by_cases h136 : 136 < (m1.arr64 CTL).size
  · rw [ite_eq_left h136] at hW
    obtain ⟨hr0, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [majorToCtor_eq]
    refine ⟨ok1, ⟨M1, ?_, hK1, ?_⟩, ?_, ?_⟩
    · rw [← hm]; exact hS1.frame_stk (MemFrame.setCtl m1 136 _) (by simp) (by simp)
    · rw [← hm]; exact StackKept.restoreG hg1 h136
    · rw [res1]; unfold decH; rw [hr0]
    · unfold ResH at hr1 ⊢; rw [← hr0]; exact hr1
  · rw [ite_eq_right h136] at hW; cases hW

end top

end L.Arena
