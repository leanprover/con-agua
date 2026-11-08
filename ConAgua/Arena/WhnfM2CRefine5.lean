module

import ConAgua.Arena.WhnfM2CRefine4
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.WhnfIotaRefine6
import ConAgua.Arena.WhnfM2CRefine3
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.WhnfM2CRefine2

@[expose] public section

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
    (cv : IConstantVal) (nP nF : Nat) (h : decCI b q = some (.ctorInfo cv nP nF)) :
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
    (ci : IConstantInfo) (h : decCI b q = some ci) :
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

/-- **`m2c_arms` refines `m2cArmsT`, both outcomes** (the errors are the arm's). -/
theorem m2cArms_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ro cvjP T indP major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hT : HW T) (hmaj : HW major) (rl : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat)
    (cvT : IConstantVal) (caps : IIndCaps) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hrl : decRule (erecP m) ro.toNat = some rl)
    (hcj : decCI (erecP m) dn cvjP.toNat = some (.ctorInfo cvj cnP cnF))
    (hci : decCI (erecP m) dn indP.toNat = some (.indInfo cvT caps))
    (hfe : ∃ c, fe.find? c = some (.indInfo cvT caps)) :
    RefE (M2CCtxE p N) (m2cArmsE p (N + 1) m mode vis d ro cvjP T indP major)
      (m2cArmsT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat rl cvj cnP (decI T)
        cvT caps (decE major)) a (GrowPost decH dn m vis fe M eb ResH) := by
  rw [m2cArmsE.eq_2]
  have hsz := hS.erec
  obtain ⟨⟨w0, e0, l0, hctor⟩, ⟨w9, e9, hkk⟩, ⟨w10, e10, heta⟩⟩ := decRule_words _ _ _ hrl
  obtain ⟨-, ⟨w3, e3, hlp⟩, -, ⟨w5, e5, hnp⟩⟩ := decCI_ctor_words _ dn _ cvj cnP cnF hcj
  have r0 : rdW (m.arr64 EREC) ro = w0 := by simp only [rdW, e0]; rfl
  have r9 : rdW (m.arr64 EREC) (ro + 9) = w9 := rdW_rec (k := 9) e9 (by decide) (by omega)
  have r10 : rdW (m.arr64 EREC) (ro + 10) = w10 := rdW_rec (k := 10) e10 (by decide) (by omega)
  have r3 : rdW (m.arr64 EREC) (cvjP + 3) = w3 := rdW_rec (k := 3) e3 (by decide) (by omega)
  have r5 : rdW (m.arr64 EREC) (cvjP + 5) = w5 := rdW_rec (k := 5) e5 (by decide) (by omega)
  rw [r0, r9, r10, r3, r5]
  have hR : ∀ v y a', GrowPost decH dn m vis fe M eb ResH v y a' →
      GrowPost decH dn m vis fe M eb ResH ([v.1.headD 0], v.2) y a' :=
    GrowPost.of_tail (KeptAll.refl _ _) (StackKept.refl _).toGrew
  cases N with
  | zero =>
    simp only [m2cKE.eq_1, m2cEtaE.eq_1, m2cAndE.eq_1, m2cArmsE.k_m2c_k.none, ite_self]
    exact RefE.of_cls0 (by simp)
  | succ N' =>
  by_cases g9 : w9 ≠ 0
  · rw [ite_eq_left g9]
    have hk' : rl.k = true := by rw [hkk]; simpa using g9
    exact RefE.tail_eq (m2cArmsE.k_m2c_k.none p) (fun v => m2cArmsE.k_m2c_k.arm1 p v.1 v.2)
      (fun h => h.mono (Nat.le_succ _)) (by simp only [m2cArmsT, hk', ↓reduceIte, hctor, hlp, hnp]) hR
      (m2cK_ref p hp hc hpi hE N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
        mode d T major w0 w3 w5 hm4 hebm hT hmaj l0 m a M hS)
  rw [ite_eq_right g9]
  have hk' : rl.k = false := by rw [hkk]; simpa using g9
  by_cases g10 : w10 ≠ 0
  · rw [ite_eq_left g10]
    have he' : rl.eta = true := by rw [heta]; simpa using g10
    exact RefE.tail_eq (m2cArmsE.k_m2c_k.none p) (fun v => m2cArmsE.k_m2c_k.arm1 p v.1 v.2)
      (fun h => h.mono (Nat.le_succ _)) (by simp only [m2cArmsT, hk', he', Bool.false_eq_true, ↓reduceIte])
      hR (m2cEta_ref p hp hc hE hcc N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
        mode d T indP major hm4 hebm hT hmaj cvT caps m a M hS hci hfe)
  rw [ite_eq_right g10]
  have he' : rl.eta = false := by rw [heta]; simpa using g10
  exact RefE.tail_eq (m2cArmsE.k_m2c_k.none p) (fun v => m2cArmsE.k_m2c_k.arm1 p v.1 v.2)
    (fun h => h.mono (Nat.le_succ _))
    (by simp only [m2cArmsT, hk', he', Bool.false_eq_true, ↓reduceIte, hctor, hlp, hnp]) hR
    (m2cAnd_ref p hp hc hpi hE hcc N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
      mode d T major w0 w3 w5 hm4 hebm hT hmaj l0 m a M hS)

/-- **`m2c_ctor` refines `m2cCtorT`, both outcomes** (the errors are `m2c_arms`'). -/
theorem m2cCtor_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ro cvjP major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hmaj : HW major) (rl : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (hrl : decRule (erecP m) ro.toNat = some rl)
    (hcj : decCI (erecP m) dn cvjP.toNat = some (.ctorInfo cvj cnP cnF)) :
    RefE (M2CCtxE p N) (m2cCtorE p (N + 1) m mode vis d ro cvjP major)
      (m2cCtorT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat rl cvj cnP
        (decE major)) a (GrowPost decH dn m vis fe M eb ResH) := by
  rw [m2cCtorE.arm1]
  have hsz := hS.erec
  obtain ⟨-, -, ⟨w4, e4, l4, hty⟩, -⟩ := decCI_ctor_words _ dn _ cvj cnP cnF hcj
  have r4 : rdW (m.arr64 EREC) (cvjP + 4) = w4 := rdW_rec (k := 4) e4 (by decide) (by omega)
  rw [r4]
  have hA0 : GrowPost decH dn m vis fe M eb ResH ([major], m) (decE major) a :=
    ⟨CoreAfter.toG ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, rfl, hmaj⟩
  have hR := hS.arena.base
  refine RefE.onlySim (fun _ => m2cCtorE.k_pi_result.none ..) (fun _ _ h =>
      triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (piResult_refines' p hp.spine.pires N _ a hR w4 l4) h)
    fun r1 m1 ⟨t1, ht1, hm1, _, hh1, hpr⟩ => ?_
  rw [m2cCtorE.k_pi_result.arm1]
  have hm1' : m1 = m := ht1.symm.trans hm1
  rw [hm1']
  have hpr' : (piResult coreWalkFuel cvj.type).run a = .ok (decE (r1.headD 0), a) := by
    rw [hty]; exact hpr
  refine RefE.onlySim (fun _ => m2cCtorE.k_get_app_fn.none ..) (fun _ _ h =>
      triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
        (getAppFn_refines' p hp.spine.fn N _ a hR (r1.headD 0) hh1) h)
    fun r2 m2 ⟨t2, ht2, hm2, _, hh2, hga⟩ => ?_
  have hm2' : m2 = m := ht2.symm.trans hm2
  rw [hm2']
  by_cases g2 : tagW (r2.headD 0) ≠ 3
  · rw [m2cCtorE.k_get_app_fn.arm1 _ _ _ _ _ _ _ _ _ _ g2]
    have ht : ((decE (r2.headD 0)).tag == ETag.const) = false := by
      rw [decE_const_tag _ hh2]; simpa using g2
    exact RefE.ret (by simp only [m2cCtorT, StateT.run_bind, hpr', except_ok_bind, hga, ht]; rfl) hA0
  have g2' : tagW (r2.headD 0) = 3 := by simpa using g2
  rw [m2cCtorE.k_get_app_fn.arm2 _ _ _ _ _ _ _ _ _ _ g2']
  have ht : ((decE (r2.headD 0)).tag == ETag.const) = true := by
    rw [decE_const_tag _ hh2]; simpa using g2'
  refine RefE.onlySim (fun _ => m2cCtorE.k_m2c_const_view.none ..) (fun _ _ h =>
      triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (m2cConstView_spec p hp.constView N _ (r2.headD 0)) h)
    fun r3 m3 ⟨t3, ht3, _, hm3, hcv⟩ => ?_
  rw [m2cCtorE.k_m2c_const_view.arm1]
  have hm3' : m3 = m := ht3.symm.trans hm3
  rw [hm3']
  simp only [cvwW] at hcv
  obtain ⟨v1, hcv⟩ := of_ite_none hcv
  obtain ⟨v2, hcv⟩ := of_ite_none hcv
  have hr3 := (Option.some.inj hcv).symm
  obtain ⟨hvw, hn32, -⟩ := view_const_f m a hR (r2.headD 0) hh2 ⟨v1, UInt64.not_le.mp v2⟩ g2'
  have hn0 : tfld m CONST (tierW (r2.headD 0)) (idxW (r2.headD 0)) 0 = r3.headD 0 := by
    rw [hr3]; rfl
  rw [hn0] at hvw hn32
  refine RefE.onlySim (fun _ => m2cCtorE.k_env_find.none ..)
    (fun r4 m4 h => callW_envFindI p hp.toIotaProg' N m vis _ hS.env hn32 r4 m4 h)
    fun r4 m4 ⟨hm4', hfind, hfound⟩ => ?_
  rw [hm4']
  have hview := view_run _ _ _ hvw
  by_cases g4 : r4.headD 0 = 0
  · rw [m2cCtorE.k_env_find.arm1 _ _ _ _ _ _ _ _ _ _ _ g4]
    have hn : fe.find? (decI (r3.headD 0)) = none := by rw [hfind]; simp only [decFound, g4, ↓reduceIte]
    exact RefE.ret (by
      simp only [m2cCtorT, StateT.run_bind, hpr', except_ok_bind, hga, ht, ↓reduceIte, hview, hn]; rfl) hA0
  obtain ⟨ci, hci⟩ := hfound g4
  have hciE := (erecP_ext m).decCI hci
  have hfind' : fe.find? (decI (r3.headD 0)) = some ci := by
    rw [hfind]; simp only [decFound, g4, ↓reduceIte]; exact hci
  obtain ⟨wk, ewk, hind, -⟩ := decCI_kind34 _ dn _ ci hciE
  have rk : rdW (m.arr64 EREC) (r4.tail.headD 0) = wk := by simp only [rdW, ewk]; rfl
  by_cases g5 : wk ≠ 3
  · rw [m2cCtorE.k_env_find.arm2 _ _ _ _ _ _ _ _ _ _ _ g4 (by rw [rk]; exact g5)]
    refine RefE.ret ?_ hA0
    simp only [m2cCtorT, StateT.run_bind, hpr', except_ok_bind, hga, ht, ↓reduceIte, hview, hfind']
    cases ci with
    | indInfo cv caps => exact absurd (hind.mp ⟨cv, caps, rfl⟩) g5
    | _ => rfl
  rw [m2cCtorE.k_env_find.arm3 _ _ _ _ _ _ _ _ _ _ _ g4 (by rw [rk]; simpa using g5)]
  obtain ⟨cvT, caps, rfl⟩ := hind.mpr (by simpa using g5)
  cases N with
  | zero => rw [m2cArmsE.eq_1, m2cCtorE.k_m2c_arms.none]; exact RefE.of_cls0 (by simp)
  | succ N' =>
  exact RefE.tail_eq (m2cCtorE.k_m2c_arms.none p) (fun v => m2cCtorE.k_m2c_arms.arm1 p v.1 v.2)
    (fun h => h.mono (Nat.le_succ _))
    (by simp only [m2cCtorT, StateT.run_bind, hpr', except_ok_bind, hga, ht, ↓reduceIte, hview, hfind'])
    (GrowPost.of_tail (KeptAll.refl _ _) (StackKept.refl _).toGrew)
    (m2cArms_ref p hp hc hpi hE hcc N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
      mode d ro cvjP _ _ major hm4 hebm hn32 hmaj rl cvj cnP cnF cvT caps m a M hS hrl hcj hciE
      ⟨_, hfind'⟩)

/-- **`m2c_head` refines `m2cHeadT`, both outcomes** (the errors are `m2c_ctor`'s). -/
theorem m2cHead_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ro rc major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hmaj : HW major) (rules : List IRecRule) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hr : decRules (erecP m) ro.toNat rc.toNat = some rules) :
    RefE (M2CCtxE p N) (m2cHeadE p (N + 1) m mode vis d ro rc major)
      (m2cHeadT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat rules
        (decE major)) a (GrowPost decH dn m vis fe M eb ResH) := by
  rw [m2cHeadE.arm1]
  cases N with
  | zero => rw [callW_zero, liftE_none, m2cHeadE.k_is_ctor_app.none]; exact RefE.of_cls0 (by simp)
  | succ N' =>
  refine RefE.onlySim (fun _ => m2cHeadE.k_is_ctor_app.none ..) (fun _ _ h => h) fun r1 m1 c1 => ?_
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, -⟩ := CoreSpec.run
    (isCtorApp_refines p hp.toIotaProg' N' ⟨m, Locals.init []⟩ a dn vis fe M eb major hS hmaj) c1
  have e1 : m1.arr64 EREC = m.arr64 EREC := hE _ _ _ _ _ _ (by simp) c1
  have hA1 : GrowPost decH dn m vis fe M eb ResH ([major], m1) (decE major)
      (AM.st (isCtorApp fe (decE major)) a) :=
    ⟨CoreAfter.toG ⟨M1, hS1, hK1, hSt1⟩, rfl, hmaj⟩
  by_cases g1 : r1.headD 0 ≠ 0
  · rw [m2cHeadE.k_is_ctor_app.arm1 _ _ _ _ _ _ _ _ _ _ g1]
    rw [decBool_t_m2c (by simpa using g1)] at hrun1
    exact RefE.ret (by simp only [m2cHeadT, StateT.run_bind, hrun1, except_ok_bind, ↓reduceIte]; rfl) hA1
  rw [decBool_f_m2c (by simpa using g1)] at hrun1
  have g1' : r1.headD 0 = 0 := by simpa using g1
  have hstep : (m2cHeadT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat rules
      (decE major)).run a = (match rules with
        | [rl] =>
          match fe.find? rl.ctor with
          | some (.ctorInfo cvj cnP _cnF) =>
            m2cCtorT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat rl cvj cnP
              (decE major)
          | _ => pure (decE major)
        | _ => pure (decE major)).run (AM.st (isCtorApp fe (decE major)) a) := by
    simp only [m2cHeadT, StateT.run_bind, hrun1, except_ok_bind, Bool.false_eq_true, ↓reduceIte]
    rfl
  obtain ⟨hlen, hget⟩ := decRules_get _ _ _ _ hr
  by_cases g2 : rc ≠ 1
  · rw [m2cHeadE.k_is_ctor_app.arm2 _ _ _ _ _ _ _ _ _ _ g1' g2]
    refine RefE.ret ?_ hA1
    rw [hstep]
    match rules, hlen with
    | [], _ => rfl
    | [_], hl => exact absurd (UInt64.toNat_inj.mp (by simpa using hl.symm)) g2
    | _ :: _ :: _, _ => rfl
  have g2' : rc = 1 := by simpa using g2
  rw [m2cHeadE.k_is_ctor_app.arm3 _ _ _ _ _ _ _ _ _ _ g1' g2']
  subst g2'
  obtain ⟨rl, rfl⟩ : ∃ rl, rules = [rl] := by
    match rules, hlen with
    | [x], _ => exact ⟨x, rfl⟩
  have hrl : decRule (erecP m) ro.toNat = some rl := by
    have := hget 0 (by decide); simpa using this
  obtain ⟨⟨w0, e0, l0, hctor⟩, -, -⟩ := decRule_words _ _ _ hrl
  have r0 : rdW (m1.arr64 EREC) ro = w0 := by rw [e1]; simp only [rdW, e0]; rfl
  rw [r0]
  refine RefE.onlySim (fun _ => m2cHeadE.k_env_find.none ..)
    (fun r2 m2 h => callW_envFindI p hp.toIotaProg' (N' + 1) m1 vis _ hS1.env l0 r2 m2 h)
    fun r2 m2 ⟨hm2, hfind, hfound⟩ => ?_
  rw [hm2]
  by_cases g3 : r2.headD 0 = 0
  · rw [m2cHeadE.k_env_find.arm1 _ _ _ _ _ _ _ _ _ g3]
    have hn : fe.find? rl.ctor = none := by
      rw [hctor, hfind]; simp only [decFound, g3, ↓reduceIte]
    exact RefE.ret (by rw [hstep]; simp only [hn]; rfl) hA1
  obtain ⟨ci, hci⟩ := hfound g3
  have hciE := (erecP_ext m1).decCI hci
  have hfind' : fe.find? rl.ctor = some ci := by
    rw [hctor, hfind]; simp only [decFound, g3, ↓reduceIte]; exact hci
  obtain ⟨wk, ewk, -, hctr⟩ := decCI_kind34 _ dn _ ci hciE
  have rk : rdW (m1.arr64 EREC) (r2.tail.headD 0) = wk := by simp only [rdW, ewk]; rfl
  by_cases g4 : wk ≠ 4
  · rw [m2cHeadE.k_env_find.arm2 _ _ _ _ _ _ _ _ _ g3 (by rw [rk]; exact g4)]
    refine RefE.ret ?_ hA1
    rw [hstep]; simp only [hfind']
    cases ci with
    | ctorInfo cv nP nF => exact absurd (hctr.mp ⟨cv, nP, nF, rfl⟩) g4
    | _ => rfl
  rw [m2cHeadE.k_env_find.arm3 _ _ _ _ _ _ _ _ _ g3 (by rw [rk]; simpa using g4)]
  obtain ⟨cvj, cnP, cnF, rfl⟩ := hctr.mpr (by simpa using g4)
  exact RefE.tail_eq (m2cHeadE.k_m2c_ctor.none p) (fun v => m2cHeadE.k_m2c_ctor.arm1 p v.1 v.2)
    (fun h => h.mono (Nat.le_succ _)) (by rw [hstep]; simp only [hfind'])
    (GrowPost.of_tail hK1 hSt1.toGrew)
    (m2cCtor_ref p hp hc hpi hE hcc N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
      mode d ro _ major hm4 hebm hmaj rl cvj cnP cnF m1 _ M1 hS1 (by rw [e1]; exact hrl) hciE)

/-- **`major_to_ctor` refines `majorToCtor`, both outcomes** (the top put back): `m2c_head`'s
(`m2cHead_ref`). -/
theorem mtc_ref (n F : Nat) (hk : KnotUpTo p n) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode d rec ro rc major : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hmaj : HW major) (rules : List IRecRule)
    (m : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m a vis fe M eb)
    (hr : decRules (erecP m) ro.toNat rc.toNat = some rules) :
    RefE (M2CCtxE p n) (mtcE p (n + 1) m mode vis d rec ro rc major)
      (majorToCtor (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec) rules
        (decE major)) a (CorePost decH dn m vis fe M eb ResH) := by
  simp only [mtcE]
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ N =>
  rw [majorToCtor_eq]
  exact RefE.tail_eq (k := mtcE.k_m2c_head p (rdW (m.arr64 CTL) 136)) (fun _ => rfl) (fun _ => rfl)
    (fun h => h.mono (Nat.le_succ _)) rfl
    (fun v y a' h => by
      obtain ⟨M', hS', hK', hg⟩ := h.after
      exact ⟨⟨M', hS'.frame_stk (MemFrame.setCtl _ _ _) (by simp) (by simp), hK',
        StackKept.restoreG' hg⟩, h.res, h.valid⟩)
    (m2cHead_ref p hp hc hpi hE hcc N F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
      mode d ro rc major hm4 hebm hmaj rules m a M hS hr)

/-- **`major_to_ctor` refines `majorToCtor`** (the callees' specs as hypotheses): `mtc_ref`'s ok
half. -/
theorem majorToCtor_refines' : MajorToCtorOK p :=
  fun n hk F hnF s₀ a₀ dn vis fe MM eb mode d rec ro rc major rules hn62 hS hm4 hebm hmaj hr =>
    RefE.coreSpec (mtcE_spec p hp.toM2CProg hp.majorToCtor (n + 1) s₀ mode vis d rec ro rc major)
      (mtc_ref p hp hc hpi hE hcc n F hk hnF hn62 dn vis fe eb mode d rec ro rc major hm4 hebm hmaj
        rules s₀.mem a₀ MM hS hr)

end top

end L.Arena
