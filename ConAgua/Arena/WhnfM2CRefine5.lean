module

import ConAgua.Arena.WhnfM2CRefine4
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.WhnfM2CRefine3
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.WhnfM2CRefine2
import ConAgua.Arena.WhnfM2CRefine4
import ConAgua.Arena.DeclCanonEq
import all ConAgua.Arena.WhnfM2C
import all ConAgua.Arena.WhnfIota
import ConAgua.Arena.EtaRescueRef

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

set_option maxRecDepth 8192 in
theorem isCtorApp_coreFn : "is_ctor_app" ∈ coreFns := List.elem_iff.mp (by decide)

/-! ## Record words -/

/-- A rule record's `ctor` word. -/
theorem decRule_ctorRd {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {rl : IRecRule} (h : decRule R q.toNat = some rl) : rl.ctor = decI (rd q) ∧ HW (rd q) := by
  obtain ⟨w, hw, hl, e⟩ := hd?_some (L.Ind.decRule_ctor h)
  have e' : rd q = w := hR.rd _ _ hw
  exact ⟨by rw [e', e], by rw [e']; exact hl⟩

/-- A constructor record's level-parameter count, type and parameter count words. -/
theorem decCI_ctorWords {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {cv : IConstantVal} {nP nF : Nat} (h : decCI R q.toNat = some (.ctorInfo cv nP nF)) :
    cv.levelParams.length = (rd (q + 3)).toNat ∧ nP = (rd (q + 5)).toNat ∧
      cv.type = decI (rd (q + 4)) ∧ HW (rd (q + 4)) := by
  obtain ⟨-, hlen, hty, hty32⟩ := decCV_rd hR (L.Arena.decCI_ctor_cv h)
  refine ⟨hlen, ?_, hty, hty32⟩
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, -, h⟩ := h
  rcases k with _ | _ | _ | _ | _ | _ | k <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq, and_false, exists_false] at h
  obtain ⟨_, -, np, hnp, _, -, he⟩ := h
  simp only [IConstantInfo.ctorInfo.injEq] at he
  obtain ⟨-, rfl, -⟩ := he
  simp only [nat?, Option.map_eq_some_iff] at hnp
  obtain ⟨w, hw, rfl⟩ := hnp
  have e : rd (q + 5) = w := hR.offN (k := 5) (by simpa [Nat.add_assoc] using hw) (by decide)
  rw [e]

/-- The kind word of a decoded record says whether it is an inductive or a constructor. -/
theorem decCI_kind34' {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {ci : IConstantInfo} (h : decCI R q.toNat = some ci) :
    ((∃ cv caps, ci = .indInfo cv caps) ↔ rd q = 3) ∧
      ((∃ cv nP nF, ci = .ctorInfo cv nP nF) ↔ rd q = 4) := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  simp only [nat?, Option.map_eq_some_iff] at hk
  obtain ⟨w, ew, kw⟩ := hk
  have e : rd q = w := hR.rd _ _ ew
  rw [e]
  have e3 : w = 3 ↔ k = 3 :=
    ⟨fun e => by rw [← kw, e]; rfl, fun e => UInt64.toNat_inj.mp (by rw [kw, e]; rfl)⟩
  have e4 : w = 4 ↔ k = 4 :=
    ⟨fun e => by rw [← kw, e]; rfl, fun e => UInt64.toNat_inj.mp (by rw [kw, e]; rfl)⟩
  rw [e3, e4]
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  all_goals grind

section top
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hpi : ProofIrrelOKM p)
  (hE : ErecPKept p) (hcc : ProjCallees p) (hpr : PropReadProg p) (hilp : InstLPOK p)
include hp hc hpi hE hcc hpr hilp

/-- **`m2c_arms` refines `m2cArmsT`, both outcomes** (the errors are the arm's). -/
theorem m2cArms_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d isK ro cvjP T indP major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hT : HW T) (hmaj : HW major) (rl : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat)
    (cvT : IConstantVal) (caps : IIndCaps) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hrl : decRule (erecP m) ro.toNat = some rl)
    (hcj : decCI (erecP m) cvjP.toNat = some (.ctorInfo cvj cnP cnF))
    (hci : decCI (erecP m) indP.toNat = some (.indInfo cvT caps))
    (hfe : ∃ c, fe.find? c = some (.indInfo cvT caps)) :
    RefE (M2CCtxE p N) (m2cArmsE p (N + 1) m mode vis d isK ro cvjP T indP major)
      (m2cArmsT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (isK != 0) rl
        cvj cnP (decI T) cvT caps (decE major)) a (GrowPost decH dn m vis fe M eb ResH) := by
  sorry

/-- **`m2c_ctor` refines `m2cCtorT`, both outcomes** (the errors are `m2c_arms`'). -/
theorem m2cCtor_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d isK ro cvjP major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hmaj : HW major) (rl : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (hrl : decRule (erecP m) ro.toNat = some rl)
    (hcj : decCI (erecP m) cvjP.toNat = some (.ctorInfo cvj cnP cnF)) :
    RefE (M2CCtxE p N) (m2cCtorE p (N + 1) m mode vis d isK ro cvjP major)
      (m2cCtorT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (isK != 0) rl cvj cnP
        (decE major)) a (GrowPost decH dn m vis fe M eb ResH) := by
  rw [m2cCtorE.arm1]
  obtain ⟨-, -, hty, l4⟩ := decCI_ctorWords (erRdOK m) hcj
  have hA0 : GrowPost decH dn m vis fe M eb ResH ([major], m) (decE major) a :=
    ⟨CoreAfter.toG ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, rfl, hmaj⟩
  have hR := hS.arena.base
  refine RefE.onlySim (fun _ => m2cCtorE.k_pi_result.none ..) (fun _ _ h =>
      triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (piResult_refines' p hp.spine.pires N _ a hR _ l4) h)
    fun r1 m1 ⟨t1, ht1, hm1, _, hh1, hprR⟩ => ?_
  rw [m2cCtorE.k_pi_result.arm1]
  have hm1' : m1 = m := ht1.symm.trans hm1
  rw [hm1']
  have hpr' : (piResult coreWalkFuel cvj.type).run a = .ok (decE (r1.headD 0), a) := by
    rw [hty]; exact hprR
  refine RefE.onlySim (fun _ => m2cCtorE.k_get_app_fn.none ..) (fun _ _ h =>
      triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
        (getAppFn_refines' p hp.spine.fn N _ a hR (r1.headD 0) hh1) h)
    fun r2 m2 ⟨t2, ht2, hm2, _, hh2, hga⟩ => ?_
  have hm2' : m2 = m := ht2.symm.trans hm2
  rw [hm2']
  by_cases g2 : tagW (r2.headD 0) ≠ 3
  · rw [m2cCtorE.k_get_app_fn.arm1 _ _ _ _ _ _ _ _ _ _ _ g2]
    have ht : ((decE (r2.headD 0)).tag == ETag.const) = false := by
      rw [decE_const_tag _ hh2]; simpa using g2
    exact RefE.ret (by simp only [m2cCtorT, StateT.run_bind, hpr', except_ok_bind, hga, ht]; rfl) hA0
  have g2' : tagW (r2.headD 0) = 3 := by simpa using g2
  rw [m2cCtorE.k_get_app_fn.arm2 _ _ _ _ _ _ _ _ _ _ _ g2']
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
  obtain ⟨hvw, hn32, -⟩ := L.Ind.view_const_f m a hR (r2.headD 0) hh2 ⟨v1, UInt64.not_le.mp v2⟩ g2'
  have hn0 : tfld m CONST (tierW (r2.headD 0)) (idxW (r2.headD 0)) 0 = r3.headD 0 := by
    rw [hr3]; rfl
  rw [hn0] at hvw hn32
  refine RefE.onlySim (fun _ => m2cCtorE.k_env_find.none ..)
    (fun r4 m4 h => callW_envFindI p hp.toIotaProg' N m vis _ hS.env hn32 r4 m4 h)
    fun r4 m4 ⟨hm4', hfind, hfound⟩ => ?_
  rw [hm4']
  have hview := view_run _ _ _ hvw
  by_cases g4 : r4.headD 0 = 0
  · rw [m2cCtorE.k_env_find.arm1 _ _ _ _ _ _ _ _ _ _ _ _ g4]
    have hn : fe.find? (decI (r3.headD 0)) = none := by rw [hfind]; simp only [envFound, g4, ↓reduceIte]
    exact RefE.ret (by
      simp only [m2cCtorT, StateT.run_bind, hpr', except_ok_bind, hga, ht, ↓reduceIte, hview, hn]; rfl) hA0
  obtain ⟨ci, hciE⟩ := hfound g4
  have hfind' : fe.find? (decI (r3.headD 0)) = some ci := by
    rw [hfind]; simp only [envFound, g4, ↓reduceIte]; exact hciE
  obtain ⟨hind, -⟩ := decCI_kind34' (erRdOK m) hciE
  by_cases g5 : erRd m (r4.tail.headD 0) ≠ 3
  · rw [m2cCtorE.k_env_find.arm2 _ _ _ _ _ _ _ _ _ _ _ _ g4 g5]
    refine RefE.ret ?_ hA0
    simp only [m2cCtorT, StateT.run_bind, hpr', except_ok_bind, hga, ht, ↓reduceIte, hview, hfind']
    cases ci with
    | indInfo cv caps => exact absurd (hind.mp ⟨cv, caps, rfl⟩) g5
    | _ => rfl
  rw [m2cCtorE.k_env_find.arm3 _ _ _ _ _ _ _ _ _ _ _ _ g4 (by simpa [erRd] using g5)]
  obtain ⟨cvT, caps, rfl⟩ := hind.mpr (by simpa using g5)
  cases N with
  | zero => rw [m2cArmsE.eq_1, m2cCtorE.k_m2c_arms.none]; exact RefE.of_cls0 (by simp)
  | succ N' =>
  exact RefE.tail_eq (m2cCtorE.k_m2c_arms.none p) (fun v => m2cCtorE.k_m2c_arms.arm1 p v.1 v.2)
    (fun h => h.mono (Nat.le_succ _))
    (by simp only [m2cCtorT, StateT.run_bind, hpr', except_ok_bind, hga, ht, ↓reduceIte, hview, hfind'])
    (GrowPost.of_tail (KeptAll.refl _ _) (StackKept.refl _).toGrew)
    (m2cArms_ref p hp hc hpi hE hcc hpr hilp N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
      mode d isK ro cvjP _ _ major hm4 hebm hn32 hmaj rl cvj cnP cnF cvT caps m a M hS hrl hcj hciE
      ⟨_, hfind'⟩)

/-- **`m2c_head` refines `m2cHeadT`, both outcomes** (the errors are `m2c_ctor`'s). -/
theorem m2cHead_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d isK ro rc major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hmaj : HW major) (rules : List IRecRule) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hr : decRules (erecP m) ro.toNat rc.toNat = some rules) :
    RefE (M2CCtxE p N) (m2cHeadE p (N + 1) m mode vis d isK ro rc major)
      (m2cHeadT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (isK != 0) rules
        (decE major)) a (GrowPost decH dn m vis fe M eb ResH) := by
  rw [m2cHeadE.arm1]
  cases N with
  | zero => rw [callW_zero, liftE_none, m2cHeadE.k_is_ctor_app.none]; exact RefE.of_cls0 (by simp)
  | succ N' =>
  refine RefE.onlySim (fun _ => m2cHeadE.k_is_ctor_app.none ..) (fun _ _ h => h) fun r1 m1 c1 => ?_
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, -⟩ := CoreSpec.run
    (isCtorApp_refines p hp.toIotaProg' N' ⟨m, Locals.init []⟩ a dn vis fe M eb major hS hmaj) c1
  have e1 : erecP m1 = erecP m := hE _ _ _ _ _ _ isCtorApp_coreFn c1
  have hA1 : GrowPost decH dn m vis fe M eb ResH ([major], m1) (decE major)
      (AM.st (isCtorApp fe (decE major)) a) :=
    ⟨CoreAfter.toG ⟨M1, hS1, hK1, hSt1⟩, rfl, hmaj⟩
  by_cases g1 : r1.headD 0 ≠ 0
  · rw [m2cHeadE.k_is_ctor_app.arm1 _ _ _ _ _ _ _ _ _ _ _ g1]
    rw [L.Arena.decBool_true_of (by simpa using g1)] at hrun1
    exact RefE.ret (by simp only [m2cHeadT, StateT.run_bind, hrun1, except_ok_bind, ↓reduceIte]; rfl) hA1
  rw [L.Arena.decBool_false_of (by simpa using g1)] at hrun1
  have g1' : r1.headD 0 = 0 := by simpa using g1
  have hstep : (m2cHeadT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (isK != 0) rules
      (decE major)).run a = (match rules with
        | [rl] =>
          match fe.find? rl.ctor with
          | some (.ctorInfo cvj cnP _cnF) =>
            m2cCtorT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (isK != 0) rl cvj cnP
              (decE major)
          | _ => pure (decE major)
        | _ => pure (decE major)).run (AM.st (isCtorApp fe (decE major)) a) := by
    simp only [m2cHeadT, StateT.run_bind, hrun1, except_ok_bind, Bool.false_eq_true, ↓reduceIte]
    rfl
  obtain ⟨hlen, hget⟩ := L.Arena.decRules_getR _ _ _ hr
  by_cases g2 : rc ≠ 1
  · rw [m2cHeadE.k_is_ctor_app.arm2 _ _ _ _ _ _ _ _ _ _ _ g1' g2]
    refine RefE.ret ?_ hA1
    rw [hstep]
    match rules, hlen with
    | [], _ => rfl
    | [_], hl => exact absurd (UInt64.toNat_inj.mp (by simpa using hl.symm)) g2
    | _ :: _ :: _, _ => rfl
  have g2' : rc = 1 := by simpa using g2
  rw [m2cHeadE.k_is_ctor_app.arm3 _ _ _ _ _ _ _ _ _ _ _ g1' g2']
  subst g2'
  obtain ⟨rl, rfl⟩ : ∃ rl, rules = [rl] := by
    match rules, hlen with
    | [x], _ => exact ⟨x, rfl⟩
  have hrl : decRule (erecP m) ro.toNat = some rl := by
    have := hget 0 (by decide); simpa using this
  have hrl1 : decRule (erecP m1) ro.toNat = some rl := by rw [e1]; exact hrl
  obtain ⟨hctor, l0⟩ := decRule_ctorRd (erRdOK m1) hrl1
  refine RefE.onlySim (fun _ => m2cHeadE.k_env_find.none ..)
    (fun r2 m2 h => callW_envFindI p hp.toIotaProg' (N' + 1) m1 vis _ hS1.env l0 r2 m2 h)
    fun r2 m2 ⟨hm2, hfind, hfound⟩ => ?_
  rw [hm2]
  by_cases g3 : r2.headD 0 = 0
  · rw [m2cHeadE.k_env_find.arm1 _ _ _ _ _ _ _ _ _ _ g3]
    have hn : fe.find? rl.ctor = none := by
      rw [hctor, hfind]; simp only [envFound, g3, ↓reduceIte]
    exact RefE.ret (by rw [hstep]; simp only [hn]; rfl) hA1
  obtain ⟨ci, hciE⟩ := hfound g3
  have hfind' : fe.find? rl.ctor = some ci := by
    rw [hctor, hfind]; simp only [envFound, g3, ↓reduceIte]; exact hciE
  obtain ⟨-, hctr⟩ := decCI_kind34' (erRdOK m1) hciE
  by_cases g4 : erRd m1 (r2.tail.headD 0) ≠ 4
  · rw [m2cHeadE.k_env_find.arm2 _ _ _ _ _ _ _ _ _ _ g3 g4]
    refine RefE.ret ?_ hA1
    rw [hstep]; simp only [hfind']
    cases ci with
    | ctorInfo cv nP nF => exact absurd (hctr.mp ⟨cv, nP, nF, rfl⟩) g4
    | _ => rfl
  rw [m2cHeadE.k_env_find.arm3 _ _ _ _ _ _ _ _ _ _ g3 (by simpa [erRd] using g4)]
  obtain ⟨cvj, cnP, cnF, rfl⟩ := hctr.mpr (by simpa using g4)
  exact RefE.tail_eq (m2cHeadE.k_m2c_ctor.none p) (fun v => m2cHeadE.k_m2c_ctor.arm1 p v.1 v.2)
    (fun h => h.mono (Nat.le_succ _)) (by rw [hstep]; simp only [hfind'])
    (GrowPost.of_tail hK1 hSt1.toGrew)
    (m2cCtor_ref p hp hc hpi hE hcc hpr hilp N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
      mode d isK ro _ major hm4 hebm hmaj rl cvj cnP cnF m1 _ M1 hS1 hrl1 hciE)

/-- **`major_to_ctor` refines `majorToCtor`, both outcomes** (the top put back): `m2c_head`'s
(`m2cHead_ref`). -/
theorem mtc_ref (n F : Nat) (hk : KnotUpTo p n) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode d rec isK ro rc major : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hmaj : HW major) (rules : List IRecRule)
    (m : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m a vis fe M eb)
    (hr : decRules (erecP m) ro.toNat rc.toNat = some rules) :
    RefE (M2CCtxE p n) (mtcE p (n + 1) m mode vis d rec isK ro rc major)
      (majorToCtor (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec) (isK != 0) rules
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
    (m2cHead_ref p hp hc hpi hE hcc hpr hilp N F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
      mode d isK ro rc major hm4 hebm hmaj rules m a M hS hr)

/-- **`major_to_ctor` refines `majorToCtor`** (the callees' specs as hypotheses): `mtc_ref`'s ok
half. -/
theorem majorToCtor_refines' : MajorToCtorOK p :=
  fun n hk F hnF s₀ a₀ dn vis fe MM eb mode d rec isK ro rc major rules hn62 hS hm4 hebm hmaj hr =>
    RefE.coreSpec (mtcE_spec p hp.toM2CProg hp.majorToCtor (n + 1) s₀ mode vis d rec isK ro rc major)
      (mtc_ref p hp hc hpi hE hcc hpr hilp n F hk hnF hn62 dn vis fe eb mode d rec isK ro rc major hm4 hebm hmaj
        rules s₀.mem a₀ MM hS hr)

end top

end L.Arena
