module

import ConAgua.Arena.RecLayout.RuleDec
import ConAgua.Arena.WhnfM2CRefine4
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.WhnfM2CRefine3
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.WhnfM2CRefine2
import ConAgua.Arena.WhnfM2CRefine4
import all ConAgua.Arena.WhnfM2C
import all ConAgua.Arena.WhnfIota
import ConAgua.Arena.EtaRescueRef
import ConAgua.Arena.RecLayout.CIDec

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


/-- The kind word of a decoded record says whether it is an inductive or a constructor. -/
theorem decCI_kind34' {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {ci : IConstantInfo} (h : decCI R q.toNat = some ci) :
    ((∃ cv caps, ci = .indInfo cv caps) ↔ rd q = 3) ∧
      ((∃ cv nP nF fam, ci = .ctorInfo cv nP nF fam) ↔ rd q = 4) := by
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

set_option maxRecDepth 8192 in
theorem ctorView_coreFn : "ctor_view" ∈ coreFns := List.elem_iff.mp (by decide)

set_option maxRecDepth 8192 in
theorem mtcr_coreFn : "major_to_ctor_rescue" ∈ coreFns := List.elem_iff.mp (by decide)

/-- **What `major_to_ctor`'s errors assume**: the rescue's (`M2CCtxE`) and the verdict closure
(the rescue is read through its call). -/
structure MtcG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  pirr : ProofIrrelWE p
  nv : closedNV p L.Checker.nvFns = true

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
    {fam : NIdx} (hcj : decCI (erecP m) cvjP.toNat = some (.ctorInfo cvj cnP cnF fam))
    (hci : decCI (erecP m) indP.toNat = some (.indInfo cvT caps))
    (hfe : ∃ c, fe.find? c = some (.indInfo cvT caps)) :
    RefE (M2CCtxE p N) (m2cArmsE p (N + 1) m mode vis d isK ro cvjP T indP major)
      (m2cArmsT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (isK != 0) rl
        cvj cnP (decI T) cvT caps (decE major)) a (GrowPost decH dn m vis fe M eb ResH) := by
  obtain ⟨hctorHW, hctor, -⟩ := decRule_rd (erRdOK m) hrl
  obtain ⟨-, hcvj, hnp, -⟩ := decCI_ctorInfo_rd (erRdOK m) hcj
  obtain ⟨-, -, -, hlp, -, -⟩ := decCV_rd_ci (erRdOK m) hcvj
  have hR : ∀ v y a', GrowPost decH dn m vis fe M eb ResH v y a' →
      GrowPost decH dn m vis fe M eb ResH ([v.1.headD 0], v.2) y a' :=
    GrowPost.of_tail (KeptAll.refl _ _) (StackKept.refl _).toGrew
  by_cases g : isK = 0
  · rw [m2cArmsE.arm2 _ _ _ _ _ _ _ _ _ _ _ _ g]
    have hK : (isK != 0) = false := by simp [g]
    cases N with
    | zero => rw [callW_zero, liftE_none, m2cArmsE.k_find_table.none]; exact RefE.of_cls0 (by simp)
    | succ N' =>
    unfold m2cArmsT
    simp only [hK, Bool.false_eq_true, ↓reduceIte]
    have hTw : T.toNat < 2 ^ 32 := hT
    refine RefE.onlySim (fun _ => m2cArmsE.k_find_table.none ..) (fun _ _ h =>
        triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
          (findTable_refines p hp.findTable (N' + 1) _ vis T hS.env hTw) h)
      fun r0 m0 ⟨t0, ht0, hm0, _, hft, hfs⟩ => ?_
    have hm0' : m0 = m := ht0.symm.trans hm0
    subst hm0'
    rw [m2cArmsE.k_find_table.arm1]
    refine RefE.bindLift (fun _ => m2cArmsE.k_eta_rescue_table.none ..) fun r1 m1 c1 => ?_
    obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m0, Locals.init []⟩)
      (ertW_spec p hp.etaRescueTable (N' + 1) ⟨m0, Locals.init []⟩ _ _ _ _) c1
    rw [hs1] at hW1
    obtain ⟨hm1, hrun1, hsome1⟩ := ert_ok hp.erSlEq' hp.pinat ⟨fun _ => hS.pins⟩ hctorHW hcj hci
      (fun h0 => by simp only at hfs; exact hfs h0) hW1
    clear hs1
    subst m1
    refine ⟨_, _, by rw [hctor, hft]; simp only; exact hrun1, ?_⟩
    by_cases g1 : r1.headD 0 ≠ 0
    · rw [m2cArmsE.k_eta_rescue_table.arm1 (hc1 := g1)]
      obtain ⟨tb, htb⟩ := hsome1 g1
      simp only [htb]
      exact RefE.tail_eq (m2cArmsE.k_m2c_k.none p) (fun v => m2cArmsE.k_m2c_k.arm1 p v.1 v.2)
        (fun h => h.mono (Nat.le_succ _)) rfl hR
        (m2cEta_ref p hp hc hE hpr hilp N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
          mode d T indP _ major hm4 hebm hT hmaj cvT caps tb m0 a M hS hci hfe htb)
    · have g1' : r1.headD 0 = 0 := by simpa using g1
      rw [m2cArmsE.k_eta_rescue_table.arm2 (hc1 := g1')]
      have hz : tblFound m0 (r1.headD 0) = none := by rw [tblFound, ite_eq_left g1']
      simp only [hz]
      exact RefE.tail_eq (m2cArmsE.k_m2c_k.none p) (fun v => m2cArmsE.k_m2c_k.arm1 p v.1 v.2)
        (fun h => h.mono (Nat.le_succ _)) (by rw [hctor, hlp, hnp]; rfl) hR
        (m2cAnd_ref p hp hc hpi hE hcc N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
          mode d T major _ _ _ hm4 hebm hT hmaj hctorHW m0 a M hS)
  · rw [m2cArmsE.arm1 _ _ _ _ _ _ _ _ _ _ _ _ g]
    have hK : (isK != 0) = true := by simpa using g
    cases N with
    | zero => rw [m2cKE.eq_1, m2cArmsE.k_m2c_k.none]; exact RefE.of_cls0 (by simp)
    | succ N' =>
    exact RefE.tail_eq (m2cArmsE.k_m2c_k.none p) (fun v => m2cArmsE.k_m2c_k.arm1 p v.1 v.2)
      (fun h => h.mono (Nat.le_succ _)) (by simp only [m2cArmsT, hK, ↓reduceIte, hctor, hlp, hnp, _root_.L.Ind.erRd_foldN]) hR
      (m2cK_ref p hp hc hpi hE N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
        mode d T major _ _ _ hm4 hebm hT hmaj hctorHW m a M hS)

/-- **`m2c_ctor` refines `m2cCtorT`, both outcomes** (the family the constructor record's word
`7`; the errors are `m2c_arms`'). -/
theorem m2cCtor_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d isK ro cvjP major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hmaj : HW major) (rl : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (hrl : decRule (erecP m) ro.toNat = some rl)
    {fam : NIdx} (hcj : decCI (erecP m) cvjP.toNat = some (.ctorInfo cvj cnP cnF fam)) :
    RefE (M2CCtxE p N) (m2cCtorE p (N + 1) m mode vis d isK ro cvjP major)
      (m2cCtorT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (isK != 0) rl cvj cnP
        fam (decE major)) a (GrowPost decH dn m vis fe M eb ResH) := by
  rw [m2cCtorE.arm1]
  have hk4 : erRd m cvjP = 4 := ((decCI_kind34' (erRdOK m) hcj).2.mp ⟨_, _, _, _, rfl⟩)
  obtain ⟨cv', he, hfw⟩ := (decCI_ctorR (erRdOK m) hcj).1 hk4
  simp only [IConstantInfo.ctorInfo.injEq] at he
  obtain ⟨-, -, -, rfl⟩ := he
  have hA0 : GrowPost decH dn m vis fe M eb ResH ([major], m) (decE major) a :=
    ⟨CoreAfter.toG ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, rfl, hmaj⟩
  simp only [L.Ind.erRd_foldN] at *
  refine RefE.onlySim (fun _ => m2cCtorE.k_env_find.none ..)
    (fun r4 m4 h => callW_envFindI p hp.toIotaProg' N m vis _ hS.env hfw r4 m4 h)
    fun r4 m4 ⟨hm4', hfind, hfound⟩ => ?_
  rw [hm4']
  by_cases g4 : r4.headD 0 = 0
  · rw [m2cCtorE.k_env_find.arm1 _ _ _ _ _ _ _ _ _ _ _ _ g4]
    have hn : fe.find? (decI (erRd m (cvjP + CI.ctorInduct))) = none := by
      rw [hfind]; simp only [envFound, g4, ↓reduceIte]
    exact RefE.ret (by simp only [m2cCtorT, hn]; rfl) hA0
  obtain ⟨ci, hciE⟩ := hfound g4
  have hfind' : fe.find? (decI (erRd m (cvjP + CI.ctorInduct))) = some ci := by
    rw [hfind]; simp only [envFound, g4, ↓reduceIte]; exact hciE
  obtain ⟨hind, -⟩ := decCI_kind34' (erRdOK m) hciE
  by_cases g5 : erRd m (r4.tail.headD 0) ≠ 3
  · rw [m2cCtorE.k_env_find.arm2 _ _ _ _ _ _ _ _ _ _ _ _ g4 g5]
    refine RefE.ret ?_ hA0
    simp only [m2cCtorT, hfind']
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
    (by simp only [m2cCtorT, hfind'])
    (GrowPost.of_tail (KeptAll.refl _ _) (StackKept.refl _).toGrew)
    (m2cArms_ref p hp hc hpi hE hcc hpr hilp N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
      mode d isK ro cvjP _ _ major hm4 hebm hfw hmaj rl cvj cnP cnF cvT caps m a M hS hrl hcj hciE
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
  have hA1 : GrowPost decH dn m vis fe M eb ResH ([major], m) (decE major) a :=
    ⟨CoreAfter.toG ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, rfl, hmaj⟩
  obtain ⟨hlen, hget⟩ := L.Arena.decRules_get hr
  by_cases g2 : rc ≠ 1
  · rw [m2cHeadE.arm1 (hc1 := g2) ..]
    refine RefE.ret ?_ hA1
    match rules, hlen with
    | [], _ => rfl
    | [_], hl => exact absurd (UInt64.toNat_inj.mp (by simpa using hl.symm)) g2
    | _ :: _ :: _, _ => rfl
  have g2' : rc = 1 := by simpa using g2
  rw [m2cHeadE.arm2 (hc1 := g2') ..]
  subst g2'
  obtain ⟨rl, rfl⟩ : ∃ rl, rules = [rl] := by
    match rules, hlen with
    | [x], _ => exact ⟨x, rfl⟩
  have hrl : decRule (erecP m) ro.toNat = some rl := by
    have := hget 0 (by decide); simpa using this
  obtain ⟨l0, hctor, -⟩ := decRule_rd (erRdOK m) hrl
  cases N with
  | zero =>
    rw [callW_zero, liftE_none, m2cHeadE.k_env_find.none]; exact RefE.of_cls0 (by simp)
  | succ N' =>
  refine RefE.onlySim (fun _ => m2cHeadE.k_env_find.none ..)
    (fun r2 m2 h => callW_envFindI p hp.toIotaProg' (N' + 1) m vis _ hS.env l0 r2 m2 h)
    fun r2 m2 ⟨hm2, hfind, hfound⟩ => ?_
  rw [hm2]
  have hstep : (m2cHeadT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id (F)) fe d.toNat
      (isK != 0) [rl] (decE major)) =
      (match fe.find? rl.ctor with
          | some (.ctorInfo cvj cnP _cnF T) =>
            m2cCtorT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (isK != 0) rl cvj
              cnP T (decE major)
          | _ => pure (decE major)) := rfl
  by_cases g3 : r2.headD 0 = 0
  · rw [m2cHeadE.k_env_find.arm1 (hc1 := g3) ..]
    have hn : fe.find? rl.ctor = none := by
      rw [hctor, hfind]; simp only [envFound, g3, ↓reduceIte]
    exact RefE.ret (by rw [hstep]; simp only [hn]; rfl) hA1
  obtain ⟨ci, hciE⟩ := hfound g3
  have hfind' : fe.find? rl.ctor = some ci := by
    rw [hctor, hfind]; simp only [envFound, g3, ↓reduceIte]; exact hciE
  obtain ⟨-, hctr⟩ := decCI_kind34' (erRdOK m) hciE
  by_cases g4 : erRd m (r2.tail.headD 0) ≠ 4
  · rw [m2cHeadE.k_env_find.arm2 (hc1 := g3) (hc2 := g4) ..]
    refine RefE.ret ?_ hA1
    rw [hstep]; simp only [hfind']
    cases ci with
    | ctorInfo cv nP nF fam => exact absurd (hctr.mp ⟨cv, nP, nF, fam, rfl⟩) g4
    | _ => rfl
  rw [m2cHeadE.k_env_find.arm3 (hc1 := g3) (hc2 := by simpa [erRd] using g4) ..]
  obtain ⟨cvj, cnP, cnF, fam, rfl⟩ := hctr.mpr (by simpa using g4)
  exact RefE.tail_eq (m2cHeadE.k_m2c_ctor.none p) (fun v => m2cHeadE.k_m2c_ctor.arm1 p v.1 v.2)
    (fun h => h.mono (Nat.le_succ _)) (by rw [hstep]; simp only [hfind'])
    (GrowPost.of_tail (KeptAll.refl _ _) (StackKept.refl _).toGrew)
    (m2cCtor_ref p hp hc hpi hE hcc hpr hilp N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
      mode d isK ro _ major hm4 hebm hmaj rl cvj cnP cnF m _ M hS hrl hciE)

/-- **`major_to_ctor_rescue` refines `majorToCtorRescue`, both outcomes** (the top put back):
`m2c_head`'s (`m2cHead_ref`). -/
theorem mtcr_ref (n F : Nat) (hk : KnotUpTo p n) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode d rec isK ro rc major : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hmaj : HW major) (rules : List IRecRule)
    (m : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m a vis fe M eb)
    (hr : decRules (erecP m) ro.toNat rc.toNat = some rules) :
    RefE (M2CCtxE p n) (mtcrE p (n + 1) m mode vis d rec isK ro rc major)
      (majorToCtorRescue (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec)
        (isK != 0) rules (decE major)) a (CorePost decH dn m vis fe M eb ResH) := by
  simp only [mtcrE]
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ N =>
  rw [majorToCtorRescue_eq]
  exact RefE.tail_eq (k := mtcrE.k_m2c_head p (rdW (m.arr64 CTL) 136)) (fun _ => rfl) (fun _ => rfl)
    (fun h => h.mono (Nat.le_succ _)) rfl
    (fun v y a' h => by
      obtain ⟨M', hS', hK', hg⟩ := h.after
      exact ⟨⟨M', hS'.frame_stk (MemFrame.setCtl _ _ _) (by simp) (by simp), hK',
        StackKept.restoreG' hg⟩, h.res, h.valid⟩)
    (m2cHead_ref p hp hc hpi hE hcc hpr hilp N F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
      mode d isK ro rc major hm4 hebm hmaj rules m a M hS hr)

/-- **`major_to_ctor` refines `majorToCtor`, both outcomes**: the view (`ctor_view`), else the
rescue's (`mtcr_ref`) and its view, the records read in the entry memory (the record pool is
kept: `ErecPKept`). -/
theorem mtc_ref (n F : Nat) (hk : KnotUpTo p n) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode d rec isK ro rc major : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hmaj : HW major) (rules : List IRecRule)
    (m : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m a vis fe M eb)
    (hr : decRules (erecP m) ro.toNat rc.toNat = some rules) :
    RefE (MtcG p n) (mtcE p (n + 1) m mode vis d rec isK ro rc major)
      (majorToCtor (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec) (isK != 0) rules
        (decE major)) a (CorePost (decMV m) dn m vis fe M eb (MVOk m)) := by
  simp only [mtcE]
  cases n with
  | zero => rw [callW_zero, liftE_none, mtcE.k_ctor_view.none]; exact RefE.of_cls0 (by simp)
  | succ N =>
  unfold majorToCtor
  refine RefE.bindLift (fun _ => rfl) fun r1 m1 c1 => ?_
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, hok1⟩ := CoreSpec.run
    (ctorView_refines p hp.toIotaProg' N ⟨m, Locals.init []⟩ a dn vis fe M eb major hS hmaj) c1
  have e1 : erecP m1 = erecP m := hE _ _ _ _ _ _ ctorView_coreFn c1
  refine ⟨_, _, hrun1, ?_⟩
  dsimp only [mtcE.k_ctor_view]
  by_cases g1 : r1.headD 0 ≠ 0
  · simp only [g1, ne_eq, not_false_eq_true, ↓reduceIte]
    obtain ⟨hlen, hq⟩ := hok1
    obtain ⟨cv, nP, nF, ind, hci⟩ := hq g1
    have hct : (decMV m r1).isCtor = true := by
      have : r1.headD 0 = 0 ↔ False := ⟨g1, False.elim⟩
      simp only [decMV, this, hci, ↓reduceIte]; rfl
    have h5 := list5_eta r1 hlen
    refine RefE.ret ?_ ⟨⟨M1, hS1, hK1, hSt1⟩, by rw [h5], by rw [h5]; exact ⟨hlen, hq⟩⟩
    simp only [hct, ↓reduceIte]; rfl
  have g1' : r1.headD 0 = 0 := by simpa using g1
  have hst : (decMV m r1).isCtor = false := by unfold decMV; dsimp only; rw [if_pos g1']; rfl
  simp only [g1, ↓reduceIte, hst, Bool.false_eq_true]
  have hr1 : decRules (erecP m1) ro.toNat rc.toNat = some rules := by rw [e1]; exact hr
  refine RefE.bindRun (s₀ := ⟨m1, Locals.init []⟩) (fun _ => rfl)
    (mtcrE_spec p hp.toM2CProg hp.majorToCtorRescue (N + 1) _ mode vis d rec isK ro rc major)
    (fun hG => hG.nv) (fun (hG : MtcG p (N + 1)) => (⟨hG.knot.mono (Nat.le_succ N), hG.pirr⟩ : M2CCtxE p N))
    (mtcr_ref p hp hc hpi hE hcc hpr hilp N F (hk.mono (Nat.le_succ N)) (by omega) (by omega) dn vis fe eb
      mode d rec isK ro rc major hm4 hebm hmaj rules m1 _ M1 hS1 hr1)
    fun r2 s2 y a2 c2 _ hrun2 hP2 => ?_
  obtain ⟨M2, hS2, hK2, hSt2⟩ := hP2.after
  have e2 : erecP s2.mem = erecP m1 := hE _ _ _ _ _ _ mtcr_coreFn (callW_of_callE c2)
  have hy : y = decE (r2.headD 0) := hP2.res
  have hw2 : HW (r2.headD 0) := hP2.valid
  subst hy
  dsimp only [mtcE.k_major_to_ctor_rescue]
  by_cases g2 : r2.headD 0 = major
  · have hb : (decE (r2.headD 0) == decE major) = true := by rw [g2]; exact beq_self_eq_true _
    simp only [g2, ↓reduceIte] at hb ⊢
    refine RefE.ret ?_ ⟨⟨M2, hS2, hK1.trans hK2, hSt1.trans hSt2⟩, by rw [decMV_stuck], ⟨rfl, fun h => absurd rfl h⟩⟩
    simp only [hb, ↓reduceIte]; rfl
  have hb : (decE (r2.headD 0) == decE major) = false := by
    rw [show (decE (r2.headD 0) == decE major) = (r2.headD 0 == major) from decI_beq _ _ hw2 hmaj]
    simpa using g2
  simp only [g2, ↓reduceIte, hb, Bool.false_eq_true]
  rw [← bind_pure (ctorView fe (decE (r2.headD 0)))]
  refine RefE.bindLift (fun _ => rfl) fun r3 m3 c3 => ?_
  obtain ⟨hrun3, ⟨M3, hS3, hK3, hSt3⟩, hok3⟩ := CoreSpec.run
    (ctorView_refines p hp.toIotaProg' N ⟨s2.mem, Locals.init []⟩ a2 dn vis fe M2 eb (r2.headD 0) hS2 hw2) c3
  have e3 : erecP m3 = erecP s2.mem := hE _ _ _ _ _ _ ctorView_coreFn c3
  refine ⟨_, _, hrun3, ?_⟩
  dsimp only [mtcE.k_ctor_view_2]
  have e31 : erecP s2.mem = erecP m := e2.trans e1
  have h5 := list5_eta r3 hok3.1
  refine RefE.ret rfl ⟨⟨M3, hS3, (hK1.trans hK2).trans hK3, (hSt1.trans hSt2).trans hSt3⟩, ?_, ?_⟩
  · rw [h5]; exact decMV_congr e31.symm r3 ▸ rfl
  · rw [h5]; exact MVOk_congr e31 hok3

/-- **`major_to_ctor` refines `majorToCtor`** (the callees' specs as hypotheses): `mtc_ref`'s ok
half. -/
theorem majorToCtor_refines' : MajorToCtorOK p :=
  fun n hk F hnF s₀ a₀ dn vis fe MM eb mode d rec isK ro rc major rules hn62 hS hm4 hebm hmaj hr =>
    RefE.coreSpec (mtcE_spec p hp.majorToCtor (n + 1) s₀ mode vis d rec isK ro rc major)
      (mtc_ref p hp hc hpi hE hcc hpr hilp n F hk hnF hn62 dn vis fe eb mode d rec isK ro rc major hm4 hebm hmaj
        rules s₀.mem a₀ MM hS hr)

end top

end L.Arena
