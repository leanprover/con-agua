module

import ConAgua.Arena.WhnfM2CRefine3
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.WhnfIotaRefine3
import ConAgua.Arena.IndRecRead
import ConAgua.Arena.EtaRescueRef
import all ConAgua.Arena.WhnfM2C
public import ConAgua.Arena.WhnfM2CRefine2
import ConAgua.Arena.WhnfDeltaRefine

@[expose] public section

/-!
# `major_to_ctor`: refinements of the η arm (`m2c_eta`, `m2c_eta2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

section etaarm
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hE : ErecPKept p)
  (hcc : ProjCallees p) (hpr : PropReadProg p) (hilp : InstLPOK p)
include hp hc hcc hpr hilp

omit hcc in
/-- **`m2c_eta2` refines `m2cEta2T`, both outcomes** (the slice `(to, tn)` ends at the stack top;
the errors are `family_never_zero_at`'s). -/
theorem m2cEta2_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d T indP ec ef to tn ust major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hT : HW T) (hec : HW ec) (hus : HW ust) (hmaj : HW major) (cvT : IConstantVal)
    (caps : IIndCaps) (tbl : IProjTable) (targs : List EIdx) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hci : decCI (erecP m) indP.toNat = some (.indInfo cvT caps))
    (hfe : ∃ c, fe.find? c = some (.indInfo cvT caps)) (hecE : tbl.ctor = decI ec)
    (hef : tbl.numFields = ef.toNat) (hsp : SpineR m to tn targs.toArray) (htop : to + tn = spTop m)
    (hvus : ∃ x c, a.store.view x = some (.const c (decI ust))) :
    RefE (M2CCtxE p N) (m2cEta2E p (N + 1) m mode vis d T indP ec ef to tn ust major)
      (m2cEta2T (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decI T) cvT caps tbl targs
        (decI ust) (decE major)) a (GrowPost decH dn m vis fe M eb ResH) := by
  rw [m2cEta2E.arm1]
  cases N with
  | zero => rw [fanzaE.eq_1, m2cEta2E.k_family_never_zero_at.none]; exact RefE.of_cls0 (by simp)
  | succ N' =>
  unfold m2cEta2T
  -- `former_never_zero_at`
  have hks : ∃ ks, cvT.levelParams.mapM (denoteN a.store.ns) = some ks := by
    obtain ⟨c, hcf⟩ := hfe; exact hS.den.constLps c _ hcf
  have hlsd : ∃ ls, denoteLs a.store.lss (decI ust) = some ls := by
    obtain ⟨x, c, hx⟩ := hvus; exact hS.den.constLs x c _ hx
  have hf := fanza_ref p (hp.fnzaProg hpr hilp hc.inst1) N' F (hk.mono (Nat.le_succ _)) (by omega)
    (by omega) dn vis fe eb mode hm4 hebm m a M indP ust cvT caps hS hci hks hus hlsd
  refine RefE.bind_coreEG (w := id) (fun _ => m2cEta2E.k_family_never_zero_at.none ..)
    (fun (hG : M2CCtxE p (N' + 1)) => hG.knot.mono (Nat.le_succ _)) hf
    fun r4 m4 _ h4 M4 hS4 hSt4 => ?_
  have hrun4 := AM.run_of_ok _ _ h4.run
  have hA4 : GrowPost decH dn m4 vis fe M4 eb ResH (id ([major], m4)) (decE major)
      (AM.st (ConRon.Arena.familyNeverZeroAt (coreKnot (decMode mode) (decEager mode) fe id F) cvT caps (decI ust)) a) :=
    ⟨CoreAfter.toG ⟨M4, hS4, KeptAll.refl _ _, StackKept.refl _⟩, rfl, hmaj⟩
  by_cases g4 : r4.headD 0 = 0
  · rw [m2cEta2E.k_family_never_zero_at.arm1 _ _ _ _ _ _ _ _ _ _ _ _ g4]
    simp only [L.Arena.decBool_false_of g4, Bool.false_eq_true, ↓reduceIte]
    exact RefE.ret rfl hA4
  rw [m2cEta2E.k_family_never_zero_at.arm2 _ _ _ _ _ _ _ _ _ _ _ _ g4]
  simp only [L.Arena.decBool_true_of g4, ↓reduceIte]
  have hspn := hS.spn
  have hSt34 := hSt4
  have hsp4 : SpineR m4 to tn targs.toArray :=
    hsp.ofKept hSt34 (by
      have hb := hsp.bound
      rw [← htop, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
      exact Nat.le_refl _) hspn
  have htop4 : to + tn = spTop m4 := htop.trans hSt34.1.symm
  have hvus4 : ∃ x c, (AM.st (ConRon.Arena.familyNeverZeroAt (coreKnot (decMode mode) (decEager mode) fe id F) cvT caps
      (decI ust)) a).store.view x = some (.const c (decI ust)) := by
    obtain ⟨x, c, hx⟩ := hvus
    exact ⟨x, c, familyNeverZeroAt_fwd hrun4 x _ (.inr ⟨_, _, rfl⟩) hx⟩
  rw [hecE, hef]
  rcases c5 : callW p (N' + 1) "eta_fab_args" [T, to, tn, major, ef] m4 with _ | ⟨r5, m5⟩
  · rw [liftE_none, m2cEta2E.k_eta_fab_args.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, m2cEta2E.k_eta_fab_args.arm1]
  obtain ⟨t5, ht5, -, ok5, ⟨M5, hS5, hK5, hg5⟩, xs, res5, hsp5⟩ := triple_of_callW
    (s₀ := ⟨m4, Locals.init []⟩)
    (etaFabArgs_refines p hp.toIotaProg' (N' + 1) _ _ dn vis fe M4 eb T to tn major ef targs.toArray hS4 hT hmaj
      hsp4 htop4) c5
  rw [ht5] at hS5 hg5 hsp5
  have hrun5 := AM.run_of_ok _ _ ok5
  rw [res5] at hrun5
  rcases c6 : callW p (N' + 1) "intern_const" [ec, ust] m5 with _ | ⟨r6, m6⟩
  · rw [liftE_none, m2cEta2E.k_intern_const.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, m2cEta2E.k_intern_const.arm1]
  obtain ⟨ok6, hD6, res6, hfr6, hh6⟩ := callW_internConst' p hp.constFind' hp.constPush'
    hp.internConst' (N' + 1) m5 _ hS5.arena ec ust hec hus r6 m6 c6
  have hrun6 := AM.run_of_ok _ _ ok6
  rw [res6] at hrun6
  have hS6 := hS5.of_const hD6 (Keeps.run (L.Arena.keeps_cpl_internConst _ _) hrun6) hfr6 hrun6 (by
    obtain ⟨x, c, hx⟩ := hvus4
    exact hS5.den.constLs _ _ _ (etaFabArgsE_fwd hrun5 x _ (.inr ⟨_, _, rfl⟩) hx))
  have hsp6 := hsp5.of_spn (const_spn hfr6)
  rcases c7 : callW p (N' + 1) "mk_app_n" [r6.headD 0, r5.headD 0, r5.tail.headD 0] m6 with _ | ⟨r7, m7⟩
  · rw [liftE_none, m2cEta2E.k_mk_app_n.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, m2cEta2E.k_mk_app_n.arm1]
  obtain ⟨ok7, hD7, res7, hfr7, hh7⟩ := callW_mkAppN' p hp.spine (N' + 1) m6 _ hS6.arena
    (r6.headD 0) (r5.headD 0) (r5.tail.headD 0) _ hh6 hsp6 r7 m7 c7
  have hrun7 := AM.run_of_ok _ _ ok7
  rw [res7, show xs.toArray.toList = xs from rfl,
    show decE (r6.headD 0) = decI (r6.headD 0) from rfl] at hrun7
  have hS7 := hS6.of_app hD7 (Keeps.run (keeps_cpl_mkAppN' _ _) hrun7) hfr7
  rcases c8 : callW p (N' + 1) "fab_scope_ok" [d, r7.headD 0, major] m7 with _ | ⟨r8, m8⟩
  · rw [liftE_none, m2cEta2E.k_fab_scope_ok.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hrun8, ⟨M8, hS8, hK8, hSt8⟩, -⟩ := CoreSpec.run
    (fabScopeOk_refines' p hp.toIotaProg' hc (N' + 1) ⟨m7, Locals.init []⟩ _ dn vis fe M5 eb d (r7.headD 0)
      major hS7 hh7 hmaj) c8
  have hA8 : CoreAfterG dn m4 m8 _ vis fe M4 eb :=
    ⟨M8, hS8, hK5.trans hK8, hg5.trans ((L.Arena.StackKept.of_const_frame hfr6).trans
      ((StackKept.of_app_frame hfr7).trans hSt8)).toGrew⟩
  refine RefE.bind_right hrun5 (RefE.bind_right hrun6 (RefE.bind_right hrun7 (RefE.bind_right hrun8 ?_)))
  by_cases g8 : r8.headD 0 = 0
  · rw [m2cEta2E.k_fab_scope_ok.arm1 _ _ _ _ _ g8]
    simp only [L.Arena.decBool_false_of g8, Bool.false_eq_true, ↓reduceIte]
    exact RefE.ret rfl ⟨hA8, rfl, hmaj⟩
  · rw [m2cEta2E.k_fab_scope_ok.arm2 _ _ _ _ _ g8]
    simp only [L.Arena.decBool_true_of g8, ↓reduceIte]
    exact RefE.ret rfl ⟨hA8, rfl, hh7⟩

omit hcc in
include hE in
/-- **`m2c_eta` refines `m2cEtaT`, both outcomes** (`indP` the family's record; the errors are
`m2c_pre`'s and `m2c_eta2`'s). -/
theorem m2cEta_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d T indP tq major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hT : HW T) (hmaj : HW major) (cvT : IConstantVal) (caps : IIndCaps) (tbl : IProjTable)
    (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb)
    (hci : decCI (erecP m) indP.toNat = some (.indInfo cvT caps))
    (hfe : ∃ c, fe.find? c = some (.indInfo cvT caps)) (htbl : tblFound m tq = some tbl) :
    RefE (M2CCtxE p N) (m2cEtaE p (N + 1) m mode vis d T indP tq major)
      (m2cEtaT (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decI T) cvT caps tbl (decE major)) a
      (GrowPost decH dn m vis fe M eb ResH) := by
  rw [m2cEtaE.arm1]
  have hrec := decCI_indCaps (erRdOK m) hci
  have htw := tblFound_words htbl
  have hlps : cvT.levelParams.length = (erRd m (indP + 3)).toNat := hslice?_lenR hrec.lp
  cases N with
  | zero => rw [m2cPreE.eq_1, m2cEtaE.k_m2c_pre.none]; exact RefE.of_cls0 (by simp)
  | succ N' =>
  have hpre0 := m2cPre_ref p hp hE N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode
    d major hm4 hebm hmaj m a M hS
  rcases c1 : m2cPreE p (N' + 1) m mode vis d major with e1 | ⟨L, m1⟩
  · rw [m2cEtaE.k_m2c_pre.none]
    rw [c1] at hpre0
    unfold m2cEtaT
    exact fun hG => hpre0 (hG.mono (Nat.le_succ _)) _
  rw [c1] at hpre0
  obtain ⟨a1, hpre, ⟨M1, hS1, hK1, hSt1⟩, he1, hhw⟩ := hpre0
  by_cases g0 : L.headD 0 = 0
  · rw [m2cEtaE.k_m2c_pre.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ g0]
    exact RefE.ret (by unfold m2cEtaT; exact m2cPreT_none hpre g0 _)
      ⟨CoreAfter.toG ⟨M1, hS1, hK1, hSt1⟩, rfl, hmaj⟩
  rw [m2cEtaE.k_m2c_pre.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ g0]
  obtain ⟨htm, hT2, hus⟩ := hhw g0
  obtain ⟨l, hvls, hll, -⟩ := hpre.view g0
  obtain ⟨hh0, c0, hv0⟩ := hpre.cview g0
  have hpre' := m2cPreT_some hpre g0
  refine RefE.onlySim (fun _ => m2cEtaE.k_get_app_args.none ..) (fun _ _ h => h) fun r2' m2 c2 => ?_
  obtain ⟨t2, ht2, -, hfr2, hg2, htop2, htop2', xs, hargs, hsp2⟩ := triple_of_callW
    (s₀ := ⟨m1, Locals.init []⟩) (getAppArgs_refines p hp.spine (N' + 1) _ a1 hS1.arena.base _ htm hS1.spn) c2
  rw [ht2] at hfr2 hg2 hsp2 htop2'
  have hS2 := hS1.frame_stk hfr2 (by simp) (by simp)
  have he2 : erecP m2 = erecP m := (erecP_frame hfr2 (by simp [EREC, SPN]) (by simp [EREC, SPN, tier1])
    (by simp) (by simp)).trans he1
  have hlen : xs.length = (r2'.tail.headD 0).toNat := by simpa using hsp2.size
  have hstep : (m2cEtaT (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decI T) cvT caps tbl
      (decE major)).run a =
      (if (decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ xs.length = tbl.numParams ∧
          l.length = cvT.levelParams.length then
        m2cEta2T (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decI T) cvT caps tbl xs
          (decI (L.tail.tail.tail.headD 0)) (decE major)
      else pure (decE major)).run a1 := by
    unfold m2cEtaT; rw [hpre']
    simp only [StateT.run_bind, hvls, except_ok_bind, hargs]
  have hA2 : GrowPost decH dn m vis fe M eb ResH ([major], m2) (decE major) a1 :=
    ⟨⟨M1, hS2, hK1, hSt1.toGrew.trans hg2⟩, rfl, hmaj⟩
  have hmaj' : ∀ (hn : ¬ ((decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ xs.length = tbl.numParams ∧
      l.length = cvT.levelParams.length)),
      RefE (M2CCtxE p (N' + 1)) (.ok ([major], m2))
        (m2cEtaT (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decI T) cvT caps tbl (decE major)) a
        (GrowPost decH dn m vis fe M eb ResH) :=
    fun hn => RefE.ret (by rw [hstep, ite_eq_right hn]; rfl) hA2
  by_cases g2 : L.tail.tail.headD 0 ≠ T
  · rw [m2cEtaE.k_get_app_args.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g2]
    exact hmaj' (fun e => g2 ((decI_inj_iff hT2 hT).mp e.1))
  have g2' : L.tail.tail.headD 0 = T := by simpa using g2
  simp only [_root_.L.Ind.erRd_foldN]
  by_cases g3 : r2'.tail.headD 0 ≠ erRd m (tq + (ProjTbl.numParams - 1))
  · rw [m2cEtaE.k_get_app_args.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g2' g3]
    exact hmaj' (fun e => g3 (UInt64.toNat_inj.mp (by rw [← hlen, e.2.1, htw.2.1])))
  have g3' : r2'.tail.headD 0 = erRd m (tq + (ProjTbl.numParams - 1)) := by simpa using g3
  by_cases g4 : L.tail.tail.tail.tail.headD 0 ≠ erRd m (indP + 3)
  · rw [m2cEtaE.k_get_app_args.arm3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g2' g3' g4]
    exact hmaj' (fun e => g4 (UInt64.toNat_inj.mp (by rw [← hll, e.2.2, hlps])))
  have g4' : L.tail.tail.tail.tail.headD 0 = erRd m (indP + 3) := by simpa using g4
  rw [m2cEtaE.k_get_app_args.arm4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g2' g3' g4']
  have hcond : (decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ xs.length = tbl.numParams ∧
      l.length = cvT.levelParams.length :=
    ⟨by rw [g2'], by rw [hlen, g3', htw.2.1], by rw [hll, g4', hlps]⟩
  exact RefE.tail_eq (m2cEtaE.k_m2c_eta2.none p) (fun v => m2cEtaE.k_m2c_eta2.arm1 p v.1 v.2)
    (fun h => h.mono (Nat.le_succ _)) (by rw [hstep, ite_eq_left hcond])
    (GrowPost.of_tail hK1 (hSt1.toGrew.trans hg2))
    (m2cEta2_ref p hp hc hpr hilp N' F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
      mode d T indP _ _ _ _ _ major hm4 hebm hT htw.2.2.1 hus hmaj cvT caps tbl xs m2 a1 M1 hS2
      (by rw [he2]; exact hci) hfe htw.2.2.2.1 htw.2.2.2.2 hsp2 (by rw [htop2]; exact htop2'.symm) ⟨hh0, c0, hv0⟩)

end etaarm

end L.Arena
