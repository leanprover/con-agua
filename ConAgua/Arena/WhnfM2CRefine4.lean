import ConAgua.Arena.WhnfM2CRefine3

/-!
# `major_to_ctor`: refinements of the η arm (`m2c_eta`, `m2c_eta2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- The η words of an inductive's record: `etaCtor` at `q + 6`, `etaParams` at `q + 7`,
`etaFields` at `q + 8`. -/
theorem decCI_ind_eta (b : Array Word) (dn : NIdx → Option ConLeche.Name) (q : Nat)
    (cv : IConstantVal) (caps : IIndCaps) (h : decCI b dn q = some (.indInfo cv caps)) :
    ∃ w6 w7 w8 : Word, b[q+6]? = some w6 ∧ w6.toNat < 2 ^ 32 ∧ caps.etaCtor = decI w6 ∧
      b[q+7]? = some w7 ∧ caps.etaParams = w7.toNat ∧ b[q+8]? = some w8 ∧
      caps.etaFields = w8.toNat := by
  have hk := L.Ind.decCI_indInfo_kind h
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk', h⟩ := h
  have hk3 : k = 3 := Option.some.inj (hk'.symm.trans hk)
  subst hk3
  simp only [Option.bind_eq_some_iff, Option.some.injEq, IConstantInfo.indInfo.injEq] at h
  obtain ⟨cv', hcv, caps', hcaps, hc1, hc2⟩ := h
  subst hc1; subst hc2
  simp only [decCaps, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hcaps
  obtain ⟨a0, -, a1, h1, a2, h2, a3, h3, a4, -, a5, -, a6, -, a7, -, a8, -, a9, -, a10, -, hfin⟩ :=
    hcaps
  obtain ⟨w6, e6, l6, rfl⟩ := hd?_eq h1
  obtain ⟨w7, e7, rfl⟩ := nat?_some h2
  obtain ⟨w8, e8, rfl⟩ := nat?_some h3
  have hc := (Option.some.inj hfin).symm
  subst hc
  exact ⟨w6, w7, w8, by simpa [Nat.add_assoc] using e6, l6, rfl, by simpa [Nat.add_assoc] using e7,
    rfl, by simpa [Nat.add_assoc] using e8, rfl⟩

section etaarm
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hE : ErecKeptKnot p)
  (hcc : ProjCallees p)
include hp hc hcc

/-- **`m2c_eta2` refines `m2cEta2T`** (the slice `(to, tn)` ends at the stack top). -/
theorem m2cEta2_ok (N : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb d T ec ef to tn ust major : Word) (hT : HW T) (hec : HW ec) (hus : HW ust)
    (hmaj : HW major) (targs : List EIdx) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hsp : SpineR m to tn targs.toArray) (htop : to + tn = spTop m)
    (r : List Word) (m' : Mem) (hvus : ∃ x c, a.store.view x = some (.const c (decI ust)))
    (h : callW p (N + 1) "m2c_eta2" [vis, d, T, ec, ef, to, tn, ust, major] m = some (r, m')) :
    GrowRef (m2cEta2T fe d.toNat (decI T) (decI ec) ef.toNat targs (decI ust) (decE major)) a decH
      dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (m2cEta2_spec p hp.eta2 N _ vis d T ec ef to tn ust major) h
  dsimp only at hW
  rw [hs'] at hW
  simp only [m2cEta2W] at hW
  rcases c1 : callW p N "reserved_contains_w" [T] m with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨hm1, l, hl, hcT, -⟩ := callW_reservedContains p hp.reservedContains N m a hS.pins T hT r1 m1 c1
  subst m1
  have hA0 : CoreAfterG dn m m a vis fe M eb :=
    CoreAfter.toG ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩
  by_cases g1 : r1.headD 0 ≠ 0
  · rw [if_pos g1] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA0 (decH_of _ _ hr) (resH_of_m2c _ _ hr hmaj)
    have hn : ¬ (l.contains (decI T) = false ∧ l.contains (decI ec) = false) := fun e => by
      have e1 := e.1; rw [hcT] at e1; exact g1 (by simpa using e1)
    simp only [m2cEta2T, StateT.run_bind, hl, except_ok_bind]
    rw [if_neg hn]; rfl
  rw [if_neg g1] at hW
  rcases c2 : callW p N "reserved_contains_w" [ec] m with _ | ⟨r2, m2⟩ <;>
    simp only [c2, reduceCtorEq] at hW
  obtain ⟨hm2, l', hl', hcE, -⟩ :=
    callW_reservedContains p hp.reservedContains N m a hS.pins ec hec r2 m2 c2
  subst m2
  have hll : l' = l := by
    have := hl'.symm.trans hl
    simp only [Except.ok.injEq, Prod.mk.injEq] at this
    exact this.1
  subst hll
  by_cases g2 : r2.headD 0 ≠ 0
  · rw [if_pos g2] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA0 (decH_of _ _ hr) (resH_of_m2c _ _ hr hmaj)
    have hn : ¬ (l'.contains (decI T) = false ∧ l'.contains (decI ec) = false) := fun e => by
      have e2 := e.2; rw [hcE] at e2; exact g2 (by simpa using e2)
    simp only [m2cEta2T, StateT.run_bind, hl, except_ok_bind]
    rw [if_neg hn]; rfl
  rw [if_neg g2] at hW
  have hres : l'.contains (decI T) = false ∧ l'.contains (decI ec) = false := by
    have g1' : r1.headD 0 = 0 := Classical.not_not.mp g1
    have g2' : r2.headD 0 = 0 := Classical.not_not.mp g2
    exact ⟨by rw [hcT, g1']; rfl, by rw [hcE, g2']; rfl⟩
  rcases c3 : callW p N "tower_slots_all" [vis, T, ef] m with _ | ⟨r3, m3⟩ <;>
    simp only [c3, reduceCtorEq] at hW
  obtain ⟨hrun3, ⟨M3, hS3, hK3, hSt3⟩, -⟩ := CoreSpec.run
    (towerSlotsAll_refines' p hp.toIotaProg' hcc.findProj hcc.projFound N ⟨m, Locals.init []⟩ a dn vis fe M eb T ef hS hT) c3
  by_cases g3 : r3.headD 0 = 0
  · rw [if_pos g3] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ (CoreAfter.toG ⟨M3, hS3, hK3, hSt3⟩) (decH_of _ _ hr)
      (resH_of_m2c _ _ hr hmaj)
    rw [decBool_f_m2c g3] at hrun3
    simp only [m2cEta2T, StateT.run_bind, hl, except_ok_bind]
    rw [if_pos hres]
    simp only [StateT.run_bind, hrun3, except_ok_bind, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [if_neg g3] at hW
  rw [decBool_t_m2c g3] at hrun3
  have hspn := hS.spn
  have hsp3 : SpineR m3 to tn targs.toArray :=
    hsp.ofKept hSt3 (by
      have hb := hsp.bound
      rw [← htop, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
      exact Nat.le_refl _) hspn
  rcases c4 : callW p N "eta_fab_args" [T, to, tn, major, ef] m3 with _ | ⟨r4, m4⟩ <;>
    simp only [c4, reduceCtorEq] at hW
  obtain ⟨t4, ht4, -, ok4, ⟨M4, hS4, hK4, hg4⟩, xs, res4, hsp4⟩ := triple_of_callW
    (s₀ := ⟨m3, Locals.init []⟩)
    (etaFabArgs_refines p hp.toIotaProg' N _ _ dn vis fe M3 eb T to tn major ef targs.toArray hS3 hT hmaj
      hsp3 (htop.trans hSt3.1.symm)) c4
  rw [ht4] at hS4 hg4 hsp4
  have ok4' : AM.ok (etaFabArgsE (decI T) targs (decE major) ef.toNat)
      (AM.st (pure (towerSlotsAll fe (decI T) ef.toNat) : AM Bool) a) := ok4
  have res4' : AM.res (etaFabArgsE (decI T) targs (decE major) ef.toNat)
      (AM.st (pure (towerSlotsAll fe (decI T) ef.toNat) : AM Bool) a) = xs := res4
  replace hS4 : CoreS dn m4 (AM.st (etaFabArgsE (decI T) targs (decE major) ef.toNat)
      (AM.st (pure (towerSlotsAll fe (decI T) ef.toNat) : AM Bool) a)) vis fe M4 eb := hS4
  have hrun4 := AM.run_of_ok _ _ ok4'
  rw [res4'] at hrun4
  rcases c5 : callW p N "intern_const" [ec, ust] m4 with _ | ⟨r5, m5⟩ <;>
    simp only [c5, reduceCtorEq] at hW
  obtain ⟨ok5, hD5, res5, hfr5, hh5⟩ := callW_internConst' p hp.constFind' hp.constPush'
    hp.internConst' N m4 _ hS4.arena ec ust hec hus r5 m5 c5
  have hrun5 := AM.run_of_ok _ _ ok5
  rw [res5] at hrun5
  have hS5 := hS4.of_const' hD5 (Keeps.run (keeps_cpl_internConst' _ _) hrun5) hfr5 hrun5 (by
    obtain ⟨x, c, hx⟩ := hvus
    have hx1 : (AM.st (pure (towerSlotsAll fe (decI T) ef.toNat) : AM Bool) a).store.view x = _ := hx
    exact hS4.den.constLs _ _ _ (etaFabArgsE_fwd hrun4 x _ (.inr ⟨_, _, rfl⟩) hx1))
  have hsp5 := hsp4.of_spn_core (const_spn hfr5)
  rcases c6 : callW p N "mk_app_n" [r5.headD 0, r4.headD 0, r4.tail.headD 0] m5 with _ | ⟨r6, m6⟩ <;>
    simp only [c6, reduceCtorEq] at hW
  obtain ⟨ok6, hD6, res6, hfr6, hh6⟩ := callW_mkAppN' p hp.spine N m5 _ hS5.arena
    (r5.headD 0) (r4.headD 0) (r4.tail.headD 0) _ hh5 hsp5 r6 m6 c6
  have hrun6 := AM.run_of_ok _ _ ok6
  rw [res6, show xs.toArray.toList = xs from rfl,
    show decE (r5.headD 0) = decI (r5.headD 0) from rfl] at hrun6
  have hS6 := hS5.of_app hD6 (Keeps.run (keeps_cpl_mkAppN' _ _) hrun6) hfr6
  rcases c7 : callW p N "fab_scope_ok" [d, r6.headD 0, major] m6 with _ | ⟨r7, m7⟩ <;>
    simp only [c7, reduceCtorEq] at hW
  obtain ⟨hrun7, ⟨M7, hS7, hK7, hSt7⟩, -⟩ := CoreSpec.run
    (fabScopeOk_refines' p hp.toIotaProg' hc N ⟨m6, Locals.init []⟩ _ dn vis fe M4 eb d (r6.headD 0)
      major hS6 hh6 hmaj) c7
  rw [show xs.toArray.toList = xs from rfl,
    show decE (r5.headD 0) = decI (r5.headD 0) from rfl] at hrun7
  have hA7 : CoreAfterG dn m m7 _ vis fe M eb :=
    ⟨M7, hS7, hK3.trans (hK4.trans hK7), hSt3.toGrew.trans (hg4.trans
      ((StackKept.of_constF hfr5).trans ((StackKept.of_app_frame hfr6).trans hSt7)).toGrew)⟩
  have hpre : (m2cEta2T fe d.toNat (decI T) (decI ec) ef.toNat targs (decI ust) (decE major)).run a =
      (if decBool r7 = true then pure (decE (r6.headD 0)) else pure (decE major) : AM EIdx).run
        (AM.st (fabScopeOk d.toNat (decE (r6.headD 0)) (decE major))
          (AM.st (mkAppN (decI (r5.headD 0)) xs) (AM.st (internE (.const (decI ec) (decI ust)))
            (AM.st (etaFabArgsE (decI T) targs (decE major) ef.toNat)
              (AM.st (pure (towerSlotsAll fe (decI T) ef.toNat) : AM Bool) a))))) := by
    simp only [m2cEta2T, StateT.run_bind, hl, except_ok_bind]
    rw [if_pos hres]
    simp only [StateT.run_bind, hrun3, except_ok_bind, ↓reduceIte, hrun4, hrun5, hrun6, hrun7]
  by_cases g7 : r7.headD 0 = 0
  · rw [if_pos g7] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA7 (decH_of _ _ hr) (resH_of_m2c _ _ hr hmaj)
    rw [hpre, decBool_f_m2c g7]; rfl
  · rw [if_neg g7] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA7 (decH_of _ _ hr) (resH_of_m2c _ _ hr hh6)
    rw [hpre, decBool_t_m2c g7]; rfl

include hE in
/-- **`m2c_eta` refines `m2cEtaT`** (`indP` the family's record). -/
theorem m2cEta_ok (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d T indP major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hT : HW T) (hmaj : HW major) (cvT : IConstantVal) (caps : IIndCaps) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb)
    (hci : decCI (m.arr64 EREC) dn indP.toNat = some (.indInfo cvT caps))
    (hfe : ∃ c, fe.find? c = some (.indInfo cvT caps)) (r : List Word) (m' : Mem)
    (h : callW p (N + 1) "m2c_eta" [mode, vis, d, T, indP, major] m = some (r, m')) :
    GrowRef (m2cEtaT (coreKnot (decMode mode) fe id F) fe d.toNat (decI T) cvT caps (decE major)) a
      decH dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (m2cEta_spec p hp.eta N _ mode vis d T indP major) h
  dsimp only at hW
  rw [hs'] at hW
  simp only [m2cEtaW] at hW
  -- the record's words
  obtain ⟨po, pc, swd, so, sc, hpo, hpc, hsl, hswd, hso, hsc, hpw⟩ :=
    decCI_ind_fields _ dn _ cvT caps hci
  obtain ⟨w6, w7, w8, e6, l6, hec, e7, hep, e8, hef⟩ := decCI_ind_eta _ dn _ cvT caps hci
  have hsz := hS.erec
  have r2 : rdW (m.arr64 EREC) (indP + 2) = po := rdW_off' hpo (by simp) (by omega)
  have r3 : rdW (m.arr64 EREC) (indP + 3) = pc := rdW_off' hpc (by simp) (by omega)
  have r6 : rdW (m.arr64 EREC) (indP + 6) = w6 := rdW_off' e6 (by simp) (by omega)
  have r7 : rdW (m.arr64 EREC) (indP + 7) = w7 := rdW_off' e7 (by simp) (by omega)
  have r8 : rdW (m.arr64 EREC) (indP + 8) = w8 := rdW_off' e8 (by simp) (by omega)
  have r12 : rdW (m.arr64 EREC) (indP + 12) = swd := rdW_off' hswd (by simp) (by omega)
  have r13 : rdW (m.arr64 EREC) (indP + 13) = so := rdW_off' hso (by simp) (by omega)
  have r14 : rdW (m.arr64 EREC) (indP + 14) = sc := rdW_off' hsc (by simp) (by omega)
  rw [r2, r3, r6, r7, r8, r12, r13, r14] at hW
  have hlps : cvT.levelParams.length = pc.toNat := hslice?_length hsl
  cases N with
  | zero => simp [callW_zero] at hW
  | succ N' =>
  rcases c1 : callW p (N' + 1) "m2c_pre" [mode, vis, d, major] m with _ | ⟨L, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨a1, hpre, ⟨M1, hS1, hK1, hSt1⟩, he1, hhw⟩ := m2cPre_ok p hp hE N' F
    (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode d major hm4 hebm hmaj m a M hS
    L m1 c1
  by_cases g0 : L.headD 0 = 0
  · rw [if_pos g0] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ (CoreAfter.toG ⟨M1, hS1, hK1, hSt1⟩) (decH_of _ _ hr)
      (resH_of_m2c _ _ hr hmaj)
    unfold m2cEtaT; exact m2cPreT_none hpre g0 _
  rw [if_neg g0] at hW
  obtain ⟨htm, hT2, hus⟩ := hhw g0
  obtain ⟨l, hvls, hll, -⟩ := hpre.view g0
  have hpre' := m2cPreT_some hpre g0
  rcases c2 : callW p (N' + 1) "get_app_args" [L.tail.headD 0] m1 with _ | ⟨r2', m2⟩ <;>
    simp only [c2, reduceCtorEq] at hW
  obtain ⟨t2, ht2, -, hfr2, hg2, htop2, htop2', xs, hargs, hsp2⟩ := triple_of_callW
    (s₀ := ⟨m1, Locals.init []⟩) (getAppArgs_refines p hp.spine (N' + 1) _ a1 hS1.arena.1 _ htm hS1.spn) c2
  rw [ht2] at hfr2 hg2 hsp2 htop2'
  have hS2 := hS1.frame_stk hfr2 (by simp) (by simp)
  have he2 : m2.arr64 EREC = m1.arr64 EREC := hfr2.1 EREC (by simp [EREC, SPN]) (by decide)
  have hlen : xs.length = (r2'.tail.headD 0).toNat := by simpa using hsp2.size
  rcases c3 : callW p (N' + 1) "caps_never_zero" [po, pc, L.tail.tail.tail.headD 0, swd, so, sc] m2 with _ | ⟨r3', m3⟩ <;>
    simp only [c3, reduceCtorEq] at hW
  have hEe : m2.arr64 EREC = m.arr64 EREC := he2.trans he1
  obtain ⟨hrun3, ⟨M3, hS3, hK3, hSt3⟩, -⟩ := CoreSpec.run
    (hc.capsNeverZero (N' + 1) ⟨m2, Locals.init []⟩ a1 dn vis fe M1 eb po pc _ swd so sc
      cvT.levelParams caps.sortZ hS2 hus (by rw [hEe]; exact hsl)
      (hS2.den.constLps _ _ hfe.choose_spec) (by rw [hEe]; exact hpw)) c3
  have hrun3' : (capsNeverZero cvT.levelParams (decI (L.tail.tail.tail.headD 0)) caps).run a1 =
      .ok (decBool r3', AM.st (capsNeverZeroPW cvT.levelParams (decI (L.tail.tail.tail.headD 0))
        caps.sortZ) a1) := hrun3
  have hA3 : CoreAfterG dn m m3 (AM.st (capsNeverZeroPW cvT.levelParams
      (decI (L.tail.tail.tail.headD 0)) caps.sortZ) a1) vis fe M eb :=
    ⟨M3, hS3, hK1.trans hK3, hSt1.toGrew.trans (hg2.trans hSt3.toGrew)⟩
  have hstep : (m2cEtaT (coreKnot (decMode mode) fe id F) fe d.toNat (decI T) cvT caps
      (decE major)).run a =
      (if (decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ xs.length = caps.etaParams ∧
          l.length = cvT.levelParams.length ∧ decBool r3' = true then
        m2cEta2T fe d.toNat (decI T) caps.etaCtor caps.etaFields xs (decI (L.tail.tail.tail.headD 0))
          (decE major)
      else pure (decE major)).run (AM.st (capsNeverZeroPW cvT.levelParams
        (decI (L.tail.tail.tail.headD 0)) caps.sortZ) a1) := by
    unfold m2cEtaT; rw [hpre']
    simp only [StateT.run_bind, hvls, except_ok_bind, hargs, hrun3']
  have hmaj' : ∀ (hn : ¬ ((decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ xs.length = caps.etaParams ∧
      l.length = cvT.levelParams.length ∧ decBool r3' = true))
      (hr : major = r.headD 0) (hm : m3 = m'),
      GrowRef (m2cEtaT (coreKnot (decMode mode) fe id F) fe d.toNat (decI T) cvT caps (decE major)) a
        decH dn m vis fe M eb r m' := by
    intro hn hr hm
    subst hm
    refine GrowRef.of_run ?_ hA3 (decH_of _ _ hr) (resH_of_m2c _ _ hr hmaj)
    rw [hstep, if_neg hn]; rfl
  by_cases g2 : L.tail.tail.headD 0 ≠ T
  · rw [if_pos g2] at hW
    obtain ⟨hr, hm⟩ := ret_eq hW
    exact hmaj' (fun e => g2 ((decI_inj_m2c hT2 hT).mp e.1)) hr hm
  rw [if_neg g2] at hW
  have g2' : L.tail.tail.headD 0 = T := by simpa using g2
  by_cases g3 : r2'.tail.headD 0 ≠ w7
  · rw [if_pos g3] at hW
    obtain ⟨hr, hm⟩ := ret_eq hW
    exact hmaj' (fun e => g3 (UInt64.toNat_inj.mp (by rw [← hlen, e.2.1, hep]))) hr hm
  rw [if_neg g3] at hW
  have g3' : r2'.tail.headD 0 = w7 := by simpa using g3
  by_cases g4 : L.tail.tail.tail.tail.headD 0 ≠ pc
  · rw [if_pos g4] at hW
    obtain ⟨hr, hm⟩ := ret_eq hW
    exact hmaj' (fun e => g4 (UInt64.toNat_inj.mp (by rw [← hll, e.2.2.1, hlps]))) hr hm
  rw [if_neg g4] at hW
  have g4' : L.tail.tail.tail.tail.headD 0 = pc := by simpa using g4
  by_cases g5 : r3'.headD 0 = 0
  · rw [if_pos g5] at hW
    obtain ⟨hr, hm⟩ := ret_eq hW
    exact hmaj' (fun e => by rw [decBool_f_m2c g5] at e; exact Bool.false_ne_true e.2.2.2) hr hm
  rw [if_neg g5] at hW
  have hcond : (decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ xs.length = caps.etaParams ∧
      l.length = cvT.levelParams.length ∧ decBool r3' = true :=
    ⟨by rw [g2'], by rw [hlen, g3', hep], by rw [hll, g4', hlps], decBool_t_m2c g5⟩
  rcases c4 : callW p (N' + 1) "m2c_eta2" [vis, d, T, w6, w8, r2'.headD 0, r2'.tail.headD 0,
      L.tail.tail.tail.headD 0, major] m3 with _ | ⟨r4, m4⟩ <;> simp only [c4, reduceCtorEq] at hW
  obtain ⟨hr, rfl⟩ := ret_eq hW
  have hspn2 : (m2.arr64 SPN).size < 2 ^ 63 := hS2.spn
  have htop3 : r2'.headD 0 + r2'.tail.headD 0 = spTop m3 := by
    rw [hSt3.1, htop2', htop2]
  have hsp3 : SpineR m3 (r2'.headD 0) (r2'.tail.headD 0) xs.toArray :=
    hsp2.ofKept hSt3 (by
      have hb := hsp2.bound
      rw [htop2', ← htop2, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
      exact Nat.le_refl _) hspn2
  obtain ⟨ok4, hA4, res4, hr4⟩ := m2cEta2_ok p hp hc hcc N' dn vis fe eb d T w6 w8 _ _ _ major hT l6
    hus hmaj xs m3 _ M3 hS3 hsp3 htop3 r4 m4
    (by obtain ⟨_, _, _, _, _, _, _, _, hp5⟩ := hpre
        exact ⟨_, _, view_after_noLss (by
          unfold capsNeverZeroPW
          exact Keeps.noLss_of_stP (Keeps.bind (keeps_stP_readNamesM _) fun _ =>
            Keeps.bind (keeps_stP_readLevelsM _) fun _ => Keeps.pure _)) (hp5 g0).2.2.1⟩) c4
  have hrun4 := AM.run_of_ok _ _ ok4
  rw [res4] at hrun4
  refine GrowRef.of_run (v := decH r4) ?_ (CoreAfterG.compK (hK1.trans hK3)
    (hSt1.toGrew.trans (hg2.trans hSt3.toGrew)) hA4) (by unfold decH; rw [hr])
    (by unfold ResH at hr4 ⊢; rw [← hr]; exact hr4)
  rw [hstep, if_pos hcond, hec, hef]; exact hrun4

end etaarm

end L.Arena
