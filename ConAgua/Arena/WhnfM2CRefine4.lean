module

import ConAgua.Arena.WhnfM2CRefine3
import ConAgua.Arena.WhnfIotaRefine6
import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.Arena.RefWalk
import ConAgua.Arena.StoreDenIntern
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.WhnfIotaRefine3
public import ConAgua.Arena.WhnfM2CRefine2

@[expose] public section

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
    (cv : IConstantVal) (caps : IIndCaps) (h : decCI (aread b) q = some (.indInfo cv caps)) :
    ∃ w6 w7 w8 : Word, b[q+6]? = some w6 ∧ w6.toNat < 2 ^ 32 ∧ caps.etaCtor = decI w6 ∧
      b[q+7]? = some w7 ∧ caps.etaParams = w7.toNat ∧ b[q+8]? = some w8 ∧
      caps.etaFields = w8.toNat := by
  sorry

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
  · rw [ite_eq_left g1] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA0 (decH_of _ _ hr) (resH_of_m2c _ _ hr hmaj)
    have hn : ¬ (l.contains (decI T) = false ∧ l.contains (decI ec) = false) := fun e => by
      have e1 := e.1; rw [hcT] at e1; exact g1 (by simpa using e1)
    simp only [m2cEta2T, StateT.run_bind, hl, except_ok_bind]
    rw [ite_eq_right hn]; rfl
  rw [ite_eq_right g1] at hW
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
  · rw [ite_eq_left g2] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA0 (decH_of _ _ hr) (resH_of_m2c _ _ hr hmaj)
    have hn : ¬ (l'.contains (decI T) = false ∧ l'.contains (decI ec) = false) := fun e => by
      have e2 := e.2; rw [hcE] at e2; exact g2 (by simpa using e2)
    simp only [m2cEta2T, StateT.run_bind, hl, except_ok_bind]
    rw [ite_eq_right hn]; rfl
  rw [ite_eq_right g2] at hW
  have hres : l'.contains (decI T) = false ∧ l'.contains (decI ec) = false := by
    have g1' : r1.headD 0 = 0 := Classical.not_not.mp g1
    have g2' : r2.headD 0 = 0 := Classical.not_not.mp g2
    exact ⟨by rw [hcT, g1']; rfl, by rw [hcE, g2']; rfl⟩
  rcases c3 : callW p N "tower_slots_all" [vis, T, ef] m with _ | ⟨r3, m3⟩ <;>
    simp only [c3, reduceCtorEq] at hW
  obtain ⟨hrun3, ⟨M3, hS3, hK3, hSt3⟩, -⟩ := CoreSpec.run
    (towerSlotsAll_refines' p hp.toIotaProg' hcc.findProj hcc.projFound N ⟨m, Locals.init []⟩ a dn vis fe M eb T ef hS hT) c3
  by_cases g3 : r3.headD 0 = 0
  · rw [ite_eq_left g3] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ (CoreAfter.toG ⟨M3, hS3, hK3, hSt3⟩) (decH_of _ _ hr)
      (resH_of_m2c _ _ hr hmaj)
    rw [decBool_f_m2c g3] at hrun3
    simp only [m2cEta2T, StateT.run_bind, hl, except_ok_bind]
    rw [ite_eq_left hres]
    simp only [StateT.run_bind, hrun3, except_ok_bind, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [ite_eq_right g3] at hW
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
    rw [ite_eq_left hres]
    simp only [StateT.run_bind, hrun3, except_ok_bind, ↓reduceIte, hrun4, hrun5, hrun6, hrun7]
  by_cases g7 : r7.headD 0 = 0
  · rw [ite_eq_left g7] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA7 (decH_of _ _ hr) (resH_of_m2c _ _ hr hmaj)
    rw [hpre, decBool_f_m2c g7]; rfl
  · rw [ite_eq_right g7] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ hA7 (decH_of _ _ hr) (resH_of_m2c _ _ hr hh6)
    rw [hpre, decBool_t_m2c g7]; rfl

/- ronsync2 stage 2: commented out (statement at the old twin/L)
include hE in
/-- **`m2c_eta` refines `m2cEtaT`, both outcomes** (`indP` the family's record; the errors are
`m2c_pre`'s). -/
theorem m2cEta_ref (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d T indP major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hT : HW T) (hmaj : HW major) (cvT : IConstantVal) (caps : IIndCaps) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb)
    (hci : decCI (erecP m) indP.toNat = some (.indInfo cvT caps))
    (hfe : ∃ c, fe.find? c = some (.indInfo cvT caps)) :
    RefE (M2CCtxE p N) (m2cEtaE p (N + 1) m mode vis d T indP major)
      (m2cEtaT (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI T) cvT caps (decE major)) a
      (GrowPost decH dn m vis fe M eb ResH) := by
  sorry

-/

end etaarm

end L.Arena
