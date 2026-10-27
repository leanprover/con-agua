import ConAgua.Arena.WhnfM2CRefine2

/-!
# `major_to_ctor`: refinements of the `And` arm (`m2c_and`, `m2c_and2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The two projections pushed after the type's arguments -/

theorem word_add2 (x : Word) : x + 1 + 1 = x + 2 := by
  rw [UInt64.add_assoc]; rfl

/-- **`m2c_and2`'s stack writes**: the relation is kept, the stack grew, and the slice `(to, tn + 2)`
denotes the arguments followed by the two projections. -/
theorem and2Push_ok {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {to tn p0 p1 : Word}
    {xs : Array EIdx} (hsp : SpineR m to tn xs) (htop : to + tn = spTop m) (hp0 : HW p0)
    (hp1 : HW p1) {m₃ : Mem} (h : and2Push m to tn p0 p1 = some m₃) :
    CoreS dn m₃ a vis fe M eb ∧ StackGrew m m₃ ∧
      SpineR m₃ to (tn + 2) ((xs.push (decE p0)).push (decE p1)) := by
  unfold and2Push at h
  split at h
  · rename_i hc
    obtain ⟨-, c2, -, c4, c5⟩ := hc
    obtain rfl := (Option.some.inj h).symm
    have hspn := hS.spn
    have hb := hsp.bound
    have ht : (to + tn).toNat = to.toNat + tn.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hassoc : to + tn + 1 = to + (tn + 1) := UInt64.add_assoc _ _ _
    have h1 : (tn + 1).toNat = tn.toNat + 1 := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]; rfl
    have sp1 := hsp.push hspn (by omega) p0 hp0
    have sz1 : ((m.set64 SPN (to + tn) p0).arr64 SPN).size = (m.arr64 SPN).size :=
      size_set64L _ _ _ _ _
    have h3 : (to + tn + 1).toNat = to.toNat + tn.toNat + 1 := by
      rw [UInt64.toNat_add, ht, Nat.mod_eq_of_lt (by simp; omega)]; rfl
    have sp2 := sp1.push (by rw [sz1]; exact hspn) (by rw [sz1, h1]; rw [sz1, h3] at c4; omega) p1 hp1
    rw [← hassoc, word_add2] at sp2
    have sp3 := sp2.setCtl 136 (to + tn + 2)
    have hf : MemFrame [SPN] [136] m
        (((m.set64 SPN (to + tn) p0).set64 SPN (to + tn + 1) p1).set64 CTL 136 (to + tn + 2)) :=
      ((MemFrame.set64 m SPN (by decide) _ _).mono (by simp) (by simp)).trans
        (((MemFrame.set64 _ SPN (by decide) _ _).mono (by simp) (by simp)).trans
          ((MemFrame.setCtl _ 136 _).mono (by simp) (by simp)))
    have e : spTop (((m.set64 SPN (to + tn) p0).set64 SPN (to + tn + 1) p1).set64 CTL 136
        (to + tn + 2)) = to + tn + 2 := by
      unfold spTop; rw [rdW_set64, ite_eq_left ⟨rfl, rfl, by simpa using c5⟩]
    have h2 : (to + tn + 2).toNat = to.toNat + tn.toNat + 2 := by
      rw [UInt64.toNat_add, ht, Nat.mod_eq_of_lt (by simp; omega)]; rfl
    refine ⟨hS.frame_stk hf (by simp) (by simp), ⟨?_, ?_, fun i hi => ?_,
      BKept.of_frame hf (by decide) (by decide), PoolGrew.of_frame hf (by decide) (by decide)⟩, sp3⟩
    · rw [e, ← htop, UInt64.le_iff_toNat_le, h2, ht]; omega
    · rw [size_set64L, size_set64L, size_set64L]
    · rw [← htop, UInt64.lt_iff_toNat_lt, ht] at hi
      rw [spW_setCtl, spW_set64_ne _ _ _ _ (fun e => by rw [← e, h3] at hi; omega),
        spW_set64_ne _ _ _ _ (fun e => by rw [← e, ht] at hi; omega)]
  · cases h

/-- A `proj` interning writes neither the stack nor its top. -/
theorem store_spn {m m' : Mem} (hf : MemFrame L.Rom.StoreA L.Rom.StoreC m m') :
    m'.arr64 SPN = m.arr64 SPN ∧ spTop m' = spTop m := by
  refine ⟨hf.1 SPN (fun h => by
      unfold L.Rom.StoreA at h; simp [lowTierArrs, SPN] at h) (by decide), ?_⟩
  unfold spTop
  exact hf.2.1 136 (fun h => by
    obtain ⟨k, hk, hkk⟩ := List.mem_map.mp
      (show (136 : Word) ∈ (List.range 64).map UInt64.ofNat by unfold L.Rom.StoreC at h; exact h)
    have := List.mem_range.mp hk
    have h' := congrArg UInt64.toNat hkk
    simp [UInt64.toNat_ofNat] at h'; omega)

theorem const_spn {m m' : Mem} (hf : MemFrame [CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP] [18, 19] m m') :
    m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [tier1, tierOff, CREC, CSLOT, CLP, SPN]) (by decide)

/-- A slice below the top survives a run that kept the stack. -/
theorem SpineR.ofKept {m m' : Mem} {o n : Word} {xs : Array EIdx} (h : SpineR m o n xs)
    (hk : StackKept m m') (htop : o.toNat + n.toNat ≤ (spTop m).toNat)
    (hspn : (m.arr64 SPN).size < 2 ^ 63) : SpineR m' o n xs :=
  h.keep hk.size hk.below htop hspn

theorem viewLsLen_some {a : AState} {h : LsIdx} {k : Nat} (hv : a.store.lss.viewLen h = some k) :
    (viewLsLen h).run a = .ok (some k, a) := by
  rw [viewLsLen_run, hv]

section andarm
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hpi : ProofIrrelOKM p)
  (hE : ErecKeptKnot p) (hcc : ProjCallees p)
include hp hc hpi

/-- **`m2c_and2` refines `m2cAnd2T`** (the slice `(to, tn)` ends at the stack top). -/
theorem m2cAnd2_ok (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ctor T tmaj to tn ust major : Word) (hm4 : mode < 4)
    (hebm : eb = (mode >>> 1) &&& 1) (hctor : HW ctor) (_hT : HW T) (htm : HW tmaj) (hus : HW ust)
    (hmaj : HW major) (targs : List EIdx) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hsp : SpineR m to tn targs.toArray) (htop : to + tn = spTop m)
    (r : List Word) (m' : Mem) (hvus : ∃ x c, a.store.view x = some (.const c (decI ust)))
    (h : callW p (N + 1) "m2c_and2" [mode, vis, d, ctor, T, tmaj, to, tn, ust, major] m =
      some (r, m')) :
    GrowRef (m2cAnd2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI ctor)
      (decI T) (decE tmaj) targs (decI ust) (decE major)) a decH dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (m2cAnd2_spec p hp.and2 N _ mode vis d ctor T tmaj to tn ust major) h
  dsimp only at hW
  rw [hs'] at hW
  simp only [m2cAnd2W] at hW
  cases N with
  | zero => simp [callW_zero] at hW
  | succ N' =>
  rcases c1 : callW p (N' + 1) "mk_proj" [T, 0, major] m with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨ok1, hD1, res1, hfr1, hh1⟩ := callW_mkProj p hp.toIotaProg' (N' + 1) ⟨m, Locals.init []⟩ a
    hS.arena T 0 major r1 m1 c1
  have hrun1 := AM.run_of_ok _ _ ok1
  rw [res1, show (0 : Word).toNat = 0 from rfl] at hrun1
  have hS1 := hS.of_proj hD1 (Keeps.run (keeps_cpl_internProj _ _ _) hrun1) hfr1
  obtain ⟨e1, t1⟩ := store_spn hfr1.pjStore
  rcases c2 : callW p (N' + 1) "mk_proj" [T, 1, major] m1 with _ | ⟨r2, m2⟩ <;>
    simp only [c2, reduceCtorEq] at hW
  obtain ⟨ok2, hD2, res2, hfr2, hh2⟩ := callW_mkProj p hp.toIotaProg' (N' + 1) ⟨m1, Locals.init []⟩ _
    hS1.arena T 1 major r2 m2 c2
  have hrun2 := AM.run_of_ok _ _ ok2
  rw [res2, show (1 : Word).toNat = 1 from rfl] at hrun2
  have hS2 := hS1.of_proj hD2 (Keeps.run (keeps_cpl_internProj _ _ _) hrun2) hfr2
  obtain ⟨e2, t2⟩ := store_spn hfr2.pjStore
  have hsp2 : SpineR m2 to tn targs.toArray := (hsp.of_spn_core e1).of_spn_core e2
  cases c3 : and2Push m2 to tn (r1.headD 0) (r2.headD 0) with
  | none => rw [c3] at hW; cases hW
  | some m3 =>
  rw [c3] at hW
  simp only at hW
  obtain ⟨hS3, hg3, hsp3⟩ := and2Push_ok hS2 hsp2 (by rw [t2, t1]; exact htop) hh1 hh2 c3
  rcases c4 : callW p (N' + 1) "intern_const" [ctor, ust] m3 with _ | ⟨r4, m4⟩ <;>
    simp only [c4, reduceCtorEq] at hW
  obtain ⟨ok4, hD4, res4, hfr4, hh4⟩ := callW_internConst' p hp.constFind' hp.constPush'
    hp.internConst' (N' + 1) m3 _ hS3.arena ctor ust hctor hus r4 m4 c4
  have hrun4 := AM.run_of_ok _ _ ok4
  rw [res4] at hrun4
  have hS4 := hS3.of_const' hD4 (Keeps.run (keeps_cpl_internConst' _ _) hrun4) hfr4 hrun4 (by
    obtain ⟨x, c, hx⟩ := hvus
    have hx1 := internNodeE_fwd (v := .proj _ _ _) (by simpa [internE] using hrun1) x _
      (.inr ⟨_, _, rfl⟩) hx
    have hx2 := internNodeE_fwd (v := .proj _ _ _) (by simpa [internE] using hrun2) x _
      (.inr ⟨_, _, rfl⟩) hx1
    exact hS3.den.constLs _ _ _ hx2)
  have hsp4 := hsp3.of_spn_core (const_spn hfr4)
  rcases c5 : callW p (N' + 1) "mk_app_n" [r4.headD 0, to, tn + 2] m4 with _ | ⟨r5, m5⟩ <;>
    simp only [c5, reduceCtorEq] at hW
  obtain ⟨ok5, hD5, res5, hfr5, hh5⟩ := callW_mkAppN' p hp.spine (N' + 1) m4 _ hS4.arena
    (r4.headD 0) to (tn + 2) _ hh4 hsp4 r5 m5 c5
  have hrun5 := AM.run_of_ok _ _ ok5
  rw [res5] at hrun5
  have hS5 := hS4.of_app hD5 (Keeps.run (keeps_cpl_mkAppN' _ _) hrun5) hfr5
  rcases c6 : callW p (N' + 1) "m2c_check" [mode, vis, d, tmaj, r5.headD 0, major] m5 with _ | ⟨r6, m6⟩ <;>
    simp only [c6, reduceCtorEq] at hW
  obtain ⟨hr, rfl⟩ := ret_eq hW
  obtain ⟨ok6, ⟨M6, hS6, hK6, hSt6⟩, res6, hr6⟩ := m2cCheck_ok p hp hc hpi N' F (hk.mono (Nat.le_succ _))
    (by omega) (by omega) dn vis fe eb mode d tmaj (r5.headD 0) major hm4 hebm htm hh5 hmaj m5 _ M
    hS5 r6 m6 c6
  have hrun6 := AM.run_of_ok _ _ ok6
  rw [res6] at hrun6
  have hgrow : StackGrew m m6 :=
    ((StackKept.of_frame hfr1).trans (StackKept.of_frame hfr2)).toGrew.trans
      (hg3.trans (((StackKept.of_constF hfr4).trans
        ((StackKept.of_app_frame hfr5).trans hSt6)).toGrew))
  refine GrowRef.of_run (v := decH r6) ?_ ⟨M6, hS6, hK6, hgrow⟩
    (by unfold decH; rw [hr]) (by unfold ResH at hr6 ⊢; rw [← hr]; exact hr6)
  have el : ((targs.toArray.push (decE (r1.headD 0))).push (decE (r2.headD 0))).toList =
      targs ++ [decE (r1.headD 0), decE (r2.headD 0)] := by simp
  rw [el, show decE (r4.headD 0) = decI (r4.headD 0) from rfl] at hrun5 hrun6
  have z0 : (0 : Word).toNat = 0 := rfl
  have z1 : (1 : Word).toNat = 1 := rfl
  simp only [z0, z1] at hrun2 hrun4 hrun5 hrun6
  rw [el, show decE (r4.headD 0) = decI (r4.headD 0) from rfl]
  simp only [z0, z1]
  simp only [m2cAnd2T, StateT.run_bind, hrun1, except_ok_bind, hrun2, hrun4, hrun5]
  exact hrun6

include hE hcc in
/-- **`m2c_and` refines `m2cAndT`.** -/
theorem m2cAnd_ok (N F : Nat) (hk : KnotUpTo p N) (hnF : N ≤ F) (hn62 : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d T major ctor lpl cnP : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hT : HW T) (hmaj : HW major) (hctor : HW ctor) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (r : List Word) (m' : Mem)
    (h : callW p (N + 1) "m2c_and" [mode, vis, d, T, major, ctor, lpl, cnP] m = some (r, m')) :
    GrowRef (m2cAndT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI ctor)
      lpl.toNat cnP.toNat (decI T) (decE major)) a decH dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (m2cAnd_spec p hp.and_ N _ mode vis d T major ctor lpl cnP) h
  dsimp only at hW
  rw [hs'] at hW
  simp only [m2cAndW] at hW
  cases N with
  | zero => simp [callW_zero] at hW
  | succ N' =>
  rcases c1 : callW p (N' + 1) "pin_at" [11] m with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨t1, ht1, hm1, -, hanHW, hpin⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pinAt_refines p hp.pinat (N' + 1) _ a ⟨fun _ => hS.pins⟩ 11) c1
  have hm1' : m1 = m := ht1.symm.trans hm1
  rw [hm1'] at hW
  have hpin' : pinAnd.run a = .ok (decI (r1.headD 0), a) := by simpa [pinAnd, PIN_AND] using hpin
  by_cases g1 : T ≠ r1.headD 0
  · rw [ite_eq_left g1] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ (CoreAfter.toG ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩)
      (decH_of _ _ hr) (resH_of_m2c _ _ hr hmaj)
    have hcond : ¬ ((decI T : NIdx) = decI (r1.headD 0)) := fun e => g1 ((decI_inj_m2c hT hanHW).mp e)
    simp only [m2cAndT, StateT.run_bind, hpin', except_ok_bind]
    rw [ite_eq_right hcond]; rfl
  rw [ite_eq_right g1] at hW
  have g1' : T = r1.headD 0 := by simpa using g1
  have hTan : (decI T : NIdx) = decI (r1.headD 0) := by rw [g1']
  rcases c2 : callW p (N' + 1) "m2c_pre" [mode, vis, d, major] m with _ | ⟨L, m2⟩ <;>
    simp only [c2, reduceCtorEq] at hW
  obtain ⟨a2, hpre, ⟨M2, hS2, hK2, hSt2⟩, -, hhw⟩ := m2cPre_ok p hp hE N' F
    (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode d major hm4 hebm hmaj m a M hS
    L m2 c2
  by_cases g0 : L.headD 0 = 0
  · rw [ite_eq_left g0] at hW
    obtain ⟨hr, rfl⟩ := ret_eq hW
    refine GrowRef.of_run ?_ (CoreAfter.toG ⟨M2, hS2, hK2, hSt2⟩) (decH_of _ _ hr)
      (resH_of_m2c _ _ hr hmaj)
    simp only [m2cAndT, StateT.run_bind, hpin', except_ok_bind]
    rw [ite_eq_left hTan]; exact m2cPreT_none hpre g0 _
  rw [ite_eq_right g0] at hW
  obtain ⟨htm, hT2, hus⟩ := hhw g0
  obtain ⟨l, -, hll, hvl⟩ := hpre.view g0
  have hpre' := m2cPreT_some hpre g0
  rcases c3 : callW p (N' + 1) "get_app_args" [L.tail.headD 0] m2 with _ | ⟨r3, m3⟩ <;>
    simp only [c3, reduceCtorEq] at hW
  obtain ⟨t3, ht3, -, hfr3, hg3, htop3, htop3', xs, hargs, hsp3⟩ := triple_of_callW
    (s₀ := ⟨m2, Locals.init []⟩) (getAppArgs_refines p hp.spine (N' + 1) _ a2 hS2.arena.1 _ htm hS2.spn) c3
  rw [ht3] at hfr3 hg3 hsp3 htop3'
  have hS3 := hS2.frame_stk hfr3 (by simp) (by simp)
  have hlen : xs.length = (r3.tail.headD 0).toNat := by simpa using hsp3.size
  rcases c4 : callW p (N' + 1) "and_rescue_slots" [vis, ctor, cnP, L.tail.tail.tail.headD 0] m3 with _ | ⟨r4, m4⟩ <;>
    simp only [c4, reduceCtorEq] at hW
  obtain ⟨hrun4, ⟨M4, hS4, hK4, hSt4⟩, -⟩ := CoreSpec.run
    (andRescueSlots_refines' p hp.toIotaProg' hcc (N' + 1) ⟨m3, Locals.init []⟩ a2 dn vis fe M2 eb
      ctor cnP _ hS3 hctor hus (hpre.cview g0)) c4
  have hA4 : CoreAfterG dn m m4 (AM.st (andRescueSlots fe (decI ctor) cnP.toNat
      (decI (L.tail.tail.tail.headD 0))) a2) vis fe M eb :=
    ⟨M4, hS4, hK2.trans hK4, hSt2.toGrew.trans (hg3.trans hSt4.toGrew)⟩
  have hstep : (m2cAndT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI ctor)
      lpl.toNat cnP.toNat (decI T) (decE major)).run a =
      (if (decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ xs.length = cnP.toNat ∧
          lpl.toNat = (L.tail.tail.tail.tail.headD 0).toNat ∧ decBool r4 = true then
        m2cAnd2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI ctor) (decI T)
          (decE (L.tail.headD 0)) xs (decI (L.tail.tail.tail.headD 0)) (decE major)
      else pure (decE major)).run
        (AM.st (andRescueSlots fe (decI ctor) cnP.toNat (decI (L.tail.tail.tail.headD 0))) a2) := by
    simp only [m2cAndT, StateT.run_bind, hpin', except_ok_bind]
    rw [ite_eq_left hTan, hpre']
    simp only [StateT.run_bind, viewLsLen_some hvl, except_ok_bind, hargs, hrun4]
  have hmaj' : ∀ (hn : ¬ ((decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ xs.length = cnP.toNat ∧
      lpl.toNat = (L.tail.tail.tail.tail.headD 0).toNat ∧ decBool r4 = true))
      (hr : major = r.headD 0) (hm : m4 = m'),
      GrowRef (m2cAndT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI ctor)
        lpl.toNat cnP.toNat (decI T) (decE major)) a decH dn m vis fe M eb r m' := by
    intro hn hr hm
    subst hm
    refine GrowRef.of_run ?_ hA4 (decH_of _ _ hr) (resH_of_m2c _ _ hr hmaj)
    rw [hstep, ite_eq_right hn]; rfl
  by_cases g2 : L.tail.tail.headD 0 ≠ T
  · rw [ite_eq_left g2] at hW
    obtain ⟨hr, hm⟩ := ret_eq hW
    exact hmaj' (fun e => g2 ((decI_inj_m2c hT2 hT).mp e.1)) hr hm
  rw [ite_eq_right g2] at hW
  have g2' : L.tail.tail.headD 0 = T := by simpa using g2
  by_cases g3 : r3.tail.headD 0 ≠ cnP
  · rw [ite_eq_left g3] at hW
    obtain ⟨hr, hm⟩ := ret_eq hW
    exact hmaj' (fun e => g3 (UInt64.toNat_inj.mp (hlen ▸ e.2.1))) hr hm
  rw [ite_eq_right g3] at hW
  have g3' : r3.tail.headD 0 = cnP := by simpa using g3
  by_cases g4 : lpl ≠ L.tail.tail.tail.tail.headD 0
  · rw [ite_eq_left g4] at hW
    obtain ⟨hr, hm⟩ := ret_eq hW
    exact hmaj' (fun e => g4 (UInt64.toNat_inj.mp e.2.2.1)) hr hm
  rw [ite_eq_right g4] at hW
  have g4' : lpl = L.tail.tail.tail.tail.headD 0 := by simpa using g4
  by_cases g5 : r4.headD 0 = 0
  · rw [ite_eq_left g5] at hW
    obtain ⟨hr, hm⟩ := ret_eq hW
    exact hmaj' (fun e => by rw [decBool_f_m2c g5] at e; exact Bool.false_ne_true e.2.2.2) hr hm
  rw [ite_eq_right g5] at hW
  have hcond : (decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ xs.length = cnP.toNat ∧
      lpl.toNat = (L.tail.tail.tail.tail.headD 0).toNat ∧ decBool r4 = true :=
    ⟨by rw [g2'], by rw [hlen, g3'], by rw [g4'], decBool_t_m2c g5⟩
  rcases c5 : callW p (N' + 1) "m2c_and2" [mode, vis, d, ctor, T, L.tail.headD 0, r3.headD 0,
      r3.tail.headD 0, L.tail.tail.tail.headD 0, major] m4 with _ | ⟨r5, m5⟩ <;>
    simp only [c5, reduceCtorEq] at hW
  obtain ⟨hr, rfl⟩ := ret_eq hW
  have hspn3 : (m3.arr64 SPN).size < 2 ^ 63 := hS3.spn
  have htop4 : r3.headD 0 + r3.tail.headD 0 = spTop m4 := by
    rw [hSt4.1, htop3', htop3]
  have hsp4 : SpineR m4 (r3.headD 0) (r3.tail.headD 0) xs.toArray :=
    hsp3.ofKept hSt4 (by
      have hb := hsp3.bound
      rw [htop3', ← htop3, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
      exact Nat.le_refl _) hspn3
  obtain ⟨ok5, hA5, res5, hr5⟩ := m2cAnd2_ok p hp hc hpi N' F (hk.mono (Nat.le_succ _)) (by omega)
    (by omega) dn vis fe eb mode d ctor T _ _ _ _ major hm4 hebm hctor hT htm hus hmaj xs m4 _ M4
    hS4 hsp4 htop4 r5 m5
    (by obtain ⟨_, _, _, _, _, _, _, _, hp5⟩ := hpre
        exact ⟨_, _, view_after_noLss (keeps_noLss_andRescueSlots _ _ _ _) (hp5 g0).2.2.1⟩) c5
  have hrun5 := AM.run_of_ok _ _ ok5
  rw [res5] at hrun5
  refine GrowRef.of_run (v := decH r5) ?_ (CoreAfterG.compK (hK2.trans hK4)
    (hSt2.toGrew.trans (hg3.trans hSt4.toGrew)) hA5) (by unfold decH; rw [hr])
    (by unfold ResH at hr5 ⊢; rw [← hr]; exact hr5)
  rw [hstep, ite_eq_left hcond]; exact hrun5

end andarm

end L.Arena
