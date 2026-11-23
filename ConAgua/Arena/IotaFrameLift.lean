module

public import ConAgua.Arena.IotaFrameMinors
import ConAgua.Arena.IndMaster
import ConAgua.Arena.IndCopy2
import ConAgua.Arena.IndSumSpec.StructProjArgP
import ConAgua.Arena.IndPosSpec.DpGoW
import ConAgua.Arena.LiftRefine
import ConAgua.Arena.Keeps
import ConAgua.Arena.WriteSets
import ConAgua.L.WordOff

@[expose] public section

/-!
# `lift_field_doms` refines `liftFieldDoms` (lane ronsync8)

The loop fills a fresh slice `(o, fl)`: word `j` the `j`-th domain lifted (`lift_entry`, the
twin's `liftLooseBVarsFast`), the written prefix a `decHL` prefix of the answer.
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

theorem iotaLiftA_tier : ∀ b ∈ liftA, InStoreTier b := by simp only [liftA]; decide

theorem iotaLiftC_lt : ∀ x ∈ liftC, x.toNat < 64 := by
  intro x hx; simp only [liftC, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- **`lift_entry`'s step** at any cutoff `c`: con-ron's `liftLooseBVarsFast` at the core walk
fuel, the stage relation and the growth after. -/
theorem liftEntry_stepC {p : Prog} {vis : Word} {fe : IFEnv} (hL : LiftProg p)
    (he : p.lookup "lift_entry" = some liftEntry) {n : Nat}
    {m m' : Mem} {a : AState} {h k c : Word} {r : List Word} (hS : StageR vis fe m a)
    (hh : H h) (hc : callW p n "lift_entry" [h, k, c, CWF] m = some (r, m')) :
    ∃ a', (liftLooseBVarsFast coreWalkFuel k.toNat c.toNat (decI h)).run a = .ok (decI (r.headD 0), a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' := by
  have hfr : MemFrame liftA liftC m m' :=
    (run_memFrame (hL.closed he) (by decide) (run_of_callW hc)).1
  rcases n with _ | n
  · rw [callW_zero] at hc; cases hc
  obtain ⟨s', hs', -, hok, hD, hres⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (liftEntry_refines p hL he n _ a hS.check.arena h k c CWF hh) hc
  rw [hs'] at hD
  have hrun := AM.run_of_ok _ a hok
  rw [CWF_eq] at hrun hD hres
  have hcp := (keeps_liftFast _ _ _ _).run hrun
  obtain ⟨hS', hg⟩ := StageR.of_walk hS hD hfr iotaLiftA_tier iotaLiftC_lt hcp
  refine ⟨_, ?_, hS', hg⟩
  show (liftLooseBVarsFast coreWalkFuel k.toNat c.toNat (decE h)).run a = .ok (decE (r.headD 0), _)
  rw [hrun, hres]

/-- A slice of handles past its first `j` words. -/
theorem decHL_step {k : IdxKind} {m : Mem} {fo fl j : Word} {ds : List (Idx k)}
    (h : decHL m (fo.toNat + j.toNat) (fl.toNat - j.toNat) = some ds) (hj : j < fl)
    (hb : fo.toNat + fl.toNat < 2 ^ 64) :
    ∃ w ds', ds = decI w :: ds' ∧ rdW (m.arr64 IW) (fo + j) = w ∧ w.toNat < 2 ^ 32 ∧
      decHL m (fo.toNat + (j.toNat + 1)) (fl.toNat - (j.toNat + 1)) = some ds' := by
  have hj' := UInt64.lt_iff_toNat_lt.mp hj
  have hfj : (fo + j).toNat = fo.toNat + j.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hlj : (fl - j).toNat = fl.toNat - j.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
  rw [← hfj, ← hlj] at h
  obtain ⟨w, ds', rfl, hw, hlt, hr⟩ := decHL_cons h
    (fun e => by rw [e] at hlj; simp at hlj; omega) (by rw [hfj, hlj]; omega)
  refine ⟨w, ds', rfl, hw, hlt, ?_⟩
  have e1 : (fo + j + 1).toNat = fo.toNat + (j.toNat + 1) := by
    rw [UInt64.toNat_add, hfj]; simp; omega
  have e2 : (fl - j - 1).toNat = fl.toNat - (j.toNat + 1) := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hlj]; simp; omega), hlj]; simp; omega
  rw [e1, e2] at hr; exact hr

/-- **`lift_field_doms`' loop against the twin's recursion**: from field `j` (the rest `ds` of the
input slice), a returning loop writes the twin's answer from `j` on after the prefix `ps`. -/
theorem liftFieldDoms_loop {p : Prog} (P : IotaFrameProg p) (vis : Word) (fe : IFEnv)
    (amt fo fl o : Word) (m₀ : Mem) (hfl : fo.toNat + fl.toNat ≤ iwTop m₀)
    (ho : iwTop m₀ ≤ o.toNat) :
    ∀ (k : Nat) (m m' : Mem) (a : AState) (j : Word) (ds ps : List EIdx),
      liftFieldDomsW.loop1 p k m amt fo fl o j = some m' →
      StageR vis fe m a → IWGrow m₀ m → j.toNat ≤ fl.toNat →
      decHL m₀ (fo.toNat + j.toNat) (fl.toNat - j.toNat) = some ds →
      o.toNat + fl.toNat ≤ iwTop m → decHL m o.toNat j.toNat = some ps →
      ∃ xs a', (liftFieldDoms amt.toNat ds j.toNat).run a = .ok (xs, a') ∧
        StageR vis fe m' a' ∧ IWGrow m₀ m' ∧ decHL m' o.toNat fl.toNat = some (ps ++ xs) ∧
        o.toNat + fl.toNat ≤ iwTop m' := by
  have hT0 := iwTop_lt' m₀
  intro k
  induction k with
  | zero => intro m m' a j ds ps hl; rw [liftFieldDomsW.loop1.eq_1] at hl; cases hl
  | succ k ih =>
  intro m m' a j ds ps hl hS hg hjl hds hb hps
  by_cases hj : j < fl
  · rw [liftFieldDomsW.loop1.arm1 _ _ _ _ _ _ _ _ hj] at hl
    have hj' : j.toNat < fl.toNat := UInt64.lt_iff_toNat_lt.mp hj
    obtain ⟨w, ds', rfl, hw, hwlt, hds'⟩ := decHL_step hds hj (by omega)
    have hfj : (fo + j).toNat = fo.toNat + j.toNat := by
      rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [rdW_iw_grow hg (by rw [hfj]; omega), hw] at hl
    rcases h1 : callW p k "lift_entry" [w, amt, j, CWF] m with _ | ⟨r1, m1⟩
    · rw [h1, liftFieldDomsW.k_lift_entry.none] at hl; cases hl
    by_cases hbig : 4294967296 ≤ r1.headD 0
    · rw [h1, liftFieldDomsW.k_lift_entry.abort1 (hc1 := hbig)] at hl; cases hl
    rw [h1, liftFieldDomsW.k_lift_entry.arm1 (hc1 := hbig)] at hl
    have hH1 : H (r1.headD 0) := by
      have : ¬ (4294967296 : Nat) ≤ (r1.headD 0).toNat := hbig; show _ < _; omega
    obtain ⟨a1, hrun1, hS1, hg1⟩ := liftEntry_stepC P.lift P.lift_entry hS hwlt h1
    have hps1 : decHL m1 o.toNat j.toNat = some ps := decHL_grow' hg1 (by omega) hps
    have hj1 : (j + 1).toNat = j.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hsz : o.toNat + j.toNat < (m1.arr64 IW).size := by
      have := hS1.iw.iw; have := hg1.iw; omega
    have hps2 := decHL_write m1 o j (r1.headD 0) ps hH1 hS1.iw.iwSize hsz hps1
    rw [← hj1] at hps2
    have hoj : (o + j).toNat = o.toNat + j.toNat := by
      rw [UInt64.toNat_add]; have := hg1.iw; have := iwTop_lt' m1; exact Nat.mod_eq_of_lt (by omega)
    have hg2 : IWGrow m₀ (m1.set64 IW (o + j) (r1.headD 0)) :=
      (hg.trans hg1).set_iw _ _ (by rw [hoj]; omega)
    obtain ⟨xs, a', hrun, hS', hg', hd', hb'⟩ := ih _ m' a1 (j + 1) ds' (ps ++ [decI (r1.headD 0)]) hl
      (hS1.set_iw _ _) hg2 (by omega) (by rw [hj1]; exact hds') (by rw [iwTop_set64IW]; have := hg1.iw; omega) hps2
    rw [hj1] at hrun
    refine ⟨decI (r1.headD 0) :: xs, a', ?_, hS', hg', by simpa using hd', hb'⟩
    simp only [ConRon.Arena.liftFieldDoms, StateT.run_bind, hrun1, except_ok_bind, hrun]
    rfl
  · rw [liftFieldDomsW.loop1.arm2 _ _ _ _ _ _ _ _ hj] at hl
    cases hl
    have hjf : j.toNat = fl.toNat := by
      have := UInt64.not_lt.mp hj; rw [UInt64.le_iff_toNat_le] at this; omega
    rw [hjf, Nat.sub_self] at hds
    have : ds = [] := by simpa [decHL, hslice?] using hds.symm
    subst this
    refine ⟨[], a, rfl, hS, hg, by rw [← hjf]; simpa using hps, hb⟩

/-- **`lift_field_doms` refines `liftFieldDoms … 0`**: a fresh `IW` slice of handles. -/
@[refines ConRon.Arena.liftFieldDoms]
theorem liftFieldDoms_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (amt fo fl : Word) (fd : List EIdx) :
    RelW (fun m args => callW p n "lift_field_doms" args m) [amt, fo, fl]
      (fun m a => StageR vis fe m a ∧ decHL m fo.toNat fl.toNat = some fd ∧
        fo.toNat + fl.toNat ≤ iwTop m)
      (liftFieldDoms amt.toNat fd 0) (KeepPost vis fe (decRL (fun m => decHL m) 0)) := by
  intro m m' a r hc ⟨hS, hfd, htop⟩
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (liftFieldDoms_specW p P.lift_field_doms n _ amt fo fl) hc
  rcases n with _ | n
  · simp [liftFieldDomsW] at hW
  simp only [liftFieldDomsW] at hW
  by_cases hq : fl = 0
  · rw [if_pos hq] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hq
    have : fd = [] := by simpa [decHL, hslice?] using hfd.symm
    subst this
    exact ⟨[], a, rfl, hS, IWGrow.refl _, by simp [decHL, hslice?], by simp⟩
  rw [if_neg hq] at hW
  rcases ha : callW p n "iw_alloc" [fl] m with _ | ⟨r1, m1⟩
  · rw [ha, liftFieldDomsW.k_iw_alloc.none] at hW; cases hW
  rw [ha, liftFieldDomsW.k_iw_alloc.arm1] at hW
  obtain ⟨s1, rfl, -, ha1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iwAlloc_specW p (P.strip.get "iw_alloc") n _ _) ha
  obtain ⟨hS1, hg1, ho1, ht1⟩ := allocW_stage ha1 hS
  rcases hl : liftFieldDomsW.loop1 p (n + 1) s1.mem amt fo fl (r1.headD 0) 0 with _ | m2
  · rw [hl] at hW; cases hW
  rw [hl] at hW
  simp only [liftFieldDomsW.k_loop1] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨xs, a', hrun, hS', hg', hd', hb'⟩ := liftFieldDoms_loop P vis fe amt fo fl (r1.headD 0)
    m htop (Nat.le_of_eq ho1.symm) (n + 1) s1.mem _ a 0 fd [] hl hS1 hg1 (by simp)
    (by simpa using hfd) (by rw [ht1, ho1]; exact Nat.le_refl _) (by simp [decHL, hslice?])
  exact ⟨xs, a', hrun, hS', hg', by simpa using hd', hb'⟩

end L.Ind
