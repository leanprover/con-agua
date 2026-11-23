module

public import ConAgua.Arena.IotaFrameMinor
import ConAgua.Arena.RecClassSpec.Classes
import ConAgua.Arena.IndMaster
import ConAgua.Arena.IndCopy2
import ConAgua.L.WordOff

@[expose] public section

/-!
# `minors_from` refines `minorsFrom` (lane ronsync8)

The loop fills the fresh slice `(o, preL - q)` with the accepted positions, a prefix of it
(`decNL` of the count so far); `is_minor_at` grows the pool above the slice, so the slice's words
stay.
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

theorem iwTop_set64IW (m : Mem) (k v : Word) : iwTop (m.set64 IW k v) = iwTop m := by
  simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]

/-- A number written at the end of a decoded prefix extends it. -/
theorem decNL_set_end (m : Mem) (o j : Nat) (w v : Word) (ps : List Nat) (hw : w.toNat = o + j)
    (hsz : o + j < (m.arr64 IW).size) (h : decNL m o j = some ps) :
    decNL (m.set64 IW w v) o (j + 1) = some (ps ++ [v.toNat]) := by
  have e1 : decNL (m.set64 IW w v) o j = decNL m o j := by
    simp only [decNL]
    apply L.Ind.mapM_congr_of
    intro i hi
    have hi' : i < j := List.mem_range.mp hi
    simp only [iwN, nat?, iwA, aread_apply, set64IW_get]
    rw [ite_eq_right (by omega)]
  have e2 : iwN (m.set64 IW w v) (o + j) = some v.toNat := by
    simp [iwN, nat?, iwA, aread_apply, set64IW_get, hw, hsz]
  simp only [decNL, List.range_succ, List.mapM_append] at e1 h ⊢
  rw [e1, h]
  simp [e2]

/-- `decW0B`'s word is `0` exactly at `false`. -/
theorem decW0B_false {m : Mem} {r : List Word} {b : Bool} (h : decW0B m r b) (h0 : r.headD 0 = 0) :
    b = false := by
  have := h.1; rw [h0] at this; simpa using this.symm

theorem decW0B_true_im {m : Mem} {r : List Word} {b : Bool} (h : decW0B m r b) (h0 : r.headD 0 ≠ 0) :
    b = true := by
  have := h.1; rw [bne_iff_ne.mpr h0] at this; exact this.symm

/-- **`minors_from`'s loop against the twin's recursion**: from position `j` with the count `c`
and the prefix `ps` written, a returning loop answers the twin's positions from `j` on after `ps`;
the pool only grows from `m₀` (whose top is at most the slice's start `o`). -/
theorem minorsFrom_loop {p : Prog} (P : IotaFrameProg p) (vis : Word) (fe : IFEnv)
    (preO preL mot o : Word) (pre : List EIdx) (m₀ : Mem) (hpl : preL.toNat < 2 ^ 32)
    (hpre : decHL m₀ preO.toNat preL.toNat = some pre) (htop : preO.toNat + preL.toNat ≤ iwTop m₀)
    (ho : iwTop m₀ ≤ o.toNat) :
    ∀ (k : Nat) (m m' : Mem) (a : AState) (c j c' : Word) (ps : List Nat),
      minorsFromW.loop1 p k m preO preL mot o c j = some (c', m') →
      StageR vis fe m a → IWGrow m₀ m → j.toNat ≤ preL.toNat → c.toNat ≤ j.toNat →
      o.toNat + c.toNat + (preL.toNat - j.toNat) ≤ iwTop m →
      decNL m o.toNat c.toNat = some ps →
      ∃ xs a', (minorsFrom pre mot.toNat j.toNat).run a = .ok (xs, a') ∧
        StageR vis fe m' a' ∧ IWGrow m₀ m' ∧ decNL m' o.toNat c'.toNat = some (ps ++ xs) ∧
        o.toNat + c'.toNat ≤ iwTop m' := by
  have hlen : pre.length = preL.toNat := decHL_length m₀ hpre
  intro k
  induction k with
  | zero => intro m m' a c j c' ps hl; rw [minorsFromW.loop1.eq_1] at hl; cases hl
  | succ k ih =>
  intro m m' a c j c' ps hl hS hg hjl hcj hb hps
  by_cases hj : j < preL
  · rw [minorsFromW.loop1.arm1 _ _ _ _ _ _ _ _ _ hj] at hl
    have hj' : j.toNat < preL.toNat := UInt64.lt_iff_toNat_lt.mp hj
    rcases h1 : callW p k "is_minor_at" [preO, preL, mot, j] m with _ | ⟨r1, m1⟩
    · rw [h1, minorsFromW.k_is_minor_at.none] at hl; cases hl
    obtain ⟨b, a1, hrun1, hS1, hg1, hb1⟩ := isMinorAt_rel P k vis fe preO preL mot j pre
      (by omega) m m1 a r1 h1 ⟨hS, decHL_grow' hg htop hpre, Nat.le_trans htop hg.iw⟩
    have hps1 : decNL m1 o.toNat c.toNat = some ps := by
      rw [decNL_grow hg1 (by omega)]; exact hps
    have hj1 : (j + 1).toNat = j.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hstep : ∀ xs' a2, (minorsFrom pre mot.toNat (j.toNat + 1)).run a1 = .ok (xs', a2) →
        (minorsFrom pre mot.toNat j.toNat).run a =
          .ok ((if b then j.toNat :: xs' else xs'), a2) := by
      intro xs' a2 h2
      rw [minorsFrom.eq_def, ite_eq_left (by omega), StateT.run_bind, hrun1, except_ok_bind,
        StateT.run_bind, h2, except_ok_bind]
      cases b <;> rfl
    by_cases h0 : r1.headD 0 = 0
    · rw [h1, minorsFromW.k_is_minor_at.arm2 _ _ _ _ _ _ _ _ _ _ h0, minorsFromW.j1.eq_1] at hl
      have hbf := decW0B_false hb1 h0
      subst hbf
      obtain ⟨xs, a', hrun, hS', hg', hd', hb'⟩ := ih m1 m' a1 c (j + 1) c' ps hl hS1 (hg.trans hg1)
        (by omega) (by omega) (by rw [hj1]; have := hg1.iw; omega) hps1
      rw [hj1] at hrun
      exact ⟨xs, a', hstep _ _ hrun, hS', hg', hd', hb'⟩
    · rw [h1, minorsFromW.k_is_minor_at.arm1 _ _ _ _ _ _ _ _ _ _ h0, minorsFromW.j1.eq_1] at hl
      have hbt := decW0B_true_im hb1 h0
      subst hbt
      have hc1 : (c + 1).toNat = c.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; omega
      have hT1 := iwTop_lt' m1
      have hoc : (o + c).toNat = o.toNat + c.toNat := by
        rw [UInt64.toNat_add]; have := hg1.iw; exact Nat.mod_eq_of_lt (by omega)
      have hsz : o.toNat + c.toNat < (m1.arr64 IW).size := by
        have := hS1.iw.iw; have := hg1.iw; omega
      have hS2 := hS1.set_iw (o + c) j
      have hg2 : IWGrow m₀ (m1.set64 IW (o + c) j) :=
        (hg.trans hg1).set_iw _ _ (by rw [hoc]; omega)
      have hps2 := decNL_set_end m1 o.toNat c.toNat (o + c) j ps hoc hsz hps1
      rw [← hc1] at hps2
      obtain ⟨xs, a', hrun, hS', hg', hd', hb'⟩ := ih _ m' a1 (c + 1) (j + 1) c' (ps ++ [j.toNat]) hl
        hS2 hg2 (by omega) (by omega)
        (by rw [hj1, hc1, iwTop_set64IW]; have := hg1.iw; omega) hps2
      rw [hj1] at hrun
      refine ⟨j.toNat :: xs, a', hstep _ _ hrun, hS', hg', by simpa using hd', hb'⟩
  · rw [minorsFromW.loop1.arm2 _ _ _ _ _ _ _ _ _ hj] at hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
    have hj' : ¬ j.toNat < pre.length := by
      rw [hlen]; exact fun h => hj (UInt64.lt_iff_toNat_lt.mpr h)
    refine ⟨[], a, ?_, hS, hg, by simpa using hps, by omega⟩
    rw [minorsFrom.eq_def, ite_eq_right hj']; rfl

/-- **`minors_from` refines `minorsFrom`**: the positions as a fresh `IW` slice of numbers. -/
@[refines ConRon.Arena.minorsFrom]
theorem minorsFrom_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (preO preL mot q : Word) (pre : List EIdx) (hpl : preL.toNat < 2 ^ 32) :
    RelW (fun m args => callW p n "minors_from" args m) [preO, preL, mot, q]
      (fun m a => StageR vis fe m a ∧ decHL m preO.toNat preL.toNat = some pre ∧
        preO.toNat + preL.toNat ≤ iwTop m)
      (minorsFrom pre mot.toNat q.toNat) (KeepPost vis fe (decRL (fun m => decNL m) 0)) := by
  intro m m' a r hc ⟨hS, hpre, htop⟩
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (minorsFrom_specW p P.minors_from n _ preO preL mot q) hc
  have hlen : pre.length = preL.toNat := decHL_length m hpre
  rcases n with _ | n
  · simp [minorsFromW] at hW
  simp only [minorsFromW] at hW
  by_cases hq : preL ≤ q
  · rw [ite_eq_left hq] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have : ¬ q.toNat < pre.length := by rw [hlen]; rw [UInt64.le_iff_toNat_le] at hq; omega
    refine ⟨[], a, ?_, hS, IWGrow.refl _, rfl, by simp⟩
    rw [minorsFrom.eq_def, ite_eq_right this]; rfl
  rw [ite_eq_right hq] at hW
  have hq' : q.toNat < preL.toNat := by
    rw [UInt64.not_le, UInt64.lt_iff_toNat_lt] at hq; exact hq
  rcases ha : callW p n "iw_alloc" [preL - q] m with _ | ⟨r1, m1⟩
  · rw [ha, minorsFromW.k_iw_alloc.none] at hW; cases hW
  rw [ha, minorsFromW.k_iw_alloc.arm1] at hW
  obtain ⟨s1, rfl, -, ha1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iwAlloc_specW p (P.strip.get "iw_alloc") n _ _) ha
  obtain ⟨hS1, hg1, ho1, ht1⟩ := allocW_stage ha1 hS
  rcases hl : minorsFromW.loop1 p (n + 1) s1.mem preO preL mot (r1.headD 0) 0 q with _ | ⟨c', m2⟩
  · rw [hl] at hW; cases hW
  rw [hl] at hW
  simp only [minorsFromW.k_loop1] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have hpq : (preL - q).toNat = preL.toNat - q.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
  obtain ⟨xs, a', hrun, hS', hg', hd', hb'⟩ := minorsFrom_loop P vis fe preO preL mot (r1.headD 0) pre
    m hpl hpre htop (Nat.le_of_eq ho1.symm) (n + 1) s1.mem _ a 0 q c' [] hl hS1 hg1 (by omega) (by simp)
    (by rw [ht1, hpq, ho1]; simp) rfl
  exact ⟨xs, a', hrun, hS', hg', by simpa using hd', hb'⟩

end L.Ind
