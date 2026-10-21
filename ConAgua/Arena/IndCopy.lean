import ConAgua.Arena.IndLibSpec

/-!
# Copying slices (`iw_copy`) and building lists (`sl_cons`, `sl_snoc`, `sl_append`) (lane `induct`)

`iw_copy(d, s, l)` copies `IW[s ‥ s + l)` to `IW[d ‥ d + l)`, ascending; the word model `copyW`
follows the recursion, and `copyW_get` says what the array holds after it when the source lies
below the destination (every use: the destination is fresh, above the top).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The model of `iw_copy`. -/
def copyW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, d, s, l =>
    if l = 0 then some m
    else copyW n (m.set64 IW d (rdW (m.arr64 IW) s)) (d + 1) (s + 1) (l - 1)

section arms
variable (n : Nat) (m : Mem) (d s l : Word)
theorem copyW_nil (hl : l = 0) : copyW (n + 1) m d s l = some m := by simp [copyW, hl]
theorem copyW_step (hl : l ≠ 0) :
    copyW (n + 1) m d s l = copyW n (m.set64 IW d (rdW (m.arr64 IW) s)) (d + 1) (s + 1) (l - 1) := by
  simp [copyW, hl]
end arms

grind_pattern [ind_grind] copyW_nil => copyW (n + 1) m d s l
grind_pattern [ind_grind] copyW_step => copyW (n + 1) m d s l

theorem iwCopy_spec (p : Prog) (hp : p.lookup "iw_copy" = some iwCopy) (n : Nat) :
    ∀ (s₀ : St) (d s l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "iw_copy" [d, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ copyW n s₀.mem d s l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ d s l; rw [invoke_eq _ hp]; simp only [callFn, iwCopy]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ d s l
    rw [invoke_eq _ hp]
    simp only [callFn, iwCopy]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 20)

/-- **What a copy leaves**: every other array as it was, `IW` the same size, the destination
holding the source, the rest of `IW` unchanged — when the source ends at or below the destination
and the destination is in bounds (Nat offsets, no wrap). -/
theorem copyW_get (n : Nat) : ∀ (m m' : Mem) (d s l : Word), copyW n m d s l = some m' →
    s.toNat + l.toNat ≤ d.toNat → d.toNat + l.toNat ≤ (m.arr64 IW).size →
    (m.arr64 IW).size < 2 ^ 64 →
    (∀ b, b ≠ IW → m'.arr64 b = m.arr64 b) ∧ (m'.arr64 IW).size = (m.arr64 IW).size ∧
    m'.words.size = m.words.size ∧
    ∀ i, (m'.arr64 IW)[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + l.toNat then (m.arr64 IW)[s.toNat + (i - d.toNat)]?
      else (m.arr64 IW)[i]? := by
  induction n with
  | zero => intro m m' d s l h; simp [copyW] at h
  | succ n ih =>
    intro m m' d s l h hsd hd hsz
    by_cases hl : l = 0
    · rw [copyW_nil n m d s l hl] at h
      cases h
      subst hl
      refine ⟨fun _ _ => rfl, rfl, rfl, fun i => ?_⟩
      have : ¬ (d.toNat ≤ i ∧ i < d.toNat + (0 : Word).toNat) := by
        simp only [UInt64.toNat_zero]; omega
      simp only [this, if_false]
    · rw [copyW_step n m d s l hl] at h
      have hl0 : 0 < l.toNat := by
        have : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      have hl1 : (l - 1).toNat = l.toNat - 1 := by
        rw [UInt64.toNat_sub]; simp; omega
      have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hs1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hslt : s.toNat < (m.arr64 IW).size := by omega
      have hdlt : d.toNat < (m.arr64 IW).size := by omega
      obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.set64 IW d (rdW (m.arr64 IW) s) := ⟨_, rfl⟩
      rw [← hm1] at h
      have hsz1 : (m1.arr64 IW).size = (m.arr64 IW).size := by
        rw [hm1, Mem.arr64_set64_same]; simp
      have hget1 : ∀ i, (m1.arr64 IW)[i]? = if i = d.toNat then (m.arr64 IW)[s.toNat]?
          else (m.arr64 IW)[i]? := by
        intro i
        rw [hm1, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        by_cases hi : d.toNat = i
        · subst hi
          simp only [hdlt, true_and, if_true]
          simp [rdW, Array.getElem?_eq_getElem hslt]
        · simp [hi, Ne.symm hi]
      obtain ⟨hA, hS, hW, hG⟩ := ih m1 m' (d + 1) (s + 1) (l - 1) h
        (by rw [hs1, hd1, hl1]; omega) (by rw [hd1, hl1, hsz1]; omega) (by rw [hsz1]; exact hsz)
      refine ⟨fun b hb => (hA b hb).trans ?_, hS.trans hsz1, hW.trans ?_, fun i => ?_⟩
      · rw [hm1, Mem.arr64_set64_ne _ _ _ _ _ hb]
      · rw [hm1]; exact Mem.words_size_set64 _ _ _ _
      · rw [hG i, hd1, hl1, hs1]
        by_cases hi : d.toNat ≤ i ∧ i < d.toNat + l.toNat
        · rw [if_pos hi]
          by_cases hid : i = d.toNat
          · subst hid
            have : ¬ (d.toNat + 1 ≤ d.toNat ∧ d.toNat < d.toNat + 1 + (l.toNat - 1)) := by omega
            rw [if_neg this, hget1, if_pos rfl]; simp
          · have h2 : d.toNat + 1 ≤ i ∧ i < d.toNat + 1 + (l.toNat - 1) := by omega
            rw [if_pos h2, hget1, if_neg (by omega)]
            congr 1; omega
        · rw [if_neg hi, if_neg (by omega), hget1, if_neg (by omega)]

end L.Ind
