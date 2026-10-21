import ConAgua.Arena.LitRefine

/-!
# Slices of the pool as keys

The `lit` store keeps a natural number's limbs in the pool (`POOL`) and its record points at the
slice. The level-list store (`LsRefine.lean`) and the name store's `str` table (`NStrRefine.lean`)
do the same with other contents: a level list's handle words, a string's UTF-8 bytes (one byte
per word). What they share is that a key is a list of words, stored as a slice `(o, l)` below the
pool top, compared by `limbs_eq` (`eqW`) after the lengths, hashed by `lit_hash` (`hashN`):

* `sliceL p o l`, the words of a slice, as a list;
* `slice_key`: for slices that do not wrap, "the lengths agree and `limbs_eq` holds" is equality
  of the two word lists; `slice_key_hash`: equal lists, equal hashes;
* `Agree.sliceL`: the pool growing above the top leaves every slice below it alone.

A table instance adds the encoding of its key as a list of words and the encoding's injectivity
(`lsWords_inj`, `strWords_inj`). `lit`'s key is not a list: a natural number is a *normalised*
slice, and its uniqueness (`pv_len`, `pv_limbs`, `LitRefine.lean`) is about the value, not the
words; it shares `eqW_iff` and `hashN_congr` with this file, not the statement.
-/

open ConRon.Arena

namespace L.Arena

/-- The words of the slice `(o, l)` of `p`. -/
def sliceL (p : Array Word) (o l : Nat) : List Word := List.ofFn fun k : Fin l => p[o + k]?.getD 0

theorem sliceL_length (p : Array Word) (o l : Nat) : (sliceL p o l).length = l := by
  simp [sliceL]

theorem sliceL_eq_iff (p q : Array Word) (a b l : Nat) :
    sliceL p a l = sliceL q b l ↔ ∀ k < l, p[a + k]?.getD 0 = q[b + k]?.getD 0 := by
  rw [sliceL, sliceL, List.ext_getElem_iff]
  simp

/-- The pool growing above `t` leaves the slices below `t` alone. -/
theorem Agree.sliceL (p q : Array Word) (t o l : Nat) (h : Agree p q t) (hk : o + l ≤ t) :
    L.Arena.sliceL p o l = L.Arena.sliceL q o l :=
  (sliceL_eq_iff p q o o l).mpr fun i hi => by rw [h (o + i) (by omega)]

/-- **A slice key matches iff the word lists are equal**: for a record slice `(a, la)` and a
query slice `(b, lb)` that do not wrap, the L match (lengths, then `limbs_eq`) holds iff the two
slices hold the same words. -/
theorem slice_key (p : Array Word) (a la b lb : Word) (ha : a.toNat + la.toNat < 2 ^ 64)
    (hb : b.toNat + lb.toNat < 2 ^ 64) :
    ((la == lb) && eqW p a b lb 0) = true ↔
      L.Arena.sliceL p a.toNat la.toNat = L.Arena.sliceL p b.toNat lb.toNat := by
  constructor
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, he⟩ := h
    exact (sliceL_eq_iff p p _ _ _).mpr fun k hk =>
      (eqW_iff p a b la 0 ha hb).mp he k (Nat.zero_le _) hk
  · intro h
    have hl : la = lb := UInt64.toNat_inj.mp (by
      have := congrArg List.length h; simpa only [sliceL_length] using this)
    subst hl
    simp only [beq_self_eq_true, Bool.true_and]
    exact (eqW_iff p a b la 0 ha hb).mpr fun k _ hk => (sliceL_eq_iff p p _ _ _).mp h k hk

/-- Equal slices have equal hashes. -/
theorem slice_key_hash (p q : Array Word) (a la b lb : Nat)
    (h : L.Arena.sliceL p a la = L.Arena.sliceL q b lb) : hashN p a la = hashN q b lb := by
  have hl : la = lb := by have := congrArg List.length h; simpa only [sliceL_length] using this
  subst hl
  exact hashN_congr p q a b la ((sliceL_eq_iff p q a b la).mp h)

end L.Arena
