module

public import ConAgua.L.Syntax

public section

/-!
# L: words at a literal offset, word arithmetic, word lists

A packed record is a base word plus a literal field offset, `b + 9`. `off_toNat` turns
`(b + 9).toNat` into `b.toNat + 9` when the sum fits; used as
`simp (disch := omega) only [off_toNat]`, it rewrites every literal offset of a goal and leaves
`omega` a context without chained `(b + k).toNat = b.toNat + k` facts (with many of those in
context, `omega`'s equality elimination slows down exponentially). `off_omega` is that rewrite
followed by `omega`.

The literal is matched as `no_index (OfNat.ofNat k)`, and the right side is the `Nat` numeral
`OfNat.ofNat k`, not the raw `k`, which `omega` would treat as an atom.
-/

namespace L

/-- A word plus a literal offset, when the sum fits. -/
theorem off_toNat {b : Word} {k : Nat} (h : b.toNat + (OfNat.ofNat k : Nat) < 2 ^ 64) :
    (b + (no_index (OfNat.ofNat k) : Word)).toNat = b.toNat + (OfNat.ofNat k : Nat) := by
  change b.toNat + k < 2 ^ 64 at h
  show (b + UInt64.ofNat k).toNat = b.toNat + k
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']; omega

/-- `omega` after the goal's literal offsets `(b + k).toNat` are rewritten to `b.toNat + k`
(`off_toNat`, each room bound discharged by `omega`). -/
macro "off_omega" : tactic => `(tactic| ((try simp (disch := omega) only [L.off_toNat]) <;> omega))

/-! ## Word arithmetic

The `toNat` of a word sum, successor or predecessor when it does not wrap, and a few word
identities. One copy each (lane dedup2); the binder kinds are those most callers used. -/

/-- A word plus a number, when the sum fits. -/
theorem toNat_add_ofNat_of_lt (w : Word) (k : Nat) (h : w.toNat + k < 2 ^ 64) :
    (w + UInt64.ofNat k).toNat = w.toNat + k := by
  rw [UInt64.toNat_add]; simp; omega

/-- A word sum, when it fits. -/
theorem toNat_add_of_lt (d k : Word) (h : d.toNat + k.toNat < 2 ^ 64) :
    (d + k).toNat = d.toNat + k.toNat := by
  rw [UInt64.toNat_add]; omega

/-- A word sum that does not wrap (the `x + y < x` overflow test failed). -/
theorem toNat_add_of_not_lt {x y : Word} (h : ¬ x + y < x) : (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
  have := y.toNat_lt; have := x.toNat_lt
  rw [UInt64.toNat_add]; omega

theorem toNat_add_one_of_lt {w : Word} (h : w.toNat + 1 < 2 ^ 64) : (w + 1).toNat = w.toNat + 1 := by
  rw [UInt64.toNat_add]; simp; omega

/-- The successor of a word below another word. -/
theorem toNat_add_one_of_word_lt (j l : Word) (h : j < l) : (j + 1).toNat = j.toNat + 1 := by
  have := UInt64.lt_iff_toNat_lt.mp h
  have := UInt64.toNat_lt l
  rw [UInt64.toNat_add]; simp; omega

theorem toNat_add_one_of_ne (x : Word) (h : x + 1 ≠ 0) : (x + 1).toNat = x.toNat + 1 := by
  have := x.toNat_lt
  rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]
  rw [Nat.mod_eq_of_lt]
  rcases Nat.lt_or_ge (x.toNat + 1) (2 ^ 64) with hl | hl
  · exact hl
  · exfalso; apply h; apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add]; simp only [UInt64.toNat_one, UInt64.toNat_zero]; omega

theorem toNat_ne_zero_of_ne (f : Word) (hf : f ≠ 0) : f.toNat ≠ 0 :=
  fun h => hf (UInt64.toNat_inj.mp (by simpa using h))

theorem toNat_sub_one_of_ne {w : Word} (h : w ≠ 0) : (w - 1).toNat = w.toNat - 1 := by
  have : w.toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.mp (by simpa using h0))
  have h1 : (1 : Word).toNat = 1 := by decide
  have : (1 : Word) ≤ w := UInt64.le_iff_toNat_le.mpr (by omega)
  rw [UInt64.toNat_sub_of_le _ _ this, h1]

/-- A nonzero counter is the successor of its decrement (the twin's `fuel + 1` clause). -/
theorem toNat_eq_toNat_sub_one_add_one (c : Word) (hc : c ≠ 0) : c.toNat = (c - 1).toNat + 1 := by
  have : c.toNat ≠ 0 := fun h => hc (UInt64.toNat_inj.mp (by simpa using h))
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega

/-- A nonzero word: its `toNat` is a successor, the predecessor's `toNat` that. -/
theorem exists_toNat_eq_succ {w : Word} (h : w ≠ 0) : ∃ k, w.toNat = k + 1 ∧ (w - 1).toNat = k := by
  have hpos : 1 ≤ w.toNat := by
    rcases Nat.eq_zero_or_pos w.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) h
    · omega
  refine ⟨w.toNat - 1, by omega, ?_⟩
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h

theorem ofNat_toNat (w : Word) : UInt64.ofNat w.toNat = w := by
  apply UInt64.toNat_inj.mp; simp

theorem toUInt64_toNat (w : Word) : w.toNat.toUInt64 = w := by
  simp [Nat.toUInt64]

theorem toNat_and_one_le (t : Word) : (t &&& 1).toNat ≤ 1 := by
  rw [UInt64.toNat_and]; exact Nat.le_trans Nat.and_le_right (by decide)

theorem eq_zero_or_eq_one_of_le_one (t : Word) (h : t ≤ 1) : t = 0 ∨ t = 1 := by
  have : t.toNat ≤ 1 := h
  rcases (show t.toNat = 0 ∨ t.toNat = 1 by omega) with h | h
  · exact .inl (UInt64.toNat_inj.mp h)
  · exact .inr (UInt64.toNat_inj.mp h)

theorem add_one_add_one (d : Word) : d + 1 + 1 = d + 2 := by rw [UInt64.add_assoc]; rfl

theorem add_toUInt64_succ (d : Word) (j : Nat) : d + (j + 1).toUInt64 = d + 1 + j.toUInt64 := by
  simp [Nat.toUInt64, UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm]

theorem decide_lt_eq_not_decide_le (x y : Word) : decide (x < y) = !decide (y ≤ x) := by
  by_cases h : y ≤ x
  · have : ¬ x < y := fun h' => absurd h (UInt64.not_le.mpr h')
    simp [h, this]
  · have : x < y := UInt64.not_le.mp h
    simp [h, this]

/-! ## A word list at a literal index

`r.getD k 0` as the `headD` after `k` tails (a return list's `k`-th word). -/

theorem getD_zero (r : List Word) : r.getD 0 0 = r.headD 0 := by cases r <;> rfl

theorem getD_one (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> rfl

theorem getD_two (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> rfl

theorem getD_three (r : List Word) : r.getD 3 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩ <;> rfl

theorem getD_four (r : List Word) : r.getD 4 0 = r.tail.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> rfl

theorem drop_three (r : List Word) : r.drop 3 = r.tail.tail.tail := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> simp

theorem headD_drop_three (r : List Word) : (r.drop 3).headD 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

end L
