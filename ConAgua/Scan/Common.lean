module

public import ConAgua.L.Semantics
import ConAgua.L.GrindAttr
import ConAgua.L.Logic

@[expose] public section

/-!
# Shared facts for the Stage B validator (`ConAgua/Scan/{Str,Values,Member,Records,Line}.lean`)

The validator's models compute with words, as the L code does: a position is a `Word`, compared
with `UInt64.ofNat b.size` (what `len(IN.u8)` evaluates to), and a validator returns the
position after what it read, `0` for failure (no success position is `0`).
-/

namespace L.Scan

/-- A word below `UInt64.ofNat n` is below `n`: a position the L code has compared with
`len(IN.u8)` is inside the array. -/
theorem lt_of_lt_ofNat {j : Word} {n : Nat} (h : j < UInt64.ofNat n) : j.toNat < n := by
  rw [UInt64.lt_iff_toNat_lt] at h
  have := UInt64.toNat_ofNat_le (n := n)
  omega

/-- Stepping a position below `UInt64.ofNat n` does not wrap. -/
theorem toNat_add_one_of_lt_ofNat {j : Word} {n : Nat} (h : j < UInt64.ofNat n) :
    (j + 1).toNat = j.toNat + 1 := by
  rw [UInt64.lt_iff_toNat_lt] at h
  have := (UInt64.ofNat n).toNat_lt
  rw [UInt64.toNat_add]; simp; omega

/-- Setting locals leaves the memory alone (one equation instead of a chain through
`St.setLocs_cons`, which for a call with five results runs into `grind`'s generation limit). -/
@[lang_grind =] theorem St.setLocs_mem (s : St) (xs : List Var) (vs : List Word) :
    (s.setLocs xs vs).mem = s.mem := by
  induction xs generalizing s vs with
  | nil => rfl
  | cons x xs ih => rw [St.setLocs_cons, ih]; rfl

end L.Scan
