module

public import ConAgua.Arena.SlotGrow
public import ConAgua.Arena.Pool
public import ConAgua.L.Logic
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# Packed 32-bit columns (lane p32)

A word array can hold 32-bit elements, two per word: L's `A⟨t⟩.u32[i]` (`Expr.ld32t`) reads
element `i`, `A⟨t⟩.u32[i] := e` (`Stmt.st32t`) writes the low 32 bits of `e` there, and
`len(A⟨t⟩) * 2` is the number of elements. In L's semantics element `i` is half `i % 2` of word
`i / 2` (`L.half32`, `L.Mem.set32`); the compiled code reads and writes it with one 4-byte move.

This file is what code above L sees of such a column, and all it sees: the element `p32Get a i`
of the column `a` (`0` past its end, as `rdW`), the store `Mem.set32`, and their equations
(`p32Get_set32`, the frame lemmas, `p32Get_lt`). Proofs about a packed column never mention
halves or words; the word layout is the business of the semantics and the compiler.

The specs for `vcgen` (`ld32_p32_spec`, `st32_p32_spec`) state a load as `p32Get` and a store as
`Mem.set32`, the way `ld64_rdW_spec` states a word load as `rdW`. The model generator
(`l_model`) renders `A⟨t⟩.u32[i]` as `p32Get` and the store as `Mem.set32`.
-/

open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **Element `i` of the packed column `a`**: half `i % 2` of word `i / 2`, `0` past the end. -/
def p32Get (a : Array Word) (i : Word) : Word := half32 (rdW a (i / 2)) i

/-- The number of elements of a packed column of `n` words. -/
def p32Len (n : Word) : Word := n * 2

theorem p32Get_toNat_lt (a : Array Word) (i : Word) : (p32Get a i).toNat < 4294967296 := by
  unfold p32Get
  have := (rdW a (i / 2)).toNat_lt
  rw [half32_toNat]; split <;> omega

/-- An element is below `2^32`. -/
theorem p32Get_lt (a : Array Word) (i : Word) : p32Get a i < 4294967296 := by
  have := p32Get_toNat_lt a i
  simp only [UInt64.lt_iff_toNat_lt]; exact this

/-- In bounds, an element read is the half of its word (the shape `L.ld32` unfolds to). -/
theorem p32Get_eq (a : Array Word) (i : Word) (k : Nat) (hk : k = (i / 2).toNat) (h : k < a.size) :
    half32 a[k] i = p32Get a i := by
  subst hk
  have h' : i.toNat / 2 < a.size := by simpa [UInt64.toNat_div] using h
  simp [p32Get, rdW, h']
grind_pattern [arena_grind] p32Get_eq => half32 a[k] i

/-- The words of a column other than `A` are unchanged by a store into `A`. -/
@[arena_grind =] theorem Mem.arr64_set32_ne (m : Mem) (A B : TieredArray) (i v : Word) (h : B ≠ A) :
    (m.set32 A i v).arr64 B = m.arr64 B := by
  simp [Mem.set32, Mem.arr64_set64_ne _ _ _ _ _ h]

/-- A store changes no array's size. -/
@[arena_grind =] theorem Mem.size_set32 (m : Mem) (A B : TieredArray) (i v : Word) :
    ((m.set32 A i v).arr64 B).size = (m.arr64 B).size := by
  simp only [Mem.set32, Mem.set64, Mem.arr64]
  split <;> simp_all

theorem half32_setHalf32 (w i j v : Word) :
    half32 (setHalf32 w i v) j = if i % 2 = j % 2 then v % 4294967296 else half32 w j := by
  apply UInt64.toNat_inj.mp
  have hw := w.toNat_lt
  have hv := v.toNat_lt
  have hij : (i % 2 = j % 2) ↔ i.toNat % 2 = j.toNat % 2 := by
    rw [← UInt64.toNat_inj]; simp
  rw [half32_toNat, setHalf32_toNat]
  by_cases h : i % 2 = j % 2
  · rw [ite_eq_left h]; have := hij.mp h
    simp only [UInt64.toNat_mod, show (4294967296 : Word).toNat = 4294967296 from rfl]
    repeat' split
    all_goals omega
  · rw [ite_eq_right h, half32_toNat]; have : ¬ (i.toNat % 2 = j.toNat % 2) := fun e => h (hij.mpr e)
    repeat' split
    all_goals omega

theorem rdW_set64_32 (m : Mem) (a : TieredArray) (k v x : Word) :
    rdW ((m.set64 a k v).arr64 a) x = if k = x ∧ k.toNat < (m.arr64 a).size then v else rdW (m.arr64 a) x := by
  rw [Mem.arr64_set64_same]
  simp only [rdW, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  grind

/-- **The column after a store**: element `k` of `A` is the low 32 bits of `v`, the others are as
before (no change out of bounds). -/
theorem p32Get_set32 (m : Mem) (A B : TieredArray) (k v x : Word) :
    p32Get ((m.set32 A k v).arr64 B) x =
      if B = A ∧ k = x ∧ (k / 2).toNat < (m.arr64 A).size then v % 4294967296
      else p32Get (m.arr64 B) x := by
  by_cases hB : B = A
  · subst A
    have hkx : k = x ↔ (k / 2 = x / 2 ∧ k % 2 = x % 2) := by
      simp only [← UInt64.toNat_inj, UInt64.toNat_div, UInt64.toNat_mod]
      have : (2 : Word).toNat = 2 := rfl
      constructor
      · intro h; rw [h]; exact ⟨rfl, rfl⟩
      · intro h; simp only [this] at h; omega
    simp only [p32Get, Mem.set32, rdW_set64_32, true_and]
    by_cases h1 : k / 2 = x / 2 ∧ (k / 2).toNat < (m.arr64 B).size
    · rw [ite_eq_left h1, half32_setHalf32]
      by_cases h2 : k % 2 = x % 2
      · rw [ite_eq_left h2, ite_eq_left ⟨hkx.mpr ⟨h1.1, h2⟩, h1.2⟩]
      · rw [ite_eq_right h2, ite_eq_right (fun h => h2 (hkx.mp h.1).2)]
        congr 1
        rw [← h1.1]
        have h3 : k.toNat / 2 < (m.arr64 B).size := by simpa [UInt64.toNat_div] using h1.2
        simp [rdW, Array.getD, h3]
    · rw [ite_eq_right h1, ite_eq_right (fun h => h1 ⟨(hkx.mp h.1).1, h.2⟩)]
  · rw [Mem.arr64_set32_ne _ _ _ _ _ hB]; simp [hB]

/-! ## Loads for `vcgen` -/

/-- **A 32-bit load as `p32Get`** (the form `vcgen`'s own unfolding of `L.ld32` does not give:
it leaves the read under the bound hypothesis). -/
theorem ld32_p32_spec (a : TieredArray) (i : Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ ld32 a i
    ⦃fun r s' => s' = s₀ ∧ r = p32Get (s₀.mem.arr64 a) i ∧ (i / 2).toNat < (s₀.mem.arr64 a).size; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs hrun
  subst hs
  simp only [ld32, StateT.run_bind, StateT.run_get, pure_bind] at hrun
  split at hrun
  · rename_i h
    simp only [pure] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨rfl, p32Get_eq _ _ _ rfl h, h⟩
  · simp [throw, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift] at hrun
    cases hrun

end L.Arena
