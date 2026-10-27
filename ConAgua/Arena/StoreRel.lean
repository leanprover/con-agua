import ConAgua.Arena.Refine
import ConAgua.Arena.SlotGrow
import ConAgua.Arena.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# What the store relations share

The facts the `lit` and `app` store relations (`LitRefine.lean`, `AppRefine.lean`) both use,
none of them about a particular record: reads after a write, the probe run of the open-addressing
tables, handle words, the arena's `Tbl.push`.
-/

open ConRon.Arena

namespace L.Arena

/-! ## Store reads: one equation per write

Every fact about the memory after an append follows from these: a read of a word array after
`set64` is the written word or the old read. -/

theorem rdW_set! (a : Array Word) (k : Nat) (v x : Word) :
    rdW (a.set! k v) x = if k = x.toNat ∧ k < a.size then v else rdW a x := by
  simp only [rdW, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  grind

theorem rdW_set64 (m : Mem) (a b : ArrId) (k v x : Word) :
    rdW ((m.set64 a k v).arr64 b) x =
      if b = a ∧ k = x ∧ k.toNat < (m.arr64 a).size then v else rdW (m.arr64 b) x := by
  by_cases h : b = a
  · subst h; rw [Mem.arr64_set64_same, rdW_set!]; grind
  · rw [Mem.arr64_set64_ne _ _ _ _ _ h]; simp [h]

theorem size_set64 (m : Mem) (a b : ArrId) (k v : Word) :
    ((m.set64 a k v).arr64 b).size = (m.arr64 b).size := by
  by_cases h : b = a
  · subst h; rw [Mem.arr64_set64_same]; simp
  · rw [Mem.arr64_set64_ne _ _ _ _ _ h]

theorem top_rdW (m : Mem) : m.top = rdW (m.arr64 CTL) 0 := rfl

theorem len64_eq (m : Mem) (a : ArrId) : m.len64 a = UInt64.ofNat (m.arr64 a).size := rfl

attribute [store_grind =] rdW_set64 size_set64 top_rdW Mem.words_size_set64 len64_eq

/-! ## The probe run -/

/-- Slot `e` of the probe run from slot `x` among `n` slots (the probe's step, `e` times). -/
def walkW (n x : Word) : Nat → Word
  | 0 => x
  | e + 1 => (walkW n x e + 1) * (if walkW n x e + 1 < n then 1 else 0)

theorem walkW_succ (n x : Word) (e : Nat) :
    walkW n x (e + 1) = (walkW n x e + 1) * (if walkW n x e + 1 < n then 1 else 0) := rfl

theorem walkW_lt (n x : Word) (e : Nat) (hx : x < n) : walkW n x e < n := by
  induction e with
  | zero => exact hx
  | succ e ih => rw [walkW_succ]; grind
grind_pattern [store_grind] walkW_lt => walkW n x e

theorem homeW_lt (h n : Word) (hn : 0 < n) : homeW h n < n := by
  simp only [homeW]
  have hx := ((h * golden) ^^^ ((h * golden) >>> 32)).toNat_lt
  have hn' := n.toNat_lt
  have : ((h * golden) ^^^ ((h * golden) >>> 32)).toNat * n.toNat / 2 ^ 64 < n.toNat :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right hx (by grind))
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact this
grind_pattern [store_grind] homeW_lt => homeW h n


/-! ## Handles -/

/-- The handle word of node `i` of tier `t` of the constructor with tag `g`. -/
def hdW (g t i : Word) : Word := g * 0x10000000 + t * 0x8000000 + i

/-- The handle of any kind a word encodes (`decE` at expressions). -/
def decI {k : IdxKind} (w : Word) : Idx k := Idx.ofWord w.toUInt32

theorem decE_eq (w : Word) : decE w = decI w := rfl

/-- The index of a handle, as a word. -/
def hix {k : IdxKind} (x : Idx k) : Word := UInt64.ofNat x.idxNat

theorem hix_hdW {k : IdxKind} (g t i : Word) (hi : i.toNat < 2 ^ 27) :
    hix (decI (hdW g t i) : Idx k) = i := by
  simp only [hix, decI, hdW, Idx.idxNat, Idx.index]
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofNat', UInt32.toNat_mod, UInt64.toNat_toUInt32, UInt64.toNat_add,
    UInt64.toNat_mul]
  grind
grind_pattern [store_grind] hix_hdW => hix (decI (hdW g t i) : Idx k)

/-- The arena's handle of node `n` of tier `b` is the L handle word. -/
theorem mk_eq {k : IdxKind} (g : UInt32) (b n : Nat) :
    (Idx.mk g (UInt32.ofNat b) (UInt32.ofNat n) : Idx k) =
      decI (hdW g.toUInt64 (UInt64.ofNat b) (UInt64.ofNat n)) := by
  simp only [decI, hdW, Idx.mk]
  congr 1
  apply UInt32.toNat_inj.mp
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat',
    UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_toUInt64]
  simp only [show (268435456 : UInt32).toNat = 268435456 from rfl,
    show (134217728 : UInt32).toNat = 134217728 from rfl,
    show (0x10000000 : UInt64).toNat = 268435456 from rfl,
    show (0x8000000 : UInt64).toNat = 134217728 from rfl]
  omega

/-- Bit 27 of a word (the tier bit of a handle word). -/
theorem bit27_toNat (w : Word) : ((w >>> 27) &&& 1).toNat = w.toNat / 2 ^ 27 % 2 := by
  simp [UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

theorem bit27_or (f a : Word) :
    (((f ||| a) >>> 27) &&& 1 = 0) ↔ ((f >>> 27) &&& 1 = 0 ∧ (a >>> 27) &&& 1 = 0) := by
  have h : ∀ x : Word, ((x >>> 27) &&& 1 = 0) ↔ x.toNat.testBit 27 = false := by
    intro x
    rw [← UInt64.toNat_inj, bit27_toNat, Nat.testBit_eq_decide_div_mod_eq]
    simp
  rw [h, h, h, UInt64.toNat_or, Nat.testBit_or]; simp

/-- The tier bit of a handle word, at any handle kind (a `sort`/`const`/`letE` child may be a
level, name or level-list handle, not only an expression one). -/
theorem isPersistent_decI {k : IdxKind} (w : Word) (hw : w.toNat < 2 ^ 32) :
    (decI w : Idx k).isPersistent = ((w >>> 27) &&& 1 == 0) := by
  simp only [decI, Idx.isPersistent, Idx.tier]
  have := bit27_toNat w
  have : (w.toUInt32 / 134217728 % 2).toNat = w.toNat / 2 ^ 27 % 2 := by
    simp [UInt32.toNat_mod, UInt32.toNat_div, UInt64.toNat_toUInt32]; omega
  grind

/-- The tier bit of a handle word, at expression handles (`isPersistent_decI` specialised, as
`app`'s skip test uses it). -/
theorem isPersistent_decE (w : Word) (hw : w.toNat < 2 ^ 32) :
    (decE w).isPersistent = ((w >>> 27) &&& 1 == 0) := by
  rw [decE_eq]; exact isPersistent_decI w hw

/-- A handle is the decoding of a word below `2^32` iff that word is the handle's. -/
theorem word_decI {k : IdxKind} (x : Idx k) (w : Word) (hw : w.toNat < 2 ^ 32) :
    (x.word.toUInt64 = w) = (x = decI w) := by
  cases x with | ofWord u =>
  simp only [decI, Idx.ofWord.injEq, eq_iff_iff]
  constructor
  · intro h; subst h; apply UInt32.toNat_inj.mp; simp
  · intro h; subst h; apply UInt64.toNat_inj.mp; simp; omega

/-! ## The arena side -/

theorem AM.of_run_ok {α : Type} [Inhabited α] (x : AM α) (a a' : AState) (v : α)
    (h : x.run a = .ok (v, a')) : AM.ok x a ∧ AM.st x a = a' ∧ AM.res x a = v := by
  simp [AM.ok, AM.st, AM.res, h]

section tbl
variable {α ι δ : Type} [BEq α] [Hashable α]

theorem Tbl.push_nodes (tb : Tbl α ι δ) (a : α) (d : δ) (i : ι) :
    (tb.push a d i).nodes = tb.nodes.push a := by cases tb; rfl

theorem Tbl.push_cons (tb : Tbl α ι δ) (a : α) (d : δ) (i : ι) :
    (tb.push a d i).cons = tb.cons.insert a i := by cases tb; rfl

end tbl

end L.Arena
