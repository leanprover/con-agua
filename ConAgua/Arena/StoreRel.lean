import ConAgua.Arena.Refine
import ConAgua.Arena.Handle
import ConAgua.Arena.SlotGrow
import ConAgua.Arena.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# What the store relations share

The facts the `lit` and `app` store relations (`LitRefine.lean`, `AppRefine.lean`) both use,
none of them about a particular record: reads after a write, the probe run of the open-addressing
tables, the arena's `Tbl.push`.
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

theorem rdW_set64 (m : Mem) (a b : TieredArray) (k v x : Word) :
    rdW ((m.set64 a k v).arr64 b) x =
      if b = a ∧ k = x ∧ k.toNat < (m.arr64 a).size then v else rdW (m.arr64 b) x := by
  by_cases h : b = a
  · subst h; rw [Mem.arr64_set64_same, rdW_set!]; grind
  · rw [Mem.arr64_set64_ne _ _ _ _ _ h]; simp [h]

theorem size_set64 (m : Mem) (a b : TieredArray) (k v : Word) :
    ((m.set64 a k v).arr64 b).size = (m.arr64 b).size := by
  by_cases h : b = a
  · subst h; rw [Mem.arr64_set64_same]; simp
  · rw [Mem.arr64_set64_ne _ _ _ _ _ h]

theorem top_rdW (m : Mem) : m.top = rdW (m.arr64 CTL) 0 := rfl

theorem len64_eq (m : Mem) (a : TieredArray) : m.len64 a = UInt64.ofNat (m.arr64 a).size := rfl

attribute [store_grind =] rdW_set64 size_set64 top_rdW len64_eq

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
