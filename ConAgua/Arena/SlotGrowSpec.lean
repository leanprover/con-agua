module

public import ConAgua.Arena.SlotGrow
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# The cons tables' slot layout and growth: the models (lane kstp)

`ConsLib.lean`'s slot array (KSTP): words `2 t`, `2 t + 1` hold tier `t`'s slot count less `SN0`
and its table's offset; tier 0's table starts at word `4 + o_0`, tier 1's ends at word
`len - o_1`; slot `j` is the value word `r_t + 2 j` and the key word after it. This file has the
layout's reads (`knW`, `koW`, `krW`) and the models of the growth block `kgrowB` (`kgrowM`): each
loop a function of the memory and its variables that returns `none` where the L code aborts.
`G m q` stands for the hash the growth computes from a key word `q` (`ConsLibSpec.lean`'s `ghC`).

The table relation's side (the growth re-registers every live slot, so every node is found again)
is `StoreLib.lean`'s `storeR_kgrow`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The layout -/

/-- The slot count of tier `t` of the table with slot array `sa`: its count word plus `SN0`. -/
def knW (sa : ArrId) (m : Mem) (t : Word) : Word := rdW (m.arr64 sa) (t * 2) + SN0

/-- The offset of tier `t`'s table. -/
def koW (sa : ArrId) (m : Mem) (t : Word) : Word := rdW (m.arr64 sa) (t * 2 + 1)

/-- The first word of tier `t`'s table: `4 + o` (tier 0), `len - o - 2 n` (tier 1). -/
def krW (sa : ArrId) (m : Mem) (t : Word) : Word :=
  if t = 0 then koW sa m t + 4 else m.len64 sa - koW sa m t - knW sa m t * 2

/-! ## The growth's loops -/

/-- The growth's probe: from slot `j` (of `n`, the table at word `nb`) after `d` steps, the first
slot whose value word is `0` (`none`: the abort after `n` steps). -/
def kprobeW (sl : Array Word) (nb n j d : Word) : Option Word :=
  if rdW sl (nb + j * 2) = 0 then some j
  else if n ≤ d then none
  else kprobeW sl nb n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by
    have := ‹¬ n ≤ d›; simp only [UInt64.le_iff_toNat_le] at this; omega
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  omega

/-- Eight zero words of `sa` from `k`. -/
def zero8 (sa : ArrId) (k : Word) (m : Mem) : Mem :=
  (((((((m.set64 sa k 0).set64 sa (k + 1) 0).set64 sa (k + 2) 0).set64 sa (k + 3) 0).set64 sa
    (k + 4) 0).set64 sa (k + 5) 0).set64 sa (k + 6) 0).set64 sa (k + 7) 0

/-- The zero loop: `e` steps of eight zero words from `x`. -/
def kzeroW (sa : ArrId) : Word → Nat → Mem → Mem
  | _, 0, m => m
  | x, e + 1, m => kzeroW sa (x + 8) e (zero8 sa x m)

/-- The walk: `e` slots of the old table from word `x`; each live one (value word above `bt`) is
written, with its key word, to the first free slot of the new table (`n` slots at word `nb`)
from the home of `G` of its key word. -/
def kwalkW (sa : ArrId) (G : Mem → Word → Word) (n nb bt : Word) : Nat → Word → Mem → Option Mem
  | 0, _, m => some m
  | e + 1, x, m =>
    if bt < rdW (m.arr64 sa) x then
      match kprobeW (m.arr64 sa) nb n (homeW (G m (rdW (m.arr64 sa) (x + 1))) n) 0 with
      | none => none
      | some j => kwalkW sa G n nb bt e (x + 2)
          ((m.set64 sa (nb + j * 2) (rdW (m.arr64 sa) x)).set64 sa (nb + j * 2 + 1)
            (rdW (m.arr64 sa) (x + 1)))
    else kwalkW sa G n nb bt e (x + 2) m

/-- **The growth of tier `t`** (`kgrowB`): the memory after it, `none` where it aborts. -/
def kgrowM (sa : ArrId) (G : Mem → Word → Word) (t : Word) (m : Mem) : Option Mem :=
  let nb := if koW sa m t = 0 then knW sa m t * 2 * 4 else 0
  if (if t = 0 then (m.len64 sa >>> 1) - 4 else m.len64 sa - (m.len64 sa >>> 1)) <
      nb + knW sa m t * 2 * 2
  then none
  else
    kwalkW sa G (knW sa m t * 2)
      (if t = 0 then nb + 4 else m.len64 sa - nb - knW sa m t * 2 * 2)
      (rdW (m.arr64 CTL) SCB * t) (knW sa m t).toNat
      (if t = 0 then koW sa m t + 4 else m.len64 sa - koW sa m t - knW sa m t * 2)
      (kzeroW sa (if t = 0 then nb + 4 else m.len64 sa - nb - knW sa m t * 2 * 2)
        (knW sa m t >>> 1).toNat
        ((m.set64 sa (t * 2) (knW sa m t * 2 - SN0)).set64 sa (t * 2 + 1) nb))

/-! ## The frame of the growth -/

/-- From `m` to `m'` only array `sa` changes, and no size. -/
def GFr (sa : ArrId) (m m' : Mem) : Prop :=
  (∀ b, b ≠ sa → m'.arr64 b = m.arr64 b) ∧ (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧
    m'.words.size = m.words.size

theorem GFr.refl (sa : ArrId) (m : Mem) : GFr sa m m := ⟨fun _ _ => rfl, fun _ => rfl, rfl⟩

theorem GFr.trans {sa : ArrId} {m₁ m₂ m₃ : Mem} (h₁ : GFr sa m₁ m₂) (h₂ : GFr sa m₂ m₃) :
    GFr sa m₁ m₃ :=
  ⟨fun b hb => (h₂.1 b hb).trans (h₁.1 b hb), fun b => (h₂.2.1 b).trans (h₁.2.1 b),
    h₂.2.2.trans h₁.2.2⟩

theorem GFr.set64 (sa : ArrId) (m : Mem) (i v : Word) : GFr sa m (m.set64 sa i v) := by
  refine ⟨fun b hb => Mem.arr64_set64_ne _ _ _ _ _ hb, fun b => ?_, Mem.words_size_set64 _ _ _ _⟩
  by_cases h : b = sa
  · subst h; exact Mem.size_arr64_set64 _ _ _ _
  · rw [Mem.arr64_set64_ne _ _ _ _ _ h]

theorem GFr.zero8 (sa : ArrId) (k : Word) (m : Mem) : GFr sa m (zero8 sa k m) := by
  unfold L.Arena.zero8
  exact ((((((GFr.set64 _ _ _ _).trans (GFr.set64 _ _ _ _)).trans (GFr.set64 _ _ _ _)).trans
    (GFr.set64 _ _ _ _)).trans (GFr.set64 _ _ _ _)).trans (GFr.set64 _ _ _ _)).trans
    (GFr.set64 _ _ _ _) |>.trans (GFr.set64 _ _ _ _)

theorem kzeroW_fr (sa : ArrId) : ∀ (e : Nat) (x : Word) (m : Mem), GFr sa m (kzeroW sa x e m)
  | 0, _, m => GFr.refl _ m
  | e + 1, x, m => (GFr.zero8 sa x m).trans (kzeroW_fr sa e (x + 8) _)

theorem kwalkW_fr (sa : ArrId) (G : Mem → Word → Word) (n nb bt : Word) :
    ∀ (e : Nat) (x : Word) (m m' : Mem), kwalkW sa G n nb bt e x m = some m' → GFr sa m m'
  | 0, _, m, m', h => by simp only [kwalkW, Option.some.injEq] at h; subst h; exact GFr.refl _ _
  | e + 1, x, m, m', h => by
    simp only [kwalkW] at h
    split at h
    · split at h
      · cases h
      · exact ((GFr.set64 _ _ _ _).trans (GFr.set64 _ _ _ _)).trans (kwalkW_fr sa G n nb bt e _ _ _ h)
    · exact kwalkW_fr sa G n nb bt e _ _ _ h

/-- **The growth writes only the slot array** (and keeps every size). -/
theorem ite_none_some {α : Type} {c : Prop} [Decidable c] {x : Option α} {y : α}
    (h : (if c then none else x) = some y) : x = some y := by
  by_cases hc : c <;> simp_all

theorem kgrowM_fr (sa : ArrId) (G : Mem → Word → Word) (t : Word) (m m' : Mem)
    (h : kgrowM sa G t m = some m') : GFr sa m m' := by
  simp only [kgrowM] at h
  exact (((GFr.set64 _ _ _ _).trans (GFr.set64 _ _ _ _)).trans (kzeroW_fr _ _ _ _)).trans
    (kwalkW_fr _ _ _ _ _ _ _ _ _ (ite_none_some h))

/-- Word stores to two different arrays commute. -/
theorem Mem.set64_comm (m : Mem) (a b : ArrId) (i j v w : Word) (h : a ≠ b) :
    (m.set64 a i v).set64 b j w = (m.set64 b j w).set64 a i v := by
  have e1 : (m.set64 a i v).arr64 b = m.arr64 b := Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h)
  have e2 : (m.set64 b j w).arr64 a = m.arr64 a := Mem.arr64_set64_ne _ _ _ _ _ h
  simp only [Mem.set64] at *
  rw [e1, e2]
  congr 1
  apply Array.ext_getElem?
  intro n
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  grind

/-- A word array after a store, for any array. -/
theorem arr64_set64_any (m : Mem) (a a' : ArrId) (i v : Word) :
    (m.set64 a i v).arr64 a' = if a = a' then (m.arr64 a).set! i.toNat v else m.arr64 a' := by
  simp only [Mem.set64, Mem.arr64]
  by_cases h : a = a'
  · subst h; simp [Array.getD]
    intro h1 h2; omega
  · simp [h, Array.getD]
    split
    · rw [Array.getElem_setIfInBounds_ne]; omega
    · rfl

/-- The variables below `o` are kept. -/
def KeepLo (o : Nat) (s s' : St) : Prop := ∀ x, x < o → s'.loc x = s.loc x

theorem KeepLo.loc {o : Nat} {s s' : St} (h : KeepLo o s s') (x : Var) (hx : x < o) :
    s'.loc x = s.loc x := h x hx

grind_pattern [lang_grind] KeepLo.loc => KeepLo o s s', s'.loc x

/-- Every local but `x` and `y` is kept. -/
def Keep2 (x y : Var) (s s' : St) : Prop := ∀ z, z ≠ x → z ≠ y → s'.loc z = s.loc z

theorem Keep2.loc {x y : Var} {s s' : St} (h : Keep2 x y s s') (z : Var) (hx : z ≠ x) (hy : z ≠ y) :
    s'.loc z = s.loc z := h z hx hy

grind_pattern [lang_grind] Keep2.loc => Keep2 x y s s', s'.loc z

end L.Arena
