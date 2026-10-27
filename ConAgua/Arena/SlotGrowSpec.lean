module

public import ConAgua.Arena.SlotGrow
public import ConAgua.L.Logic
import ConAgua.L.GrindAttr

@[expose] public section

/-!
# The cons tables' slot layout and growth: the models (lane kstp)

`ConsLib.lean`'s slot arrays (KSTP on tiered arrays, lane tierswitch): tier `t`'s own array
`tierA sa t` holds its slot count less `SN0` in word `0`, its table's offset `o` in word `1`, and
the table from word `2 + o`; slot `j` is the value word `r + 2 j` and the key word after it. This file has the
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

/-- The slot count of tier `t` of the table with slot array `sa` (tier `t`'s own array
`tierA sa t`): its word `0` plus `SN0`. -/
def knW (sa : ArrId) (m : Mem) (t : Word) : Word := rdW (m.arr64 (tierA sa t)) 0 + SN0

/-- The offset of tier `t`'s table: word `1` of its array. -/
def koW (sa : ArrId) (m : Mem) (t : Word) : Word := rdW (m.arr64 (tierA sa t)) 1

/-- The first word of tier `t`'s table: `2 + o`. -/
def krW (sa : ArrId) (m : Mem) (t : Word) : Word := koW sa m t + 2

/-! ## The growth's loops -/

/-- Eight zero words of `sa` from `k`. -/
def zero8 (sa : ArrId) (k : Word) (m : Mem) : Mem :=
  (((((((m.set64 sa k 0).set64 sa (k + 1) 0).set64 sa (k + 2) 0).set64 sa (k + 3) 0).set64 sa
    (k + 4) 0).set64 sa (k + 5) 0).set64 sa (k + 6) 0).set64 sa (k + 7) 0

/-- The zero loop: `e` steps of eight zero words from `x`. -/
def kzeroW (sa : ArrId) : Word → Nat → Mem → Mem
  | _, 0, m => m
  | x, e + 1, m => kzeroW sa (x + 8) e (zero8 sa x m)

/-- The mark loop: `e` slots from word `x`; a live one (value word above `bt`) gets `MARK`. -/
def kmarkW (sa : ArrId) (bt : Word) : Nat → Word → Mem → Mem
  | 0, _, m => m
  | e + 1, x, m => kmarkW sa bt e (x + 2)
      (if bt < rdW (m.arr64 sa) x then m.set64 sa x (rdW (m.arr64 sa) x + MARK) else m)

/-- The probe of the re-insertion of slot `i`'s entry (`N` slots from word `ob`): from slot `j`
after `d` steps, past the live unmarked slots, the first slot that is `i`, free or marked
(`none`: the abort after `N` steps). -/
def kprobeW (sl : Array Word) (ob N i bt j d : Word) : Option Word :=
  if j ≠ i ∧ bt < rdW sl (ob + j * 2) ∧ rdW sl (ob + j * 2) < MARK then
    if N ≤ d then none
    else kprobeW sl ob N i bt ((j + 1) * (if j + 1 < N then 1 else 0)) (d + 1)
  else some j
termination_by N.toNat - d.toNat
decreasing_by
  have : d.toNat < N.toNat := by
    have := ‹¬ N ≤ d›; simp only [UInt64.le_iff_toNat_le] at this; omega
  have := N.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  omega

/-- The placement of slot `i`'s entry (value word `v`, key word `q`, unmarked) at slot `j`
(`kplaceB`): the memory and the next value word to re-insert (`0`: none). -/
def kplaceW (sa : ArrId) (ob i j v q : Word) (m : Mem) : Mem × Word :=
  if j = i then (m.set64 sa (ob + i * 2) v, 0)
  else if MARK ≤ rdW (m.arr64 sa) (ob + j * 2) then
    ((((m.set64 sa (ob + j * 2) v).set64 sa (ob + j * 2 + 1) q).set64 sa (ob + i * 2)
      (rdW (m.arr64 sa) (ob + j * 2))).set64 sa (ob + i * 2 + 1) (rdW (m.arr64 sa) (ob + j * 2 + 1)),
      rdW (m.arr64 sa) (ob + j * 2))
  else
    (((m.set64 sa (ob + j * 2) v).set64 sa (ob + j * 2 + 1) q).set64 sa (ob + i * 2) 0, 0)

/-- The re-insertions at slot `i` (`kinnerL`): while the value word `v` is marked, spend one of
the budget `e`, probe from the home of `G` of slot `i`'s key word, place. The memory and the
budget left; `none` where L aborts. -/
def kinnerW (sa : ArrId) (G : Mem → Word → Word) (N ob bt i : Word) (e v : Word) (m : Mem) :
    Option (Mem × Word) :=
  if MARK ≤ v then
    if e = 0 then none
    else
      match kprobeW (m.arr64 sa) ob N i bt
          (homeW (G m (rdW (m.arr64 sa) (ob + i * 2 + 1))) N) 0 with
      | none => none
      | some j =>
        kinnerW sa G N ob bt i (e - 1)
          (kplaceW sa ob i j (v - MARK) (rdW (m.arr64 sa) (ob + i * 2 + 1)) m).2
          (kplaceW sa ob i j (v - MARK) (rdW (m.arr64 sa) (ob + i * 2 + 1)) m).1
  else some (m, e)
termination_by e.toNat
decreasing_by
  have : e.toNat ≠ 0 := fun h => ‹¬ e = 0› (UInt64.toNat_inj.mp (by simpa using h))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

/-- The re-insertion loop (`krehashL`): slots `i ‥ n - 1` of the old half, the budget `e`. -/
def krehashW (sa : ArrId) (G : Mem → Word → Word) (N n ob bt i e : Word) (m : Mem) : Option Mem :=
  if i < n then
    match kinnerW sa G N ob bt i e (rdW (m.arr64 sa) (ob + i * 2)) m with
    | none => none
    | some (m', e') => krehashW sa G N n ob bt (i + 1) e' m'
  else some m
termination_by n.toNat - i.toNat
decreasing_by
  have : i.toNat < n.toNat := UInt64.lt_iff_toNat_lt.mp ‹i < n›
  have := n.toNat_lt
  have : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  omega

/-- **The growth of tier `t`** (`kgrowB`, in place): the memory after it, `none` where it
aborts. The table (`n` slots from word `ob = o + 2`) doubles where it is: the count word, the
upper half zeroed (`2 n` words from `ob + 2 n`), the old half's live slots marked, the marked
entries re-inserted. -/
def kgrowM (sa : ArrId) (G : Mem → Word → Word) (t : Word) (m : Mem) : Option Mem :=
  if m.len64 (tierA sa t) - 2 < koW sa m t + knW sa m t * 2 * 2 then none
  else
    krehashW (tierA sa t) G (knW sa m t * 2) (knW sa m t) (koW sa m t + 2)
      (rdW (m.arr64 CTL) SCB * t) 0 (knW sa m t)
      (kmarkW (tierA sa t) (rdW (m.arr64 CTL) SCB * t) (knW sa m t).toNat (koW sa m t + 2)
        (kzeroW (tierA sa t) (koW sa m t + 2 + knW sa m t * 2) (knW sa m t >>> 2).toNat
          (m.set64 (tierA sa t) 0 (knW sa m t * 2 - SN0))))

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

theorem kmarkW_fr (sa : ArrId) (bt : Word) :
    ∀ (e : Nat) (x : Word) (m : Mem), GFr sa m (kmarkW sa bt e x m)
  | 0, _, m => GFr.refl _ m
  | e + 1, x, m => by
    simp only [kmarkW]
    split
    · exact (GFr.set64 _ _ _ _).trans (kmarkW_fr sa bt e _ _)
    · exact kmarkW_fr sa bt e _ _

theorem kplaceW_fr (sa : ArrId) (ob i j v q : Word) (m : Mem) : GFr sa m (kplaceW sa ob i j v q m).1 := by
  unfold kplaceW
  split
  · exact GFr.set64 _ _ _ _
  split
  · exact (((GFr.set64 _ _ _ _).trans (GFr.set64 _ _ _ _)).trans (GFr.set64 _ _ _ _)).trans
      (GFr.set64 _ _ _ _)
  · exact ((GFr.set64 _ _ _ _).trans (GFr.set64 _ _ _ _)).trans (GFr.set64 _ _ _ _)

theorem kinnerW_fr (sa : ArrId) (G : Mem → Word → Word) (N ob bt i e v : Word) (m m' : Mem)
    (e' : Word) (h : kinnerW sa G N ob bt i e v m = some (m', e')) : GFr sa m m' := by
  fun_induction kinnerW sa G N ob bt i e v m generalizing m' e' with
  | case1 => simp_all
  | case2 => simp_all
  | case3 e v m hv he j hj ih =>
    exact (kplaceW_fr _ _ _ _ _ _ _).trans (ih m' e' h)
  | case4 => obtain ⟨rfl, rfl⟩ := (by simpa using h : _ ∧ _); exact GFr.refl _ _

/-- **The growth writes only the slot array** (and keeps every size). -/
theorem ite_none_some {α : Type} {c : Prop} [Decidable c] {x : Option α} {y : α}
    (h : (if c then none else x) = some y) : x = some y := by
  by_cases hc : c <;> simp_all

theorem krehashW_fr (sa : ArrId) (G : Mem → Word → Word) (N n ob bt i e : Word) (m m' : Mem)
    (h : krehashW sa G N n ob bt i e m = some m') : GFr sa m m' := by
  fun_induction krehashW sa G N n ob bt i e m generalizing m' with
  | case1 => simp_all
  | case2 i e m hi m1 e1 h1 ih =>
    exact (kinnerW_fr _ _ _ _ _ _ _ _ _ _ _ h1).trans (ih m' h)
  | case3 => simp at h; subst h; exact GFr.refl _ _

theorem kgrowM_fr (sa : ArrId) (G : Mem → Word → Word) (t : Word) (m m' : Mem)
    (h : kgrowM sa G t m = some m') : GFr (tierA sa t) m m' := by
  simp only [kgrowM] at h
  exact (((GFr.set64 _ _ _ _).trans (kzeroW_fr _ _ _ _)).trans (kmarkW_fr _ _ _ _ _)).trans
    (krehashW_fr _ _ _ _ _ _ _ _ _ _ (ite_none_some h))

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
