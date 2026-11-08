module

meta import ConAgua.L.Semantics
public import ConAgua.Arena.SlotGrow
public import ConAgua.L.Logic
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# The cons tables' slot layout and growth: the models (lane kstp)

`ConsLib.lean`'s slot arrays (KSTP on tiered arrays, lane tierswitch): tier `t`'s own array
`tierA sa t` holds its slot count less `SN0` in word `0`, its table's offset `o` in word `1`, and
the table from word `2 + o`; slot `j` is word `r + j`, its value (`vwd`, the low 48 bits) and the
key's fragment (`kwd`, the top 16; `pk` packs them). This file has the layout's reads (`knW`,
`koW`, `krW`) and the models of the growth block `kgrowB` (`kgrowM`): each loop a function of the
memory and its variables that returns `none` where the L code aborts. `G m i` stands for the hash
the growth computes for node `i` (the value `bt + i + 1`; from the node's record,
`ConsLibSpecBase.lean`'s `ghC`).

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

/-! ## Slot words -/

/-- The value of slot word `x` of `sl`: its low 48 bits. -/
def vwd (sl : Array Word) (x : Word) : Word := rdW sl x &&& VMASK

/-- The fragment of slot word `x` of `sl`: its top 16 bits. -/
def kwd (sl : Array Word) (x : Word) : Word := rdW sl x >>> 48

/-- A slot word: the value `v` (below `2^48`) and the fragment `q` (below `2^16`). -/
def pk (v q : Word) : Word := v ||| q <<< 48

/-! ## The growth's loops -/

/-- Eight zero words of `sa` from `k`. -/
def zero8 (sa : TieredArray) (k : Word) (m : Mem) : Mem :=
  (((((((m.set64 sa k 0).set64 sa (k + 1) 0).set64 sa (k + 2) 0).set64 sa (k + 3) 0).set64 sa
    (k + 4) 0).set64 sa (k + 5) 0).set64 sa (k + 6) 0).set64 sa (k + 7) 0

/-- The zero loop: `e` steps of eight zero words from `x`. -/
def kzeroW (sa : TieredArray) : Word → Nat → Mem → Mem
  | _, 0, m => m
  | x, e + 1, m => kzeroW sa (x + 8) e (zero8 sa x m)

/-- The two mark ranges of the sweep, `[a0, a1)` and `[b0, b1)`. -/
structure MkR where
  a0 : Word
  a1 : Word
  b0 : Word
  b1 : Word

/-- A deferred entry at slot `i` joins a range (`kdefB`): the first below `n / 2`, the second
from it on. -/
def kdefR (n i : Word) (k : MkR) : MkR :=
  if i * 2 < n then { k with a1 := if k.a1 = 0 then i + 1 else k.a1, a0 := i }
  else { k with b1 := if k.b1 = 0 then i + 1 else k.b1, b0 := i }

/-- The sweep's probe (`kupL`, `N` slots from word `ob`): from slot `j` upward past the live
unmarked slots, without wrapping: the first slot that is not live unmarked, or the top one (`j <
N` holds on every call from the sweep, it only makes the model terminate). -/
def kupW (sl : Array Word) (ob N bt j : Word) : Word :=
  if j < N ∧ bt < vwd sl (ob + j) ∧ vwd sl (ob + j) < MARK ∧ j + 1 < N then
    kupW sl ob N bt (j + 1)
  else j
termination_by N.toNat - j.toNat
decreasing_by
  have h1 : j.toNat < N.toNat := UInt64.lt_iff_toNat_lt.mp ‹j < N ∧ _›.1
  have h2 := N.toNat_lt
  have : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  omega

/-- The new home of slot `i`'s entry: the home of `G` of its node in the doubled table. -/
def kjW (sa : TieredArray) (G : Mem → Word → Word) (N ob bt i : Word) (m : Mem) : Word :=
  homeW (G m (vwd (m.arr64 sa) (ob + i) - bt - 1)) N

/-- Where the sweep's step at slot `i` ends: above `i`, the probe's slot; else the home. -/
def ktgW (sa : TieredArray) (G : Mem → Word → Word) (N ob bt i : Word) (m : Mem) : Word :=
  if i < kjW sa G N ob bt i m then kupW (m.arr64 sa) ob N bt (kjW sa G N ob bt i m)
  else kjW sa G N ob bt i m

/-- The value word the step tests (`x`): the probe's slot's, or slot `i`'s own. -/
def kxW (sa : TieredArray) (G : Mem → Word → Word) (N ob bt i : Word) (m : Mem) : Word :=
  if i < kjW sa G N ob bt i m then vwd (m.arr64 sa) (ob + ktgW sa G N ob bt i m)
  else vwd (m.arr64 sa) (ob + i)

/-- The placement (`ktopQ`) of slot `i`'s entry (value `v`, fragment `q`) after the probe ended
at slot `j` with value `x`: moved to the free slot `j`, kept at `j = i`, or marked and recorded
in a range. -/
def ktopQW (sa : TieredArray) (n ob bt i j x v q : Word) (k : MkR) (m : Mem) : Mem × MkR :=
  if x ≤ bt then ((m.set64 sa (ob + j) (pk v q)).set64 sa (ob + i) 0, k)
  else if j = i then (m, k)
  else (m.set64 sa (ob + i) (pk (v + MARK) q), kdefR n i k)

/-- The step at the live slot `i` (`ktopB`). -/
def ktopBW (sa : TieredArray) (G : Mem → Word → Word) (N n ob bt i : Word) (k : MkR) (m : Mem) :
    Mem × MkR :=
  ktopQW sa n ob bt i (ktgW sa G N ob bt i m) (kxW sa G N ob bt i m) (vwd (m.arr64 sa) (ob + i))
    (kwd (m.arr64 sa) (ob + i)) k m

/-- The sweep's step at slot `i`: only a live slot is touched. -/
def ktopS (sa : TieredArray) (G : Mem → Word → Word) (N n ob bt i : Word) (k : MkR) (m : Mem) :
    Mem × MkR :=
  if bt < vwd (m.arr64 sa) (ob + i) then ktopBW sa G N n ob bt i k m else (m, k)

/-- **The top-down sweep** (`ktopL`) over the slots `H - 1 ‥ 0`. -/
def ktopW (sa : TieredArray) (G : Mem → Word → Word) (N n ob bt H : Word) (k : MkR) (m : Mem) :
    Mem × MkR :=
  if H = 0 then (m, k)
  else ktopW sa G N n ob bt (H - 1) (ktopS sa G N n ob bt (H - 1) k m).2
    (ktopS sa G N n ob bt (H - 1) k m).1
termination_by H.toNat
decreasing_by
  have : H.toNat ≠ 0 := fun h => ‹¬ H = 0› (UInt64.toNat_inj.mp (by simpa using h))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

/-- The probe of the re-insertion of slot `i`'s entry (`N` slots from word `ob`): from slot `j`
after `d` steps, past the live unmarked slots, the first slot that is `i`, free or marked
(`none`: the abort after `N` steps). -/
def kprobeW (sl : Array Word) (ob N i bt j d : Word) : Option Word :=
  if j ≠ i ∧ bt < vwd sl (ob + j) ∧ vwd sl (ob + j) < MARK then
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

/-- The placement of slot `i`'s entry (value `v`, fragment `q`, unmarked) at slot `j`
(`kplaceB`): the memory and the next value to re-insert (`0`: none). -/
def kplaceW (sa : TieredArray) (ob i j v q : Word) (m : Mem) : Mem × Word :=
  if j = i then (m.set64 sa (ob + i) (pk v q), 0)
  else if MARK ≤ vwd (m.arr64 sa) (ob + j) then
    ((m.set64 sa (ob + j) (pk v q)).set64 sa (ob + i) (rdW (m.arr64 sa) (ob + j)),
      vwd (m.arr64 sa) (ob + j))
  else
    ((m.set64 sa (ob + j) (pk v q)).set64 sa (ob + i) 0, 0)

/-- The re-insertions at slot `i` (`kinnerL`): while the value `v` is marked, spend one of the
budget `e`, probe from the home of `G` of its node, place it with slot `i`'s fragment.
The memory and the budget left; `none` where L aborts. -/
def kinnerW (sa : TieredArray) (G : Mem → Word → Word) (N ob bt i : Word) (e v : Word) (m : Mem) :
    Option (Mem × Word) :=
  if MARK ≤ v then
    if e = 0 then none
    else
      match kprobeW (m.arr64 sa) ob N i bt (homeW (G m (v - MARK - bt - 1)) N) 0 with
      | none => none
      | some j =>
        kinnerW sa G N ob bt i (e - 1)
          (kplaceW sa ob i j (v - MARK) (kwd (m.arr64 sa) (ob + i)) m).2
          (kplaceW sa ob i j (v - MARK) (kwd (m.arr64 sa) (ob + i)) m).1
  else some (m, e)
termination_by e.toNat
decreasing_by
  have : e.toNat ≠ 0 := fun h => ‹¬ e = 0› (UInt64.toNat_inj.mp (by simpa using h))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

/-- The re-insertion loop (`krehashL`): slots `i ‥ n - 1` of the old half, the budget `e`. -/
def krehashW (sa : TieredArray) (G : Mem → Word → Word) (N n ob bt i e : Word) (m : Mem) : Option Mem :=
  if i < n then
    match kinnerW sa G N ob bt i e (vwd (m.arr64 sa) (ob + i)) m with
    | none => none
    | some (m', e') => krehashW sa G N n ob bt (i + 1) e' m'
  else some m
termination_by n.toNat - i.toNat
decreasing_by
  have : i.toNat < n.toNat := UInt64.lt_iff_toNat_lt.mp ‹i < n›
  have := n.toNat_lt
  have : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  omega

/-- The memory after the growth's head and zero loop: the count word, the upper half zeroed
(`n` words from `ob + n`). -/
def kzM (sa : ArrId) (t : Word) (m : Mem) : Mem :=
  kzeroW (tierA sa t) (koW sa m t + 2 + knW sa m t) (knW sa m t >>> 3).toNat
    (m.set64 (tierA sa t) 0 (knW sa m t * 2 - SN0))

/-- The sweep of the growth, from the memory `kzM`. -/
def ktopM (sa : ArrId) (G : Mem → Word → Word) (t : Word) (m : Mem) : Mem × MkR :=
  ktopW (tierA sa t) G (knW sa m t * 2) (knW sa m t) (koW sa m t + 2) (rdW (m.arr64 CTL) SCB * t)
    (knW sa m t) ⟨0, 0, 0, 0⟩ (kzM sa t m)

/-- **The growth of tier `t`** (`kgrowB`, in place): the memory after it, `none` where it
aborts. The table (`n` slots from word `ob = o + 2`) doubles where it is: the count word, the
upper half zeroed, the top-down sweep, then the marked entries re-inserted over the two mark
ranges. -/
def kgrowM (sa : ArrId) (G : Mem → Word → Word) (t : Word) (m : Mem) : Option Mem :=
  if m.len64 (tierA sa t) - 2 < koW sa m t + knW sa m t * 2 then none
  else
    (krehashW (tierA sa t) G (knW sa m t * 2) (ktopM sa G t m).2.a1 (koW sa m t + 2)
      (rdW (m.arr64 CTL) SCB * t) (ktopM sa G t m).2.a0 (knW sa m t) (ktopM sa G t m).1).bind
    (krehashW (tierA sa t) G (knW sa m t * 2) (ktopM sa G t m).2.b1 (koW sa m t + 2)
      (rdW (m.arr64 CTL) SCB * t) (ktopM sa G t m).2.b0 (knW sa m t))

/-! ## The frame of the growth -/

/-- From `m` to `m'` only array `sa` changes, and no size. -/
structure GFr (sa : TieredArray) (m m' : Mem) : Prop where
  arr : ∀ b, b ≠ sa → m'.arr64 b = m.arr64 b
  size : ∀ b, (m'.arr64 b).size = (m.arr64 b).size

theorem GFr.refl (sa : TieredArray) (m : Mem) : GFr sa m m := ⟨fun _ _ => rfl, fun _ => rfl⟩

theorem GFr.trans {sa : TieredArray} {m₁ m₂ m₃ : Mem} (h₁ : GFr sa m₁ m₂) (h₂ : GFr sa m₂ m₃) :
    GFr sa m₁ m₃ :=
  ⟨fun b hb => (h₂.arr b hb).trans (h₁.arr b hb), fun b => (h₂.size b).trans (h₁.size b)⟩

theorem GFr.set64 (sa : TieredArray) (m : Mem) (i v : Word) : GFr sa m (m.set64 sa i v) := by
  refine ⟨fun b hb => Mem.arr64_set64_ne _ _ _ _ _ hb, fun b => ?_⟩
  by_cases h : b = sa
  · subst h; exact Mem.size_arr64_set64 _ _ _ _
  · rw [Mem.arr64_set64_ne _ _ _ _ _ h]

theorem GFr.zero8 (sa : TieredArray) (k : Word) (m : Mem) : GFr sa m (zero8 sa k m) := by
  unfold L.Arena.zero8
  exact ((((((GFr.set64 _ _ _ _).trans (GFr.set64 _ _ _ _)).trans (GFr.set64 _ _ _ _)).trans
    (GFr.set64 _ _ _ _)).trans (GFr.set64 _ _ _ _)).trans (GFr.set64 _ _ _ _)).trans
    (GFr.set64 _ _ _ _) |>.trans (GFr.set64 _ _ _ _)

theorem kzeroW_fr (sa : TieredArray) : ∀ (e : Nat) (x : Word) (m : Mem), GFr sa m (kzeroW sa x e m)
  | 0, _, m => GFr.refl _ m
  | e + 1, x, m => (GFr.zero8 sa x m).trans (kzeroW_fr sa e (x + 8) _)

theorem ktopBW_fr (sa : TieredArray) (G : Mem → Word → Word) (N n ob bt i : Word) (k : MkR)
    (m : Mem) : GFr sa m (ktopBW sa G N n ob bt i k m).1 := by
  unfold ktopBW ktopQW
  split
  · exact (GFr.set64 _ _ _ _).trans (GFr.set64 _ _ _ _)
  split
  · exact GFr.refl _ _
  · exact GFr.set64 _ _ _ _

theorem ktopS_fr (sa : TieredArray) (G : Mem → Word → Word) (N n ob bt i : Word) (k : MkR)
    (m : Mem) : GFr sa m (ktopS sa G N n ob bt i k m).1 := by
  unfold ktopS
  split
  · exact ktopBW_fr _ _ _ _ _ _ _ _ _
  · exact GFr.refl _ _

theorem ktopW_fr (sa : TieredArray) (G : Mem → Word → Word) (N n ob bt H : Word) (k : MkR)
    (m : Mem) : GFr sa m (ktopW sa G N n ob bt H k m).1 := by
  fun_induction ktopW sa G N n ob bt H k m with
  | case1 => exact GFr.refl _ _
  | case2 H k m hH ih => exact (ktopS_fr _ _ _ _ _ _ _ _ _).trans ih

theorem kplaceW_fr (sa : TieredArray) (ob i j v q : Word) (m : Mem) : GFr sa m (kplaceW sa ob i j v q m).1 := by
  unfold kplaceW
  split
  · exact GFr.set64 _ _ _ _
  split
  · exact (GFr.set64 _ _ _ _).trans (GFr.set64 _ _ _ _)
  · exact (GFr.set64 _ _ _ _).trans (GFr.set64 _ _ _ _)

theorem kinnerW_fr (sa : TieredArray) (G : Mem → Word → Word) (N ob bt i e v : Word) (m m' : Mem)
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

theorem krehashW_fr (sa : TieredArray) (G : Mem → Word → Word) (N n ob bt i e : Word) (m m' : Mem)
    (h : krehashW sa G N n ob bt i e m = some m') : GFr sa m m' := by
  fun_induction krehashW sa G N n ob bt i e m generalizing m' with
  | case1 => simp_all
  | case2 i e m hi m1 e1 h1 ih =>
    exact (kinnerW_fr _ _ _ _ _ _ _ _ _ _ _ h1).trans (ih m' h)
  | case3 => simp at h; subst h; exact GFr.refl _ _

theorem kgrowM_fr (sa : ArrId) (G : Mem → Word → Word) (t : Word) (m m' : Mem)
    (h : kgrowM sa G t m = some m') : GFr (tierA sa t) m m' := by
  simp only [kgrowM] at h
  have h' := ite_none_some h
  obtain ⟨m4, h4, h5⟩ := Option.bind_eq_some_iff.mp h'
  exact ((((GFr.set64 _ _ _ _).trans (kzeroW_fr _ _ _ _)).trans (ktopW_fr _ _ _ _ _ _ _ _ _)).trans
    (krehashW_fr _ _ _ _ _ _ _ _ _ _ h4)).trans (krehashW_fr _ _ _ _ _ _ _ _ _ _ h5)

/-- Word stores to two different arrays commute. -/
theorem Mem.set64_comm (m : Mem) (a b : TieredArray) (i j v w : Word) (h : a ≠ b) :
    (m.set64 a i v).set64 b j w = (m.set64 b j w).set64 a i v := by
  simp only [Mem.set64, Mem.arr64, h, Ne.symm h, ite_false, Mem.mk.injEq, and_true,
    true_and]
  funext s
  by_cases ha : s = a <;> by_cases hb : s = b <;> simp_all

/-- A word array after a store, for any array. -/
theorem arr64_set64_any (m : Mem) (a a' : TieredArray) (i v : Word) :
    (m.set64 a i v).arr64 a' = if a = a' then (m.arr64 a).set! i.toNat v else m.arr64 a' := by
  simp only [Mem.set64, Mem.arr64]
  by_cases h : a = a'
  · subst h; simp
  · simp [h, Ne.symm h]

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
