module

public import ConAgua.Arena.JustifySideModels
public import ConAgua.Arena.FreezeTrunc
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import all ConAgua.Arena.JustifySideModels

@[expose] public section

/-!
# The move of the solution's index: the refinement (lane compare)

`index_to_solution(cnt)` after the solution's `build_index(cnt)`: from `IndexR m IS` (and the
index's keys being persistent names below the name counts, `IndexKeysIn`), the solution's index
part of `SolR` holds at `IS` (`SolIdxR`), the stream index is empty (`IndexR m' {}`, what
`build_index` starts from), and only the row arrays and `CTL[128]`, `CTL[225]`, `CTL[226]` change.

One loop moves one tag's rows (`sdMoveAW.loop1`, …): `mvLoop_ok` is its meaning, for any function
with the loop's equation.
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

open Std.WP
open scoped Lean.Order
open ConRon.Arena

namespace L.Arena

/-! ## One loop -/

/-- One step of a move loop: word `i` of `E` to `S`, of `T` to `U`, the sources zeroed. -/
def mvStep (E S T U : TieredArray) (m : Mem) (i : Word) : Mem :=
  (((m.set64 S i (rdW (m.arr64 E) i)).set64 E i 0).set64 U i
    (rdW (((m.set64 S i (rdW (m.arr64 E) i)).set64 E i 0).arr64 T) i)).set64 T i 0

/-- The loop's abort test on word `i` of the array (after the first half's writes for `T`). -/
def mvBad (v i : Word) : Prop := i &&& 1 = 0 ∧ v >>> 32 ≠ 0

/-- **A move loop's equation** (the generated loop models' `eq_1`, `eq_2`). -/
structure MvLoop (E S T U : TieredArray) (F : Nat → Mem → Word → Word → Option Mem) : Prop where
  zero : ∀ m i N, F 0 m i N = none
  succ : ∀ n m i N, F (n + 1) m i N =
    if i < N then
      if i &&& 1 = 0 ∧ rdW (m.arr64 E) i >>> 32 ≠ 0 then none
      else if i &&& 1 = 0 ∧ rdW (((m.set64 S i (rdW (m.arr64 E) i)).set64 E i 0).arr64 T) i >>> 32 ≠ 0
        then none
      else F n (mvStep E S T U m i) (i + 1) N
    else some m

/-- What a move loop has done from `m₀` up to word `i` (exclusive). -/
structure MvInv (E S T U : TieredArray) (m₀ m : Mem) (i : Nat) : Prop where
  other : ∀ b, b ≠ E → b ≠ S → b ≠ T → b ≠ U → m.arr64 b = m₀.arr64 b
  size : ∀ b, (m.arr64 b).size = (m₀.arr64 b).size
  lo : ∀ j < i, rdN (m.arr64 S) j = rdN (m₀.arr64 E) j ∧ rdN (m.arr64 E) j = 0 ∧
    rdN (m.arr64 U) j = rdN (m₀.arr64 T) j ∧ rdN (m.arr64 T) j = 0 ∧
    (j % 2 = 0 → (rdN (m₀.arr64 E) j).toNat < 2 ^ 32 ∧ (rdN (m₀.arr64 T) j).toNat < 2 ^ 32)
  hi : ∀ j, i ≤ j → rdN (m.arr64 E) j = rdN (m₀.arr64 E) j ∧ rdN (m.arr64 S) j = rdN (m₀.arr64 S) j ∧
    rdN (m.arr64 T) j = rdN (m₀.arr64 T) j ∧ rdN (m.arr64 U) j = rdN (m₀.arr64 U) j

theorem size_set64_any (m : Mem) (a b : TieredArray) (k v : Word) :
    ((m.set64 a k v).arr64 b).size = (m.arr64 b).size := by
  by_cases h : b = a
  · subst h; exact Mem.size_arr64_set64 _ _ _ _
  · rw [Mem.arr64_set64_ne _ _ _ _ _ h]

theorem rdW_rdN (a : Array Word) (x : Word) : rdW a x = rdN a x.toNat := rfl

theorem rdN_oob {a : Array Word} {j : Nat} (h : a.size ≤ j) : rdN a j = 0 := by
  simp [rdN, Array.getElem?_eq_none h]

theorem and1_eq0 (i : Word) : i &&& 1 = 0 ↔ i.toNat % 2 = 0 := by
  constructor
  · intro h; have := congrArg UInt64.toNat h; simp [UInt64.toNat_and] at this; omega
  · intro h; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_and]; omega

theorem shr32_eq0 (v : Word) : v >>> 32 = 0 ↔ v.toNat < 2 ^ 32 := by
  constructor
  · intro h; have := congrArg UInt64.toNat h; simp [UInt64.toNat_shiftRight] at this
    rw [Nat.shiftRight_eq_div_pow] at this; have := Nat.div_eq_zero_iff.mp this; omega
  · intro h; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_shiftRight]
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt h

theorem MvInv.start (E S T U : TieredArray) (m : Mem) : MvInv E S T U m m 0 :=
  ⟨fun _ _ _ _ _ => rfl, fun _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- One step of the loop keeps the invariant. -/
theorem MvInv.step {E S T U : TieredArray} {m₀ m : Mem}
    (hd : E ≠ S ∧ E ≠ T ∧ E ≠ U ∧ S ≠ T ∧ S ≠ U ∧ T ≠ U)
    (hsz : (m₀.arr64 S).size = (m₀.arr64 E).size ∧ (m₀.arr64 U).size = (m₀.arr64 T).size) {i : Word} (h : MvInv E S T U m₀ m i.toNat)
    (hE : ¬ (i &&& 1 = 0 ∧ rdW (m.arr64 E) i >>> 32 ≠ 0))
    (hT : ¬ (i &&& 1 = 0 ∧ rdW (((m.set64 S i (rdW (m.arr64 E) i)).set64 E i 0).arr64 T) i >>> 32 ≠ 0)) :
    MvInv E S T U m₀ (mvStep E S T U m i) (i.toNat + 1) := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
  have hs := h.size
  have hh := h.hi i.toNat (Nat.le_refl _)
  have hT' : rdW (((m.set64 S i (rdW (m.arr64 E) i)).set64 E i 0).arr64 T) i = rdW (m.arr64 T) i := by
    rw [Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm d2), Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm d4)]
  rw [hT'] at hT
  simp only [rdW_rdN, and1_eq0, shr32_eq0, not_and, Decidable.not_not] at hE hT
  rw [hh.1] at hE; rw [hh.2.2.1] at hT
  have key : ∀ b j, rdN ((mvStep E S T U m i).arr64 b) j =
      if b = T ∧ i.toNat = j ∧ j < (m.arr64 T).size then 0
      else if b = U ∧ i.toNat = j ∧ j < (m.arr64 U).size then rdN (m.arr64 T) i.toNat
      else if b = E ∧ i.toNat = j ∧ j < (m.arr64 E).size then 0
      else if b = S ∧ i.toNat = j ∧ j < (m.arr64 S).size then rdN (m.arr64 E) i.toNat
      else rdN (m.arr64 b) j := by
    intro b j
    unfold mvStep; rw [hT']
    simp only [rdN_set64, size_set64_any, rdW_rdN]
  refine ⟨fun b b1 b2 b3 b4 => ?_, fun b => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · simp only [mvStep]; rw [Mem.arr64_set64_ne _ _ _ _ _ b3, Mem.arr64_set64_ne _ _ _ _ _ b4,
      Mem.arr64_set64_ne _ _ _ _ _ b1, Mem.arr64_set64_ne _ _ _ _ _ b2]; exact h.other b b1 b2 b3 b4
  · simp only [mvStep, size_set64_any]; exact hs b
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have := h.lo j hj
      simp only [key]
      have hne : i.toNat ≠ j := by omega
      simp only [hne, false_and, and_false, ite_false]; exact this
    · simp only [key]
      refine ⟨?_, ?_, ?_, ?_, fun he => ⟨hE he, hT he⟩⟩
      · simp only [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, false_and, ite_false, true_and]
        by_cases c : i.toNat < (m.arr64 S).size
        · rw [ite_eq_left c, hh.1]
        · rw [ite_eq_right c, rdN_oob (Nat.le_of_not_lt c), rdN_oob (a := m₀.arr64 E) (by have := hs S; omega)]
      · simp only [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, false_and, ite_false, true_and]
        by_cases c : i.toNat < (m.arr64 E).size
        · rw [ite_eq_left c]
        · rw [ite_eq_right c, rdN_oob (Nat.le_of_not_lt c)]
      · simp only [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, false_and, ite_false, true_and]
        by_cases c : i.toNat < (m.arr64 U).size
        · rw [ite_eq_left c, hh.2.2.1]
        · rw [ite_eq_right c, rdN_oob (Nat.le_of_not_lt c), rdN_oob (a := m₀.arr64 T) (by have := hs U; omega)]
      · simp only [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, false_and, ite_false, true_and]
        by_cases c : i.toNat < (m.arr64 T).size
        · rw [ite_eq_left c]
        · rw [ite_eq_right c, rdN_oob (Nat.le_of_not_lt c)]
  · have := h.hi j (by omega)
    simp only [key]
    have hne : i.toNat ≠ j := by omega
    simp only [hne, false_and, and_false, ite_false]; exact this

/-- **A move loop's meaning**: run from word `0` to `N`, it moves `E[0‥N)` to `S`, `T[0‥N)` to
`U` (the sources zeroed), leaves the other arrays and every size, and every even word it moved is
below `2^32`. -/
theorem mvLoop_ok {E S T U : TieredArray} {F : Nat → Mem → Word → Word → Option Mem}
    (hF : MvLoop E S T U F) (hd : E ≠ S ∧ E ≠ T ∧ E ≠ U ∧ S ≠ T ∧ S ≠ U ∧ T ≠ U)
    {m₀ : Mem} (hsz : (m₀.arr64 S).size = (m₀.arr64 E).size ∧ (m₀.arr64 U).size = (m₀.arr64 T).size)
    {N : Word} :
    ∀ n (m : Mem) (i : Word) (m' : Mem), MvInv E S T U m₀ m i.toNat → i ≤ N →
      F n m i N = some m' → MvInv E S T U m₀ m' N.toNat := by
  intro n
  induction n with
  | zero => intro m i m' _ _ h; rw [hF.zero] at h; cases h
  | succ n ih =>
    intro m i m' hI hle h
    rw [hF.succ] at h
    by_cases hi : i < N
    · rw [ite_eq_left hi] at h
      split at h; · cases h
      split at h; · cases h
      rename_i hE hT
      have e : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add]; have := UInt64.lt_iff_toNat_lt.mp hi; have := UInt64.toNat_lt N
        simp; omega
      exact ih _ _ _ (by rw [e]; exact hI.step hd hsz hE hT) (UInt64.le_iff_toNat_le.mpr (by rw [e]; have := UInt64.lt_iff_toNat_lt.mp hi; omega)) h
    · rw [ite_eq_right hi] at h; cases h
      have : i = N := by
        have := UInt64.le_iff_toNat_le.mp hle; have := UInt64.not_lt.mp hi
        exact UInt64.le_antisymm hle this
      subst this; exact hI

/-! ## One tag -/

/-- The words a tag's move covers: twice the tag's tier-0 name count. -/
def mvLen (m : Mem) (g : Nat) : Nat := 2 * nmCnt m g

/-- A tag's move, done: `MvInv` over its four arrays up to `mvLen`. -/
abbrev MvTag (m₀ m : Mem) (g : Nat) : Prop :=
  MvInv (eixArr g) (sixArr g) (tixArr g) (stxArr g) m₀ m (mvLen m₀ g)

theorem shl1_toNat {c : Word} (h : ¬ 134217728 < c) : (c <<< 1).toNat = 2 * c.toNat := by
  have : c.toNat ≤ 134217728 := by
    have := UInt64.not_lt.mp h; exact UInt64.le_iff_toNat_le.mp this
  rw [UInt64.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega

/-- A tag's move from its loop: `sd_move_*`'s model returned, so its loop did. -/
theorem mvTag_of {g : Nat} {F : Nat → Mem → Word → Word → Option Mem}
    (hF : MvLoop (eixArr g) (sixArr g) (tixArr g) (stxArr g) F)
    (hd : (eixArr g : TieredArray) ≠ sixArr g ∧ (eixArr g : TieredArray) ≠ tixArr g ∧
      (eixArr g : TieredArray) ≠ stxArr g ∧ (sixArr g : TieredArray) ≠ tixArr g ∧
      (sixArr g : TieredArray) ≠ stxArr g ∧ (tixArr g : TieredArray) ≠ stxArr g)
    {m m' : Mem} (hsz : (m.arr64 (sixArr g)).size = (m.arr64 (eixArr g)).size ∧
      (m.arr64 (stxArr g)).size = (m.arr64 (tixArr g)).size)
    {k : Nat} {c : Word} (hca : UInt64.ofNat (nmCS g).ca.toNat = c)
    (hc : ¬ 134217728 < rdW (m.arr64 CTL) c)
    (h : F k m 0 (rdW (m.arr64 CTL) c <<< 1) = some m') :
    MvTag m m' g := by
  have := mvLoop_ok hF hd hsz k m 0 m' (MvInv.start _ _ _ _ m) (UInt64.zero_le) h
  unfold MvTag mvLen nmCnt; rw [hca, ← shl1_toNat hc]; exact this

/-- The tag of `w`'s rows, and its move's words: a tier-0 row of tag `g` is moved iff its index is
below the count. -/
theorem sd_rowIx_lt {m : Mem} {w : Word} :
    rowIx w < mvLen m (rowTag w) ↔ (idxW w).toNat < nmCnt m (rowTag w) := by
  unfold rowIx mvLen; omega

theorem sd_rowIx1_lt {m : Mem} {w : Word} (h : rowIx w < mvLen m (rowTag w)) :
    rowIx w + 1 < mvLen m (rowTag w) := by
  unfold rowIx mvLen at *; omega

/-- A tag's four arrays. -/
def tagArrs (g : Nat) : List TieredArray := [eixArr g, sixArr g, tixArr g, stxArr g]

/-- **A tag's rows after the move**, from the memory `m` before it: the solution's rows the old
stream rows below `mvLen`, the stream rows zero there; past it both kept; the moved counter words
below `2^32`. -/
structure TagDone (m M : Mem) (g : Nat) : Prop where
  six : ∀ j, rdN (M.arr64 (sixArr g)) j =
    if j < mvLen m g then rdN (m.arr64 (eixArr g)) j else rdN (m.arr64 (sixArr g)) j
  eix : ∀ j, rdN (M.arr64 (eixArr g)) j = if j < mvLen m g then 0 else rdN (m.arr64 (eixArr g)) j
  stx : ∀ j, rdN (M.arr64 (stxArr g)) j =
    if j < mvLen m g then rdN (m.arr64 (tixArr g)) j else rdN (m.arr64 (stxArr g)) j
  tix : ∀ j, rdN (M.arr64 (tixArr g)) j = if j < mvLen m g then 0 else rdN (m.arr64 (tixArr g)) j
  even : ∀ j < mvLen m g, j % 2 = 0 →
    (rdN (m.arr64 (eixArr g)) j).toNat < 2 ^ 32 ∧ (rdN (m.arr64 (tixArr g)) j).toNat < 2 ^ 32

theorem MvTag.done {m mg M : Mem} {g : Nat} (h : MvTag m mg g)
    (hc : ∀ b ∈ tagArrs g, M.arr64 b = mg.arr64 b) : TagDone m M g := by
  have e1 := hc (eixArr g) (by simp [tagArrs]); have e2 := hc (sixArr g) (by simp [tagArrs])
  have e3 := hc (tixArr g) (by simp [tagArrs]); have e4 := hc (stxArr g) (by simp [tagArrs])
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j hj he => (h.lo j hj).2.2.2.2 he⟩ <;>
    (by_cases hj : j < mvLen m g
     · simp only [hj, ite_true, e1, e2, e3, e4]; have := h.lo j hj; simp only [this]
     · simp only [hj, ite_false, e1, e2, e3, e4]; have := h.hi j (by omega); simp only [this])

theorem ctl_ne_tag (g : Nat) : ∀ b ∈ tagArrs g, b ≠ (CTL : TieredArray) := by
  intro b hb; simp only [tagArrs, eixArr, sixArr, tixArr, stxArr, List.mem_cons, List.not_mem_nil,
    or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> split <;> (try split) <;> decide

/-- The arrays of two tags are apart. -/
theorem tags_apart {g g' : Nat} (hg : g ≤ 2) (hg' : g' ≤ 2) (h : g ≠ g') :
    ∀ b ∈ tagArrs g, ∀ b' ∈ tagArrs g', b ≠ b' := by
  rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl <;>
  rcases (show g' = 0 ∨ g' = 1 ∨ g' = 2 by omega) with rfl | rfl | rfl <;>
  first | exact absurd rfl h | decide

theorem MvInv.ctl {E S T U : TieredArray} {m₀ m : Mem} {i : Nat} (h : MvInv E S T U m₀ m i)
    (hn : (CTL : TieredArray) ≠ E ∧ (CTL : TieredArray) ≠ S ∧ (CTL : TieredArray) ≠ T ∧ (CTL : TieredArray) ≠ U) :
    m.arr64 CTL = m₀.arr64 CTL := h.other _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2

theorem MvTag.ctlEq {m m' : Mem} {g : Nat} (h : MvTag m m' g) : m'.arr64 CTL = m.arr64 CTL := by
  have := ctl_ne_tag g
  exact h.other _ (Ne.symm (this _ (by simp [tagArrs]))) (Ne.symm (this _ (by simp [tagArrs])))
    (Ne.symm (this _ (by simp [tagArrs]))) (Ne.symm (this _ (by simp [tagArrs])))

/-- A tag's move leaves another tag's arrays. -/
theorem MvTag.keep {m m' : Mem} {g g' : Nat} (hg : g ≤ 2) (hg' : g' ≤ 2) (hne : g ≠ g')
    (h : MvTag m m' g) : ∀ b ∈ tagArrs g', m'.arr64 b = m.arr64 b := by
  intro b hb
  have := tags_apart hg' hg (Ne.symm hne) b hb
  exact h.other b (this _ (by simp [tagArrs])) (this _ (by simp [tagArrs]))
    (this _ (by simp [tagArrs])) (this _ (by simp [tagArrs]))

theorem mvLen_congr {m m' : Mem} (h : m'.arr64 CTL = m.arr64 CTL) (g : Nat) : mvLen m' g = mvLen m g := by
  simp only [mvLen, nmCnt, h]

/-! ## The rows after the move -/

section after
variable {m M : Mem} (hD : ∀ g ≤ 2, TagDone m M g)
  (hz : ∀ g ≤ 2, ∀ j, rdN (m.arr64 (sixArr g)) j = 0 ∧ rdN (m.arr64 (stxArr g)) j = 0)
include hD hz

theorem solRow_after {w : Word} (ht : rowTag w ≤ 2 ∧ rowTier w = 0) :
    solRow M w = if (idxW w).toNat < nmCnt m (rowTag w) then baseRow m w else (0, 0) := by
  have d := hD _ ht.1
  simp only [solRow, baseRow, ht, and_self, ite_true, d.six]
  by_cases h : (idxW w).toNat < nmCnt m (rowTag w)
  · have h1 := sd_rowIx_lt.mpr h; have h2 := sd_rowIx1_lt h1
    simp [h, h1, h2]
  · have h1 : ¬ rowIx w < mvLen m (rowTag w) := fun e => h (sd_rowIx_lt.mp e)
    have h2 : ¬ rowIx w + 1 < mvLen m (rowTag w) := by unfold rowIx mvLen at *; omega
    simp [h, h1, h2, (hz _ ht.1 _).1]

theorem solTbl_after {w : Word} (ht : rowTag w ≤ 2 ∧ rowTier w = 0) :
    solTbl M w = if (idxW w).toNat < nmCnt m (rowTag w) then baseTbl m w else (0, 0) := by
  have d := hD _ ht.1
  simp only [solTbl, baseTbl, ht, and_self, ite_true, d.stx]
  by_cases h : (idxW w).toNat < nmCnt m (rowTag w)
  · have h1 := sd_rowIx_lt.mpr h; have h2 := sd_rowIx1_lt h1
    simp [h, h1, h2]
  · have h1 : ¬ rowIx w < mvLen m (rowTag w) := fun e => h (sd_rowIx_lt.mp e)
    have h2 : ¬ rowIx w + 1 < mvLen m (rowTag w) := by unfold rowIx mvLen at *; omega
    simp [h, h1, h2, (hz _ ht.1 _).2]

omit hz in
theorem baseRow_after {w : Word} (ht : rowTag w ≤ 2 ∧ rowTier w = 0) :
    (baseRow M w).1 = if (idxW w).toNat < nmCnt m (rowTag w) then 0 else (baseRow m w).1 := by
  have d := hD _ ht.1
  simp only [baseRow, ht, and_self, ite_true, d.eix]
  by_cases h : (idxW w).toNat < nmCnt m (rowTag w)
  · simp [h, sd_rowIx_lt.mpr h]
  · have h1 : ¬ rowIx w < mvLen m (rowTag w) := fun e => h (sd_rowIx_lt.mp e)
    simp [h, h1]

omit hz in
theorem baseTbl_after {w : Word} (ht : rowTag w ≤ 2 ∧ rowTier w = 0) :
    (baseTbl M w).1 = if (idxW w).toNat < nmCnt m (rowTag w) then 0 else (baseTbl m w).1 := by
  have d := hD _ ht.1
  simp only [baseTbl, ht, and_self, ite_true, d.tix]
  by_cases h : (idxW w).toNat < nmCnt m (rowTag w)
  · simp [h, sd_rowIx_lt.mpr h]
  · have h1 : ¬ rowIx w < mvLen m (rowTag w) := fun e => h (sd_rowIx_lt.mp e)
    simp [h, h1]

omit hz in
/-- The moved counter words are below `2^32`. -/
theorem moved_lt {w : Word} (ht : rowTag w ≤ 2 ∧ rowTier w = 0)
    (h : (idxW w).toNat < nmCnt m (rowTag w)) :
    (baseRow m w).1.toNat < 2 ^ 32 ∧ (baseTbl m w).1.toNat < 2 ^ 32 := by
  have := (hD _ ht.1).even (rowIx w) (sd_rowIx_lt.mpr h) (by unfold rowIx; omega)
  simp only [baseRow, baseTbl, ht, and_self, ite_true]; exact this

end after

/-- Outside the moved words a stream row is empty: every key of the index is a name below its
tag's count. -/
theorem baseRow_out {m : Mem} {I : IStreamIndex} (hI : IndexR m I) (hK : IndexKeysIn m I) (n : NIdx)
    (ht : rowTag n.word.toUInt64 ≤ 2)
    (hout : ¬ (idxW n.word.toUInt64).toNat < nmCnt m (rowTag n.word.toUInt64)) :
    (baseRow m n.word.toUInt64).1 = 0 ∧ (baseTbl m n.word.toUInt64).1 = 0 := by
  constructor
  · refine Decidable.byContradiction fun h0 => ?_
    have hb := hI.base n
    rw [ite_eq_right_of_eq_false _ _ (eq_false h0)] at hb
    cases e : I.base.idx[n]? with
    | none => rw [e] at hb; cases hb
    | some p => exact hout (hK.idx n p e ht).2
  · refine Decidable.byContradiction fun h0 => ?_
    have hb := hI.btbl n
    rw [ite_eq_right_of_eq_false _ _ (eq_false h0)] at hb
    cases e : I.base.tbls[n]? with
    | none => rw [e] at hb; cases hb
    | some p => exact hout (hK.tbls n p e ht).2

theorem TagDone.congr {m m₁ M : Mem} {g : Nat} (h : TagDone m₁ M g)
    (hA : ∀ b ∈ tagArrs g, m₁.arr64 b = m.arr64 b) (hc : m₁.arr64 CTL = m.arr64 CTL) :
    TagDone m M g := by
  have e1 := hA (eixArr g) (by simp [tagArrs]); have e2 := hA (sixArr g) (by simp [tagArrs])
  have e3 := hA (tixArr g) (by simp [tagArrs]); have e4 := hA (stxArr g) (by simp [tagArrs])
  have el := mvLen_congr hc g
  obtain ⟨a, b, c, d, e⟩ := h
  rw [e1, e2, e3, e4, el] at *
  exact ⟨a, b, c, d, e⟩

/-! ## The three moves -/

theorem sdMoveA_tag {n : Nat} {m m' : Mem} {x : Word} (h : sdMoveAW n m = some (x, m'))
    (hsz : (m.arr64 (sixArr 0)).size = (m.arr64 (eixArr 0)).size ∧
      (m.arr64 (stxArr 0)).size = (m.arr64 (tixArr 0)).size) : MvTag m m' 0 := by
  rcases n with _ | n
  · simp [sdMoveAW] at h
  by_cases c : 134217728 < rdW (m.arr64 CTL) nanonCS.ca
  · rw [sdMoveAW.abort1 _ _ c] at h; cases h
  rw [sdMoveAW.arm1 _ _ c] at h
  cases e : sdMoveAW.loop1 (n + 1) m 0 (rdW (m.arr64 CTL) nanonCS.ca <<< 1) with
  | none => rw [e, sdMoveAW.k_loop1.none] at h; cases h
  | some m₁ =>
    rw [e, sdMoveAW.k_loop1.arm1] at h; cases h
    exact mvTag_of (g := 0) ⟨sdMoveAW.loop1.eq_1, fun n m i N => sdMoveAW.loop1.eq_2 m i N n⟩ (by decide) hsz rfl c e

theorem sdMoveS_tag {n : Nat} {m m' : Mem} {x : Word} (h : sdMoveSW n m = some (x, m'))
    (hsz : (m.arr64 (sixArr 1)).size = (m.arr64 (eixArr 1)).size ∧
      (m.arr64 (stxArr 1)).size = (m.arr64 (tixArr 1)).size) : MvTag m m' 1 := by
  rcases n with _ | n
  · simp [sdMoveSW] at h
  by_cases c : 134217728 < rdW (m.arr64 CTL) nstrCS.ca
  · rw [sdMoveSW.abort1 _ _ c] at h; cases h
  rw [sdMoveSW.arm1 _ _ c] at h
  cases e : sdMoveSW.loop1 (n + 1) m 0 (rdW (m.arr64 CTL) nstrCS.ca <<< 1) with
  | none => rw [e, sdMoveSW.k_loop1.none] at h; cases h
  | some m₁ =>
    rw [e, sdMoveSW.k_loop1.arm1] at h; cases h
    exact mvTag_of (g := 1) ⟨sdMoveSW.loop1.eq_1, fun n m i N => sdMoveSW.loop1.eq_2 m i N n⟩ (by decide) hsz rfl c e

theorem sdMoveN_tag {n : Nat} {m m' : Mem} {x : Word} (h : sdMoveNW n m = some (x, m'))
    (hsz : (m.arr64 (sixArr 2)).size = (m.arr64 (eixArr 2)).size ∧
      (m.arr64 (stxArr 2)).size = (m.arr64 (tixArr 2)).size) : MvTag m m' 2 := by
  rcases n with _ | n
  · simp [sdMoveNW] at h
  by_cases c : 134217728 < rdW (m.arr64 CTL) nnumCS.ca
  · rw [sdMoveNW.abort1 _ _ c] at h; cases h
  rw [sdMoveNW.arm1 _ _ c] at h
  cases e : sdMoveNW.loop1 (n + 1) m 0 (rdW (m.arr64 CTL) nnumCS.ca <<< 1) with
  | none => rw [e, sdMoveNW.k_loop1.none] at h; cases h
  | some m₁ =>
    rw [e, sdMoveNW.k_loop1.arm1] at h; cases h
    exact mvTag_of (g := 2) ⟨sdMoveNW.loop1.eq_1, fun n m i N => sdMoveNW.loop1.eq_2 m i N n⟩ (by decide) hsz rfl c e

/-! ## The refinement -/

/-- **The solution's index part of `SolR`** at the index `I`: `SolR`'s fields but the mates. -/
structure SolIdxR (m : Mem) (I : IStreamIndex) : Prop where
  base : ∀ n : NIdx,
    (I.base.idx[n]?).map (fun e => (e.1, some e.2)) =
      (if (solRow m n.word.toUInt64).1 = 0 then none
       else some ((solRow m n.word.toUInt64).1.toNat - 1,
         decCI (erecP m) (solRow m n.word.toUInt64).2.toNat))
  btbl : ∀ n : NIdx,
    (I.base.tbls[n]?).map (fun e => (e.1, some e.2)) =
      (if (solTbl m n.word.toUInt64).1 = 0 then none
       else some ((solTbl m n.word.toUInt64).1.toNat - 1,
         decTbl (erecP m) (solTbl m n.word.toUInt64).2.toNat))
  next : (ctlW m SNEXTC).toNat = I.next
  size : (ctlW m SCNTC).toNat = I.firsts.size
  rows : ∀ w : Word, (solRow m w).1.toNat < 2 ^ 32 ∧ (solTbl m w).1.toNat < 2 ^ 32

/-- `SolR` from its index part and the mates' part. -/
theorem SolR.ofIdx {m : Mem} {J : ISolution} (h : SolIdxR m J.idx)
    (hm : ∀ n : NIdx, J.mates[n]? = matList m n.word.toUInt64)
    (hd : ∀ w : Word, (matRow m w).1 ≠ 0 → (matList m w).isSome) : SolR m J :=
  ⟨h.base, h.btbl, h.next, h.size, hm, hd, h.rows⟩

/-- The arrays the move writes. -/
def moveA : List TieredArray := tagArrs 0 ++ tagArrs 1 ++ tagArrs 2

/-- The control words the move writes. -/
def moveC : List Word := [SNEXTC, SCNTC, 128]

theorem tag_mem_moveA {g : Nat} (hg : g ≤ 2) {b : TieredArray} (hb : b ∈ tagArrs g) : b ∈ moveA := by
  rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl <;> simp [moveA, hb]

theorem row_off {m : Mem} {w : Word} (ht : ¬ (rowTag w ≤ 2 ∧ rowTier w = 0)) :
    baseRow m w = (0, 0) ∧ baseTbl m w = (0, 0) ∧ solRow m w = (0, 0) ∧ solTbl m w = (0, 0) := by
  simp only [baseRow, baseTbl, solRow, solTbl, ht, ite_false, and_self]

section move
variable {p : Prog} (h0 : p.lookup "index_to_solution" = some indexToSolutionL)
  (ha : p.lookup "sd_move_a" = some sdMoveAL) (hs : p.lookup "sd_move_s" = some sdMoveSL)
  (hn : p.lookup "sd_move_n" = some sdMoveNL)
include h0 ha hs hn

/-- **`index_to_solution(cnt)` moves the solution's index**: after the solution's
`build_index(cnt)` (its index `I`, `IndexR`, every key a persistent name below its tag's count,
`IndexKeysIn`; `cnt` its records), with the solution's rows empty and as long as the stream rows,
a returning run leaves the solution's index part of `SolR` at `I`, the stream index empty (what
`build_index` starts from), and changes only the row arrays and `CTL[225]`, `CTL[226]`, `CTL[128]`. -/
theorem indexToSolution_ref {n : Nat} {cnt : Word} {m m' : Mem} {r : List Word} {I : IStreamIndex}
    (hc : callW p n "index_to_solution" [cnt] m = some (r, m'))
    (hI : IndexR m I) (hK : IndexKeysIn m I) (hcnt : I.firsts.size = cnt.toNat)
    (hz : ∀ g ≤ 2, ∀ j, rdN (m.arr64 (sixArr g)) j = 0 ∧ rdN (m.arr64 (stxArr g)) j = 0)
    (hsz : ∀ g ≤ 2, (m.arr64 (sixArr g)).size = (m.arr64 (eixArr g)).size ∧
      (m.arr64 (stxArr g)).size = (m.arr64 (tixArr g)).size)
    (hctl : 228 < (m.arr64 CTL).size) :
    SolIdxR m' I ∧ IndexR m' {} ∧ MemFrame moveA moveC m m' := by
  obtain ⟨s', hs', -, hw⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (indexToSolution_specW p h0 n _ cnt) hc
  subst hs'
  rcases n with _ | n
  · simp [indexToSolutionW] at hw
  rw [indexToSolutionW.arm1] at hw
  cases h1 : callW p n "sd_move_a" [] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨ρ1, m1⟩ := q1
  rw [h1, L.Ind.bW_some] at hw
  cases h2 : callW p n "sd_move_s" [] m1 with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨ρ2, m2⟩ := q2
  rw [h2, L.Ind.bW_some] at hw
  cases h3 : callW p n "sd_move_n" [] m2 with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨ρ3, m3⟩ := q3
  rw [h3, L.Ind.bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨-, hM⟩ := hw
  obtain ⟨t1, e1, -, w1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (sdMoveA_specW p ha n _) h1
  obtain ⟨t2, e2, -, w2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩) (sdMoveS_specW p hs n _) h2
  obtain ⟨t3, e3, -, w3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩) (sdMoveN_specW p hn n _) h3
  rw [e1] at w1; rw [e2] at w2; rw [e3] at w3
  simp only at w1 w2 w3
  rw [← hM]
  generalize hM' : ((m3.set64 (↑CTL) SNEXTC (rdW (m3.arr64 ↑CTL) 128)).set64 (↑CTL) SCNTC cnt).set64 (↑CTL) 128 0 = M
  have T0 := sdMoveA_tag w1 (hsz 0 (by decide))
  have T1 := sdMoveS_tag w2 (by rw [T0.size, T0.size, T0.size, T0.size]; exact hsz 1 (by decide))
  have T2 := sdMoveN_tag w3 (by
    rw [T1.size, T1.size, T1.size, T1.size, T0.size, T0.size, T0.size, T0.size]; exact hsz 2 (by decide))
  have c1 := T0.ctlEq; have c2 := T1.ctlEq; have c3 := T2.ctlEq
  have hMa : ∀ b : TieredArray, b ≠ CTL → M.arr64 b = m3.arr64 b := fun b h => by
    rw [← hM', Mem.arr64_set64_ne _ _ _ _ _ h, Mem.arr64_set64_ne _ _ _ _ _ h, Mem.arr64_set64_ne _ _ _ _ _ h]
  have hsM : ∀ b, (M.arr64 b).size = (m.arr64 b).size := fun b => by
    rw [← hM', size_set64_any, size_set64_any, size_set64_any, T2.size, T1.size, T0.size]
  have hc3 : (m3.arr64 CTL) = m.arr64 CTL := c3.trans (c2.trans c1)
  have hMc : ∀ x : Word, rdW (M.arr64 CTL) x =
      if x = 128 then 0 else if x = SCNTC then cnt else if x = SNEXTC then rdW (m.arr64 CTL) 128
      else rdW (m.arr64 CTL) x := fun x => by
    rw [← hM']
    simp only [rdW_set64, size_set64_any, hc3]
    have : (128 : Word).toNat < (m.arr64 CTL).size := by simp; omega
    have : SCNTC.toNat < (m.arr64 CTL).size := by simp [SCNTC]; omega
    have : SNEXTC.toNat < (m.arr64 CTL).size := by simp [SNEXTC]; omega
    by_cases a1 : x = 128 <;> by_cases a2 : x = SCNTC <;> by_cases a3 : x = SNEXTC <;>
      simp_all [eq_comm, SCNTC, SNEXTC]
  have D0 : TagDone m M 0 := T0.done fun b hb => by
    rw [hMa b (ctl_ne_tag 0 b hb), T2.keep (by decide) (by decide) (by decide) b hb,
      T1.keep (by decide) (by decide) (by decide) b hb]
  have D1 : TagDone m M 1 := (T1.done fun b hb => by
    rw [hMa b (ctl_ne_tag 1 b hb), T2.keep (by decide) (by decide) (by decide) b hb]).congr
    (fun b hb => T0.keep (by decide) (by decide) (by decide) b hb) c1
  have D2 : TagDone m M 2 := (T2.done fun b hb => hMa b (ctl_ne_tag 2 b hb)).congr
    (fun b hb => by rw [T1.keep (by decide) (by decide) (by decide) b hb,
      T0.keep (by decide) (by decide) (by decide) b hb]) (c2.trans c1)
  have hD : ∀ g ≤ 2, TagDone m M g := fun g hg => by
    rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl
    · exact D0
    · exact D1
    · exact D2
  have hO : ∀ b, b ∉ moveA → b ≠ CTL → M.arr64 b = m.arr64 b := fun b hb hb' => by
    have nt : ∀ g ≤ 2, ∀ b' ∈ tagArrs g, b ≠ b' := fun g hg b' hb'' e => hb (e ▸ tag_mem_moveA hg hb'')
    rw [hMa b hb', T2.other b (nt 2 (by decide) _ (by simp [tagArrs])) (nt 2 (by decide) _ (by simp [tagArrs]))
      (nt 2 (by decide) _ (by simp [tagArrs])) (nt 2 (by decide) _ (by simp [tagArrs])),
      T1.other b (nt 1 (by decide) _ (by simp [tagArrs])) (nt 1 (by decide) _ (by simp [tagArrs]))
      (nt 1 (by decide) _ (by simp [tagArrs])) (nt 1 (by decide) _ (by simp [tagArrs])),
      T0.other b (nt 0 (by decide) _ (by simp [tagArrs])) (nt 0 (by decide) _ (by simp [tagArrs]))
      (nt 0 (by decide) _ (by simp [tagArrs])) (nt 0 (by decide) _ (by simp [tagArrs]))]
  have hF : MemFrame moveA moveC m M := ⟨hO, fun x hx => by
    rw [hMc]; simp only [moveC, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [hx.1, hx.2.1, hx.2.2], hsM⟩
  have hP : erecP M = erecP m := erecP_congr' (hO _ (by decide) (by decide)) (hO _ (by decide) (by decide))
    (hF.ctl 129 (by decide)) (hF.ctl 130 (by decide))
  -- the rows, name by name
  have kR : ∀ x : NIdx, (solRow M x.word.toUInt64).1 = (baseRow m x.word.toUInt64).1 ∧
      ((baseRow m x.word.toUInt64).1 ≠ 0 → solRow M x.word.toUInt64 = baseRow m x.word.toUInt64) ∧
      (solTbl M x.word.toUInt64).1 = (baseTbl m x.word.toUInt64).1 ∧
      ((baseTbl m x.word.toUInt64).1 ≠ 0 → solTbl M x.word.toUInt64 = baseTbl m x.word.toUInt64) ∧
      (baseRow M x.word.toUInt64).1 = 0 ∧ (baseTbl M x.word.toUInt64).1 = 0 := fun x => by
    by_cases ht : rowTag x.word.toUInt64 ≤ 2 ∧ rowTier x.word.toUInt64 = 0
    · rw [solRow_after hD hz ht, solTbl_after hD hz ht, baseRow_after hD ht, baseTbl_after hD ht]
      by_cases hi : (idxW x.word.toUInt64).toNat < nmCnt m (rowTag x.word.toUInt64)
      · simp [hi]
      · have := baseRow_out hI hK x ht.1 hi
        simp [hi, this.1, this.2]
    · have a := row_off (m := m) ht; have b := row_off (m := M) ht
      simp [a.1, a.2.1, b.1, b.2.1, b.2.2.1, b.2.2.2]
  refine ⟨⟨fun x => ?_, fun x => ?_, ?_, ?_, fun w => ?_⟩, ⟨fun x => ?_, fun x => ?_, fun i hi => ?_, ?_, ?_,
    fun w hw => ?_⟩, hF⟩
  · obtain ⟨k1, k2, -⟩ := kR x
    rw [hP]
    by_cases b0 : (baseRow m x.word.toUInt64).1 = 0
    · have := hI.base x; rw [ite_eq_left b0] at this; rw [this, k1, ite_eq_left b0]
    · rw [k2 b0]; exact hI.base x
  · obtain ⟨-, -, k1, k2, -⟩ := kR x
    rw [hP]
    by_cases b0 : (baseTbl m x.word.toUInt64).1 = 0
    · have := hI.btbl x; rw [ite_eq_left b0] at this; rw [this, k1, ite_eq_left b0]
    · rw [k2 b0]; exact hI.btbl x
  · simp only [ctlW, hMc]; simp [SNEXTC]; exact hI.next
  · simp only [ctlW, hMc]; simp [SCNTC]; exact hcnt.symm
  · by_cases ht : rowTag w ≤ 2 ∧ rowTier w = 0
    · rw [solRow_after hD hz ht, solTbl_after hD hz ht]
      by_cases hi : (idxW w).toNat < nmCnt m (rowTag w)
      · simp only [hi, ite_true]; exact moved_lt hD ht hi
      · simp [hi]
    · have b := row_off (m := M) ht; simp [b.2.2.1, b.2.2.2]
  · obtain ⟨-, -, -, -, k5, -⟩ := kR x; simp [k5]
  · obtain ⟨-, -, -, -, -, k6⟩ := kR x; simp [k6]
  · simp at hi
  · simp
  · simp only [hMc]; simp
  · by_cases ht : rowTag w ≤ 2 ∧ rowTier w = 0
    · rw [baseRow_after hD ht]
      split
      · simp
      · exact hI.rows w hw
    · have b := row_off (m := M) ht; simp [b.1]

end move

end L.Arena
