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
    · rw [if_pos hi] at h
      split at h; · cases h
      split at h; · cases h
      rename_i hE hT
      have e : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add]; have := UInt64.lt_iff_toNat_lt.mp hi; have := UInt64.toNat_lt N
        simp; omega
      exact ih _ _ _ (by rw [e]; exact hI.step hd hsz hE hT) (UInt64.le_iff_toNat_le.mpr (by rw [e]; have := UInt64.lt_iff_toNat_lt.mp hi; omega)) h
    · rw [if_neg hi] at h; cases h
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
    {k : Nat} (hc : ¬ 134217728 < rdW (m.arr64 CTL) (UInt64.ofNat (nmCS g).ca.toNat))
    (h : F k m 0 (rdW (m.arr64 CTL) (UInt64.ofNat (nmCS g).ca.toNat) <<< 1) = some m') :
    MvTag m m' g := by
  have := mvLoop_ok hF hd hsz k m 0 m' (MvInv.start _ _ _ _ m) (UInt64.zero_le) h
  unfold MvTag mvLen nmCnt; rw [← shl1_toNat hc]; exact this

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

end L.Arena
