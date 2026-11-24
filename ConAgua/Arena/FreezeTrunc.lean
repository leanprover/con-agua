module

import ConAgua.Arena.FreezeTruncArena
import ConAgua.Arena.FreezeTruncKeep
import ConAgua.Front.ApplyDeclRefine
public import ConAgua.Arena.Jobs
public import ConAgua.Arena.FreezeTruncBase
public import ConRon.Bridge.Checker.StreamIndex

@[expose] public section

/-!
# The truncation theorem (lane parmode, docs/design/parmode.md, "Redesign", "Step 4")

`PhaseBStart.trunc`: what phase A leaves for phase B survives cutting every frozen array to its
extent (`truncFrozen`). Each relation reads a frozen array only below its extent: a store's
tier-0 records below `count₀ · w`, its slot table within `2 + 2 n` (`FreezeTruncStore.lean`),
the columns below `count₀`, the pool below its top (`FreezeTruncArena.lean`), `PINS` below 71,
`EREC` below `CTL[129]` (`erecP`), `PEND` below `3 CTL[130]`, the env index's tier-0 rows below
`2 · (name count)`, and the relations over the other arrays read nothing that changes
(`FreezeTruncKeep.lean`).

Three facts the truncation needs are invariants of the library relations: a frozen slot table
sits at word 2 (tier 0's offset word is `0`, `TierLay`; the extent `2 + 2 n` assumes it), `PoolOK`
bounds the saved tier-0 top `PT0[0]` by `POOL`'s size only while the top is in tier 1 (`POOL` is
cut to the top), and `PendR` bounds the pending count by `2^62` (so `PEND`'s extent `3 · CTL[130]`
does not wrap). `EnvKeysIn m fe` (every name the environment indexes, in its constant index and its table map, is a tier-0 name below its
table's count, which `EnvR` does not say) follows from the twin's invariant (`envKeysIn_of`), and
the scratch flag `CTL[1] = 0` (so the pool top is in tier 0) from `TwinPend.off`.
`PhaseBStart.trunc'` is the theorem without hypotheses.
-/

namespace L.Arena

open ConRon.Arena

/-! ## The pins -/

theorem PinsR.trunc {m : Mem} {p : Pins} (h : PinsR m p) : PinsR (truncFrozen m) p := by
  have hw : ∀ i, i < 73 → pinW (truncFrozen m) i = pinW m i := fun i hi => by
    simp only [pinW, truncFrozen_pins, Array.getElem?_extract, Nat.zero_add]
    by_cases h2 : i < (m.arr64 PINS).size <;> simp [hi, h2, Nat.lt_min]
  refine ⟨fun h0 => ?_⟩
  have hf := h.full (by rwa [← hw 0 (by decide)])
  refine ⟨by rw [truncFrozen_pins, size_extract0]; have := hf.size; omega, hf.names_size,
    fun i hi => by rw [hw _ (by omega)]; exact hf.names_lt i hi,
    fun i hi => by rw [hw _ (by omega)]; exact hf.names i hi,
    by rw [hw _ (by decide)]; exact hf.quotMk_lt, by rw [hw _ (by decide)]; exact hf.quotMk,
    by rw [hw _ (by decide), hw _ (by decide), hw _ (by decide)]; exact hf.lv_lt,
    by rw [hw _ (by decide)]; exact hf.emptyLevels, by rw [hw _ (by decide)]; exact hf.zeroLevel,
    by rw [hw _ (by decide)]; exact hf.sortOne,
    fun i hi => by rw [hw _ (by omega)]; exact hf.reserved_lt i hi, ?_,
    by rw [hw _ (by decide)]; exact hf.maxNatSize⟩
  rw [hf.reserved]
  apply List.map_congr_left
  intro i hi
  rw [hw _ (by simp at hi; omega)]

/-! ## The record pool -/

theorem erTop_trunc (m : Mem) : erTop (truncFrozen m) = erTop m := by
  simp only [erTop, truncFrozen_ctl]

theorem erecP_trunc (m : Mem) : erecP (truncFrozen m) = erecP m := by
  funext i
  have h1 : erecTop1 (truncFrozen m) = erecTop1 m := by simp only [erecTop1, truncFrozen_ctl]
  have h2 : (truncFrozen m).arr64 (tier1 EREC) = m.arr64 (tier1 EREC) :=
    truncFrozen_other m _ (by decide)
  simp only [erecP, erTop_trunc, h1, h2, truncFrozen_erec]
  split
  · split
    · split
      · rename_i h3
        simp only [Array.getElem?_extract, Nat.zero_add]
        by_cases h4 : i % 2 ^ 40 < (m.arr64 EREC).size <;> simp [h3, h4, Nat.lt_min]
      · rfl
    · rfl
  · rfl

theorem rdW_erec_trunc (m : Mem) {x : Word} (hx : x.toNat < erTop m) :
    rdW ((truncFrozen m).arr64 EREC) x = rdW (m.arr64 EREC) x := by
  rw [truncFrozen_erec]; exact rdW_extract _ hx

theorem IWOK.trunc {m : Mem} (h : L.Ind.IWOK m) : L.Ind.IWOK (truncFrozen m) := by
  have hI : (truncFrozen m).arr64 L.Ind.IW = m.arr64 L.Ind.IW := truncFrozen_other m _ (by decide)
  have hE1 : (truncFrozen m).arr64 (tier1 EREC) = m.arr64 (tier1 EREC) :=
    truncFrozen_other m _ (by decide)
  have he : ((truncFrozen m).arr64 EREC).size = min (erTop m) (m.arr64 EREC).size := by
    rw [truncFrozen_erec, size_extract0]
  have h0 := (L.Ind.IWOK_iff m).1 h
  simp only [L.Ind.IWOK_iff, L.Ind.iwTop, erTop, erecTop1, hI, hE1, truncFrozen_ctl, he] at h0 ⊢
  simp only [erTop] at he ⊢
  omega

theorem PinSetsR.trunc {m : Mem} {ips : List INatOpPinSet} (h : L.Rom.PinSetsR m ips) :
    L.Rom.PinSetsR (truncFrozen m) ips := by
  obtain ⟨h1, h2, h3⟩ := h
  have hc := truncFrozen_ctl m
  have ht := L.Ind.erTop_lt m
  refine ⟨by rw [hc]; exact h1, by rw [hc, erTop_trunc]; exact h2, fun k hk => ?_⟩
  rw [hc, rdW_erec_trunc m (by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]; omega)]
  refine L.Rom.PinSetR.keep (h3 k hk) ⟨Nat.le_of_eq (erTop_trunc m).symm, fun i hi => ?_⟩
  rw [truncFrozen_erec]
  simp only [Array.getElem?_extract, Nat.zero_add]
  by_cases h2 : i < (m.arr64 EREC).size <;> simp [hi, h2, Nat.lt_min]

/-! ## The stream index -/

/-- The name table with tag `g` (`anonymous`, `str`, `num`). -/
def nmCS : Nat → ConsSch
  | 0 => nanonCS
  | 1 => nstrCS
  | _ => nnumCS

/-- The tier-0 name count of the name table with tag `g` (`anonymous`, `str`, `num`). -/
def nmCnt (m : Mem) (g : Nat) : Nat := (rdW (m.arr64 CTL) (UInt64.ofNat (nmCS g).ca.toNat)).toNat

theorem getD_extract' (a : Array Word) (e i : Nat) :
    (a.extract 0 e)[i]?.getD 0 = if i < e then a[i]?.getD 0 else 0 := by
  split
  · exact getD_extract a (by assumption)
  · rename_i h
    simp only [Array.getElem?_extract, Nat.sub_zero, Nat.zero_add]
    split
    · omega
    · rfl

theorem rdN_extract (a : Array Word) (e i : Nat) :
    rdN (a.extract 0 e) i = if i < e then rdN a i else 0 := getD_extract' a e i

section idx
variable {m : Mem} (hcnt : ∀ g, g ≤ 2 → nmCnt m g ≤ 2 ^ 27)
include hcnt

omit hcnt in
theorem two_mul_toNat {c : Word} (hc : c.toNat ≤ 2 ^ 27) : (2 * c).toNat = 2 * c.toNat := by
  rw [UInt64.toNat_mul]; simp; omega

/-- A tier-0 row array of the stream index under the truncation. -/
theorem eix_trunc (g : Nat) (hg : g ≤ 2) :
    (truncFrozen m).arr64 (eixArr g) = (m.arr64 (eixArr g)).extract 0 (2 * nmCnt m g) := by
  rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl
  · rw [show eixArr 0 = EIXA from rfl, truncFrozen_eixa]
    exact congrArg _ (two_mul_toNat (hcnt 0 (by decide)))
  · rw [show eixArr 1 = EIXS from rfl, truncFrozen_eixs]
    exact congrArg _ (two_mul_toNat (hcnt 1 (by decide)))
  · rw [show eixArr 2 = EIXN from rfl, truncFrozen_eixn]
    exact congrArg _ (two_mul_toNat (hcnt 2 (by decide)))

/-- A tier-0 table-row array of the stream index under the truncation. -/
theorem tix_trunc (g : Nat) (hg : g ≤ 2) :
    (truncFrozen m).arr64 (tixArr g) = (m.arr64 (tixArr g)).extract 0 (2 * nmCnt m g) := by
  rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl
  · rw [show tixArr 0 = TIXA from rfl, truncFrozen_tixa]
    exact congrArg _ (two_mul_toNat (hcnt 0 (by decide)))
  · rw [show tixArr 1 = TIXS from rfl, truncFrozen_tixs]
    exact congrArg _ (two_mul_toNat (hcnt 1 (by decide)))
  · rw [show tixArr 2 = TIXN from rfl, truncFrozen_tixn]
    exact congrArg _ (two_mul_toNat (hcnt 2 (by decide)))

theorem baseRow_trunc (w : Word) :
    ((baseRow (truncFrozen m) w).1 = (baseRow m w).1 ∨ (baseRow (truncFrozen m) w).1 = 0) ∧
    (rowTier w = 0 → (idxW w).toNat < nmCnt m (rowTag w) → baseRow (truncFrozen m) w = baseRow m w) := by
  unfold baseRow
  by_cases hg : rowTag w ≤ 2 ∧ rowTier w = 0
  · simp only [hg, and_self, ↓reduceIte]
    rw [eix_trunc hcnt _ hg.1, rdN_extract, rdN_extract]
    refine ⟨by split <;> simp, fun _ hr => ?_⟩
    simp only [rowIx] at *
    simp only [show 2 * (idxW w).toNat < 2 * nmCnt m (rowTag w) by omega,
      show 2 * (idxW w).toNat + 1 < 2 * nmCnt m (rowTag w) by omega, ↓reduceIte]
  · simp only [hg, ↓reduceIte, or_self, true_and]
    intro _ _; trivial

theorem baseTbl_trunc (w : Word) :
    ((baseTbl (truncFrozen m) w).1 = (baseTbl m w).1 ∨ (baseTbl (truncFrozen m) w).1 = 0) ∧
    (rowTier w = 0 → (idxW w).toNat < nmCnt m (rowTag w) → baseTbl (truncFrozen m) w = baseTbl m w) := by
  unfold baseTbl
  by_cases hg : rowTag w ≤ 2 ∧ rowTier w = 0
  · simp only [hg, and_self, ↓reduceIte]
    rw [tix_trunc hcnt _ hg.1, rdN_extract, rdN_extract]
    refine ⟨by split <;> simp, fun _ hr => ?_⟩
    simp only [rowIx] at *
    simp only [show 2 * (idxW w).toNat < 2 * nmCnt m (rowTag w) by omega,
      show 2 * (idxW w).toNat + 1 < 2 * nmCnt m (rowTag w) by omega, ↓reduceIte]
  · simp only [hg, ↓reduceIte, or_self, true_and]
    intro _ _; trivial

/-! ### The solution's rows (`SIX*`, `STX*`, `MAT*`, frozen on a compared run, `CTL[cmpCW] = 1`) -/

omit hcnt in
theorem solArr_mem (g : Nat) (hg : g ≤ 2) :
    (sixArr g, (⟨sixArr g, fzSolExt (nmCS g).ca.toNat⟩ : Fz)) ∈ frozen.drop 1 ∧
    (stxArr g, (⟨stxArr g, fzSolExt (nmCS g).ca.toNat⟩ : Fz)) ∈ frozen.drop 1 ∧
    (matArr g, (⟨matArr g, fzSolExt (nmCS g).ca.toNat⟩ : Fz)) ∈ frozen.drop 1 := by
  rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_⟩ <;> (rw [frozen_drop1]; simp [sixArr, stxArr, matArr, nmCS])

/-- The solution's row arrays of tag `g` under the truncation, with the flag on. -/
theorem sol_trunc (hf : rdW (m.arr64 CTL) (UInt64.ofNat cmpCW) = 1) (g : Nat) (hg : g ≤ 2) :
    (truncFrozen m).arr64 (sixArr g) = (m.arr64 (sixArr g)).extract 0 (2 * nmCnt m g) ∧
    (truncFrozen m).arr64 (stxArr g) = (m.arr64 (stxArr g)).extract 0 (2 * nmCnt m g) ∧
    (truncFrozen m).arr64 (matArr g) = (m.arr64 (matArr g)).extract 0 (2 * nmCnt m g) := by
  obtain ⟨h1, h2, h3⟩ := solArr_mem g hg
  have e := two_mul_toNat (hcnt g hg)
  exact ⟨by rw [truncFrozen_sol m h1 hf, e]; rfl, by rw [truncFrozen_sol m h2 hf, e]; rfl,
    by rw [truncFrozen_sol m h3 hf, e]; rfl⟩

omit hcnt in
/-- A two-word row of `A` at name handle `w` (`rdN A (rowIx w)`, `rdN A (rowIx w + 1)`), cut to
`2 · c` words: the row, or zeros; the row itself below the count. -/
theorem row_extract (A : Array Word) (c : Nat) (w : Word) :
    ((rdN (A.extract 0 (2 * c)) (rowIx w), rdN (A.extract 0 (2 * c)) (rowIx w + 1)) =
        (rdN A (rowIx w), rdN A (rowIx w + 1)) ∨
      (rdN (A.extract 0 (2 * c)) (rowIx w), rdN (A.extract 0 (2 * c)) (rowIx w + 1)) = (0, 0)) ∧
    ((idxW w).toNat < c →
      (rdN (A.extract 0 (2 * c)) (rowIx w), rdN (A.extract 0 (2 * c)) (rowIx w + 1)) =
        (rdN A (rowIx w), rdN A (rowIx w + 1))) := by
  rw [rdN_extract, rdN_extract]
  simp only [rowIx]
  refine ⟨?_, fun h => ?_⟩
  · by_cases h : 2 * (idxW w).toNat < 2 * c
    · left; simp only [h, show 2 * (idxW w).toNat + 1 < 2 * c by omega, ↓reduceIte]
    · right; simp only [h, show ¬ 2 * (idxW w).toNat + 1 < 2 * c by omega, ↓reduceIte]
  · simp only [show 2 * (idxW w).toNat < 2 * c by omega,
      show 2 * (idxW w).toNat + 1 < 2 * c by omega, ↓reduceIte]

theorem solRow_trunc (hf : rdW (m.arr64 CTL) (UInt64.ofNat cmpCW) = 1) (w : Word) :
    (solRow (truncFrozen m) w = solRow m w ∨ solRow (truncFrozen m) w = (0, 0)) ∧
    (rowTier w = 0 → (idxW w).toNat < nmCnt m (rowTag w) → solRow (truncFrozen m) w = solRow m w) := by
  unfold solRow
  by_cases hg : rowTag w ≤ 2 ∧ rowTier w = 0
  · simp only [hg, and_self, ↓reduceIte]
    rw [(sol_trunc hcnt hf _ hg.1).1]
    exact ⟨(row_extract _ _ w).1, fun _ => (row_extract _ _ w).2⟩
  · simp only [hg, ↓reduceIte, or_self, true_and]
    intro _ _; trivial

theorem solTbl_trunc (hf : rdW (m.arr64 CTL) (UInt64.ofNat cmpCW) = 1) (w : Word) :
    (solTbl (truncFrozen m) w = solTbl m w ∨ solTbl (truncFrozen m) w = (0, 0)) ∧
    (rowTier w = 0 → (idxW w).toNat < nmCnt m (rowTag w) → solTbl (truncFrozen m) w = solTbl m w) := by
  unfold solTbl
  by_cases hg : rowTag w ≤ 2 ∧ rowTier w = 0
  · simp only [hg, and_self, ↓reduceIte]
    rw [(sol_trunc hcnt hf _ hg.1).2.1]
    exact ⟨(row_extract _ _ w).1, fun _ => (row_extract _ _ w).2⟩
  · simp only [hg, ↓reduceIte, or_self, true_and]
    intro _ _; trivial

theorem matRow_trunc (hf : rdW (m.arr64 CTL) (UInt64.ofNat cmpCW) = 1) (w : Word) :
    (matRow (truncFrozen m) w = matRow m w ∨ matRow (truncFrozen m) w = (0, 0)) ∧
    (rowTier w = 0 → (idxW w).toNat < nmCnt m (rowTag w) → matRow (truncFrozen m) w = matRow m w) := by
  unfold matRow
  by_cases hg : rowTag w ≤ 2 ∧ rowTier w = 0
  · simp only [hg, and_self, ↓reduceIte]
    rw [(sol_trunc hcnt hf _ hg.1).2.2]
    exact ⟨(row_extract _ _ w).1, fun _ => (row_extract _ _ w).2⟩
  · simp only [hg, ↓reduceIte, or_self, true_and]
    intro _ _; trivial

end idx

/-- The name counts of a related store fit in a handle's index. -/
theorem nmCnt_le {m : Mem} {a : AState} (h : ArenaR m a) (g : Nat) (hg : g ≤ 2) :
    nmCnt m g ≤ 2 ^ 27 := by
  rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl
  · have := ConsR.cnt0 h.nanon (ca := nanonCS.ca.toNat) (by decide)
    have := h.nanon.cap 0 (by decide)
    simp only [show nanonCS.wide = false from rfl, capS] at this; simp at this
    unfold nmCnt; simp only [nmCS]; omega
  · have := ConsR.cnt0 h.nstr (ca := nstrCS.ca.toNat) (by decide)
    have := h.nstr.cap 0 (by decide)
    simp only [show nstrCS.wide = false from rfl, capS] at this; simp at this
    unfold nmCnt; simp only [nmCS]; omega
  · have := ConsR.cnt0 h.nnum (ca := nnumCS.ca.toNat) (by decide)
    have := h.nnum.cap 0 (by decide)
    simp only [show nnumCS.wide = false from rfl, capS] at this; simp at this
    unfold nmCnt; simp only [nmCS]; omega

theorem denoteN_view {st : NStore} {n : NIdx} {x : ConLeche.Name} (h : denoteN st n = some x) :
    (st.view n).isSome := by
  unfold denoteN at h
  rw [denoteNAux] at h
  cases e : st.view n with
  | none => rw [e] at h; simp at h
  | some _ => rfl

/-- A persistent name handle that denotes is a tier-0 name below its table's count. -/
theorem nameIn_of {m : Mem} {a : AState} (hR : ArenaR m a) {n : NIdx} {nm : ConLeche.Name}
    (hper : n.isPersistent = true) (hdn : denoteN a.store.ns n = some nm)
    (hn : rowTag n.word.toUInt64 ≤ 2) :
    rowTier n.word.toUInt64 = 0 ∧ (idxW n.word.toUInt64).toNat < nmCnt m (rowTag n.word.toUInt64) := by
  have hv := denoteN_view hdn
  simp only [NStore.view, hper, ↓reduceIte, EStore.ns, NTables.get] at hv
  have hw : n.word.toUInt64.toNat < 2 ^ 32 := by have := n.word.toNat_lt; simpa using this
  have hnr := rowTag_narrow hn
  have htier : rowTier n.word.toUInt64 = 0 := by
    have hp := decI_pers (k := .name) n.word.toUInt64 hw
    rw [decI_word, hper] at hp
    have : tierW n.word.toUInt64 = 0 := by simpa using hp.symm
    rw [← tierW_toNat_row, this]; rfl
  have htag : ∀ g : UInt32, n.tag = g → rowTag n.word.toUInt64 = g.toNat := fun g e => by
    have ht := decI_tag (k := .name) n.word.toUInt64 hw
    rw [decI_word, e] at ht
    have hl := rowTag_lt n.word.toUInt64
    rw [ht]; simp only [rowTag, UInt64.toNat_toUInt32] at hl ⊢; omega
  have hidx : n.idxNat = (idxW n.word.toUInt64).toNat := by
    have := decI_idx (k := .name) n.word.toUInt64 hnr
    rwa [decI_word] at this
  refine ⟨htier, ?_⟩
  by_cases h0 : n.tag == NTag.anonymous
  · simp only [h0, ↓reduceIte, Option.isSome_map] at hv
    have e := htag _ (beq_iff_eq.mp h0)
    have hl := (Option.isSome_iff_exists.mp hv).choose_spec
    have hlt := (Array.getElem?_eq_some_iff.mp hl).1
    have hcnt := ConsR.cnt0 hR.nanon (ca := nanonCS.ca.toNat) (by decide)
    rw [e]; simp only [nmCnt, nmCS, NTag.anonymous, UInt32.toNat_zero] at hcnt ⊢
    rw [hidx] at hlt; omega
  by_cases h1 : n.tag == NTag.str
  · simp only [h0, h1, ↓reduceIte, Option.isSome_map, Bool.false_eq_true] at hv
    have e := htag _ (beq_iff_eq.mp h1)
    have hl := (Option.isSome_iff_exists.mp hv).choose_spec
    have hlt := (Array.getElem?_eq_some_iff.mp hl).1
    have hcnt := ConsR.cnt0 hR.nstr (ca := nstrCS.ca.toNat) (by decide)
    rw [e]; simp only [nmCnt, nmCS, NTag.str] at hcnt ⊢
    rw [hidx] at hlt; simp at hcnt ⊢; omega
  by_cases h2 : n.tag == NTag.num
  · simp only [h0, h1, h2, ↓reduceIte, Option.isSome_map, Bool.false_eq_true] at hv
    have e := htag _ (beq_iff_eq.mp h2)
    have hl := (Option.isSome_iff_exists.mp hv).choose_spec
    have hlt := (Array.getElem?_eq_some_iff.mp hl).1
    have hcnt := ConsR.cnt0 hR.nnum (ca := nnumCS.ca.toNat) (by decide)
    rw [e]; simp only [nmCnt, nmCS, NTag.num] at hcnt ⊢
    rw [hidx] at hlt; simp at hcnt ⊢; omega
  · simp [h0, h1, h2] at hv

/-- **Every key of the stream index's base is a tier-0 name below its table's count**: the keys
denote (`IndexDenotes`) and are persistent (`PersIFBase`). -/
structure IndexKeysIn (m : Mem) (I : IStreamIndex) : Prop where
  idx : ∀ (n : NIdx) p, I.base.idx[n]? = some p → rowTag n.word.toUInt64 ≤ 2 →
    rowTier n.word.toUInt64 = 0 ∧ (idxW n.word.toUInt64).toNat < nmCnt m (rowTag n.word.toUInt64)
  tbls : ∀ (n : NIdx) p, I.base.tbls[n]? = some p → rowTag n.word.toUInt64 ≤ 2 →
    rowTier n.word.toUInt64 = 0 ∧ (idxW n.word.toUInt64).toNat < nmCnt m (rowTag n.word.toUInt64)

theorem indexKeysIn_of {m : Mem} {a : AState} {I : IStreamIndex}
    {J : ConLeche.Cached.StreamIndex} (hR : ArenaR m a) (hI : ConRon.Bridge.IndexDenotes a.store I J)
    (hP : ConRon.Bridge.PersIFBase I.base) : IndexKeysIn m I where
  idx n p hp hn := by
    obtain ⟨nm, -, hdn, -⟩ := hI.idxHit n p hp
    exact nameIn_of hR (hP.idx n p hp).1 hdn hn
  tbls n p hp hn := by
    obtain ⟨nm, -, hdn, -⟩ := hI.tblHit n p hp
    exact nameIn_of hR (hP.tbls n p hp).1 hdn hn

/-- **The stream index survives the truncation**: its rows are below the name counts, `FIRSTS`
below the record count, `CTL` kept. -/
theorem IndexR.trunc {m : Mem} {I : IStreamIndex} (hcnt : ∀ g, g ≤ 2 → nmCnt m g ≤ 2 ^ 27)
    (hk : IndexKeysIn m I) (hD : (rdW (m.arr64 L.Front.DECL) 0).toNat = I.firsts.size)
    (hx : (rdW (m.arr64 L.Front.DECL) 0).toNat ≤ (xD m).toNat)
    (h : IndexR m I) : IndexR (truncFrozen m) I := by
  have he := erecP_trunc m
  refine ⟨fun n => ?_, fun n => ?_, fun i hi => ?_, ?_, by rw [truncFrozen_ctl]; exact h.next,
    fun x hx => ?_⟩
  rotate_right
  · rcases (baseRow_trunc hcnt x).1 with e' | e'
    · rw [e']; exact h.rows x hx
    · rw [e']; decide
  · cases e : I.base.idx[n]? with
    | none =>
      have h0 := h.base n
      rw [e] at h0
      have h1 : (baseRow m n.word.toUInt64).1 = 0 := by
        split at h0
        · assumption
        · simp at h0
      have h2 : (baseRow (truncFrozen m) n.word.toUInt64).1 = 0 := by
        rcases (baseRow_trunc hcnt n.word.toUInt64).1 with e' | e'
        · rw [e']; exact h1
        · exact e'
      simp [h2]
    | some p =>
      have hg : rowTag n.word.toUInt64 ≤ 2 := by
        refine Decidable.byContradiction fun hg => ?_
        have h0 := h.base n
        rw [e] at h0
        simp [baseRow, hg] at h0
      obtain ⟨ht, hl⟩ := hk.idx n p e hg
      rw [(baseRow_trunc hcnt _).2 ht hl, he, ← e]; exact h.base n
  · cases e : I.base.tbls[n]? with
    | none =>
      have h0 := h.btbl n
      rw [e] at h0
      have h1 : (baseTbl m n.word.toUInt64).1 = 0 := by
        split at h0
        · assumption
        · simp at h0
      have h2 : (baseTbl (truncFrozen m) n.word.toUInt64).1 = 0 := by
        rcases (baseTbl_trunc hcnt n.word.toUInt64).1 with e' | e'
        · rw [e']; exact h1
        · exact e'
      simp [h2]
    | some p =>
      have hg : rowTag n.word.toUInt64 ≤ 2 := by
        refine Decidable.byContradiction fun hg => ?_
        have h0 := h.btbl n
        rw [e] at h0
        simp [baseTbl, hg] at h0
      obtain ⟨ht, hl⟩ := hk.tbls n p e hg
      rw [(baseTbl_trunc hcnt _).2 ht hl, he, ← e]; exact h.btbl n
  · rw [truncFrozen_firsts, rdW_extract _ (by
      rw [UInt64.toNat_ofNat_of_lt' (by have := h.firstsSize; have := UInt64.toNat_lt (rdW (m.arr64 L.Front.DECL) 0); simp only [UInt64.size]; omega)]; omega)]
    exact h.firsts i hi
  · rw [truncFrozen_firsts, size_extract0]; have := h.firstsSize; omega

/-! ## The front's records -/

theorem trunc_extract (P : Array Word) {e t : Nat} (h : t + 1 ≤ e) :
    L.Front.trunc (P.extract 0 e) t = L.Front.trunc P t := by
  simp only [L.Front.trunc, Array.extract_extract, Nat.zero_add, Nat.min_eq_left h]

theorem DeclsF.extract {D P : Array Word} {ds : Array IDeclaration} (h : L.Front.DeclsF D P ds)
    {eD eP : Nat} (heD : 1 + 8 * ds.size ≤ eD) (heP : (P[0]?.getD 0).toNat + 1 ≤ eP) :
    L.Front.DeclsF (D.extract 0 eD) (P.extract 0 eP) ds := by
  have gD : ∀ j, j < 1 + 8 * ds.size → (D.extract 0 eD)[j]? = D[j]? := fun j hj => get?_extract D (by omega)
  have gP : ∀ j, j < 1 + (P[0]?.getD 0).toNat → (P.extract 0 eP)[j]? = P[j]? :=
    fun j hj => get?_extract P (by omega)
  have hP0 : ((P.extract 0 eP)[0]?.getD 0) = (P[0]?.getD 0) := by rw [gP 0 (by omega)]
  have hroom := h.room
  have hptop := h.ptop
  refine ⟨Nat.lt_of_le_of_lt (by simp; omega) h.dsize, Nat.lt_of_le_of_lt (by simp; omega) h.psize,
    by rw [gD 0 (by omega)]; exact h.count, by simp only [Array.size_extract]; omega,
    by rw [hP0]; simp only [Array.size_extract]; omega, fun i hi => ?_, h.npb⟩
  have hr := h.recs i hi
  have hw : ∀ j, 0 < j → j < 1 + 8 * i + 8 → (D.extract 0 eD)[j]? = D[j]? := fun j _ hj => gD j (by omega)
  generalize ds[i] = d at hr ⊢
  cases d with
  | indDecl b nP =>
    have hw' : ∀ k, k < 8 → L.Front.dw (D.extract 0 eD) i k = L.Front.dw D i k := fun k hk => by
      simp only [L.Front.dw]; rw [hw _ (by omega) (by omega)]
    obtain ⟨a0, a4, t, ht, hdec⟩ := hr
    refine ⟨by rw [hw' 0 (by omega)]; exact a0, by rw [hw' 4 (by omega)]; exact a4, t,
      by rw [hP0]; exact ht, ?_⟩
    rw [hw' 2 (by omega), hw' 3 (by omega), trunc_extract P (by omega)]; exact hdec
  | _ =>
    simp only [L.Front.DeclAtF] at hr ⊢
    exact L.Front.DeclAt_mono D _ P _ i _ hw (fun j _ hj => gP j hj) (by rw [hP0]; exact Nat.le_refl _) hr

/-- **The extents of `FIRSTS`, `DECL`, `DLP` cover the used prefixes** and do not wrap: on a flat
run they are the counts (`ExtOK.flat`), on a compared run the larger of the two phases'. -/
structure ExtOK (m : Mem) : Prop where
  dle : (rdW (m.arr64 L.Front.DECL) 0).toNat ≤ (xD m).toNat
  dlt : (xD m).toNat < 2 ^ 60
  ple : (rdW (m.arr64 L.Front.DLP) 0).toNat ≤ (xP m).toNat
  plt : (xP m).toNat < 2 ^ 63

theorem ExtOK.flat {m : Mem} {ds : Array IDeclaration}
    (h : L.Front.DeclsF (m.arr64 L.Front.DECL) (m.arr64 L.Front.DLP) ds)
    (hcw : rdW (m.arr64 CTL) (UInt64.ofNat cmpCW) = 0) : ExtOK m := by
  have hc := h.count
  have hroom := h.room
  have hds := h.dsize
  have hptop := h.ptop
  have hps := h.psize
  have hr0 : rdW (m.arr64 L.Front.DECL) 0 = ((m.arr64 L.Front.DECL)[0]?.getD 0) := by simp [rdW]
  have hp0 : rdW (m.arr64 L.Front.DLP) 0 = ((m.arr64 L.Front.DLP)[0]?.getD 0) := by simp [rdW]
  have e1 : xD m = rdW (m.arr64 L.Front.DECL) 0 := cmpOrW_off hcw _ _
  have e2 : xP m = rdW (m.arr64 L.Front.DLP) 0 := cmpOrW_off hcw _ _
  refine ⟨by rw [e1]; exact Nat.le_refl _, by rw [e1, hr0]; omega, by rw [e2]; exact Nat.le_refl _,
    by rw [e2, hp0]; omega⟩

theorem DeclsF.trunc {m : Mem} {ds : Array IDeclaration}
    (h : L.Front.DeclsF (m.arr64 L.Front.DECL) (m.arr64 L.Front.DLP) ds) (hx : ExtOK m) :
    L.Front.DeclsF ((truncFrozen m).arr64 L.Front.DECL) ((truncFrozen m).arr64 L.Front.DLP) ds := by
  rw [truncFrozen_decl, truncFrozen_dlp]
  have hc := h.count
  have hd := hx.dle
  have hd' := hx.dlt
  have hp := hx.ple
  have hp' := hx.plt
  have hr0 : rdW (m.arr64 L.Front.DECL) 0 = ((m.arr64 L.Front.DECL)[0]?.getD 0) := by
    simp [rdW]
  have hp0 : rdW (m.arr64 L.Front.DLP) 0 = ((m.arr64 L.Front.DLP)[0]?.getD 0) := by
    simp [rdW]
  rw [hr0] at hd; rw [hp0] at hp
  apply DeclsF.extract h
  · rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  · rw [UInt64.toNat_add]; simp; omega

/-! ## The whole relation -/

theorem ModeOK.trunc {m : Mem} (h : ModeOK m) : ModeOK (truncFrozen m) := by
  unfold ModeOK at *; simp only [Mem.flag, Mem.top, truncFrozen_ctl]; exact h

theorem pinW_trunc (m : Mem) : pinW (truncFrozen m) 0 = pinW m 0 := by
  simp only [pinW, truncFrozen_pins, getD_extract _ (show 0 < 73 by decide)]

theorem TwinMem.trunc {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState}
    (h : TwinMem dn m a) : TwinMem dn (truncFrozen m) a := by
  have hk := keepNF_trunc m
  refine ⟨?_, by rw [hk.arr _ (by decide)]; exact h.spn, by rw [hk.arr _ (by decide)]; exact h.bstk,
    hk.coreMemos h.memos, h.dnN⟩
  rw [truncFrozen_erec, size_extract0]; have := h.erec; omega

theorem envArrs_fz : ∀ b ∈ envArrs, b ∈ fzSrcs → b.arr < 137 ∨ b = EREC := by decide

theorem OwnBelow.trunc {m : Mem} (h : OwnBelow m) : OwnBelow (truncFrozen m) := by
  intro w hw
  have hO : ∀ (b : TieredArray), b ∈ envArrs → 140 ≤ b.arr → (truncFrozen m).arr64 b = m.arr64 b :=
    fun b hb h1 => truncFrozen_other m b (fun hf => by
      rcases envArrs_fz b hb hf with e | e
      · omega
      · subst e; revert h1; decide)
  have hA : ∀ (t : UInt64), 140 ≤ (tierA (oixArr (rowTag w)) t).arr := fun t => by
    unfold tierA oixArr; generalize (t &&& 1 != 0) = b
    cases b <;> split <;> (try split) <;> decide
  have hB : ∀ (t : UInt64), 140 ≤ (tierA (otxArr (rowTag w)) t).arr := fun t => by
    unfold tierA otxArr; generalize (t &&& 1 != 0) = b
    cases b <;> split <;> (try split) <;> decide
  have e1 : ownRow (truncFrozen m) w = ownRow m w := by
    simp only [ownRow, hO _ (tierA_oix_mem _ _) (hA _)]
  have e2 := hO _ (tierA_otx_mem (rowTag w) (tierW w)) (hB _)
  simp only [stampW, truncFrozen_ctl, e1, e2]
  exact h w hw

theorem IndMemos.trunc {m : Mem} (h : IndMemos m) : IndMemos (truncFrozen m) := by
  have hk := keepNF_trunc m
  have hc := truncFrozen_ctl m
  obtain ⟨⟨⟨⟨a1, h1⟩, ⟨a2, h2⟩, ⟨a3, h3⟩, ⟨a4, h4⟩, ⟨M, G, g, hR, hB, hF⟩⟩, ⟨a5, h5⟩, ⟨a6, h6⟩,
    ⟨a7, h7⟩⟩, ⟨a8, h8⟩, hcr⟩ := h
  refine ⟨⟨⟨⟨a1, hk.memoRV (by decide) (fun _ _ h => h) h1⟩, ⟨a2, hk.memoRV (by decide) (fun _ _ h => h) h2⟩,
    ⟨a3, hk.memoRV (by decide) (fun _ _ h => h) h3⟩, ⟨a4, hk.memoRV (by decide) (fun _ _ h => h) h4⟩,
    ⟨M, G, g, hk.memoRV (by decide) (fun _ _ h => h) hR, ?_, hF⟩⟩,
    ⟨a5, hk.memoRV (by decide) (fun _ _ h => h) h5⟩, ⟨a6, hk.memoRV (by decide) (fun _ _ h => h) h6⟩,
    ⟨a7, hk.memoRV (by decide) (fun _ _ h => h) h7⟩⟩, ⟨a8, hk.memoRV (by decide) (fun _ _ h => h) h8⟩,
    hk.crOK hcr⟩
  unfold BankW at *; rw [hc]; exact hB

/-- With the scratch flag off (the twin's `scratchOn` is `false`), the pool top is in tier 0. -/
theorem top_tier0_of {m : Mem} {a : AState} (h : ArenaR m a) (hmode : ModeOK m)
    (hoff : a.store.scratchOn = false) : m.top.toNat < 2 ^ 40 := by
  have hf := h.app.flag
  rw [hoff] at hf
  have h0 : m.flag = 0 := by
    simp only [Mem.flag]
    have : rdW (m.arr64 CTL) 1 = 0 := by simpa using hf
    simpa only [rdW, UInt64.toNat_one] using this
  rcases hmode with h1 | h1
  · exact absurd h0 h1
  · exact h1

/-! ## The run's solution -/

/-- **The solution's keys in the store**: every name its index (constants and tables) and its
mates map hold is a tier-0 name below its table's count (so the solution's rows, frozen as their
prefix of `2 · count` words, keep every row the relation reads). -/
structure SolKeysIn (m : Mem) (J : ISolution) : Prop where
  idx : IndexKeysIn m J.idx
  mates : ∀ (n : NIdx) l, J.mates[n]? = some l → rowTag n.word.toUInt64 ≤ 2 →
    rowTier n.word.toUInt64 = 0 ∧ (idxW n.word.toUInt64).toNat < nmCnt m (rowTag n.word.toUInt64)

/-- A key whose row is in another tag is not in the map: `solRow`, `solTbl`, `matRow` are `(0, 0)`
there. -/
theorem solRow_tag {m : Mem} {w : Word} (hg : ¬ rowTag w ≤ 2) :
    solRow m w = (0, 0) ∧ solTbl m w = (0, 0) ∧ matRow m w = (0, 0) := by
  simp [solRow, solTbl, matRow, hg]

/-- **The solution survives the truncation** (with the flag on and the keys in the store). -/
theorem SolR.trunc {m : Mem} {J : ISolution} (hcnt : ∀ g, g ≤ 2 → nmCnt m g ≤ 2 ^ 27)
    (hf : rdW (m.arr64 CTL) (UInt64.ofNat cmpCW) = 1) (hk : SolKeysIn m J) (h : SolR m J) :
    SolR (truncFrozen m) J := by
  have he := erecP_trunc m
  have hc : ∀ x, ctlW (truncFrozen m) x = ctlW m x := fun x => by simp only [ctlW, truncFrozen_ctl]
  refine ⟨fun n => ?_, fun n => ?_, by rw [hc]; exact h.next, by rw [hc]; exact h.size,
    fun n => ?_, fun w hw => ?_, fun w => ?_⟩
  · cases e : J.idx.base.idx[n]? with
    | none =>
      have h0 := h.base n
      rw [e] at h0
      have h1 : (solRow m n.word.toUInt64).1 = 0 := by
        split at h0
        · assumption
        · simp at h0
      have h2 : (solRow (truncFrozen m) n.word.toUInt64).1 = 0 := by
        rcases (solRow_trunc hcnt hf n.word.toUInt64).1 with e' | e'
        · rw [e']; exact h1
        · rw [e']
      simp [h2]
    | some p =>
      have hg : rowTag n.word.toUInt64 ≤ 2 := by
        refine Decidable.byContradiction fun hg => ?_
        have h0 := h.base n
        rw [e, (solRow_tag hg).1] at h0
        simp at h0
      obtain ⟨ht, hl⟩ := hk.idx.idx n p e hg
      rw [(solRow_trunc hcnt hf _).2 ht hl, he, ← e]; exact h.base n
  · cases e : J.idx.base.tbls[n]? with
    | none =>
      have h0 := h.btbl n
      rw [e] at h0
      have h1 : (solTbl m n.word.toUInt64).1 = 0 := by
        split at h0
        · assumption
        · simp at h0
      have h2 : (solTbl (truncFrozen m) n.word.toUInt64).1 = 0 := by
        rcases (solTbl_trunc hcnt hf n.word.toUInt64).1 with e' | e'
        · rw [e']; exact h1
        · rw [e']
      simp [h2]
    | some p =>
      have hg : rowTag n.word.toUInt64 ≤ 2 := by
        refine Decidable.byContradiction fun hg => ?_
        have h0 := h.btbl n
        rw [e, (solRow_tag hg).2.1] at h0
        simp at h0
      obtain ⟨ht, hl⟩ := hk.idx.tbls n p e hg
      rw [(solTbl_trunc hcnt hf _).2 ht hl, he, ← e]; exact h.btbl n
  · have hml : ∀ w, matRow (truncFrozen m) w = matRow m w → matList (truncFrozen m) w = matList m w :=
      fun w e => by simp only [matList, e, he]
    rw [h.mates n]
    cases e : J.mates[n]? with
    | none =>
      rw [h.mates n] at e
      rcases (matRow_trunc hcnt hf n.word.toUInt64).1 with e' | e'
      · rw [hml _ e', e]
      · rw [e]; simp [matList, e']
    | some l =>
      rw [h.mates n] at e
      have hg : rowTag n.word.toUInt64 ≤ 2 := by
        refine Decidable.byContradiction fun hg => ?_
        simp [matList, (solRow_tag (m := m) hg).2.2] at e
      rw [← h.mates n] at e
      obtain ⟨ht, hl⟩ := hk.mates n l e hg
      rw [hml _ ((matRow_trunc hcnt hf _).2 ht hl), ← h.mates n, e]
  · rcases (matRow_trunc hcnt hf w).1 with e' | e'
    · rw [e'] at hw
      have := h.mates_dec w hw
      simp only [matList, e', he] at this ⊢
      exact this
    · rw [e'] at hw; exact absurd rfl hw
  · obtain ⟨h1, h2⟩ := h.rows w
    refine ⟨?_, ?_⟩
    · rcases (solRow_trunc hcnt hf w).1 with e' | e'
      · rw [e']; exact h1
      · rw [e']; decide
    · rcases (solTbl_trunc hcnt hf w).1 with e' | e'
      · rw [e']; exact h2
      · rw [e']; decide

/-- **The run's solution survives the truncation**: the flag and the walks' memos are not cut, the
solution's rows by `SolR.trunc`. -/
theorem JSol.trunc {m : Mem} {J : Option ISolution} (hcnt : ∀ g, g ≤ 2 → nmCnt m g ≤ 2 ^ 27)
    (hk : ∀ J', J = some J' → SolKeysIn m J' ∧ rdW (m.arr64 CTL) (UInt64.ofNat cmpCW) = 1)
    (h : JSol J m) : JSol J (truncFrozen m) := by
  have hK := keepNF_trunc m
  cases J with
  | none => exact JSol.none (by rw [truncFrozen_ctl]; exact h.sol)
  | some J =>
    obtain ⟨hf, hS⟩ := h.sol
    refine ⟨⟨by simp only [ctlW, truncFrozen_ctl]; exact hf, hS.trunc hcnt (hk J rfl).2 (hk J rfl).1⟩,
      fun J' e => ?_⟩
    obtain ⟨⟨⟨mp, hn⟩, ⟨mq, hc⟩, h1, h2⟩, hnx⟩ := h.walk J' e
    exact ⟨⟨⟨mp, hK.memoRG (by decide) hn⟩, ⟨mq, hK.memoRG (by decide) hc⟩,
      by rw [truncFrozen_ctl]; exact h1, by rw [truncFrozen_ctl]; exact h2⟩, hnx⟩

/-- **The truncation theorem**: the jobs' memory half survives cutting every frozen array to its
extent, given the scratch flag off, the stream index's keys in the store, and the solution's (if
any). -/
theorem JobM.truncJ {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {J : Option ISolution} {I : IStreamIndex} {m : Mem} {a : AState}
    (h : JobM pins dn ds J I m a) (hoff : a.store.scratchOn = false) (hk : IndexKeysIn m I)
    (hx : rdW (m.arr64 CTL) (UInt64.ofNat cmpCW) = 0 ∨ ExtOK m)
    (hs : ∀ J', J = some J' → SolKeysIn m J' ∧ rdW (m.arr64 CTL) (UInt64.ofNat cmpCW) = 1) :
    JobM pins dn ds J I (truncFrozen m) a := by
  have hx' : ExtOK m := hx.elim (ExtOK.flat h.decls) id
  have htop := top_tier0_of h.arena.base h.mode hoff
  have hK := keepNF_trunc m
  have hD : (rdW (m.arr64 L.Front.DECL) 0).toNat = I.firsts.size := by
    rw [h.fsize, ← h.decls.count]; simp [rdW]
  exact ⟨h.arena.trunc htop, hK.coreR h.core, h.pinsR.trunc, h.mode.trunc,
    h.idx.trunc (nmCnt_le h.arena.base) hk hD hx'.dle, h.below.trunc,
    by simp only [stampW, truncFrozen_ctl]; exact h.stamp, DeclsF.trunc h.decls hx', IWOK.trunc h.iw,
    by rw [truncFrozen_ctl]; exact h.top1, PinSetsR.trunc h.pinsets, h.mem.trunc,
    by rw [pinW_trunc]; exact h.flag, h.memos.trunc, h.fsize,
    h.frozen.congr (fun x _ => by rw [truncFrozen_ctl]),
    h.jsol.trunc (nmCnt_le h.arena.base) hs⟩

/-- `JobM.truncJ` without a solution. -/
theorem JobM.trunc {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {I : IStreamIndex} {m : Mem} {a : AState}
    (h : JobM pins dn ds none I m a) (hoff : a.store.scratchOn = false) (hk : IndexKeysIn m I)
    (hx : rdW (m.arr64 CTL) (UInt64.ofNat cmpCW) = 0 ∨ ExtOK m) :
    JobM pins dn ds none I (truncFrozen m) a :=
  h.truncJ hoff hk hx (fun _ e => nomatch e)

end L.Arena
