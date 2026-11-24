module

public import ConAgua.Arena.JustifySideRefMove
public import ConAgua.Arena.FreezeTrunc

@[expose] public section

/-!
# The sequential compared run's views by prefix copies (lane compare2, the sJ variant)

Modes `8` and `9` (`Checker/CmpSeqEntry.lean`) switch between the challenge's and the solution's
view of the one region by copying the used prefixes of the stream index's rows, `FIRSTS`, `DECL`
and `DLP` (never whole arrays). The relations only read those prefixes:

* `DeclsF.agree`: the front's records from arrays agreeing on the used words;
* `csIndexRP`: the solution's rows as the stream index from rows agreeing below `2 · count`
  (rows past the counts are empty in both: `baseRow_out`, `SolKeysIn`).
-/

namespace L.Checker

open L L.Arena L.Front

theorem cq_trunc_agree {P P' : Array Word} {t : Nat} (h1 : t + 1 ≤ P.size) (h2 : t + 1 ≤ P'.size)
    (g : ∀ j, j ≤ t → P'[j]? = P[j]?) : L.Front.trunc P' t = L.Front.trunc P t := by
  have e : P'.extract 0 (t + 1) = P.extract 0 (t + 1) := by
    apply Array.ext_getElem?
    intro j
    by_cases hj : j < t + 1
    · rw [get?_extract _ hj, get?_extract _ hj]; exact g j (by omega)
    · rw [Array.getElem?_eq_none (by simp; omega), Array.getElem?_eq_none (by simp; omega)]
  simp only [L.Front.trunc, e]

/-- **`DeclsF` reads only the used words**: arrays agreeing with `D` below `1 + 8 · count` and
with `P` below `1 + P[0]`, with room, hold the same records. -/
theorem DeclsF.agree {D P D' P' : Array Word} {ds : Array IDeclaration} (h : L.Front.DeclsF D P ds)
    (gD : ∀ j, j < 1 + 8 * ds.size → D'[j]? = D[j]?)
    (gP : ∀ j, j < 1 + (P[0]?.getD 0).toNat → P'[j]? = P[j]?)
    (hDs : D'.size < 2 ^ 63) (hPs : P'.size < 2 ^ 63) (hDr : 1 + 8 * ds.size ≤ D'.size)
    (hPr : (P[0]?.getD 0).toNat + 1 ≤ P'.size) :
    L.Front.DeclsF D' P' ds := by
  have hP0 : (P'[0]?.getD 0) = (P[0]?.getD 0) := by rw [gP 0 (by omega)]
  have hptop := h.ptop
  refine ⟨hDs, hPs, by rw [gD 0 (by omega)]; exact h.count, hDr, by rw [hP0]; exact hPr,
    fun i hi => ?_, h.npb⟩
  have hr := h.recs i hi
  have hw : ∀ j, 0 < j → j < 1 + 8 * i + 8 → D'[j]? = D[j]? := fun j _ hj => gD j (by omega)
  generalize ds[i] = d at hr ⊢
  cases d with
  | indDecl b nP =>
    have hw' : ∀ k, k < 8 → L.Front.dw D' i k = L.Front.dw D i k := fun k hk => by
      simp only [L.Front.dw]; rw [hw _ (by omega) (by omega)]
    obtain ⟨a0, a4, t, ht, hdec⟩ := hr
    refine ⟨by rw [hw' 0 (by omega)]; exact a0, by rw [hw' 4 (by omega)]; exact a4, t,
      by rw [hP0]; exact ht, ?_⟩
    rw [hw' 2 (by omega), hw' 3 (by omega),
      cq_trunc_agree (P := P) (P' := P') (by omega) (by omega) (fun j hj => gP j (by omega))]
    exact hdec
  | _ =>
    simp only [L.Front.DeclAtF] at hr ⊢
    exact L.Front.DeclAt_mono D _ P _ i _ hw (fun j _ hj => gP j hj) (by rw [hP0]; exact Nat.le_refl _) hr

/-- A row array agreeing with `src` below `2 · count` and with `old` past it. -/
def RowsP (new src old : Array Word) (c : Nat) : Prop :=
  ∀ j, new[j]? = if j < 2 * c then src[j]? else old[j]?

theorem RowsP.lo {new src old : Array Word} {c : Nat} (h : RowsP new src old c) {j : Nat}
    (hj : j < 2 * c) : rdN new j = rdN src j := by
  simp only [rdN, h j, if_pos hj]

theorem RowsP.hi {new src old : Array Word} {c : Nat} (h : RowsP new src old c) {j : Nat}
    (hj : ¬ j < 2 * c) : rdN new j = rdN old j := by
  simp only [rdN, h j, if_neg hj]

/-- **The solution's rows as the stream index, by prefix copies**: `EIX*`/`TIX*` holding the
solution's rows `SIX*`/`STX*` below `2 · count` and the challenge's past it (empty there: `hout`),
the record pool, `FIRSTS` and the counter as `csIndexR`. -/
theorem csIndexRP {m9 mS : Mem} {I : IStreamIndex} (hS : SolIdxR m9 I) (hK : IndexKeysIn m9 I)
    (hout : ∀ w : Word, rowTag w ≤ 2 → rowTier w = 0 → ¬ (idxW w).toNat < nmCnt m9 (rowTag w) →
      (baseRow m9 w).1 = 0 ∧ (baseTbl m9 w).1 = 0)
    (heix : ∀ g ≤ 2, RowsP (mS.arr64 (eixArr g)) (m9.arr64 (sixArr g)) (m9.arr64 (eixArr g)) (nmCnt m9 g))
    (htix : ∀ g ≤ 2, RowsP (mS.arr64 (tixArr g)) (m9.arr64 (stxArr g)) (m9.arr64 (tixArr g)) (nmCnt m9 g))
    (hE : erecP mS = erecP m9)
    (hfst : ∀ i (h : i < I.firsts.size), (rdW (mS.arr64 FIRSTS) (UInt64.ofNat i)).toNat = I.firsts[i])
    (hfsz : I.firsts.size ≤ (mS.arr64 FIRSTS).size)
    (h128 : rdW (mS.arr64 CTL) 128 = rdW (m9.arr64 CTL) 225) : IndexR mS I := by
  -- a row inside the counts is the solution's; past them, the challenge's (empty)
  have hin : ∀ w : Word, rowTag w ≤ 2 → rowTier w = 0 → (idxW w).toNat < nmCnt m9 (rowTag w) →
      baseRow mS w = solRow m9 w ∧ baseTbl mS w = solTbl m9 w := fun w hg ht hl => by
    have h1 : rowIx w < 2 * nmCnt m9 (rowTag w) := by unfold rowIx; omega
    have h2 : rowIx w + 1 < 2 * nmCnt m9 (rowTag w) := by unfold rowIx; omega
    simp only [baseRow, baseTbl, solRow, solTbl, hg, ht, and_self, ite_true,
      (heix _ hg).lo h1, (heix _ hg).lo h2, (htix _ hg).lo h1, (htix _ hg).lo h2]
  have hpast : ∀ w : Word, rowTag w ≤ 2 → rowTier w = 0 → ¬ (idxW w).toNat < nmCnt m9 (rowTag w) →
      (baseRow mS w).1 = 0 ∧ (baseTbl mS w).1 = 0 := fun w hg ht hl => by
    have h1 : ¬ rowIx w < 2 * nmCnt m9 (rowTag w) := by unfold rowIx; omega
    have e1 : (baseRow mS w).1 = (baseRow m9 w).1 := by
      simp only [baseRow, hg, ht, and_self, ite_true, (heix _ hg).hi h1]
    have e2 : (baseTbl mS w).1 = (baseTbl m9 w).1 := by
      simp only [baseTbl, hg, ht, and_self, ite_true, (htix _ hg).hi h1]
    rw [e1, e2]; exact hout w hg ht hl
  have hother : ∀ w : Word, ¬ (rowTag w ≤ 2 ∧ rowTier w = 0) →
      baseRow mS w = solRow m9 w ∧ baseTbl mS w = solTbl m9 w := fun w h => by
    simp only [baseRow, baseTbl, solRow, solTbl, h, ite_false, and_self]
  refine ⟨fun n => ?_, fun n => ?_, hfst, hfsz, ?_, fun w _ => ?_⟩
  · by_cases hc : rowTag n.word.toUInt64 ≤ 2 ∧ rowTier n.word.toUInt64 = 0
    · by_cases hl : (idxW n.word.toUInt64).toNat < nmCnt m9 (rowTag n.word.toUInt64)
      · rw [(hin _ hc.1 hc.2 hl).1, hE]; exact hS.base n
      · rw [if_pos (hpast _ hc.1 hc.2 hl).1]
        cases e : I.base.idx[n]? with
        | none => rfl
        | some p => exact absurd (hK.idx n p e hc.1).2 hl
    · rw [(hother _ hc).1, hE]; exact hS.base n
  · by_cases hc : rowTag n.word.toUInt64 ≤ 2 ∧ rowTier n.word.toUInt64 = 0
    · by_cases hl : (idxW n.word.toUInt64).toNat < nmCnt m9 (rowTag n.word.toUInt64)
      · rw [(hin _ hc.1 hc.2 hl).2, hE]; exact hS.btbl n
      · rw [if_pos (hpast _ hc.1 hc.2 hl).2]
        cases e : I.base.tbls[n]? with
        | none => rfl
        | some p => exact absurd (hK.tbls n p e hc.1).2 hl
    · rw [(hother _ hc).2, hE]; exact hS.btbl n
  · rw [h128]; exact hS.next
  · by_cases hc : rowTag w ≤ 2 ∧ rowTier w = 0
    · by_cases hl : (idxW w).toNat < nmCnt m9 (rowTag w)
      · rw [(hin _ hc.1 hc.2 hl).1]; exact (hS.rows w).1
      · rw [(hpast _ hc.1 hc.2 hl).1]; decide
    · rw [(hother _ hc).1]; exact (hS.rows w).1

end L.Checker
