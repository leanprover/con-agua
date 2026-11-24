module

public import ConAgua.Arena.JustifySideRefMove
public import ConAgua.Arena.FreezeTrunc
import ConAgua.Arena.IWFrame
import ConAgua.Front.ApplyDeclRefine
import ConAgua.Arena.LevelInternRef

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
open ConRon.Arena ConRon.Arena.Frontend

/-- The arrays header S's view replaces: the stream index's rows, `FIRSTS`, `DECL`, `DLP`. -/
def csA : List TieredArray := [TIXA, TIXS, TIXN, EIXA, EIXS, EIXN, FIRSTS, L.Front.DECL, L.Front.DLP]

/-- The `CTL` words header S's view replaces: the index's counter, the frozen index's words, the
solution's flag. -/
def csC : List Word := [128, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 224]

theorem csA_arr {b : TieredArray} (h : b ∈ csA) : b.hi = false ∧ (b.arr = 67 ∨ b.arr = 68 ∨ (129 ≤ b.arr ∧ b.arr ≤ 137)) := by
  simp only [csA, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `csA` and the stash arrays modes `8`/`9` keep the challenge's view in (`CDECL`, `CEIX*`,
`CTIX*`, `CFIRSTS`, `CDLP`, `CCTL`): what a bank switch writes. -/
def csAS : List TieredArray := csA ++ ([CDECL, CEIXA, CEIXS, CEIXN, CTIXA, CTIXS, CTIXN, CFIRSTS, CDLP, CCTL] : List ArrId).map TieredArray.t0

theorem csAS_arr {b : TieredArray} (h : b ∈ csAS) : b.hi = false ∧
    (b.arr = 67 ∨ b.arr = 68 ∨ (129 ≤ b.arr ∧ b.arr ≤ 137) ∨ (223 ≤ b.arr ∧ b.arr ≤ 236)) := by
  simp only [csAS, csA, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> decide

theorem csA_sub_csAS {b : TieredArray} (h : b ∈ csA) : b ∈ csAS := List.mem_append_left _ h

/-- The solution's index rows: header S shows the challenge's `EIX*`/`TIX*` there (the swap). -/
def solRowsS : List TieredArray := [SIXA, SIXS, SIXN, STXA, STXS, STXN]

/-- The arrays header S's view replaces: `csA` and the swapped solution's rows. -/
def csAV : List TieredArray := csA ++ solRowsS

/-- `csAS` and the swapped solution's rows. -/
def csAX : List TieredArray := csAS ++ solRowsS

theorem csAX_arr {b : TieredArray} (h : b ∈ csAX) : b.hi = false ∧
    (b.arr = 67 ∨ b.arr = 68 ∨ (129 ≤ b.arr ∧ b.arr ≤ 137) ∨ (210 ≤ b.arr ∧ b.arr ≤ 215) ∨
      (223 ≤ b.arr ∧ b.arr ≤ 236)) := by
  rcases List.mem_append.mp h with h | h
  · have := csAS_arr h; exact ⟨this.1, by omega⟩
  · simp only [solRowsS, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem csAV_sub_csAX {b : TieredArray} (h : b ∈ csAV) : b ∈ csAX := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ (csA_sub_csAS h)
  · exact List.mem_append_right _ h

theorem csA_sub_csAV {b : TieredArray} (h : b ∈ csA) : b ∈ csAV := List.mem_append_left _ h

theorem csC_val {x : Word} (h : x ∈ csC) : x.toNat = 128 ∨ (162 ≤ x.toNat ∧ x.toNat ≤ 173) ∨ x.toNat = 224 := by
  simp only [csC, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem not_mem_csA {b : TieredArray} (h : b.hi = true ∨ (b.arr ≠ 67 ∧ b.arr ≠ 68 ∧ (b.arr < 129 ∨ 137 < b.arr))) : b ∉ csA :=
  fun hm => by
    have := csA_arr hm
    rcases h with h | h
    · rw [this.1] at h; cases h
    · omega

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
  simp only [rdN, h j, hj, ite_true]

theorem RowsP.hi {new src old : Array Word} {c : Nat} (h : RowsP new src old c) {j : Nat}
    (hj : ¬ j < 2 * c) : rdN new j = rdN old j := by
  simp only [rdN, h j, hj, ite_false]

/-- **The solution's rows as the stream index, by prefix copies**: `EIX*`/`TIX*` holding the
solution's rows `SIX*`/`STX*` below `2 · count` and the challenge's past it (empty there: `hout`),
the record pool, `FIRSTS` and the counter as `csIndexR`. -/
theorem csIndexRP {m9 mS : Mem} {I : IStreamIndex} (hS : SolIdxR m9 I) (hK : IndexKeysIn m9 I)
    (hout : ∀ w : Word, w.toNat < 2 ^ 32 → rowTag w ≤ 2 → rowTier w = 0 →
      ¬ (idxW w).toNat < nmCnt m9 (rowTag w) → (baseRow m9 w).1 = 0 ∧ (baseTbl m9 w).1 = 0)
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
  have hpast : ∀ w : Word, w.toNat < 2 ^ 32 → rowTag w ≤ 2 → rowTier w = 0 →
      ¬ (idxW w).toNat < nmCnt m9 (rowTag w) → (baseRow mS w).1 = 0 ∧ (baseTbl mS w).1 = 0 :=
    fun w hw hg ht hl => by
    have h1 : ¬ rowIx w < 2 * nmCnt m9 (rowTag w) := by unfold rowIx; omega
    have e1 : (baseRow mS w).1 = (baseRow m9 w).1 := by
      simp only [baseRow, hg, ht, and_self, ite_true, (heix _ hg).hi h1]
    have e2 : (baseTbl mS w).1 = (baseTbl m9 w).1 := by
      simp only [baseTbl, hg, ht, and_self, ite_true, (htix _ hg).hi h1]
    rw [e1, e2]; exact hout w hw hg ht hl
  have hother : ∀ w : Word, ¬ (rowTag w ≤ 2 ∧ rowTier w = 0) →
      baseRow mS w = solRow m9 w ∧ baseTbl mS w = solTbl m9 w := fun w h => by
    simp only [baseRow, baseTbl, solRow, solTbl, h, ite_false, and_self]
  refine ⟨fun n => ?_, fun n => ?_, hfst, hfsz, ?_, fun w hw => ?_⟩
  · by_cases hc : rowTag n.word.toUInt64 ≤ 2 ∧ rowTier n.word.toUInt64 = 0
    · by_cases hl : (idxW n.word.toUInt64).toNat < nmCnt m9 (rowTag n.word.toUInt64)
      · rw [(hin _ hc.1 hc.2 hl).1, hE]; exact hS.base n
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (hpast _ (by have := n.word.toNat_lt; simpa using this) hc.1 hc.2 hl).1)]
        cases e : I.base.idx[n]? with
        | none => rfl
        | some p => exact absurd (hK.idx n p e hc.1).2 hl
    · rw [(hother _ hc).1, hE]; exact hS.base n
  · by_cases hc : rowTag n.word.toUInt64 ≤ 2 ∧ rowTier n.word.toUInt64 = 0
    · by_cases hl : (idxW n.word.toUInt64).toNat < nmCnt m9 (rowTag n.word.toUInt64)
      · rw [(hin _ hc.1 hc.2 hl).2, hE]; exact hS.btbl n
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (hpast _ (by have := n.word.toNat_lt; simpa using this) hc.1 hc.2 hl).2)]
        cases e : I.base.tbls[n]? with
        | none => rfl
        | some p => exact absurd (hK.tbls n p e hc.1).2 hl
    · rw [(hother _ hc).2, hE]; exact hS.btbl n
  · rw [h128]; exact hS.next
  · by_cases hc : rowTag w ≤ 2 ∧ rowTier w = 0
    · by_cases hl : (idxW w).toNat < nmCnt m9 (rowTag w)
      · rw [(hin _ hc.1 hc.2 hl).1]; exact (hS.rows w).1
      · rw [(hpast _ ‹_› hc.1 hc.2 hl).1]; decide
    · rw [(hother _ hc).1]; exact (hS.rows w).1

/-! ## Back to the challenge's view after the solution's jobs -/

/-- **`SolR` across a memory keeping the solution's rows and words** whose record pool extends
(`SolR.growF` without a frame). -/
theorem _root_.L.Arena.SolR.keepX {m m' : Mem} {J : ISolution} (h : SolR m J)
    (he : ∀ b ∈ solArrs, m'.arr64 b = m.arr64 b)
    (hc : ∀ x ∈ solCtl, rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x)
    (hx : ArrExt (erecP m) (erecP m')) : SolR m' J := by
  have hr : ∀ w, solRow m' w = solRow m w := fun w => by simp only [solRow, he _ (six_mem _)]
  have ht : ∀ w, solTbl m' w = solTbl m w := fun w => by simp only [solTbl, he _ (stx_mem _)]
  have hm : ∀ w, matRow m' w = matRow m w := fun w => by simp only [matRow, he _ (mat_mem _)]
  have hl : ∀ w, matList m' w = matList m w := fun w => by
    unfold matList
    rw [hm]
    split
    · rfl
    · rename_i c
      obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp (h.mates_dec w c)
      unfold matList at hxs; simp only [c, ite_false] at hxs
      rw [hxs, hx.hslice? hxs]
  refine ⟨fun n => ?_, fun n => ?_, ?_, ?_, fun n => by rw [h.mates n, hl], fun w hw => ?_,
    fun w => by rw [hr, ht]; exact h.rows w⟩
  · have := h.base n; rw [hr]
    rw [this]; split
    · rfl
    · cases e : J.idx.base.idx[n]? with
      | none => rw [e] at this; simp_all
      | some y =>
        rw [e] at this
        simp only [Option.map_some, ite_eq_right_of_eq_false _ _ (eq_false ‹_›), Option.some.injEq,
          Prod.mk.injEq] at this
        rw [← this.2, hx.decCI this.2.symm]
  · have := h.btbl n; rw [ht]
    rw [this]; split
    · rfl
    · cases e : J.idx.base.tbls[n]? with
      | none => rw [e] at this; simp_all
      | some y =>
        rw [e] at this
        simp only [Option.map_some, ite_eq_right_of_eq_false _ _ (eq_false ‹_›), Option.some.injEq,
          Prod.mk.injEq] at this
        rw [← this.2, hx.decTbl this.2.symm]
  · rw [ctlW, hc _ (by decide)]; exact h.next
  · rw [ctlW, hc _ (by decide)]; exact h.size
  · rw [hl]; rw [hm] at hw; exact h.mates_dec w hw

/-- The stream index's arrays (`IndexR`'s: rows `129‥134`, `FIRSTS`) are header S's view's. -/
theorem csA_of_idx {b : TieredArray} (h0 : b.hi = false) (h1 : (129 ≤ b.arr ∧ b.arr ≤ 134) ∨ b.arr = 137) :
    b ∈ csA := by
  obtain ⟨n, hi⟩ := b
  simp only at h0 h1; subst h0
  have : n = 129 ∨ n = 130 ∨ n = 131 ∨ n = 132 ∨ n = 133 ∨ n = 134 ∨ n = 137 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

section
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds ds' : Array IDeclaration}
  {I I' : IStreamIndex} {a : AState}

/-- **The jobs' memory half across a swap of the stream index, at any solution** (`JobM.csSwap`
with the new memory's solution `J'` given; the swapped solution's rows may differ too). -/
theorem _root_.L.Arena.JobM.csSwapX {J J' : Option ISolution} {t t' : Mem} (h : JobM pins dn ds J I t a)
    (hf : MemFrame csAX csC t t') (hI : IndexR t' I') (hD : DeclsF (t'.arr64 DECL) (t'.arr64 DLP) ds')
    (hfz : FrozenR t' I') (hfs : I'.firsts.size = ds'.size) (hs : JSol J' t') :
    JobM pins dn ds' J' I' t' a := by
  have hE : t'.arr64 EREC = t.arr64 EREC := hf.arr _ (by decide) (by decide)
  have hbelow : OwnBelow t' := by
    intro w hw
    have hA : ∀ (u : UInt64), 140 ≤ (tierA (oixArr (rowTag w)) u).arr ∧ (tierA (oixArr (rowTag w)) u).arr ≤ 148 := fun u => by
      unfold tierA oixArr; generalize (u &&& 1 != 0) = b
      cases b <;> split <;> (try split) <;> decide
    have hB : ∀ (u : UInt64), 140 ≤ (tierA (otxArr (rowTag w)) u).arr ∧ (tierA (otxArr (rowTag w)) u).arr ≤ 148 := fun u => by
      unfold tierA otxArr; generalize (u &&& 1 != 0) = b
      cases b <;> split <;> (try split) <;> decide
    have e1 : ∀ u, t'.arr64 (tierA (oixArr (rowTag w)) u) = t.arr64 (tierA (oixArr (rowTag w)) u) :=
      fun u => hf.arr _ (fun hm => by have := csAX_arr hm; have := hA u; omega)
        (fun e => by have := hA u; rw [e] at this; revert this; decide)
    have e2 : ∀ u, t'.arr64 (tierA (otxArr (rowTag w)) u) = t.arr64 (tierA (otxArr (rowTag w)) u) :=
      fun u => hf.arr _ (fun hm => by have := csAX_arr hm; have := hB u; omega)
        (fun e => by have := hB u; rw [e] at this; revert this; decide)
    have e3 : ownRow t' w = ownRow t w := by simp only [ownRow, e1]
    simp only [stampW, hf.ctl 133 (by decide), e3, e2]
    exact h.below w hw
  have hAh : ∀ b ∈ csAX, InHigh b := fun b hb => by have := csAX_arr hb; exact ⟨this.1, by omega⟩
  have hCh : ∀ x ∈ csC, 64 ≤ x.toNat := fun x hx => by have := csC_val hx; omega
  exact ⟨arenaD_frame_hi h.arena hf hAh hCh,
    h.core.frame (fun b hb => by have := csAX_arr hb; omega) (fun x hx => by have := csC_val hx; omega) hf,
    h.pinsR.frame (fun b hb => by have := csAX_arr hb; omega) hf, h.mode.frame hf (by decide) (by decide),
    hI, hbelow,
    by simp only [stampW, hf.ctl 133 (by decide)]; exact h.stamp,
    hD,
    IWOK.frame hf (by decide) (by decide) (by decide) (by decide) h.iw (by decide) (by decide),
    by rw [hf.ctl 130 (by decide)]; exact h.top1,
    PinSetsR.grow h.pinsets (RecGrow.of_eq hE (hf.ctl 129 (by decide)))
      (hf.ctl 150 (by decide)) (hf.ctl 151 (by decide)),
    ⟨by rw [hf.size]; exact h.mem.erec, by rw [hf.size]; exact h.mem.spn, by rw [hf.size]; exact h.mem.bstk,
      h.mem.memos.frame hf ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide)
        ⟨by decide, by decide, by decide⟩ (by decide)
        ⟨by decide, by decide, by decide⟩ (by decide) (by decide), h.mem.dnN⟩,
    by rw [pinW_frame hf (by decide)]; exact h.flag,
    h.memos.frame hf (fun b hb => by have := csAX_arr hb; refine ⟨?_, ?_, ?_⟩ <;>
        (try (intro e; subst e; revert this; decide)) <;> omega)
      (fun x hx => by have := csC_val hx; omega),
    hfs, hfz, hs⟩


/-- **The jobs' memory half across a swap of the stream index, at any solution** (`JobM.csSwapX`
over `csAS`). -/
theorem _root_.L.Arena.JobM.csSwapJ {J J' : Option ISolution} {t t' : Mem} (h : JobM pins dn ds J I t a)
    (hf : MemFrame csAS csC t t') (hI : IndexR t' I') (hD : DeclsF (t'.arr64 DECL) (t'.arr64 DLP) ds')
    (hfz : FrozenR t' I') (hfs : I'.firsts.size = ds'.size) (hs : JSol J' t') :
    JobM pins dn ds' J' I' t' a :=
  h.csSwapX (hf.mono (fun _ h => List.mem_append_left _ h) (fun _ h => h)) hI hD hfz hfs hs
end

/-- **Header C's view after the solution's jobs** `mC`: the memory `mS` the solution's jobs left
but in the stream index's arrays and words (`csA`, `csC`), which are the challenge's frozen memory
`m9`'s again (restored from copies, or a header's images): the stream index's arrays exactly, the
records and the declaration pool in their used words (the jobs may write past them). -/
structure CsViewC (m9 mS mC : Mem) : Prop where
  frame : MemFrame csAV csC mS mC
  rows : ∀ b ∈ solRowsS, mC.arr64 b = m9.arr64 b
  idx : ∀ b, IdxArr b = true → mC.arr64 b = m9.arr64 b
  decl : ∀ j, j < 1 + 8 * (rdW (m9.arr64 L.Front.DECL) 0).toNat →
    (mC.arr64 L.Front.DECL)[j]? = (m9.arr64 L.Front.DECL)[j]?
  dlp : ∀ j, j < 1 + (rdW (m9.arr64 L.Front.DLP) 0).toNat →
    (mC.arr64 L.Front.DLP)[j]? = (m9.arr64 L.Front.DLP)[j]?
  dsz : (mC.arr64 L.Front.DECL).size = (m9.arr64 L.Front.DECL).size
  psz : (mC.arr64 L.Front.DLP).size = (m9.arr64 L.Front.DLP).size
  ctl : ∀ x ∈ csC, rdW (mC.arr64 CTL) x = rdW (m9.arr64 CTL) x

/-- **What the solution's jobs keep of the challenge's frozen memory** `m9`: the solution's rows
and words, the record pool (it only grew: `checkJobs_refX`), and the walks' memos. -/
structure CsKeep (m9 mS : Mem) : Prop where
  sol : ∀ b ∈ solArrs, b ∉ solRowsS → mS.arr64 b = m9.arr64 b
  snext : rdW (mS.arr64 CTL) SNEXTC = rdW (m9.arr64 CTL) SNEXTC
  scnt : rdW (mS.arr64 CTL) SCNTC = rdW (m9.arr64 CTL) SCNTC
  grow : ArrExt (erecP m9) (erecP mS)
  walk : WalkMem mS

section
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}

/-- **The challenge's jobs' memory half after the solution's jobs**: from the solution's (at the
owned state `a` its jobs left, memory `mS`), the challenge's at the frozen memory `m9` (its index
`IC`, records `dsC`, solution `J`), header C's view `mC` (`CsViewC`) and what the solution's jobs
kept (`CsKeep`): the challenge's at `mC`, at the solution's owned state `a`. -/
theorem _root_.L.Arena.JobM.csBack {J : ISolution} {IS IC : IStreamIndex} {dsS dsC : Array IDeclaration}
    {m9 mS mC : Mem} {a9 a : AState}
    (hS : JobM pins dn dsS none IS mS a) (hC : JobM pins dn dsC (some J) IC m9 a9)
    (hV : CsViewC m9 mS mC) (hK : CsKeep m9 mS) : JobM pins dn dsC (some J) IC mC a := by
  have hf := hV.frame
  have hEC : erecP mC = erecP mS :=
    erecP_congr' (hf.arr EREC (by decide) (by decide)) (hf.arr _ (by decide) (by decide))
      (hf.ctl 129 (by decide)) (hf.ctl 130 (by decide))
  have hx : ArrExt (erecP m9) (erecP mC) := by rw [hEC]; exact hK.grow
  have hI : IndexR mC IC :=
    hC.idx.grow (fun b h0 h1 => hV.idx b (by simp only [IdxArr, h0]; grind)) (hV.ctl 128 (by decide)) hx
  have hsol : SolR mC J := hC.jsol.sol.2.keepX
    (fun b hb => by
      by_cases hr : b ∈ solRowsS
      · exact hV.rows b hr
      · rw [hf.arr b (fun hm => by
            rcases List.mem_append.mp hm with hm | hm
            · have := csA_arr hm; have := solArrs_arr hb; omega
            · exact hr hm)
          (fun e => by subst e; revert hb; decide)]
        exact hK.sol b hb hr)
    (fun x hx' => by
      simp only [solCtl, List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with rfl | rfl | rfl
      · exact hV.ctl _ (by decide)
      · rw [hf.ctl _ (by decide)]; exact hK.snext
      · rw [hf.ctl _ (by decide)]; exact hK.scnt) hx
  have h224 : ctlW mC SOLC = 1 := by
    simp only [ctlW]; rw [hV.ctl _ (by decide)]; exact hC.jsol.sol.1
  have hd := hC.decls
  have e0 : ∀ P : Array Word, P[0]?.getD 0 = rdW P 0 := fun P => by simp [rdW]
  have hD : DeclsF (mC.arr64 L.Front.DECL) (mC.arr64 L.Front.DLP) dsC :=
    DeclsF.agree hd (fun j hj => hV.decl j (by rw [← e0, hd.count]; exact hj))
      (fun j hj => hV.dlp j (by rw [← e0]; exact hj)) (by rw [hV.dsz]; exact hd.dsize)
      (by rw [hV.psz]; exact hd.psize) (by rw [hV.dsz]; exact hd.room) (by rw [hV.psz]; exact hd.ptop)
  refine hS.csSwapX (hf.mono (fun _ h => csAV_sub_csAX h) (fun _ h => h)) hI hD
    (hC.frozen.congr fun x hx' => hV.ctl x (by
      simp only [frozenCtl, csC, List.mem_cons, List.not_mem_nil, or_false] at hx' ⊢
      rcases hx' with h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]))
    hC.fsize ⟨⟨h224, hsol⟩, fun J' e => ?_⟩
  cases e
  exact ⟨hK.walk.frame hf (by decide) (by decide) (by decide) (by decide), (hC.jsol.walk J rfl).2⟩

end

/-! ## The solution's view by prefix copies -/

/-- **What the frozen memory `m9` keeps of the solution's index build `m`** (`cmp_sstash`'s copies,
kept through the challenge's stages): its records' words (`SDECL`, below `1 + 8 · count`), its
index's firsts (`SFIRSTS`, below the count), its declaration pool (`SDLP`, below `1 + DLP[0]`) and
its frozen index words (`SCTL`). -/
structure CsStash (m m9 : Mem) : Prop where
  decl : ∀ j, j < 1 + 8 * (rdW (m.arr64 L.Front.DECL) 0).toNat →
    (m9.arr64 SDECL)[j]? = (m.arr64 L.Front.DECL)[j]?
  firsts : ∀ j, j < (rdW (m.arr64 L.Front.DECL) 0).toNat → (m9.arr64 SFIRSTS)[j]? = (m.arr64 FIRSTS)[j]?
  dlp : ∀ j, j < 1 + (rdW (m.arr64 L.Front.DLP) 0).toNat → (m9.arr64 SDLP)[j]? = (m.arr64 L.Front.DLP)[j]?
  frz : ∀ x ∈ frozenCtl, rdW (m9.arr64 SCTL) x = rdW (m.arr64 CTL) x

end L.Checker
