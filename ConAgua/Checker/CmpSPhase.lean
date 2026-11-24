module

public import ConAgua.Checker.CompareChain6J
public import ConAgua.Checker.CmpSeqView
import ConAgua.Arena.IWFrame
import ConAgua.Arena.LevelInternRef

@[expose] public section

/-!
# The solution's phase at the challenge's index state: the job relation (lane compare2, design (i))

The compared run freezes one store image after the challenge's index build (`m9`, `F6`) and
two headers. Header S's view (`mS`) is `m9` with the stream index's arrays (`EIX*`/`TIX*`) the
solution's rows (`SIX*`/`STX*`), `FIRSTS` and `DECL` the solution's (as the solution's index build
left them, `m`), `CTL[128]` the solution's next counter (`CTL[225]`), the frozen index's words
`CTL[162‥173]` the solution's, and the flag `CTL[224] = 0`.

* `JobM.csSwap`: the jobs' memory half across a frame of the index's arrays and words, at a new
  index, records and no solution.
* `csIndexR`: the solution's rows as the stream index (`SolR`'s rows are `IndexR`'s at `SIX*`).
* `CsViewS m m9 mS`: the view, hypothesis-level; `F6.jobMS`: the solution's job memory half at
  `mS`, at the twin's state after the challenge's index build (`sI`).
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend

section
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds ds' : Array IDeclaration}
  {I I' : IStreamIndex} {a : AState}

/-- **The jobs' memory half across a swap of the stream index** (its arrays `csA`, its words
`csC`): at the new memory's index `I'`, records `ds'`, frozen words, and no solution (the flag
`0`). -/
theorem _root_.L.Arena.JobM.csSwap {J : Option ISolution} {t t' : Mem} (h : JobM pins dn ds J I t a)
    (hf : MemFrame csA csC t t') (hI : IndexR t' I') (hD : DeclsF (t'.arr64 DECL) (t'.arr64 DLP) ds')
    (hfz : FrozenR t' I') (hfs : I'.firsts.size = ds'.size) (h224 : rdW (t'.arr64 CTL) 224 = 0) :
    JobM pins dn ds' none I' t' a := by
  have hE : t'.arr64 EREC = t.arr64 EREC := hf.arr _ (by decide) (by decide)
  have hE1 : t'.arr64 (tier1 EREC) = t.arr64 (tier1 EREC) := hf.arr _ (by decide) (by decide)
  have hbelow : OwnBelow t' := by
    intro w hw
    have hA : ∀ (u : UInt64), 140 ≤ (tierA (oixArr (rowTag w)) u).arr := fun u => by
      unfold tierA oixArr; generalize (u &&& 1 != 0) = b
      cases b <;> split <;> (try split) <;> decide
    have hB : ∀ (u : UInt64), 140 ≤ (tierA (otxArr (rowTag w)) u).arr := fun u => by
      unfold tierA otxArr; generalize (u &&& 1 != 0) = b
      cases b <;> split <;> (try split) <;> decide
    have e1 : ∀ u, t'.arr64 (tierA (oixArr (rowTag w)) u) = t.arr64 (tierA (oixArr (rowTag w)) u) :=
      fun u => hf.arr _ (not_mem_csA (.inr ⟨by have := hA u; omega, by have := hA u; omega, .inr (by have := hA u; omega)⟩))
        (fun e => by have := hA u; rw [e] at this; revert this; decide)
    have e2 : ∀ u, t'.arr64 (tierA (otxArr (rowTag w)) u) = t.arr64 (tierA (otxArr (rowTag w)) u) :=
      fun u => hf.arr _ (not_mem_csA (.inr ⟨by have := hB u; omega, by have := hB u; omega, .inr (by have := hB u; omega)⟩))
        (fun e => by have := hB u; rw [e] at this; revert this; decide)
    have e3 : ownRow t' w = ownRow t w := by simp only [ownRow, e1]
    simp only [stampW, hf.ctl 133 (by decide), e3, e2]
    exact h.below w hw
  have hAh : ∀ b ∈ csA, InHigh b := fun b hb => by have := csA_arr hb; exact ⟨this.1, by omega⟩
  have hCh : ∀ x ∈ csC, 64 ≤ x.toNat := fun x hx => by have := csC_val hx; omega
  exact ⟨arenaD_frame_hi h.arena hf hAh hCh,
    h.core.frame (fun b hb => by have := csA_arr hb; omega) (fun x hx => by have := csC_val hx; omega) hf,
    h.pinsR.frame (fun b hb => by have := csA_arr hb; omega) hf, h.mode.frame hf (by decide) (by decide),
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
    h.memos.frame hf (fun b hb => by have := csA_arr hb; refine ⟨?_, ?_, ?_⟩ <;>
        (try (intro e; subst e; revert this; decide)) <;> omega)
      (fun x hx => by have := csC_val hx; omega),
    hfs, hfz, JSol.none h224⟩

end

/-! ## The solution's rows as the stream index -/

/-- **The solution's rows read as the stream index**: a memory whose `EIX*`/`TIX*` are another's
`SIX*`/`STX*`, with that one's record pool and the counter `CTL[225]` at `CTL[128]`, has the
solution's index as its stream index, given `FIRSTS` as the solution's. -/
theorem csIndexR {m9 mS : Mem} {I : IStreamIndex} (hS : SolIdxR m9 I)
    (heix : ∀ g ≤ 2, mS.arr64 (eixArr g) = m9.arr64 (sixArr g))
    (htix : ∀ g ≤ 2, mS.arr64 (tixArr g) = m9.arr64 (stxArr g))
    (hE : erecP mS = erecP m9)
    (hfst : ∀ i (h : i < I.firsts.size), (rdW (mS.arr64 FIRSTS) (UInt64.ofNat i)).toNat = I.firsts[i])
    (hfsz : I.firsts.size ≤ (mS.arr64 FIRSTS).size)
    (h128 : rdW (mS.arr64 CTL) 128 = rdW (m9.arr64 CTL) 225) : IndexR mS I := by
  have hr : ∀ w, baseRow mS w = solRow m9 w := fun w => by
    unfold baseRow solRow
    split
    · next h => rw [heix _ h.1]
    · rfl
  have ht : ∀ w, baseTbl mS w = solTbl m9 w := fun w => by
    unfold baseTbl solTbl
    split
    · next h => rw [htix _ h.1]
    · rfl
  refine ⟨fun n => ?_, fun n => ?_, hfst, hfsz, ?_, fun w _ => ?_⟩
  · rw [hr, hE]; exact hS.base n
  · rw [ht, hE]; exact hS.btbl n
  · rw [h128]; exact hS.next
  · rw [hr]; exact (hS.rows w).1

/-! ## Header S's view -/

/-- **Header S's view** `mS` of the memory `m9` the compaction freezes (hypothesis-level; the
buffer's header S maps its frozen entries to `mS`'s arrays): `m9` but the stream index's rows are
the solution's (`SIX*`/`STX*`), `FIRSTS`, `DECL` and `DLP` the solution's (`m`'s, after its index build),
`CTL[128]` the solution's next counter (`CTL[225]`), the frozen index's words the solution's, and
the flag `CTL[224] = 0`. -/
structure CsViewS (m m9 mS : Mem) : Prop where
  frame : MemFrame csA csC m9 mS
  eix : ∀ g ≤ 2, mS.arr64 (eixArr g) = m9.arr64 (sixArr g)
  tix : ∀ g ≤ 2, mS.arr64 (tixArr g) = m9.arr64 (stxArr g)
  firsts : mS.arr64 FIRSTS = m.arr64 FIRSTS
  decl : mS.arr64 L.Front.DECL = m.arr64 L.Front.DECL
  dlp : mS.arr64 L.Front.DLP = m.arr64 L.Front.DLP
  c128 : rdW (mS.arr64 CTL) 128 = rdW (m9.arr64 CTL) 225
  frz : ∀ x ∈ frozenCtl, rdW (mS.arr64 CTL) x = rdW (m.arr64 CTL) x
  c224 : rdW (mS.arr64 CTL) 224 = 0
  bytes : mS.bytes = m9.bytes

section
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds dsS : Array IDeclaration}
  {I : IStreamIndex} {a : AState}

/-- **The solution's jobs' memory half at header S's view**: from the challenge's (at the
solution `J`, `m9`), the solution's index build's stream index and frozen words (`m`), and its
records (`m`'s `DECL`, `DLP`), at the same twin state. -/
theorem _root_.L.Arena.JobM.csViewS {J : ISolution} {m m9 mS : Mem}
    (h : JobM pins dn ds (some J) I m9 a) (hV : CsViewS m m9 mS) (hIm : IndexR m J.idx)
    (hFz : FrozenR m J.idx) (hD : DeclsF (m.arr64 L.Front.DECL) (m.arr64 DLP) dsS)
    (hfs : J.idx.firsts.size = dsS.size) : JobM pins dn dsS none J.idx mS a := by
  have hf := hV.frame
  have hS : SolR m9 J := h.jsol.sol.2
  have hE : erecP mS = erecP m9 :=
    erecP_congr' (hf.arr EREC (by decide) (by decide)) (hf.arr _ (by decide) (by decide))
      (hf.ctl 129 (by decide)) (hf.ctl 130 (by decide))
  have hI : IndexR mS J.idx := csIndexR ⟨hS.base, hS.btbl, hS.next, hS.size, hS.rows⟩ hV.eix hV.tix hE
    (fun i hi => by rw [hV.firsts]; exact hIm.firsts i hi) (by rw [hV.firsts]; exact hIm.firstsSize)
    hV.c128
  exact h.csSwap hf hI (by rw [hV.decl, hV.dlp]; exact hD)
    (hFz.congr hV.frz) hfs hV.c224

end

/-- **`ExtOK` at header S's view** of mode `6`'s frozen memory (the extent words are not patched;
the view's records are the solution's). -/
theorem F6.extOKS {bC bS pb : ByteArray} {sz : TieredArray → Nat} {PS : PhaseS bC bS} {m₇ m : Mem}
    (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) {c : Word} {m9 mS : Mem}
    (h6 : F6 PS m c m9) (hV : CsViewS m m9 mS) : ExtOK mS := by
  obtain ⟨h1, -, h3, h4, -, h6', h7⟩ := F6.ext hF h6
  have c1 : rdW (mS.arr64 CTL) (UInt64.ofNat cmpCW) = 1 := by rw [hV.frame.ctl _ (by decide)]; exact h1
  have cD : rdW (mS.arr64 CTL) (UInt64.ofNat cmpKD) = rdW (m9.arr64 CTL) (UInt64.ofNat cmpKD) :=
    hV.frame.ctl _ (by decide)
  have cP : rdW (mS.arr64 CTL) (UInt64.ofNat cmpKP) = rdW (m9.arr64 CTL) (UInt64.ofNat cmpKP) :=
    hV.frame.ctl _ (by decide)
  have e1 : xD mS = rdW (mS.arr64 CTL) (UInt64.ofNat cmpKD) := cmpOrW_on c1 _ _
  have e2 : xP mS = rdW (mS.arr64 CTL) (UInt64.ofNat cmpKP) := cmpOrW_on c1 _ _
  exact ⟨by rw [e1, cD, hV.decl]; exact h3, by rw [e1, cD]; exact h4, by rw [e2, cP, hV.dlp]; exact h6',
    by rw [e2, cP]; exact h7⟩

end L.Checker
