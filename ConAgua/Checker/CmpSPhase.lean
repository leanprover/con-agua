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
`csC`, and the swapped solution's rows): at the new memory's index `I'`, records `ds'`, frozen
words, and no solution (the flag `0`). -/
theorem _root_.L.Arena.JobM.csSwap {J : Option ISolution} {t t' : Mem} (h : JobM pins dn ds J I t a)
    (hf : MemFrame csAV csC t t') (hI : IndexR t' I') (hD : DeclsF (t'.arr64 DECL) (t'.arr64 DLP) ds')
    (hfz : FrozenR t' I') (hfs : I'.firsts.size = ds'.size) (h224 : rdW (t'.arr64 CTL) 224 = 0) :
    JobM pins dn ds' none I' t' a :=
  h.csSwapX (hf.mono (fun _ h => csAV_sub_csAX h) (fun _ h => h)) hI hD hfz hfs (JSol.none h224)

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
the solution's (`SIX*`/`STX*`), `FIRSTS`, `DECL` and `DLP` the solution's in their used words (`m`'s, after its
index build; the view's arrays may be longer, with other words past them), the solution's rows the
challenge's stream index's (the swap; the solution's jobs do not read them),
`CTL[128]` the solution's next counter (`CTL[225]`), the frozen index's words the solution's, and
the flag `CTL[224] = 0`. -/
structure CsViewS (m m9 mS : Mem) : Prop where
  frame : MemFrame csAV csC m9 mS
  eix : ∀ g ≤ 2, mS.arr64 (eixArr g) = m9.arr64 (sixArr g)
  tix : ∀ g ≤ 2, mS.arr64 (tixArr g) = m9.arr64 (stxArr g)
  firsts : ∀ j, j < (rdW (m.arr64 L.Front.DECL) 0).toNat → (mS.arr64 FIRSTS)[j]? = (m.arr64 FIRSTS)[j]?
  decl : ∀ j, j < 1 + 8 * (rdW (m.arr64 L.Front.DECL) 0).toNat →
    (mS.arr64 L.Front.DECL)[j]? = (m.arr64 L.Front.DECL)[j]?
  dlp : ∀ j, j < 1 + (rdW (m.arr64 L.Front.DLP) 0).toNat → (mS.arr64 L.Front.DLP)[j]? = (m.arr64 L.Front.DLP)[j]?
  fsz : (rdW (m.arr64 L.Front.DECL) 0).toNat ≤ (mS.arr64 FIRSTS).size
  dsz : 1 + 8 * (rdW (m.arr64 L.Front.DECL) 0).toNat ≤ (mS.arr64 L.Front.DECL).size ∧
    (mS.arr64 L.Front.DECL).size < 2 ^ 63
  psz : 1 + (rdW (m.arr64 L.Front.DLP) 0).toNat ≤ (mS.arr64 L.Front.DLP).size ∧
    (mS.arr64 L.Front.DLP).size < 2 ^ 63
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
  have e0 : ∀ P : Array Word, P[0]?.getD 0 = rdW P 0 := fun P => by simp [rdW]
  have hcnt : (rdW (m.arr64 L.Front.DECL) 0).toNat = dsS.size := by rw [← e0]; exact hD.count
  have hI : IndexR mS J.idx := csIndexR ⟨hS.base, hS.btbl, hS.next, hS.size, hS.rows⟩ hV.eix hV.tix hE
    (fun i hi => by
      have hi' : i < 2 ^ 64 := by have := hD.dsize; have := hD.room; omega
      have e : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' hi'
      have := hIm.firsts i hi
      simp only [rdW, e] at this ⊢
      rw [hV.firsts i (by rw [hcnt, ← hfs]; exact hi)]; exact this)
    (by have := hV.fsz; omega) hV.c128
  have hD' : DeclsF (mS.arr64 L.Front.DECL) (mS.arr64 L.Front.DLP) dsS :=
    DeclsF.agree hD (fun j hj => hV.decl j (by rw [hcnt]; exact hj))
      (fun j hj => hV.dlp j (by rw [← e0]; exact hj)) hV.dsz.2 hV.psz.2 (by have := hV.dsz.1; omega)
      (by have := hV.psz.1; rw [e0]; omega)
  exact h.csSwap hf hI hD' (hFz.congr hV.frz) hfs hV.c224

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
  have d0 : rdW (mS.arr64 L.Front.DECL) 0 = rdW (m.arr64 L.Front.DECL) 0 := by
    simp only [rdW, UInt64.reduceToNat]; rw [hV.decl 0 (by omega)]
  have p0 : rdW (mS.arr64 L.Front.DLP) 0 = rdW (m.arr64 L.Front.DLP) 0 := by
    simp only [rdW, UInt64.reduceToNat]; rw [hV.dlp 0 (by omega)]
  exact ⟨by rw [e1, cD, d0]; exact h3, by rw [e1, cD]; exact h4, by rw [e2, cP, p0]; exact h6',
    by rw [e2, cP]; exact h7⟩

end L.Checker
