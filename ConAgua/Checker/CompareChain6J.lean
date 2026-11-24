module

public import ConAgua.Checker.CompareChain6Run
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.JobsStart
import ConAgua.Arena.IWFrame

@[expose] public section

/-!
# The challenge's job relation after mode `6` (lane compare)

`F6.jobM`, `F6.jobR`: after mode `6`'s steps (`F6`: the challenge's index build `G6`, then the flag
`CTL[224] := 1`), the flushed memory is in the job relation at the challenge's records, its index
and the solution `solutionOf IS res` (the solution's index moved, the challenge's mates), from
the twin's state after the challenge's index build with its caches emptied (as `FoldOn.jobRJ` for
the flat run).
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend

section
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
  {I : IStreamIndex} {a : AState}

/-- The `CTL` words mode `6`'s end sets: the solution's flag and the extent words (`cmp_ext`). -/
def flagC : List Word := [224, 229, 230, 231]

/-- **Setting the solution's flag and the extent words keeps the jobs' memory half** (as
`JobM.cut`), at the solution the flag's memory holds. -/
theorem _root_.L.Arena.JobM.setFlag {J J' : Option ISolution} {t t' : Mem} (h : JobM pins dn ds J I t a)
    (hf : MemFrame [] flagC t t') (hs : JSol J' t') : JobM pins dn ds J' I t' a := by
  have hA : ∀ b ∈ ([] : List TieredArray), False := fun _ h => absurd h (by simp)
  have hC : ∀ x ∈ flagC, x = 224 ∨ x = 229 ∨ x = 230 ∨ x = 231 := fun x hx => by simpa [flagC] using hx
  have he : erecP t' = erecP t :=
    erecP_congr' (hf.arr EREC (by simp) (by decide)) (hf.arr _ (by simp) (by decide))
      (hf.ctl 129 (by decide)) (hf.ctl 130 (by decide))
  exact ⟨⟨ArenaR.frame_ext [] _ (by simp) (fun x hx => by rcases hC x hx with rfl | rfl | rfl | rfl <;> decide) _ _ hf _ h.arena.base,
      DerR.frameM [] _ _ _ hf (by simp) _ h.arena.der⟩,
    h.core.frame (fun b hb => (hA b hb).elim) (fun x hx => by rcases hC x hx with rfl | rfl | rfl | rfl <;> decide) hf,
    h.pinsR.frame (fun b hb => (hA b hb).elim) hf, h.mode.frame hf (by decide) (by decide),
    h.idx.grow (fun b _ hr => hf.arr b (by simp) (fun e => by subst e; revert hr; decide)) (hf.ctl 128 (by decide))
      (by rw [he]; exact fun _ _ h => h),
    h.below.frame (fun b hb => (hA b hb).elim) (by decide) hf,
    by simp only [stampW, hf.ctl 133 (by decide)]; exact h.stamp,
    by rw [hf.arr _ (by simp) (by decide), hf.arr _ (by simp) (by decide)]; exact h.decls,
    IWOK.frame hf (by simp) (by simp) (by decide) (by decide) h.iw (by simp) (by decide),
    by rw [hf.ctl 130 (by decide)]; exact h.top1,
    PinSetsR.grow h.pinsets (RecGrow.of_eq (hf.arr EREC (by simp) (by decide)) (hf.ctl 129 (by decide)))
      (hf.ctl 150 (by decide)) (hf.ctl 151 (by decide)),
    ⟨by rw [hf.size]; exact h.mem.erec, by rw [hf.size]; exact h.mem.spn, by rw [hf.size]; exact h.mem.bstk,
      h.mem.memos.frame hf ⟨by simp, by simp⟩ ⟨by decide, by decide⟩ (by simp)
        ⟨by decide, by decide, by decide⟩ (by simp)
        ⟨by decide, by decide, by decide⟩ (by simp) (by decide), h.mem.dnN⟩,
    by rw [pinW_frame hf (by simp)]; exact h.flag,
    h.memos.frame hf (fun b hb => (hA b hb).elim) (fun x hx => by rcases hC x hx with rfl | rfl | rfl | rfl <;> decide), h.fsize,
    h.frozen.frame (fun x hx => by rcases hC x hx with rfl | rfl | rfl | rfl <;> exact not_mem_frozenCtl (by decide)) hf, hs⟩

/-- **The flush after the jobs' memory half** (`FoldOn.jobRJ`'s flush, at any memory half): the
job relation at the flushed memory and the twin state with its caches emptied. -/
theorem _root_.L.Arena.JobM.flushR {J : Option ISolution} {m : Mem} (h : JobM pins dn ds J I m a)
    (hwf : StoreWF a.store) (hoff : a.store.scratchOn = false) (hfok : FlushOK m) :
    JobR pins dn ds J I (flushMem m) { a with caches := Caches.empty } := by
  have hF := flushMem_frame m
  have hA0 := loArr_nil
  have hC0 := loCtl_flush
  have hD := h.arena.caches_irrel Caches.empty
  exact ⟨⟨⟨ArenaR.frame_ext [] _ (by simp) flushCtl_ge _ _ hF _ hD.base,
      DerR.frameM [] _ _ _ hF (by simp) _ hD.der⟩, h.core.flush hfok,
    h.pinsR.frame (fun _ h => absurd h (by simp)) hF, h.mode.frame hF (by decide) (by decide),
    h.idx.frameLo hA0 hC0 hF, h.below.frameLo hA0 hC0 hF,
    by rw [stampW_frameLo hC0 hF]; exact h.stamp, declsF_frameLo hA0 hF h.decls,
    iwOK_frameLo hA0 hC0 hF h.iw, by rw [hC0.ctl hF (by decide)]; exact h.top1,
    pinSetsR_frameLo hA0 hC0 hF h.pinsets, h.mem.frameLo hA0 hC0 hF h.mem.dnN,
    by rw [pinW_frame hF (by simp)]; exact h.flag,
    h.memos.frameLo hA0 hC0 hF, h.fsize, h.frozen.frameLo hC0 hF,
    h.jsol.frameLo hA0 hC0 hF⟩, ⟨hwf⟩, hoff, rfl⟩

end

/-- **The solution's index part across a frame** outside its rows and words, whose record pool
extends. -/
theorem _root_.L.Arena.SolIdxR.frameX {A : List TieredArray} {C : List Word} {m m' : Mem} {I : IStreamIndex}
    (h : SolIdxR m I) (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b ∉ solArrs) (h225 : SNEXTC ∉ C)
    (h226 : SCNTC ∉ C) (hx : ArrExt (erecP m) (erecP m')) : SolIdxR m' I := by
  have he : ∀ b ∈ solArrs, m'.arr64 b = m.arr64 b := fun b hb =>
    hf.arr b (fun hm => hA b hm hb) (fun e => by subst e; revert hb; decide)
  have hr : ∀ w, solRow m' w = solRow m w := fun w => by simp only [solRow, he _ (six_mem _)]
  have hb : ∀ w, solTbl m' w = solTbl m w := fun w => by simp only [solTbl, he _ (stx_mem _)]
  refine ⟨fun n => ?_, fun n => ?_, ?_, ?_, fun w => by rw [hr, hb]; exact h.rows w⟩
  · have := h.base n; rw [hr, this]; split
    · rfl
    · cases e : I.base.idx[n]? with
      | none => rw [e] at this; simp_all
      | some y =>
        rw [e] at this
        simp only [Option.map_some, ite_eq_right_of_eq_false _ _ (eq_false ‹_›), Option.some.injEq,
          Prod.mk.injEq] at this
        rw [← this.2, hx.decCI this.2.symm]
  · have := h.btbl n; rw [hb, this]; split
    · rfl
    · cases e : I.base.tbls[n]? with
      | none => rw [e] at this; simp_all
      | some y =>
        rw [e] at this
        simp only [Option.map_some, ite_eq_right_of_eq_false _ _ (eq_false ‹_›), Option.some.injEq,
          Prod.mk.injEq] at this
        rw [← this.2, hx.decTbl this.2.symm]
  · rw [ctlW, hf.ctl _ h225]; exact h.next
  · rw [ctlW, hf.ctl _ h226]; exact h.size

/-- **`SolR` across the solution's flag and the extent words** (`CTL[224]`, `CTL[229‥231]`, which
`SolR` does not read). -/
theorem _root_.L.Arena.SolR.flagFrame {m m' : Mem} {J : ISolution} (h : SolR m J) (hf : MemFrame [] flagC m m') :
    SolR m' J := by
  have he : erecP m' = erecP m :=
    erecP_congr' (hf.arr EREC (by simp) (by decide)) (hf.arr _ (by simp) (by decide))
      (hf.ctl 129 (by decide)) (hf.ctl 130 (by decide))
  have hm : ∀ w, matRow m' w = matRow m w := fun w => by
    simp only [matRow, hf.arr _ (by simp) (show (matArr (rowTag w) : TieredArray) ≠ CTL by
      unfold matArr; split <;> (try split) <;> decide)]
  have hl : ∀ w, matList m' w = matList m w := fun w => by
    unfold matList; rw [hm, he]
  exact SolR.ofIdx (SolIdxR.frameX ⟨h.base, h.btbl, h.next, h.size, h.rows⟩ hf (by simp) (by decide)
      (by decide) (by rw [he]; exact fun _ _ x => x))
    (fun n => by rw [hl]; exact h.mates n) (fun w hw => by rw [hl]; rw [hm] at hw; exact h.mates_dec w hw)

theorem biA_not_sol {b : TieredArray} (hb : b ∈ biA) : b ∉ solArrs ∧ b ≠ (NDM : TieredArray) ∧
    b ≠ (CSM : TieredArray) := by
  have h : ¬(210 ≤ b.arr ∧ b.arr ≤ 222) := by
    have := (List.mem_filter.mp hb).2
    intro hc; simp [hc.1, hc.2] at this
  exact ⟨fun hs => h (by have := solArrs_arr hs; omega), fun e => h (by subst e; decide),
    fun e => h (by subst e; decide)⟩

section six
variable {bC bS pb : ByteArray} {sz : TieredArray → Nat} {PS : PhaseS bC bS} {m₇ m : Mem}

/-- **A `CTL` word outside every write of mode `6` up to the challenge's index build** keeps the
solution's index build's value. -/
theorem G6.ctl {c : Word} {m2 m3 : Mem} {dsC : Array IDeclaration} {sG : AState}
    {res : List IDeclaration} {m4 m5 m6 : Mem} (h : Side6 PS m c m2 m3 dsC sG res m4) (hK : MKeep m4 m5)
    (hfr : MemFrame biA biC m5 m6) {x : Word} (h64 : x ∉ C64) (h129 : x ≠ 129) (hbi : x ∉ biC) :
    rdW (m6.arr64 CTL) x = rdW (m.arr64 CTL) x := by
  rw [hfr.ctl _ hbi, hK.frame.ctl _ (by simpa using h129), h.frameM.ctl _ h64]

/-- **The challenge's job memory half after mode `6`'s steps** (before the flush): the steps' twin
facts, the challenge's index build, and the jobs' memory half at the memory `F6` ends in, at the
solution `solutionOf IS res` (the twin's store well formed with the scratch tier off). -/
theorem F6.jobM (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) {c : Word} {m9 : Mem}
    (h6 : F6 PS m c m9) :
    ∃ (m2 m3 : Mem) (dsC : Array IDeclaration) (sG : AState) (res : List IDeclaration) (m4 : Mem)
      (I : IStreamIndex) (a' : AState),
      Side6 PS m c m2 m3 dsC sG res m4 ∧ buildIndex res.toArray sG = .ok (.ok I, a') ∧
      JobM PS.ipins (dnOf sG.store) res.toArray (some (solutionOf PS.IS res)) I m9 a' ∧
      StoreWF a'.store ∧ a'.store.scratchOn = false ∧ ∀ t, (m9.arr64 t).size = (m.arr64 t).size := by
  obtain ⟨m6, ⟨m2, m3, dsC, sG, res, m4, m5, h, hMt, hMI, hK, I, a', hI, hB, hFz, hfs, hBK, hfr, -⟩,
    rfl, -⟩ := h6
  refine ⟨m2, m3, dsC, sG, res, m4, I, a', h, hI, ?_, hB.drv.state.wf, hB.off, fun t => by
    rw [(cmpExt_frame _).size, (MemFrame.setCtl m6 224 1).size, hfr.size, hK.frame.size, h.frameM.size]⟩
  have hS := hB.stage
  have hctl : 228 < (m.arr64 CTL).size := by
    rw [hF.sizeAt]
    have := hF.r7.since.caps.2.1; rw [loadMem_arr, Array.size_replicate] at this
    simp only [ctlMin] at this; omega
  have hsz6 : (m6.arr64 CTL).size = (m.arr64 CTL).size := by
    rw [hfr.size, hK.frame.size, h.frameM.size]
  have h220 : rdW (m.arr64 CTL) 220 = 0 := by
    rw [hF.frame.ctl _ (not_mem_biC (by decide)), hF.r7.since.frame.ctl _ (by decide)]
    exact loadMem_rd bS pb sz CTL 220
  have h222 : rdW (m.arr64 CTL) 222 = 0 := by
    rw [hF.frame.ctl _ (not_mem_biC (by decide)), hF.r7.since.frame.ctl _ (by decide)]
    exact loadMem_rd bS pb sz CTL 222
  have hc6 : ∀ x : Word, x ∉ C64 → x ≠ 129 → x ∉ biC → rdW (m6.arr64 CTL) x = rdW (m.arr64 CTL) x :=
    fun x h1 h2 h3 => G6.ctl h hK hfr h1 h2 h3
  -- the memory half without a solution, at the challenge's index build
  have c224 : rdW (m6.arr64 CTL) 224 = 0 := by
    rw [hc6 _ (not_mem_C64 (by decide)) (by decide) (not_mem_biC (by decide))]; exact hF.c224
  have h130 : rdW (m6.arr64 CTL) 130 = 0 := by
    rw [hBK.ctl130, hK.frame.ctl _ (by decide), h.frameM.ctl _ (not_mem_C64 (by decide)), hF.grow.ctl130]
    exact hF.r7.c130
  have hP0 : PinSetsR m PS.ipins := PinSetsR.grow hF.r7.pinSets hF.grow.grow
    (hF.frame.ctl _ (not_mem_biC (by decide))) (hF.frame.ctl _ (not_mem_biC (by decide)))
  have hg04 : RecGrow m m4 := RecGrow.of_eq (h.frameM.arr EREC (not_mem_A64 (by decide)) (by decide))
    (h.frameM.ctl 129 (not_mem_C64 (by decide)))
  have hg45 : RecGrow m4 m5 := ⟨hK.grow.top, hK.grow.get⟩
  have hP6 : PinSetsR m6 PS.ipins := PinSetsR.grow hP0 ((hg04.trans hg45).trans hBK.grow)
    (hc6 _ (not_mem_C64 (by decide)) (by decide) (not_mem_biC (by decide)))
    (hc6 _ (not_mem_C64 (by decide)) (by decide) (not_mem_biC (by decide)))
  have hJM6 : JobM PS.ipins (dnOf sG.store) res.toArray none I m6 a' :=
    ⟨hS.check.arena, hS.check.core, hS.check.pins, hS.check.mode, hB.idx, hS.check.env.ownBelow,
      hS.check.env.stamp, hB.decls, hS.iw, h130, hP6, hB.twin.mem, hB.pin, hB.memos, hfs, hFz,
      JSol.none c224⟩
  -- the solution
  obtain ⟨m1, ⟨m0, -, hSI, -, -⟩, -, hf14⟩ := h.from1
  have hx14 : erecP m4 = erecP m1 :=
    erecP_congr' (hf14.arr _ (fun h => by have := A14_arr _ h; simp [EREC] at this) (by decide))
      (hf14.arr _ (fun h => by have := A14_arr _ h; simp [EREC] at this) (by decide))
      (hf14.ctl _ (fun h => by rcases C14_val _ h with e | e | e | e | e | e | e | e | e <;> revert e <;> decide))
      (hf14.ctl _ (fun h => by rcases C14_val _ h with e | e | e | e | e | e | e | e | e <;> revert e <;> decide))
  have hSI4 : SolIdxR m4 PS.IS := hSI.frameX hf14
    (fun b hb hs => by have := A14_arr _ hb; have := solArrs_arr hs; omega)
    (fun h => by rcases C14_val _ h with e | e | e | e | e | e | e | e | e <;> revert e <;> decide)
    (fun h => by rcases C14_val _ h with e | e | e | e | e | e | e | e | e <;> revert e <;> decide)
    (by rw [hx14]; exact fun _ _ x => x)
  have hMt' : MatesR m5 (recordMatesGo ∅ res) := by simpa using hMt
  have hSol5 : SolR m5 (solutionOf PS.IS res) := solR_of hSI4 hMt' hK
  have h130' : rdW (m5.arr64 CTL) 130 = 0 := by rw [← hBK.ctl130]; exact h130
  have hE56 : ErecGrow m5 m6 := ⟨hBK.grow.1, hBK.grow.2,
    by simp only [erecTop1, hBK.ctl130]; exact Nat.le_refl _,
    fun i hi => absurd hi (by simp [erecTop1, h130'])⟩
  have hSol6 := hSol5.growF hfr (fun b hb => (biA_not_sol hb).1) (fun x hx hs => by
    simp only [solCtl, SOLC, SNEXTC, SCNTC, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> exact not_mem_biC (by decide) hx) hE56
  -- the walks' memos
  have hz : ∀ t : TieredArray, 210 ≤ t.arr ∧ t.arr ≤ 222 → ∀ j, rdW (m.arr64 t) j = 0 := fun t ht j => by
    rw [cmp_zero6 hF (OutEq.refl m) ht]; simp only [rdW, Array.getElem?_replicate]; split <;> rfl
  have hW : WalkMem m := ⟨⟨∅, memoRV_zeroAt ndSch bmKey _ m (by simp [ndSch]; omega) h220
      (hz NDM (by decide))⟩, ⟨∅, memoRV_zeroAt csSch nmKey _ m (by simp [csSch]; omega) h222
      (hz CSM (by decide))⟩, by simp [NTOPC]; omega, by simp [CTOPC]; omega⟩
  have hf9 : MemFrame [] flagC m6 (cmpExtM (m6.set64 CTL 224 1)) :=
    ((MemFrame.setCtl m6 224 1).mono (by simp) (by simp [flagC])).trans
      ((cmpExt_frame _).mono (by simp) (by simp [flagC]))
  have hW9 : WalkMem (cmpExtM (m6.set64 CTL 224 1)) :=
    ((((hW.frame h.frameM (not_mem_A64 (by decide)) (not_mem_A64 (by decide)) (not_mem_C64 (by decide))
      (not_mem_C64 (by decide))).frame hK.frame (by decide) (by decide) (by decide) (by decide)).frame
      hfr (fun hm => (biA_not_sol hm).2.1 rfl) (fun hm => (biA_not_sol hm).2.2 rfl)
      (not_mem_biC (by decide)) (not_mem_biC (by decide))).frame hf9 (by simp) (by simp) (by decide)
      (by decide))
  have hJS : JSol (some (solutionOf PS.IS res)) (cmpExtM (m6.set64 CTL 224 1)) :=
    ⟨⟨by
        simp only [ctlW, SOLC]
        rw [(cmpExt_frame _).ctl _ (by decide)]
        exact rdW_set64_self _ _ _ _ (by rw [hsz6]; simp; omega), hSol6.flagFrame hf9⟩,
      fun J' e => by
        cases e
        refine ⟨hW9, ?_⟩
        have := hF.build.nextLt
        show PS.IS.next + 1 < _
        omega⟩
  exact hJM6.setFlag hf9 hJS

/-- **The challenge's job relation after mode `6`**: the steps' twin facts, the challenge's index
build, and the job relation at the flushed memory, at the solution `solutionOf IS res`. -/
theorem F6.jobR (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) {c : Word} {m9 : Mem}
    (h6 : F6 PS m c m9) :
    ∃ (m2 m3 : Mem) (dsC : Array IDeclaration) (sG : AState) (res : List IDeclaration) (m4 : Mem)
      (I : IStreamIndex) (a' : AState),
      Side6 PS m c m2 m3 dsC sG res m4 ∧ buildIndex res.toArray sG = .ok (.ok I, a') ∧
      (FlushOK m9 → JobR PS.ipins (dnOf sG.store) res.toArray (some (solutionOf PS.IS res)) I
        (flushMem m9) { a' with caches := Caches.empty }) := by
  obtain ⟨m2, m3, dsC, sG, res, m4, I, a', h, hI, hJ, hwf, hoff, -⟩ := F6.jobM hF h6
  exact ⟨m2, m3, dsC, sG, res, m4, I, a', h, hI, fun hfok => hJ.flushR hwf hoff hfok⟩

end six

end L.Checker
