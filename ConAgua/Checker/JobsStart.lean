module

public import ConAgua.Checker.BuildStage
import ConRon.Bridge.Stages
import ConRon.Bridge.Checker.Install
import ConAgua.Checker.RomProgInit
public import ConAgua.Arena.Jobs

@[expose] public section

/-!
# The jobs' start after the index build (stage 3 of lane ronsync2)

`FoldAt.jobR`: after the index build (`FoldAt`, `Checker/BuildStage.lean`) and the worker's
cache flush (`check_b`'s first call: `flush_caches()`, the L side of `AState.worker`'s empty
caches), the memory is `JobR` at the index state with its caches emptied, which enters the
scratch tier as the index state's worker does (`sameEnter_worker`).
-/

open ConRon.Arena ConRon.Arena.Frontend

namespace L.Checker

open L L.Arena L.Rom

theorem loCtl_flush : LoCtl flushCtl := fun x h => .inr ⟨by have := flushCtl_ge x h; omega, flushCtl_lt x h⟩

theorem loArr_nil : LoArr [] := fun _ h => absurd h (by simp)

/-- The twin's facts of the stages, and the index build's, at a phase A. -/
theorem PhaseA.twin {b : ByteArray} (PA : PhaseA b) :
    Ext PA.sE.store PA.sF.store ∧ PA.sF.pins = PA.sE.pins := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := PA.pfx
  obtain ⟨hoff, hdrv, hpp, -, -, hpd, _rc, _preC, -, hden⟩ :=
    ConRon.Bridge.stages_frame (chunks := [b]) hA hB hC hD hE
  obtain ⟨-, hx, hp, -⟩ := ConRon.Bridge.buildIndex_run ConRon.Bridge.constsSpec
    ConRon.Bridge.tablesSpec hdrv hpp hoff hpd hden PA.idx
  exact ⟨hx, hp⟩

/-- **The solution's flag after the index build** is the loaded memory's `0`: neither the stages
before the loop (`preLoopC`) nor the index build (`biC`) write `CTL[224]`. -/
theorem FoldAt.c224 {b pb : ByteArray} {sz : TieredArray → Nat} {PA : PhaseA b} {m₇ m : Mem}
    (h : FoldAt b pb sz PA m₇ m) : rdW (m.arr64 CTL) 224 = 0 := by
  rw [h.frame.ctl _ (not_mem_biC (by decide)), h.r7.since.frame.ctl _ (by decide)]
  exact loadMem_rd b pb sz CTL 224

/-- **The jobs' start**: after the index build and the cache flush, `JobR` at the index state
with its caches emptied (the twin's worker state, `AState.worker`: the scratch tier and memos as
every job's `enterScratch` leaves them, `Arena/JobStart.lean`). -/
@[refines ConRon.Arena.AState.worker]
theorem FoldAt.jobR {b pb : ByteArray} {sz : TieredArray → Nat} {PA : PhaseA b} {m₇ m : Mem}
    (h : FoldAt b pb sz PA m₇ m) (hfok : FlushOK m) :
    JobR PA.ipins (dnOf PA.sE.store) PA.ds none PA.I (flushMem m) { PA.sF with caches := Caches.empty } := by
  have hB := h.build
  have hS := hB.stage
  have hF := flushMem_frame m
  have hA0 := loArr_nil
  have hC0 := loCtl_flush
  have h7 := h.r7
  have hcaps := h7.since.caps
  have hsz : ∀ t, ((flushMem m).arr64 t).size = ((ConAgua.Final.loadMem b pb sz).arr64 t).size :=
    fun t => by rw [hF.size, h.frame.size, h7.since.frame.size]
  have hx := PA.twin.1
  have hD := hS.check.arena.caches_irrel Caches.empty
  refine ⟨⟨⟨ArenaR.frame_ext [] _ (by simp) flushCtl_ge _ _ hF _ hD.base,
      DerR.frameM [] _ _ _ hF (by simp) _ hD.der⟩, hS.check.core.flush hfok,
    hS.check.pins.frame (fun _ h => absurd h (by simp)) hF, hS.check.mode.frame hF (by decide) (by decide),
    hB.idx.frameLo hA0 hC0 hF, hS.check.env.ownBelow.frameLo hA0 hC0 hF,
    by rw [stampW_frameLo hC0 hF]; exact hS.check.env.stamp, declsF_frameLo hA0 hF hB.decls,
    iwOK_frameLo hA0 hC0 hF hS.iw, ?_, pinSetsR_frameLo hA0 hC0 hF ?_, ?_, ?_,
    hB.memos.frameLo hA0 hC0 hF, h.fsize, h.frozen.frameLo hC0 hF,
    JSol.none (by rw [hC0.ctl hF (by decide)]; exact h.c224)⟩, ⟨hB.drv.state.wf⟩, hB.off, rfl⟩
  · rw [hC0.ctl hF (by decide), h.grow.ctl130]; exact h7.c130
  · exact PinSetsR.grow h7.pinSets h.grow.grow (h.frame.ctl _ (not_mem_biC (by decide)))
      (h.frame.ctl _ (not_mem_biC (by decide)))
  · refine ⟨?_, ?_, ?_, (h.grow.memos ?_).frameLo hA0 hC0 hF, fun k x hk => ?_⟩
    · rw [hsz]; have := hcaps.2.2.2.2.2.2.1; omega
    · rw [hsz]; have := (hcaps.1 SPN (by decide)).1; omega
    · rw [hsz]; have := (hcaps.1 BSTK (by decide)).1; omega
    · exact since_coreMemos h7.since (by rw [h7.since.frame.size]; have := hcaps.2.1; simp only [ctlMin] at this; omega)
    · simp only [dnOf] at hk
      split at hk
      · exact ConRon.Bridge.denoteN_ext hk hx
      · cases hk
  · rw [pinW_frame hF (by simp), pinW_frame h.frame (by simp [biA])]; exact h7.pin0

/-- **The jobs' memory half after the index build**, before the flush, at the index state. -/
theorem FoldAt.jobM {b pb : ByteArray} {sz : TieredArray → Nat} {PA : PhaseA b} {m₇ m : Mem}
    (h : FoldAt b pb sz PA m₇ m) : JobM PA.ipins (dnOf PA.sE.store) PA.ds none PA.I m PA.sF := by
  have hB := h.build
  have hS := hB.stage
  have hF : MemFrame [] [] m m := MemFrame.refl _ _ _
  have hA0 := loArr_nil
  have hC0 : LoCtl [] := fun _ h => absurd h (by simp)
  have h7 := h.r7
  have hcaps := h7.since.caps
  have hsz : ∀ t, (m.arr64 t).size = ((ConAgua.Final.loadMem b pb sz).arr64 t).size :=
    fun t => by rw [h.frame.size, h7.since.frame.size]
  have hx := PA.twin.1
  refine ⟨hS.check.arena, hS.check.core, hS.check.pins, hS.check.mode,
    hB.idx, hS.check.env.ownBelow, hS.check.env.stamp, hB.decls, hS.iw, ?_,
    PinSetsR.grow h7.pinSets h.grow.grow (h.frame.ctl _ (not_mem_biC (by decide)))
      (h.frame.ctl _ (not_mem_biC (by decide))), ?_, ?_, hB.memos, h.fsize, h.frozen, JSol.none h.c224⟩
  · rw [h.grow.ctl130]; exact h7.c130
  · refine ⟨?_, ?_, ?_, h.grow.memos ?_, fun k x hk => ?_⟩
    · rw [hsz]; have := hcaps.2.2.2.2.2.2.1; omega
    · rw [hsz]; have := (hcaps.1 SPN (by decide)).1; omega
    · rw [hsz]; have := (hcaps.1 BSTK (by decide)).1; omega
    · exact since_coreMemos h7.since (by rw [h7.since.frame.size]; have := hcaps.2.1; simp only [ctlMin] at this; omega)
    · simp only [dnOf] at hk
      split at hk
      · exact ConRon.Bridge.denoteN_ext hk hx
      · cases hk
  · rw [pinW_frame h.frame (by simp [biA])]; exact h7.pin0

/-- **`JobR` across a memory with the same word arrays** (the globals, the byte arrays). -/
theorem _root_.L.Arena.JobR.frame0 {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {J : Option ISolution} {I : IStreamIndex} {M M' : Mem} {a : AState}
    (h : JobR pins dn ds J I M a) (hf : MemFrame [] [] M M') : JobR pins dn ds J I M' a := by
  have hA : LoArr [] := loArr_nil
  have hC : LoCtl [] := fun _ h => absurd h (by simp)
  refine ⟨⟨⟨ArenaR.frame_ext [] _ (by simp) (by simp) _ _ hf _ h.arena.base,
      DerR.frameM [] _ _ _ hf (by simp) _ h.arena.der⟩,
    h.core.frame (fun _ h => absurd h (by simp)) (fun _ h => absurd h (by simp)) hf,
    h.pinsR.frame (fun _ h => absurd h (by simp)) hf, h.mode.frame hf (by simp) (by simp),
    h.idx.frameLo hA hC hf, h.below.frameLo hA hC hf,
    by rw [stampW_frameLo hC hf]; exact h.stamp, declsF_frameLo hA hf h.decls, iwOK_frameLo hA hC hf h.iw,
    by rw [hC.ctl hf (by decide)]; exact h.top1, pinSetsR_frameLo hA hC hf h.pinsets,
    h.mem.frameLo hA hC hf fun k x e => ?_, by rw [pinW_frame hf (by simp)]; exact h.flag,
    h.memos.frameLo hA hC hf, h.fsize, h.frozen.frameLo hC hf, h.jsol.frameLo hA hC hf⟩, h.state, h.off,
    h.caches⟩
  exact h.mem.dnN k x e

/-- `JobR` reads no global. -/
theorem _root_.L.Arena.JobR.setGlob {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {J : Option ISolution} {I : IStreamIndex} {M : Mem} {a : AState}
    (h : JobR pins dn ds J I M a) (g : GVar → Word) : JobR pins dn ds J I ⟨M.bytes, M.words, g⟩ a :=
  h.frame0 ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

end L.Checker
