module

import ConAgua.Checker.PreludeRef
import ConAgua.Checker.PrepRef
import ConAgua.Checker.TwinPins
public import ConAgua.Checker.PreLoopWSStages
import ConAgua.Checker.PrepProgExt
import all ConRon.Bridge.Frontend.Prepare
import ConAgua.Checker.PrepProgHoist
import ConAgua.Checker.RomProg
import ConAgua.Checker.RomProgInit
import ConAgua.Front.ChunkBridge
import ConAgua.Front.FrontRunRef
import ConRon.Bridge.Checker.Pins
public import ConAgua.Checker.PipePrelude

@[expose] public section

/-!
# The stages after `intern_reserved_pins` (lane `pipeline`)

The relations `R4`‥`R7` and the stages `builtin_prelude`, `front_run`, `prepare_prelude`,
`intern_all_pins` at `checkerProg`. The facts about the pin table, `RSET`'s memo and the ROM
stack (`PinFacts`) ride along each stage that does not write them (per-stage write sets,
`PreLoopWSStages.lean`).
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

/-- The pin table, `RSET`'s memo, the ROM stack. -/
structure PinFacts (m : Mem) (p : Pins) : Prop where
  rset : RsetR m
  stk : stkTop m = 0
  full : PinsFull m p
  pin0 : pinW m 0 ≠ 0

theorem PinFacts.frame {A : List TieredArray} {C : List Word} {m m' : Mem} {p : Pins} (h : PinFacts m p)
    (hf : MemFrame A C m m') (hP : (PINS : TieredArray) ∉ A) (hR1 : (RSET : TieredArray) ∉ A)
    (hR2 : (RMEMO : TieredArray) ∉ A)
    (h131 : (131 : Word) ∉ C) (h132 : (132 : Word) ∉ C) (h148 : (148 : Word) ∉ C) :
    PinFacts m' p := by
  have he : m'.arr64 PINS = m.arr64 PINS := hf.arr _ hP (by decide)
  refine ⟨h.rset.frame hf hR1 hR2 h148 h132, ?_, h.full.congr he, ?_⟩
  · simp only [stkTop] at h ⊢; rw [hf.ctl 131 h131]; exact h.stk
  · simp only [pinW, he]; exact h.pin0

/-- **After `builtin_prelude`**: the prelude's records are `DECL[0‥P)`, `P` in `CTL[240]`, the id
tables empty. -/
structure R4 (l m : Mem) (pb : ByteArray) (pre : PreludeIx) (a : AState) : Prop where
  since : Since l m pb
  arena : ArenaD m a
  sdr : StateDR m (StateD.blank.pre pre.decls)
  np : (rdW (m.arr64 CTL) 240).toNat = pre.decls.size
  pf : PinFacts m a.pins
  twin : TwinFacts a
  hz : HZ m
  rok : RecsOK m pre.decls
  mode : ModeOK m

theorem preludeStage_checker (h64 : System.Platform.numBits = 64) (b pb : ByteArray)
    (sz : TieredArray → Nat) (a : AState) :
    RelSpec checkerProg "builtin_prelude" (fun m => R3 (loadMem b pb sz) m pb a) fun _ m =>
      ∃ pre a', builtinPreludeE a = .ok (.ok pre, a') ∧ R4 (loadMem b pb sz) m pb pre a' := by
  sorry

/-! ## `front_run` -/

/-- **After `front_run`**: `DECL` holds the prelude's records, then the stream's. -/
structure R5 (l m : Mem) (pb : ByteArray) (pre : PreludeIx) (rc : ParseResultD) (a : AState) : Prop where
  since : Since l m pb
  arena : ArenaD m a
  decls : DeclsF (m.arr64 DECL) (m.arr64 DLP) (pre.decls ++ rc.decls)
  np : (rdW (m.arr64 CTL) 240).toNat = pre.decls.size
  pf : PinFacts m a.pins
  twin : TwinFacts a
  hz : HZ m
  rok : RecsOK m (pre.decls ++ rc.decls)
  mode : ModeOK m

theorem loadMem_in (b pb : ByteArray) (sz : TieredArray → Nat) : (loadMem b pb sz).arr8 IN = b.data := by
  simp [loadMem, Mem.arr8, IN]

theorem frontStage_checker (h64 : System.Platform.numBits = 64) (b pb : ByteArray)
    (hb : b.size < 2 ^ 63) (sz : TieredArray → Nat) (pre : PreludeIx) (a : AState) :
    RelSpec checkerProg "front_run" (fun m => R4 (loadMem b pb sz) m pb pre a) fun r m =>
      r.headD 0 = 0 → ∃ rc a', parseChunks [b] a = .ok (.ok rc, a') ∧
        R5 (loadMem b pb sz) m pb pre rc a' := by
  sorry

/-! ## `prepare_prelude` -/

/-- A memo whose stamps are all `0` at epoch word `0` is the empty memo (as loopt2's
`memoRV_zeroAt`, `Arena/LoopT.lean`). -/
theorem memoRV_zero0 {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
    (S : MemoSch) (K : MemoKey κ) (VR : Mem → Word → ν → Prop) (m : Mem)
    (hctl : S.cs.toNat + 2 ≤ (m.arr64 CTL).size) (he : rdW (m.arr64 CTL) S.cs = 0)
    (hz : ∀ j, rdW (m.arr64 S.arr) j = 0) : MemoRV S K VR m (∅ : Std.HashMap κ ν) := by
  have hep : epG S m = 1 := by simp [epG, he]
  exact memoRV_fresh S K VR m hctl (by rw [hep]; decide) (by rw [hep, hz]; decide)
    (fun j _ => by rw [hep]; simp [mstG, hz])

/-- **After `prepare_prelude`**: `DECL` holds the prepared records. -/
structure R6 (l m : Mem) (pb : ByteArray) (ds : Array IDeclaration) (a : AState) : Prop where
  since : Since l m pb
  arena : ArenaD m a
  decls : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds
  pf : PinFacts m a.pins
  iw : L.Ind.IWOK m
  mode : ModeOK m

theorem prepareStage_checker (b pb : ByteArray) (sz : TieredArray → Nat) (pre : PreludeIx)
    (rc : ParseResultD) (a : AState) :
    RelSpec checkerProg "prepare_prelude" (fun m => R5 (loadMem b pb sz) m pb pre rc a) fun _ m =>
      ∃ ds a', preparePrelude pre rc.decls a = .ok (ds, a') ∧ R6 (loadMem b pb sz) m pb ds a' := by
  sorry

/-! ## `intern_all_pins` -/

/-- The twin's facts before `internAllPins` (as `Final/Twin.lean`'s `stages_frame`). -/
theorem prefix4_facts {b : ByteArray} {sA : AState} {pre : PreludeIx} {sB : AState}
    {rc : ParseResultD} {sC : AState} {ds : Array IDeclaration} {sD : AState}
    (h : TwinPrefix4 b sA pre sB rc sC ds sD) :
    ConRon.Bridge.StateOK sD ∧ sD.store.scratchOn = false ∧ ConRon.Bridge.PinsOK sD ∧
      ConRon.Bridge.PersPins sD := by
  obtain ⟨hA, hB, hC, hD⟩ := h
  have hok0 : ConRon.Bridge.StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, -⟩ := ConRon.Bridge.internReservedPins_run hok0 rfl hA
  obtain ⟨hstep1, hpersPre, preC, hrelPre⟩ :=
    ConRon.Bridge.Frontend.builtinPreludeE_run hokA hoffA hpinsA hB
  obtain ⟨hstep2, hpersR, rc', hclR, hrelR⟩ :=
    ConRon.Bridge.Frontend.parseChunks_run hstep1.ok
      (by rw [hstep1.scratch, hoffA]) (hpinsA.mono hstep1.ext hstep1.pins) hC
  obtain ⟨hstep3, -, -⟩ :=
    ConRon.Bridge.Frontend.preparePrelude_run (preC := preC) hstep2.ok
      (by rw [hstep2.scratch, hstep1.scratch, hoffA])
      (hpinsA.mono (hstep1.trans hstep2).ext (hstep1.trans hstep2).pins)
      (ConRon.Bridge.Frontend.denoteDeclArray_ext hstep2.ext hrelPre) hpersPre
      hrelR.decls hpersR hD
  refine ⟨hstep3.ok, by rw [hstep3.scratch, hstep2.scratch, hstep1.scratch]; exact hoffA,
    hpinsA.mono ((hstep1.ext.trans hstep2.ext).trans hstep3.ext)
      (by rw [hstep3.pins, hstep2.pins, hstep1.pins]),
    hppA.mono (by rw [hstep3.pins, hstep2.pins, hstep1.pins])⟩

/-- **After `intern_all_pins`**: what the declaration loop starts from (with the twin's prefix:
`foldStage_checker`, `CheckARun.lean`). Everything else is still the loaded memory's: `since.frame` (`MemFrame preLoopA
preLoopC`, `PreLoopWS.lean`). -/
structure R7 (l m : Mem) (pb : ByteArray) (ds : Array IDeclaration) (ipins : List INatOpPinSet)
    (a : AState) : Prop where
  since : Since l m pb
  arena : ArenaD m a
  decls : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds
  pinSets : PinSetsR m ipins
  rset : RsetR m
  pin0 : pinW m 0 ≠ 0
  pinsFull : PinsFull m a.pins
  iw : L.Ind.IWOK m
  mode : ModeOK m

theorem pinsStage_checker (b pb : ByteArray) (sz : TieredArray → Nat) (hpb : pb.size < 2 ^ 63)
    (sA : AState) (pre : PreludeIx) (sB : AState) (rc : ParseResultD) (sC : AState)
    (ds : Array IDeclaration) (a : AState) (hpx : TwinPrefix4 b sA pre sB rc sC ds a) :
    RelSpec checkerProg "intern_all_pins" (fun m => R6 (loadMem b pb sz) m pb ds a) fun _ m =>
      ∃ pins ipins a', internAllPins pins a = .ok (ipins, a') ∧
        R7 (loadMem b pb sz) m pb ds ipins a' := by
  sorry

end L.Checker
