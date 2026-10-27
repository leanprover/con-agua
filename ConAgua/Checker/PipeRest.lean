import ConAgua.Checker.PipePrelude
import ConAgua.Checker.PrepRef
import ConAgua.Checker.TwinPins
import ConAgua.Checker.PreLoopWSStages

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

theorem PinFacts.frame {A : List ArrId} {C : List Word} {m m' : Mem} {p : Pins} (h : PinFacts m p)
    (hf : MemFrame A C m m') (hP : PINS ∉ A) (hR1 : RSET ∉ A) (hR2 : RMEMO ∉ A)
    (h131 : (131 : Word) ∉ C) (h132 : (132 : Word) ∉ C) (h148 : (148 : Word) ∉ C) :
    PinFacts m' p := by
  have he : m'.arr64 PINS = m.arr64 PINS := hf.1 PINS hP (by decide)
  refine ⟨h.rset.frame hf hR1 hR2 h148 h132, ?_, h.full.congr he, ?_⟩
  · simp only [stkTop] at h ⊢; rw [hf.2.1 131 h131]; exact h.stk
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

theorem bytes_pos {l m : Mem} {pb : ByteArray} (h : Since l m pb) (hl : 0 < l.bytes.size) :
    0 < m.bytes.size := by rw [h.keep.1]; exact hl

theorem loadMem_bytes (b pb : ByteArray) (s8 s64 : List Nat) : 0 < (loadMem b pb s8 s64).bytes.size := by
  simp [loadMem]

theorem preludeStage_checker (h64 : System.Platform.numBits = 64) (b pb : ByteArray)
    (s8 s64 : List Nat) (a : AState) :
    RelSpec checkerProg "builtin_prelude" (fun m => R3 (loadMem b pb s8 s64) m pb a) fun _ m =>
      ∃ pre a', builtinPreludeE a = .ok (.ok pre, a') ∧ R4 (loadMem b pb s8 s64) m pb pre a' := by
  intro n _hn s₀ h3
  refine triple_post (triple_and (triple_and (builtinPrelude_checker h64 a n _hn s₀)
    (stage_since n (preLoop_mem "builtin_prelude" (by decide +kernel)) s₀))
    (stageFrame_builtin_prelude n s₀)) fun _ s' ⟨⟨⟨hl, hbp⟩, _, hk, hpf⟩, hsf⟩ => ⟨hl, ?_⟩
  have hc := CapsOK.keep h3.since.keep h3.since.caps
  obtain ⟨st, a', hb, hA, hD, ht, h240, hrk, hmo⟩ := hbp ⟨h3.arena, h3.sdr, h3.twin, by have := hc.pool; omega,
    bytes_pos h3.since (loadMem_bytes b pb s8 s64), h3.mode⟩
  obtain ⟨hstep, -, -, -⟩ := ConRon.Bridge.Frontend.builtinPreludeE_run h3.twin.ok h3.twin.off
    h3.twin.pins hb
  have hpf0 : PinFacts s₀.mem a.pins := ⟨h3.rset, h3.stk, h3.pinsFull, h3.pin0⟩
  refine ⟨_, a', hb, h3.since.step hk hpf, hA, hD, h240, ?_, ht, ?_, hrk, hmo⟩
  rotate_left
  · exact h3.hz.frame hsf (by decide +kernel) (by decide +kernel)
      (not_mem_of_toNat (Z := [73, 75, 129, 200]) (by decide +kernel) _ (by decide))
      (not_mem_of_toNat (Z := [73, 75, 129, 200]) (by decide +kernel) _ (by decide))
      (not_mem_of_toNat (Z := [73, 75, 129, 200]) (by decide +kernel) _ (by decide))
      (not_mem_of_toNat (Z := [73, 75, 129, 200]) (by decide +kernel) _ (by decide))
  rw [hstep.pins]
  exact hpf0.frame hsf stageA_builtin_prelude_pins (by decide +kernel) (by decide +kernel)
    (stageC_builtin_prelude_off _ (by decide)) (stageC_builtin_prelude_off _ (by decide))
    (stageC_builtin_prelude_off _ (by decide))

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

theorem loadMem_in (b pb : ByteArray) (s8 s64 : List Nat) : (loadMem b pb s8 s64).arr8 IN = b.data := by
  simp [loadMem, Mem.arr8, IN]

theorem frontStage_checker (h64 : System.Platform.numBits = 64) (b pb : ByteArray)
    (hb : b.size < 2 ^ 63) (s8 s64 : List Nat) (pre : PreludeIx) (a : AState) :
    RelSpec checkerProg "front_run" (fun m => R4 (loadMem b pb s8 s64) m pb pre a) fun r m =>
      r.headD 0 = 0 → ∃ rc a', parseChunks [b] a = .ok (.ok rc, a') ∧
        R5 (loadMem b pb s8 s64) m pb pre rc a' := by
  intro n _hn s₀ h4
  have hc := CapsOK.keep h4.since.keep h4.since.caps
  have hm : s₀.mem.arr8 IN = b.data := by rw [h4.since.keep.arr8]; exact loadMem_in b pb s8 s64
  refine triple_post (triple_and (triple_and (L.Front.frontRunOK_checker pre.decls b h64 hb n s₀ hm (by have := hc.pool; omega)
    a h4.arena h4.sdr h4.twin.ok h4.twin.off h4.twin.pins h4.rok h4.mode)
    (stage_since n (preLoop_mem "front_run" (by decide +kernel)) s₀))
    (stageFrame_front_run n s₀)) fun r s' ⟨⟨hpost, hl, hk, hpf⟩, hsf⟩ => ⟨hl, fun h0 => ?_⟩
  obtain ⟨st, a', hp, hA, hD, hto, hM, hR⟩ := hpost h0
  have hu : b.size < USize.size := by
    rw [show USize.size = 2 ^ 64 by simp [USize.size, h64]]; omega
  have hcp : parseChunks [b] a = .ok (.ok (.ofState st), a') := by
    have := ConAgua.Front.ChunkBridge.parseChunks_single b hu
    rw [this]; exact hp
  obtain ⟨hstep, -, -⟩ := ConRon.Bridge.Frontend.parseChunks_run h4.twin.ok h4.twin.off h4.twin.pins hcp
  refine ⟨_, a', hcp, ⟨h4.since.step hk hpf, hA, hD.decls, ?_, ?_, ?_, ?_, ?_, hM⟩⟩
  · rw [hsf.2.1 240 (stageC_front_run_off _ (by decide))]; exact h4.np
  · rw [hstep.pins]
    exact h4.pf.frame hsf stageA_front_run_pins (by decide +kernel) (by decide +kernel)
      (stageC_front_run_off _ (by decide)) (stageC_front_run_off _ (by decide))
      (stageC_front_run_off _ (by decide))
  · exact ⟨hto.1, hto.2.1, hto.2.2.1, h4.twin.pers.mono hstep.pins,
      by simp only [PinsReadyP, hstep.pins]; exact h4.twin.ready⟩
  · exact h4.hz.frame hsf (by decide +kernel) (by decide +kernel)
      (not_mem_of_toNat (Z := [73, 75, 129, 200]) (by decide +kernel) _ (by decide))
      (not_mem_of_toNat (Z := [73, 75, 129, 200]) (by decide +kernel) _ (by decide))
      (not_mem_of_toNat (Z := [73, 75, 129, 200]) (by decide +kernel) _ (by decide))
      (not_mem_of_toNat (Z := [73, 75, 129, 200]) (by decide +kernel) _ (by decide))
  · exact fun x hx => hR x (by simpa [ParseResultD.ofState] using hx)

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

theorem prepareStage_checker (b pb : ByteArray) (s8 s64 : List Nat) (pre : PreludeIx)
    (rc : ParseResultD) (a : AState) :
    RelSpec checkerProg "prepare_prelude" (fun m => R5 (loadMem b pb s8 s64) m pb pre rc a) fun _ m =>
      ∃ ds a', preparePrelude pre rc.decls a = .ok (ds, a') ∧ R6 (loadMem b pb s8 s64) m pb ds a' := by
  intro n _hn s₀ h5
  have hc := CapsOK.keep h5.since.keep h5.since.caps
  have hctl : 256 ≤ (s₀.mem.arr64 CTL).size := hc.2.1
  have hI : L.Ind.IWOK s₀.mem := by
    refine ⟨?_, ?_, ?_, ?_, by omega⟩
    · simp only [L.Ind.iwTop, h5.hz.c200]; simp
    · simp only [L.Ind.erTop, h5.hz.c129]; simp
    · have := hc.1 L.Ind.IW (by decide); omega
    · have := hc.1 EREC (by decide); omega
  have hseen : ∃ s, L.Checker.SeenR s₀.mem s :=
    ⟨∅, memoRV_zero0 hsSch bmKey _ s₀.mem (by simp; omega) h5.hz.c73 h5.hz.seen⟩
  have hnix : ∃ idx, NixR s₀.mem idx :=
    ⟨∅, memoRV_zero0 hnSch nmKey _ s₀.mem (by simp; omega) h5.hz.c75 h5.hz.nix⟩
  have hdsz : (s₀.mem.arr64 DECL).size < 2 ^ 64 := by have := hc.1 DECL (by decide); omega
  refine triple_post (triple_and (triple_and (preparePrelude_refines checkerProg checkerProg_prepProg
    checkerProg_prepExt checkerProg_hoistProg checkerProg_hoistExt n s₀ a pre rc.decls
    (fun x hx => ⟨h5.decls.recs x hx, h5.rok x hx⟩) (by simpa [rdW] using h5.decls.count) h5.np
    h5.decls.room hdsz h5.arena.1 hseen hnix hI
    ⟨fun _ => h5.pf.full⟩)
    (stage_since n (preLoop_mem "prepare_prelude" (by decide +kernel)) s₀))
    (stageFrame_prepare_prelude n s₀)) fun _ s' ⟨⟨⟨hl, hpost⟩, _, hk, hpf⟩, hsf⟩ => ⟨hl, ?_⟩
  obtain ⟨ds', a', hrun, hcnt, hrecs, hAR, hIW, -, hDLP, hDs, hpe, hse, hpins, hle⟩ := hpost
  refine ⟨ds', a', hrun, h5.since.step hk hpf,
    ⟨hAR, L.Front.DerR.congrSt hpe hse (DerR.frameM _ _ _ _ hsf (by decide +kernel) _ h5.arena.2)⟩, ?_, ?_, hIW,
    ModeOK.frame h5.mode hsf (not_mem_of_toNat (Z := [0, 1]) (by decide +kernel) _ (by decide))
      (not_mem_of_toNat (Z := [0, 1]) (by decide +kernel) _ (by decide))⟩
  · refine ⟨by rw [hDs]; have := hc.1 DECL (by decide); omega, by rw [hDLP]; exact h5.decls.psize,
      by simpa [rdW] using hcnt, ?_, by rw [hDLP]; exact h5.decls.ptop, fun i hi => (hrecs i hi).1⟩
    rw [hDs]; have := h5.decls.room; omega
  · rw [hpins]
    exact h5.pf.frame hsf stageA_prepare_prelude_pins (by decide +kernel) (by decide +kernel)
      (stageC_prepare_prelude_off _ (by decide)) (stageC_prepare_prelude_off _ (by decide))
      (stageC_prepare_prelude_off _ (by decide))

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

theorem pinsStage_checker (b pb : ByteArray) (s8 s64 : List Nat) (hpb : pb.size < 2 ^ 63)
    (sA : AState) (pre : PreludeIx) (sB : AState) (rc : ParseResultD) (sC : AState)
    (ds : Array IDeclaration) (a : AState) (hpx : TwinPrefix4 b sA pre sB rc sC ds a) :
    RelSpec checkerProg "intern_all_pins" (fun m => R6 (loadMem b pb s8 s64) m pb ds a) fun _ m =>
      ∃ pins ipins a', internAllPins pins a = .ok (ipins, a') ∧
        R7 (loadMem b pb s8 s64) m pb ds ipins a' := by
  intro n _hn s₀ h6
  have hc := CapsOK.keep h6.since.keep h6.since.caps
  obtain ⟨hok, hoff, hpins, hpp⟩ := prefix4_facts hpx
  have hbs : s₀.mem.arr8 PB = pb.data.toList.toArray := by
    rw [h6.since.keep.arr8]; exact loadMem_pb b pb s8 s64
  refine triple_post (triple_and (triple_and (checkerProg_internAllPins_PB pb.data.toList
    (by simpa [RomOK] using hpb) h6.since.pbpre n s₀ a hbs h6.arena h6.mode h6.pf.full.names_size hok hpins hpp
    hoff h6.pf.rset (by rw [h6.pf.stk]; decide) hc.ctl)
    (stage_since n (preLoop_mem "intern_all_pins" (by decide +kernel)) s₀))
    (stageFrame_intern_all_pins n s₀)) fun _ s' ⟨⟨⟨hl, hpost⟩, _, hk, hpf⟩, hsf⟩ => ⟨hl, ?_⟩
  obtain ⟨pins, ips, a', hrun, hA, hPS, -, hR, htop, hM⟩ := hpost
  have hpins' : a'.pins = a.pins := TwinCaches.internAllPins_pins hok hpins hoff hrun
  have hPINS : s'.mem.arr64 PINS = s₀.mem.arr64 PINS := hsf.1 PINS (by decide +kernel) (by decide)
  have h200 : rdW (s'.mem.arr64 CTL) 200 = rdW (s₀.mem.arr64 CTL) 200 :=
    hsf.2.1 200 (not_mem_of_toNat (Z := [200]) (by decide +kernel) _ (by decide))
  have hIW : s'.mem.arr64 L.Ind.IW = s₀.mem.arr64 L.Ind.IW := hsf.1 _ (by decide +kernel) (by decide)
  have hc' := CapsOK.keep (h6.since.step hk hpf).keep h6.since.caps
  refine ⟨pins, ips, a', hrun, h6.since.step hk hpf, hA, ?_, hPS, hR, ?_,
    by rw [hpins']; exact h6.pf.full.congr hPINS, ?_, hM⟩
  · rw [hsf.1 DECL (by decide +kernel) (by decide), hsf.1 DLP (by decide +kernel) (by decide)]
    exact h6.decls
  · simp only [pinW, hsf.1 PINS (by decide +kernel) (by decide)]; exact h6.pf.pin0
  · refine ⟨?_, htop, ?_, ?_, ?_⟩
    · simp only [L.Ind.iwTop, h200, hIW]; exact h6.iw.1
    · have := hc'.1 L.Ind.IW (by decide); omega
    · have := hc'.1 EREC (by decide); omega
    · have := hc'.2.1; simp only [ctlMin] at this; omega

end L.Checker
