import ConAgua.Checker.PipePrelude

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

theorem bytes_pos {l m : Mem} {pb : ByteArray} (h : Since l m pb) (hl : 0 < l.bytes.size) :
    0 < m.bytes.size := by rw [h.keep.1]; exact hl

theorem loadMem_bytes (b pb : ByteArray) (s8 s64 : List Nat) : 0 < (loadMem b pb s8 s64).bytes.size := by
  simp [loadMem]

theorem preludeStage_checker (h64 : System.Platform.numBits = 64) (b pb : ByteArray)
    (s8 s64 : List Nat) (a : AState) :
    RelSpec checkerProg "builtin_prelude" (fun m => R3 (loadMem b pb s8 s64) m pb a) fun _ m =>
      ∃ pre a', builtinPreludeE a = .ok (.ok pre, a') ∧ R4 (loadMem b pb s8 s64) m pb pre a' := by
  intro n s₀ h3
  refine triple_post (triple_and (triple_and (builtinPrelude_checker h64 a n s₀)
    (stage_since n (preLoop_mem "builtin_prelude" (by decide +kernel)) s₀))
    (stageFrame_builtin_prelude n s₀)) fun _ s' ⟨⟨⟨hl, hbp⟩, _, hk, hpf⟩, hsf⟩ => ⟨hl, ?_⟩
  have hc := CapsOK.keep h3.since.keep h3.since.caps
  obtain ⟨st, a', hb, hA, hD, ht, h240, hrk⟩ := hbp ⟨h3.arena, h3.sdr, h3.twin, hc.pool,
    bytes_pos h3.since (loadMem_bytes b pb s8 s64)⟩
  obtain ⟨hstep, -, -, -⟩ := ConRon.Bridge.Frontend.builtinPreludeE_run h3.twin.ok h3.twin.off
    h3.twin.pins hb
  have hpf0 : PinFacts s₀.mem a.pins := ⟨h3.rset, h3.stk, h3.pinsFull, h3.pin0⟩
  refine ⟨_, a', hb, h3.since.step hk hpf, hA, hD, h240, ?_, ht, ?_, hrk⟩
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

end L.Checker
