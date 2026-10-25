import ConAgua.Checker.ParEntryA
import ConAgua.Checker.IndArm
import ConAgua.Arena.PhaseAEntry

/-!
# Entry 1 at the checker's program: `checkA_run` (lane parmode)

docs/design/parmode.md, "Step 4" (a). A run of `check` from the loaded memory with the mode word
`MODE` set to `1` or `3` (`loadMemM b pb s8 s64 w`, what the stubs `ca_start_a`/`ca_start_a0`
hand it) that returns anything but `1` (a line that did not scan):

* the twin's stages before the loop ran and its phase A accepted (`PhaseA b`: `TwinPrefix` and
  `installFold … = .ok (.ok (k, fe, pend), sF)`);
* the memory after the fold, `m`, is `PhaseBStart … m sF v` at the fold's result `v` (the final
  view), and the final memory is the frozen buffer's, `parCompactMem m v (modeFlag w)`;
* the result is `2^63 + |pend|`.

The stages are `pipelineRefines_of_stages`' (`stageSpecs_of_rels` at `checkerRels`), except the
first three, which start from the loaded memory with the mode word set: no relation reads a global
(`R1`‥`R3` name the loaded memory only through its arrays), so their proofs are those of
`capStage_checker`, `pbStage_checker`, `irpStage_checker` at `loadMemM`. The fold at the
substituted program as `loopStage_of_rom` (`triple_subPB`), from `installFoldGo_start`.
-/

open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Checker

open L L.Arena L.Front L.Rom L.Compiler ConAgua.Final

/-- The memory an entry-1 stub hands to `check`: the loaded memory with the mode word `w`. -/
def loadMemM (b pb : ByteArray) (s8 s64 : List Nat) (w : Word) : Mem := (loadMem b pb s8 s64).setG MODE w

/-! ## The first three stages from the loaded memory with the mode word set -/

/-- A global write is a frame with no array write. -/
theorem memFrame_setG (m : Mem) (g : GVar) (w : Word) : MemFrame [] [] m (m.setG g w) :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩

theorem capStage_setG (b pb : ByteArray) (s8 s64 : List Nat) (hs : ∀ n ∈ s64, n < 2 ^ 64) (w : Word) :
    RelSpec checkerProg "cap_check" (· = loadMemM b pb s8 s64 w)
      fun _ m => m = loadMemM b pb s8 s64 w ∧ CapsOK (loadMem b pb s8 s64) := by
  intro n _hn s₀ hm
  refine triple_post (capCheck_spec checkerProg checkerProg_capCheck n s₀
    (hm ▸ loadMem_wordsFit b pb s8 s64 hs)) fun _ s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · rw [h2, hm]
  · rw [hm] at h3; exact h3

theorem pbStage_setG (b pb : ByteArray) (s8 s64 : List Nat) (hpb : pb.size < 2 ^ 63) (w : Word) :
    RelSpec checkerProg "pb_check" (fun m => m = loadMemM b pb s8 s64 w ∧ CapsOK (loadMem b pb s8 s64))
      fun _ m => m = loadMemM b pb s8 s64 w ∧ CapsOK (loadMem b pb s8 s64) ∧ PbPre pb := by
  intro n _hn s₀ ⟨hm, hc⟩
  refine triple_post (checkerProg_pbCheck_PB pb.data.toList (by simpa [RomOK] using hpb) n s₀
    (by rw [hm]; exact loadMem_pb b pb s8 s64)) fun _ s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, hc, h3⟩
  rw [h2, hm]

theorem irpStage_setG (b pb : ByteArray) (s8 s64 : List Nat) (hpb : pb.size < 2 ^ 63) (w : Word) :
    RelSpec checkerProg "intern_reserved_pins"
      (fun m => m = loadMemM b pb s8 s64 w ∧ CapsOK (loadMem b pb s8 s64) ∧ PbPre pb)
      fun _ m => ∃ a', internReservedPins (AState.init EStore.empty) = .ok ((), a') ∧
        R3 (loadMem b pb s8 s64) m pb a' := by
  intro n _hn s₀ ⟨hm, hc, hpre⟩
  have hirp := checkerProg_internReservedPins_PB pb.data.toList (by simpa [RomOK] using hpb) hpre n
    s₀ (AState.init EStore.empty) (by rw [hm]; exact loadMem_pb b pb s8 s64)
    (by rw [hm, loadMemM]; exact ArenaD.frameHi (memFrame_setG _ MODE w) (by simp) (by simp) (arenaD_loadMem b pb s8 s64 hc))
    (by rw [hm]; exact Or.inr (by show (rdW ((loadMem b pb s8 s64).arr64 CTL) 0).toNat < 2 ^ 40
                                  rw [loadMem_rd]; decide))
  refine triple_post (triple_and hirp (stage_since n (preLoop_mem "intern_reserved_pins"
    (by decide +kernel)) s₀)) fun _ s' ⟨⟨hl, hok, hA, hfull, hp0, hfr, hmo⟩, _, hk, hpf⟩ => ⟨hl, ?_⟩
  have hrun := AM.run_of_ok _ _ hok
  have hrun' : internReservedPins (AState.init EStore.empty) =
      .ok ((), AM.st internReservedPins (AState.init EStore.empty)) := hrun
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, hcachesA⟩ :=
    ConRon.Bridge.internReservedPins_run ⟨EStore.empty_wf⟩ rfl hrun'
  refine ⟨_, hrun', ?_⟩
  rw [hm] at hk hpf hfr
  have hk' : L.Keep (loadMem b pb s8 s64) s'.mem := hk
  have hpf' : MemFrame preLoopA preLoopC (loadMem b pb s8 s64) s'.mem := hpf
  have hfr' : MemFrame PinA StoreC (loadMem b pb s8 s64) s'.mem := hfr
  refine ⟨⟨hk', hc, by simpa [PbPre] using hpre, hpf'⟩, hA, ?_, ?_, ?_, hfull, hp0,
    ⟨hokA, hoffA, hpinsA, hppA, hfull.names_size⟩, hcachesA, ?_, hmo⟩
  · exact (stateDR_loadMem b pb s8 s64 hc).frame hfr' (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (pinA_not (by decide) (by decide)) pinA_idArrs storeC_idCtl
  · exact (rsetR_loadMem b pb s8 s64 hc).frame hfr' (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (not_mem_storeC _ (by decide)) (not_mem_storeC _ (by decide))
  · have := hfr'.2.1 131 (not_mem_storeC _ (by decide))
    simp only [stkTop] at this ⊢
    rw [this]; exact stkTop_loadMem b pb s8 s64
  · have z := loadMem_rd b pb s8 s64
    exact HZ.frame ⟨z _ _, z _ _, z _ _, z _ _, z _, z _⟩ hfr' (pinA_not (by decide) (by decide))
      (pinA_not (by decide) (by decide)) (not_mem_storeC _ (by decide)) (not_mem_storeC _ (by decide))
      (not_mem_storeC _ (by decide)) (not_mem_storeC _ (by decide))

end L.Checker
