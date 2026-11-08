module

public import ConAgua.Checker.VerdictEntry1
import ConAgua.Checker.NoVerdictClosed
import ConAgua.Checker.PreludeRef
import ConAgua.Checker.RomProgInit
import ConAgua.Front.ChunkBridge
import ConAgua.Front.FrontRunRef
import ConAgua.Verdict.FrontSafeE

@[expose] public section

/-!
# The frontend's two stages' error specs: `builtin_prelude`, `front_run`

`Entry1StagesE.prelude` and `.front` (`Checker/VerdictEntry1.lean`): the error halves of
`builtinPrelude_ref` (`Checker/PreludeRef.lean`) and of `front_run`'s refinement at the checker's
program (`frontRun_errClaim`, `Front/FrontRunRef.lean`).
-/

open ConRon.Arena
open ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order
open L.Arena L.Front ConAgua.Final

namespace L.Checker

/-- **`Entry1StagesE.prelude`'s statement**: `builtinPrelude_ref`'s error half. -/
theorem checker_preludeStageE : ∀ b pb sz, InputsOK b pb sz →
    StageSpecE checkerProg "builtin_prelude" [] (Q3 b (checkerRels b pb sz)) (TwinVerdict [b]) := by
  sorry

/-- **`Entry1StagesE.front`'s statement**: `front_run`'s error half at the checker's program. -/
theorem checker_frontStageE : ∀ b pb sz, InputsOK b pb sz →
    StageSpecE checkerProg "front_run" [] (Q4 b (checkerRels b pb sz)) (TwinVerdict [b]) := by
  intro b pb sz hin n _hn s₀
  refine M.triple_of_run' (fun _ _ _ _ _ => trivial) fun s e hs hr hQ hk => ?_
  subst hs
  obtain ⟨sA, pre, sB, hA, hB, h4⟩ := hQ
  have h4 : R4 (loadMem b pb sz) s.mem pb pre sB := h4
  have hm : s.mem.arr8 IN = b.data := by rw [h4.since.keep.arr8]; exact loadMem_in b pb sz
  have hf := frontRun_errClaim pre.decls b hin.1 hin.2.1 (safeLink hin.1 b hin.2.1) n s.mem sB
    ⟨hm, h4.arena, h4.sdr, h4.twin.ok, h4.twin.off, h4.twin.pins, h4.rok, h4.mode⟩
    (L.Front.callE_of_run_err hr) hk
  have hu : b.size < USize.size := by
    rw [show USize.size = 2 ^ 64 by simp [USize.size, hin.1]]; have := hin.2.1; omega
  refine TwinVerdict.front hA hB ?_
  rw [ConAgua.Front.ChunkBridge.parseChunks_single b hu]
  exact hf

end L.Checker
