import ConAgua.L.Notation
import ConAgua.Final.Statement
import ConAgua.Arena.Prelude
import ConAgua.Rom.PinRead

/-!
# The checker's entry `check()`, as the e2e lane runs it (lane `e2e`)

`check()` is `ConAgua.Final.Statement`'s entry: no parameters, the input is byte array 0, the
pin-data buffer byte array 1 (`pb_check` first: it starts with the program's `romData`; DESIGN.md
lane `romload`), and the first result is `ACCEPT` exactly when every stage of the twin's pipeline (`TwinAccepts`:
`internReservedPins`, `builtinPreludeE`, `parseChunks [b]`, `preparePrelude`, `internAllPins`,
`installThenCheck`) succeeded. Every twin error is an L `abort` inside the stage, so the stages
only report through their results where the twin has a non-error "no": `front_run` returns the
number of the first line that did not scan (`0` when all applied), and then `check` returns `1`.

`check_np()` is the partial pipeline the e2e runs while the prelude has no L code: no
`builtin_prelude`, no `prepare_prelude` (the reference is `e2e-ref --no-prelude`). It is a test
entry, not the checker.

Not here yet (`docs/e2e.md`, "Structural gaps"): the capacity checks at entry
(`len8`/`len64` against `ArenaR`'s minimums, ROADMAP §3; in L an array that is too small makes a
run abort on its first out-of-bounds access, so this is a proof obligation, not a soundness hole
of the test runs), and `AState.worker` between phase A and phase B (`SeqAccepts`).

`intern_reserved_pins` is bound here at its offset `0`; the readers are the pin-data buffer's
(`L.Rom.romProgPB`), which `scripts/e2e.py` prefers over the ROM instances `ConAgua/E2E/Dump.lean`
derives from the lanes' `…Prog rom p` structures. The functions without L code are not
named here: `scripts/e2e.py` finds every called function
the lanes' modules do not define and adds a stub for it (`docs/e2e.md`).
-/

namespace L.E2E

open L

/-- `check()`: the whole pipeline. -/
-- con-ron: ConRon/Arena/Main.lean:130-162 ConRon.Arena.runPipelineHead
-- con-ron: ConRon/Arena/Main.lean:164-190 ConRon.Arena.runPipelineTail
def checkL : FunDecl := lfn () locals (r, z) {
  z := call pb_check();
  z := call intern_reserved_pins();
  z := call builtin_prelude();
  r := call front_run();
  if r != 0 { return 1 };
  z := call prepare_prelude();
  z := call intern_all_pins();
  z := call install_then_check();
  return 71757147230292
}

/-- `check_np()`: the pipeline without the prelude (a test entry). -/
-- con-ron: none — the e2e lane's partial pipeline (no prelude), reference `e2e-ref --no-prelude`
def checkNpL : FunDecl := lfn () locals (r, z) {
  z := call pb_check();
  z := call intern_reserved_pins();
  r := call front_run();
  if r != 0 { return 1 };
  z := call intern_all_pins();
  z := call install_then_check();
  return 71757147230292
}

/-- `e2e_front()`: the stages before the fold (`e2e-diff`'s starting state, `ConAgua/E2E/Diff.lean`). -/
-- con-ron: none — the e2e lane's test entry (the first stages of `e2e-ref --no-prelude`)
def e2eFrontL : FunDecl := lfn () locals (r, z) {
  z := call pb_check();
  z := call intern_reserved_pins();
  r := call front_run();
  if r != 0 { return r };
  z := call intern_all_pins();
  return 0
}

/-! ## E2E patches

Each patch is a hook a lane has specified but not yet made (the lane's proofs are not ready for
it); the e2e program runs with it so that the code behind the hook is tested now. Each is listed
in `docs/e2e.md`. -/

/-- `apply_dline(j)` with the inductive line's hook, as `ConAgua/Front/IndApply.lean`'s header
specifies it (DESIGN.md, lane `indproofs`, "The frontend's inductive lines: not hooked yet"). -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:405-455 ConRon.Arena.Frontend.processLineCoreD
def applyDLineHooked : FunDecl := lfn (j) locals (pl, nm, lps, ty, vl, hk, hn, fl, z) {
  (pl, nm, lps, ty, vl, hk, hn, fl) := call rec_decl_line(j);
  if pl == 0 { abort };
  if pl == 25 { z := call apply_ind_line(j); return 0 };
  z := call apply_decl(pl, nm, lps, ty, vl, hk, hn, fl);
  return 0
}

example : (71757147230292 : Word) = ConAgua.Final.ACCEPT := rfl

/-- The e2e lane's own functions; `scripts/e2e.py` gives them priority over every other binding. -/
def e2eProg : Prog := [("check", checkL), ("check_np", checkNpL), ("e2e_front", e2eFrontL),
  -- the reserved pins at their ROM offset (lane `decls` binds it only parametrically, `IrpProg rom
  -- off p`; its readers read the pin-data buffer, `L.Rom.romProgPB`)
  ("intern_reserved_pins", L.Rom.internReservedPinsL),
  -- the pin stage over the buffer (three bodies are bound to this name on master; this is the one
  -- `L.Rom.romProgPB` names)
  ("intern_all_pins", L.Rom.internAllPinsPB),
  -- patches
  ("apply_dline", applyDLineHooked)]

/-- The names `e2eProg` binds as patches (reported as such). -/
def e2ePatches : List String := ["apply_dline"]

end L.E2E
