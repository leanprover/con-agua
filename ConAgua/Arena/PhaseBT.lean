module

import ConAgua.Arena.LoopT
import ConAgua.Arena.PhaseWorker
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.Verdict.DeclValE
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.RefWalk
import ConAgua.Arena.ScratchRefine
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.ModelGen
import ConRon.Bridge.Checker.Fold
import ConRon.Bridge.Inductives.Decl
import ConRon.Bridge.Specs
public import ConAgua.Arena.Checker
public import ConAgua.Arena.DeclTwin
public import ConAgua.Arena.LeafFns
import all ConAgua.Arena.CheckerL

@[expose] public section

/-!
# Phase B under `StageT` (lane `loopt3`, items 12 and 12a)

Phase B runs `check_value_group` from `StageT` with the program's own core (`cvg_ref`,
`realCall p`; its `StageR` version through the stubs is gone). Per pending check:

* **The twin side** (`TwinPend`): con-ron's phase-B invariant (`Arena.checkPendingList_bridge`'s
  induction hypotheses): `FoldOK` at the final environment `env` (names unique), the remaining
  records related to their pure value groups (`PendRel`), the caches empty and the scratch tier
  off (each check ends with `dropScratch`). `TwinPend.step` is that induction's step
  (`Arena.checkPending_prefix`); `TwinPend.start` gets it from phase A's twin run
  (`Arena.installFold_bridge` from `TwinFold` at the loop's start).
* **`TwinOK` at the record's view**: con-ron's `CheckOK` at the prefix environment and the
  restricted index (`IFEnvOK_prefix`, the caches empty) and the memory's half (`LoopMem`,
  `CoreMemos`), `TwinOK.of_check`; the bracket's opening keeps it (`enter_loopB`, as
  `CheckerT.lean`'s `enter_loopW`); `check_value_group` from `StageT` (`checkValueGroup_specT`);
  `scratch_drop` is a leaf (`CoreMemos` by its frame, `drop_loopB`); `LoopMem` back by the
  loop's write set (`LoopClosed`) and the twin's `PExt`.
* **Item 12a** (`installFold_drop`): an accepting `installFold` from a state with empty caches
  (scratch tier off) ends with empty caches (scratch tier off): every step ends in `dropScratch`.
-/

-- ronsync2: phase B is gone upstream (#143, every record is a job); the module is kept empty so
-- that its importers resolve.
