module

public import ConAgua.Checker.PhaseBReads
public import ConAgua.Arena.LevelIntern
public import ConAgua.Arena.LevelSubstLP
meta import ConAgua.Checker.PhaseBReads
meta import ConAgua.Arena.LevelIntern
meta import ConAgua.Arena.LevelSubstLP

@[expose] public section

/-!
# Phase B's read set is the thread's arrays (lane parmode)

docs/design/parmode.md, "Step 4". A thread's worker memory (`bufMem`, `Arena/FreezeRel.lean`) has
content only in the frozen arrays (the buffer's images) and the worker's own arrays
(`parOwnedL`); every other word array is empty. `checkerProg_thrReads`: phase B's loop
(`phaseBFns`, the closure of `check_pending_go`) names only those, without the header `HDRF` and
the seed `CTLF` (`thrS`), so by `L/Agree.lean` a run on the worker memory is the run on any memory
that agrees with it on `thrS` (the same per-function kernel check as `checkerProg_phaseBReads`,
with the smaller set; `Checker/ParOwned.lean`'s `parMissing` is its unproved precursor).
-/

namespace L.Checker

open L.Arena L.Compiler

/-- **The arrays a thread's run of phase B names**: the frozen arrays but the header `HDRF` and the
seed `CTLF`, and the owned arrays. -/
def thrS (a : TieredArray) : Bool :=
  a != HDRF && a != CTLF && (frozenIdsL.contains a || parOwnedL.contains a)

/-- **What `thrS` holds**: a frozen id (not the header or the seed) or an owned one. -/
theorem thrS_iff (a : TieredArray) : thrS a = true ↔
    a ≠ HDRF ∧ a ≠ CTLF ∧ (a ∈ frozenIdsL ∨ a ∈ parOwnedL) := by
  simp [thrS, and_assoc]

/-- Every function of the checker passes the thread's per-function read check. -/
prog_all checkerProg_thrReadsChk : checkerProg (rdChk thrS (fun _ => false) phaseBTree)

/-- **Phase B's read set, for a thread**: the call closure of `check_pending_go` names only word
arrays of `thrS`, no byte array, and calls only into itself. -/
theorem checkerProg_thrReads : readsIn checkerProg thrS (fun _ => false) phaseBFns = true :=
  readsIn_of_all phaseBTree.eq checkerProg_thrReadsChk

end L.Checker
