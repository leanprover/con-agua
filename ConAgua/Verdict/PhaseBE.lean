module

public import ConAgua.Arena.PhaseBT
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr

@[expose] public section

/-!
# Phase B's loop fails only where the twin does (lane verdicts-b, calibration)

`check_pending_go` / `check_pending_next` (`Arena/Checker.lean`) is phase B's loop, a pair of
mutually recursive functions; its twin `checkPendingList` turns a record's failure into the value
`.ok (.error (ce, pc.pos))`. Both functions have one model and one refinement for both outcomes
(`cp_ref`, `Arena/PhaseBT.lean`); here its error half from a failing run
(`checkPendingGo_refinesE`) and the worker's failure (`checkPendingList_worker_fails`).
-/

-- ronsync2: phase B is gone upstream (#143, every record is a job); the module is kept empty so
-- that its importers resolve.
