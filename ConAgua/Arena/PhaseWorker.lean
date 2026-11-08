module


@[expose] public section

/-!
# Phase B on the worker (lane `tails`)

ronsync2: phase B is gone upstream (#143); this module is kept empty so imports resolve.

The twin's pipeline (`ConAgua/Final/Twin.lean`'s `SeqAccepts`, con-ron's `check_decls_phased`)
runs phase B, `checkPendingList`, on **the phase-A state's worker** `s.worker` (scratch dropped,
fresh memos and caches); L's phase B (`check_pending_go`, `Checker.lean`) runs straight on the
memory phase A left, as the twin's `installThenCheck` does on `s`. The two agree: when the caches are empty (phase A's every step ends with `dropScratch`,
which flushes them), every `checkPending` opens with `enterScratch`, which overwrites what
`AState.worker` changes (con-ron's `checkPending_worker`). So `AState.worker` needs no L code: the
identity refines it in front of phase B, and `checkPendingGo_worker` says so for the L phase B.
-/

