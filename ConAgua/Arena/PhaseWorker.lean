import ConRon.Arena.Phased

/-!
# Phase B on the worker (lane `tails`)

The twin's pipeline (`ConAgua/Final/Twin.lean`'s `SeqAccepts`, con-ron's `check_decls_phased`)
runs phase B, `checkPendingList`, on **the phase-A state's worker** `s.worker` (scratch dropped,
fresh memos and caches); L's phase B (`check_pending_go`, `Checker.lean`) runs straight on the
memory phase A left, as the twin's `installThenCheck` does on `s`. The two agree: when the caches are empty (phase A's every step ends with `dropScratch`,
which flushes them), every `checkPending` opens with `enterScratch`, which overwrites what
`AState.worker` changes (con-ron's `checkPending_worker`). So `AState.worker` needs no L code: the
identity refines it in front of phase B, and `checkPendingGo_worker` says so for the L phase B.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **Phase B on the worker is phase B on the state**, when the caches are empty (needed only if
some check runs): the same verdict (the states after differ only on an empty list, where nothing
runs). -/
theorem checkPendingList_worker_ok {mode : ConLeche.CheckMode} {fe : IFEnv}
    {pend : List PendingCheck} {s s' : AState} (hc : pend ≠ [] → s.caches = Caches.empty)
    (h : checkPendingList mode fe pend s = .ok (.ok (), s')) :
    ∃ s'', checkPendingList mode fe pend s.worker = .ok (.ok (), s'') := by
  cases pend with
  | nil => exact ⟨s.worker, rfl⟩
  | cons pc rest =>
    have hpc := checkPending_worker (mode := mode) (fe := fe) (pc := pc) (hc (by simp))
    refine ⟨s', ?_⟩
    simp only [checkPendingList] at h ⊢
    rw [hpc]; exact h

end L.Arena
