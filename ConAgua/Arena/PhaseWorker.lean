import ConAgua.Arena.Checker
import ConRon.Arena.Phased
import ConAgua.Census.Attr

/-!
# Phase B on the worker (lane `tails`)

The twin's pipeline (`ConAgua/Final/Twin.lean`'s `SeqAccepts`, con-ron's `check_decls_phased`)
runs phase B, `checkPendingList`, on **the phase-A state's worker** `s.worker` (scratch dropped,
fresh memos and caches); L's declaration loop (`install_then_check`, `Checker.lean`) runs
`check_pending_go` straight on the memory phase A left, as the twin's `installThenCheck` does on
`s`. The two agree: when the caches are empty (phase A's every step ends with `dropScratch`,
which flushes them), every `checkPending` opens with `enterScratch`, which overwrites what
`AState.worker` changes (con-ron's `checkPending_worker`). So `AState.worker` needs no L code: the
identity refines it in front of phase B, and `checkPendingGo_worker` says so for the L phase B.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **Phase B on the worker is phase B on the state**, when the caches are empty: the same
verdict (the states after differ only on an empty list, where nothing runs). -/
theorem checkPendingList_worker_ok {mode : ConLeche.CheckMode} {fe : IFEnv}
    {pend : List PendingCheck} {s s' : AState} (hc : s.caches = Caches.empty)
    (h : checkPendingList mode fe pend s = .ok (.ok (), s')) :
    ∃ s'', checkPendingList mode fe pend s.worker = .ok (.ok (), s'') := by
  cases pend with
  | nil => exact ⟨s.worker, rfl⟩
  | cons pc rest =>
    have hpc := checkPending_worker (mode := mode) (fe := fe) (pc := pc) hc
    refine ⟨s', ?_⟩
    simp only [checkPendingList] at h ⊢
    rw [hpc]; exact h

section
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog) (fe : IFEnv) (pend : Array PendingCheck)
  (hpc : p.lookup "check_pending" = some checkPendingL)
  (hpg : p.lookup "check_pending_go" = some checkPendingGoL)
  (hpx : p.lookup "check_pending_next" = some checkPendingNextL) (hb : BracketProg p)
  (hm : mode = .verified) (hcv : CvgProg p)

/-- **L's phase B refines phase B on the worker** (`AState.worker` by the identity): a returning
`check_pending_go(0, cnt, vis)` from a memory related to the phase-A state `a₀` (with empty
caches) means the twin's phase B on `a₀.worker` accepts. -/
@[refines ConRon.Arena.AState.worker]
theorem checkPendingGo_worker (n : Nat) (s₀ : St) (a₀ : AState) (cnt vis : Word)
    (hcnt : cnt.toNat = pend.size) (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds)
    (hc : a₀.caches = Caches.empty) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_pending_go" [0, cnt, vis]
    ⦃fun _ s' => LocEq s' s₀ ∧
      ∃ s'', checkPendingList mode fe pend.toList a₀.worker = .ok (.ok (), s''); ⊤⦄ := by
  refine triple_post ((checkPendingGo_refines mode pins dn ds p fe pend hpc hpg hpx hb hm hcv n).1
    s₀ a₀ 0 cnt vis (by simp) hcnt hR) ?_
  rintro r s' ⟨hl, hok, hres, -⟩
  refine ⟨hl, ?_⟩
  have hrun := AM.run_of_ok _ _ hok
  simp only [UInt64.toNat_zero, List.drop_zero] at hrun hres
  rw [hres] at hrun
  exact checkPendingList_worker_ok hc hrun

end

end L.Arena
