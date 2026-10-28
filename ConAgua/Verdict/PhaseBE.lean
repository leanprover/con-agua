import ConAgua.Arena.PhaseBT
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# Phase B's loop fails only where the twin does (lane verdicts-b, calibration)

`check_pending_go` / `check_pending_next` (`Arena/Checker.lean`) is phase B's loop, a pair of
mutually recursive functions; its twin `checkPendingList` turns a record's failure into the value
`.ok (.error (ce, pc.pos))`. Both functions have one model and one refinement for both outcomes
(`cp_ref`, `Arena/PhaseBT.lean`); here its error half from a failing run
(`checkPendingGo_refinesE`) and the worker's failure (`checkPendingList_worker_fails`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open ConRon.Bridge (FoldOK PExt PendRel ListRel)

/-! ## The twin side -/

/-- **Phase B's failure on the worker is its failure on the state**, when the caches are empty
(the error half of `checkPendingList_worker_ok`; `checkPending_worker`). -/
theorem checkPendingList_worker_fails {mode : ConLeche.CheckMode} {fe : IFEnv}
    {pend : List PendingCheck} {s : AState} {c : Word} (hc : pend ≠ [] → s.caches = Caches.empty)
    (h : TwinFailsV (checkPendingList mode fe pend) s c) :
    TwinFailsV (checkPendingList mode fe pend) s.worker c := by
  cases pend with
  | nil =>
    rcases h with ⟨ce, hce, -⟩ | ⟨ce, i, a', hce, -⟩ <;> cases hce
  | cons pc rest =>
    have hpc := checkPending_worker (mode := mode) (fe := fe) (pc := pc) (hc (by simp))
    have e : (checkPendingList mode fe (pc :: rest)).run s.worker =
        (checkPendingList mode fe (pc :: rest)).run s := by
      show checkPendingList mode fe (pc :: rest) s.worker = checkPendingList mode fe (pc :: rest) s
      simp only [checkPendingList]; rw [hpc]
    unfold TwinFailsV at h ⊢
    rw [e]; exact h

section phaseB
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog) (fe : IFEnv) (pend : Array PendingCheck)

/-- `check_pending_go`'s error claim at fuel `n` (the hypotheses of `CPGoSpecT`). -/
def CPGoSpecE (n : Nat) : Prop :=
  ∀ (m : Mem) (a₀ : AState) (j cnt vis : Word), j.toNat ≤ pend.size → cnt.toNat = pend.size →
    TwinPend fe (pend.toList.drop j.toNat) a₀ →
    LoopR pins dn m a₀ vis fe pend ds → LoopMem dn m a₀ → CoreMemos m → L.Stubs.CrOK m →
    ∀ e, callE p n "check_pending_go" [j, cnt, vis] m = .error e →
      ErrClaimV (checkPendingList mode fe (pend.toList.drop j.toNat)) a₀ e

section cp
variable (hP : PhaseBProg p) (hm : mode = .verified)
include hP hm

/-- **`check_pending_go` fails only where `checkPendingList` does**: from phase B's relation at
check `j` (the hypotheses of `checkPendingGo_refinesT`), a failing run of class `≠ 0` means the
twin's phase B over the checks from `j` fails with that class (a record's failure, as a value);
`cp_ref`'s error half. -/
theorem checkPendingGo_refinesE (hE : CpG p) (n : Nat)
    (hn : n ≤ 2 ^ 62) : CPGoSpecE mode pins dn ds p fe pend n :=
  fun m a₀ j cnt vis hj hc hT hR hM hcm hCr _ he =>
    RefC.run_err (checkPendingGo_specE p hP.cpg n ⟨m, Locals.init []⟩ j cnt vis)
      (fun _ h0 => ErrClaimV.of_cls0 h0) trivial hE
      ((cp_ref mode pins dn ds p fe pend hP hm n hn).1 m a₀ j cnt vis hj hc hT hR hM hcm hCr) he

end cp
end phaseB

end L.Arena
