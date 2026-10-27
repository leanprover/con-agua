import ConAgua.Arena.PhaseBT
import ConAgua.Arena.Verdict

/-!
# Phase B's loop fails only where the twin does (lane verdicts-b, calibration)

`check_pending_go` / `check_pending_next` (`Arena/Checker.lean`) is phase B's loop, a pair of
mutually recursive functions; its twin `checkPendingList` turns a record's failure into the value
`.ok (.error (ce, pc.pos))`. The error claim (`checkPendingGo_refinesE`): from the hypotheses of the
ok refinement (`checkPendingGo_refinesT`, `PhaseBT.lean`), a failing run of class `≠ 0` means
`TwinFailsV (checkPendingList mode fe (pend.toList.drop j)) a₀ e.cls`. By induction on the fuel,
both functions at once (as the ok proof): `check_pending`'s failure is the twin's value failure
at the record (its error claim, a hypothesis `CPErrT`), its ok run the twin's step
(`checkPending_loopT`) before the rest's failure (the induction hypothesis).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open ConRon.Bridge (FoldOK PExt PendRel ListRel)

/-! ## The error models -/

l_model checkPendingGo_specE (p : Prog) (hf : p.lookup "check_pending_go" = some checkPendingGoL)
  fns [hf ↦ checkPendingGoE] grind [arena_grind] errors

l_model checkPendingNext_specE (p : Prog)
  (hf : p.lookup "check_pending_next" = some checkPendingNextL)
  fns [hf ↦ checkPendingNextE] grind [arena_grind] errors

/-! ## The twin side -/

/-- A record's failure is the list's failure, as a value. -/
theorem checkPendingList_fails_head {mode : ConLeche.CheckMode} {fe : IFEnv} {pc : PendingCheck}
    {rest : List PendingCheck} {a : AState} {c : Word}
    (h : ∃ ce, (checkPending mode fe pc).run a = .error ce ∧ twinCls ce = c) :
    TwinFailsV (checkPendingList mode fe (pc :: rest)) a c := by
  obtain ⟨ce, hce, hc⟩ := h
  refine .inr ⟨ce, pc.pos, AState.abandoned, ?_, hc⟩
  show (match (checkPending mode fe pc).run a with
    | .ok ((), s') => checkPendingList mode fe rest s'
    | .error e => .ok (.error (e, pc.pos), AState.abandoned)) = _
  rw [hce]

/-- A record that checks ok: the list fails as the rest does. -/
theorem checkPendingList_fails_tail {mode : ConLeche.CheckMode} {fe : IFEnv} {pc : PendingCheck}
    {rest : List PendingCheck} {a : AState} {c : Word} (hok : AM.ok (checkPending mode fe pc) a)
    (h : TwinFailsV (checkPendingList mode fe rest) (AM.st (checkPending mode fe pc) a) c) :
    TwinFailsV (checkPendingList mode fe (pc :: rest)) a c := by
  have hrun := AM.run_of_ok _ _ hok
  have e : (checkPendingList mode fe (pc :: rest)).run a =
      (checkPendingList mode fe rest).run (AM.st (checkPending mode fe pc) a) := by
    show (match (checkPending mode fe pc).run a with
      | .ok ((), s') => checkPendingList mode fe rest s'
      | .error e => .ok (.error (e, pc.pos), AState.abandoned)) = _
    rw [hrun]; rfl
  unfold TwinFailsV at h ⊢
  rw [e]; exact h


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

/-- **`check_pending`'s error claim** (a hypothesis here, proved bottom-up): under
`checkPending_loopT`'s hypotheses, a failing run claims `checkPending`'s failure. -/
def CPErrT : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState) (j vis : Word), j.toNat < pend.size →
    TwinPend fe (pend.toList.drop j.toNat) a₀ →
    LoopR pins dn s₀.mem a₀ vis fe pend ds → LoopMem dn s₀.mem a₀ → CoreMemos s₀.mem →
    j.toNat < 2 ^ 62 → L.Stubs.CrOK s₀.mem →
    CoreSpecE p n "check_pending" [j, vis] (checkPending mode fe (pdAt pend j)) s₀ a₀

/-- `check_pending_go`'s error claim at fuel `n` (the hypotheses of `CPGoSpecT`). -/
def CPGoSpecE (n : Nat) : Prop :=
  ∀ (m : Mem) (a₀ : AState) (j cnt vis : Word), j.toNat ≤ pend.size → cnt.toNat = pend.size →
    TwinPend fe (pend.toList.drop j.toNat) a₀ →
    LoopR pins dn m a₀ vis fe pend ds → LoopMem dn m a₀ → CoreMemos m → L.Stubs.CrOK m →
    ∀ e, callE p n "check_pending_go" [j, cnt, vis] m = .error e →
      ErrClaimV (checkPendingList mode fe (pend.toList.drop j.toNat)) a₀ e

/-- `check_pending_next`'s error claim at fuel `n` (the hypotheses of `CPNextSpecT`). -/
def CPNextSpecE (n : Nat) : Prop :=
  ∀ (m : Mem) (a₀ : AState) (j cnt vis : Word), j.toNat < pend.size → cnt.toNat = pend.size →
    TwinPend fe (pend.toList.drop j.toNat) a₀ →
    LoopR pins dn m a₀ vis fe pend ds → LoopMem dn m a₀ → CoreMemos m → L.Stubs.CrOK m →
    ∀ e, callE p n "check_pending_next" [j, cnt, vis] m = .error e →
      ErrClaimV (checkPendingList mode fe (pend.toList.drop j.toNat)) a₀ e

section cp
variable (hP : PhaseBProg p) (hm : mode = .verified)
include hP

theorem cpGoE_step (n : Nat) (ih : CPNextSpecE mode pins dn ds p fe pend n) :
    CPGoSpecE mode pins dn ds p fe pend (n + 1) := by
  intro m a₀ j cnt vis hj hc hT hR hM hcm hCr e he hk0
  have hW := triple_of_callE_err (checkPendingGo_specE p hP.cpg (n + 1) ⟨m, Locals.init []⟩ j cnt vis)
    he (Err.code_ne_of_cls hk0)
  simp only [checkPendingGoE] at hW
  by_cases g1 : j = cnt
  · rw [ite_eq_left g1] at hW; cases hW
  rw [ite_eq_right g1] at hW
  have hlt : j.toNat < pend.size := by
    have : j.toNat ≠ cnt.toNat := fun e => g1 (UInt64.toNat_inj.mp e)
    omega
  cases h1 : callE p n "check_pending_next" [j, cnt, vis] m with
  | error e1 =>
    rw [h1, checkPendingGoE.k_check_pending_next.none] at hW
    cases hW
    exact ih m a₀ j cnt vis hlt hc hT hR hM hcm hCr _ h1 hk0
  | ok q =>
    obtain ⟨r, m₁⟩ := q
    rw [h1, checkPendingGoE.k_check_pending_next.arm1] at hW
    cases hW

include hm in
theorem cpNextE_step (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (hE : CPErrT mode pins dn ds p fe pend)
    (ih : CPGoSpecE mode pins dn ds p fe pend n) :
    CPNextSpecE mode pins dn ds p fe pend (n + 1) := by
  intro m a₀ j cnt vis hj hc hT hR hM hcm hCr e he hk0
  have hn' : n ≤ 2 ^ 62 := by omega
  have hW := triple_of_callE_err
    (checkPendingNext_specE p hP.cpx (n + 1) ⟨m, Locals.init []⟩ j cnt vis) he (Err.code_ne_of_cls hk0)
  simp only [checkPendingNextE] at hW
  by_cases g1 : 4611686018427387904 ≤ j
  · rw [ite_eq_left g1] at hW; cases hW; exact absurd rfl hk0
  rw [ite_eq_right g1] at hW
  have h62 : j.toNat < 2 ^ 62 := by
    have : ¬ (4611686018427387904 : Word).toNat ≤ j.toNat := fun h => g1 (UInt64.le_iff_toNat_le.mpr h)
    simp at this; omega
  have h1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [drop_cons_pdAt pend j hj h1]
  cases hc1 : callE p n "check_pending" [j, vis] m with
  | error e1 =>
    rw [hc1, checkPendingNextE.k_check_pending.none] at hW
    cases hW
    exact checkPendingList_fails_head
      (CoreSpecE.of_callE (hE n hn' ⟨m, Locals.init []⟩ a₀ j vis hj hT hR hM hcm h62 hCr) hc1 hk0)
  | ok q =>
    obtain ⟨r, m₁⟩ := q
    rw [hc1] at hW
    obtain ⟨s', hs', -, hok, hR', hcm', hM', hT', hCr'⟩ := triple_of_callE
      (checkPending_loopT mode pins dn ds p hm hP n hn' ⟨m, Locals.init []⟩ a₀ j vis fe pend hj hT hR
        hM hcm h62 hCr) hc1
    subst hs'
    simp only [checkPendingNextE.k_check_pending] at hW
    cases hc2 : callE p n "check_pending_go" [j + 1, cnt, vis] s'.mem with
    | error e2 =>
      rw [hc2, checkPendingNextE.k_check_pending_go.none] at hW
      cases hW
      refine checkPendingList_fails_tail hok ?_
      exact ih s'.mem _ (j + 1) cnt vis (by omega) hc hT' hR' hM' hcm' hCr' _ hc2 hk0
    | ok q2 =>
      obtain ⟨r2, m₂⟩ := q2
      rw [hc2, checkPendingNextE.k_check_pending_go.arm1] at hW
      cases hW

include hm in
/-- **`check_pending_go` fails only where `checkPendingList` does** (and `check_pending_next`):
from phase B's relation at check `j` (the hypotheses of `checkPendingGo_refinesT`), a failing run
of class `≠ 0` means the twin's phase B over the checks from `j` fails with that class (a record's
failure, as a value). -/
theorem checkPendingGo_refinesE (hE : CPErrT mode pins dn ds p fe pend) (n : Nat)
    (hn : n ≤ 2 ^ 62) :
    CPGoSpecE mode pins dn ds p fe pend n ∧ CPNextSpecE mode pins dn ds p fe pend n := by
  induction n with
  | zero =>
    constructor
    · intro m a₀ j cnt vis _ _ _ _ _ _ _ e he
      obtain ⟨e', he', h0⟩ := callE_zero p "check_pending_go" [j, cnt, vis] m
      rw [he] at he'; cases he'
      exact ErrClaimV.of_cls0 h0
    · intro m a₀ j cnt vis _ _ _ _ _ _ _ e he
      obtain ⟨e', he', h0⟩ := callE_zero p "check_pending_next" [j, cnt, vis] m
      rw [he] at he'; cases he'
      exact ErrClaimV.of_cls0 h0
  | succ n ih =>
    have ih := ih (by omega)
    exact ⟨cpGoE_step mode pins dn ds p fe pend hP n ih.2,
      cpNextE_step mode pins dn ds p fe pend hP hm n hn hE ih.1⟩

end cp
end phaseB

end L.Arena
