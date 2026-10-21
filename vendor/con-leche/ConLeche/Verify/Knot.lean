module

import ConLeche.Kernel.TypeChecker
public import ConLeche.Kernel.CoreIO
public import ConLeche.Verify.Modes

public section

/-!
# Knot equations

The definitional bridges between the fueled entry-point spellings
(`whnfCore mode env fuel d e`, …) and the core bodies applied to the knot
one level down.  Inversion and claims lemmas are stated against the
bodies with an abstract record; instantiating the record with
`pureFns mode env fuel` and rewriting with these equations recovers the
fueled statements the higher layers consume.
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## Loop step budgets

The reduction and lazy-delta loops (task #106) run on their own step
budgets, kept `irreducible` so that the `rfl` knot equations above do
not try to evaluate them.  Proofs that need to peel one iteration use
these positivity witnesses instead. -/

theorem whnfLoopFuel_succ : ∃ n, whnfLoopFuel = n + 1 :=
  ⟨4611686018427387903, by unfold whnfLoopFuel; rfl⟩

/-- `Expr.lamPair?`, read back: two λs. -/
theorem Expr.lamPair?_some {B₁ B₂ t₁ b₁ t₂ b₂ : Expr}
    (h : Expr.lamPair? B₁ B₂ = some (t₁, b₁, t₂, b₂)) :
    B₁ = .lam t₁ b₁ ∧ B₂ = .lam t₂ b₂ := by
  cases B₁ <;> cases B₂ <;> simp only [Expr.lamPair?, reduceCtorEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := by simpa using h
  exact ⟨rfl, rfl⟩

theorem whnfCore_succ (env : Env) (f d : Nat) (e : Expr) {c : Bool} :
    whnfCore mode env (f + 1) d e c = whnfCoreBody mode (pureFns mode env f) env c d e := rfl

theorem whnf_succ (env : Env) (f d : Nat) (e : Expr) :
    whnf mode env (f + 1) d e = whnfBody (pureFns mode env f) env d e := rfl

theorem inferTypeCore_succ (env : Env) (f d : Nat) (e : Expr) :
    inferTypeCore mode env (f + 1) d e = inferBody (pureFns mode env f) env d e := rfl

theorem isDefEqCore_succ (env : Env) (f d : Nat) (a b : Expr) :
    isDefEqCore mode env (f + 1) d a b = defeqBody mode (pureFns mode env f) env d a b := rfl

/-! ## The io lane (task #161 stage 2)

The io knot is a *leaf* lane: its reduction and definitional-equality
fields are the full knot's at the same fuel, so the equations below
fold them straight back to the full spellings and the io claims family
consumes the sealed four unchanged. -/

@[simp] theorem pureFnsIO_whnf (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsIO mode env f).whnf d e = whnf mode env f d e := by
  cases f <;> rfl

@[simp] theorem pureFnsIO_defeq (env : Env) (f d : Nat) (a b : Expr) :
    (pureFnsIO mode env f).defeq d a b = isDefEqCore mode env f d a b := by
  cases f <;> rfl

theorem ensureSortIO_def (env : Env) (f d : Nat) (e : Expr) :
    ensureSort (pureFnsIO mode env f) env d e = ensureSortCore mode env f d e := by
  cases f <;> rfl

theorem inferTypeCoreIO_succ (env : Env) (f d : Nat) (e : Expr) :
    inferTypeCoreIO mode env (f + 1) d e =
      inferBodyIO (pureFnsIO mode env f) env d e := rfl

theorem inferIO_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsIO mode env f).infer d e = inferTypeCoreIO mode env f d e := rfl

theorem inferTypeCoreIO_zero (env : Env) (d : Nat) (e : Expr) :
    inferTypeCoreIO mode env 0 d e =
      throw (.internal "fuel exhausted: infer") := rfl

/-! ## The io slot (task #172 B4)

The executable knot's `inferIO` slot **is** the leaf-lane
`inferTypeCoreIO` the io claims are stated at (`inferTypeIO_on`), at
every mode (task #346). -/

theorem inferTypeIO_succ (env : Env) (f d : Nat) (e : Expr) :
    inferTypeIO mode env (f + 1) d e =
      inferBodyIO (CoreFns.ioView (pureFns mode env f)) env d e := rfl

theorem inferTypeIO_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env f).inferIO d e = inferTypeIO mode env f d e := rfl

theorem inferTypeIO_zero (env : Env) (d : Nat) (e : Expr) :
    inferTypeIO mode env 0 d e =
      throw (.internal "fuel exhausted: infer") := rfl

/-- `inferBodyIO` reads exactly three fields of its record (`whnf`,
`infer`, `defeq`); two records agreeing there run it identically. -/
theorem inferBodyIO_congr {r₁ r₂ : CoreFns CheckM} {env : Env}
    (hw : r₁.whnf = r₂.whnf) (hi : r₁.infer = r₂.infer)
    (hd : r₁.defeq = r₂.defeq) (d : Nat) (e : Expr) :
    inferBodyIO r₁ env d e = inferBodyIO r₂ env d e := by
  cases r₁; cases r₂
  dsimp only at hw hi hd
  subst hw; subst hi; subst hd
  rfl

/-- **The io identification**: the executable
io slot runs the leaf-lane `inferTypeCoreIO` — the io claims' stated
subject — level for level.  (The two ties differ only in which record
carries the io recursion: `CoreFns.ioView` of the knot versus the leaf
knot; `inferBodyIO_congr` plus this induction identifies them.) -/
theorem inferTypeIO_on (env : Env) :
    ∀ (f d : Nat) (e : Expr),
      inferTypeIO mode env f d e = inferTypeCoreIO mode env f d e
  | 0, _, _ => rfl
  | f + 1, d, e => by
    rw [inferTypeIO_succ, inferTypeCoreIO_succ]
    exact inferBodyIO_congr
      (r₁ := (pureFns mode env f).ioView) (r₂ := pureFnsIO mode env f)
      (funext fun d' => funext fun e' => (pureFnsIO_whnf env f d' e').symm)
      (funext fun d' => funext fun e' => by
        show inferTypeIO mode env f d' e' = (pureFnsIO mode env f).infer d' e'
        rw [inferTypeIO_on env f d' e']
        exact (inferIO_def (mode := mode) env f d' e').symm)
      (funext fun d' => funext fun a => funext fun b =>
        (pureFnsIO_defeq env f d' a b).symm) d e

theorem whnfCore_def (env : Env) (f d : Nat) (e : Expr) {c : Bool} :
    (pureFns mode env f).whnfCore c d e = whnfCore mode env f d e c := rfl

theorem whnf_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env f).whnf d e = whnf mode env f d e := rfl

theorem infer_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env f).infer d e = inferTypeCore mode env f d e := rfl

theorem defeq_def (env : Env) (f d : Nat) (a b : Expr) :
    (pureFns mode env f).defeq d a b = isDefEqCore mode env f d a b := rfl

/-- **The eager slot is the eager tower's `defeq`** (task #353): the
knot ties `defeqE` to the bodies at `mode.toEager`, which is what the
knot at `mode.toEager` ties its `defeq` to. -/
theorem defeqE_def (env : Env) (f d : Nat) (a b : Expr) :
    (pureFns mode env f).defeqE d a b = isDefEqCore mode.toEager env f d a b := by
  cases f <;> rfl

/-- The mode an application argument's type is compared at (task #353):
the eager tower for an `eagerReduce _ _` argument (`defeqArg`). -/
@[expose] def CheckMode.argMode (mode : CheckMode) (a : Expr) : CheckMode :=
  if a.isEagerReduce then mode.toEager else mode

/-- The full-grade argument check, read as one comparison at the
argument's mode. -/
theorem defeqArg_def (env : Env) (f d : Nat) (a ta ty : Expr) :
    defeqArg (pureFns mode env f) d a ta ty =
      isDefEqCore (mode.argMode a) env f d ta ty := by
  unfold defeqArg CheckMode.argMode
  split
  · exact defeqE_def env f d ta ty
  · rfl

/-- The argument's mode runs the checks the mode runs. -/
@[simp] theorem CheckMode.argMode_verifiedChecks (a : Expr) :
    (mode.argMode a).verifiedChecks = mode.verifiedChecks := by
  unfold CheckMode.argMode; split <;> cases mode <;> rfl

/-- Fuel-zero spellings throw. -/
theorem whnfCore_zero (env : Env) (d : Nat) (e : Expr) {c : Bool} :
    whnfCore mode env 0 d e c = throw (.internal "fuel exhausted: whnfCore") := rfl

theorem whnf_zero (env : Env) (d : Nat) (e : Expr) :
    whnf mode env 0 d e = throw (.internal "fuel exhausted: whnf") := rfl

theorem inferTypeCore_zero (env : Env) (d : Nat) (e : Expr) :
    inferTypeCore mode env 0 d e = throw (.internal "fuel exhausted: infer") := rfl

theorem isDefEqCore_zero (env : Env) (d : Nat) (a b : Expr) :
    isDefEqCore mode env 0 d a b = throw (.internal "fuel exhausted: defeq") := rfl

theorem ensureSort_def (env : Env) (f d : Nat) (e : Expr) :
    ensureSort (pureFns mode env f) env d e = ensureSortCore mode env f d e := rfl

/-! Fueled spellings for the record-parameterized helpers: the body one
level up calls them with `pureFns mode env fuel`, so their facts appear in
inversions at the same fuel as the entry-point facts. -/

abbrev iotaRecFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM (Option Expr) := iotaRec mode (pureFns mode env fuel) env

abbrev iotaCertsFullFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    List Expr → CheckM Bool := iotaCertsFull (pureFns mode env fuel) env

abbrev iotaIndexOkFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Nat → Nat → Nat →
    Expr → List Expr → List Expr → CheckM Bool := iotaIndexOk (pureFns mode env fuel) env

abbrev defEqListFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → List Expr →
    List Expr → CheckM Bool := defEqList (pureFns mode env fuel) env

abbrev proofIrrelFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := proofIrrel (pureFns mode env fuel)

abbrev propIrrelFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := propIrrel (pureFns mode env fuel) env

abbrev stuckIrrelFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := stuckIrrel (pureFns mode env fuel) env

abbrev structEtaCertFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := structEtaCert (pureFns mode env fuel) env

abbrev structEtaCertWithFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    Expr → CheckM Bool := structEtaCertWith (pureFns mode env fuel) env

abbrev structUnitCertFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := structUnitCert (pureFns mode env fuel) env

abbrev etaCertFueled (mode : CheckMode) (env : Env) (fuel : Nat) (d : Nat)
    (ty body : Expr) (b : Expr) : CheckM Bool :=
  etaCert mode (pureFns mode env fuel) env d ty body b

abbrev majorToCtorFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Name →
    List RecRule → Expr → CheckM Expr := majorToCtor mode (pureFns mode env fuel) env

abbrev litMajorToCtorFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM Expr := litMajorToCtor (pureFns mode env fuel) env

abbrev prepareMajorFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Name →
    List RecRule → Expr → CheckM Expr := prepareMajor mode (pureFns mode env fuel) env

abbrev projLitToCtorFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM Expr := projLitToCtor (pureFns mode env fuel) env

abbrev reduceNatFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM (Option Expr) := reduceNat (pureFns mode env fuel) env

abbrev boolTrueShortcutFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM Bool := boolTrueShortcut (pureFns mode env fuel)

abbrev defeqSpineFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := defeqSpine (pureFns mode env fuel) env

abbrev reduceProjCoreFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Name →
    Nat → Expr → CheckM (Option Expr) := reduceProjCore mode (pureFns mode env fuel) env

abbrev quickDefEqFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM (Option Bool) := quickDefEq mode (pureFns mode env fuel)

abbrev defeqLamsFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Nat → Expr →
    Expr → Expr → Expr → CheckM Bool := defeqLams mode (pureFns mode env fuel)

abbrev defeqLamsInnerFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    Expr → CheckM Bool := defeqLamsInner mode (pureFns mode env fuel)

abbrev defeqOffsetFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM (Option Bool) := defeqOffset (pureFns mode env fuel)

abbrev tryUnfoldProjAppFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM (Option Expr) := tryUnfoldProjApp (pureFns mode env fuel)

abbrev deltaQuickFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM DeltaStep := deltaQuick mode (pureFns mode env fuel)

abbrev lazyDeltaStepFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM DeltaStep := lazyDeltaStep mode (pureFns mode env fuel) env

abbrev lazyDeltaReductionFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Nat →
    Expr → Expr → CheckM LazyRes := lazyDeltaReduction mode (pureFns mode env fuel) env

abbrev lazyDeltaProjReductionFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat →
    Name → Nat → Nat → Expr → Expr → CheckM Bool :=
  lazyDeltaProjReduction mode (pureFns mode env fuel) env

abbrev defeqProjPairFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := defeqProjPair mode (pureFns mode env fuel) env

abbrev defeqStuckFueled (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := defeqStuck mode (pureFns mode env fuel) env

/-! Folding rewrites: record-applied helper spellings into their fueled
`P` names (used right after unfolding a body in an inversion proof). -/

theorem iotaRec_fold (env : Env) (fuel : Nat) :
    iotaRec mode (pureFns mode env fuel) env = iotaRecFueled mode env fuel := rfl
theorem iotaCertsFull_fold (env : Env) (fuel : Nat) :
    iotaCertsFull (pureFns mode env fuel) env = iotaCertsFullFueled mode env fuel := rfl
theorem iotaIndexOk_fold (env : Env) (fuel : Nat) :
    iotaIndexOk (pureFns mode env fuel) env = iotaIndexOkFueled mode env fuel := rfl
theorem defEqList_fold (env : Env) (fuel : Nat) :
    defEqList (pureFns mode env fuel) env = defEqListFueled mode env fuel := rfl
theorem proofIrrel_fold (env : Env) (fuel : Nat) :
    proofIrrel (pureFns mode env fuel) = proofIrrelFueled mode env fuel := rfl
theorem propIrrel_fold (env : Env) (fuel : Nat) :
    propIrrel (pureFns mode env fuel) env = propIrrelFueled mode env fuel := rfl
theorem stuckIrrel_fold (env : Env) (fuel : Nat) :
    stuckIrrel (pureFns mode env fuel) env = stuckIrrelFueled mode env fuel := rfl
theorem structEtaCert_fold (env : Env) (fuel : Nat) :
    structEtaCert (pureFns mode env fuel) env = structEtaCertFueled mode env fuel := rfl
theorem structEtaCertWith_fold (env : Env) (fuel : Nat) :
    structEtaCertWith (pureFns mode env fuel) env =
      structEtaCertWithFueled mode env fuel := rfl
theorem structUnitCert_fold (env : Env) (fuel : Nat) :
    structUnitCert (pureFns mode env fuel) env = structUnitCertFueled mode env fuel := rfl
theorem etaCert_fold (env : Env) (fuel : Nat) :
    etaCert mode (pureFns mode env fuel) env = etaCertFueled mode env fuel := rfl
theorem majorToCtor_fold (env : Env) (fuel : Nat) :
    majorToCtor mode (pureFns mode env fuel) env = majorToCtorFueled mode env fuel := rfl
theorem litMajorToCtor_fold (env : Env) (fuel : Nat) :
    litMajorToCtor (pureFns mode env fuel) env = litMajorToCtorFueled mode env fuel := rfl
theorem prepareMajor_fold (env : Env) (fuel : Nat) :
    prepareMajor mode (pureFns mode env fuel) env = prepareMajorFueled mode env fuel := rfl
theorem projLitToCtor_fold (env : Env) (fuel : Nat) :
    projLitToCtor (pureFns mode env fuel) env = projLitToCtorFueled mode env fuel := rfl
theorem reduceNat_fold (env : Env) (fuel : Nat) :
    reduceNat (pureFns mode env fuel) env = reduceNatFueled mode env fuel := rfl
theorem boolTrueShortcut_fold (env : Env) (fuel : Nat) :
    boolTrueShortcut (pureFns mode env fuel) = boolTrueShortcutFueled mode env fuel := rfl
theorem defeqSpine_fold (env : Env) (fuel : Nat) :
    defeqSpine (pureFns mode env fuel) env = defeqSpineFueled mode env fuel := rfl
theorem reduceProjCore_fold (env : Env) (fuel : Nat) :
    reduceProjCore mode (pureFns mode env fuel) env = reduceProjCoreFueled mode env fuel := rfl
theorem quickDefEq_fold (env : Env) (fuel : Nat) :
    quickDefEq mode (pureFns mode env fuel) = quickDefEqFueled mode env fuel := rfl
theorem defeqOffset_fold (env : Env) (fuel : Nat) :
    defeqOffset (pureFns mode env fuel) = defeqOffsetFueled mode env fuel := rfl
theorem tryUnfoldProjApp_fold (env : Env) (fuel : Nat) :
    tryUnfoldProjApp (pureFns mode env fuel) = tryUnfoldProjAppFueled mode env fuel := rfl
theorem deltaQuick_fold (env : Env) (fuel : Nat) :
    deltaQuick mode (pureFns mode env fuel) = deltaQuickFueled mode env fuel := rfl
theorem lazyDeltaStep_fold (env : Env) (fuel : Nat) :
    lazyDeltaStep mode (pureFns mode env fuel) env = lazyDeltaStepFueled mode env fuel := rfl
theorem lazyDeltaReduction_fold (env : Env) (fuel : Nat) :
    lazyDeltaReduction mode (pureFns mode env fuel) env =
      lazyDeltaReductionFueled mode env fuel := rfl
theorem lazyDeltaProjReduction_fold (env : Env) (fuel : Nat) :
    lazyDeltaProjReduction mode (pureFns mode env fuel) env =
      lazyDeltaProjReductionFueled mode env fuel := rfl
theorem defeqProjPair_fold (env : Env) (fuel : Nat) :
    defeqProjPair mode (pureFns mode env fuel) env = defeqProjPairFueled mode env fuel := rfl
theorem defeqStuck_fold (env : Env) (fuel : Nat) :
    defeqStuck mode (pureFns mode env fuel) env = defeqStuckFueled mode env fuel := rfl

end ConLeche
