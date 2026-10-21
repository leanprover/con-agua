module

public import ConLeche.Cached.ParsedC

public section

/-!
# The knot reads the index only through `find?`

`FEnv` carries three fields, but the cached core only ever asks it
questions through `FEnv.find?`: every guard, every stored-constant
read and every rule lookup below goes through that one function.  This
file proves it, one congruence lemma per `fe`-taking function of
`ConLeche/Kernel/FEnv.lean` and `ConLeche/Cached/*` reachable from the
knot's bodies, bottom-up, landing on `coreKnotI_congr`.

The consumers are the re-check at a task-#108 prefix view —
`feFinal.restrictTo k` and `mkFEnv env` for the environment `env` of
the first `k` constants have the same `find?`, so `coreKnotI_congr`
says they run the *same* core, and the simulation stated at
`mkFEnv env` therefore covers a run at the prefix view — and the
parallel install (task #329, `ConLeche/Verify/Cached/ParInstall.lean`): a
worker installs a record at a view whose `find?` is the serial
index's, so its result is the serial step's.

**Why this is `Verify/Cached`, not `Cached`.**  The parallel install's
driver (`ConLeche/Driver/ParInstall.lean`) carries the serial fold's
accepting run, and the step it adds for a record a worker installed is
this congruence; the driver (`ConLeche/Driver/*`) may import
`Verify/*` (maintainer's ruling, 2026-10-08), so the file sits where a
proof about kernel functions that needs no model belongs.  It imports
only the cached checker — nothing from the theory — and opens a plain
`public section` (it defines nothing for anyone to unfold).
-/

namespace ConLeche.Cached

variable {mode : CheckMode} {fe₁ fe₂ : FEnv}

/-! ## The environment-index guards (`ConLeche/Kernel/FEnv.lean`) -/

/-- `FEnv.findProj?` reads `fe` only through `find?`. -/
theorem findProj?_congr (hfe : fe₁.find? = fe₂.find?) :
    fe₁.findProj? = fe₂.findProj? := by
  funext T i; unfold FEnv.findProj?; simp only [hfe]

/-- `FEnv.towerSlotsAllF` reads `fe` only through `find?`. -/
theorem towerSlotsAllF_congr (hfe : fe₁.find? = fe₂.find?) :
    fe₁.towerSlotsAllF = fe₂.towerSlotsAllF := by
  funext T nF; unfold FEnv.towerSlotsAllF; simp only [findProj?_congr hfe]

/-- `FEnv.andRescueSlotsF` reads `fe` only through `find?`. -/
theorem andRescueSlotsF_congr (hfe : fe₁.find? = fe₂.find?) :
    fe₁.andRescueSlotsF = fe₂.andRescueSlotsF := by
  funext ctor nP ust; unfold FEnv.andRescueSlotsF
  simp only [findProj?_congr hfe]

/-- `natLitSupportedF` reads `fe` only through `find?`. -/
theorem natLitSupportedF_congr (hfe : fe₁.find? = fe₂.find?) :
    natLitSupportedF fe₁ = natLitSupportedF fe₂ := by
  unfold natLitSupportedF; simp only [hfe]

/-- `strLitSupportedF` reads `fe` only through `find?`. -/
theorem strLitSupportedF_congr (hfe : fe₁.find? = fe₂.find?) :
    strLitSupportedF fe₁ = strLitSupportedF fe₂ := by
  unfold strLitSupportedF; simp only [hfe, natLitSupportedF_congr hfe]

/-- `natOpStoredF` reads `fe` only through `find?`. -/
theorem natOpStoredF_congr (hfe : fe₁.find? = fe₂.find?) :
    natOpStoredF fe₁ = natOpStoredF fe₂ := by
  funext c; unfold natOpStoredF; simp only [hfe]

/-! ## The cached guards and stored-constant reads
(`ConLeche/Cached/StateC.lean`) -/

/-- `isCtorAppC` reads `fe` only through `find?`. -/
theorem isCtorAppC_congr (hfe : fe₁.find? = fe₂.find?) :
    isCtorAppC fe₁ = isCtorAppC fe₂ := by
  funext e; unfold isCtorAppC; simp only [hfe]

/-- `headHintC` reads `fe` only through `find?`. -/
theorem headHintC_congr (hfe : fe₁.find? = fe₂.find?) :
    headHintC fe₁ = headHintC fe₂ := by
  funext e; unfold headHintC; simp only [hfe]

/-- `unfoldableHeadC` reads `fe` only through `find?`. -/
theorem unfoldableHeadC_congr (hfe : fe₁.find? = fe₂.find?) :
    unfoldableHeadC fe₁ = unfoldableHeadC fe₂ := by
  funext e; unfold unfoldableHeadC; simp only [hfe]

/-- `etaCtorShapeC` reads `fe` only through `find?`. -/
theorem etaCtorShapeC_congr (hfe : fe₁.find? = fe₂.find?) :
    etaCtorShapeC fe₁ = etaCtorShapeC fe₂ := by
  funext e; unfold etaCtorShapeC; simp only [hfe]

/-- `constTyAtM` reads `fe` only through `find?`. -/
theorem constTyAtM_congr (hfe : fe₁.find? = fe₂.find?) :
    constTyAtM fe₁ = constTyAtM fe₂ := by
  funext nI n us; unfold constTyAtM; simp only [hfe]

/-- `constValAtM` reads `fe` only through `find?`. -/
theorem constValAtM_congr (hfe : fe₁.find? = fe₂.find?) :
    constValAtM fe₁ = constValAtM fe₂ := by
  funext nI n us; unfold constValAtM; simp only [hfe]

/-- `ruleRhsAtM` reads `fe` only through `find?`. -/
theorem ruleRhsAtM_congr (hfe : fe₁.find? = fe₂.find?) :
    ruleRhsAtM fe₁ = ruleRhsAtM fe₂ := by
  funext cI jI c j us; unfold ruleRhsAtM; simp only [hfe]

/-- The walk's plain descent reads `fe` only through `find?`. -/
theorem constsResolveFP_congr (hfe : fe₁.find? = fe₂.find?) : ∀ e : Expr,
    constsResolveFP fe₁ e = constsResolveFP fe₂ e := by
  intro e
  induction e with
  | bvar i => rw [constsResolveFP, constsResolveFP]
  | sort u => rw [constsResolveFP, constsResolveFP]
  | lit l => cases l <;> simp only [constsResolveFP, hfe]
  | const n us => simp only [constsResolveFP, hfe]
  | fvar idx ty iht => simp only [constsResolveFP, iht]
  | app f a ihf iha => simp only [constsResolveFP, ihf, iha]
  | lam ty body iht ihb => simp only [constsResolveFP, iht, ihb]
  | forallE ty body iht ihb => simp only [constsResolveFP, iht, ihb]
  | letE ty val body iht ihv ihb => simp only [constsResolveFP, iht, ihv, ihb]
  | proj sn i sub ih => simp only [constsResolveFP, hfe, ih]

/-- `constsResolveFC` reads `fe` only through `find?`. -/
theorem constsResolveFC_congr (hfe : fe₁.find? = fe₂.find?) :
    constsResolveFC fe₁ = constsResolveFC fe₂ := by
  funext e
  unfold constsResolveFC
  rw [Expr.resBool_eq, Expr.resBool_eq]
  exact constsResolveFP_congr hfe e

/-! ## The core's readers (`ConLeche/Cached/CoreC.lean`)

Each lemma equates the two partial applications at everything up to
and including `fe`, so `simp only [f_congr hfe]` rewrites a call site
inside a larger body.  A few of these functions only *thread* `fe`;
their hypothesis is still taken, because it is what pins the two
indices when the lemma is used as a rewrite rule.
-/

/-- `unfoldDefinitionI` reads `fe` only through `find?`. -/
theorem unfoldDefinitionI_congr (hfe : fe₁.find? = fe₂.find?) :
    unfoldDefinitionI fe₁ = unfoldDefinitionI fe₂ := by
  funext e; unfold unfoldDefinitionI; simp only [hfe, constValAtM_congr hfe]

/-- `litToCtorIfNatI` reads `fe` only through `find?`. -/
theorem litToCtorIfNatI_congr (hfe : fe₁.find? = fe₂.find?) :
    litToCtorIfNatI fe₁ = litToCtorIfNatI fe₂ := by
  funext e; unfold litToCtorIfNatI; simp only [natLitSupportedF_congr hfe]

/-- `reduceNatI` reads `fe` only through `find?`. -/
theorem reduceNatI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    reduceNatI r fe₁ = reduceNatI r fe₂ := by
  funext depth e; unfold reduceNatI
  simp only [natLitSupportedF_congr hfe, natOpStoredF_congr hfe]

/-- `iotaCertsFullIAux` only threads `fe`. -/
theorem iotaCertsFullIAux_congr (_hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    iotaCertsFullIAux r fe₁ = iotaCertsFullIAux r fe₂ := by
  funext depth ty acc args
  induction ty, acc, args using iotaCertsFullIAux.induct with
  | case1 ty acc => rw [iotaCertsFullIAux.eq_def, iotaCertsFullIAux.eq_def]
  | case2 acc arg rest dom body ih =>
    rw [iotaCertsFullIAux.eq_def, iotaCertsFullIAux.eq_def]; simp only [ih]
  | case3 arg rest i => rw [iotaCertsFullIAux.eq_def, iotaCertsFullIAux.eq_def]
  | case4 arg rest i head tail ih =>
    rw [iotaCertsFullIAux.eq_def, iotaCertsFullIAux.eq_def]; simp only [ih]
  | case5 ty acc arg rest h₁ h₂ =>
    rw [iotaCertsFullIAux.eq_def, iotaCertsFullIAux.eq_def]
    cases ty with
    | forallE d b => exact (h₁ _ _ rfl).elim
    | bvar i => exact (h₂ _ rfl).elim
    | _ => rfl

/-- `iotaCertsFullI` only threads `fe`. -/
theorem iotaCertsFullI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    iotaCertsFullI r fe₁ = iotaCertsFullI r fe₂ := by
  funext depth ty args; unfold iotaCertsFullI
  simp only [iotaCertsFullIAux_congr hfe]

/-- `projCertAtF` reads `fe` only through `find?`. -/
theorem projCertAtF_congr (hfe : fe₁.find? = fe₂.find?) :
    projCertAtF fe₁ = projCertAtF fe₂ := by
  funext verified c args; unfold projCertAtF projCertF
  simp only [hfe]

/-- `defEqListI` only threads `fe`. -/
theorem defEqListI_congr (_hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    defEqListI r fe₁ = defEqListI r fe₂ := by
  funext depth as bs
  induction as generalizing bs with
  | nil => cases bs <;> rfl
  | cons a as ih =>
    cases bs with
    | nil => rfl
    | cons b bs => simp only [defEqListI, ih]

/-- `iotaIndexOkI` only threads `fe`. -/
theorem iotaIndexOkI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    iotaIndexOkI r fe₁ = iotaIndexOkI r fe₂ := by
  funext depth mI rP cnP tyCtor margs idx; unfold iotaIndexOkI
  simp only [defEqListI_congr hfe]

/-- `defeqSpineI` only threads `fe`. -/
theorem defeqSpineI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    defeqSpineI r fe₁ = defeqSpineI r fe₂ := by
  funext depth a b; unfold defeqSpineI; simp only [defEqListI_congr hfe]

/-- `propIrrelI` reads `fe` only through `find?`. -/
theorem propIrrelI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    propIrrelI r fe₁ = propIrrelI r fe₂ := by
  funext depth a b; unfold propIrrelI; simp only [hfe]

/-- `structEtaCertWithI` reads `fe` only through `find?`. -/
theorem structEtaCertWithI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    structEtaCertWithI r fe₁ = structEtaCertWithI r fe₂ := by
  funext depth a b wtb; unfold structEtaCertWithI
  simp only [hfe, towerSlotsAllF_congr hfe, defEqListI_congr hfe]

/-- `structEtaCertI` reads `fe` only through `find?`. -/
theorem structEtaCertI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    structEtaCertI r fe₁ = structEtaCertI r fe₂ := by
  funext depth a b; unfold structEtaCertI
  simp only [etaCtorShapeC_congr hfe, structEtaCertWithI_congr hfe]

/-- `structUnitCertI` reads `fe` only through `find?`. -/
theorem structUnitCertI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    structUnitCertI r fe₁ = structUnitCertI r fe₂ := by
  funext depth a b; unfold structUnitCertI
  simp only [hfe]

/-- `etaCertI` does not read `fe` at all. -/
theorem etaCertI_congr (_hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    etaCertI mode r fe₁ = etaCertI mode r fe₂ := rfl

/-- `stuckIrrelI` reads `fe` only through `find?`. -/
theorem stuckIrrelI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    stuckIrrelI r fe₁ = stuckIrrelI r fe₂ := by
  funext depth a b; unfold stuckIrrelI
  simp only [structEtaCertI_congr hfe, structUnitCertI_congr hfe]

/-- `majorToCtorI` reads `fe` only through `find?`. -/
theorem majorToCtorI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    majorToCtorI mode r fe₁ = majorToCtorI mode r fe₂ := by
  funext depth recName rules major; unfold majorToCtorI
  simp only [isCtorAppC_congr hfe, hfe,
    towerSlotsAllF_congr hfe, andRescueSlotsF_congr hfe]

/-- `litMajorToCtorI` reads `fe` only through `find?`. -/
theorem litMajorToCtorI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    litMajorToCtorI r fe₁ = litMajorToCtorI r fe₂ := by
  funext depth e; unfold litMajorToCtorI
  simp only [strLitSupportedF_congr hfe, litToCtorIfNatI_congr hfe]

/-- `projLitToCtorI` reads `fe` only through `find?`. -/
theorem projLitToCtorI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    projLitToCtorI r fe₁ = projLitToCtorI r fe₂ := by
  funext depth e; unfold projLitToCtorI; simp only [strLitSupportedF_congr hfe]

/-- `prepareMajorI` reads `fe` only through `find?`. -/
theorem prepareMajorI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    prepareMajorI mode r fe₁ = prepareMajorI mode r fe₂ := by
  funext depth recName rules major; unfold prepareMajorI
  simp only [majorToCtorI_congr hfe, litMajorToCtorI_congr hfe, isCtorAppC_congr hfe]

/-- `iotaArityOk` reads `fe` only through `find?`. -/
theorem iotaArityOk_congr (hfe : fe₁.find? = fe₂.find?) :
    iotaArityOk fe₁ = iotaArityOk fe₂ := by
  funext e; unfold iotaArityOk; simp only [hfe]

/-- `iotaRecI` reads `fe` only through `find?`. -/
theorem iotaRecI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    iotaRecI mode r fe₁ = iotaRecI mode r fe₂ := by
  funext depth e; unfold iotaRecI
  simp only [hfe, prepareMajorI_congr hfe, defEqListI_congr hfe,
    constTyAtM_congr hfe, iotaCertsFullI_congr hfe,
    iotaIndexOkI_congr hfe, ruleRhsAtM_congr hfe]

/-- The peel loop only threads `fe`: it reads none of it. -/
theorem betaPeelI_congr (r : CoreFnsI) (depth : Nat) :
    betaPeelI r fe₁ depth = betaPeelI r fe₂ depth := by
  funext t acc args
  induction args generalizing t acc with
  | nil => rw [betaPeelI.eq_def, betaPeelI.eq_def]
  | cons a rest ih =>
    rw [betaPeelI.eq_def, betaPeelI.eq_def]
    cases t <;> simp only [ih]

/-- `whnfAppI` reads `fe` only through `find?`. -/
theorem whnfAppI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI)
    (depth : Nat) :
    whnfAppI mode r fe₁ depth = whnfAppI mode r fe₂ depth := by
  funext v args
  induction args generalizing v with
  | nil => rw [whnfAppI.eq_def, whnfAppI.eq_def]
  | cons a rest ih =>
    rw [whnfAppI.eq_def, whnfAppI.eq_def]
    cases v <;> simp only [betaPeelI_congr (fe₁ := fe₁) (fe₂ := fe₂), iotaArityOk_congr hfe,
      iotaRecI_congr hfe, ih]

/-- `reduceProjCoreI` reads `fe` only through `find?`. -/
theorem reduceProjCoreI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    reduceProjCoreI mode r fe₁ = reduceProjCoreI mode r fe₂ := by
  funext depth sn i c; unfold reduceProjCoreI
  simp only [projLitToCtorI_congr hfe, findProj?_congr hfe, projCertAtF_congr hfe]

/-- `whnfCoreStepI` reads `fe` only through `find?`. -/
theorem whnfCoreStepI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    whnfCoreStepI mode r fe₁ = whnfCoreStepI mode r fe₂ := by
  funext cheap depth e; unfold whnfCoreStepI
  simp only [whnfAppI_congr hfe, reduceProjCoreI_congr hfe]

/-- `whnfCoreLoopI` reads `fe` only through `find?`. -/
theorem whnfCoreLoopI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    whnfCoreLoopI mode r fe₁ = whnfCoreLoopI mode r fe₂ := by
  funext cheap depth n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext e; unfold whnfCoreLoopI; rw [ih, whnfCoreStepI_congr hfe]

/-- `whnfCoreBodyI` reads `fe` only through `find?`. -/
theorem whnfCoreBodyI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    whnfCoreBodyI mode r fe₁ = whnfCoreBodyI mode r fe₂ := by
  funext cheap depth e; unfold whnfCoreBodyI; rw [whnfCoreLoopI_congr hfe]

/-- `inferSpineI` only threads `fe`. -/
theorem inferSpineI_congr (_hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    inferSpineI r fe₁ = inferSpineI r fe₂ := by
  funext depth ty acc args
  induction args generalizing ty acc with
  | nil => rfl
  | cons a as ih => simp only [inferSpineI, ih]

/-- `inferSpineIOI` only threads `fe`. -/
theorem inferSpineIOI_congr (_hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    inferSpineIOI r fe₁ = inferSpineIOI r fe₂ := by
  funext depth ty acc args
  induction args generalizing ty acc with
  | nil => rfl
  | cons a as ih => simp only [inferSpineIOI, ih]

/-- `whnfStepI` reads `fe` only through `find?`. -/
theorem whnfStepI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    whnfStepI r fe₁ = whnfStepI r fe₂ := by
  funext depth k e; unfold whnfStepI
  simp only [reduceNatI_congr hfe, unfoldDefinitionI_congr hfe]

/-- `whnfLoopI` reads `fe` only through `find?`. -/
theorem whnfLoopI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    whnfLoopI r fe₁ = whnfLoopI r fe₂ := by
  funext depth n
  induction n with
  | zero => rfl
  | succ n ih => funext e; unfold whnfLoopI; rw [ih, whnfStepI_congr hfe]

/-- `whnfBodyI` reads `fe` only through `find?`. -/
theorem whnfBodyI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    whnfBodyI r fe₁ = whnfBodyI r fe₂ := by
  funext depth e; unfold whnfBodyI; rw [whnfLoopI_congr hfe]

/-- `inferBodyI` reads `fe` only through `find?`. -/
theorem inferBodyI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    inferBodyI r fe₁ = inferBodyI r fe₂ := by
  funext depth e; unfold inferBodyI
  simp only [hfe, natLitSupportedF_congr hfe, strLitSupportedF_congr hfe,
    constTyAtM_congr hfe, inferSpineI_congr hfe, findProj?_congr hfe]

/-- `inferBodyIOI` reads `fe` only through `find?`. -/
theorem inferBodyIOI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    inferBodyIOI r fe₁ = inferBodyIOI r fe₂ := by
  funext depth e; unfold inferBodyIOI
  simp only [inferSpineIOI_congr hfe, inferBodyI_congr hfe]

/-- `lazyDeltaStepI` reads `fe` only through `find?`. -/
theorem lazyDeltaStepI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    lazyDeltaStepI mode r fe₁ = lazyDeltaStepI mode r fe₂ := by
  funext depth a b; unfold lazyDeltaStepI
  simp only [unfoldableHeadC_congr hfe, unfoldDefinitionI_congr hfe,
    headHintC_congr hfe, defeqSpineI_congr hfe]

/-- `lazyDeltaReductionI` reads `fe` only through `find?`. -/
theorem lazyDeltaReductionI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    lazyDeltaReductionI mode r fe₁ = lazyDeltaReductionI mode r fe₂ := by
  funext depth n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext a b; unfold lazyDeltaReductionI
    simp only [ih, reduceNatI_congr hfe, lazyDeltaStepI_congr hfe]

/-- `lazyDeltaProjReductionI` reads `fe` only through `find?`. -/
theorem lazyDeltaProjReductionI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    lazyDeltaProjReductionI mode r fe₁ = lazyDeltaProjReductionI mode r fe₂ := by
  funext depth sn i n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext a b; unfold lazyDeltaProjReductionI
    simp only [ih, lazyDeltaStepI_congr hfe, reduceProjCoreI_congr hfe]

/-- `defeqProjPairI` reads `fe` only through `find?`. -/
theorem defeqProjPairI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    defeqProjPairI mode r fe₁ = defeqProjPairI mode r fe₂ := by
  funext depth a b; unfold defeqProjPairI
  simp only [lazyDeltaProjReductionI_congr hfe]

/-- `defeqStuckI` reads `fe` only through `find?`. -/
theorem defeqStuckI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    defeqStuckI mode r fe₁ = defeqStuckI mode r fe₂ := by
  funext depth a b; unfold defeqStuckI
  simp only [stuckIrrelI_congr hfe, strLitSupportedF_congr hfe,
    defEqListI_congr hfe, etaCertI_congr hfe]

/-- `defeqBodyI` reads `fe` only through `find?`. -/
theorem defeqBodyI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    defeqBodyI mode r fe₁ = defeqBodyI mode r fe₂ := by
  funext depth a b; unfold defeqBodyI
  simp only [propIrrelI_congr hfe, lazyDeltaReductionI_congr hfe,
    defeqProjPairI_congr hfe, defeqStuckI_congr hfe]

/-! ## The knot, and the operation records built on it -/

/-- **The knot reads the index only through `find?`.**  `ensureSortI`
needs no lemma of its own: it takes the tied record, not the index. -/
theorem coreKnotI_congr (hfe : fe₁.find? = fe₂.find?) :
    ∀ F, coreKnotI mode fe₁ F = coreKnotI mode fe₂ F := by
  intro F
  -- the eager slot ties the knot at `mode.toEager` (task #353): the
  -- induction is over every mode at once
  induction F generalizing mode with
  | zero => rfl
  | succ F ih =>
    unfold coreKnotI
    simp only [ih, whnfCoreBodyI_congr hfe, whnfBodyI_congr hfe,
      inferBodyI_congr hfe, defeqBodyI_congr hfe, inferBodyIOI_congr hfe]

/-- `opSIxC` reads `fe` only through `find?`. -/
theorem opSIxC_congr (hfe : fe₁.find? = fe₂.find?) :
    opSIxC mode fe₁ = opSIxC mode fe₂ := by
  funext d i; unfold opSIxC; rw [coreKnotI_congr hfe]

end ConLeche.Cached
