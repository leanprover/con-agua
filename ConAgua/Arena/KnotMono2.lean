module

public import ConAgua.Arena.KnotMono1

@[expose] public section

/-!
# The twin's store only grows (2): the `defeq` family, the delta steps, the bodies

`L.Arena.KM.f` for the rest of `coreKnot`'s reachable functions (`KnotMono1.lean`'s list,
continued).
-/

open ConRon.Arena L.Arena

smono_derive ConRon.Arena.defeqBindersInner
smono_derive ConRon.Arena.defeqDomain
smono_derive ConRon.Arena.binderPair?
/-- `defeqBinders` by induction on its budget (its `match` on the budget sits under binds; the
split leaves the budget's equation beside the goal). -/
theorem L.Arena.KM.ConRon.Arena.defeqBinders (mode : ConLeche.CheckMode) (r : CoreFnsA) (lam : Bool)
    (fuel depth : Nat) (fvs : Array EIdx) (ty₁ body₁ ty₂ body₂ : EIdx) (hR : RecSMono r) :
    SMono (defeqBinders mode r lam fuel depth fvs ty₁ body₁ ty₂ body₂) := by
  induction fuel generalizing depth fvs ty₁ body₁ ty₂ body₂ with
  | zero => rw [_root_.ConRon.Arena.defeqBinders]; smono_auto <;> first | omega | simp_all
  | succ _ ih => rw [_root_.ConRon.Arena.defeqBinders]; smono_auto <;> first | omega | simp_all
smono_derive ConRon.Arena.quickDefEq
smono_derive ConRon.Arena.numArgs
smono_derive ConRon.Arena.lamProj?
smono_derive ConRon.Arena.unwrapIdDefs
smono_derive ConRon.Arena.peelPisW
smono_derive ConRon.Arena.readLevel
smono_derive ConRon.Arena.residualPW
smono_derive ConRon.Arena.substPWAt
smono_derive ConRon.Arena.binderDom
smono_derive ConRon.Arena.headTypePW
smono_derive ConRon.Arena.typeSortPWGo
smono_derive ConRon.Arena.typeSortPW
smono_derive ConRon.Arena.headProofPW
smono_derive ConRon.Arena.proofPW
smono_derive ConRon.Arena.notProofFast
smono_derive ConRon.Arena.isProofFast
smono_derive ConRon.Arena.propIrrel
smono_derive ConRon.Arena.isNatZero
smono_derive ConRon.Arena.natPred?
smono_derive ConRon.Arena.defeqOffset
smono_derive ConRon.Arena.defeqNoFvars
smono_derive ConRon.Arena.lazyFoldOk
smono_derive ConRon.Arena.unfoldableHead
smono_derive ConRon.Arena.headIsProj
smono_derive ConRon.Arena.tryUnfoldProjApp
smono_derive ConRon.Arena.deltaQuick
smono_derive ConRon.Arena.headHint
smono_derive ConRon.Arena.sameConstHeads
smono_derive ConRon.Arena.defeqSpine
smono_derive ConRon.Arena.lazyDeltaStep
smono_derive ConRon.Arena.lazyDeltaReduction
smono_derive ConRon.Arena.lazyDeltaProjReduction
smono_derive ConRon.Arena.defeqProjPair
smono_derive ConRon.Arena.etaCtorShape
smono_derive ConRon.Arena.structEtaCertWith
smono_derive ConRon.Arena.etaCtorPartial
smono_derive ConRon.Arena.structEtaFullAt
smono_derive ConRon.Arena.structEtaFull
smono_derive ConRon.Arena.structEtaExpand
smono_derive ConRon.Arena.ioNeutral
smono_derive ConRon.Arena.structEtaCertPartial
smono_derive ConRon.Arena.structEtaCert
smono_derive ConRon.Arena.isPropType
smono_derive ConRon.Arena.unitLikeFields
smono_derive ConRon.Arena.unitLikeShapeAt
smono_derive ConRon.Arena.unitLikeShape
smono_derive ConRon.Arena.unitLikeStruct
smono_derive ConRon.Arena.unitLikeLoop
smono_derive ConRon.Arena.structUnitCert
smono_derive ConRon.Arena.stuckIrrel
smono_derive ConRon.Arena.etaCert
smono_derive ConRon.Arena.defeqStuck
smono_derive ConRon.Arena.boolTrueShortcut
smono_derive ConRon.Arena.defeqBody
smono_derive ConRon.Arena.defeqSet
smono_derive ConRon.Arena.enterEager
smono_derive ConRon.Arena.leaveEager
smono_derive ConRon.Arena.abstract1ArmFVar
smono_derive ConRon.Arena.abstract1Go
smono_derive ConRon.Arena.abstract1Fast
smono_derive ConRon.Arena.inferLamResult
smono_derive ConRon.Arena.inferSpineIO
smono_derive ConRon.Arena.inferAppIOAt
smono_derive ConRon.Arena.inferBodyIO
smono_derive ConRon.Arena.inferIOSet
