module

public import ConAgua.Arena.KnotMono1

@[expose] public section

/-!
# The twin's store only grows (2): the `defeq` family, the delta steps, the bodies

`L.Arena.KM.f` for the rest of `coreKnot`'s reachable functions (`KnotMono1.lean`'s list,
continued). `defeqPeel` and `defeqLams` are structural recursions whose unfolding lemmas the equation
compiler cannot produce in its budget: one level is stated with the recursive call abstracted
(`peelStep`, as con-ron's `Bridge/Core/Arms/DefeqPeel.lean`, and `lamsStep`) and proved by `delta`.
-/

open ConRon.Arena L.Arena

/-- One level of `defeqPeel`, the recursive call abstracted as `cont` (con-ron's `peelStep`). -/
def peelStep (r : CoreFnsA) (d : Nat) (peel : Nat)
    (cont : EIdx → EIdx → Nat → Array EIdx → AM Bool)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) : AM Bool := do
  if a == b then pure true
  else if peel = 0 || a.tag != ETag.forallE || b.tag != ETag.forallE then
    defeqPeelLeaf r d a b k fvs
  else
    match ← viewBind a with
    | none => failDanglingE
    | some (da, ba) =>
      match ← viewBind b with
      | none => failDanglingE
      | some (db, bb) => do
        let sameDom := da == db
        let t1 ← instantiateListFast coreWalkFuel da fvs 0
        let t2 ← if sameDom then pure t1
                 else instantiateListFast coreWalkFuel db fvs 0
        let dq ← if sameDom then pure true else r.defeq (d + k) t1 t2
        if !dq then pure false
        else do
          let fv ← internFVarE (d + k) t2
          cont ba bb (k + 1) (fvs.push fv)

theorem defeqPeel_succ_eq' (r : CoreFnsA) (d p : Nat) (a b : EIdx) (k : Nat) (fvs : Array EIdx) :
    defeqPeel r d (p + 1) a b k fvs = peelStep r d (p + 1) (defeqPeel r d p) a b k fvs := by
  delta defeqPeel peelStep
  exact rfl

theorem defeqPeel_zero_eq' (r : CoreFnsA) (d : Nat) (a b : EIdx) (k : Nat) (fvs : Array EIdx) :
    defeqPeel r d 0 a b k fvs = peelStep r d 0 (defeqPeelLeaf r d) a b k fvs := by
  delta defeqPeel peelStep
  exact rfl

/-- `defeqPeel` by induction on the peel budget, over the unfoldings `defeqPeel_succ_eq'`,
`defeqPeel_zero_eq'` (its own unfolding lemma is out of the equation compiler's budget). -/
theorem L.Arena.KM.ConRon.Arena.defeqPeel (r : CoreFnsA) (d peel : Nat) (a b : EIdx) (k : Nat)
    (fvs : Array EIdx) (hR : RecSMono r) : SMono (defeqPeel r d peel a b k fvs) := by
  induction peel generalizing a b k fvs with
  | zero => rw [defeqPeel_zero_eq']; simp only [peelStep]; smono_auto
  | succ p ih => rw [defeqPeel_succ_eq']; simp only [peelStep]; smono_auto
smono_derive ConRon.Arena.defeqBinders
smono_derive ConRon.Arena.defeqLamsInner
smono_derive ConRon.Arena.lamPair?

/-- One level of `defeqLams`, the recursive call abstracted as `cont` (the equation compiler cannot
produce `defeqLams`' unfolding lemma in its budget; `defeqPeel`'s `peelStep`). -/
def lamsStep (mode : ConLeche.CheckMode) (r : CoreFnsA) (fuel : Nat)
    (cont : Nat → Nat → EIdx → EIdx → EIdx → EIdx → AM Bool) (depth : Nat) (ty₁ body₁ ty₂ body₂ : EIdx) :
    AM Bool := do
  if !(← r.defeq depth ty₁ ty₂) then pure false
  else do
  let fv ← internFVarE depth ty₂
  let b₁ ← instantiate1Fast coreWalkFuel body₁ fv 0
  let b₂ ← instantiate1Fast coreWalkFuel body₂ fv 0
  match fuel with
  | 0 => defeqLamsInner mode r depth b₁ b₂
  | fuel + 1 =>
    match ← lamPair? b₁ b₂ with
    | some (ty₁', body₁', ty₂', body₂') =>
      if b₁ == b₂ then pure true
      else cont fuel (depth + 1) ty₁' body₁' ty₂' body₂'
    | none => defeqLamsInner mode r depth b₁ b₂

theorem defeqLams_eq (mode : ConLeche.CheckMode) (r : CoreFnsA) (fuel depth : Nat) (a b c e : EIdx) :
    defeqLams mode r fuel depth a b c e = lamsStep mode r fuel (defeqLams mode r) depth a b c e := by
  cases fuel <;> (delta defeqLams lamsStep; exact rfl)

theorem L.Arena.KM.ConRon.Arena.defeqLams (mode : ConLeche.CheckMode) (r : CoreFnsA) (fuel depth : Nat)
    (a b c e : EIdx) (hR : RecSMono r) : SMono (defeqLams mode r fuel depth a b c e) := by
  induction fuel generalizing depth a b c e with
  | zero => rw [defeqLams_eq]; simp only [lamsStep]; smono_auto
  | succ p ih => rw [defeqLams_eq]; simp only [lamsStep]; smono_auto
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
smono_derive ConRon.Arena.structEtaCert
smono_derive ConRon.Arena.structUnitCert
smono_derive ConRon.Arena.stuckIrrel
smono_derive ConRon.Arena.ioNeutral
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
