module

public import ConRon.Arena.Inductives.RecCheck
import ConAgua.Arena.WhnfIotaRecRefine

@[expose] public section

/-!
# PdsC

`tpClosed`, `tpRest`, `tpStep`, `ite_bind'`, `tpd_cons`, `tpd_nil`, `tpd_nilr`, `word_lt_iff`.
-/

open ConRon.Arena
open scoped Lean.Order

namespace L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-! ## The twin's step -/

/-- The closedness test of `targetParamsDefEq`'s `cons` arm. -/
def tpClosed (pfvs : List EIdx) (a b : EIdx) : AM Bool := do
  if (← bvarB coreWalkFuel a) != 0 then pure false
  else if (← bvarB coreWalkFuel b) != 0 then pure false
  else if (← fvarB coreWalkFuel a) > pfvs.length then pure false
  else pure (decide ((← fvarB coreWalkFuel b) ≤ pfvs.length))

/-- The rest of the head step: `true` to go on with the tails. -/
def tpRest (fe : IFEnv) (d : Nat) (names : List NIdx) (lvls : LsIdx) (holes pfvs : List EIdx) (a b : EIdx) :
    AM Bool := do
  let ac ← ConRon.Arena.targetCanonParams pfvs a
  let a' ← ConRon.Arena.targetAbs names lvls holes ac
  let bc ← ConRon.Arena.targetCanonParams pfvs b
  let b' ← ConRon.Arena.targetAbs names lvls holes bc
  if a' == b' then pure true
  else
    let _ ← inferTypeCore V fe checkFuel d a'
    let _ ← inferTypeCore V fe checkFuel d b'
    isDefEqCore V fe checkFuel d a' b'

/-- The head step of `targetParamsDefEq`. -/
def tpStep (fe : IFEnv) (d : Nat) (names : List NIdx) (lvls : LsIdx) (holes pfvs : List EIdx) (a b : EIdx) :
    AM Bool := do
  let closed ← tpClosed pfvs a b
  if !closed then pure false else tpRest fe d names lvls holes pfvs a b

theorem tpd_cons (fe : IFEnv) (d : Nat) (names : List NIdx) (lvls : LsIdx) (holes pfvs : List EIdx)
    (a b : EIdx) (as bs : List EIdx) :
    ConRon.Arena.targetParamsDefEq V fe d names lvls holes pfvs (a :: as) (b :: bs) =
      (do let c ← tpStep fe d names lvls holes pfvs a b
          if c then ConRon.Arena.targetParamsDefEq V fe d names lvls holes pfvs as bs else pure false) := by
  rw [ConRon.Arena.targetParamsDefEq]
  simp only [tpStep, tpClosed, tpRest, bind_assoc, L.Arena.ite_bind, pure_bind]
  rfl

theorem tpd_nil (fe : IFEnv) (d : Nat) (names : List NIdx) (lvls : LsIdx) (holes pfvs : List EIdx)
    (bs : List EIdx) :
    ConRon.Arena.targetParamsDefEq V fe d names lvls holes pfvs [] bs = pure (bs.isEmpty) := by
  cases bs <;> rfl

theorem tpd_nilr (fe : IFEnv) (d : Nat) (names : List NIdx) (lvls : LsIdx) (holes pfvs : List EIdx)
    (a : EIdx) (as : List EIdx) :
    ConRon.Arena.targetParamsDefEq V fe d names lvls holes pfvs (a :: as) [] = pure false := by rfl

theorem word_lt_iff {a b : UInt64} : a < b ↔ a.toNat < b.toNat := UInt64.lt_iff_toNat_lt

end L.Ind
