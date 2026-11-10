module

public import ConAgua.Arena.IndCallM
public import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.IndCopy2
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.Bool
public import ConAgua.Arena.IndStubs
import all ConAgua.Arena.IndIface

@[expose] public section

/-!
# CheckStructFieldSortsISucc

`lvl_eq_true`'s model (`eqTrueC`) and the twin's
`checkStructFieldSortsI` at `j + 1` with its universe bound named (`sfbT`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `lvl_eq_true` -/

/-- After `lvl_eq_c`. -/
def eqTrueK : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m) => some (if r.headD 0 = 2 then 1 else 0, m)

theorem eqTrueK_some (r : List Word) (m : Mem) :
    eqTrueK (some (r, m)) = some (if r.headD 0 = 2 then 1 else 0, m) := rfl
attribute [ind_grind] eqTrueK_some

/-- The model of `lvl_eq_true(u, v)` at L fuel `k`, its `lvl_eq_c` call read through `cR`
(`eqTrueW` is the stubs' reading). -/
def eqTrueC (cR : CallM) : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, u, v => eqTrueK (cR k "lvl_eq_c" [u, v] m)

theorem eqTrueC_succ (cR : CallM) (k : Nat) (m : Mem) (u v : Word) :
    eqTrueC cR (k + 1) m u v = eqTrueK (cR k "lvl_eq_c" [u, v] m) := rfl

theorem eqTrue_specC (p : Prog) (hp : p.lookup "lvl_eq_true" = some lvlEqTrue) (cR : CallM)
    (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (u v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lvl_eq_true" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ eqTrueC cR n s₀.mem u v = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lvlEqTrue]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hcR n "lvl_eq_c"] <;>
      finish (gen := 20) [eqTrueC]

/-! ## The relation to the twin -/

/-- The twin's universe bound for one field (`checkStructFieldSortsI`'s middle, verbatim). -/
def sfbT (isProp large : Bool) (s : LIdx) (idxArgs : List EIdx) (fv : EIdx) (u : LIdx) : AM Unit := do
  if !isProp then do
    let lu ← readLevelM u
    let ls ← readLevelM s
    unless ← liftFueled "level comparison" (ConLeche.Level.leq lu ls) do
      fail (.invalid "direct sum: field universe too large")
  else if large then do
    let z ← zeroLevel
    unless (← lvlEq? u z) == some true || idxArgs.contains fv do
      fail (.invalid "direct sum: large eliminator with a non-propositional \
        field outside the indices")

/-- **`checkStructFieldSortsI` at `j + 1`**, its steps named. -/
theorem checkStructFieldSortsI_succ (fe : IFEnv) (isProp large : Bool) (s : LIdx) (nP : Nat)
    (fvs idxArgs : List EIdx) (j : Nat) :
    checkStructFieldSortsI V fe isProp large s nP fvs idxArgs (j + 1) = (do
      let fv ← unwrapOr fvs[j]? (.internal "direct sum: field index")
      let t ← fvarTypeD fv
      let ty ← inferTypeCore V fe checkFuel (nP + j) t
      let u ← ensureSortCore V fe checkFuel (nP + j) ty
      sfbT isProp large s idxArgs fv u
      checkStructFieldSortsI V fe isProp large s nP fvs idxArgs j) := by
  rw [checkStructFieldSortsI]
  simp only [sfbT]
  congr; funext fv; congr; funext t; congr; funext ty; congr; funext u
  cases isProp <;> cases large <;>
    simp only [Bool.not_false, Bool.not_true, ite_true, ite_false, Bool.false_eq_true, bind_assoc,
      pure_bind]
  all_goals first
    | rfl
    | (congr; funext lu; congr; funext ls; congr; funext d; cases d <;> simp; done)
    | (congr; funext z; congr; funext d; by_cases hc : d = some true ∨ fv ∈ idxArgs <;> simp [hc]; done)

theorem sfb_leq_eq (u s : LIdx) (k : Bool → AM Unit) :
    (do let lu ← readLevelM u; let ls ← readLevelM s
        let b ← liftFueled "level comparison" (ConLeche.Level.leq lu ls); k b) =
      ((do let lu ← readLevelM u; let ls ← readLevelM s; pure (ConLeche.Level.leq lu ls)) >>=
        fun o => liftFueled "level comparison" o >>= k) := by
  simp only [bind_assoc, pure_bind]

/-- **A handle written right before a decoded slice** extends it at the front. -/
theorem sumDecHL_write_front {k : IdxKind} (m : Mem) (o kk : Nat) (w v : Word) (acc : List (Idx k))
    (hw : w.toNat = o) (hsz : o < (m.arr64 IW).size) (hv : H v)
    (h : decHL m (o + 1) kk = some acc) :
    decHL (m.set64 IW w v) o (kk + 1) = some (decI v :: acc) := by
  simp only [decHL, hslice?_succ] at h ⊢
  have e1 : (hslice? (iwA (m.set64 IW w v)) (o + 1) kk : Option (List (Idx k))) =
      hslice? (iwA m) (o + 1) kk :=
    hslice?_congr _ _ _ _ _ fun i _ => by simp only [iwA, aread_apply, set64IW_get]; rw [ite_eq_right (by omega)]
  have e0 : (hd? (iwA (m.set64 IW w v)) o : Option (Idx k)) = some (decI v) := by
    simp [hd?, iwA, aread_apply, set64IW_get, hw, hsz, hv]
  rw [e1, e0, h]; rfl

end L.Ind

end
