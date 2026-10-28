import ConAgua.Arena.IndPosSpec.MatesW
import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# CheckStructFieldSortsISucc

`lvl_eq_true`'s model (`eqTrueC`), `check_field_sort_bound`'s (`cfbW`), and the twin's
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

/-! ## `check_field_sort_bound`: the word model -/

/-- After `sl_contains`. -/
def cfbK4 (eq : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some ct => if eq = 0 ∧ ct = 0 then none else some ([0], m)
/-- After `lvl_eq_true`. -/
def cfbK3 (n : Nat) (io il fv : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (eq, m) => cfbK4 eq m (containsW n m io il fv)
/-- After `pin_word(53)`. -/
def cfbK2 (cR : CallM) (n : Nat) (io il fv u : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some z => cfbK3 n io il fv (eqTrueC cR n m u z)
/-- After `lv_leq_top`. -/
def cfbK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 2 then some ([0], m) else none

/-- **The model of `check_field_sort_bound(isProp, large, s, io, il, fv, u)`** at exec fuel `n`. -/
def cfbW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, isProp, large, s, io, il, fv, u =>
    if isProp = 0 then cfbK1 (cR n "lv_leq_top" [u, s] m)
    else if large ≠ 0 then cfbK2 cR n io il fv u m (pinWordV m 53)
    else some ([0], m)

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (isProp large s io il fv u eq ct z : Word) (r : List Word)
theorem cfbK4_fail (h : eq = 0 ∧ ct = 0) : cfbK4 eq m (some ct) = none := by simp [cfbK4, h]
theorem cfbK4_ok (h : ¬ (eq = 0 ∧ ct = 0)) : cfbK4 eq m (some ct) = some ([0], m) := by
  simp only [cfbK4, ite_eq_right h]
theorem cfbK3_some : cfbK3 n io il fv (some (eq, m)) = cfbK4 eq m (containsW n m io il fv) := rfl
theorem cfbK2_some : cfbK2 cR n io il fv u m (some z) = cfbK3 n io il fv (eqTrueC cR n m u z) := rfl
theorem cfbK1_ok (h : r.headD 0 = 2) : cfbK1 (some (r, m)) = some ([0], m) := by
  simp only [cfbK1]; rw [ite_eq_left h]
theorem cfbK1_fail (h : r.headD 0 ≠ 2) : cfbK1 (some (r, m)) = none := by
  simp only [cfbK1]; rw [ite_eq_right h]
theorem cfbW_leq (h : isProp = 0) :
    cfbW cR (n + 1) m isProp large s io il fv u = cfbK1 (cR n "lv_leq_top" [u, s] m) := by
  simp [cfbW, h]
theorem cfbW_large (h : isProp ≠ 0) (hl : large ≠ 0) :
    cfbW cR (n + 1) m isProp large s io il fv u = cfbK2 cR n io il fv u m (pinWordV m 53) := by
  simp [cfbW, h, hl]
theorem cfbW_none (h : isProp ≠ 0) (hl : large = 0) :
    cfbW cR (n + 1) m isProp large s io il fv u = some ([0], m) := by simp [cfbW, h, hl]
end arms
attribute [ind_grind] cfbK4_fail cfbK4_ok cfbK3_some cfbK2_some cfbK1_ok cfbK1_fail cfbW_leq
  cfbW_large cfbW_none

section spec
variable (p : Prog) (hpw : p.lookup "pin_word" = some pinWordL)
  (het : p.lookup "lvl_eq_true" = some lvlEqTrue) (hc : p.lookup "sl_contains" = some slContains)
  (hp : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
include hpw het hc hp

theorem cfbW_spec (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (isProp large s io il fv u : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_field_sort_bound" [isProp, large, s, io, il, fv, u]
    ⦃fun r s' => LocEq s' s₀ ∧ cfbW cR n s₀.mem isProp large s io il fv u = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkFieldSortBoundL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        hcR n "lv_leq_top", pinWord_specV p hpw n, eqTrue_specC p het cR hcR n,
        slContains_spec p hc n] <;>
      finish (gen := 20)

end spec

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
      let rest ← checkStructFieldSortsI V fe isProp large s nP fvs idxArgs j
      pure (rest ++ [u])) := by
  simp only [checkStructFieldSortsI, sfbT]
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
    hslice?_congr _ _ _ _ _ fun i _ => by simp only [iwA, set64IW_get]; rw [ite_eq_right (by omega)]
  have e0 : (hd? (iwA (m.set64 IW w v)) o : Option (Idx k)) = some (decI v) := by
    simp [hd?, iwA, set64IW_get, hw, hsz, hv]
  rw [e1, e0, h]; rfl

theorem sum_toNat_add {a b : Word} (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h

end L.Ind

end
