module

public import ConAgua.Arena.WhnfM2C
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
public import ConAgua.L.Examples
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.WhnfM2C
import all ConAgua.Arena.WhnfIota

@[expose] public section

/-!
# `major_to_ctor`: the twin split along the L pieces, and the leaf specs

The twin `majorToCtor` (`Core.lean:1705-1820`) is one function; its pieces are named here
(`m2cHeadT` … `m2cCheckT`), each the twin's own code with the values decoded so far as
parameters, and `majorToCtorRescue` unfolds into them by `rfl` (`majorToCtorRescue_eq`). Each L piece of
`WhnfM2C.lean` has a unified model (`Verdict/WhnfModels6E.lean`); `major_to_ctor` itself and the
leaves outside the verdict closure (`m2c_const_view`, `m2c_eta2`) get a word-level model through
`callW` and an L spec by `vcgen` + `finish` here.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin, split -/

/-- The major's type in whnf and its head; `k` at a constant head, `major` otherwise. -/
def m2cPreT (r : CoreFnsA) (depth : Nat) (major : EIdx) (k : EIdx → NIdx → LsIdx → AM EIdx) :
    AM EIdx := do
  let tmaj ← r.whnf depth (← r.inferIO depth major)
  let hh ← getAppFn coreWalkFuel tmaj
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T' ust => k tmaj T' ust
    | _ => pure major
  else pure major

/-- The scope guard, the type check and proof irrelevance of a fabricated `fab` (K, `And`). -/
def m2cCheckT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (tmaj fab major : EIdx) : AM EIdx := do
  if ← fabScopeOk depth fab major then do
    if ← r.defeq depth tmaj (← r.inferIO depth fab) then do
      let irK ←
        if mode.verifiedChecks then proofIrrel r fe depth fab major
        else pure true
      if irK then pure fab else pure major
    else pure major
  else pure major

/-- The K arm's fabrication. -/
def m2cK2T (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (ctor : NIdx)
    (cnP : Nat) (tmaj : EIdx) (ust : LsIdx) (major : EIdx) : AM EIdx := do
  let targs ← getAppArgs coreWalkFuel tmaj
  if cnP ≤ targs.length then do
    let hd ← internE (.const ctor ust)
    let fab ← mkAppN hd (targs.take cnP)
    m2cCheckT mode r fe depth tmaj fab major
  else pure major

/-- The K arm. -/
def m2cKT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (ctor : NIdx)
    (lpl cnP : Nat) (T : NIdx) (major : EIdx) : AM EIdx :=
  m2cPreT r depth major fun tmaj T' ust => do
    let ustl ← viewLs ust
    if T' = T ∧ lpl = ustl.length then m2cK2T mode r fe depth ctor cnP tmaj ust major
    else pure major

/-- The η arm's fabrication: the instantiated non-`Prop` test at the use, the stored fact first
(`familyNeverZeroAt`), the η spine at the table's constructor and field count. -/
def m2cEta2T (r : CoreFnsA) (depth : Nat) (T : NIdx) (cvT : IConstantVal)
    (caps : IIndCaps) (tbl : IProjTable) (targs : List EIdx) (ust : LsIdx) (major : EIdx) :
    AM EIdx := do
  if ← familyNeverZeroAt r cvT caps ust then do
    let fabArgs ← etaFabArgsE T targs major tbl.numFields
    let hd ← internE (.const tbl.ctor ust)
    let fab ← mkAppN hd fabArgs
    if ← fabScopeOk depth fab major then pure fab
    else pure major
  else pure major

/-- The η arm. -/
def m2cEtaT (r : CoreFnsA) (depth : Nat) (T : NIdx) (cvT : IConstantVal)
    (caps : IIndCaps) (tbl : IProjTable) (major : EIdx) : AM EIdx :=
  m2cPreT r depth major fun tmaj T' ust => do
    let ustl ← viewLs ust
    let targs ← getAppArgs coreWalkFuel tmaj
    if T' = T ∧ targs.length = tbl.numParams ∧ ustl.length = cvT.levelParams.length then
      m2cEta2T r depth T cvT caps tbl targs ust major
    else pure major

/-- The `And` arm's fabrication. -/
def m2cAnd2T (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (ctor T : NIdx)
    (tmaj : EIdx) (targs : List EIdx) (ust : LsIdx) (major : EIdx) : AM EIdx := do
  let p0 ← internE (.proj T 0 major)
  let p1 ← internE (.proj T 1 major)
  let fabArgs := targs ++ [p0, p1]
  let hd ← internE (.const ctor ust)
  let fab ← mkAppN hd fabArgs
  m2cCheckT mode r fe depth tmaj fab major

/-- The `And` arm. -/
def m2cAndT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (ctor : NIdx)
    (lpl cnP : Nat) (T : NIdx) (major : EIdx) : AM EIdx := do
  let an ← pinAnd
  if T = an then
    m2cPreT r depth major fun tmaj T' ust => do
      match ← viewLsLen ust with
      | none => failDanglingLs
      | some ustl =>
      let targs ← getAppArgs coreWalkFuel tmaj
      let ars ← andRescueSlots fe ctor cnP
      if T' = T ∧ targs.length = cnP ∧ lpl = ustl ∧ ars = true then
        m2cAnd2T mode r fe depth ctor T tmaj targs ust major
      else pure major
  else pure major

/-- The dispatch on the recursor's `isK`, then `etaRescueTable?`. -/
def m2cArmsT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (isK : Bool)
    (rl : IRecRule) (cvj : IConstantVal) (cnP : Nat) (T : NIdx) (cvT : IConstantVal)
    (caps : IIndCaps) (major : EIdx) : AM EIdx := do
  if isK = true then m2cKT mode r fe depth rl.ctor cvj.levelParams.length cnP T major
  else match ← etaRescueTable? (fe.findTable? T) rl.ctor cvj cvT caps with
  | some tbl => m2cEtaT r depth T cvT caps tbl major
  | none => m2cAndT mode r fe depth rl.ctor cvj.levelParams.length cnP T major

/-- The family of the constructor, stored at its `induct` `T`. -/
def m2cCtorT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (isK : Bool)
    (rl : IRecRule) (cvj : IConstantVal) (cnP : Nat) (T : NIdx) (major : EIdx) : AM EIdx :=
  match fe.find? T with
  | some (.indInfo cvT caps) => m2cArmsT mode r fe depth isK rl cvj cnP T cvT caps major
  | _ => pure major

/-- The single rule, its constructor. -/
def m2cHeadT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (isK : Bool)
    (rules : List IRecRule) (major : EIdx) : AM EIdx := do
  match rules with
  | [rl] =>
    match fe.find? rl.ctor with
    | some (.ctorInfo cvj cnP _cnF T) => m2cCtorT mode r fe depth isK rl cvj cnP T major
    | _ => pure major
  | _ => pure major

/-- **The twin is its pieces.** -/
theorem majorToCtorRescue_eq (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (recName : NIdx) (isK : Bool) (rules : List IRecRule) (major : EIdx) :
    majorToCtorRescue mode r fe depth recName isK rules major = m2cHeadT mode r fe depth isK rules major := by
  rfl

/-! ## Word models and L specs

Each piece's run as a function of the memory, its callees through `callW` (`WhnfBase.lean`). -/

/-- Model of `m2c_const_view`. -/
def cvwW (m : Mem) (hh : Word) : Option (List Word) :=
  if tierW hh ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m CONST (tierW hh) ≤ idxW hh then none
  else some [tfld m CONST (tierW hh) (idxW hh) 0,
    tfld m CONST (tierW hh) (idxW hh) 1]

theorem m2cConstView_spec (p : Prog) (hp : p.lookup "m2c_const_view" = some m2cConstViewL)
    (n : Nat) (s₀ : St) (hh : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "m2c_const_view" [hh]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ cvwW s₀.mem hh = some r; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, m2cConstViewL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
        tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] <;>
      finish [cvwW, tierW, idxW]

/-- The stack writes of `m2c_and2`: the two projections at `to + tn`, `to + tn + 1`, the top
raised past them. -/
def and2Push (m : Mem) (to tn p0 p1 : Word) : Option Mem :=
  if to + tn < UInt64.ofNat (m.arr64 SPN).size ∧ (to + tn).toNat < (m.arr64 SPN).size ∧
      to + tn + 1 < UInt64.ofNat ((m.set64 SPN (to + tn) p0).arr64 SPN).size ∧
      (to + tn + 1).toNat < ((m.set64 SPN (to + tn) p0).arr64 SPN).size ∧
      136 < (((m.set64 SPN (to + tn) p0).set64 SPN (to + tn + 1) p1).arr64 CTL).size then
    some (((m.set64 SPN (to + tn) p0).set64 SPN (to + tn + 1) p1).set64 CTL 136 (to + tn + 2))
  else none

end L.Arena
