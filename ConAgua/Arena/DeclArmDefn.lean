import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.DeclValSpec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# The definition arm `check_decl_defn(i, vis)` (lane `decls3`)

`checkDecl`'s `.defnDecl` arm: the constant check, the definition check (the push), then two
gates at the extended environment `fe2` and the pre-insertion one `fe2.restrictTo fe.visibleBelow`:
the structural-`Nat` gate (`defn_nat_gate`, the twin's lines 104-119: `natGateT`) and the
`Nat.div`-family pin gate (`defn_div_gate`, lines 123-124: `divGateT`). The arm is proved at the
loop's relation through the gates' specs, stated here as hypotheses (`NatGateSpec`,
`DivGateSpec`) for helpers `decls3-nat` and `decls3-divmod` to discharge. The pin gate reads the
pin variants `rom_pin_sets()` lists, so its spec takes lane `romload`'s `PinSetsR m pins`, which
the arm carries from its entry to the gate (`PinSetsR.grow`: the records are below `EREC`'s top
and `CTL[150]`, `CTL[151]` are not written by the arm's text).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind
open L.Rom (PinSetsR PinSetR SliceR HdrR)
open L.Front (DECL DLP DeclsF DeclAt CVAt dw)

local notation "V" => ConLeche.CheckMode.verified

/-! ## The twin's two gates -/

/-- The structural-`Nat` gate (`checkDecl`'s lines 104-119), at the extended environment `fe2`
and the pre-insertion one `feR`. -/
def natGateT (feR fe2 : IFEnv) (c : NIdx) : AM Unit := do
  if (← natOpNames).contains c then do
    let g ← natOpGuard fe2 c
    let deps ← natOpDeps c
    unless g && (← natOpStoredOkAll fe2 deps) do
      fail (.notImplemented
        "nonstandard structural Nat operation environment")
    match fe2.find? c with
    | some (.defnInfo _ value' _) => do
      let eqs ← natOpEquations 0 c
      let ok ← certifyNatEqs V feR (← substConst0Pairs c value' eqs)
      unless ok do
        fail (.notImplemented
          "nonstandard structural Nat operation")
    | _ => fail (.internal
        "structural Nat operation not stored")

/-- The `Nat.div`-family pin gate (`checkDecl`'s lines 123-124). -/
def divGateT (pins : List INatOpPinSet) (feR fe2 : IFEnv) (c : NIdx) : AM Unit := do
  if (← natDivModNames).contains c then
    checkDivModPin V pins feR fe2 c

/-- **The arm is the two checks, then the two gates** (the twin's `do` block, its join points
distributed over the gates' branches). -/
theorem checkDecl_defn_eq (pins : List INatOpPinSet) (fe : IFEnv) (cv : IConstantVal) (v : EIdx)
    (h : ConLeche.ReducibilityHint) :
    checkDecl V pins fe (.defnDecl cv v h) = (do
      checkConstantVal V fe cv
      let fe2 ← checkDefnVal V fe cv v h
      natGateT (fe2.restrictTo fe.visibleBelow) fe2 cv.name
      divGateT pins (fe2.restrictTo fe.visibleBelow) fe2 cv.name
      pure fe2) := by
  simp only [checkDecl, natGateT, divGateT, bind_assoc]
  congr 1; funext _; congr 1; funext fe2; congr 1; funext x
  split
  · rw [bind_assoc]
    congr 1; funext g
    rw [bind_assoc]; congr 1; funext deps
    rw [bind_assoc]; congr 1; funext b
    cases hf : fe2.find? cv.name with
    | none => split <;> simp [fail_bindAM] <;> try (congr 1; funext u; congr 1; funext y; split <;> simp [fail_bindAM])
    | some ci =>
      cases ci
      case defnInfo cv' val hint =>
        split
        · simp only [bind_assoc]
          congr 1; funext eqs; congr 1; funext l; congr 1; funext ok
          split <;> simp [fail_bindAM] <;> try (congr 1; funext u; congr 1; funext y; split <;> simp)
        · simp only [bind_assoc]
          congr 1; funext u
          congr 1; funext eqs; congr 1; funext l; congr 1; funext ok
          split <;> simp [fail_bindAM] <;> try (congr 1; funext u; congr 1; funext y; split <;> simp)
      all_goals (split <;> simp [fail_bindAM] <;> try (congr 1; funext u; congr 1; funext y; split <;> simp [fail_bindAM]))
  · simp only [pure_bind]
    congr 1; funext y
    split <;> simp

/-! ## The gates' specs (hypotheses) -/

/-- A frame of the step's write set keeps the variant list. -/
theorem PinSetsR.step {m m' : Mem} {ips : List INatOpPinSet} (h : PinSetsR m ips)
    (hg : IWGrow m m') (hf : MemFrame stepA stepC m m') : PinSetsR m' ips :=
  PinSetsR.grow h (IWGrow.recGrow hg) (hf.ctl _ step_pins.1) (hf.ctl _ step_pins.2)

end L.Arena
