import ConAgua.Arena.DeclArmOpaque
import ConAgua.Arena.DeclPins

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
          split <;> simp [fail_bindAM] <;> try (congr 1; funext u; congr 1; funext y; split <;> simp [fail_bindAM])
        · simp only [bind_assoc]
          congr 1; funext u
          congr 1; funext eqs; congr 1; funext l; congr 1; funext ok
          split <;> simp [fail_bindAM] <;> try (congr 1; funext u; congr 1; funext y; split <;> simp [fail_bindAM])
      all_goals (split <;> simp [fail_bindAM] <;> try (congr 1; funext u; congr 1; funext y; split <;> simp [fail_bindAM]))
  · simp only [pure_bind, bind_assoc]
    congr 1; funext y
    split <;> simp

/-! ## The gates' specs (hypotheses) -/

/-! ## The model -/

section model
variable (p : Prog)

/-- After the pin gate: the extended view. -/
def cdfK5 (w : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m5) => some ([w], m5)

/-- After the structural gate. -/
def cdfK4 (n : Nat) (vis w nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m4) => cdfK5 w (callW p n "defn_div_gate" [vis, w, nm] m4)

/-- After `check_defn_val`. -/
def cdfK3 (n : Nat) (vis nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => cdfK4 p n vis (r3.headD 0) nm (callW p n "defn_nat_gate" [vis, r3.headD 0, nm] m3)

/-- After `check_constant_val`. -/
def cdfK2 (n : Nat) (vis q nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) => cdfK3 p n vis nm (callW p n "check_defn_val" [vis, q] m2)

/-- After `erec_ci`. -/
def cdfK1 (n : Nat) (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    cdfK2 p n vis (r1.headD 0) (rdW (m1.arr64 EREC) (r1.headD 0 + 1))
      (callW p n "check_constant_val" [vis, r1.headD 0 + 1] m1)

/-- **The model of `check_decl_defn(i, vis)`.** -/
def cdfW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, i, vis => cdfK1 p n vis (callW p n "erec_ci" [i, 1] m)

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (i vis q nm w : Word) (r1 r2 r3 r4 r5 : List Word)
theorem cdfW_step : cdfW p (n + 1) m i vis = cdfK1 p n vis (callW p n "erec_ci" [i, 1] m) := rfl
theorem cdfK1_some : cdfK1 p n vis (some (r1, m1)) =
    cdfK2 p n vis (r1.headD 0) (rdW (m1.arr64 EREC) (r1.headD 0 + 1))
      (callW p n "check_constant_val" [vis, r1.headD 0 + 1] m1) := rfl
theorem cdfK2_some : cdfK2 p n vis q nm (some (r2, m2)) =
    cdfK3 p n vis nm (callW p n "check_defn_val" [vis, q] m2) := rfl
theorem cdfK3_some : cdfK3 p n vis nm (some (r3, m3)) =
    cdfK4 p n vis (r3.headD 0) nm (callW p n "defn_nat_gate" [vis, r3.headD 0, nm] m3) := rfl
theorem cdfK4_some : cdfK4 p n vis w nm (some (r4, m4)) =
    cdfK5 w (callW p n "defn_div_gate" [vis, w, nm] m4) := rfl
theorem cdfK5_some : cdfK5 w (some (r5, m5)) = some ([w], m5) := rfl
end arms

grind_pattern [ind_grind] cdfW_step => cdfW p (n + 1) m i vis
grind_pattern [ind_grind] cdfK1_some => cdfK1 p n vis (some (r1, m1))
grind_pattern [ind_grind] cdfK2_some => cdfK2 p n vis q nm (some (r2, m2))
grind_pattern [ind_grind] cdfK3_some => cdfK3 p n vis nm (some (r3, m3))
grind_pattern [ind_grind] cdfK4_some => cdfK4 p n vis w nm (some (r4, m4))
grind_pattern [ind_grind] cdfK5_some => cdfK5 w (some (r5, m5))

set_option maxHeartbeats 1600000 in
theorem cdf_specW (hp : p.lookup "check_decl_defn" = some checkDeclDefn) (n : Nat) (s₀ : St)
    (i vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_decl_defn" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ cdfW p n s₀.mem i vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkDeclDefn]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "erec_ci",
        callW_spec p n "check_constant_val", callW_spec p n "check_defn_val",
        callW_spec p n "defn_nat_gate", callW_spec p n "defn_div_gate"] <;>
      finish (gen := 20) [rdW_eq]

end model

/-- A frame of the step's write set keeps the variant list. -/
theorem PinSetsR.step {m m' : Mem} {ips : List INatOpPinSet} (h : PinSetsR m ips)
    (hg : IWGrow m m') (hf : MemFrame stepA stepC m m') : PinSetsR m' ips :=
  PinSetsR.grow h (IWGrow.recGrow hg) (hf.2.1 _ step_pins.1) (hf.2.1 _ step_pins.2)

end L.Arena
