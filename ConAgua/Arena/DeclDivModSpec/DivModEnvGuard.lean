import ConAgua.Arena.DeclBasisSpec2
import ConAgua.Arena.DeclDivModSpec.BoolCtorTyped
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.ModelGen

/-!
# DivModEnvGuard: `ConRon.Arena.divModEnvGuard`

The refinement theorems `divModEnvGuard_refines` and the lemmas only they use.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open L.Rom (PinSetR)

namespace L.Ind

open L.Arena

structure DmProg7 (p : Prog) : Prop extends DmProg6 p where
  lDivModEnvGuard : p.lookup "div_mod_env_guard" = some divModEnvGuardL
  lFindIs : p.lookup "find_is" = some findIs
  lNatOpGuard' : p.lookup "nat_op_guard" = some natOpGuardL
  lRom : L.Rom.RomRefs p

section envguard
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-- **`div_mod_env_guard` is its model `egW`** (generated). -/
l_model eg_specW (p : Prog) (hp : p.lookup "div_mod_env_guard" = some divModEnvGuardL)
  fns [hp ↦ egW list]
  specs [callW_spec p n "nat_op_guard", callW_spec p n "nat_op_deps", callW_spec p n "nat_op_stored_ok_all", callW_spec p n "pin_at", callW_spec p n "rom_ci", callW_spec p n "find_is", callW_spec p n "bool_ctor_typed"]
  grind [arena_grind] heartbeats 3200000 bind ntBW simp [ntBW]

theorem DmProg7.ty (hD : DmProg7 p) : NatTyProg p := hD.toDmProg6.toDmProg5.toDmProg2.toNatEqProg.toNatTyProg

theorem eg_ref (hD : DmProg7 p) (hdn : DnInj dn) (c : Word) :
    CallRef p "div_mod_env_guard" [vis, c] (fun m s => StageR dn vis fe m s ∧ H c)
      (divModEnvGuard fe (decI c)) (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mq => egW p (k + 1) mq vis c)
    (eg_specW p hD.lDivModEnvGuard (k + 1) · vis c) hcall
  rw [egW.arm1] at hw
  have hT := hD.ty
  -- the dependency guard
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hd1⟩, hw⟩ :=
    (natOpGuard_ref hT.toNatGuardProg (vis := vis) (fe := fe) (dn := dn) c).bind_ ⟨hS, hc⟩ hw
  by_cases z1 : r1.headD 0 = 0
  · rw [ite_eq_left z1] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx1 := decW0B_false hd1 z1
    refine ⟨false, a1, ?_, hS1, hg1, decW0B_of_false _⟩
    simp only [divModEnvGuard, boolTrueName, boolFalseName, StateT.run_bind, hrun1, exc_ok_bind', hx1, Bool.not_false, eq_self, ite_true]
    rfl
  rw [ite_eq_right z1] at hw
  have hx1 := decW0B_true hd1 z1
  -- the dependencies
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hd2⟩, hw⟩ :=
    (natOpDeps_ref hT.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg (vis := vis) (fe := fe) (dn := dn) c).bind_
      ⟨hS1, hc⟩ hw
  unfold decRL at hd2
  simp only [Nat.zero_add, ntGetD0, ntGetD1] at hd2
  replace hw := ntBW_some hw; obtain ⟨r3, m3, h3, hw⟩ := hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := okAll_ref hT (vis := vis) (fe := fe) (dn := dn) (r2.headD 0) (r2.tail.headD 0) x2
    k m2 a2 r3 m3 hS2 hd2.1 hd2.2 h3
  have hG3 : IWGrow m m3 := hg1.trans (hg2.trans hg3)
  by_cases z3 : r3.headD 0 = 0
  · rw [ite_eq_left z3] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx3 := decW0B_false hd3 z3
    refine ⟨false, a3, ?_, hS3, hG3, decW0B_of_false _⟩
    simp only [divModEnvGuard, boolTrueName, boolFalseName, StateT.run_bind, hrun1, exc_ok_bind', hx1, hrun2, hrun3, hx3,
      Bool.not_false, Bool.not_true, eq_self, ite_true, ite_false, Bool.false_eq_true]
    rfl
  rw [ite_eq_right z3] at hw
  have hx3 := decW0B_true hd3 z3
  -- the pinned Eq
  obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4, rfl⟩, hw⟩ :=
    (pinSlot_ref p hD.toDmProg6.toDmProg5.lPinAt 0 pinEq rfl).bind_ hS3 hw
  obtain ⟨r5, m5, x5, a5, hrun5, ⟨hS5, hg5, hd5⟩, hw⟩ :=
    CallRef.bind_ (hD.lRom.ci dn vis fe 0 (by decide)) hS4 hw
  have hrun5' : eqA.run a4 = .ok (x5, a5) := hrun5
  replace hw := ntBW_some hw; obtain ⟨r6, m6, h6, hw⟩ := hw
  obtain ⟨x6, a6, hrun6, hS6, hg6, hd6⟩ :=
    (CallRef.of_refAM (findIs_spec (p := p) hD.toDmProg6.toDmProg5.toDmProg2.cvProg.lCanon dn vis fe hdn (r4.headD 0)
      (r5.headD 0) x5)) k m5 a5 r6 m6 ⟨hS5, hl4, decRCI_get hd5⟩ h6
  obtain ⟨hx6e, hxa⟩ := pure_run_eq hrun6
  subst hxa
  have hG6 : IWGrow m m6 := hG3.trans (hg4.trans (hg5.trans hg6))
  by_cases z6 : r6.headD 0 = 0
  · rw [ite_eq_left z6] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx6 := decW0B_false hd6 z6
    have hb6 : (fe.find? (decI (r4.headD 0)) == some x5) = false := by rw [← hx6e]; exact hx6
    refine ⟨false, a6, ?_, hS6, hG6, decW0B_of_false _⟩
    simp only [divModEnvGuard, boolTrueName, boolFalseName, StateT.run_bind, hrun1, exc_ok_bind', hx1, hrun2, hrun3, hx3, hrun4,
      hrun5', bne, hb6, Bool.not_false, Bool.not_true, eq_self, ite_true, ite_false,
      Bool.false_eq_true]
    rfl
  rw [ite_eq_right z6] at hw
  have hx6 := decW0B_true hd6 z6
  have hb6 : (fe.find? (decI (r4.headD 0)) == some x5) = true := by rw [← hx6e]; exact hx6
  -- the two constructors
  obtain ⟨r7, m7, x7, a7, hrun7, ⟨hS7, hg7, hl7, rfl⟩, hw⟩ :=
    (pinSlot_ref p hD.toDmProg6.toDmProg5.lPinAt 30 pinBoolTrue rfl).bind_ hS6 hw
  obtain ⟨r8, m8, x8, a8, hrun8, ⟨hS8, hg8, hd8⟩, hw⟩ :=
    (bct_ref hD.toDmProg6 (r7.headD 0)).bind_ ⟨hS7, hl7⟩ hw
  have hG8 : IWGrow m m8 := hG6.trans (hg7.trans hg8)
  by_cases z8 : r8.headD 0 = 0
  · rw [ite_eq_left z8] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx8 := decW0B_false hd8 z8
    refine ⟨false, a8, ?_, hS8, hG8, decW0B_of_false _⟩
    simp only [divModEnvGuard, boolTrueName, boolFalseName, StateT.run_bind, hrun1, exc_ok_bind', hx1, hrun2, hrun3, hx3, hrun4,
      hrun5', bne, hb6, hrun7, hrun8, hx8, Bool.not_false, Bool.not_true, eq_self, ite_true,
      ite_false, Bool.false_eq_true]
    rfl
  rw [ite_eq_right z8] at hw
  have hx8 := decW0B_true hd8 z8
  obtain ⟨r9, m9, x9, a9, hrun9, ⟨hS9, hg9, hl9, rfl⟩, hw⟩ :=
    (pinSlot_ref p hD.toDmProg6.toDmProg5.lPinAt 31 pinBoolFalse rfl).bind_ hS8 hw
  obtain ⟨r10, m10, x10, a10, hrun10, ⟨hS10, hg10, hd10⟩, hw⟩ :=
    (bct_ref hD.toDmProg6 (r9.headD 0)).bind_ ⟨hS9, hl9⟩ hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨x10, a10, ?_, hS10, hG8.trans (hg9.trans hg10), hd10⟩
  simp only [divModEnvGuard, boolTrueName, boolFalseName, StateT.run_bind, hrun1, exc_ok_bind', hx1, hrun2, hrun3, hx3, hrun4,
    hrun5', bne, hb6, hrun7, hrun8, hx8, hrun9, Bool.not_true, ite_false, Bool.false_eq_true]
  exact hrun10

@[refines ConRon.Arena.divModEnvGuard]
theorem divModEnvGuard_refines (hD : DmProg7 p) (hdn : DnInj dn) (c : Word) :
    RefAM p "div_mod_env_guard" [vis, c] (fun m s => StageR dn vis fe m s ∧ H c)
      (divModEnvGuard fe (decI c)) (KeepPost dn vis fe decW0B) :=
  (eg_ref hD hdn c).refAM

end envguard

end L.Ind
