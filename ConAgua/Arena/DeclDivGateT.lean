module

public import ConAgua.Verdict.DivModPinE
public import ConAgua.Arena.DeclArmDefn

@[expose] public section

/-!
# The `Nat.div`-family pin gate under `StageC` (lane `loopt3`, helper `loopt3-div`)

`defn_div_gate` runs after the definition arm's push, at the pre-insertion view `vis` for its core
calls and at the pushed view `w` for the environment guard, under `StageC` (`TwinStep.lean`),
mirroring con-ron's `checkDivModPin_bridge` (`Bridge/Checker/DivMod.lean`), as `crp_ref`
(`DeclCrpT.lean`) does for the reduce-pin gate. One model and one refinement for both outcomes
(`dg_ref`): the leaves (`nat_div_mod_names`, `sl_contains`, `rom_pin_sets`) lifted, by their
`StageR` refinements and the leaves' write set (`LeafClosed`); the gate `check_div_mod_pin` by
`cp_ref` (`Verdict/DivModPinE.lean`; parts 1 and 2, `DeclDivGateT1.lean`, `DeclDivGateT2.lean`,
carry the guards and the attempt). The definition arm (`cdf_ref`) consumes the halves from the
call's run: `DivGateSpecC` (with the variant records after and the frame) and `DivGateSpecE`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Ind

open L.Arena
open L.Rom (PinSetsR PinSetR)
open ConRon.Bridge (CheckOK StepOK PinsDenote CoreStep)

local notation "V" => ConLeche.CheckMode.verified

/-- **`defn_div_gate(vis, w, n)` under `StageC`**: from the stage relation at the pushed view `w`
(extended index `fe2`), `StageC` at the pre-insertion view `vis` (con-ron's `CheckOK` at the
environment `env` before the push), `env`'s well-formedness, the pushed index's `StepOK` (at
`env2`), the variant records in memory (`PinSetsR`) and in the twin's store (`PinsDenote`, from
`TwinFold.pinsD` and `Ext` since), the name's denotation; the gate's run, the stage relation at `w`,
`StageC` at `vis`, `Ext` of the twin's store, and the frame. -/
def DivGateSpecC (p : Prog) (pins : List INatOpPinSet) : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name), DnInj dn → ∀ (vis w : Word) (fe2 : IFEnv)
    (env env2 : ConLeche.Env) (n : Word) (nm : ConLeche.Name) (k : Nat), k ≤ 2 ^ 62 →
    ∀ (m m' : Mem) (a : AState) (r : List Word), n.toNat < 2 ^ 32 →
    callW p k "defn_div_gate" [vis, w, n] m = some (r, m') →
    StageR dn w fe2 m a → StageC dn vis (fe2.restrictTo vis.toNat) env m a →
    ConLeche.EnvWF env → StepOK env2 fe2 a → PinSetsR m pins →
    (∃ pinsP, PinsDenote a.store pins pinsP) →
    denoteN a.store.ns (decI n) = some nm → L.Stubs.CrOK m →
    ∃ a', (divGateT pins (fe2.restrictTo vis.toNat) fe2 (decI n)).run a = .ok ((), a') ∧
      StageR dn w fe2 m' a' ∧ StageC dn vis (fe2.restrictTo vis.toNat) env m' a' ∧
      Ext a.store a'.store ∧ IWGrow m m' ∧ PinSetsR m' pins ∧ MemFrame stepA stepC m m'

/-- **`defn_div_gate`'s error claim under `StageC`** (the error half of `DivGateSpecC`). -/
def DivGateSpecE (p : Prog) (pins : List INatOpPinSet) : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name), DnInj dn → ∀ (vis w : Word) (fe2 : IFEnv)
    (env env2 : ConLeche.Env) (n : Word) (nm : ConLeche.Name) (k : Nat), k ≤ 2 ^ 62 →
    ∀ (m : Mem) (a : AState), n.toNat < 2 ^ 32 →
    StageR dn w fe2 m a → StageC dn vis (fe2.restrictTo vis.toNat) env m a →
    ConLeche.EnvWF env → StepOK env2 fe2 a → PinSetsR m pins →
    (∃ pinsP, PinsDenote a.store pins pinsP) →
    denoteN a.store.ns (decI n) = some nm → L.Stubs.CrOK m →
    ∀ e, callE p k "defn_div_gate" [vis, w, n] m = .error e →
    ErrClaim (divGateT pins (fe2.restrictTo vis.toNat) fe2 (decI n)) a e

set_option experimental.vcgen true in
/-- **The model of `defn_div_gate`, both outcomes**: the family's names, the membership and the
variant records (outside the verdict closure) lifted, `check_div_mod_pin` by its model. -/
l_model defnDivGate_specE (p : Prog) (hD : DmProg10 p)
  fns [hD.lDefnDivGate ↦ defnDivGateE]
  specs [callW_spec p n "nat_div_mod_names", callW_spec p n "sl_contains",
    callW_spec p n "rom_pin_sets", checkDivModPin_specE p hD.toDmProg8 n]
  grind [arena_grind] extra [ld64_rdW_specE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What the pin gate gives besides the twin's run (from `m`, `a`): the stage relation at the
pushed view `w`, `StageC` at the pre-insertion view `vis`, `Ext` of the twin's store, the growth.
(The variant records after and the frame come from the call's run: `divGateSpecC`.) -/
structure DgPost (dn : NIdx → Option ConLeche.Name) (vis w : Word) (fe2 : IFEnv)
    (env : ConLeche.Env) (m : Mem) (a : AState) (m' : Mem) (a' : AState) : Prop where
  stageW : StageR dn w fe2 m' a'
  stage : StageC dn vis (fe2.restrictTo vis.toNat) env m' a'
  ext : Ext a.store a'.store
  grow : IWGrow m m'

/-- **`defn_div_gate(vis, w, n)` refines `divGateT` under `StageC`, both outcomes**: from the stage
relation at the pushed view `w` (extended index `fe2`), `StageC` at the pre-insertion view `vis`
(con-ron's `CheckOK` at the environment `env` before the push), `env`'s well-formedness, the pushed
index's `StepOK` (at `env2`), the variant records in memory (`PinSetsR`) and in the twin's store
(`PinsDenote`), the name's denotation: the family's names, the membership, the variant records,
the gate (`cp_ref`). -/
theorem dg_ref {p : Prog} (hD : DmProg10 p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hCl : StepIn p dgFns) (hs0 : ∀ dn vis fe, SubstC0 p dn vis fe)
    (hsA : ∀ dn vis fe, SubstCAll p dn vis fe) (hkp : CrKeep p) {pins : List INatOpPinSet}
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis w : Word} {fe2 : IFEnv}
    {env env2 : ConLeche.Env} {n : Word} {nm : ConLeche.Name} {k : Nat} (hk : k ≤ 2 ^ 62)
    {m : Mem} {a : AState} (hn : n.toNat < 2 ^ 32) (hS : StageR dn w fe2 m a)
    (hC : StageC dn vis (fe2.restrictTo vis.toNat) env m a) (henv : ConLeche.EnvWF env)
    (hok2 : StepOK env2 fe2 a) (hP : PinSetsR m pins) (hpd : ∃ pinsP, PinsDenote a.store pins pinsP)
    (hnm : denoteN a.store.ns (decI n) = some nm) (hCr : L.Stubs.CrOK m) :
    RefE (CoreStubsE p) (defnDivGateE p k m vis w n)
      (divGateT pins (fe2.restrictTo vis.toNat) fe2 (decI n)) a
      (fun x _ a' => DgPost dn vis w fe2 env m a x.2 a') := by
  obtain ⟨psPs, hpd⟩ := hpd
  cases k with
  | zero => rw [defnDivGateE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  rw [defnDivGateE.arm1]
  have hfrOf : ∀ {k : Nat} {f : FnName} {args : List Word} {mx my : Mem} {rx : List Word},
      f ∈ dgFns → callW p k f args mx = some (rx, my) → MemFrame stepA stepC mx my := by
    intro k f args mx my rx hf hc
    obtain ⟨s', hs', hfr', -⟩ := triple_of_callW (s₀ := ⟨mx, Locals.init []⟩)
      (hCl.memFrame k hf args ⟨mx, Locals.init []⟩) hc
    rw [← hs']; exact hfr'
  have hN : NatGateProg p := hD.toDmProg9.toDmProg8.toDmProg7.toDmProg6.toDmProg5.toDmProg2.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg
  unfold divGateT
  -- the family's names
  rcases h1 : callW p k "nat_div_mod_names" [] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, defnDivGateE.k_nat_div_mod_names.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, defnDivGateE.k_nat_div_mod_names.arm1]
  obtain ⟨x1, a1, hrun1, hS1, hg1, hd1⟩ :=
    natDivModNames_ref hN (vis := w) (fe := fe2) (dn := dn) k m a r1 m1 hS h1
  obtain ⟨e1, -⟩ := ConRon.Bridge.natDivModNames_run hC.check.pins hrun1
  rw [e1] at hrun1 hS1
  have hC1 := StageC.of_core hC (hS1.restrict vis) (callW_leafFrame hcl (leaf_mem _ (by decide)) h1)
    (CoreStep.refl hC.check)
  have hP1 := PinSetsR.step hP hg1 (hfrOf (by simp [dgFns]) h1)
  unfold decRL at hd1
  simp only [Nat.zero_add, ntGetD0, ntGetD1] at hd1
  have hrun1' : natDivModNames.run a = .ok (x1, a) := hrun1
  refine RefE.bind_right hrun1' ?_
  -- the membership
  refine RefE.onlySim (fun _ => defnDivGateE.k_sl_contains.none ..) (fun _ _ h => h) fun r2 m2 h2 => ?_
  have hCr2 := hkp.call (im_mem _ rfl) h2 (hkp.call (im_mem _ rfl) h1 hCr)
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := slContains_ref hN.lSlContains (vis := w) (fe := fe2)
    (dn := dn) (r1.headD 0) (r1.tail.headD 0) n x1 (by exact_mod_cast hn) k m1 a r2 m2 ⟨hS1, hd1.1⟩ h2
  have hP2 := PinSetsR.step hP1 hg2 (hfrOf (by simp [dgFns]) h2)
  have hrun2' : (pure (x1.contains (decI n)) : AM Bool).run a = .ok (x2, a2) := hrun2
  obtain ⟨hx2e, hxa⟩ := pure_run_eq hrun2'
  rw [hxa] at hS2
  have hC2 := StageC.of_core hC1 (hS2.restrict vis) (callW_leafFrame hcl (leaf_mem _ (by decide)) h2)
    (CoreStep.refl hC1.check)
  have hG2 : IWGrow m m2 := hg1.trans hg2
  rw [defnDivGateE.k_sl_contains.eq_2, ite_not]
  refine RefE.retIf (fun z2 => by rw [← hx2e]; exact decW0B_false hd2 z2) (fun hb => by rw [← hx2e, ← hd2.1] at hb; simpa using hb)
    (fun _ => ⟨hS2, hC2, Ext.refl _, hG2⟩) fun _ _ => ?_
  -- the variant records
  refine RefE.onlySim (fun _ => defnDivGateE.k_rom_pin_sets.none ..) (fun _ _ h => h) fun r3 m3 h3 => ?_
  rw [defnDivGateE.k_rom_pin_sets.arm1]
  obtain ⟨hS3, hg3, hP3, hI3⟩ := romPinSets_ref hD hS2 hP2 h3
  have hC3 := StageC.of_core hC2 (hS3.restrict vis)
    (callW_leafFrame hcl (leaf_mem _ (by decide)) h3) (CoreStep.refl hC2.check)
  -- the gate
  exact RefE.lastE (f := fun v => (0, v.2)) (fun _ => defnDivGateE.k_check_div_mod_pin.none ..)
    (fun _ => by rw [defnDivGateE.k_check_div_mod_pin.arm1, defnDivGateE.j1.arm1]) id
    (cp_ref hD.toDmProg8 hq hcl hkp hdn (hs0 dn vis _) (hsA dn vis _) henv hk' hS3 hC3 hok2
      (by exact_mod_cast hn) hI3 hpd hnm (hkp.call (im_mem _ rfl) h3 hCr2))
    fun _ _ _ _ hR4 => ⟨hR4.stageW, hR4.stage, hR4.core.ext, hG2.trans (hg3.trans hR4.grow)⟩

/-- **`defn_div_gate` under `StageC`** from the call's run (`dg_ref`'s ok half; the variant records
after and the frame from the gate's write set). -/
theorem divGateSpecC {p : Prog} (hD : DmProg10 p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hCl : StepIn p dgFns) (hs0 : ∀ dn vis fe, SubstC0 p dn vis fe)
    (hsA : ∀ dn vis fe, SubstCAll p dn vis fe) (hkp : CrKeep p) (pins : List INatOpPinSet) :
    DivGateSpecC p pins := by
  intro dn hdn vis w fe2 env env2 n nm k hk m m' a r hn hcall hS hC henv hok2 hP hpd hnm hCr
  obtain ⟨s', hs', -, _, a', hrun, hR⟩ := RefE.run_okW (s₀ := ⟨m, Locals.init []⟩)
    (defnDivGate_specE p hD k _ vis w n)
    (dg_ref hD hq hcl hCl hs0 hsA hkp hdn hk hn hS hC henv hok2 hP hpd hnm hCr) hcall
  subst hs'
  obtain ⟨s'', hs'', hfr, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (hCl.memFrame k (f := "defn_div_gate") (by simp [dgFns]) [vis, w, n] ⟨m, Locals.init []⟩) hcall
  rw [hs''] at hfr
  exact ⟨a', hrun, hR.stageW, hR.stage, hR.ext, hR.grow, PinSetsR.step hP hR.grow hfr, hfr⟩

/-- **`defn_div_gate`'s error claim under `StageC`** (`dg_ref`'s error half). -/
theorem divGateSpecE_of {p : Prog} (hD : DmProg10 p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hCl : StepIn p dgFns) (hs0 : ∀ dn vis fe, SubstC0 p dn vis fe)
    (hsA : ∀ dn vis fe, SubstCAll p dn vis fe) (hkp : CrKeep p) (hcE : CoreStubsE p)
    (hnv : closedNV p L.Checker.nvFns = true) (pins : List INatOpPinSet) :
    DivGateSpecE p pins :=
  fun _ hdn vis w _ _ _ n _ k hk m _ hn hS hC henv hok2 hP hpd hnm hCr _ hce =>
    RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (defnDivGate_specE p hD k _ vis w n) hnv hcE
      (dg_ref hD hq hcl hCl hs0 hsA hkp hdn hk hn hS hC henv hok2 hP hpd hnm hCr) hce

end L.Ind
