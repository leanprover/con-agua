module

public import ConAgua.Arena.DeclAxQuotT
public import ConAgua.Arena.DeclDivGateT
import ConAgua.Arena.DeclArmT
import ConAgua.Arena.StageC
import ConAgua.Arena.RefWalk
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.DeclPins
import ConRon.Bridge.Checker.Arms
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.NatOpNames
public import ConAgua.Arena.DeclNatGateSpec
import all ConAgua.Arena.DeclArms
import ConAgua.Arena.DeclArmDefn

@[expose] public section

/-!
# The definition arm under `StageT` (lane `loopt3`, helper `loopt3-nat`)

`check_decl_defn`'s unified model and its refinement for both outcomes (`cdf_ref`), from `StageT`:
the constant check and the definition check (`ccv_ref`, `checkDefnVal_ref`), then the two gates
under `StageC` at the pre-insertion index: the structural-`Nat` gate (`snp_ref`,
`DeclNatGateT.lean`) and the `Nat.div`-family pin gate (`cdmp_ref`, `DeclDivGateT.lean`), each
handing back an index with `fe`'s view; the push last. The twin side is con-ron's
`checkDecl_bridge_defn`: `FoldOK` at the arm's entry carried across the constant check
(`checkConstantVal_bridge_of_fold`), the definition check (`checkDefnVal_bridge`, which gives the
pushed index's `StepOK`, what the gates read the stored value and guards through) and the
structural gate (`FoldOK.sameView`). The variant records (`PinSetsR`, carried by the callees'
write set `StepIn p defnCallFns`) and their twin denotations (`PinsDenote`, carried by `Ext`)
reach the pin gate.
-/

open ConRon.Arena
open ConLeche (IndWF CtorWF)
open Std.WP
open scoped Lean.Order


noncomputable section

namespace L.Arena

open L.Ind
open L.Rom (PinSetsR)
open L.Front (DECL DLP DeclsF)
open ConRon.Bridge (CheckOK StepOK FoldOK CoreSpec PinsDenote)

local notation "V" => ConLeche.CheckMode.verified

/-- `check_defn_val` is one of the loop's functions. -/
theorem checkDefnVal_loop : "check_defn_val" ∈ loopFns := loop_mem _ rfl

/-- The definition arm's callees up to the pin gate (their frames keep `PinSetsR`). -/
def defnCallFns : List FnName :=
  ["check_constant_val", "check_defn_val", "nat_op_names", "sl_contains",
    "check_structural_nat_pin", "nat_div_mod_names"]

/-- The definition arm's program facts under `StageT`: its text, the constant and value checks',
the structural gate's (`SnpProg`), the pin gate's (`CdmpProg`). -/
structure DefnProgT (p : Prog) : Prop where
  df : p.lookup "check_decl_defn" = some checkDeclDefn
  ccv : CcvProg p
  snp : SnpProg p
  dm : CdmpProg p
  /-- the arm's callees keep the memory outside a step's write set (the pin variants' header) -/
  step : StepIn p defnCallFns

set_option experimental.vcgen true in
/-- **The model of `check_decl_defn`, both outcomes**: `erec_ci` and the leaves through their runs,
the constant and value checks and the two gates through `callE` (read by their unified models'
specs in `cdf_ref`). -/
l_model checkDeclDefn_specE (p : Prog) (hX : DefnProgT p)
  fns [hX.df ↦ checkDeclDefnE]
  specs [erecCi_specW p hX.ccv.val.rcp n, callW_spec p n "nat_op_names",
    callW_spec p n "sl_contains", callW_spec p n "nat_div_mod_names",
    callW_spec p n "rom_pin_sets", callW_spec p n "env_push"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `StageT` across a leaf call that leaves the twin state alone (the stage relation after it given). -/
theorem StageT.of_leaf {p : Prog} (hcl : LeafClosed p) {f : FnName} (hf : f ∈ leafFns) {k : Nat}
    {args : List Word} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {r : List Word} (hc : callW p k f args m = some (r, m'))
    (hT : StageT dn vis fe m a) (hS : StageR vis fe m' a) : StageT dn vis fe m' a := by
  have hfr := callW_leafFrame hcl hf hc
  exact ⟨hS, hT.twin.frame hfr leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp leafA_hb leafC_hb,
    by simp only [pinW, hfr.arr PINS leafA_pins (by decide)]; exact hT.flag⟩

/-- **The definition arm refines `checkDeclKind`, both outcomes**, under `StageT` (con-ron's
`checkDecl_bridge_defn`'s decomposition): the record into `EREC` (`erec_ci(i, 1)`), the constant
check with a certified operation's name allowed (`ccv_ref`, `allow = 1`), the definition check
(`checkDefnVal_ref`), then at the pre-insertion index under `StageC` the structural-`Nat` gate
(`snp_ref`) for a `natOpNames` member and the pin gate (`cdmp_ref`) over the ROM's variants for a
`natDivModNames` member, each handing back an index with `fe`'s view; the push last. -/
theorem cdf_ref {p : Prog} (hX : DefnProgT p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p) {dn : NIdx → Option ConLeche.Name}
    (hC : CcvSims p dn) {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
    {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {i : Word} {ds : Array IDeclaration} {pins : List INatOpPinSet}
    {pinsP : List ConLeche.NatOpPinSet} {cv : IConstantVal} {v : EIdx}
    {hh : ConLeche.ReducibilityHint} {c : ConLeche.ConstantVal} {x : ConLeche.Expr}
    (hS : StageT dn vis fe m a) (hPS : PinSetsR m pins)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .defnDecl cv v hh) (hfold : FoldOK env fe a)
    (hcvd : Frontend.denoteCV a.store cv = some c) (hvd : denoteE a.store v = some x)
    (hPD : PinsDenote a.store pins pinsP) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkDeclDefnE p n m i vis) (checkDeclKind V pins fe (.defnDecl cv v hh)) a
      (fun w fe' a' => CdaPost dn m w.1 w.2 fe' a') := by
  have hfr : ∀ {k : Nat} {f : FnName} {args : List Word} {mx my : Mem} {rx : List Word},
      f ∈ defnCallFns → callW p k f args mx = some (rx, my) → MemFrame stepA stepC mx my := by
    intro k f args mx my rx hf hc
    obtain ⟨s', hs', hfr', -⟩ := triple_of_callW (s₀ := ⟨mx, Locals.init []⟩)
      (hX.step.memFrame k hf args ⟨mx, Locals.init []⟩) hc
    rw [← hs']; exact hfr'
  have hG := hX.snp.toNatSubProg'.toNatSubProg.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg
  cases n with
  | zero => rw [checkDeclDefnE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkDeclDefnE.eq_2]
  unfold checkDeclKind
  simp only []
  -- `erec_ci(i, 1)`
  refine RefE.onlySim (fun _ => checkDeclDefnE.k_erec_ci.none ..) (fun _ _ h => h) fun r1 m1 h1 => ?_
  rw [checkDeclDefnE.k_erec_ci.arm1]
  have hf1 := erecCiW_frame h1
  have hCr1 := CrOK.frame hCr hf1 (by decide) (by decide)
  obtain ⟨hT1, hg1, hci1, hcv1, hv1, -⟩ :=
    erecCiW_okT (ci := .defnInfo cv v hh) h1 hS hD hi (by rw [hd]; rfl)
  have hPS1 := L.Arena.PinSetsR.grow hPS (IWGrow.recGrow hg1) (hf1.ctl _ (by decide)) (hf1.ctl _ (by decide))
  rw [hd] at hcv1 hv1
  simp only [stepCV, stepVal] at hcv1 hv1
  generalize r1.headD 0 = q at hci1 hcv1 hv1 ⊢
  obtain ⟨wt, hwt, -, -⟩ := (decCV_words hcv1).2.2
  have hq1 : (q + CI.cv).toNat = q.toNat + CI.cv.toNat :=
    off_add_toNat rfl (by have := erecP_lt64 hwt; omega)
  have hcv1' : decCV (erecP m1) (q + CI.cv).toNat = some cv := by rw [hq1]; exact hcv1
  obtain ⟨wn, hwn, hwnl, hname⟩ := decCV_name hcv1
  have ewn : rdW (m1.arr64 (L.tierA EREC ((q + (CI.cv + CV.name)) >>> 40)))
      (q + (CI.cv + CV.name) &&& 1099511627775) = wn :=
    (erRdOK m1).at _ CI.cv_name_toNat hwn
  rw [ewn]
  -- the constant check, a certified operation's name allowed
  have hcc := ccv_ref hX.ccv hq hap hkp hcrf hC hn' hT1 hcv1'
    hcvd hCr1 (allow := 1)
  rw [show ((1 : Word) != 0) = true from rfl] at hcc
  refine RefE.bindRun (s₀ := ⟨m1, Locals.init []⟩)
    (fun _ => checkDeclDefnE.k_check_constant_val.none ..)
    (checkConstantVal_specE p hX.ccv n _ vis (q + CI.cv) 1) (fun hG => hG.nv) id hcc
    fun r3 s3 _ a3 h3 _ hrun3 hP3 => ?_
  rw [checkDeclDefnE.k_check_constant_val.arm1]
  dsimp only at hP3
  have h3w := callW_of_callE h3
  have hPS3 := L.Arena.PinSetsR.step hPS1 hP3.grow (hfr (by decide) h3w)
  obtain ⟨hstep1, F, hcF⟩ :=
    ConRon.Bridge.checkConstantVal_bridge_of_fold ConRon.Bridge.CoreSpec.of_core hfold hcvd hrun3
  have hok1 := hfold.ofCore hstep1
  have hg3 := hP3.grow
  have hcA := ConRon.Bridge.denoteCV_ext hcvd hstep1.ext
  have hv3 := ConRon.Bridge.denote_ext hvd hstep1.ext
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv1
  -- the definition check
  refine RefE.bindRun (s₀ := ⟨s3.mem, Locals.init []⟩)
    (fun _ => checkDeclDefnE.k_check_defn_val.none ..)
    (checkDefnVal_specE p hX.ccv.val n _ vis q) (fun _ => trivial) id
    (checkDefnVal_ref hX.ccv hq hap hkp hcrf hn' hP3.stage (ArrExt.decCV (L.Ind.IWGrow.ext hg3) hcv1)
      (hg3.ext _ _ hwv) hwvl ⟨_, hcA⟩ hP3.crOK)
    fun r4 s4 ci4 a4 h4 _ hrun4 ⟨hP4, hr4, hci4⟩ => ?_
  rw [checkDeclDefnE.k_check_defn_val.arm1]
  dsimp only at hr4 hP4
  subst hci4
  rw [hr4]
  have h4w := callW_of_callE h4
  have hPS4 := L.Arena.PinSetsR.step hPS3 hP4.grow (hfr (by decide) h4w)
  obtain ⟨hstep2, -, hciD, hcw2, hsh2, -⟩ := ConRon.Bridge.checkDefnVal_bridge
    ConRon.Bridge.CoreSpec.of_core hok1 hcA (ConRon.Bridge.checkConstantVal_typeWF hcF) hv3 hrun4
  have hok4 := hok1.ofCore hstep2
  have hnm4 : denoteN a4.store.ns (decI wn) = some c.name := by
    rw [← hname]
    exact ConRon.Bridge.denoteN_ext (ConRon.Bridge.denoteCV_inv hcA).1 hstep2.ext
  have hPD4 := ConRon.Bridge.PinsDenote.mono (hstep1.ext.trans hstep2.ext) _ _ hPD
  have hci4 : decCI (erecP s4.mem) q.toNat = some (.defnInfo cv (decI wv) hh) :=
    ArrExt.decCI (L.Ind.IWGrow.ext ((hg3.trans hP4.grow))) hci1
  have hCr4 := hP4.crOK
  have hgr4 : IWGrow m s4.mem := hg1.trans (hg3.trans hP4.grow)
  have hcin : (IConstantInfo.defnInfo cv (decI wv) hh).name = decI wn := hname
  rw [hname]
  generalize (IConstantInfo.defnInfo cv (decI wv) hh) = ci at hci4 hciD hcin ⊢
  have hT4 := hP4.stage
  -- after the structural gate: the pin gate, then the push
  have tail : ∀ (fe3 : IFEnv) (m7 : Mem) (a7 : AState), StageC dn vis fe3 env m7 a7 →
      ConRon.Bridge.IFEnv.SameView fe3 fe → ConRon.Bridge.CoreStep env fe a4 a7 →
      decCI (erecP m7) q.toNat = some ci → IWGrow m m7 → PinSetsR m7 pins → L.Stubs.CrOK m7 →
      RefE (VerdictCtxU p) (checkDeclDefnE.j1 p n q wn vis m7)
        (do
          let ds ← natDivModNames
          let fe ← if ds.contains (decI wn) = true then checkDivModPin V pins fe3 ci (decI wn)
            else pure fe3
          pure (fe.push ci)) a7 (fun w fe' a' => CdaPost dn m w.1 w.2 fe' a') := by
    intro fe3 m7 a7 hC7 hsv7 hstep7 hci7 hg7 hPS7 hCr7
    have hok7 : FoldOK env fe3 a7 := (hok4.ofCore hstep7).sameView hsv7
    have hx7 : Ext a4.store a7.store := hstep7.ext
    have hnm7 := ConRon.Bridge.denoteN_ext hnm4 hx7
    have hciD7 := ConRon.Bridge.denoteCI_ext hciD hx7
    have hPD7 := ConRon.Bridge.PinsDenote.mono hx7 _ _ hPD4
    have final : ∀ (fe4 : IFEnv) (m8 : Mem) (a8 : AState), StageC dn vis fe4 env m8 a8 →
        decCI (erecP m8) q.toNat = some ci → IWGrow m m8 →
        RefE (VerdictCtxU p) (checkDeclDefnE.j2 p n q vis m8) (pure (fe4.push ci)) a8
          (fun w fe' a' => CdaPost dn m w.1 w.2 fe' a') := by
      intro fe4 m8 a8 hC8 hci8 hg8
      rw [checkDeclDefnE.j2.arm1]
      refine RefE.onlySim (fun _ => checkDeclDefnE.k_env_push.none ..) (fun _ _ h => h)
        fun r9 m9 h9 => ?_
      rw [checkDeclDefnE.k_env_push.arm1]
      obtain ⟨hS9, hg9⟩ := push_call hX.ccv.val.rcp h9 hC8.stage hci8
      exact RefE.ret rfl ⟨hS9, leaf_memos hcl (leaf_mem _ rfl) h9 hC8.mem.memos, hg8.trans hg9⟩
    rw [checkDeclDefnE.j1.arm1]
    refine RefE.bindSim (fun _ => checkDeclDefnE.k_nat_div_mod_names.none ..)
      (natDivModNames_ref hG n m7 a7 · · hC7.stage ·) fun r5 ns m5 a5 h5 hrun5 ⟨hS5, hg5, hd5⟩ => ?_
    obtain ⟨rfl, -⟩ := ConRon.Bridge.natDivModNames_run hok7.check.pins hrun5
    rw [checkDeclDefnE.k_nat_div_mod_names.arm1]
    have hC5 := StageC.of_frame hC7 hS5 hC7.check (callW_leafFrame hcl (leaf_mem _ (by decide)) h5)
      (Ext.refl _)
    have hPS5 := L.Arena.PinSetsR.step hPS7 hg5 (hfr (by decide) h5)
    have hCr5 := hkp.call (im_mem _ rfl) h5 hCr7
    obtain ⟨hdl5, -⟩ := decRL0 hd5
    refine RefE.onlySim (fun _ => checkDeclDefnE.k_sl_contains_2.none ..)
      (Q := fun r m' => callW p n "sl_contains" [r5.headD 0, r5.tail.headD 0, wn] m5 = some (r, m'))
      (fun _ _ h => h) fun r6 m6 h6 => ?_
    obtain ⟨b6, a6, hrun6, hS6, hg6, hb6, -⟩ :=
      slContains_ref hG.lSlContains _ _ wn ns hwnl n m5 a5 r6 m6 ⟨hS5, hdl5⟩ h6
    obtain ⟨rfl, rfl⟩ : ns.contains (decI wn) = b6 ∧ a5 = a6 := by
      simpa [StateT.run, pure, StateT.pure, Except.pure] using hrun6
    have hC6 := StageC.of_frame hC5 hS6 hC5.check (callW_leafFrame hcl (leaf_mem _ (by decide)) h6)
      (Ext.refl _)
    have hPS6 := L.Arena.PinSetsR.step hPS5 hg6 (hfr (by decide) h6)
    have hCr6 := hkp.call (im_mem _ rfl) h6 hCr5
    have hg76 : IWGrow m7 m6 := hg5.trans hg6
    by_cases hb : r6.headD 0 = 0
    · have hno : ns.contains (decI wn) = false := by rw [← hb6, hb]; rfl
      rw [checkDeclDefnE.k_sl_contains_2.arm2 _ _ _ _ _ _ _ hb, hno]
      simp only [Bool.false_eq_true, ite_false, pure_bind]
      exact final fe3 m6 a5 hC6 (ArrExt.decCI (L.Ind.IWGrow.ext hg76) hci7) (hg7.trans hg76)
    have hyes : ns.contains (decI wn) = true := by
      rw [← hb6]; exact bne_iff_ne.mpr hb
    rw [checkDeclDefnE.k_sl_contains_2.arm1 _ _ _ _ _ _ _ hb, hyes]
    simp only [ite_true]
    refine RefE.onlySim (fun _ => checkDeclDefnE.k_rom_pin_sets.none ..)
      (Q := fun r m' => callW p n "rom_pin_sets" [] m6 = some (r, m')) (fun _ _ h => h)
      fun r0 m0 h0 => ?_
    rw [checkDeclDefnE.k_rom_pin_sets.arm1]
    obtain ⟨hS0, hg0, -, hI0⟩ := romPinSets_ref hX.dm.toDmProg10 hC6.stage hPS6 h0
    have hC0 := StageC.of_frame hC6 hS0 hC6.check (callW_leafFrame hcl (leaf_mem _ (by decide)) h0)
      (Ext.refl _)
    have hCr0 := hkp.call (im_mem _ rfl) h0 hCr6
    have hg70 : IWGrow m7 m0 := hg76.trans hg0
    have hok2 := hok7.toStepOK.push hok7.check.state hciD7 hsh2 hcw2
      (hr := ConLeche.RuleWF.of_not_rec (fun _ _ _ _ _ heq => nomatch heq))
    refine RefE.bindRun (s₀ := ⟨m0, Locals.init []⟩)
      (fun _ => checkDeclDefnE.k_check_div_mod_pin.none ..)
      (cdmp_specE p hX.dm n _ (r0.headD 0) (r0.tail.headD 0) vis q wn) (fun hG => hG.nv)
      (fun hG => hG.core)
      (cdmp_ref hX.dm hq hcl hkp hcrf n hn' hwnl hC0 hok7.envWF
        (ArrExt.decCI (L.Ind.IWGrow.ext hg70) hci7) hcin hok2 hnm7 hI0 hPD7 hCr0)
      fun r8 s8 fe8 a8 h8 _ hrun8 hQ8 => ?_
    rw [checkDeclDefnE.k_check_div_mod_pin.arm1]
    dsimp only at hQ8
    rw [hQ8.ret]
    exact final fe8 s8.mem a8 hQ8.stage
      (ArrExt.decCI (L.Ind.IWGrow.ext (hg70.trans hQ8.grow)) hci7) (hg7.trans (hg70.trans hQ8.grow))
  -- the structural gate's names
  refine RefE.bindSim (fun _ => checkDeclDefnE.k_nat_op_names.none ..)
    (natOpNames_ref hG n s4.mem a4 · · hT4.stage ·) fun r5 ns m5 a5 h5 hrun5 ⟨hS5, hg5, hd5⟩ => ?_
  obtain ⟨rfl, -⟩ := ConRon.Bridge.natOpNames_run hok4.check.pins hrun5
  rw [checkDeclDefnE.k_nat_op_names.arm1]
  have hT5 := StageT.of_leaf hcl (leaf_mem _ (by decide)) h5 hT4 hS5
  have hPS5 := L.Arena.PinSetsR.step hPS4 hg5 (hfr (by decide) h5)
  have hCr5 := hkp.call (im_mem _ rfl) h5 hCr4
  obtain ⟨hdl5, -⟩ := decRL0 hd5
  refine RefE.onlySim (fun _ => checkDeclDefnE.k_sl_contains.none ..)
    (Q := fun r m' => callW p n "sl_contains" [r5.headD 0, r5.tail.headD 0, wn] m5 = some (r, m'))
    (fun _ _ h => h) fun r6 m6 h6 => ?_
  obtain ⟨b6, a6, hrun6, hS6, hg6, hb6, -⟩ :=
    slContains_ref hG.lSlContains _ _ wn ns hwnl n m5 a5 r6 m6 ⟨hS5, hdl5⟩ h6
  obtain ⟨rfl, rfl⟩ : ns.contains (decI wn) = b6 ∧ a5 = a6 := by
    simpa [StateT.run, pure, StateT.pure, Except.pure] using hrun6
  have hT6 := StageT.of_leaf hcl (leaf_mem _ (by decide)) h6 hT5 hS6
  have hC6 := L.Ind.StageC.of_T hT6 hok4.check
  have hPS6 := L.Arena.PinSetsR.step hPS5 hg6 (hfr (by decide) h6)
  have hCr6 := hkp.call (im_mem _ rfl) h6 hCr5
  have hg46 : IWGrow s4.mem m6 := hg5.trans hg6
  have hci6 := ArrExt.decCI (L.Ind.IWGrow.ext hg46) hci4
  by_cases hb : r6.headD 0 = 0
  · have hno : ns.contains (decI wn) = false := by rw [← hb6, hb]; rfl
    rw [checkDeclDefnE.k_sl_contains.arm2 _ _ _ _ _ _ _ hb, hno]
    simp only [Bool.false_eq_true, ite_false, pure_bind]
    exact tail fe m6 a5 hC6 ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, id⟩
      (ConRon.Bridge.CoreStep.refl hok4.check) hci6 (hgr4.trans hg46) hPS6 hCr6
  have hyes : ns.contains (decI wn) = true := by rw [← hb6]; exact bne_iff_ne.mpr hb
  rw [checkDeclDefnE.k_sl_contains.arm1 _ _ _ _ _ _ _ hb, hyes]
  simp only [ite_true]
  have hok2 := hok4.toStepOK.push hok4.check.state hciD hsh2 hcw2
    (hr := ConLeche.RuleWF.of_not_rec (fun _ _ _ _ _ heq => nomatch heq))
  refine RefE.bindRun (s₀ := ⟨m6, Locals.init []⟩)
    (fun _ => checkDeclDefnE.k_check_structural_nat_pin.none ..)
    (snp_specE p hX.snp.snp hX.snp.snpFe2 hX.snp.lNatCertify n _ vis q wn) (fun hG => hG.nv)
    (fun hG => hG.core)
    (snp_ref hX.snp hq hcl n hn' hwnl hC6 hok4.envWF hci6 hcin hok2 hnm4)
    fun r7 s7 fe7 a7 h7 _ hrun7 hQ7 => ?_
  rw [checkDeclDefnE.k_check_structural_nat_pin.arm1]
  dsimp only at hQ7
  rw [hQ7.ret]
  have h7w := callW_of_callE h7
  have hg67 : IWGrow m6 s7.mem := hQ7.grow
  exact tail fe7 s7.mem a7 hQ7.stage hQ7.same
    ⟨hQ7.stage.check.congr_find (fun k => (hQ7.same.find k).symm) hQ7.same.tbls.symm
      hQ7.same.base.symm hok4.check.ienv.flags, hQ7.ext, hQ7.pins⟩
    (ArrExt.decCI (L.Ind.IWGrow.ext hg67) hci6) ((hgr4.trans hg46).trans hg67)
    (L.Arena.PinSetsR.step hPS6 hg67 (hfr (by decide) h7w)) (hkp.call (im_mem _ rfl) h7w hCr6)

end L.Arena
