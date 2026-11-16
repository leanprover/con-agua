module

public import ConAgua.Verdict.DivModPinE
import ConAgua.Arena.DeclNatGate
import ConAgua.Arena.DeclNatSubAll
public import ConAgua.Arena.DeclNatGateT
import ConAgua.Arena.RefWalk
import ConAgua.Arena.StageC
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.ModelGen
import ConRon.Bridge.Checker.DeclVal
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.DeclArmsNat
import ConAgua.Arena.IndSumSpec.ConsSumCtors

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

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Ind

open L.Arena
open L.Rom (PinSetsR PinSetR)
open ConRon.Bridge (CheckOK StepOK PinsDenote CoreStep)

local notation "V" => ConLeche.CheckMode.verified

/-- `subst_const0` at the walk fuel (`sc0_ref`; DeclCheckLoop's `substC0_of`, there commented out). -/
theorem substC0_ofN {p : Prog} (hN : NatSubProg p) (vis : Word) (fe : IFEnv) : SubstC0 p vis fe :=
  fun nm r h hn hr hh k m a res m' hS hc =>
    sc0_ref hN nm r coreWalkFuel 4000000000 rfl h k m a res m' hS hn hr hh hc

/-- **The model of `check_div_mod_pin_at_fe2`, both outcomes**: the environment guard and
`env_find` through their `Option` models. -/
l_model cdmpFe2_specE (p : Prog)
  (hf : p.lookup "check_div_mod_pin_at_fe2" = some checkDivModPinAtFe2L)
  fns [hf ↦ cdmpFe2E]
  specs [callW_spec p n "div_mod_env_guard", callW_spec p n "env_find"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- The pin gate's program facts beyond `DmProg10`: the gate's reads at the pushed view, the push
and the pop (`SnpProg`'s), the walk substitutions. -/
structure CdmpProg (p : Prog) : Prop extends DmProg10 p where
  fe2 : p.lookup "check_div_mod_pin_at_fe2" = some checkDivModPinAtFe2L
  snp : SnpProg p

/-- **The model of `check_div_mod_pin`, both outcomes**: the leaves through their `Option` models,
the reads at the pushed view and the variant loop through their models. -/
l_model cdmp_specE (p : Prog) (hD : CdmpProg p)
  fns [hD.lCheckDivModPin ↦ cdmpE]
  specs [callW_spec p n "env_row_get", callW_spec p n "env_push", cdmpFe2_specE p hD.fe2 n,
    callW_spec p n "env_pop_temp", callW_spec p n "env_set_flags", checkDivModPinLoop_specE p hD.toDmProg8 n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section cdmp
variable {p : Prog}

/-- **`check_div_mod_pin_at_fe2` refines `checkDivModPinAtFe2`, both outcomes**: the environment
guard (`divModEnvGuard_refines`) at the pushed view, then the stored definition's value word. -/
theorem cdmpFe2_ref (hD : DmProg7 p) (hcl : LeafClosed p) (hkp : CrKeep p) (hF2 : Fe2Closed p)
    {w n : Word} {fe2 : IFEnv} (k : Nat)
    {m : Mem} {a : AState} (hn : H n) (hS : StageR w fe2 m a) :
    RefE True (cdmpFe2E p k m w n) (checkDivModPinAtFe2 fe2 (decI n)) a
      (fun v x a' => SnpFe2Post w fe2 m v.2 v.1 x a' ∧ (L.Stubs.CrOK m → L.Stubs.CrOK v.2)) := by
  cases k with
  | zero => rw [cdmpFe2E.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  rw [cdmpFe2E.arm1]
  have hM := hD.toDmProg6.toDmProg5.toMasterProg
  simp only [checkDivModPinAtFe2]
  refine RefE.bindSim (fun _ => rfl)
    ((CallRef.of_refAM (divModEnvGuard_refines (vis := w) (fe := fe2) hD n)) k m a · · ⟨hS, hn⟩ ·)
    fun r1 x1 m1 a1 h1 hrun1 ⟨hS1, hg1, hd1⟩ => ?_
  have hfr := callW_leafFrame hcl (leaf_mem _ (by decide)) h1
  have hown := callW_fe2_ownC hF2 (by simp [fe2Fns]) h1
  refine RefE.ofArms (fun h => cdmpFe2E.k_div_mod_env_guard.abort1 _ _ _ _ _ _ h)
    (fun h => cdmpFe2E.k_div_mod_env_guard.arm1 _ _ _ _ _ _ h) (RefE.guardIf rfl (decW0B_false hd1)
      (fun h => Classical.byContradiction fun z => Bool.false_ne_true (h.symm.trans (decW0B_true hd1 z)))
      fun _ _ => ?_)
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r4 m4 h4 => ?_
  obtain ⟨hm4, hfd⟩ := envFind_call hM n hn hS1.check.env h4
  subst hm4
  cases hf : fe2.find? (decI n) with
  | none =>
    rw [hf] at hfd
    have hz : r4.headD 0 = 0 := hfd
    rw [cdmpFe2E.k_env_find.abort1 p _ _ hz]; exact RefE.of_cls0 rfl
  | some ci =>
  rw [hf] at hfd
  obtain ⟨hf1, hci⟩ := hfd
  have hnz : r4.headD 0 ≠ 0 := by rw [hf1]; decide
  by_cases hkk' : ¬ erRd m4 (r4.tail.headD 0) = 1
  · rw [cdmpFe2E.k_env_find.abort2 p _ _ hnz hkk']; exact RefE.of_cls0 rfl
  have hkk : erRd m4 (r4.tail.headD 0) = 1 := Classical.not_not.mp hkk'
  rw [cdmpFe2E.k_env_find.arm1 p _ _ hnz hkk]
  simp only [erRd_foldN]
  generalize r4.tail.headD 0 = q at hci hkk ⊢
  rcases decCI_defn_cases hci with ⟨cv, v, hint, rfl, -, -⟩ | ⟨w1, hw1, hne, -⟩
  rotate_left
  · exact absurd hkk (by rw [(erRd_of_erecP hw1).1]; exact hne)
  obtain ⟨wv, -, hk5, hwl, hwd⟩ := decCI_defn_val hci
  have e5 : erRd m4 (q + CI.defnValue) = wv := (erRdOK m4).at _ rfl hk5
  rw [e5]
  exact RefE.ret rfl ⟨⟨hS1, hg1, hwl, hwd, hfr, hown⟩, hkp.call (im_mem _ rfl) h1⟩

/-- **`check_div_mod_pin(po, pl, vis, p, n)` refines `checkDivModPin` under `StageC`, both
outcomes** (con-ron's `checkDivModPin_bridge`): the own row read, the push, the environment guard
and the stored value at the pushed view (`cdmpFe2_ref`), the pop (`pushPop_stage`), then the
variant loop (`loop_ref`) at `vis` over the ROM's variant records (the `IW` slice `po`, `pl` of
`rom_pin_sets()`, their twin denotations `PinsDenote`). -/
theorem cdmp_ref (hD : CdmpProg p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hkp : CrKeep p) (hcrf : L.Ind.CrfF p) {dn : NIdx → Option ConLeche.Name}
    {pins : List INatOpPinSet} {pinsP : List ConLeche.NatOpPinSet} {vis pw n po pl : Word}
    {fe : IFEnv} {env env2 : ConLeche.Env} {nm : ConLeche.Name} {ci : IConstantInfo} (k : Nat)
    (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState} (hn : H n) (hC : StageC dn vis fe env m a)
    (henv : ConLeche.EnvWF env) (hci : decCI (erecP m) pw.toNat = some ci)
    (hname : ci.name = decI n) (hok2 : StepOK env2 (fe.push ci) a)
    (hnm : denoteN a.store.ns (decI n) = some nm) (hI : PinsIW m po.toNat pl.toNat pins)
    (hPD : PinsDenote a.store pins pinsP) (hCr : L.Stubs.CrOK m) :
    RefE (CoreStubsE p) (cdmpE p k m po pl vis pw n) (checkDivModPin V pins fe ci (decI n)) a
      (fun v fe' a' => L.Arena.SnpPost dn vis fe env m v.2 v.1 fe' a a') := by
  cases k with
  | zero => rw [cdmpE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  rw [cdmpE.arm1]
  have hM := hD.toDmProg9.toDmProg8.toDmProg7.toDmProg6.toDmProg5.toMasterProg
  have hN : NatSubAllProg p := ⟨hD.snp.toNatSubProg'.toNatSubProg, hD.lSubstConstAll⟩
  have hsv := ConRon.Bridge.IFEnv.sameView_popTemp fe ci
  simp only [checkDivModPin]
  -- the own row the push displaces
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r1 m1 h1 => ?_
  obtain ⟨s1, hs1, hm1, -, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envRowGet_spec p hM.lEnvRowGet k _ n) h1
  have hm1' : m1 = m := by rw [← hs1, hm1]
  subst hm1'
  rw [cdmpE.k_env_row_get.arm1, hr1]
  simp only [List.headD_cons, List.tail_cons]
  -- the push
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r2 m2 h2 => ?_
  rw [cdmpE.k_env_push.arm1]
  obtain ⟨hS2, hg2⟩ := envPush_stage hD.snp.rs hD.snp.push h2 hC.stage hci
  have hf2 := callW_leafFrame hcl (leaf_mem _ (by decide)) h2
  -- the reads at the pushed view
  refine RefE.bindE (fun _ => rfl) (fun _ => trivial)
    (cdmpFe2_ref hD.toDmProg7 hcl hkp hD.snp.fe2 k hn hS2)
    fun ⟨v3, m3⟩ y3 a3 hrun3 ⟨hQ3, hcr3⟩ => ?_
  rw [cdmpE.k_check_div_mod_pin_at_fe2.arm1]
  dsimp only at hQ3 hcr3
  obtain ⟨hst3, hx3, hc3, hp3, -, cv', v', hint', -, hv3, hws⟩ :=
    ConRon.Bridge.checkDivModPinAtFe2_bridge hC.check.state hC.check.pins hok2 hnm hrun3
  -- the pop
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r4 m4 h4 => ?_
  rw [cdmpE.k_env_pop_temp.arm1]
  obtain ⟨hS4, hg4, hr4⟩ := pushPop_stage hD.snp.rs hD.snp.push hD.snp.pop hC.stage hci hname hn h2
    hQ3.stage (hg2.trans hQ3.grow) hQ3.own h4
  have hf4 := callW_leafFrame hcl (leaf_mem _ (by decide)) h4
  rw [hname] at hS4
  have hck4 : CheckOK false env ((fe.push ci).popTemp ci.name fe.idx[ci.name]?) a3 :=
    (hC.check.mono hst3 hx3 hc3 hp3).congr_find hsv.find hsv.tbls hsv.base
  rw [hname] at hck4 hsv
  have hf04 := (hf2.trans hQ3.frame).trans hf4
  have hC4 := StageC.of_frame hC hS4 hck4 hf04 hx3
  have hCr4 := hkp.call (im_mem _ rfl) h4 (hcr3 (hkp.call (im_mem _ rfl) h2 hCr))
  have hg04 : IWGrow m1 m4 := (hg2.trans hQ3.grow).trans hg4
  -- the variant loop
  rw [← hQ3.dec]
  refine RefE.bindE (fun _ => rfl) id
    (loop_ref hD.toDmProg8 hq hcl hkp hcrf (substC0_ofN hN.toNatSubProg _ _) (substCAll_of hN _ _)
      henv n v3 hn hQ3.hw hws pins pinsP po pl [] k hk' m4 a3 hC4 hCr4 (hI.grow hg04)
      (ConRon.Bridge.PinsDenote.mono hx3 _ _ hPD) (ConRon.Bridge.denoteN_ext hnm hx3)
      (by rw [hQ3.dec]; exact hv3))
    fun ⟨z5, m5⟩ u5 a5 hrun5 hQ5 => ?_
  rw [cdmpE.k_check_div_mod_pin_loop.arm1]
  dsimp only at hQ5
  rw [hr4] at hQ5 ⊢
  exact RefE.ret rfl ⟨hQ5.stage, hg04.trans hQ5.grow, hx3.trans hQ5.ext, rfl, hsv,
    by rw [hQ5.pins, hp3]⟩

end cdmp

end L.Ind
