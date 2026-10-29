import ConAgua.Arena.DeclDivGateT2
import ConAgua.L.ModelGen

/-!
# The `Nat.div` family's variant loop and gate: `check_div_mod_pin_loop`, `check_div_mod_pin`

One model (`l_model … unified`) and one refinement for both outcomes each, under `StageC`
(con-ron's `checkDivModPinLoop_bridge`, `checkDivModPin_bridge`): the loop over the variant records
(`loop_ref`; the guards lifted, the attempt by `cpa_ref`), the gate (`cp_ref`; the environment
guard and `env_find` lifted, the loop by `loop_ref`). Their errors claim from the core stubs'
(`CoreStubsE`). The pin gate `defn_div_gate` (`DeclDivGateT.lean`) reads `cp_ref`.
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

/-- **The model of `check_div_mod_pin_loop`, both outcomes**: the two guards (outside the verdict
closure) lifted, `check_div_mod_pin_at` by its model. -/
l_model checkDivModPinLoop_specE (p : Prog) (hD : DmProg8 p)
  fns [hD.lCheckDivModPinLoop ↦ checkDivModPinLoopE]
  specs [callW_spec p n "div_mod_pin_guard", callW_spec p n "div_mod_certs_guard",
    checkDivModPinAt_specE p hD.lCheckDivModPinAt hD.lCheckTypePins hD.lCheckDivModPinValue
      hD.lCheckDivModCerts n]
  grind [arena_grind] extra [ld64_rdW_specE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What the variant loop and the gate give besides the twin's run (from `m`, `a`): `StageC`
after, the twin's core step, the growth. -/
structure PinPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (env : ConLeche.Env) (m : Mem) (a : AState) (m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  core : CoreStep V env fe a a'
  grow : IWGrow m m'

section loop
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_div_mod_pin_loop` refines `checkDivModPinLoop` under `StageC`, both outcomes**
(con-ron's `checkDivModPinLoop_bridge`): the pin guard (`pgC`), on `true` the certificates' guard
(`cgsC`), on `true` the attempt (`cpa_ref`); every other outcome moves on to the next variant; no
variant left is the twin's `fail`. -/
theorem loop_ref (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    (c value : Word) (hc : H c) (hval : H value) {nm : ConLeche.Name} {v : ConLeche.Expr}
    (hwsv : ConLeche.Expr.WScoped 0 v) :
    ∀ (ips : List INatOpPinSet) (psPs : List ConLeche.NatOpPinSet) (po pl : Word)
      (tried : List String) (k : Nat), k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState),
      StageC dn vis fe env m a → L.Stubs.CrOK m → PinsIW m po.toNat pl.toNat ips →
      PinsDenote a.store ips psPs → denoteN a.store.ns (decI c) = some nm →
      denoteE a.store (decE value) = some v →
      RefE (CoreStubsE p) (checkDivModPinLoopE p k m vis c value po pl)
        (checkDivModPinLoop V fe (decI c) (decE value) ips tried) a
        (fun w _ a' => PinPost dn vis fe env m a w.2 a') := by
  intro ips
  induction ips with
  | nil =>
    intro psPs po pl tried k hk m a hC _ hI hpd hn hv
    have hpl : pl = 0 := UInt64.toNat_inj.mp (by have := hI.2.1; simpa using this)
    cases k with
    | zero => rw [checkDivModPinLoopE.eq_1]; exact RefE.of_cls0 (by simp)
    | succ k =>
      rw [checkDivModPinLoopE.abort1 p k m vis c value po pl hpl]
      exact fun _ => ErrClaim.fail _ (.notImplemented _) rfl
  | cons ip rest ih =>
    intro psPs po pl tried k hk m a hC hCr hI hpd hn hv
    cases psPs with
    | nil => exact hpd.elim
    | cons psP restP =>
    obtain ⟨hq0, hrestP⟩ := hpd
    cases k with
    | zero => rw [checkDivModPinLoopE.eq_1]; exact RefE.of_cls0 (by simp)
    | succ k =>
    have hk' : k ≤ 2 ^ 62 := by omega
    have hS := hC.stage
    have hsz := hS.iw.iwSize
    have hI1 := hS.iw.iw
    obtain ⟨hb, hl, hj⟩ := hI
    have hpl0 : pl ≠ 0 := fun e => by rw [e] at hl; simp at hl
    rw [checkDivModPinLoopE.arm1 p k m vis c value po pl hpl0]
    obtain ⟨ps, hps, hP⟩ := hj 0 (by simp)
    replace hP : PinSetR m ps ip := by simpa using hP
    have hpsw : rdW (m.arr64 IW) po = ps := rdW_iw_of (by simpa using hps) rfl
    have hlpos : 0 < pl.toNat :=
      Nat.pos_of_ne_zero (fun e' => hpl0 (UInt64.toNat_inj.mp (by simpa using e')))
    have hpo1 : (po + 1).toNat = po.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hpl1 : (pl - 1).toNat = pl.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have hrestI : ∀ m2, IWGrow m m2 → PinsIW m2 (po + 1).toNat (pl - 1).toNat rest := by
      intro m2 hg
      have h0 : PinsIW m (po + 1).toNat (pl - 1).toNat rest := by
        rw [hpo1, hpl1]
        refine ⟨by simp at hl; omega, by simp at hl; omega, fun j hj' => ?_⟩
        obtain ⟨ps2, hp2, hP2⟩ := hj (j + 1) (by simpa using hj')
        exact ⟨ps2, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hp2, by simpa using hP2⟩
      exact h0.grow hg
    rw [hpsw]
    -- the next variant, from a state a declined variant left
    have next : ∀ (m2 : Mem) (a2 : AState) (tr : List String),
        StageC dn vis fe env m2 a2 → L.Stubs.CrOK m2 → IWGrow m m2 → CoreStep V env fe a a2 →
        RefE (CoreStubsE p) (checkDivModPinLoopE.j1 p k vis c value po pl m2)
          (checkDivModPinLoop V fe (decI c) (decE value) rest tr) a2
          (fun w _ a' => PinPost dn vis fe env m a w.2 a') := by
      intro m2 a2 tr hC2 hCr2 hG2 c02
      rw [checkDivModPinLoopE.j1.arm1]
      exact (ih restP (po + 1) (pl - 1) tr k hk' m2 a2 hC2 hCr2 (hrestI m2 hG2)
        (ConRon.Bridge.PinsDenote.mono c02.ext _ _ hrestP) (ConRon.Bridge.denoteN_ext hn c02.ext)
        (ConRon.Bridge.denote_ext hv c02.ext)).mono
        fun _ _ _ hR => ⟨hR.stage, c02.trans hR.core, hG2.trans hR.grow⟩
    -- the pin guard
    rcases h1 : callW p k "div_mod_pin_guard" [ps, vis, c] m with _ | ⟨r1, m1⟩
    · rw [liftE_none, checkDivModPinLoopE.k_div_mod_pin_guard.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]
    obtain ⟨x1, a1, hrun1, hC1, c1, hg1, hd1, hx1v⟩ :=
      pgC hD.toDmProg7.toDmProg6 hcl hkp h1 hC hc hP hq0 hn hCr
    have hCr1 := hkp.call (im_mem _ rfl) h1 hCr
    have hrun1' : (divModPinGuard ip fe (decI c)).run a = .ok (x1, a1) := hrun1
    refine RefE.bind_right hrun1' ?_
    by_cases z1 : r1.headD 0 = 0
    · rw [checkDivModPinLoopE.k_div_mod_pin_guard.arm2 _ _ _ _ _ _ _ _ _ _ z1, decW0B_false hd1 z1]
      exact RefE.ite_neg (by simp) (next m1 a1 _ hC1 hCr1 hg1 c1)
    rw [checkDivModPinLoopE.k_div_mod_pin_guard.arm1 _ _ _ _ _ _ _ _ _ _ z1]
    have hx1 := decW0B_true hd1 z1
    rw [hx1]
    refine RefE.ite_pos rfl ?_
    -- the certificates' guards
    have hq1 := (ConRon.Bridge.PinsDenote.mono c1.ext [ip] [psP] ⟨hq0, trivial⟩).1
    rcases h2 : callW p k "div_mod_certs_guard" [ps, vis, c, value] m1 with _ | ⟨r2, m2⟩
    · rw [liftE_none, checkDivModPinLoopE.k_div_mod_certs_guard.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]
    obtain ⟨x2, a2, hrun2, hC2, c2, hg2, hd2⟩ :=
      cgsC hD.toDmProg7.toDmProg6 hcl hkp hs0 hsA h2 hC1 hc hval (PinSetR.grow hP hg1) hq1
        (ConRon.Bridge.denoteN_ext hn c1.ext) (ConRon.Bridge.denote_ext hv c1.ext) hCr1
    have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
    have hG2 : IWGrow m m2 := hg1.trans hg2
    have c02 := c1.trans c2
    have hrun2' : (divModCertsGuard ip fe (decI c) (decE value)).run a1 = .ok (x2, a2) := hrun2
    refine RefE.bind_right hrun2' ?_
    by_cases z2 : r2.headD 0 = 0
    · rw [checkDivModPinLoopE.k_div_mod_certs_guard.arm2 _ _ _ _ _ _ _ _ _ _ z2, decW0B_false hd2 z2]
      exact RefE.ite_neg (by simp) (next m2 a2 _ hC2 hCr2 hG2 c02)
    rw [checkDivModPinLoopE.k_div_mod_certs_guard.arm1 _ _ _ _ _ _ _ _ _ _ z2, decW0B_true hd2 z2]
    refine RefE.ite_pos rfl ?_
    -- the attempt
    have h3R := cpa_ref hD hq hcl hkp hs0 hsA henv hk' hC2 hc hval (PinSetR.grow hP hG2)
      (ConRon.Bridge.PinsDenote.mono c02.ext [ip] [psP] ⟨hq0, trivial⟩).1
      (ConRon.Bridge.denoteN_ext hn c02.ext) (ConRon.Bridge.denote_ext hv c02.ext) hwsv
      (by rw [← hx1v, hx1]) hCr2
    rcases e3 : checkDivModPinAtE p k m2 vis c value ps with e3 | ⟨r3, m3⟩
    · rw [e3] at h3R
      rw [checkDivModPinLoopE.k_check_div_mod_pin_at.none]
      exact RefE.bind_left h3R
    rw [e3] at h3R
    obtain ⟨x3, a3, hrun3, hR3⟩ := h3R
    refine RefE.bind_right hrun3 ?_
    by_cases z3 : r3 ≠ 0
    · rw [checkDivModPinLoopE.k_check_div_mod_pin_at.arm1 _ _ _ _ _ _ _ _ _ z3,
        decW0B_true hR3.res (by simpa using z3)]
      exact RefE.ite_pos rfl (RefE.ret rfl ⟨hR3.stage, c02.trans hR3.core, hG2.trans hR3.grow⟩)
    have z3' : r3 = 0 := by simpa using z3
    rw [checkDivModPinLoopE.k_check_div_mod_pin_at.arm2 _ _ _ _ _ _ _ _ _ z3',
      decW0B_false hR3.res (by simpa using z3')]
    exact RefE.ite_neg (by simp) (next m3 a3 _ hR3.stage hR3.cr (hG2.trans hR3.grow) (c02.trans hR3.core))

end loop

/-- **The model of `check_div_mod_pin`, both outcomes**: the environment guard and `env_find`
(outside the verdict closure) lifted, the variant loop by its model. -/
l_model checkDivModPin_specE (p : Prog) (hD : DmProg8 p)
  fns [hD.lCheckDivModPin ↦ checkDivModPinE]
  specs [callW_spec p n "div_mod_env_guard", callW_spec p n "env_find",
    checkDivModPinLoop_specE p hD n]
  grind [arena_grind] extra [ld64_rdW_specE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What the gate gives besides the twin's run: `PinPost` at the pre-insertion view, and the
stage relation at the extended view `vis2`. -/
structure CpPost (dn : NIdx → Option ConLeche.Name) (vis vis2 : Word) (fe2 : IFEnv)
    (env : ConLeche.Env) (m : Mem) (a : AState) (m' : Mem) (a' : AState) : Prop
    extends PinPost dn vis (fe2.restrictTo vis.toNat) env m a m' a' where
  stageW : StageR dn vis2 fe2 m' a'

section pin
variable {p : Prog}

/-- **`check_div_mod_pin` refines `checkDivModPin` under `StageC`, both outcomes** (con-ron's
`checkDivModPin_bridge`): the environment guard at the extended view `vis2` (`StepOK`), the stored
value's lookup, the variant loop at the pre-insertion view `vis` (`loop_ref`). -/
theorem cp_ref (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis vis2 : Word} {fe2 : IFEnv}
    {env env2 : ConLeche.Env}
    (hs0 : SubstC0 p dn vis (fe2.restrictTo vis.toNat))
    (hsA : SubstCAll p dn vis (fe2.restrictTo vis.toNat)) (henv : ConLeche.EnvWF env)
    {po pl c : Word} {ips : List INatOpPinSet} {psPs : List ConLeche.NatOpPinSet}
    {nm : ConLeche.Name} {k : Nat} (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hS : StageR dn vis2 fe2 m a) (hC : StageC dn vis (fe2.restrictTo vis.toNat) env m a)
    (hok2 : StepOK env2 fe2 a) (hc : H c) (hI : PinsIW m po.toNat pl.toNat ips)
    (hpd : PinsDenote a.store ips psPs) (hn : denoteN a.store.ns (decI c) = some nm)
    (hCr : L.Stubs.CrOK m) :
    RefE (CoreStubsE p) (checkDivModPinE p k m po pl vis vis2 c)
      (checkDivModPin V ips (fe2.restrictTo vis.toNat) fe2 (decI c)) a
      (fun w _ a' => CpPost dn vis vis2 fe2 env m a w.2 a') := by
  cases k with
  | zero => rw [checkDivModPinE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  rw [checkDivModPinE.arm1]
  have hD7 := hD.toDmProg7
  -- the environment guard, at the extended view
  rcases h1 : callW p k "div_mod_env_guard" [vis2, c] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, checkDivModPinE.k_div_mod_env_guard.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨x1, a1, hrun1, ⟨hS1, hg1, hd1⟩⟩ := (eg_ref hD7 hdn c) k m a r1 m1 ⟨hS, hc⟩ h1
  obtain ⟨hst1, hx1, hc1, hp1, hgv⟩ :=
    ConRon.Bridge.divModEnvGuard_run hC.check.state hC.check.pins hok2.ienv hn hrun1
  have c1 : CoreStep V env (fe2.restrictTo vis.toNat) a a1 :=
    ⟨hC.check.mono hst1 hx1 hc1 hp1, hx1, hp1⟩
  have hC1 := StageC.of_core hC (hS1.restrict vis)
    (callW_leafFrame hcl (leaf_mem _ (by decide)) h1) c1
  have hCr1 := hkp.call (im_mem _ rfl) h1 hCr
  unfold checkDivModPin
  by_cases z1 : r1.headD 0 = 0
  · rw [checkDivModPinE.k_div_mod_env_guard.abort1 _ _ _ _ _ _ _ _ _ z1]
    have hrun1' : (divModEnvGuard fe2 (decI c)).run a = .ok (false, a1) := by
      rw [← decW0B_false hd1 z1]; exact hrun1
    exact RefE.bind_right hrun1' (RefE.ite_neg (by simp) fun _ => ErrClaim.fail _ _ rfl)
  rw [checkDivModPinE.k_div_mod_env_guard.arm1 _ _ _ _ _ _ _ _ _ z1]
  have hrun1' : (divModEnvGuard fe2 (decI c)).run a = .ok (true, a1) := by
    rw [← decW0B_true hd1 z1]; exact hrun1
  refine RefE.bind_right hrun1' (RefE.ite_pos rfl ?_)
  -- the stored value
  rcases h2 : callW p k "env_find" [c, vis2] m1 with _ | ⟨r2, m2⟩
  · rw [liftE_none, checkDivModPinE.k_env_find.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm2, hfd⟩ := envFind_call hD7.toDmProg6.toDmProg5.toMasterProg c hc hS1.check.env h2
  subst hm2
  cases hf : fe2.find? (decI c) with
  | none =>
    rw [hf] at hfd
    rw [checkDivModPinE.k_env_find.abort1 _ _ _ _ _ _ _ _ (show r2.headD 0 = 0 from hfd)]
    exact RefE.of_cls0 rfl
  | some ci =>
  rw [hf] at hfd
  obtain ⟨hr2, hci⟩ := hfd
  have hsz := hS1.iw.erSize
  by_cases hk1 : rdW (m2.arr64 EREC) (r2.tail.headD 0) ≠ 1
  · rw [checkDivModPinE.k_env_find.abort2 _ _ _ _ _ _ _ _ (by rw [hr2]; decide) hk1]
    exact RefE.of_cls0 rfl
  replace hk1 := Classical.not_not.mp hk1
  rw [checkDivModPinE.k_env_find.arm1 _ _ _ _ _ _ _ _ (by rw [hr2]; decide) hk1]
  obtain ⟨cv, v, hint, rfl, -, -⟩ : ∃ cv v hint, ci = .defnInfo cv v hint ∧
      (erecP m2)[(r2.tail.headD 0).toNat]? = some 1 ∧
      decCV (erecP m2) ((r2.tail.headD 0).toNat + 1) = some cv := by
    rcases decCI_defn_cases hci with h | ⟨w, hw', hne, hnd⟩
    · exact h
    · exfalso
      exact hne (by rw [← rdW_erec_of hsz hw']; exact hk1)
  obtain ⟨-, wv, hwv, hwlt, hvw⟩ := decCI_defn_value hci
  have hq5 : (r2.tail.headD 0 + 5).toNat = (r2.tail.headD 0).toNat + 5 := by
    have h1 : (r2.tail.headD 0).toNat + 5 < (erecP m2).size := by
      have := (Array.getElem?_eq_some_iff.mp hwv).1; omega
    have h2 : (erecP m2).size ≤ erTop m2 := erecP_size_le' m2
    have h3 : erTop m2 < 2 ^ 64 := (rdW (m2.arr64 CTL) 129).toNat_lt
    have h5 : (5 : Word).toNat = 5 := rfl
    rw [UInt64.toNat_add, h5]; exact Nat.mod_eq_of_lt (by omega)
  have hval : rdW (m2.arr64 EREC) (r2.tail.headD 0 + 5) = wv := by
    have : (erecP m2)[(r2.tail.headD 0 + 5).toNat]? = some wv := by rw [hq5]; exact hwv
    exact rdW_erec_of hsz this
  rw [hval]
  -- the twin's stored value: its denotation and its scope (con-ron's `checkDivModPin_bridge`)
  obtain ⟨nm0, cc, hn0, hcid, hfindP⟩ := hok2.ienv.hit (decI c) _ hf
  rw [hn] at hn0
  obtain rfl := Option.some.inj hn0
  simp only [Frontend.denoteCI] at hcid
  cases hcvd : Frontend.denoteCV a.store cv with
  | none => rw [hcvd] at hcid; simp at hcid
  | some cv' =>
  cases hvv : denoteE a.store v with
  | none => rw [hcvd, hvv] at hcid; simp at hcid
  | some v' =>
  rw [hcvd, hvv] at hcid
  simp only [Option.some.injEq] at hcid
  subst hcid
  have hwc := hok2.envWF.consts _ (List.mem_of_find?_eq_some hfindP)
  obtain ⟨hfv, -, -, -⟩ := hwc.2.2.2.2.1 cv' v' hint rfl
  have hwsv : ConLeche.Expr.WScoped 0 v' := ConLeche.Expr.WScoped.of_not_hasFvar hfv
  -- the variant loop, at the pre-insertion view
  have hv1 : denoteE a1.store (decE wv) = some v' := by
    have h := ConRon.Bridge.denote_ext hvv hx1
    rw [hvw] at h; exact h
  subst hvw
  have h3R := loop_ref hD hq hcl hkp hs0 hsA henv c wv hc hwlt hwsv ips psPs po pl [] k hk' m2 a1
    hC1 hCr1 (hI.grow hg1) (ConRon.Bridge.PinsDenote.mono hx1 _ _ hpd)
    (ConRon.Bridge.denoteN_ext hn hx1) hv1
  rcases e3 : checkDivModPinLoopE p k m2 vis c wv po pl with e3 | ⟨r3, m3⟩
  · rw [e3] at h3R
    rw [checkDivModPinE.k_check_div_mod_pin_loop.none]
    exact h3R
  rw [e3] at h3R
  rw [checkDivModPinE.k_check_div_mod_pin_loop.arm1]
  obtain ⟨x3, a3, hrun3, hR3⟩ := h3R
  have hS3' := StageR.restrict hR3.stage.stage vis2
  rw [IFEnv.restrictTo_restrictTo, ← hS.check.env.vis, IFEnv.restrictTo_self] at hS3'
  exact RefE.ret hrun3 ⟨⟨hR3.stage, c1.trans hR3.core, hg1.trans hR3.grow⟩, hS3'⟩

end pin

end L.Ind
