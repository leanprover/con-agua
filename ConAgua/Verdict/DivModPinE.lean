module

public import ConAgua.Arena.DeclDivGateT2
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclDivGateT1
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.DeclArmsNat

@[expose] public section

/-!
# The `Nat.div` family's variant loop `check_div_mod_pin_loop`

One model (`l_model … unified`) and one refinement for both outcomes, under `StageC`
(con-ron's `checkDivModPinLoop_bridge`): the loop over the variant records
(`loop_ref`; the guards lifted, the attempt by `cpa_ref`). Its errors claim from the core stubs'
(`CoreStubsE`). The pin gate `check_div_mod_pin` (`cdmp_ref`, `DeclDivGateT.lean`) reads it.
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
  grow : IWGrow m m'
  ext : Ext a.store a'.store
  pins : a'.pins = a.pins

section loop
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_div_mod_pin_loop` refines `checkDivModPinLoop` under `StageC`, both outcomes**
(con-ron's `checkDivModPinLoop_bridge`): the pin guard (`pgC`), on `true` the certificates' guard
(`cgsC`), on `true` the attempt (`cpa_ref`); every other outcome moves on to the next variant; no
variant left is the twin's `fail`. -/
theorem loop_ref (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p)
    (hs0 : SubstC0 p vis fe) (hsA : SubstCAll p vis fe) (henv : ConLeche.EnvWF env)
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
        StageC dn vis fe env m2 a2 → L.Stubs.CrOK m2 → IWGrow m m2 → CoreStep env fe a a2 →
        RefE (CoreStubsE p) (checkDivModPinLoopE.j1 p k vis c value po pl m2)
          (checkDivModPinLoop V fe (decI c) (decE value) rest tr) a2
          (fun w _ a' => PinPost dn vis fe env m a w.2 a') := by
      intro m2 a2 tr hC2 hCr2 hG2 c02
      rw [checkDivModPinLoopE.j1.arm1]
      exact (ih restP (po + 1) (pl - 1) tr k hk' m2 a2 hC2 hCr2 (hrestI m2 hG2)
        (ConRon.Bridge.PinsDenote.mono c02.ext _ _ hrestP) (ConRon.Bridge.denoteN_ext hn c02.ext)
        (ConRon.Bridge.denote_ext hv c02.ext)).mono
        fun _ _ _ hR => ⟨hR.stage, hG2.trans hR.grow, c02.ext.trans hR.ext, by rw [hR.pins, c02.pins]⟩
    -- the pin guard
    refine RefE.onlySim (fun _ => checkDivModPinLoopE.k_div_mod_pin_guard.none ..) (fun _ _ h => h) fun r1 m1 h1 => ?_
    obtain ⟨x1, a1, hrun1, hC1, c1, hg1, hd1, hx1v⟩ :=
      pgC hD.toDmProg7.toDmProg6 hcl hkp hcrf h1 hC hc hP hq0 hn hCr
    have hCr1 := hkp.call (im_mem _ rfl) h1 hCr
    refine RefE.bind_right hrun1 ?_
    by_cases z1 : r1.headD 0 = 0
    · rw [checkDivModPinLoopE.k_div_mod_pin_guard.arm2 _ _ _ _ _ _ _ _ _ _ z1, decW0B_false hd1 z1]
      exact RefE.ite_neg (by simp) (next m1 a1 _ hC1 hCr1 hg1 c1)
    rw [checkDivModPinLoopE.k_div_mod_pin_guard.arm1 _ _ _ _ _ _ _ _ _ _ z1]
    have hx1 := decW0B_true hd1 z1
    rw [hx1]
    refine RefE.ite_pos rfl ?_
    -- the certificates' guards
    have hq1 := (ConRon.Bridge.PinsDenote.mono c1.ext [ip] [psP] ⟨hq0, trivial⟩).1
    refine RefE.onlySim (fun _ => checkDivModPinLoopE.k_div_mod_certs_guard.none ..) (fun _ _ h => h) fun r2 m2 h2 => ?_
    obtain ⟨x2, a2, hrun2, hC2, c2, hg2, hd2⟩ :=
      cgsC hD.toDmProg7.toDmProg6 hcl hkp hcrf hs0 hsA h2 hC1 hc hval (PinSetR.grow hP hg1) hq1
        (ConRon.Bridge.denoteN_ext hn c1.ext) (ConRon.Bridge.denote_ext hv c1.ext) hCr1
    have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
    have hG2 : IWGrow m m2 := hg1.trans hg2
    have c02 := c1.trans c2
    refine RefE.bind_right hrun2 ?_
    by_cases z2 : r2.headD 0 = 0
    · rw [checkDivModPinLoopE.k_div_mod_certs_guard.arm2 _ _ _ _ _ _ _ _ _ _ z2, decW0B_false hd2 z2]
      exact RefE.ite_neg (by simp) (next m2 a2 _ hC2 hCr2 hG2 c02)
    rw [checkDivModPinLoopE.k_div_mod_certs_guard.arm1 _ _ _ _ _ _ _ _ _ _ z2, decW0B_true hd2 z2]
    refine RefE.ite_pos rfl ?_
    -- the attempt
    have h3R := cpa_ref hD hq hcl hkp hcrf hs0 hsA henv hk' hC2 hc hval (PinSetR.grow hP hG2)
      (ConRon.Bridge.PinsDenote.mono c02.ext [ip] [psP] ⟨hq0, trivial⟩).1
      (ConRon.Bridge.denoteN_ext hn c02.ext) (ConRon.Bridge.denote_ext hv c02.ext) hwsv
      (by rw [← hx1v, hx1]) hCr2
    refine RefE.bindE (fun _ => checkDivModPinLoopE.k_check_div_mod_pin_at.none ..) id h3R
      fun ⟨r3, m3⟩ x3 a3 _ hR3 => ?_
    by_cases z3 : r3 ≠ 0
    · rw [checkDivModPinLoopE.k_check_div_mod_pin_at.arm1 _ _ _ _ _ _ _ _ _ z3,
        decW0B_true hR3.res (by simpa using z3)]
      exact RefE.ite_pos rfl (RefE.ret rfl ⟨hR3.stage, hG2.trans hR3.grow, (c02.trans hR3.core).ext, by rw [(c02.trans hR3.core).pins]⟩)
    have z3' : r3 = 0 := by simpa using z3
    rw [checkDivModPinLoopE.k_check_div_mod_pin_at.arm2 _ _ _ _ _ _ _ _ _ z3',
      decW0B_false hR3.res (by simpa using z3')]
    exact RefE.ite_neg (by simp) (next m3 a3 _ hR3.stage hR3.cr (hG2.trans hR3.grow) (c02.trans hR3.core))

end loop

end L.Ind
