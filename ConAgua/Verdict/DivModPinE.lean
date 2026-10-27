import ConAgua.Arena.DeclDivGateT2
import ConAgua.Arena.Verdict
import ConAgua.Checker.NoVerdictFns
import ConAgua.L.ModelGen

/-!
# The verdict claim of the `Nat.div` family's pin gate: `check_div_mod_pin_loop`, `check_div_mod_pin`

Error models (`l_model … errors`) and error refinements (calibration helper `verdicts-b-c4`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena
open L.Rom (PinSetsR PinSetR)
open ConRon.Bridge (CheckOK StepOK PinsDenote CoreStep)

theorem getElem_rdW_add5 (a : Array Word) (x : Word) (h : (x.toNat + 5) % 18446744073709551616 < a.size) :
    a[(x.toNat + 5) % 18446744073709551616] = rdW a (x + 5) := by
  have : (x + 5).toNat = (x.toNat + 5) % 18446744073709551616 := by
    rw [UInt64.toNat_add]; rfl
  have h' : (x + 5).toNat < a.size := by rw [this]; exact h
  simp only [rdW, this, Array.getElem?_eq_getElem h, Option.getD_some]

l_model loopE_spec (p : Prog) (hp : p.lookup "check_div_mod_pin_loop" = some checkDivModPinLoopL)
  fns [hp ↦ loopE] extra [ld64_rdW_specE] simp [] errors

l_model cpE_spec (p : Prog) (hp : p.lookup "check_div_mod_pin" = some checkDivModPinL)
  fns [hp ↦ cpE list] extra [ld64_rdW_specE] simp [] errors

/-! ## The loop -/

section loop
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

local notation "V" => ConLeche.CheckMode.verified

/-- **The error claim of `check_div_mod_pin_at`** (the callee's statement shape: `cpaC`'s hypotheses,
the failing call, the twin's attempt). -/
def CpaClaimE (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (env : ConLeche.Env) : Prop :=
  ∀ (c value ps : Word) (ip : INatOpPinSet) (psP : ConLeche.NatOpPinSet) (nm : ConLeche.Name)
    (v : ConLeche.Expr) (k : Nat), k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState),
    StageC dn vis fe env m a → H c → H value → PinSetR m ps ip → ConRon.Bridge.PinSetDenote a.store ip psP →
    denoteN a.store.ns (decI c) = some nm → denoteE a.store (decE value) = some v →
    ConLeche.Expr.WScoped 0 v → ConLeche.divModPinGuard psP env nm = true → L.Stubs.CrOK m →
    ∀ e, callE p k "check_div_mod_pin_at" [vis, c, value, ps] m = .error e →
      ErrClaim (checkDivModPinAt V fe (decI c) (decE value) ip) a e

/-- **`check_div_mod_pin_loop`'s error refinement** (`loopC`'s statement; the callee `check_div_mod_pin_at`
by its error claim, the guards claim nothing). -/
theorem loopCE (hD : DmProg9 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    (hnv : closedNV p L.Checker.nvFns = true) (hCpa : CpaClaimE p dn vis fe env)
    (c value : Word) (hc : H c) (hval : H value) {nm : ConLeche.Name} {v : ConLeche.Expr}
    (hwsv : ConLeche.Expr.WScoped 0 v) :
    ∀ (ips : List INatOpPinSet) (psPs : List ConLeche.NatOpPinSet) (po pl : Word)
      (tried : List String) (k : Nat), k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState),
      StageC dn vis fe env m a → L.Stubs.CrOK m → PinsIW m po.toNat pl.toNat ips →
      PinsDenote a.store ips psPs → denoteN a.store.ns (decI c) = some nm →
      denoteE a.store (decE value) = some v → ∀ e,
      loopE p k m vis c value po pl = .error e →
      ErrClaim (checkDivModPinLoop V fe (decI c) (decE value) ips tried) a e := by
  intro ips
  induction ips with
  | nil =>
    intro psPs po pl tried k hk m a hC _ hI hpd hn hv e he
    have hpl : pl = 0 := UInt64.toNat_inj.mp (by have := hI.2.1; simpa using this)
    cases k with
    | zero =>
      rw [loopE.eq_1] at he; cases he; exact ErrClaim.of_cls0 rfl
    | succ k =>
      rw [loopE.abort1 p k m vis c value po pl hpl] at he
      cases he
      exact ErrClaim.fail _ (.notImplemented _) rfl
  | cons ip rest ih =>
    intro psPs po pl tried k hk m a hC hCr hI hpd hn hv e he
    cases psPs with
    | nil => exact hpd.elim
    | cons psP restP =>
    obtain ⟨hq0, hrestP⟩ := hpd
    cases k with
    | zero => rw [loopE.eq_1] at he; cases he; exact ErrClaim.of_cls0 rfl
    | succ k =>
    have hk' : k ≤ 2 ^ 62 := by omega
    have hS := hC.stage
    have hsz := hS.2.2.2.1
    have hI1 := hS.2.1
    obtain ⟨hb, hl, hj⟩ := hI
    have hpl0 : pl ≠ 0 := fun e => by rw [e] at hl; simp at hl
    rw [loopE.eq_2, ite_eq_right hpl0] at he
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
    rw [hpsw] at he
    -- the next variant, from a state a declined variant left
    have next : ∀ (m2 : Mem) (a2 : AState) (tr : List String),
        StageC dn vis fe env m2 a2 → L.Stubs.CrOK m2 → IWGrow m m2 → CoreStep V env fe a a2 →
        loopE p k m2 vis c value (po + 1) (pl - 1) = .error e →
        ErrClaim (checkDivModPinLoop V fe (decI c) (decE value) rest tr) a2 e := by
      intro m2 a2 tr hC2 hCr2 hG2 c02 h4
      exact ih restP (po + 1) (pl - 1) tr k hk' m2 a2 hC2
        hCr2 (hrestI m2 hG2) (ConRon.Bridge.PinsDenote.mono c02.ext _ _ hrestP)
        (ConRon.Bridge.denoteN_ext hn c02.ext) (ConRon.Bridge.denote_ext hv c02.ext) e h4
    -- the pin guard
    cases h1 : callE p k "div_mod_pin_guard" [ps, vis, c] m with
    | error e1 =>
      rw [h1, loopE.k_div_mod_pin_guard.none] at he
      cases he
      exact ErrClaim.of_callE_nv hnv (by decide) h1
    | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1] at he
    obtain ⟨x1, a1, hrun1, hC1, c1, hg1, hd1, hx1v⟩ :=
      pgC hD.toDmProg8.toDmProg7.toDmProg6 hcl hkp (callW_of_callE h1) hC hc hP hq0 hn hCr
    have hCr1 := hkp.call (im_mem _ rfl) (callW_of_callE h1) hCr
    have hrun1' : (divModPinGuard ip fe (decI c)).run a = .ok (x1, a1) := hrun1
    by_cases z1 : r1.headD 0 = 0
    · rw [loopE.k_div_mod_pin_guard.arm2 _ _ _ _ _ _ _ _ _ _ z1, loopE.j1.arm1] at he
      have hx1 := decW0B_false hd1 z1
      refine ErrClaim.bind_right hrun1' ?_
      rw [hx1]
      refine ErrClaim.ite_neg (by simp) ?_
      exact next m1 a1 _ hC1 hCr1 hg1 c1 he
    rw [loopE.k_div_mod_pin_guard.arm1 _ _ _ _ _ _ _ _ _ _ z1] at he
    have hx1 := decW0B_true hd1 z1
    refine ErrClaim.bind_right hrun1' ?_
    rw [hx1]
    refine ErrClaim.ite_pos rfl ?_
    -- the certificates' guards
    have hq1 := (ConRon.Bridge.PinsDenote.mono c1.ext [ip] [psP] ⟨hq0, trivial⟩).1
    cases h2 : callE p k "div_mod_certs_guard" [ps, vis, c, value] m1 with
    | error e2 =>
      rw [h2, loopE.k_div_mod_certs_guard.none] at he
      cases he
      exact ErrClaim.of_callE_nv hnv (by decide) h2
    | ok q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [h2] at he
    obtain ⟨x2, a2, hrun2, hC2, c2, hg2, hd2⟩ :=
      cgsC hD.toDmProg8.toDmProg7.toDmProg6 hcl hkp hs0 hsA (callW_of_callE h2) hC1 hc hval
        (PinSetR.grow hP hg1) hq1
        (ConRon.Bridge.denoteN_ext hn c1.ext) (ConRon.Bridge.denote_ext hv c1.ext) hCr1
    have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hCr1
    have hG2 : IWGrow m m2 := hg1.trans hg2
    have c02 := c1.trans c2
    have hrun2' : (divModCertsGuard ip fe (decI c) (decE value)).run a1 = .ok (x2, a2) := hrun2
    by_cases z2 : r2.headD 0 = 0
    · rw [loopE.k_div_mod_certs_guard.arm2 _ _ _ _ _ _ _ _ _ _ z2, loopE.j1.arm1] at he
      have hx2 := decW0B_false hd2 z2
      refine ErrClaim.bind_right hrun2' ?_
      rw [hx2]
      refine ErrClaim.ite_neg (by simp) ?_
      exact next m2 a2 _ hC2 hCr2 hG2 c02 he
    rw [loopE.k_div_mod_certs_guard.arm1 _ _ _ _ _ _ _ _ _ _ z2] at he
    have hx2 := decW0B_true hd2 z2
    refine ErrClaim.bind_right hrun2' ?_
    rw [hx2]
    refine ErrClaim.ite_pos rfl ?_
    -- the attempt
    cases h3 : callE p k "check_div_mod_pin_at" [vis, c, value, ps] m2 with
    | error e3 =>
      rw [h3, loopE.k_check_div_mod_pin_at.none] at he
      cases he
      exact ErrClaim.bind_left (hCpa c value ps ip psP nm v k hk' m2 a2 hC2 hc hval
        (PinSetR.grow hP hG2) (ConRon.Bridge.PinsDenote.mono c02.ext [ip] [psP] ⟨hq0, trivial⟩).1
        (ConRon.Bridge.denoteN_ext hn c02.ext) (ConRon.Bridge.denote_ext hv c02.ext) hwsv
        (by rw [← hx1v, hx1]) hCr2 _ h3)
    | ok q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3] at he
    obtain ⟨x3, a3, hrun3, hC3, c3, hg3, hd3⟩ :=
      cpaC hD.toDmProg8 hq hcl hkp hs0 hsA henv hk' (callW_of_callE h3) hC2 hc hval
        (PinSetR.grow hP hG2)
        (ConRon.Bridge.PinsDenote.mono c02.ext [ip] [psP] ⟨hq0, trivial⟩).1
        (ConRon.Bridge.denoteN_ext hn c02.ext) (ConRon.Bridge.denote_ext hv c02.ext) hwsv
        (by rw [← hx1v, hx1]) hCr2
    have hG3 : IWGrow m m3 := hG2.trans hg3
    have c03 := c02.trans c3
    refine ErrClaim.bind_right hrun3 ?_
    by_cases z3 : r3.headD 0 ≠ 0
    · rw [loopE.k_check_div_mod_pin_at.arm1 _ _ _ _ _ _ _ _ _ z3] at he
      cases he
    have z3' : r3.headD 0 = 0 := by simpa using z3
    rw [loopE.k_check_div_mod_pin_at.arm2 _ _ _ _ _ _ _ _ _ z3', loopE.j1.arm1] at he
    have hx3 := decW0B_false hd3 z3'
    rw [hx3]
    refine ErrClaim.ite_neg (by simp) ?_
    exact next m3 a3 _ hC3 (hkp.call (im_mem _ rfl) (callW_of_callE h3) hCr2) hG3 c03 he

end loop

/-! ## The gate -/

section pin
variable {p : Prog}

local notation "V" => ConLeche.CheckMode.verified

/-- **The error claim of `check_div_mod_pin_loop`** (`loopC`'s hypotheses, the failing call). -/
def LoopClaimE (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (env : ConLeche.Env) : Prop :=
  ∀ (c value : Word), H c → H value → ∀ {nm : ConLeche.Name} {v : ConLeche.Expr},
    ConLeche.Expr.WScoped 0 v →
    ∀ (ips : List INatOpPinSet) (psPs : List ConLeche.NatOpPinSet) (po pl : Word)
      (tried : List String) (k : Nat), k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState),
      StageC dn vis fe env m a → L.Stubs.CrOK m → PinsIW m po.toNat pl.toNat ips →
      PinsDenote a.store ips psPs → denoteN a.store.ns (decI c) = some nm →
      denoteE a.store (decE value) = some v → ∀ e,
      callE p k "check_div_mod_pin_loop" [vis, c, value, po, pl] m = .error e →
      ErrClaim (checkDivModPinLoop V fe (decI c) (decE value) ips tried) a e

/-- **`check_div_mod_pin`'s error refinement** (`cpC`'s statement; the loop by its error claim, the
environment guard and `env_find` claim nothing). -/
theorem cpCE {p : Prog} (hD : DmProg9 p) (_hq : KnotStageProg p) (hcl : LeafClosed p)
    (hkp : CrKeep p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis vis2 : Word}
    {fe2 : IFEnv} {env env2 : ConLeche.Env}
    (hnv : closedNV p L.Checker.nvFns = true)
    (hLoop : LoopClaimE p dn vis (fe2.restrictTo vis.toNat) env)
    {po pl c : Word} {ips : List INatOpPinSet} {psPs : List ConLeche.NatOpPinSet}
    {nm : ConLeche.Name} {k : Nat} (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hS : StageR dn vis2 fe2 m a) (hC : StageC dn vis (fe2.restrictTo vis.toNat) env m a)
    (hok2 : StepOK env2 fe2 a) (hc : H c) (hI : PinsIW m po.toNat pl.toNat ips)
    (hpd : PinsDenote a.store ips psPs) (hn : denoteN a.store.ns (decI c) = some nm)
    (hCr : L.Stubs.CrOK m) (e : Err)
    (he : cpE p k m po pl vis vis2 c = .error e) :
    ErrClaim (checkDivModPin V ips (fe2.restrictTo vis.toNat) fe2 (decI c)) a e := by
  cases k with
  | zero => rw [cpE.eq_1] at he; cases he; exact ErrClaim.of_cls0 rfl
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  rw [cpE.arm1] at he
  have hD7 := hD.toDmProg8.toDmProg7
  -- the environment guard, at the extended view
  cases h1 : callE p k "div_mod_env_guard" [vis2, c] m with
  | error e1 =>
    rw [h1, cpE.k_div_mod_env_guard.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide) h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1] at he
  obtain ⟨x1, a1, hrun1, ⟨hS1, hg1, hd1⟩⟩ :=
    (eg_ref hD7 hdn c) k m a r1 m1 ⟨hS, hc⟩ (callW_of_callE h1)
  obtain ⟨hst1, hx1, hc1, hp1, hgv⟩ :=
    ConRon.Bridge.divModEnvGuard_run hC.check.state hC.check.pins hok2.ienv hn hrun1
  have c1 : CoreStep V env (fe2.restrictTo vis.toNat) a a1 :=
    ⟨hC.check.mono hst1 hx1 hc1 hp1, hx1, hp1⟩
  have hf1 := callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h1)
  have hC1 := StageC.of_core hC (hS1.restrict vis) hf1 c1
  have hCr1 := hkp.call (im_mem _ rfl) (callW_of_callE h1) hCr
  by_cases z1 : r1.headD 0 = 0
  · rw [cpE.k_div_mod_env_guard.abort1 _ _ _ _ _ _ _ _ _ z1] at he
    cases he
    have hxf := decW0B_false hd1 z1
    have hrun1' : (divModEnvGuard fe2 (decI c)).run a = .ok (false, a1) := by
      rw [← hxf]; exact hrun1
    unfold checkDivModPin
    refine ErrClaim.bind_right hrun1' ?_
    exact ErrClaim.ite_neg (by simp) (ErrClaim.fail _ _ rfl)
  rw [cpE.k_div_mod_env_guard.arm1 _ _ _ _ _ _ _ _ _ z1] at he
  have hxt := decW0B_true hd1 z1
  have hrun1' : (divModEnvGuard fe2 (decI c)).run a = .ok (true, a1) := by
    rw [← hxt]; exact hrun1
  unfold checkDivModPin
  refine ErrClaim.bind_right hrun1' ?_
  refine ErrClaim.ite_pos rfl ?_
  -- the stored value
  cases h2 : callE p k "env_find" [c, vis2] m1 with
  | error e2 =>
    rw [h2, cpE.k_env_find.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2] at he
  obtain ⟨hm2, hfd⟩ := envFind_call hD7.toDmProg6.toDmProg5.toMasterProg c hc hS1.1.env
    (callW_of_callE h2)
  subst hm2
  cases hf : fe2.find? (decI c) with
  | none =>
    rw [hf] at hfd
    rw [cpE.k_env_find.abort1 _ _ _ _ _ _ _ _ (show r2.headD 0 = 0 from hfd)] at he
    cases he; exact ErrClaim.of_cls0 rfl
  | some ci =>
  rw [hf] at hfd
  obtain ⟨hr2, hci⟩ := hfd
  have hsz := hS1.2.2.2.2.1
  by_cases hk1 : rdW (m2.arr64 EREC) (r2.tail.headD 0) ≠ 1
  · rw [cpE.k_env_find.abort2 _ _ _ _ _ _ _ _ (by rw [hr2]; decide) hk1] at he
    cases he; exact ErrClaim.of_cls0 rfl
  replace hk1 := Classical.not_not.mp hk1
  rw [cpE.k_env_find.arm1 _ _ _ _ _ _ _ _ (by rw [hr2]; decide) hk1] at he
  obtain ⟨cv, v, hint, rfl, hk1', hcv⟩ : ∃ cv v hint, ci = .defnInfo cv v hint ∧
      (erecP m2)[(r2.tail.headD 0).toNat]? = some 1 ∧
      decCV (erecP m2) ((r2.tail.headD 0).toNat + 1) = some cv := by
    rcases decCI_defn_cases hci with h | ⟨w, hw', hne, hnd⟩
    · exact h
    · exfalso
      have := rdW_erec_of hsz hw'
      exact hne (by rw [← this]; exact hk1) 
  obtain ⟨-, wv, hwv, hwlt, hvw⟩ := decCI_defn_value hci
  have hk1'' : rdW (m2.arr64 EREC) (r2.tail.headD 0) = 1 := hk1
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
  rw [hval] at he
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
  show ErrClaim (checkDivModPinLoop V _ (decI c) (decE wv) ips []) a1 e
  cases h3 : callE p k "check_div_mod_pin_loop"
      [vis, c, wv, po, pl] m2 with
  | error e3 =>
    rw [h3, cpE.k_check_div_mod_pin_loop.none] at he
    cases he
    exact hLoop c wv hc hwlt hwsv ips psPs po pl [] k hk' m2 a1 hC1 hCr1 (hI.grow hg1)
      (ConRon.Bridge.PinsDenote.mono hx1 _ _ hpd) (ConRon.Bridge.denoteN_ext hn hx1) hv1 _ h3
  | ok q3 =>
    rw [h3, cpE.k_check_div_mod_pin_loop.arm1] at he
    cases he

/-- **The loop's callee-shape error claim from its refinement**: `LoopClaimE`, given the claim of
`check_div_mod_pin_at` and the program's text. -/
theorem loopClaimE (hD : DmProg9 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    (hnv : closedNV p L.Checker.nvFns = true) (hCpa : CpaClaimE p dn vis fe env) :
    LoopClaimE p dn vis fe env := by
  intro c value hc hval nm v hwsv ips psPs po pl tried k hk m a hC hCr hI hpd hn hv e hce
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hE := triple_of_callE_err (loopE_spec p hD.lCheckDivModPinLoop k ⟨m, Locals.init []⟩ vis c
    value po pl) hce (Err.code_ne_of_cls hk0)
  exact loopCE hD hq hcl hkp hs0 hsA henv hnv hCpa c value hc hval hwsv ips psPs po pl tried k hk
    m a hC hCr hI hpd hn hv e hE

end pin

end L.Ind

