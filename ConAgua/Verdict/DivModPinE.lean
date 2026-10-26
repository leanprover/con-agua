import ConAgua.Arena.DeclDivGateT
import ConAgua.Arena.KnotE
import ConAgua.Checker.NoVerdictFns
import ConAgua.Checker.NoVerdictClosed

/-!
# The verdict claim of the `Nat.div` family's pin gate: `check_div_mod_pin_loop`, `check_div_mod_pin`

Error models (`l_model … errors`) and error refinements (calibration helper `verdicts-b-c4`).
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

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
  simp only [rdW, h', ↓reduceDIte, this, Array.getElem?_eq_getElem h, Option.getD_some]

l_model loopE_spec (p : Prog) (hp : p.lookup "check_div_mod_pin_loop" = some checkDivModPinLoopL)
  fns [hp ↦ loopE] simp [rdW_eq, getElem_rdW'] errors

l_model cpE_spec (p : Prog) (hp : p.lookup "check_div_mod_pin" = some checkDivModPinL)
  fns [hp ↦ cpE list] simp [rdW_eq, getElem_rdW', getElem_rdW_add5] errors

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
    rw [loopE.eq_2, if_neg hpl0] at he
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

end L.Ind
#print axioms L.Ind.loopCE
