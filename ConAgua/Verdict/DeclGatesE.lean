import ConAgua.Verdict.DeclDefnE
import ConAgua.Arena.DeclDivGateT
import ConAgua.Arena.DeclNatGateT

/-!
# The verdict claims of the definition arm's gates (lane `verdicts-b`, helper `d`)

`defn_nat_gate` / `defn_nat_cert` / `certify_nat_eqs` (the structural-`Nat` gate) and
`defn_div_gate` / `check_div_mod_pin*` / `check_type_pins` / `check_div_mod_certs` (the
`Nat.div`-family pin gate).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Rom (PinSetsR)
open ConRon.Bridge (FoldOK PinsDenote CheckOK StepOK)

local notation "V" => ConLeche.CheckMode.verified

l_model defnNatGate_specE (p : Prog) (hf : p.lookup "defn_nat_gate" = some defnNatGate)
  fns [hf ↦ defnNatGateE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model defnNatCert_specE (p : Prog) (hf : p.lookup "defn_nat_cert" = some defnNatCert)
  fns [hf ↦ defnNatCertE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model certifyNatEqs_specE (p : Prog) (hf : p.lookup "certify_nat_eqs" = some certifyNatEqsL)
  fns [hf ↦ certifyNatEqsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

section cert
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- The gates' callees outside the verdict closure. -/
def gateNvList : List FnName :=
  ["nat_op_equations", "subst_const0_pairs", "subst_const0", "subst_const_all", "subst_const0_list",
   "div_mod_env_guard", "div_mod_pin_guard", "div_mod_certs_guard", "div_mod_cert_guard",
   "div_mod_cert_applied", "div_mod_cert_stmts", "div_mod_cert_proofs", "div_mod_type_pins",
   "div_mod_decl_pin", "type_pin_stored", "ground_guards", "nat_op_guard", "nat_op_deps",
   "nat_op_stored_ok_all", "nat_op_names", "sl_contains", "env_find", "rom_pin_sets",
   "nat_div_mod_names", "env_push", "pin_word", "pin_at"]

theorem gateNv_mem : ∀ f ∈ gateNvList, f ∈ L.Checker.nvFns := by
  decide +kernel

/-- A failing callee of the gates' list claims nothing. -/
theorem nvlG {p : Prog} (hnv : closedNV p L.Checker.nvFns = true) {α : Type} {T : AM α}
    {a : AState} {f : FnName} (hf : f ∈ gateNvList) {n : Nat} {vs : List Word} {m : Mem} {e : Err}
    (h : callE p n f vs m = .error e) : ErrClaim T a e :=
  ErrClaim.of_callE_nv hnv (gateNv_mem f hf) h

/-- **`certify_nat_eqs`' error claim under `StageT`**, on the model, by induction on the pairs
(the error half of `certW_okT`; the recursion is the model's). -/
theorem certE_okT (hq : KnotStageProg p) (hcE : CoreStubsE p) (o l : Word)
    (ps : List (EIdx × EIdx)) :
    ∀ (k : Nat), k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (e : Err),
      certifyNatEqsE p k m vis o l = .error e → StageT dn vis fe m a → EqL m o.toNat l.toNat ps →
      o.toNat + l.toNat < 2 ^ 64 → ErrClaim (certifyNatEqs V fe ps) a e := by
  induction ps generalizing o l with
  | nil =>
    intro k _ m a e h _ hE _
    have hl0 : l = 0 := UInt64.toNat_inj.mp (by have := hE.2.1; simpa using this)
    cases k with
    | zero => rw [certifyNatEqsE.eq_1] at h; cases h; exact fun hk => absurd rfl hk
    | succ k => rw [certifyNatEqsE.arm1 p k m vis o l hl0] at h; cases h
  | cons e0 es ih =>
    intro k hk m a e h hS hE hb
    cases k with
    | zero => rw [certifyNatEqsE.eq_1] at h; cases h; exact fun hk => absurd rfl hk
    | succ k =>
    have hk' : k ≤ 2 ^ 62 := by omega
    obtain ⟨pp, ea, eb, hl0, hpp, hrec, hea, heb, he, hrest⟩ := hE.cons
    rw [certifyNatEqsE.arm2 p k m vis o l (fun h => hl0 (by simp [h]))] at h
    have hpp' : rdW (m.arr64 IW) o = pp := by
      simp only [iwA] at hpp; simp [rdW, hpp]
    have hea' : rdW (m.arr64 IW) pp = ea := by
      obtain ⟨-, h2, -⟩ := hrec; simp only [iwA] at h2; simp [rdW, h2]
    have heb' : rdW (m.arr64 IW) (pp + 1) = eb := by
      obtain ⟨h1, -, h3⟩ := hrec
      have hpb : (pp + 1).toNat = pp.toNat + 1 := by
        have e1 := hS.stage.2.1; have e2 := hS.stage.2.2.2.1
        have e3 : pp.toNat + 1 < 2 ^ 64 := by omega
        rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; exact Nat.mod_eq_of_lt e3
      simp only [iwA] at h3; simp [rdW, hpb, h3]
    rw [hpp', hea', heb'] at h
    subst he
    simp only [certifyNatEqs]
    cases h1 : callE p k "is_def_eq_core" [vis, 2, ea, eb] m with
    | error e1 =>
      rw [h1, certifyNatEqsE.k_is_def_eq_core.none] at h; cases h
      have := hcE.isDefEqCore k hk' hS 2 ea eb hea heb _ h1
      exact ErrClaim.bind_left this
    | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1] at h
    obtain ⟨x1, a1, hrun1, hS1, hg1, hx1⟩ := hq.isDefEqCore_sim k hk' hS 2 ea eb hea heb r1 m1
      (callW_of_callE h1)
    have hrun1' : (isDefEqCore V fe checkFuel 2 (decE ea) (decE eb)).run a = .ok (x1, a1) := hrun1
    refine ErrClaim.bind_right hrun1' ?_
    by_cases hz : r1.headD 0 = 0
    · rw [certifyNatEqsE.k_is_def_eq_core.arm1 p k vis o l r1 m1 hz] at h; cases h
    rw [certifyNatEqsE.k_is_def_eq_core.arm2 p k vis o l r1 m1 hz] at h
    have hx : x1 = true := by rw [← hx1]; simpa [decBool] using hz
    rw [hx]
    refine ErrClaim.ite_pos rfl ?_
    have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hl1 : (l - 1).toNat = l.toNat - 1 := by
      have : 0 < l.toNat := Nat.pos_of_ne_zero (fun h0 => hl0 (by simp [h0]))
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have hrest1 : EqL m1 (o + 1).toNat (l - 1).toNat es := by
      rw [ho1, hl1]; exact hrest.grow hg1
    have hb1 : (o + 1).toNat + (l - 1).toNat < 2 ^ 64 := by omega
    exact ih (o + 1) (l - 1) k hk' m1 a1 e h hS1 hrest1 hb1

end cert

section gate
variable {p : Prog} {dn : NIdx → Option ConLeche.Name}

/-- **`defn_nat_cert`'s error claim under `StageC`** (the error half of `defnNatCert_okC`). -/
theorem defnNatCertE_okC (hN : NatSubProg' p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hcE : CoreStubsE p) (hnv : closedNV p L.Checker.nvFns = true)
    (hc : p.lookup "defn_nat_cert" = some defnNatCert)
    {vis w n : Word} {fe2 : IFEnv}
    {env env2 : ConLeche.Env} {nm : ConLeche.Name} {k : Nat} (hk : k ≤ 2 ^ 62) {m : Mem}
    {a : AState} {e : Err} (hn : H n)
    (hcall : callE p k "defn_nat_cert" [vis, w, n] m = .error e)
    (hSw : StageR dn w fe2 m a) (hC : StageC dn vis (fe2.restrictTo vis.toNat) env m a)
    (henv : ConLeche.EnvWF env) (hie : StepOK env2 fe2 a)
    (hnm : denoteN a.store.ns (decI n) = some nm) :
    ErrClaim (natCertT fe2 (fe2.restrictTo vis.toNat) (decI n)) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (defnNatCert_specE p hc k ⟨m, Locals.init []⟩ vis w n) hcall
    (Err.code_ne_of_cls hk0)
  cases k with
  | zero => rw [defnNatCertE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  rw [defnNatCertE.arm1] at hW
  have hE := hN.toNatSubProg.toNatEqProg
  have hG := hE.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg
  cases h1 : callE p k "env_find" [n, w] m with
  | error e1 =>
    rw [h1, defnNatCertE.k_env_find.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1] at hW
  obtain ⟨hm1, hfd⟩ := envFind_call hG.toMasterProg n hn hSw.1.env (callW_of_callE h1)
  subst hm1
  cases hf : fe2.find? (decI n) with
  | none =>
    rw [hf] at hfd
    have hz : r1.headD 0 = 0 := hfd
    rw [defnNatCertE.k_env_find.abort1 p _ _ _ _ _ hz] at hW; cases hW
    exact ErrClaim.of_cls0 rfl
  | some ci =>
  rw [hf] at hfd
  obtain ⟨hf1, hci⟩ := hfd
  have hnz : ¬ r1.headD 0 = 0 := by rw [hf1]; decide
  have hsz := hSw.2.2.2.2.1
  by_cases hkk' : ¬ rdW (m1.arr64 EREC) (r1.tail.headD 0) = 1
  · rw [defnNatCertE.k_env_find.abort2 p _ _ _ _ _ hnz hkk'] at hW; cases hW
    exact ErrClaim.of_cls0 rfl
  have hkk : rdW (m1.arr64 EREC) (r1.tail.headD 0) = 1 := Classical.not_not.mp hkk'
  rw [defnNatCertE.k_env_find.arm1 p _ _ _ _ _ hnz hkk] at hW
  generalize hq0 : r1.tail.headD 0 = q at hW hci hkk
  rcases decCI_defn_cases hci with ⟨cv, v, hint, rfl, hk1, hcv⟩ | ⟨w1, hw1, hne, hnd⟩
  rotate_left
  · have hk' := erecP_get hw1
    exact absurd hkk (by rw [rdW, hk']; exact hne)
  obtain ⟨wv, hk1', hk5, hwl, hwd⟩ := decCI_defn_val hci
  have hq5 : (q + 5).toNat = q.toNat + 5 := by
    have : q.toNat + 5 < (m1.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp (erecP_get hk5)).1
    rw [UInt64.toNat_add]; simp; omega
  have hqlt : q.toNat + 5 < erTop m1 := erecP_lt (erecP_get_rev hk5)
  obtain ⟨nm', c', hnm', hci', hfindP⟩ := hie.ienv.hit (decI n) _ hf
  have hnmEq : nm' = nm := by rw [hnm] at hnm'; exact (Option.some.inj hnm').symm
  subst hnmEq
  simp only [Frontend.denoteCI] at hci'
  cases hcv' : Frontend.denoteCV a.store cv with
  | none => rw [hcv'] at hci'; simp at hci'
  | some cvP =>
  cases hjv : denoteE a.store v with
  | none => rw [hcv', hjv] at hci'; simp at hci'
  | some vP =>
  rw [hcv', hjv] at hci'
  simp only [Option.some.injEq] at hci'
  subst hci'
  have hv : decE wv = v := hwd
  simp only [natCertT, hf]
  -- the equations
  cases h2 : callE p k "nat_op_equations" [0, n] m1 with
  | error e2 =>
    rw [h2, defnNatCertE.k_nat_op_equations.none] at hW; cases hW
    exact ErrClaim.bind_left (nvlG (T := natOpEquations 0 (decI n)) hnv (by decide +kernel) h2)
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, defnNatCertE.k_nat_op_equations.arm1] at hW
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ :=
    natOpEquations_ref hN 0 n k m1 a r2 m2 ⟨hSw, by decide, hn⟩ (callW_of_callE h2)
  have hrun2' : (natOpEquations 0 (decI n)).run a = .ok (x2, a2) := hrun2
  obtain ⟨hst2, hx2, hc2, hp2, hdeq⟩ :=
    ConRon.Bridge.natOpEquations_run hC.check.state hC.check.pins hnm hrun2'
  have hC2 := StageC.of_run hC (hS2.restrict vis)
    (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h2)) hst2 hx2 hc2 hp2
  have hE2 := decEqRL_headD hd2
  have e5' : rdW (m2.arr64 EREC) (q + 5) = wv := by
    simp only [rdW, hq5]; rw [hg2.2.2.2 _ hqlt, erecP_get hk5]; rfl
  rw [e5'] at hW
  refine ErrClaim.bind_right hrun2' ?_
  -- their substitution
  cases h3 : callE p k "subst_const0_pairs" [n, wv, r2.headD 0, r2.tail.headD 0] m2 with
  | error e3 =>
    rw [h3, defnNatCertE.k_subst_const0_pairs.none] at hW; cases hW
    exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h3)
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, defnNatCertE.k_subst_const0_pairs.arm1] at hW
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := pairs_ref hN.toNatSubProg n wv hn hwl x2 (r2.headD 0)
    (r2.tail.headD 0) k m2 a2 r3 m3 hS2 hE2 (EqL.lt64 hE2 hS2.2) (callW_of_callE h3)
  have hvP2 : denoteE a2.store (decE wv) = some vP := by
    rw [hv]; exact ConRon.Bridge.denote_ext hjv hx2
  obtain ⟨hst3, hx3, hc3, hp3, hdps⟩ := ConRon.Bridge.substConst0Pairs_run hst2 hC2.check.pins
    (ConRon.Bridge.denoteN_ext hnm hx2) hvP2 hdeq hrun3
  have hC3 := StageC.of_run hC2 (hS3.restrict vis)
    (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h3)) hst3 hx3 hc3 hp3
  have hE3 := decEqRL_headD hd3
  have hrun3' : (substConst0Pairs (decI n) (decE wv) x2).run a2 = .ok (x3, a3) := hrun3
  rw [← hv]
  refine ErrClaim.bind_right hrun3' ?_
  -- the certificate, at the pre-insertion view
  cases h4 : callE p k "certify_nat_eqs" [vis, r3.headD 0, r3.tail.headD 0] m3 with
  | error e4 =>
    rw [h4, defnNatCertE.k_certify_nat_eqs.none] at hW; cases hW
    by_cases hk4 : e.cls = 0
    · exact ErrClaim.of_cls0 hk4
    have hW4 := triple_of_callE_err
      (certifyNatEqs_specE p hN.toNatSubProg.toNatEqProg.lNatCertify k ⟨m3, Locals.init []⟩ vis
        (r3.headD 0) (r3.tail.headD 0)) h4 (Err.code_ne_of_cls hk4)
    exact ErrClaim.bind_left (certE_okT hq hcE _ _ x3 k hk' m3 a3 e hW4 hC3.stageT hE3
      (EqL.lt64 hE3 hS3.2))
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4] at hW
  obtain ⟨x4, a4, hrun4, hC4, hg4, hd4, hx4⟩ := certW_okC hE hq henv hk' hC3 hE3
    (EqL.lt64 hE3 hS3.2) hdps (ConRon.Bridge.natOpEqs_wscoped hie.envWF hfindP) (callW_of_callE h4)
  refine ErrClaim.bind_right hrun4 ?_
  by_cases e4 : r4.headD 0 = 0
  · rw [defnNatCertE.k_certify_nat_eqs.abort1 p r4 m4 e4] at hW; cases hW
    have t4 : x4 = false := by rw [← hd4.1, e4]; rfl
    rw [t4]
    exact ErrClaim.ite_neg (by decide) (ErrClaim.fail _ _ rfl)
  rw [defnNatCertE.k_certify_nat_eqs.arm1 p r4 m4 e4] at hW; cases hW

/-- **`defn_nat_gate`'s error claim under `StageC`** (the error half of `defnNatGate_okC`). -/
theorem defnNatGateE_okC (hN : NatSubProg' p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hcE : CoreStubsE p) (hnv : closedNV p L.Checker.nvFns = true)
    (hg : p.lookup "defn_nat_gate" = some defnNatGate)
    (hc : p.lookup "defn_nat_cert" = some defnNatCert)
    {vis w n : Word} {fe2 : IFEnv} {env env2 : ConLeche.Env} {nm : ConLeche.Name} {k : Nat}
    (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState} {e : Err} (hn : H n)
    (hcall : callE p k "defn_nat_gate" [vis, w, n] m = .error e)
    (hSw : StageR dn w fe2 m a) (hC : StageC dn vis (fe2.restrictTo vis.toNat) env m a)
    (henv : ConLeche.EnvWF env) (hie : StepOK env2 fe2 a)
    (hnm : denoteN a.store.ns (decI n) = some nm) :
    ErrClaim (natGateT (fe2.restrictTo vis.toNat) fe2 (decI n)) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (defnNatGate_specE p hg k ⟨m, Locals.init []⟩ vis w n) hcall
    (Err.code_ne_of_cls hk0)
  cases k with
  | zero => rw [defnNatGateE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  rw [defnNatGateE.arm1] at hW
  have hE := hN.toNatSubProg.toNatEqProg
  have hT := hE.toNatTyProg
  have hGd := hT.toNatGuardProg
  have hG := hGd.toNatLitProg.toNatCvProg.toNatGateProg
  have hvb : fe2.visibleBelow = w.toNat := hSw.1.env.vis
  rw [natGateT_eq]
  -- the operation names
  cases h1 : callE p k "nat_op_names" [] m with
  | error e1 =>
    rw [h1, defnNatGateE.k_nat_op_names.none] at hW; cases hW
    exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, defnNatGateE.k_nat_op_names.arm1] at hW
  obtain ⟨xs, a1, hrun1, hS1, hg1, hd1⟩ := natOpNames_ref hG k m a r1 m1 hSw (callW_of_callE h1)
  obtain ⟨e1, -⟩ := ConRon.Bridge.natOpNames_run hC.check.pins hrun1
  have e1' := e1.symm
  subst e1'
  refine ErrClaim.bind_right hrun1 ?_
  have hC1 := StageC.of_run hC (hS1.restrict vis)
    (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h1))
    hC.check.state (Ext.refl _) rfl rfl
  obtain ⟨hdh1, hb1⟩ := decRL0 hd1
  -- membership
  cases h2 : callE p k "sl_contains" [r1.headD 0, r1.tail.headD 0, n] m1 with
  | error e2 =>
    rw [h2, defnNatGateE.k_sl_contains.none] at hW; cases hW
    exact nvlG hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2] at hW
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := slContains_ref hG.lSlContains (r1.headD 0)
    (r1.tail.headD 0) n xs hn k m1 a r2 m2 ⟨hS1, hdh1⟩ (callW_of_callE h2)
  have ha2 : a2 = a := by
    simp only [pure, StateT.pure, StateT.run, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun2
    exact hrun2.2.symm
  rw [ha2] at hS2
  rw [ha2] at hrun2
  have hx2 : x2 = xs.contains (decI n) := by
    simp only [pure, StateT.pure, StateT.run, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun2
    exact hrun2.1.symm
  have hC2 := StageC.of_run hC1 (hS2.restrict vis)
    (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h2))
    hC.check.state (Ext.refl _) rfl rfl
  by_cases e2 : r2.headD 0 = 0
  · rw [defnNatGateE.k_sl_contains.arm2 p _ _ _ _ _ _ e2, defnNatGateE.j1.arm1] at hW; cases hW
  rw [defnNatGateE.k_sl_contains.arm1 p _ _ _ _ _ _ e2] at hW
  have hx2t : xs.contains (decI n) = true := by
    rw [← hx2, ← hd2.1]; simpa using e2
  rw [hx2t]
  refine ErrClaim.ite_pos rfl ?_
  -- the guard
  cases h3 : callE p k "nat_op_guard" [w, n] m2 with
  | error e3 =>
    rw [h3, defnNatGateE.k_nat_op_guard.none] at hW; cases hW
    exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h3)
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, defnNatGateE.k_nat_op_guard.arm1] at hW
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := natOpGuard_ref hGd n k m2 a r3 m3 ⟨hS2, hn⟩
    (callW_of_callE h3)
  obtain ⟨hst3, hx3, hc3, hp3, -⟩ :=
    ConRon.Bridge.natOpGuard_run hC2.check.state hC2.check.pins hie.ienv hnm hrun3
  have hC3 := StageC.of_run hC2 (hS3.restrict vis)
    (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h3)) hst3 hx3 hc3 hp3
  have hnm3 := ConRon.Bridge.denoteN_ext hnm hx3
  refine ErrClaim.bind_right hrun3 ?_
  -- the dependencies
  cases h4 : callE p k "nat_op_deps" [n] m3 with
  | error e4 =>
    rw [h4, defnNatGateE.k_nat_op_deps.none] at hW; cases hW
    exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h4)
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, defnNatGateE.k_nat_op_deps.arm1] at hW
  obtain ⟨ds, a4, hrun4, hS4, hg4, hd4⟩ := natOpDeps_ref hG n k m3 a3 r4 m4 ⟨hS3, hn⟩
    (callW_of_callE h4)
  obtain ⟨hst4, hx4, hc4, hp4, hdeps⟩ :=
    ConRon.Bridge.natOpDeps_run hst3 hC3.check.pins hnm3 hrun4
  have hC4 := StageC.of_run hC3 (hS4.restrict vis)
    (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h4)) hst4 hx4 hc4 hp4
  obtain ⟨hdh4, hb4⟩ := decRL0 hd4
  refine ErrClaim.bind_right hrun4 ?_
  -- the stored dependencies
  cases h5 : callE p k "nat_op_stored_ok_all" [w, r4.headD 0, r4.tail.headD 0] m4 with
  | error e5 =>
    rw [h5, defnNatGateE.k_nat_op_stored_ok_all.none] at hW; cases hW
    exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h5)
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5] at hW
  obtain ⟨x5, a5, hrun5, hS5, hg5, hd5⟩ :=
    okAll_ref hT (r4.headD 0) (r4.tail.headD 0) ds k m4 a4 r5 m5 hS4 hdh4 hb4 (callW_of_callE h5)
  obtain ⟨hst5, hx5, hc5, hp5, -⟩ := ConRon.Bridge.natOpStoredOkAll_run hst4 hC4.check.pins
    (hie.mono (hx3.trans hx4)).ienv hdeps hrun5
  have hC5 := StageC.of_run hC4 (hS5.restrict vis)
    (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h5)) hst5 hx5 hc5 hp5
  by_cases e35 : r3.headD 0 = 0 ∨ r5.headD 0 = 0
  · rw [defnNatGateE.k_nat_op_stored_ok_all.abort1 p _ _ _ _ _ _ _ e35] at hW; cases hW
    have hbool : (x3 && x5) = false := by
      rcases e35 with e | e
      · have : x3 = false := by rw [← hd3.1, e]; rfl
        simp [this]
      · have : x5 = false := by rw [← hd5.1, e]; rfl
        simp [this]
    refine ErrClaim.bind_right hrun5 ?_
    rw [hbool]
    exact ErrClaim.ite_neg (by decide) (ErrClaim.bind_left (ErrClaim.fail _ _ rfl))
  rw [defnNatGateE.k_nat_op_stored_ok_all.arm1 p _ _ _ _ _ _ _ e35] at hW
  have t3 : x3 = true := by rw [← hd3.1]; simp at e35; simp [e35.1]
  have t5 : x5 = true := by rw [← hd5.1]; simp at e35; simp [e35.2]
  refine ErrClaim.bind_right hrun5 ?_
  rw [t3, t5]
  refine ErrClaim.ite_pos rfl ?_
  -- the certificate
  have hx35 := hx3.trans (hx4.trans hx5)
  cases h6 : callE p k "defn_nat_cert" [vis, w, n] m5 with
  | error e6 =>
    rw [h6, defnNatGateE.k_defn_nat_cert.none] at hW; cases hW
    exact defnNatCertE_okC hN hq hcl hcE hnv hc hk' hn h6 hS5 hC5 henv (hie.mono hx35)
      (ConRon.Bridge.denoteN_ext hnm hx35)
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [h6, defnNatGateE.k_defn_nat_cert.arm1, defnNatGateE.j1.arm1] at hW; cases hW

end gate

/-- **`defn_nat_gate`'s error claim** (`NatGateSpecE`). -/
theorem natGateSpecE_of {p : Prog} (hN : NatSubProg' p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hcE : CoreStubsE p) (hnv : closedNV p L.Checker.nvFns = true)
    (hg : p.lookup "defn_nat_gate" = some defnNatGate)
    (hc : p.lookup "defn_nat_cert" = some defnNatCert) : NatGateSpecE p :=
  fun _dn _vis _w _fe2 _env _env2 _n _nm _k hk _m _a hn hSw hC henv hie hnm _e hcall =>
    defnNatGateE_okC hN hq hcl hcE hnv hg hc hk hn hcall hSw hC henv hie hnm

end L.Arena
