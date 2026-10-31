import ConAgua.Arena.DeclDivGateT1
import ConAgua.Arena.DeclDivModSpec.RomPinSets
import ConAgua.Arena.DeclCrpT

/-!
# The `Nat.div`-family pin gate under `StageC`, part 2: the attempt (lane `loopt3`, `loopt3-div`)

`check_div_mod_certs` (`cm_ref`), `check_type_pins` (`ctp_ref`), `check_div_mod_pin_value`
(`cpv_ref`), `check_div_mod_pin_at` (`cpa_ref`), each one refinement of its unified model for both
outcomes (the variant loop and the gate over them: `Verdict/DivModPinE.lean`): the core calls
`infer_type_core`, `is_def_eq_core` by the knot's `StageT` sims (`KnotStageProg`; their failures
by `CoreStubsE`) and `CheckOK` after from con-ron's `KnotSpec` (`StageC.of_T`), the leaves as in
part 1, lifted (their failures are of class `0`). The twin side follows con-ron's
`checkDivModCerts_bridge_aux`, `checkTypePins_spec` and `checkDivModPinAt_bridge`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena
open L.Rom (PinSetsR PinSetR)
open ConRon.Bridge (CheckOK StepOK PinsDenote PinSetDenote CoreStep CoreSpec)

local notation "V" => ConLeche.CheckMode.verified

/-- **`infer_type_core`'s twin side** (`defeq_check`'s): con-ron's `KnotSpec.infer` at `checkFuel`. -/
theorem infer_check {env : ConLeche.Env} {fe : IFEnv} {a a' : AState} {d : Nat} {i t : EIdx}
    {x : ConLeche.Expr} (henv : ConLeche.EnvWF env) (hck : CheckOK V env fe a)
    (hi : denoteE a.store i = some x) (hws : ConLeche.Expr.WScoped d x)
    (hrun : (inferTypeCore V fe checkFuel d i).run a = .ok (t, a')) :
    CheckOK V env fe a' ∧ Ext a.store a'.store ∧ a'.pins = a.pins ∧
      ConRon.Bridge.Core.SimE (ConLeche.inferTypeCore V env) d x a'.store t :=
  ConRon.Bridge.AM.of_run (P := fun t => t = a) rfl hrun
    (((CoreSpec.of_core rfl).knot env fe henv).infer a d i x hck hi hws)

l_model checkDivModCerts_specE (p : Prog)
  (hf : p.lookup "check_div_mod_certs" = some checkDivModCertsL)
  fns [hf ↦ checkDivModCertsE]
  specs [callW_spec p n "div_mod_cert_guard", callW_spec p n "subst_const_all",
    callW_spec p n "subst_const0_list", callW_spec p n "div_mod_cert_applied",
    callW_spec p n "subst_const0"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What the `Nat.div`-family pin gate's checks give besides the twin's answer `x` (from `m`,
`a`): `StageC` after, the twin's core step, the growth, the result word decoding `x`,
`consts_resolve_ffast`'s memo kept. -/
structure DmPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (r : Word) (m' : Mem) (x : Bool) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  core : CoreStep V env fe a a'
  grow : IWGrow m m'
  res : decW0B m' [r] x
  cr : L.Stubs.CrOK m'

section certs
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_div_mod_certs` refines `checkDivModCerts` under `StageC`, both outcomes** (con-ron's
`checkDivModCerts_bridge_aux`), by induction on the statements. -/
theorem cm_ref (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    (c annVal : Word) (hc : H c) (hann : H annVal) {nm : ConLeche.Name} {v : ConLeche.Expr}
    (hwsv : ConLeche.Expr.WScoped 0 v) :
    ∀ (ss : List (List EIdx × EIdx)) (xs : List (List ConLeche.Expr × ConLeche.Expr))
      (proofs : List EIdx) (ps : List ConLeche.Expr) (so sl po pl : Word) (k : Nat), k ≤ 2 ^ 62 →
      ∀ (m : Mem) (a : AState), StageC dn vis fe env m a →
      L.Stubs.CrOK m →
      StmtL m so.toNat sl.toNat ss → decHL m po.toNat pl.toNat = some proofs →
      po.toNat + pl.toNat ≤ iwTop m → denoteN a.store.ns (decI c) = some nm →
      denoteE a.store (decE annVal) = some v → ConRon.Bridge.StmtsDenote a.store ss xs →
      Frontend.denoteEList a.store proofs = some ps →
      (∀ q ∈ xs, (∀ h ∈ q.1, ConLeche.Expr.WScoped 2 h) ∧ ConLeche.Expr.WScoped 2 q.2) →
      RefE (CoreStubsE p) (checkDivModCertsE p k m vis c annVal so sl po pl)
        (checkDivModCerts V fe (decI c) (decE annVal) ss proofs) a
        (fun v x a' => DmPost dn vis fe env m a v.1 v.2 x a') := by
  have hws4 : ConLeche.Expr.WScoped 4 v := ConLeche.Expr.WScoped.mono (by omega) hwsv
  have hws2 : ConLeche.Expr.WScoped 2 v := ConLeche.Expr.WScoped.mono (by omega) hwsv
  intro ss
  induction ss with
  | nil =>
    intro xs proofs ps so sl po pl k hk m a hC hCr hs hd hb hn hv hsd hpr hwq
    have hsl : sl = 0 := UInt64.toNat_inj.mp (by have := hs.2.1; simpa using this)
    cases k with
    | zero => rw [checkDivModCertsE.eq_1]; exact RefE.of_cls0 (by simp)
    | succ k =>
    cases proofs with
    | nil =>
      have hpl : pl = 0 := UInt64.toNat_inj.mp (by have := decHL_length m hd; simp at this ⊢; omega)
      rw [checkDivModCertsE.arm1 p k m vis c annVal so sl po pl ⟨hsl, hpl⟩]
      exact RefE.ret rfl ⟨hC, CoreStep.refl hC.check, IWGrow.refl _, by simp [decW0B], hCr⟩
    | cons pf pfs =>
      have hpl : pl ≠ 0 := fun e => by
        have := decHL_length m hd; rw [e] at this; simp at this
      rw [checkDivModCertsE.arm2 p k m vis c annVal so sl po pl (fun h => hpl h.2) (Or.inl hsl)]
      exact RefE.ret rfl ⟨hC, CoreStep.refl hC.check, IWGrow.refl _, by simp [decW0B], hCr⟩
  | cons st ss ih =>
    rcases st with ⟨hy, eqq⟩
    intro xs proofs ps so sl po pl k hk m a hC hCr hs hd hb hn hv hsd hpr hwq
    have hS := hC.stage
    cases xs with
    | nil => exact hsd.elim
    | cons xq xrest =>
    obtain ⟨hx, ex⟩ := xq
    obtain ⟨hsd1, hsd2, hsd3⟩ := hsd
    obtain ⟨hwh, hwe⟩ := hwq (hx, ex) (by simp)
    obtain ⟨hsl0, q, hq0, hstm, hrest⟩ := StmtL.cons hS.iw hs
    cases k with
    | zero => rw [checkDivModCertsE.eq_1]; exact RefE.of_cls0 (by simp)
    | succ k =>
    have hk' : k ≤ 2 ^ 62 := by omega
    cases proofs with
    | nil =>
      have hpl : pl = 0 := UInt64.toNat_inj.mp (by have := decHL_length m hd; simp at this ⊢; omega)
      rw [checkDivModCertsE.arm2 p k m vis c annVal so sl po pl (fun h => hsl0 h.1) (Or.inr hpl)]
      exact RefE.ret rfl ⟨hC, CoreStep.refl hC.check, IWGrow.refl _, by simp [decW0B], hCr⟩
    | cons pf pfs =>
    obtain ⟨px, pxs, hpx, hpxs, rfl⟩ := ConRon.Bridge.denoteEList_cons hpr
    obtain ⟨hpl0, hpwlt, hpf, hdrest⟩ := decHL_cons_iw hS.iw.iwSize hd
    subst hpf
    obtain ⟨ho, hl, e0, hr3, hbd, hdh, he, hst2⟩ := hstm
    obtain ⟨hp3, h0, h1, h2⟩ := hr3
    have hst2' : eqq = decE e0 := hst2
    subst hst2'
    rw [checkDivModCertsE.arm3 p k m vis c annVal so sl po pl (fun h => hsl0 h.1)
      (by rintro (h | h); exact hsl0 h; exact hpl0 h)]
    have hsz := hS.iw.iwSize
    have hI1 := hS.iw.iw
    have r0 : rdW (m.arr64 IW) so = q := hq0
    have rq1 : rdW (m.arr64 IW) q = ho := rdW_iw_of h0 rfl
    have rq2 : rdW (m.arr64 IW) (q + 1) = hl := rdW_iw_of h1 (word_add_one (by omega))
    have rq3 : rdW (m.arr64 IW) (q + 2) = e0 := rdW_iw_of h2 (word_add_two (by omega))
    have hlpos : 0 < pl.toNat :=
      Nat.pos_of_ne_zero (fun e' => hpl0 (UInt64.toNat_inj.mp (by simpa using e')))
    have hpo1 : (po + 1).toNat = po.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hpl1 : (pl - 1).toNat = pl.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have hpo : po.toNat < iwTop m := by omega
    have hq3 : q.toNat + 3 ≤ iwTop m := hp3
    have hq0' : q.toNat < iwTop m := by omega
    have hq1 : (q + 1).toNat < iwTop m := by rw [word_add_one (by omega)]; omega
    have hq2 : (q + 2).toNat < iwTop m := by rw [word_add_two (by omega)]; omega
    rw [r0, rq1, rq2, rq3]
    simp only [checkDivModCerts]
    -- the guard
    refine RefE.bindLift (fun _ => checkDivModCertsE.k_div_mod_cert_guard.none ..) fun r1 m1 h1' => ?_
    obtain ⟨x1, a1, hrun1, hC1, c1, hg1, hd1, hxv1⟩ :=
      cgC hD.toDmProg7.toDmProg6.toDmProg5 hcl hkp hs0 hsA h1' hC hc hann he hpwlt
        hdh hbd hn hv hsd1 hsd2 hpx hCr
    have hCr1 := hkp.call (im_mem _ rfl) h1' hCr
    have hrun1' : (divModCertGuard fe (decI c) (decE annVal) hy (decE e0)
        (decI (rdW (m.arr64 IW) po))).run a = .ok (x1, a1) := hrun1
    refine ⟨_, _, hrun1', ?_⟩
    rw [checkDivModCertsE.k_div_mod_cert_guard.eq_2]
    refine RefE.retIf (decW0B_false hd1) (fun hb => by grind [decW0B])
      (fun _ => ⟨hC1, c1, hg1, by simp [decW0B], hCr1⟩) fun z1 hx1 => ?_
    have hg' : ConLeche.divModCertGuard env nm v hx ex px = true := by rw [← hxv1, hx1]
    simp only [ConLeche.divModCertGuard, Bool.and_eq_true, Bool.not_eq_true'] at hg'
    have hPf : (ConLeche.Expr.substConstAll nm v px).hasFvar = false := hg'.1.1.1.1.2
    have hn1 := ConRon.Bridge.denoteN_ext hn c1.ext
    have hv1 := ConRon.Bridge.denote_ext hv c1.ext
    -- the substituted proof
    rw [iw_rd_grow hg1 hpo]
    refine RefE.bindLift (fun _ => checkDivModCertsE.k_subst_const_all.none ..) fun r2 m2 h2' => ?_
    rw [checkDivModCertsE.k_subst_const_all.eq_2]
    have hCr2 := hkp.call (im_mem _ rfl) h2' hCr1
    obtain ⟨x2, a2, hrun2, hS2, hg2, hl2, hx2⟩ := hsA c annVal _ hc hann hpwlt k m1 a1 r2 m2 hC1.stage h2'
    subst hx2
    obtain ⟨hi2, hpd⟩ := ConRon.Bridge.substConstAll_run coreWalkFuel hC1.check.state
      hC1.check.pins hn1 hv1 (ConRon.Bridge.denote_ext hpx c1.ext) hrun2
    have c2 := ConRon.Bridge.CoreStep.of_istep hC1.check hi2
    have hC2 := StageC.of_core hC1 hS2 (callW_leafFrame hcl (leaf_mem _ (by decide)) h2') c2
    have c02 := c1.trans c2
    have hG2 : IWGrow m m2 := hg1.trans hg2
    refine ⟨_, _, hrun2, ?_⟩
    -- the substituted hypotheses
    rw [iw_rd_grow hG2 hq0', rq1, iw_rd_grow hG2 hq1, rq2]
    refine RefE.bindLift (fun _ => checkDivModCertsE.k_subst_const0_list.none ..) fun r3 m3 h3' => ?_
    rw [checkDivModCertsE.k_subst_const0_list.eq_2]
    have hdh2 : decHL m2 ho.toNat hl.toNat = some hy := by rw [decHL_grow hG2 hbd]; exact hdh
    have hCr3 := hkp.call (im_mem _ rfl) h3' hCr2
    obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := sc0List_ref hD.toDmProg7.toDmProg6.toDmProg5 hs0 c
      annVal hc hann hy ho hl k m2 a2 r3 m3 hC2.stage hdh2 (Nat.le_trans hbd hG2.iw) h3'
    simp only [decRL, Nat.zero_add, ntGetD0, ntGetD1] at hd3
    obtain ⟨hi3, hhs⟩ := ConRon.Bridge.substConst0List_run hy hx hC2.check.state hC2.check.pins
      (ConRon.Bridge.denoteN_ext hn c02.ext) (ConRon.Bridge.denote_ext hv c02.ext)
      (ConRon.Bridge.denoteEList_ext c02.ext _ _ hsd1) hrun3
    have c3 := ConRon.Bridge.CoreStep.of_istep hC2.check hi3
    have hC3 := StageC.of_core hC2 hS3 (callW_leafFrame hcl (leaf_mem _ (by decide)) h3') c3
    have c03 := c02.trans c3
    have hG3 : IWGrow m m3 := hG2.trans hg3
    refine ⟨_, _, hrun3, ?_⟩
    -- the application
    refine RefE.bindLift (fun _ => checkDivModCertsE.k_div_mod_cert_applied.none ..) fun r4 m4 h4' => ?_
    rw [checkDivModCertsE.k_div_mod_cert_applied.arm1]
    obtain ⟨x4, a4, hrun4, hS4, hg4, hl4, rfl⟩ :=
      (applied_ref (dn := dn) (vis := vis) (fe := fe) hD.toDmProg7.toDmProg6.toDmProg5 (r2.headD 0)
        (r3.headD 0) (r3.tail.headD 0) x3) k m3 a3 r4 m4 ⟨hC3.stage, hl2, hd3.1, hd3.2⟩ h4'
    have hCr4 := hkp.call (im_mem _ rfl) h4' hCr3
    obtain ⟨hi4, hap0⟩ := ConRon.Bridge.divModCertApplied_run hC3.check.state hC3.check.pins
      (ConRon.Bridge.denote_ext hpd hi3.ext) hhs hrun4
    have c4 := ConRon.Bridge.CoreStep.of_istep hC3.check hi4
    have hC4 := StageC.of_core hC3 hS4 (callW_leafFrame hcl (leaf_mem _ (by decide)) h4') c4
    have c04 := c03.trans c4
    have hG4 : IWGrow m m4 := hG3.trans hg4
    have hwsA : ConLeche.Expr.WScoped 4 (ConLeche.divModCertApplied
        (ConLeche.Expr.substConstAll nm v px) (hx.map (ConLeche.Expr.substConst0 nm v))) := by
      refine ConRon.Bridge.divModCertApplied_wscoped hPf fun h hh => ?_
      obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh
      exact ConRon.Bridge.substConst0_wscoped hws2 _ (hwh h0 hh0)
    have hrun4' : (divModCertApplied (decI (r2.headD 0)) x3).run a3 =
        .ok (decI (r4.headD 0), a4) := hrun4
    refine ⟨_, _, hrun4', ?_⟩
    -- the type
    refine RefE.bindCall (fun _ => checkDivModCertsE.k_infer_type_core.eq_1 ..)
      (fun hcE _ h5 => hcE.inferTypeCore k hk' hC4.stageT 4 (r4.headD 0) hl4 _ h5)
      (fun b h5 => hq.inferTypeCore_sim k hk' hC4.stageT 4 (r4.headD 0) hl4 b.1 b.2 h5)
      fun r5 m5 x5 a5 h5 hrun5 ⟨hT5, hg5, hl5, hx5⟩ => ?_
    rw [checkDivModCertsE.k_infer_type_core.arm1]
    subst hx5
    obtain ⟨hck5, hx5', hp5, tpx, htp5, hwstp, -⟩ := infer_check henv hC4.check hap0 hwsA hrun5
    have c5 : CoreStep V env fe a4 a5 := ⟨hck5, hx5', hp5⟩
    have hC5 := StageC.of_T hT5 hck5
    have c05 := c04.trans c5
    have hG5 : IWGrow m m5 := hG4.trans hg5
    -- the equation, substituted
    rw [iw_rd_grow hG5 hq2, rq3]
    refine RefE.bindLift (fun _ => checkDivModCertsE.k_subst_const0.none ..) fun r6 m6 h6 => ?_
    rw [checkDivModCertsE.k_subst_const0.arm1]
    have hCr6 := hkp.call (im_mem _ rfl) h6 (hkp.call (im_mem _ rfl) (callW_of_callE h5) hCr4)
    obtain ⟨x6, a6, hrun6, hS6, hg6, hl6, hx6⟩ :=
      hs0 c annVal e0 hc hann he k m5 a5 r6 m6 hC5.stage h6
    subst hx6
    obtain ⟨hi6, hrhs⟩ := ConRon.Bridge.substConst0_run coreWalkFuel hC5.check.state hC5.check.pins
      (ConRon.Bridge.denoteN_ext hn c05.ext) (ConRon.Bridge.denote_ext hv c05.ext)
      (ConRon.Bridge.denote_ext hsd2 c05.ext) hrun6
    have c6 := ConRon.Bridge.CoreStep.of_istep hC5.check hi6
    have hC6 := StageC.of_core hC5 hS6 (callW_leafFrame hcl (leaf_mem _ (by decide)) h6) c6
    have hG6 : IWGrow m m6 := hG5.trans hg6
    have hwsR : ConLeche.Expr.WScoped 4 (ConLeche.Expr.substConst0 nm v ex) :=
      ConRon.Bridge.substConst0_wscoped hws4 _ (ConLeche.Expr.WScoped.mono (by omega) hwe)
    have hrun6' : (substConst0 (decI c) (decE annVal) coreWalkFuel (decE e0)).run a5 =
        .ok (decI (r6.headD 0), a6) := hrun6
    refine ⟨_, _, hrun6', ?_⟩
    -- the comparison
    refine RefE.bindCall (fun _ => checkDivModCertsE.k_is_def_eq_core.eq_1 ..)
      (fun hcE _ h7 => hcE.isDefEqCore k hk' hC6.stageT 4 (r5.headD 0) (r6.headD 0) hl5 hl6 _ h7)
      (fun b h7 => hq.isDefEqCore_sim k hk' hC6.stageT 4 (r5.headD 0) (r6.headD 0) hl5 hl6 b.1 b.2 h7)
      fun r7 m7 x7 a7 h7 hrun7 ⟨hT7, hg7, hd7⟩ => ?_
    have hCr7 := hkp.call (im_mem _ rfl) (callW_of_callE h7) hCr6
    obtain ⟨hck7, hx7', hp7, -⟩ := defeq_check henv hC6.check
      (ConRon.Bridge.denote_ext htp5 hi6.ext) hrhs hwstp hwsR hrun7
    have c7 : CoreStep V env fe a6 a7 := ⟨hck7, hx7', hp7⟩
    have hC7 := StageC.of_T hT7 hck7
    have c07 := (c05.trans c6).trans c7
    have hG7 : IWGrow m m7 := hG6.trans hg7
    rw [checkDivModCertsE.k_is_def_eq_core.eq_2]
    refine RefE.retIf (fun z7 => hd7 ▸ decBool_f_m2c z7) (fun hb => by simpa [← hd7, decBool] using hb)
      (fun _ => ⟨hC7, c07, hG7, by simp [decW0B], hCr7⟩) fun z7 _ => ?_
    have hdr1 : decHL m7 (po + 1).toNat (pl - 1).toNat = some pfs := by
      rw [decHL_grow hG7 (by rw [hpo1, hpl1]; omega)]; exact hdrest
    refine (ih xrest pfs pxs (so + 1) (sl - 1) (po + 1) (pl - 1) k (by omega) m7 a7 hC7 hCr7
      (hrest.grow hG7) hdr1 (by rw [hpo1, hpl1]; have := hG7.iw; omega)
      (ConRon.Bridge.denoteN_ext hn c07.ext) (ConRon.Bridge.denote_ext hv c07.ext)
      (ConRon.Bridge.StmtsDenote.mono c07.ext _ _ hsd3)
      (ConRon.Bridge.denoteEList_ext c07.ext _ _ hpxs)
      (fun q hq => hwq q (List.mem_cons_of_mem _ hq))).mono ?_
    exact fun _ _ _ hR => ⟨hR.stage, c07.trans hR.core, hG7.trans hR.grow, hR.res, hR.cr⟩

end certs

l_model checkTypePins_specE (p : Prog) (hf : p.lookup "check_type_pins" = some checkTypePinsL)
  fns [hf ↦ checkTypePinsE]
  specs [callW_spec p n "type_pin_stored"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section typePins
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_type_pins` refines `checkTypePins` under `StageC`, both outcomes** (con-ron's
`checkTypePins_spec`): per pair the stored type by `tps_ref`, then `is_def_eq_core` by the knot's
`StageT` sim (its failure by `CoreStubsE`), `CheckOK` after from con-ron's `KnotSpec`; both sides
closed by the variant's pin guard (`hcl'`). -/
theorem ctp_ref (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (henv : ConLeche.EnvWF env) :
    ∀ (tps : List (NIdx × EIdx)) (tpsP : List (ConLeche.Name × ConLeche.Expr)) (o l : Word)
      (k : Nat), k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState),
      StageC dn vis fe env m a → L.Stubs.CrOK m → L.Rom.TPinsR m o l tps →
      ConRon.Bridge.TypePinsDenote a.store tps tpsP →
      (∀ q ∈ tpsP, (ConLeche.typePinStored env q.1).hasFvar = false ∧ q.2.hasFvar = false) →
      RefE (CoreStubsE p) (checkTypePinsE p k m vis o l) (checkTypePins V fe tps) a
        (fun v x a' => DmPost dn vis fe env m a v.1 v.2 x a') := by
  intro tps
  induction tps with
  | nil =>
    intro tpsP o l k _ m a hC hCr ht hd _
    have hl : l = 0 := UInt64.toNat_inj.mp (by have := ht.2.1; simpa using this)
    cases k with
    | zero => rw [checkTypePinsE.eq_1]; exact RefE.of_cls0 (by simp)
    | succ k =>
    rw [checkTypePinsE.arm1 p k m vis o l hl]
    exact RefE.ret rfl ⟨hC, CoreStep.refl hC.check, IWGrow.refl _, by simp [decW0B], hCr⟩
  | cons tp tps ih =>
    intro tpsP o l k hk m a hC hCr ht hd hcl'
    cases tpsP with
    | nil => exact hd.elim
    | cons q qs =>
    obtain ⟨hd1, hd2, hd3⟩ := hd
    cases k with
    | zero => rw [checkTypePinsE.eq_1]; exact RefE.of_cls0 (by simp)
    | succ k =>
    have hk' : k ≤ 2 ^ 62 := by omega
    obtain ⟨hb, hlen, hv⟩ := ht
    have hl0 : l ≠ 0 := fun e => by rw [e] at hlen; simp at hlen
    rw [checkTypePinsE.arm2 p k m vis o l hl0]
    obtain ⟨v0, v1⟩ := hv 0 (by simp)
    simp only [List.getElem_cons_zero, show (2 : Word) * UInt64.ofNat 0 = 0 from rfl,
      UInt64.add_zero] at v0 v1
    rw [v0]
    have htl := L.Rom.top_lt m
    have hD6 := hD.toDmProg7.toDmProg6
    simp only [checkTypePins]
    -- the stored type
    refine RefE.bindLift (fun _ => checkTypePinsE.k_type_pin_stored.none ..) fun r1 m1 h1 => ?_
    rw [checkTypePinsE.k_type_pin_stored.arm1]
    obtain ⟨x1, a1, hrun1, hS1, hg1, hl1, hx1⟩ :=
      (tps_ref hD6 tp.1.word.toUInt64) k m a r1 m1 ⟨hC.stage, dmWord_lt32 _⟩ h1
    have hCr1 := hkp.call (im_mem _ rfl) h1 hCr
    rw [decI_word] at hrun1
    obtain ⟨hck1, hxt1, hp1, hden1⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a) rfl hrun1
      (ConRon.Bridge.typePinStored_spec a tp.1 q.1 hC.check hd1)
    have c1 : CoreStep V env fe a a1 := ⟨hck1, hxt1, hp1⟩
    have hC1 := StageC.of_core hC hS1 (callW_leafFrame hcl (leaf_mem _ (by decide)) h1) c1
    rw [← hx1] at hden1 hrun1
    have hrd : rdW (m1.arr64 EREC) (o + 1) = tp.2.word.toUInt64 := by
      rw [rdW_erec_grow hg1 (by
        have hlen1 : l.toNat = tps.length + 1 := by simpa using hlen
        obtain ⟨_, h1⟩ := L.Rom.pairIdx (o := o) (i := 0) (by omega)
        simp only [show (2 : Word) * UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at h1
        rw [h1]; omega)]
      exact v1
    rw [hrd]
    refine ⟨_, _, hrun1, ?_⟩
    -- the comparison
    rw [show isDefEqCore V fe checkFuel 0 (decI (r1.headD 0)) tp.2 =
      isDefEqCore V fe checkFuel 0 (decI (r1.headD 0)) (decI tp.2.word.toUInt64) by rw [decI_word]]
    refine RefE.bindCall (fun _ => checkTypePinsE.k_is_def_eq_core.eq_1 ..)
      (fun hcE _ h2 => hcE.isDefEqCore k hk' hC1.stageT 0 (r1.headD 0) tp.2.word.toUInt64 hl1
        (dmWord_lt32 _) _ h2)
      (fun b h2 => hq.isDefEqCore_sim k hk' hC1.stageT 0 (r1.headD 0) tp.2.word.toUInt64 hl1
        (dmWord_lt32 _) b.1 b.2 h2)
      fun r2 m2 x2 a2 h2 hrun2 ⟨hT2, hg2, hd2'⟩ => ?_
    have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hCr1
    have hq1 := hcl' q (by simp)
    obtain ⟨hck2, hx2', hp2, -⟩ := defeq_check henv hC1.check hden1
      (by rw [decI_word]; exact ConRon.Bridge.denote_ext hd2 c1.ext)
      (ConLeche.Expr.WScoped.of_not_hasFvar hq1.1) (ConLeche.Expr.WScoped.of_not_hasFvar hq1.2) hrun2
    have c2 : CoreStep V env fe a1 a2 := ⟨hck2, hx2', hp2⟩
    have hC2 := StageC.of_T hT2 hck2
    have hG2 : IWGrow m m2 := hg1.trans hg2
    rw [checkTypePinsE.k_is_def_eq_core.eq_2]
    refine RefE.retIf (fun z2 => hd2' ▸ decBool_f_m2c z2) (fun hb => by simpa [← hd2', decBool] using hb)
      (fun _ => ⟨hC2, c1.trans c2, hG2, by simp [decW0B], hCr2⟩) fun z2 _ => ?_
    have hlen' : l.toNat = tps.length + 1 := by simpa using hlen
    have hrest : L.Rom.TPinsR m2 (o + 2) (l - 1) tps := by
      have hl1' : (l - 1).toNat = l.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
      have ho2 : (o + 2).toNat = o.toNat + 2 := L.Rom.addN (by simp; omega)
      refine L.Rom.TPinsR.keep ⟨by rw [ho2, hl1']; omega, by rw [hl1']; omega,
        fun i hi => ?_⟩ ⟨hG2.er, hG2.erGet⟩
      have := hv (i + 1) (by simpa using hi)
      simp only [List.getElem_cons_succ] at this
      have e : o + 2 * UInt64.ofNat (i + 1) = o + 2 + 2 * UInt64.ofNat i := by
        rw [UInt64.ofNat_add, UInt64.ofNat_one, UInt64.mul_add, UInt64.mul_one]; ac_rfl
      rw [e] at this
      exact this
    refine (ih qs (o + 2) (l - 1) k hk' m2 a2 hC2 hCr2 hrest
      (ConRon.Bridge.TypePinsDenote.mono (c1.trans c2).ext _ _ hd3)
      (fun r hr => hcl' r (by simp [hr]))).mono ?_
    exact fun _ _ _ hR => ⟨hR.stage, (c1.trans c2).trans hR.core, hG2.trans hR.grow, hR.res, hR.cr⟩

end typePins

l_model checkDivModPinValue_specE (p : Prog)
  (hf : p.lookup "check_div_mod_pin_value" = some checkDivModPinValueL)
  (hc : p.lookup "check_div_mod_certs" = some checkDivModCertsL)
  fns [hf ↦ checkDivModPinValueE]
  specs [callW_spec p n "div_mod_decl_pin", callW_spec p n "div_mod_cert_stmts",
    callW_spec p n "div_mod_cert_proofs", checkDivModCerts_specE p hc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section pinValue
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_div_mod_pin_value` refines `checkDivModPinValue` under `StageC`, both outcomes** (the
second half of con-ron's `checkDivModPinAt_bridge`, which takes the pin guard's `true` for the
pin's scope). -/
theorem cpv_ref (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    {c value ps : Word} {ip : INatOpPinSet} {psP : ConLeche.NatOpPinSet} {nm : ConLeche.Name}
    {v : ConLeche.Expr} {k : Nat} (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hC : StageC dn vis fe env m a) (hc : H c) (hval : H value) (hP : PinSetR m ps ip)
    (hps : PinSetDenote a.store ip psP) (hn : denoteN a.store.ns (decI c) = some nm)
    (hv : denoteE a.store (decE value) = some v) (hwsv : ConLeche.Expr.WScoped 0 v)
    (hpg : ConLeche.divModPinGuard psP env nm = true) (hCr : L.Stubs.CrOK m) :
    RefE (CoreStubsE p) (checkDivModPinValueE p k m vis c value ps)
      (checkDivModPinValue V fe (decI c) (decE value) ip) a
      (fun v x a' => DmPost dn vis fe env m a v.1 v.2 x a') := by
  cases k with
  | zero => rw [checkDivModPinValueE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  rw [checkDivModPinValueE.arm1]
  have hD5 := hD.toDmProg7.toDmProg6.toDmProg5
  have hwsP : ConLeche.Expr.WScoped 0 (ConLeche.divModDeclPin psP nm) := by
    simp only [ConLeche.divModPinGuard, Bool.and_eq_true, Bool.not_eq_true'] at hpg
    exact ConLeche.Expr.WScoped.of_not_hasFvar hpg.1.1.1.2
  simp only [checkDivModPinValue]
  -- the pin
  refine RefE.bindLift (fun _ => rfl) fun r1 m1 h1 => ?_
  obtain ⟨x1, a1, hrun1, hS1, hg1, hl1, hx1⟩ :=
    (divModDeclPin_ref hD5.toDmProg2.toDmProg1 ps c ip) k m a r1 m1 ⟨hC.stage, hc, hP⟩ h1
  have hCr1 := hkp.call (im_mem _ rfl) h1 hCr
  obtain ⟨e1, hpd⟩ := ConRon.Bridge.divModDeclPin_run hC.check.state hC.check.pins hps hn hrun1
  rw [e1] at hrun1 hS1
  have hC1 := StageC.of_core hC hS1 (callW_leafFrame hcl (leaf_mem _ (by decide)) h1)
    (CoreStep.refl hC.check)
  rw [← hx1] at hpd
  refine ⟨_, _, (by rw [hx1]; exact hrun1 :
    (divModDeclPin ip (decI c)).run a = .ok (decI (r1.headD 0), a)), ?_⟩
  dsimp only [checkDivModPinValueE.k_div_mod_decl_pin]
  -- the value against the pin
  refine RefE.bindCall (fun _ => rfl)
    (fun hcE _ h2 => hcE.isDefEqCore k hk' hC1.stageT 0 value (r1.headD 0) hval hl1 _ h2)
    (fun b h2 => hq.isDefEqCore_sim k hk' hC1.stageT 0 value (r1.headD 0) hval hl1 b.1 b.2 h2)
    fun r2 m2 x2 a2 h2 hrun2 ⟨hT2, hg2, hd2⟩ => ?_
  have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hCr1
  obtain ⟨hck2, hx2', hp2, -⟩ := defeq_check henv hC1.check hv hpd hwsv hwsP hrun2
  have c2 : CoreStep V env fe a a2 := ⟨hck2, hx2', hp2⟩
  have hC2 := StageC.of_T hT2 hck2
  rw [checkDivModPinValueE.k_is_def_eq_core.eq_2]
  refine RefE.retIf (fun z2 => hd2 ▸ decBool_f_m2c z2) (fun hb => by simpa [← hd2, decBool] using hb)
    (fun _ => ⟨hC2, c2, hg1.trans hg2, by simp [decW0B], hCr2⟩) fun z2 _ => ?_
  -- the statements and the proofs
  refine RefE.bindSim (fun _ => rfl) ((divModCertStmts_ref hD5.toDmProg2 c) k m2 a2 · · ⟨hC2.stage, hc⟩ ·)
    fun r3 x3 m3 a3 h3 hrun3 ⟨hS3, hg3, hd3⟩ => ?_
  dsimp only [checkDivModPinValueE.k_div_mod_cert_stmts]
  have hCr3 := hkp.call (im_mem _ rfl) h3 hCr2
  have hn2 := ConRon.Bridge.denoteN_ext hn c2.ext
  obtain ⟨hi3, hsd⟩ := ConRon.Bridge.divModCertStmts_run hC2.check.state hC2.check.pins hn2 hrun3
  have c3 := ConRon.Bridge.CoreStep.of_istep hC2.check hi3
  have hC3 := StageC.of_core hC2 hS3 (callW_leafFrame hcl (leaf_mem _ (by decide)) h3) c3
  have c03 := c2.trans c3
  refine RefE.bindLift (fun _ => rfl) fun r4 m4 h4 => ?_
  obtain ⟨x4, a4, hrun4, hS4, hg4, hd4⟩ :=
    (divModCertProofs_ref hD5.toDmProg2.toDmProg1 ps c ip) k m3 a3 r4 m4
      ⟨hS3, hc, PinSetR.grow (PinSetR.grow hP hg1) (hg2.trans hg3)⟩ h4
  have hCr4 := hkp.call (im_mem _ rfl) h4 hCr3
  have hps3 := (ConRon.Bridge.PinsDenote.mono c03.ext [ip] [psP] ⟨hps, trivial⟩).1
  have hn3 := ConRon.Bridge.denoteN_ext hn c03.ext
  obtain ⟨e4, hpr⟩ := ConRon.Bridge.divModCertProofs_run hC3.check.state hC3.check.pins hps3 hn3
    hrun4
  rw [e4] at hrun4 hS4
  have hC4 := StageC.of_core hC3 hS4 (callW_leafFrame hcl (leaf_mem _ (by decide)) h4)
    (CoreStep.refl hC3.check)
  refine ⟨_, _, hrun4, ?_⟩
  dsimp only [checkDivModPinValueE.k_div_mod_cert_proofs]
  -- the certificates
  simp only [decStmtL, ntGetD0, ntGetD1] at hd3
  unfold decRL at hd4
  simp only [Nat.zero_add, ntGetD0, ntGetD1] at hd4
  refine (cm_ref hD hq hcl hkp hs0 hsA henv c value hc hval hwsv x3 _ x4 _ (r3.headD 0)
    (r3.tail.headD 0) (r4.headD 0) (r4.tail.headD 0) k hk' m4 a3 hC4 hCr4 (hd3.grow hg4) hd4.1
    hd4.2 hn3 (ConRon.Bridge.denote_ext hv c03.ext) hsd hpr
    (ConRon.Bridge.divModCertStmts_wscoped nm)).mono ?_
  exact fun _ _ _ hR => ⟨hR.stage, c03.trans hR.core,
    hg1.trans (hg2.trans (hg3.trans (hg4.trans hR.grow))), hR.res, hR.cr⟩

end pinValue

l_model checkDivModPinAt_specE (p : Prog)
  (hf : p.lookup "check_div_mod_pin_at" = some checkDivModPinAtL)
  (ht : p.lookup "check_type_pins" = some checkTypePinsL)
  (hv : p.lookup "check_div_mod_pin_value" = some checkDivModPinValueL)
  (hc : p.lookup "check_div_mod_certs" = some checkDivModCertsL)
  fns [hf ↦ checkDivModPinAtE]
  specs [callW_spec p n "div_mod_type_pins", checkTypePins_specE p ht n,
    checkDivModPinValue_specE p hv hc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section pinAt
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_div_mod_pin_at` refines `checkDivModPinAt` under `StageC`, both outcomes** (con-ron's
`checkDivModPinAt_bridge`, which takes the pin guard's `true` for the type pins' and the pin's
scope): the type pins (`ctp_ref`), then the value pin and the certificates (`cpv_ref`). -/
theorem cpa_ref (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    {c value ps : Word} {ip : INatOpPinSet} {psP : ConLeche.NatOpPinSet} {nm : ConLeche.Name}
    {v : ConLeche.Expr} {k : Nat} (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hC : StageC dn vis fe env m a) (hc : H c) (hval : H value) (hP : PinSetR m ps ip)
    (hps : PinSetDenote a.store ip psP) (hn : denoteN a.store.ns (decI c) = some nm)
    (hv : denoteE a.store (decE value) = some v) (hwsv : ConLeche.Expr.WScoped 0 v)
    (hpg : ConLeche.divModPinGuard psP env nm = true) (hCr : L.Stubs.CrOK m) :
    RefE (CoreStubsE p) (checkDivModPinAtE p k m vis c value ps)
      (checkDivModPinAt V fe (decI c) (decE value) ip) a
      (fun v x a' => DmPost dn vis fe env m a v.1 v.2 x a') := by
  cases k with
  | zero => rw [checkDivModPinAtE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  rw [checkDivModPinAtE.arm1]
  have hD1 := hD.toDmProg7.toDmProg6.toDmProg5.toDmProg2.toDmProg1
  simp only [checkDivModPinAt]
  -- the type pins
  refine RefE.bindSim (fun _ => rfl) ((divModTypePins_ref hD1 ps c ip) k m a · · ⟨hC.stage, hc, hP⟩ ·)
    fun r1 x1 m1 a1 h1 hrun1 ⟨hS1, hg1, hd1⟩ => ?_
  dsimp only [checkDivModPinAtE.k_div_mod_type_pins]
  have hCr1 := hkp.call (im_mem _ rfl) h1 hCr
  obtain ⟨e1, htd⟩ := ConRon.Bridge.divModTypePins_run hC.check.state hC.check.pins hps hn hrun1
  subst a1
  have hC1 := StageC.of_core hC hS1 (callW_leafFrame hcl (leaf_mem _ (by decide)) h1)
    (CoreStep.refl hC.check)
  refine RefE.bindE (fun _ => rfl) id (ctp_ref hD hq hcl hkp henv x1 _ _ _ k hk' m1 a hC1 hCr1 hd1 htd
    (ConRon.Bridge.divModTypePins_closed hpg)) fun ⟨r2, m2⟩ x2 a2 _ hR2 => ?_
  rw [checkDivModPinAtE.k_check_type_pins.eq_2]
  refine RefE.retIf (fun z2 => decW0B_false hR2.res (by simpa using z2))
    (fun hb => by have := hR2.res; grind [decW0B])
    (fun _ => ⟨hR2.stage, hR2.core, hg1.trans hR2.grow, by simp [decW0B], hR2.cr⟩) fun z2 _ => ?_
  -- the value pin and the certificates
  refine (cpv_ref hD hq hcl hkp hs0 hsA henv hk' hR2.stage hc hval
    (PinSetR.grow hP (hg1.trans hR2.grow))
    (ConRon.Bridge.PinsDenote.mono hR2.core.ext [ip] [psP] ⟨hps, trivial⟩).1
    (ConRon.Bridge.denoteN_ext hn hR2.core.ext) (ConRon.Bridge.denote_ext hv hR2.core.ext) hwsv hpg
    hR2.cr).mono ?_
  exact fun _ _ _ hR => ⟨hR.stage, hR2.core.trans hR.core, hg1.trans (hR2.grow.trans hR.grow), hR.res, hR.cr⟩

end pinAt

/-! ## The ok halves from the run (the census links) -/

section okRuns
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_div_mod_certs` under `StageC`** from the call's run (`cm_ref`'s ok half). -/
@[refines ConRon.Arena.checkDivModCerts]
theorem cmC (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    (c annVal : Word) (hc : H c) (hann : H annVal) {nm : ConLeche.Name} {v : ConLeche.Expr}
    (hwsv : ConLeche.Expr.WScoped 0 v) {ss : List (List EIdx × EIdx)}
    {xs : List (List ConLeche.Expr × ConLeche.Expr)} {proofs : List EIdx} {ps : List ConLeche.Expr}
    {so sl po pl : Word} {k : Nat} (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState} {res : List Word}
    {m' : Mem} (hC : StageC dn vis fe env m a) (hCr : L.Stubs.CrOK m)
    (hs : StmtL m so.toNat sl.toNat ss) (hd : decHL m po.toNat pl.toNat = some proofs)
    (hb : po.toNat + pl.toNat ≤ iwTop m) (hn : denoteN a.store.ns (decI c) = some nm)
    (hv : denoteE a.store (decE annVal) = some v) (hsd : ConRon.Bridge.StmtsDenote a.store ss xs)
    (hpr : Frontend.denoteEList a.store proofs = some ps)
    (hwq : ∀ q ∈ xs, (∀ h ∈ q.1, ConLeche.Expr.WScoped 2 h) ∧ ConLeche.Expr.WScoped 2 q.2)
    (hcall : callW p k "check_div_mod_certs" [vis, c, annVal, so, sl, po, pl] m = some (res, m')) :
    ∃ x a', (checkDivModCerts V fe (decI c) (decE annVal) ss proofs).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ CoreStep V env fe a a' ∧ IWGrow m m' ∧ decW0B m' res x := by
  obtain ⟨s', rfl, -, x, a', hrun, hR⟩ := RefE.run_okW (s₀ := ⟨m, Locals.init []⟩)
    (checkDivModCerts_specE p hD.lCheckDivModCerts k _ vis c annVal so sl po pl)
    (cm_ref hD hq hcl hkp hs0 hsA henv c annVal hc hann hwsv ss xs proofs ps so sl po pl k hk m a
      hC hCr hs hd hb hn hv hsd hpr hwq) hcall
  exact ⟨x, a', hrun, hR.stage, hR.core, hR.grow, by simpa [decW0B] using hR.res⟩

/-- **`check_div_mod_pin_value` under `StageC`** from the call's run (`cpv_ref`'s ok half). -/
@[refines ConRon.Arena.checkDivModPinValue]
theorem cpvC (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    {c value ps : Word} {ip : INatOpPinSet} {psP : ConLeche.NatOpPinSet} {nm : ConLeche.Name}
    {v : ConLeche.Expr} {k : Nat} (hk : k ≤ 2 ^ 62) {m m' : Mem} {a : AState} {r : List Word}
    (hcall : callW p k "check_div_mod_pin_value" [vis, c, value, ps] m = some (r, m'))
    (hC : StageC dn vis fe env m a) (hc : H c) (hval : H value) (hP : PinSetR m ps ip)
    (hps : PinSetDenote a.store ip psP) (hn : denoteN a.store.ns (decI c) = some nm)
    (hv : denoteE a.store (decE value) = some v) (hwsv : ConLeche.Expr.WScoped 0 v)
    (hpg : ConLeche.divModPinGuard psP env nm = true) (hCr : L.Stubs.CrOK m) :
    ∃ x a', (checkDivModPinValue V fe (decI c) (decE value) ip).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ CoreStep V env fe a a' ∧ IWGrow m m' ∧ decW0B m' r x := by
  obtain ⟨s', rfl, -, x, a', hrun, hR⟩ := RefE.run_okW (s₀ := ⟨m, Locals.init []⟩)
    (checkDivModPinValue_specE p hD.lCheckDivModPinValue hD.lCheckDivModCerts k _ vis c value ps)
    (cpv_ref hD hq hcl hkp hs0 hsA henv hk hC hc hval hP hps hn hv hwsv hpg hCr) hcall
  exact ⟨x, a', hrun, hR.stage, hR.core, hR.grow, by simpa [decW0B] using hR.res⟩

/-- **`check_div_mod_pin_at` under `StageC`** from the call's run (`cpa_ref`'s ok half). -/
@[refines ConRon.Arena.checkDivModPinAt]
theorem cpaC (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    {c value ps : Word} {ip : INatOpPinSet} {psP : ConLeche.NatOpPinSet} {nm : ConLeche.Name}
    {v : ConLeche.Expr} {k : Nat} (hk : k ≤ 2 ^ 62) {m m' : Mem} {a : AState} {r : List Word}
    (hcall : callW p k "check_div_mod_pin_at" [vis, c, value, ps] m = some (r, m'))
    (hC : StageC dn vis fe env m a) (hc : H c) (hval : H value) (hP : PinSetR m ps ip)
    (hps : PinSetDenote a.store ip psP) (hn : denoteN a.store.ns (decI c) = some nm)
    (hv : denoteE a.store (decE value) = some v) (hwsv : ConLeche.Expr.WScoped 0 v)
    (hpg : ConLeche.divModPinGuard psP env nm = true) (hCr : L.Stubs.CrOK m) :
    ∃ x a', (checkDivModPinAt V fe (decI c) (decE value) ip).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ CoreStep V env fe a a' ∧ IWGrow m m' ∧ decW0B m' r x := by
  obtain ⟨s', rfl, -, x, a', hrun, hR⟩ := RefE.run_okW (s₀ := ⟨m, Locals.init []⟩)
    (checkDivModPinAt_specE p hD.lCheckDivModPinAt hD.lCheckTypePins hD.lCheckDivModPinValue
      hD.lCheckDivModCerts k _ vis c value ps)
    (cpa_ref hD hq hcl hkp hs0 hsA henv hk hC hc hval hP hps hn hv hwsv hpg hCr) hcall
  exact ⟨x, a', hrun, hR.stage, hR.core, hR.grow, by simpa [decW0B] using hR.res⟩

end okRuns

end L.Ind
