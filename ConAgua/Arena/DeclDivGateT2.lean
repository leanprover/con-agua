import ConAgua.Arena.DeclDivGateT1
import ConAgua.Arena.DeclDivModSpec.CmW
import ConAgua.Arena.DeclDivModSpec.RomPinSets
import ConAgua.Arena.DeclCrpT
import ConAgua.Census.Attr

/-!
# The `Nat.div`-family pin gate under `StageC`, part 2: the attempt (lane `loopt3`, `loopt3-div`)

`check_div_mod_certs` (`cmC`), `check_type_pins` (`ctpC`), `check_div_mod_pin_value` (`cpvC`),
`check_div_mod_pin_at` (`cpaC`) and the variant loop (`loopC`) from the real program: the core calls `infer_type_core`, `is_def_eq_core`
by the knot's `StageT` sims (`KnotStageProg`) and `CheckOK` after from con-ron's `KnotSpec`
(`StageC.of_T`), the leaves as in part 1. The twin side follows con-ron's
`checkDivModCerts_bridge_aux`, `checkTypePins_spec`, `checkDivModPinAt_bridge` and
`checkDivModPinLoop_bridge`.
-/

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

section certs
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_div_mod_certs` under `StageC`** (`cm_ref`'s at the real program; con-ron's
`checkDivModCerts_bridge_aux`). -/
@[refines ConRon.Arena.checkDivModCerts]
theorem cmC (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    (c annVal : Word) (hc : H c) (hann : H annVal) {nm : ConLeche.Name} {v : ConLeche.Expr}
    (hwsv : ConLeche.Expr.WScoped 0 v) :
    ∀ (ss : List (List EIdx × EIdx)) (xs : List (List ConLeche.Expr × ConLeche.Expr))
      (proofs : List EIdx) (ps : List ConLeche.Expr) (so sl po pl : Word) (k : Nat), k ≤ 2 ^ 62 →
      ∀ (m : Mem) (a : AState) (res : List Word) (m' : Mem), StageC dn vis fe env m a →
      L.Stubs.CrOK m →
      StmtL m so.toNat sl.toNat ss → decHL m po.toNat pl.toNat = some proofs →
      po.toNat + pl.toNat ≤ iwTop m → denoteN a.store.ns (decI c) = some nm →
      denoteE a.store (decE annVal) = some v → ConRon.Bridge.StmtsDenote a.store ss xs →
      Frontend.denoteEList a.store proofs = some ps →
      (∀ q ∈ xs, (∀ h ∈ q.1, ConLeche.Expr.WScoped 2 h) ∧ ConLeche.Expr.WScoped 2 q.2) →
      cmW p (realCall p) k m vis c annVal so sl po pl = some (res, m') →
      ∃ x a', (checkDivModCerts V fe (decI c) (decE annVal) ss proofs).run a = .ok (x, a') ∧
        StageC dn vis fe env m' a' ∧ CoreStep V env fe a a' ∧ IWGrow m m' ∧ decW0B m' res x := by
  have hws4 : ConLeche.Expr.WScoped 4 v := ConLeche.Expr.WScoped.mono (by omega) hwsv
  have hws2 : ConLeche.Expr.WScoped 2 v := ConLeche.Expr.WScoped.mono (by omega) hwsv
  intro ss
  induction ss with
  | nil =>
    intro xs proofs ps so sl po pl k hk m a res m' hC _ hs hd hb hn hv hsd hpr hwq hw
    have hsl : sl = 0 := UInt64.toNat_inj.mp (by have := hs.2.1; simpa using this)
    unfold cmW at hw
    cases proofs with
    | nil =>
      have hpl : pl = 0 := UInt64.toNat_inj.mp (by have := decHL_length m hd; simp at this ⊢; omega)
      simp only [hsl, hpl, and_self, ite_true, Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨true, a, rfl, hC, CoreStep.refl hC.check, IWGrow.refl _, by simp [decW0B]⟩
    | cons pf pfs =>
      have hpl : pl ≠ 0 := fun e => by
        have := decHL_length m hd; rw [e] at this; simp at this
      rw [ite_eq_right (fun h => hpl h.2), ite_eq_left (Or.inl hsl)] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨false, a, rfl, hC, CoreStep.refl hC.check, IWGrow.refl _, by simp [decW0B]⟩
  | cons st ss ih =>
    rcases st with ⟨hy, eqq⟩
    intro xs proofs ps so sl po pl k hk m a res m' hC hCr hs hd hb hn hv hsd hpr hwq hw
    have hS := hC.stage
    cases xs with
    | nil => exact hsd.elim
    | cons xq xrest =>
    obtain ⟨hx, ex⟩ := xq
    obtain ⟨hsd1, hsd2, hsd3⟩ := hsd
    obtain ⟨hwh, hwe⟩ := hwq (hx, ex) (by simp)
    unfold cmW at hw
    obtain ⟨hsl0, q, hq0, hstm, hrest⟩ := StmtL.cons hS.2 hs
    cases proofs with
    | nil =>
      have hpl : pl = 0 := UInt64.toNat_inj.mp (by have := decHL_length m hd; simp at this ⊢; omega)
      simp only [hpl, and_true, or_true, hsl0, ite_false, ite_true, Option.some.injEq,
        Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨false, a, rfl, hC, CoreStep.refl hC.check, IWGrow.refl _, by simp [decW0B]⟩
    | cons pf pfs =>
    obtain ⟨px, pxs, hpx, hpxs, rfl⟩ := ConRon.Bridge.denoteEList_cons hpr
    obtain ⟨hpl0, hpwlt, hpf, hdrest⟩ := decHL_cons_iw hS.2.2.2.1 hd
    subst hpf
    obtain ⟨ho, hl, e, hr3, hbd, hdh, he, hst2⟩ := hstm
    obtain ⟨hp3, h0, h1, h2⟩ := hr3
    have hst2' : eqq = decE e := hst2
    subst hst2'
    rw [ite_eq_right (fun h => hsl0 h.1), ite_eq_right (by rintro (h | h); exact hsl0 h; exact hpl0 h)] at hw
    have hsz := hS.2.2.2.1
    have hI1 := hS.2.1
    have r0 : rdW (m.arr64 IW) so = q := hq0
    have rq1 : rdW (m.arr64 IW) q = ho := rdW_iw_of h0 rfl
    have rq2 : rdW (m.arr64 IW) (q + 1) = hl := rdW_iw_of h1 (word_add_one (by omega))
    have rq3 : rdW (m.arr64 IW) (q + 2) = e := rdW_iw_of h2 (word_add_two (by omega))
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
    rw [r0, rq1, rq2, rq3] at hw
    -- the guard
    replace hw := ntBW_some hw; obtain ⟨r1, m1, h1', hw⟩ := hw
    obtain ⟨x1, a1, hrun1, hC1, c1, hg1, hd1, hxv1⟩ :=
      cgC hD.toDmProg7.toDmProg6.toDmProg5 hcl hkp hs0 hsA h1' hC hc hann he hpwlt hdh hbd hn hv hsd1
        hsd2 hpx hCr
    have hCr1 := hkp.call (im_mem _ rfl) h1' hCr
    have hrun1' : (divModCertGuard fe (decI c) (decE annVal) hy (decE e)
        (decI (rdW (m.arr64 IW) po))).run a = .ok (x1, a1) := hrun1
    by_cases z1 : r1.headD 0 = 0
    · rw [ite_eq_left z1] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx1 := decW0B_false hd1 z1
      refine ⟨false, a1, ?_, hC1, c1, hg1, decW0B_of_false _⟩
      simp only [checkDivModCerts, StateT.run_bind, hrun1', exc_ok_bind', hx1, Bool.false_eq_true,
        ite_false]
      rfl
    rw [ite_eq_right z1] at hw
    have hx1 := decW0B_true hd1 z1
    have hg' : ConLeche.divModCertGuard env nm v hx ex px = true := by rw [← hxv1, hx1]
    simp only [ConLeche.divModCertGuard, Bool.and_eq_true, Bool.not_eq_true'] at hg'
    have hPf : (ConLeche.Expr.substConstAll nm v px).hasFvar = false := hg'.1.1.1.1.2
    have hn1 := ConRon.Bridge.denoteN_ext hn c1.ext
    have hv1 := ConRon.Bridge.denote_ext hv c1.ext
    -- the substituted proof
    rw [iw_rd_grow hg1 hpo] at hw
    replace hw := ntBW_some hw; obtain ⟨r2, m2, h2', hw⟩ := hw
    have hCr2 := hkp.call (im_mem _ rfl) h2' hCr1
    obtain ⟨x2, a2, hrun2, hS2, hg2, hl2, hx2⟩ := hsA c annVal _ hc hann hpwlt k m1 a1 r2 m2 hC1.stage h2'
    subst hx2
    obtain ⟨hi2, hpd⟩ := ConRon.Bridge.substConstAll_run coreWalkFuel hC1.check.state
      hC1.check.pins hn1 hv1 (ConRon.Bridge.denote_ext hpx c1.ext) hrun2
    have c2 := ConRon.Bridge.CoreStep.of_istep hC1.check hi2
    have hC2 := StageC.of_core hC1 hS2 (callW_leafFrame hcl (leaf_mem _ (by decide)) h2') c2
    have c02 := c1.trans c2
    have hG2 : IWGrow m m2 := hg1.trans hg2
    -- the substituted hypotheses
    rw [iw_rd_grow hG2 hq0', rq1, iw_rd_grow hG2 hq1, rq2] at hw
    replace hw := ntBW_some hw; obtain ⟨r3, m3, h3', hw⟩ := hw
    have hdh2 : decHL m2 ho.toNat hl.toNat = some hy := by rw [decHL_grow hG2 hbd]; exact hdh
    have hCr3 := hkp.call (im_mem _ rfl) h3' hCr2
    obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := sc0List_ref hD.toDmProg7.toDmProg6.toDmProg5 hs0 c
      annVal hc hann hy ho hl k m2 a2 r3 m3 hC2.stage hdh2 (Nat.le_trans hbd hG2.1) h3'
    simp only [decRL, Nat.zero_add, ntGetD0, ntGetD1] at hd3
    obtain ⟨hi3, hhs⟩ := ConRon.Bridge.substConst0List_run hy hx hC2.check.state hC2.check.pins
      (ConRon.Bridge.denoteN_ext hn c02.ext) (ConRon.Bridge.denote_ext hv c02.ext)
      (ConRon.Bridge.denoteEList_ext c02.ext _ _ hsd1) hrun3
    have c3 := ConRon.Bridge.CoreStep.of_istep hC2.check hi3
    have hC3 := StageC.of_core hC2 hS3 (callW_leafFrame hcl (leaf_mem _ (by decide)) h3') c3
    have c03 := c02.trans c3
    have hG3 : IWGrow m m3 := hG2.trans hg3
    -- the application
    obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4, rfl⟩, hf4, hCr4, hw⟩ :=
      (applied_ref (dn := dn) (vis := vis) (fe := fe) hD.toDmProg7.toDmProg6.toDmProg5 (r2.headD 0)
        (r3.headD 0) (r3.tail.headD 0) x3).bindLC hcl (leaf_mem _ (by decide)) hkp (im_mem _ rfl)
        ⟨hC3.stage, hl2, hd3.1, hd3.2⟩ hCr3 hw
    obtain ⟨hi4, hap0⟩ := ConRon.Bridge.divModCertApplied_run hC3.check.state hC3.check.pins
      (ConRon.Bridge.denote_ext hpd hi3.ext) hhs hrun4
    have c4 := ConRon.Bridge.CoreStep.of_istep hC3.check hi4
    have hC4 := StageC.of_core hC3 hS4 hf4 c4
    have c04 := c03.trans c4
    have hG4 : IWGrow m m4 := hG3.trans hg4
    have hwsA : ConLeche.Expr.WScoped 4 (ConLeche.divModCertApplied
        (ConLeche.Expr.substConstAll nm v px) (hx.map (ConLeche.Expr.substConst0 nm v))) := by
      refine ConRon.Bridge.divModCertApplied_wscoped hPf fun h hh => ?_
      obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh
      exact ConRon.Bridge.substConst0_wscoped hws2 _ (hwh h0 hh0)
    -- the type
    cases k with
    | zero => simp [realCall, callW_zero] at hw
    | succ k' =>
    have hk' : k' + 1 ≤ 2 ^ 62 := hk
    cases h5 : realCall p (k' + 1) "infer_type_core" [vis, 4, r4.headD 0] m4 with
    | none => rw [h5] at hw; simp at hw
    | some q5 =>
    obtain ⟨r5, m5⟩ := q5
    rw [h5, bW_some] at hw
    have hCr5 := hkp.call (im_mem _ rfl) h5 hCr4
    obtain ⟨x5, a5, hrun5, hT5, hg5, hl5, hx5⟩ :=
      hq.inferTypeCore_sim (k' + 1) hk' hC4.stageT 4 (r4.headD 0) hl4 r5 m5 h5
    subst hx5
    have h4w : (4 : Word).toNat = 4 := rfl
    rw [h4w] at hrun5
    obtain ⟨hck5, hx5', hp5, tpx, htp5, hwstp, -⟩ := infer_check henv hC4.check hap0 hwsA hrun5
    have c5 : CoreStep V env fe a4 a5 := ⟨hck5, hx5', hp5⟩
    have hC5 := StageC.of_T hT5 hck5
    have c05 := c04.trans c5
    have hG5 : IWGrow m m5 := hG4.trans hg5
    -- the equation, substituted
    rw [iw_rd_grow hG5 hq2, rq3] at hw
    replace hw := ntBW_some hw; obtain ⟨r6, m6, h6, hw⟩ := hw
    have hCr6 := hkp.call (im_mem _ rfl) h6 hCr5
    obtain ⟨x6, a6, hrun6, hS6, hg6, hl6, hx6⟩ :=
      hs0 c annVal e hc hann he (k' + 1) m5 a5 r6 m6 hC5.stage h6
    subst hx6
    obtain ⟨hi6, hrhs⟩ := ConRon.Bridge.substConst0_run coreWalkFuel hC5.check.state hC5.check.pins
      (ConRon.Bridge.denoteN_ext hn c05.ext) (ConRon.Bridge.denote_ext hv c05.ext)
      (ConRon.Bridge.denote_ext hsd2 c05.ext) hrun6
    have c6 := ConRon.Bridge.CoreStep.of_istep hC5.check hi6
    have hC6 := StageC.of_core hC5 hS6 (callW_leafFrame hcl (leaf_mem _ (by decide)) h6) c6
    have hG6 : IWGrow m m6 := hG5.trans hg6
    have hwsR : ConLeche.Expr.WScoped 4 (ConLeche.Expr.substConst0 nm v ex) :=
      ConRon.Bridge.substConst0_wscoped hws4 _ (ConLeche.Expr.WScoped.mono (by omega) hwe)
    -- the comparison
    cases h7 : realCall p (k' + 1) "is_def_eq_core" [vis, 4, r5.headD 0, r6.headD 0] m6 with
    | none => rw [h7] at hw; simp at hw
    | some q7 =>
    obtain ⟨r7, m7⟩ := q7
    rw [h7, bW_some] at hw
    have hCr7 := hkp.call (im_mem _ rfl) h7 hCr6
    obtain ⟨x7, a7, hrun7, hT7, hg7, hd7⟩ :=
      hq.isDefEqCore_sim (k' + 1) hk' hC6.stageT 4 (r5.headD 0) (r6.headD 0) hl5 hl6 r7 m7 h7
    rw [h4w] at hrun7
    obtain ⟨hck7, hx7', hp7, -⟩ := defeq_check henv hC6.check
      (ConRon.Bridge.denote_ext htp5 hi6.ext) hrhs hwstp hwsR hrun7
    have c7 : CoreStep V env fe a6 a7 := ⟨hck7, hx7', hp7⟩
    have hC7 := StageC.of_T hT7 hck7
    have c07 := (c05.trans c6).trans c7
    have hG7 : IWGrow m m7 := hG6.trans hg7
    have hrun4' : (divModCertApplied (decI (r2.headD 0)) x3).run a3 =
        .ok (decI (r4.headD 0), a4) := hrun4
    have hrun2' : (substConstAll (decI c) (decE annVal) coreWalkFuel
        (decI (rdW (m.arr64 IW) po))).run a1 = .ok (decI (r2.headD 0), a2) := hrun2
    have hrun6' : (substConst0 (decI c) (decE annVal) coreWalkFuel (decE e)).run a5 =
        .ok (decI (r6.headD 0), a6) := hrun6
    by_cases z7 : r7.headD 0 = 0
    · rw [ite_eq_left z7] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx7 : x7 = false := by rw [← hd7]; unfold decBool; rw [z7]; rfl
      refine ⟨false, a7, ?_, hC7, c07, hG7, decW0B_of_false _⟩
      simp only [checkDivModCerts, StateT.run_bind, hrun1', exc_ok_bind', hx1, ite_true, hrun2',
        hrun3, hrun4', hrun5, hrun6', hrun7, hx7, Bool.false_eq_true, ite_false]
      try rfl
    rw [ite_eq_right z7] at hw
    have hx7 : x7 = true := by rw [← hd7]; simpa [decBool] using z7
    replace hw := ntBW_some hw; obtain ⟨r8, m8, h8, hw⟩ := hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hdr1 : decHL m7 (po + 1).toNat (pl - 1).toNat = some pfs := by
      rw [decHL_grow hG7 (by rw [hpo1, hpl1]; omega)]; exact hdrest
    have hw8 := callW_model (M := fun mq => cmW p (realCall p) k' mq vis c annVal (so + 1) (sl - 1)
      (po + 1) (pl - 1)) (cm_specW p hD.lCheckDivModCerts (realCall p) (realCall_spec p) k' · vis c
      annVal (so + 1) (sl - 1) (po + 1) (pl - 1)) h8
    obtain ⟨x8, a8, hrun8, hC8, c8, hg8, hd8⟩ := ih xrest pfs pxs (so + 1) (sl - 1) (po + 1) (pl - 1)
      k' (by omega) m7 a7 r8 m8 hC7 hCr7 (hrest.grow hG7) hdr1
      (by rw [hpo1, hpl1]; have := hG7.1; omega)
      (ConRon.Bridge.denoteN_ext hn c07.ext) (ConRon.Bridge.denote_ext hv c07.ext)
      (ConRon.Bridge.StmtsDenote.mono c07.ext _ _ hsd3)
      (ConRon.Bridge.denoteEList_ext c07.ext _ _ hpxs)
      (fun q hq => hwq q (List.mem_cons_of_mem _ hq)) hw8
    refine ⟨x8, a8, ?_, hC8, c07.trans c8, hG7.trans hg8, hd8⟩
    simp only [checkDivModCerts, StateT.run_bind, hrun1', exc_ok_bind', hx1, ite_true, hrun2',
      hrun3, hrun4', hrun5, hrun6', hrun7, hx7, ite_true]
    exact hrun8

end certs

/-! ## `check_type_pins` -/

section typePins
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_type_pins` under `StageC`** (con-ron's `checkTypePins_spec`): per pair the stored
type by `tps_ref`, then `is_def_eq_core` by the knot's `StageT` sim, `CheckOK` after from
con-ron's `KnotSpec`; both sides closed by the variant's pin guard (`hcl'`). -/
theorem ctpC (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (henv : ConLeche.EnvWF env) :
    ∀ (tps : List (NIdx × EIdx)) (tpsP : List (ConLeche.Name × ConLeche.Expr)) (o l : Word)
      (k : Nat), k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (res : List Word) (m' : Mem),
      StageC dn vis fe env m a → L.Stubs.CrOK m → L.Rom.TPinsR m o l tps →
      ConRon.Bridge.TypePinsDenote a.store tps tpsP →
      (∀ q ∈ tpsP, (ConLeche.typePinStored env q.1).hasFvar = false ∧ q.2.hasFvar = false) →
      callW p k "check_type_pins" [vis, o, l] m = some (res, m') →
      ∃ x a', (checkTypePins V fe tps).run a = .ok (x, a') ∧ StageC dn vis fe env m' a' ∧
        CoreStep V env fe a a' ∧ IWGrow m m' ∧ decW0B m' res x := by
  intro tps
  induction tps with
  | nil =>
    intro tpsP o l k _ m a res m' hC _ ht hd _ hc'
    have hl : l = 0 := UInt64.toNat_inj.mp (by have := ht.2.1; simpa using this)
    cases k with
    | zero => rw [callW_zero] at hc'; cases hc'
    | succ k =>
    have hw := callW_model (M := fun mq => dmCtpW p (realCall p) k mq vis o l)
      (ctp_specW p hD.lCheckTypePins (realCall p) (realCall_spec p) k · vis o l) hc'
    simp only [dmCtpW, hl, ite_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨true, a, rfl, hC, CoreStep.refl hC.check, IWGrow.refl _, by simp [decW0B]⟩
  | cons tp tps ih =>
    intro tpsP o l k hk m a res m' hC hCr ht hd hcl' hc'
    cases tpsP with
    | nil => exact hd.elim
    | cons q qs =>
    obtain ⟨hd1, hd2, hd3⟩ := hd
    cases k with
    | zero => rw [callW_zero] at hc'; cases hc'
    | succ k =>
    have hk' : k ≤ 2 ^ 62 := by omega
    have hw := callW_model (M := fun mq => dmCtpW p (realCall p) k mq vis o l)
      (ctp_specW p hD.lCheckTypePins (realCall p) (realCall_spec p) k · vis o l) hc'
    unfold dmCtpW at hw
    obtain ⟨hb, hlen, hv⟩ := ht
    have hl0 : l ≠ 0 := fun e => by rw [e] at hlen; simp at hlen
    rw [ite_eq_right hl0] at hw
    obtain ⟨v0, v1⟩ := hv 0 (by simp)
    simp only [List.getElem_cons_zero, show (2 : Word) * UInt64.ofNat 0 = 0 from rfl,
      UInt64.add_zero] at v0 v1
    rw [v0] at hw
    have htl := L.Rom.top_lt m
    have hD6 := hD.toDmProg7.toDmProg6
    -- the stored type
    obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1, hx1⟩, hf1, hCr1, hw⟩ :=
      (tps_ref hD6 tp.1.word.toUInt64).bindLC hcl (leaf_mem _ (by decide)) hkp (im_mem _ rfl)
        ⟨hC.stage, dmWord_lt32 _⟩ hCr hw
    rw [decI_word] at hrun1
    obtain ⟨hck1, hxt1, hp1, hden1⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a) rfl hrun1
      (ConRon.Bridge.typePinStored_spec a tp.1 q.1 hC.check hd1)
    have c1 : CoreStep V env fe a a1 := ⟨hck1, hxt1, hp1⟩
    have hC1 := StageC.of_core hC hS1 hf1 c1
    rw [← hx1] at hden1 hrun1
    -- the pinned type, read after the leaf
    have hrd : rdW (m1.arr64 EREC) (o + 1) = tp.2.word.toUInt64 := by
      rw [rdW_erec_grow hg1 (by
        have hlen1 : l.toNat = tps.length + 1 := by simpa using hlen
        obtain ⟨_, h1⟩ := L.Rom.pairIdx (o := o) (i := 0) (by omega)
        simp only [show (2 : Word) * UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at h1
        rw [h1]; omega)]
      exact v1
    rw [hrd] at hw
    -- the comparison
    cases h2 : realCall p k "is_def_eq_core" [vis, 0, r1.headD 0, tp.2.word.toUInt64] m1 with
    | none => rw [h2] at hw; simp at hw
    | some q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [h2, bW_some] at hw
    have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
    obtain ⟨x2, a2, hrun2, hT2, hg2, hd2'⟩ :=
      hq.isDefEqCore_sim k hk' hC1.stageT 0 (r1.headD 0) tp.2.word.toUInt64 hl1 (dmWord_lt32 _)
        r2 m2 h2
    have h0w : (0 : Word).toNat = 0 := rfl
    rw [h0w] at hrun2
    have hq1 := hcl' q (by simp)
    obtain ⟨hck2, hx2', hp2, -⟩ := defeq_check henv hC1.check hden1
      (by rw [decI_word]; exact ConRon.Bridge.denote_ext hd2 c1.ext)
      (ConLeche.Expr.WScoped.of_not_hasFvar hq1.1) (ConLeche.Expr.WScoped.of_not_hasFvar hq1.2) hrun2
    have c2 : CoreStep V env fe a1 a2 := ⟨hck2, hx2', hp2⟩
    have hC2 := StageC.of_T hT2 hck2
    have hrun2' : (isDefEqCore V fe checkFuel 0 (decI (r1.headD 0)) tp.2).run a1 = .ok (x2, a2) := by
      rw [← decI_word tp.2]; exact hrun2
    by_cases z2 : r2.headD 0 = 0
    · rw [ite_eq_left z2] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx2 : x2 = false := by rw [← hd2']; unfold decBool; rw [z2]; rfl
      refine ⟨false, a2, ?_, hC2, c1.trans c2, hg1.trans hg2, decW0B_of_false _⟩
      simp only [checkTypePins, StateT.run_bind, hrun1, exc_ok_bind', hrun2', hx2,
        Bool.false_eq_true, ite_false]
      rfl
    rw [ite_eq_right z2] at hw
    have hx2 : x2 = true := by rw [← hd2']; simpa [decBool] using z2
    replace hw := ntBW_some hw; obtain ⟨r3, m3, h3, hw⟩ := hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hG2 : IWGrow m m2 := hg1.trans hg2
    have hlen' : l.toNat = tps.length + 1 := by simpa using hlen
    have hrest : L.Rom.TPinsR m2 (o + 2) (l - 1) tps := by
      have hl1' : (l - 1).toNat = l.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
      have ho2 : (o + 2).toNat = o.toNat + 2 := L.Rom.addN (by simp; omega)
      refine L.Rom.TPinsR.keep ⟨by rw [ho2, hl1']; omega, by rw [hl1']; omega,
        fun i hi => ?_⟩ ⟨hG2.2.1, hG2.2.2.2⟩
      have := hv (i + 1) (by simpa using hi)
      simp only [List.getElem_cons_succ] at this
      have e : o + 2 * UInt64.ofNat (i + 1) = o + 2 + 2 * UInt64.ofNat i := by
        rw [UInt64.ofNat_add, UInt64.ofNat_one, UInt64.mul_add, UInt64.mul_one]; ac_rfl
      rw [e] at this
      exact this
    obtain ⟨x3, a3, hrun3, hC3, c3, hg3, hd3'⟩ := ih qs (o + 2) (l - 1) k hk' m2 a2 r3 m3 hC2 hCr2
      hrest (ConRon.Bridge.TypePinsDenote.mono (c1.trans c2).ext _ _ hd3)
      (fun r hr => hcl' r (by simp [hr])) h3
    refine ⟨x3, a3, ?_, hC3, (c1.trans c2).trans c3, hG2.trans hg3, hd3'⟩
    simp only [checkTypePins, StateT.run_bind, hrun1, exc_ok_bind', hrun2', hx2, ite_true]
    exact hrun3

end typePins

/-! ## `check_div_mod_pin_value` -/

section pinValue
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_div_mod_pin_value` under `StageC`** (the second half of con-ron's
`checkDivModPinAt_bridge`, which takes the pin guard's `true` for the pin's scope). -/
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
  cases k with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  have hw := callW_model (M := fun mq => dmCpvW p (realCall p) k mq vis c value ps)
    (cpv_specW p hD.lCheckDivModPinValue (realCall p) (realCall_spec p) k · vis c value ps) hcall
  unfold dmCpvW at hw
  have h0w : (0 : Word).toNat = 0 := rfl
  have hD5 := hD.toDmProg7.toDmProg6.toDmProg5
  have hwsP : ConLeche.Expr.WScoped 0 (ConLeche.divModDeclPin psP nm) := by
    simp only [ConLeche.divModPinGuard, Bool.and_eq_true, Bool.not_eq_true'] at hpg
    exact ConLeche.Expr.WScoped.of_not_hasFvar hpg.1.1.1.2
  -- the pin
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1, hx1⟩, hf1, hCr1, hw⟩ :=
    (divModDeclPin_ref hD5.toDmProg2.toDmProg1 ps c ip).bindLC hcl (leaf_mem _ (by decide)) hkp
      (im_mem _ rfl) ⟨hC.stage, hc, hP⟩ hCr hw
  obtain ⟨e1, hpd⟩ := ConRon.Bridge.divModDeclPin_run hC.check.state hC.check.pins hps hn hrun1
  rw [e1] at hrun1 hS1
  have hC1 := StageC.of_core hC hS1 hf1 (CoreStep.refl hC.check)
  rw [← hx1] at hpd
  have hrun1' : (divModDeclPin ip (decI c)).run a = .ok (decI (r1.headD 0), a) := by
    rw [hx1]; exact hrun1
  -- the value against the pin
  cases h2 : realCall p k "is_def_eq_core" [vis, 0, value, r1.headD 0] m1 with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
  obtain ⟨x2, a2, hrun2, hT2, hg2, hd2⟩ :=
    hq.isDefEqCore_sim k hk' hC1.stageT 0 value (r1.headD 0) hval hl1 r2 m2 h2
  rw [h0w] at hrun2
  obtain ⟨hck2, hx2', hp2, -⟩ := defeq_check henv hC1.check hv hpd hwsv hwsP hrun2
  have c2 : CoreStep V env fe a a2 := ⟨hck2, hx2', hp2⟩
  have hC2 := StageC.of_T hT2 hck2
  have hrun2' : (isDefEqCore V fe checkFuel 0 (decE value) (decI (r1.headD 0))).run a =
      .ok (x2, a2) := hrun2
  by_cases z2 : r2.headD 0 = 0
  · rw [ite_eq_left z2] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx2 : x2 = false := by rw [← hd2]; unfold decBool; rw [z2]; rfl
    refine ⟨false, a2, ?_, hC2, c2, hg1.trans hg2, decW0B_of_false _⟩
    simp only [checkDivModPinValue, StateT.run_bind, hrun1', exc_ok_bind', hrun2', hx2,
      Bool.false_eq_true, ite_false]
    rfl
  rw [ite_eq_right z2] at hw
  have hx2 : x2 = true := by rw [← hd2]; simpa [decBool] using z2
  -- the statements and the proofs
  obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hd3⟩, hf3, hCr3, hw⟩ :=
    (divModCertStmts_ref hD5.toDmProg2 c).bindLC hcl (leaf_mem _ (by decide)) hkp (im_mem _ rfl)
      ⟨hC2.stage, hc⟩ hCr2 hw
  have hn2 := ConRon.Bridge.denoteN_ext hn c2.ext
  obtain ⟨hi3, hsd⟩ := ConRon.Bridge.divModCertStmts_run hC2.check.state hC2.check.pins hn2 hrun3
  have c3 := ConRon.Bridge.CoreStep.of_istep hC2.check hi3
  have hC3 := StageC.of_core hC2 hS3 hf3 c3
  have c03 := c2.trans c3
  obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hd4⟩, hf4, hCr4, hw⟩ :=
    (divModCertProofs_ref hD5.toDmProg2.toDmProg1 ps c ip).bindLC hcl (leaf_mem _ (by decide)) hkp
      (im_mem _ rfl) ⟨hS3, hc, PinSetR.grow (PinSetR.grow hP hg1) (hg2.trans hg3)⟩ hCr3 hw
  have hps3 := (ConRon.Bridge.PinsDenote.mono c03.ext [ip] [psP] ⟨hps, trivial⟩).1
  have hn3 := ConRon.Bridge.denoteN_ext hn c03.ext
  obtain ⟨e4, hpr⟩ := ConRon.Bridge.divModCertProofs_run hC3.check.state hC3.check.pins hps3 hn3
    hrun4
  rw [e4] at hrun4 hS4
  have hC4 := StageC.of_core hC3 hS4 hf4 (CoreStep.refl hC3.check)
  -- the certificates
  cases h5 : callW p k "check_div_mod_certs" [vis, c, value, r3.headD 0, r3.tail.headD 0,
      r4.headD 0, r4.tail.headD 0] m4 with
  | none => rw [h5] at hw; simp at hw
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  simp only [decStmtL, ntGetD0, ntGetD1] at hd3
  unfold decRL at hd4
  simp only [Nat.zero_add, ntGetD0, ntGetD1] at hd4
  cases k with
  | zero => rw [callW_zero] at h5; cases h5
  | succ k' =>
  have hw5 := callW_model (M := fun mq => cmW p (realCall p) k' mq vis c value (r3.headD 0)
    (r3.tail.headD 0) (r4.headD 0) (r4.tail.headD 0))
    (cm_specW p hD.lCheckDivModCerts (realCall p) (realCall_spec p) k' · vis c value (r3.headD 0)
      (r3.tail.headD 0) (r4.headD 0) (r4.tail.headD 0)) h5
  obtain ⟨x5, a5, hrun5, hC5, c5, hg5, hd5⟩ := cmC hD hq hcl hkp hs0 hsA henv c value hc hval hwsv
    x3 _ x4 _ (r3.headD 0) (r3.tail.headD 0) (r4.headD 0) (r4.tail.headD 0) k' (by omega) m4 a3 r5
    m5 hC4 hCr4 (hd3.grow hg4) hd4.1 hd4.2 hn3 (ConRon.Bridge.denote_ext hv c03.ext) hsd hpr
    (ConRon.Bridge.divModCertStmts_wscoped nm) hw5
  refine ⟨x5, a5, ?_, hC5, c03.trans c5, hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5))), hd5⟩
  simp only [checkDivModPinValue, StateT.run_bind, hrun1', exc_ok_bind', hrun2', hx2, ite_true, hrun3,
    hrun4]
  exact hrun5

end pinValue

/-! ## `check_div_mod_pin_at` -/

section pinAt
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_div_mod_pin_at` under `StageC`** (con-ron's `checkDivModPinAt_bridge`, which takes
the pin guard's `true` for the type pins' and the pin's scope): the type pins (`ctpC`), then the
value pin and the certificates (`cpvC`). -/
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
  cases k with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  have hw := callW_model (M := fun mq => cpaW p (k + 1) mq vis c value ps)
    (cpa_specW p hD.lCheckDivModPinAt (k + 1) · vis c value ps) hcall
  rw [cpaW.arm1] at hw
  have hD1 := hD.toDmProg7.toDmProg6.toDmProg5.toDmProg2.toDmProg1
  -- the type pins
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hd1⟩, hf1, hCr1, hw⟩ :=
    (divModTypePins_ref hD1 ps c ip).bindLC hcl (leaf_mem _ (by decide)) hkp (im_mem _ rfl)
      ⟨hC.stage, hc, hP⟩ hCr hw
  obtain ⟨e1, htd⟩ := ConRon.Bridge.divModTypePins_run hC.check.state hC.check.pins hps hn hrun1
  rw [e1] at hrun1 hS1
  have hC1 := StageC.of_core hC hS1 hf1 (CoreStep.refl hC.check)
  replace hw := ntBW_some hw; obtain ⟨r2, m2, h2, hw⟩ := hw
  obtain ⟨x2, a2, hrun2, hC2, c2, hg2, hd2⟩ := ctpC hD hq hcl hkp henv x1 _ _ _ k hk' m1 a r2 m2 hC1
    hCr1 hd1 htd (ConRon.Bridge.divModTypePins_closed hpg) h2
  have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
  by_cases z2 : r2.headD 0 = 0
  · rw [ite_eq_left z2] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx2 := decW0B_false hd2 z2
    refine ⟨false, a2, ?_, hC2, c2, hg1.trans hg2, decW0B_of_false _⟩
    simp only [checkDivModPinAt, StateT.run_bind, hrun1, exc_ok_bind', hrun2, hx2,
      Bool.false_eq_true, ite_false]
    rfl
  rw [ite_eq_right z2] at hw
  have hx2 := decW0B_true hd2 z2
  -- the value pin and the certificates
  replace hw := ntBW_some hw; obtain ⟨r3, m3, h3, hw⟩ := hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨x3, a3, hrun3, hC3, c3, hg3, hd3⟩ := cpvC hD hq hcl hkp hs0 hsA henv hk' h3 hC2 hc hval
    (PinSetR.grow hP (hg1.trans hg2)) (ConRon.Bridge.PinsDenote.mono c2.ext [ip] [psP] ⟨hps, trivial⟩).1
    (ConRon.Bridge.denoteN_ext hn c2.ext) (ConRon.Bridge.denote_ext hv c2.ext) hwsv hpg hCr2
  refine ⟨x3, a3, ?_, hC3, c2.trans c3, hg1.trans (hg2.trans hg3), hd3⟩
  simp only [checkDivModPinAt, StateT.run_bind, hrun1, exc_ok_bind', hrun2, hx2, ite_true]
  exact hrun3

end pinAt

/-! ## `check_div_mod_pin_loop` -/

section loop
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_div_mod_pin_loop` under `StageC`** (con-ron's `checkDivModPinLoop_bridge`): the pin
guard (`pgC`), on `true` the certificates' guard (`cgsC`), on `true` the attempt (`cpaC`); every
other outcome moves on to the next variant. -/
theorem loopC (hD : DmProg9 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    (c value : Word) (hc : H c) (hval : H value) {nm : ConLeche.Name} {v : ConLeche.Expr}
    (hwsv : ConLeche.Expr.WScoped 0 v) :
    ∀ (ips : List INatOpPinSet) (psPs : List ConLeche.NatOpPinSet) (po pl : Word)
      (tried : List String) (k : Nat), k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (res : List Word)
      (m' : Mem), StageC dn vis fe env m a → L.Stubs.CrOK m → PinsIW m po.toNat pl.toNat ips →
      PinsDenote a.store ips psPs → denoteN a.store.ns (decI c) = some nm →
      denoteE a.store (decE value) = some v →
      callW p k "check_div_mod_pin_loop" [vis, c, value, po, pl] m = some (res, m') →
      ∃ x a', (checkDivModPinLoop V fe (decI c) (decE value) ips tried).run a = .ok (x, a') ∧
        StageC dn vis fe env m' a' ∧ CoreStep V env fe a a' ∧ IWGrow m m' := by
  intro ips
  induction ips with
  | nil =>
    intro psPs po pl tried k hk m a res m' hC _ hI hpd hn hv hc'
    have hpl : pl = 0 := UInt64.toNat_inj.mp (by have := hI.2.1; simpa using this)
    cases k with
    | zero => rw [callW_zero] at hc'; cases hc'
    | succ k =>
    have hw := callW_model (M := fun mq => loopW p (k + 1) mq vis c value po pl)
      (loop_specW p hD.lCheckDivModPinLoop (k + 1) · vis c value po pl) hc'
    simp [loopW.eq_2, hpl] at hw
  | cons ip rest ih =>
    intro psPs po pl tried k hk m a res m' hC hCr hI hpd hn hv hc'
    cases psPs with
    | nil => exact hpd.elim
    | cons psP restP =>
    obtain ⟨hq0, hrestP⟩ := hpd
    cases k with
    | zero => rw [callW_zero] at hc'; cases hc'
    | succ k =>
    have hk' : k ≤ 2 ^ 62 := by omega
    have hw := callW_model (M := fun mq => loopW p (k + 1) mq vis c value po pl)
      (loop_specW p hD.lCheckDivModPinLoop (k + 1) · vis c value po pl) hc'
    rw [loopW.eq_2] at hw
    have hS := hC.stage
    have hsz := hS.2.2.2.1
    have hI1 := hS.2.1
    obtain ⟨hb, hl, hj⟩ := hI
    have hpl0 : pl ≠ 0 := fun e => by rw [e] at hl; simp at hl
    rw [ite_eq_right hpl0] at hw
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
    rw [hpsw] at hw
    -- the next variant, from a state a declined variant left
    have next : ∀ (m2 : Mem) (a2 : AState) (tr : List String) (r4 : List Word) (m4 : Mem),
        StageC dn vis fe env m2 a2 → L.Stubs.CrOK m2 → IWGrow m m2 → CoreStep V env fe a a2 →
        callW p k "check_div_mod_pin_loop" [vis, c, value, po + 1, pl - 1] m2 = some (r4, m4) →
        ∃ x a', (checkDivModPinLoop V fe (decI c) (decE value) rest tr).run a2 = .ok (x, a') ∧
          StageC dn vis fe env m4 a' ∧ CoreStep V env fe a a' ∧ IWGrow m m4 := by
      intro m2 a2 tr r4 m4 hC2 hCr2 hG2 c02 h4
      obtain ⟨x4, a4, hrun4, hC4, c4, hg4⟩ := ih restP (po + 1) (pl - 1) tr k hk' m2 a2 r4 m4 hC2
        hCr2 (hrestI m2 hG2) (ConRon.Bridge.PinsDenote.mono c02.ext _ _ hrestP)
        (ConRon.Bridge.denoteN_ext hn c02.ext) (ConRon.Bridge.denote_ext hv c02.ext) h4
      exact ⟨x4, a4, hrun4, hC4, c02.trans c4, hG2.trans hg4⟩
    -- the pin guard
    replace hw := ntBW_some hw; obtain ⟨r1, m1, h1, hw⟩ := hw
    obtain ⟨x1, a1, hrun1, hC1, c1, hg1, hd1, hx1v⟩ :=
      pgC hD.toDmProg8.toDmProg7.toDmProg6 hcl hkp h1 hC hc hP hq0 hn hCr
    have hCr1 := hkp.call (im_mem _ rfl) h1 hCr
    have hrun1' : (divModPinGuard ip fe (decI c)).run a = .ok (x1, a1) := hrun1
    by_cases z1 : r1.headD 0 = 0
    · rw [ite_eq_right (by simpa using z1)] at hw
      simp only [loopW.j1] at hw
      replace hw := ntBW_some hw; obtain ⟨r4, m4, h4, hw⟩ := hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx1 := decW0B_false hd1 z1
      obtain ⟨x4, a4, hrun4, hC4, c4, hg4⟩ := next m1 a1 _ r4 m4 hC1 hCr1 hg1 c1 h4
      refine ⟨x4, a4, ?_, hC4, c4, hg4⟩
      simp only [checkDivModPinLoop, StateT.run_bind, hrun1', exc_ok_bind', hx1,
        Bool.false_eq_true, ite_false]
      exact hrun4
    rw [ite_eq_left (show r1.headD 0 ≠ 0 from z1)] at hw
    have hx1 := decW0B_true hd1 z1
    -- the certificates' guards
    replace hw := ntBW_some hw; obtain ⟨r2, m2, h2, hw⟩ := hw
    have hq1 := (ConRon.Bridge.PinsDenote.mono c1.ext [ip] [psP] ⟨hq0, trivial⟩).1
    obtain ⟨x2, a2, hrun2, hC2, c2, hg2, hd2⟩ :=
      cgsC hD.toDmProg8.toDmProg7.toDmProg6 hcl hkp hs0 hsA h2 hC1 hc hval (PinSetR.grow hP hg1) hq1
        (ConRon.Bridge.denoteN_ext hn c1.ext) (ConRon.Bridge.denote_ext hv c1.ext) hCr1
    have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
    have hG2 : IWGrow m m2 := hg1.trans hg2
    have c02 := c1.trans c2
    have hrun2' : (divModCertsGuard ip fe (decI c) (decE value)).run a1 = .ok (x2, a2) := hrun2
    by_cases z2 : r2.headD 0 = 0
    · rw [ite_eq_right (by simpa using z2)] at hw
      simp only [loopW.j1] at hw
      replace hw := ntBW_some hw; obtain ⟨r4, m4, h4, hw⟩ := hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx2 := decW0B_false hd2 z2
      obtain ⟨x4, a4, hrun4, hC4, c4, hg4⟩ := next m2 a2 _ r4 m4 hC2 hCr2 hG2 c02 h4
      refine ⟨x4, a4, ?_, hC4, c4, hg4⟩
      simp only [checkDivModPinLoop, StateT.run_bind, hrun1', exc_ok_bind', hx1, ite_true, hrun2',
        hx2, Bool.false_eq_true, ite_false]
      exact hrun4
    rw [ite_eq_left (show r2.headD 0 ≠ 0 from z2)] at hw
    have hx2 := decW0B_true hd2 z2
    -- the attempt
    replace hw := ntBW_some hw; obtain ⟨r3, m3, h3, hw⟩ := hw
    obtain ⟨x3, a3, hrun3, hC3, c3, hg3, hd3⟩ :=
      cpaC hD.toDmProg8 hq hcl hkp hs0 hsA henv hk' h3 hC2 hc hval (PinSetR.grow hP hG2)
        (ConRon.Bridge.PinsDenote.mono c02.ext [ip] [psP] ⟨hq0, trivial⟩).1
        (ConRon.Bridge.denoteN_ext hn c02.ext) (ConRon.Bridge.denote_ext hv c02.ext) hwsv
        (by rw [← hx1v, hx1]) hCr2
    have hG3 : IWGrow m m3 := hG2.trans hg3
    have c03 := c02.trans c3
    by_cases z3 : r3.headD 0 ≠ 0
    · rw [ite_eq_left z3] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx3 := decW0B_true hd3 z3
      refine ⟨(), a3, ?_, hC3, c03, hG3⟩
      simp only [checkDivModPinLoop, StateT.run_bind, hrun1', exc_ok_bind', hx1, ite_true, hrun2',
        hx2, hrun3, hx3]
      rfl
    rw [ite_eq_right z3] at hw
    have z3' : r3.headD 0 = 0 := by simpa using z3
    have hx3 := decW0B_false hd3 z3'
    simp only [loopW.j1] at hw
    replace hw := ntBW_some hw; obtain ⟨r4, m4, h4, hw⟩ := hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨x4, a4, hrun4, hC4, c4, hg4⟩ :=
      next m3 a3 _ r4 m4 hC3 (hkp.call (im_mem _ rfl) h3 hCr2) hG3 c03 h4
    refine ⟨x4, a4, ?_, hC4, c4, hg4⟩
    simp only [checkDivModPinLoop, StateT.run_bind, hrun1', exc_ok_bind', hx1, ite_true, hrun2',
      hx2, hrun3, hx3, Bool.false_eq_true, ite_false]
    exact hrun4

end loop

end L.Ind
