import ConAgua.Arena.IndT.RecCheckTcm
import ConAgua.Verdict.IndBTpd
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
/-!
# Error refinement of `target_class_match` (lane `verdicts-b`, helper `ib`)
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs dShape)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tcmE_spec (p : Prog) (hL : TcmLook p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
  fns [hL.tcm ↦ tcmE]
  specs [callW_spec p n "lvls_eq_c", blockShapeMemberNames_spec p hL.ha hL.mnc hL.mn n,
    blockShapeLps_spec p hL.ha hL.erc hL.eri hL.lps n,
    plW_spec p hL.ha hL.ic hL.sc hL.sg hL.pf hL.pp hL.ip hL.plg hL.pl hL.il n,
    targetHoles_spec p hL.ff hL.fp hL.iff hL.ic hL.ha hL.sc hL.th n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] unified nv [hnv, _root_.L.Checker.nv_mem]

/-- What `target_class_match` gives besides the twin's result `c` (from `m`): the result word, the
stage invariant, the growth. -/
structure TcmPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (r : Word) (m' : Mem) (c : Bool) (a' : AState) : Prop where
  res : (r != 0) = c
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  rc : RcMR m'
  abs : AbsOK m'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hq henv hnv hcE in
/-- **`target_class_match` refines `targetClassMatch`, both outcomes** (twin side: con-ron's
`targetClassMatch_spec`'s proof): `lvlsEq?` (`lvlsEqC_simC`), the shape's member names and
parameters (L only), `paramLevels`, `targetHoles`, then `targetParamsDefEq` (`pdeW_okC`, its
error claim). -/
theorem tcm_ref (hL : TcmLook p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {q fto ftl pfo pfl us dso dsl lvls edso edsl : Word} {bs : BlockShape}
    {formerTys pfvs ds eds : List EIdx} (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hus : H us) (hlv : H lvls)
    (hft : decHL m fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop m)
    (hpf : HSl0 m pfo pfl pfvs) (hds : HSl0 m dso dsl ds) (heds : HSl0 m edso edsl eds)
    (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP edsP : List ConLeche.Expr}
    {usP lvlsP : List ConLeche.Level}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hpfP : Frontend.denoteEList a.store pfvs = some pfvsP)
    (husP : denoteLs a.store.lss (decI us) = some usP)
    (hdsP : Frontend.denoteEList a.store ds = some dsP)
    (hlvP : denoteLs a.store.lss (decI lvls) = some lvlsP)
    (hedsP : Frontend.denoteEList a.store eds = some edsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hpw : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped pfvsP.length x) :
    RefE (tcmE p n m vis q fto ftl pfo pfl us dso dsl lvls edso edsl)
      (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds) a
      (fun v c a' => TcmPost dn vis fe env m v.1 v.2 c a') := by
  cases n with
  | zero => rw [tcmE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hS := hC.stage
  rw [tcmE.arm1]
  rcases h1 : callW p n "lvls_eq_c" [us, lvls] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, tcmE.k_lvls_eq_c.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨o1, a1, run1, hC1, hg1, hd1, hA1, c1, -⟩ :=
    lvlsEqC_simC p hq.closed hq.knot.lvc n hC hA us lvls hus hlv husP hlvP r1 m1 h1
  have hS1 := hC1.stage
  have hP1 := hP.fr (MFr.ofCore hq.closed (by decide) h1)
  unfold ConRon.Arena.targetClassMatch
  refine RefE.bind_right run1 ?_
  by_cases hne : r1.headD 0 ≠ 2
  · rw [tcmE.k_lvls_eq_c.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne]
    refine RefE.ret (y := false) ?_ ⟨rfl, hC1, hg1, hP1, hA1⟩
    simp only [decLvlEq] at hd1
    rcases o1 with _ | _ | _
    · rfl
    · rfl
    · exact absurd hd1 hne
  rw [tcmE.k_lvls_eq_c.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using hne)]
  have ho1 : o1 = some true := by
    simp only [decLvlEq] at hd1
    rcases o1 with _ | _ | _
    · exfalso; apply hne; simp only at hd1; rw [hd1]; decide
    · exfalso; apply hne; simp only at hd1; rw [hd1]; decide
    · rfl
  subst ho1
  simp only []
  have hsz := hS1.2.2.2.1
  have hbs1 := hbs.grow hg1
  -- `block_shape_member_names`
  rcases h2 : memberNamesW n m1 q with _ | ⟨rn, m2⟩
  · rw [liftE_none, tcmE.k_block_shape_member_names.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, tcmE.k_block_shape_member_names.arm1]
  obtain ⟨hS2, hg2, -, hdn, htn⟩ := memberNamesW_stage h2 hS1 hbs1
  have hf2 := (memberNamesW_dec h2 hsz hS1.2.2.2.2.2 hbs1.dec
    (by have := hbs1.ptop; have := hS1.lt64 (Nat.le_refl _); omega) hbs1.2.1 hbs1.2.2).2.2.2.1
  have hP2 := hP1.fr (MFr.of_iw hf2)
  have hA2 := AFr.iw hf2 hA1
  have hC2 := hC1.of_pstep hS2 hA2 (PStep.refl hC1.check.state)
  -- `block_shape_lps`
  rcases h3 : lpsW n m2 q with _ | ⟨rl, m3⟩
  · rw [liftE_none, tcmE.k_block_shape_lps.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, tcmE.k_block_shape_lps.arm1]
  obtain ⟨hS3, hg3, hdl, hbl⟩ := lpsW_ok' h3 hS2 ((hbs1.1.grow (decBS_mono _) hg2))
  have hP3 := hP2.fr (lpsW_mfr h3)
  have hA3 := lpsW_afr h3 hA2
  have hC3 := hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state)
  -- `param_levels`
  rcases h4 : plW n m3 (rl.headD 0) (rl.tail.headD 0) with _ | ⟨rb, m4⟩
  · rw [liftE_none, tcmE.k_param_levels.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨blv, a4, run4, hS4, hg4, hH4, hdb⟩ := plW_ok dn vis fe n m3 m4 a1 _ _ bs.lps rb h4 hS3 hdl
    (hS3.lt64 hbl) hbl
  have hP4 := hP3.fr (plW_mfr h4)
  have hA4 := plW_afr h4 hA3
  obtain ⟨q4, hbl4⟩ := ConRon.Bridge.Inductives.paramLevels_spec bs.lps pP.lps a1 a4 blv
    hC3.check.state (ConRon.Bridge.denoteNListE_ext c1.ext _ _
      (ConRon.Bridge.Inductives.BlockShape.lps_spec hsh)) run4
  have hC4 := hC3.of_pstep hS4 hA4 q4
  refine RefE.bind_right run4 ?_
  by_cases hw : pfl + ftl < pfl
  · rw [tcmE.k_param_levels.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw]; exact RefE.of_cls0 (by simp)
  rw [tcmE.k_param_levels.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw]
  have hd : (pfl + ftl).toNat = pfl.toNat + ftl.toNat := word_add_nowrap hw
  have hg04 : IWGrow m m4 := hg1.trans ((hg2.trans hg3).trans hg4)
  -- `target_holes`
  rcases h5 : thW n m4 fto ftl pfl with _ | ⟨rh, m5⟩
  · rw [liftE_none, tcmE.k_target_holes.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, tcmE.k_target_holes.arm1]
  obtain ⟨holes, a5, run5, hS5, hg5, hdh, hbh⟩ := thW_ok dn vis fe n m4 m5 a4 fto ftl pfl rh formerTys h5 hS4
    (by rw [decHL_grow hg04 hftb]; exact hft) (hS.lt64 hftb) (by have := hg04.1; omega)
    (by rw [← hd]; exact (pfl + ftl).toNat_lt)
  have hP5 := hP4.fr (thW_mfr n h5)
  have hA5 := thW_afr n h5 hA4
  have hlen : pfvs.length = pfl.toNat := hpf.len
  have hlenf : formerTys.length = ftl.toNat := decHL_length _ hft
  have hlenP : pfvs.length = pfvsP.length := ConRon.Bridge.Inductives.denoteEList_length hpfP
  have hlenfP : formerTys.length = formerTysP.length :=
    ConRon.Bridge.Inductives.denoteEList_length hftP
  have c14 := c1.trans (q4.toCore hC1.check)
  rw [← hlen] at run5
  obtain ⟨q5, hhs⟩ := ConRon.Bridge.Inductives.targetHoles_spec formerTys formerTysP pfvs.length a4 a5
    holes hC4.check.state (denoteEList_ext c14.ext _ _ hftP) run5
  have hC5 := hC4.of_pstep hS5 hA5 q5
  have hg05 := hg04.trans hg5
  have c15 := c14.trans (q5.toCore hC4.check)
  refine RefE.bind_right run5 ?_
  -- `target_params_def_eq`: the twin's last step
  have hg25 := (hg3.trans hg4).trans hg5
  have hdP : (pfl + ftl).toNat = pfvsP.length + formerTysP.length := by
    rw [hd, ← hlen, ← hlenf, hlenP, hlenfP]
  rw [← hdb] at hbl4
  have hdn5 : decHL m5 (rn.headD 0).toNat (rn.tail.headD 0).toNat = some bs.memberNames := by
    rw [decHL_grow hg25 (by omega)]; exact hdn
  have hTA : TAArgs bs.memberNames (decI (rb.headD 0)) holes pP.memberNames
      (pP.lps.map ConLeche.Level.param) (ConLeche.targetHoles formerTysP pfvsP.length) a5.store :=
    ⟨ConRon.Bridge.denoteNListE_ext c15.ext _ _
        (ConRon.Bridge.Inductives.BlockShape.memberNames_spec hsh),
      ConRon.Bridge.denoteLs_ext hbl4 q5.ext, by rw [← hlenP]; exact hhs⟩
  have habs : ∀ e, ConLeche.Expr.WScoped (pfl + ftl).toNat e → ConLeche.Expr.WScoped (pfl + ftl).toNat
      (ConLeche.targetAbs pP.memberNames (pP.lps.map ConLeche.Level.param)
        (ConLeche.targetHoles formerTysP pfvsP.length) e) := by
    rw [hdP]
    exact ConLeche.targetAbs_WScoped (ConLeche.Cached.targetHoles_WScoped hformer pfvsP.length)
  have hpw5 : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped (pfl + ftl).toNat x :=
    fun x hx => by rw [hdP]; exact (hpw x hx).mono (by omega)
  have htw : ConRon.Arena.targetParamsDefEq V fe (pfvs.length + formerTys.length) bs.memberNames blv holes
      pfvs ds eds = ConRon.Arena.targetParamsDefEq V fe (pfl + ftl).toNat bs.memberNames
      (decI (rb.headD 0)) holes pfvs ds eds := by rw [hd, ← hlen, ← hlenf, hdb]
  rw [htw]
  cases h6 : callE p n "target_params_def_eq" [vis, pfl + ftl, rn.headD 0, rn.tail.headD 0, rb.headD 0,
      rh.headD 0, rh.tail.headD 0, pfo, pfl, dso, dsl, edso, edsl] m5 with
  | error e6 =>
    rw [tcmE.k_target_params_def_eq.none]
    exact CoreSpecE.of_callE (targetParamsDefEq_claim hq henv hnv hcE hL.tp n (by omega)
      ⟨m5, Locals.init []⟩ a5 (pfl + ftl) (rn.headD 0) (rn.tail.headD 0) (rb.headD 0) (rh.headD 0)
      (rh.tail.headD 0) pfo pfl dso dsl edso edsl bs.memberNames holes pfvs ds eds hC5 hA5 hH4 hdn5
      (by have := hg25.1; omega) hdh hbh (hpf.grow hg05) (hds.grow hg05) (heds.grow hg05) hP5 hTA
      (denoteEList_ext c15.ext _ _ hpfP) (denoteEList_ext c15.ext _ _ hdsP)
      (denoteEList_ext c15.ext _ _ hedsP) habs hpw5) h6
  | ok q6 =>
    obtain ⟨r6, m6⟩ := q6
    rw [tcmE.k_target_params_def_eq.arm1]
    obtain ⟨s6, hs6, -, h6m⟩ := triple_of_callW (tpd_spec p hL.tp (realCall p) (realCall_spec p) n
      ⟨m5, Locals.init []⟩ _ _ _ _ _ _ _ _ _ _ _ _ _) (callW_of_callE h6)
    subst hs6
    obtain ⟨c, a6, run6, hc, hC6, hg6, hP6, hA6⟩ := pdeW_okC hq henv n (by omega) h6m hC5 hA5 hH4 hdn5
      (by have := hg25.1; omega) hdh hbh (hpf.grow hg05) (hds.grow hg05) (heds.grow hg05) hP5 hTA
      (denoteEList_ext c15.ext _ _ hpfP) (denoteEList_ext c15.ext _ _ hdsP)
      (denoteEList_ext c15.ext _ _ hedsP) habs hpw5
    exact RefE.ret run6 ⟨by simpa using hc, hC6, hg05.trans hg6, hP6, hA6⟩

end sims

end L.Ind

end
