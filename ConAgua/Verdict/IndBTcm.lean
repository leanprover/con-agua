import ConAgua.Arena.IndT.RecCheckTcm
import ConAgua.Verdict.IndBTpd

/-!
# Error refinement of `target_class_match` (lane `verdicts-b`, helper `ib`)
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs dShape)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tcmE_spec (p : Prog) (hf : p.lookup "target_class_match" = some targetClassMatch)
  fns [hf ↦ tcmE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hq henv hnv hcE in
/-- **`target_class_match`'s error claim** (the hypotheses of `tcmW_okC`; `target_params_def_eq`'s
error claim is a hypothesis in its own shape, `pdeClaim`). -/
theorem tcm_claim (L : TcmLook p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (q fto ftl pfo pfl us dso dsl lvls edso edsl : Word)
    (bs : BlockShape) (formerTys pfvs ds eds : List EIdx) (hC : StageC dn vis fe env s₀.mem a₀)
    (hA : AbsOK s₀.mem) (hbs : BSOK s₀.mem q.toNat bs) (hus : H us) (hlv : H lvls)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hpf : HSl0 s₀.mem pfo pfl pfvs) (hds : HSl0 s₀.mem dso dsl ds)
    (heds : HSl0 s₀.mem edso edsl eds) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP edsP : List ConLeche.Expr}
    {usP lvlsP : List ConLeche.Level}
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hpfP : Frontend.denoteEList a₀.store pfvs = some pfvsP)
    (husP : denoteLs a₀.store.lss (decI us) = some usP)
    (hdsP : Frontend.denoteEList a₀.store ds = some dsP)
    (hlvP : denoteLs a₀.store.lss (decI lvls) = some lvlsP)
    (hedsP : Frontend.denoteEList a₀.store eds = some edsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hpw : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped pfvsP.length x) :
    CoreSpecE p (n + 1) "target_class_match" [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, lvls, edso, edsl]
      (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (tcmE_spec p L.tcm (n + 1) ⟨s₀.mem, Locals.init []⟩ vis q fto ftl pfo pfl us
    dso dsl lvls edso edsl) hc' (Err.code_ne_of_cls hk0)
  rw [tcmE.arm1] at hW
  have hS := hC.stage
  cases h1 : callE p n "lvls_eq_c" [us, lvls] s₀.mem with
  | error e1 =>
    rw [h1, tcmE.k_lvls_eq_c.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨o1, a1, run1, hC1, hg1, hd1, hA1, c1, -⟩ :=
    lvlsEqC_simC p hq.closed hq.knot.lvc n hC hA us lvls hus hlv husP hlvP r1 m1 (callW_of_callE h1)
  have hS1 := hC1.stage
  have hP1 := hP.fr (MFr.ofCore hq.closed (by decide) (callW_of_callE h1))
  by_cases hne : r1.headD 0 ≠ 2
  · rw [h1, tcmE.k_lvls_eq_c.arm1 p n vis q fto ftl pfo pfl dso dsl edso edsl r1 m1 hne] at hW
    cases hW
  have hne' : r1.headD 0 = 2 := by simpa using hne
  rw [h1, tcmE.k_lvls_eq_c.arm2 p n vis q fto ftl pfo pfl dso dsl edso edsl r1 m1 hne'] at hW
  have ho1 : o1 = some true := by
    simp only [decLvlEq] at hd1
    rcases o1 with _ | _ | _
    · exfalso; apply hne; simp only at hd1; rw [hd1]; decide
    · exfalso; apply hne; simp only at hd1; rw [hd1]; decide
    · rfl
  subst ho1
  have hsz := hS1.2.2.2.1
  have hbs1 := hbs.grow hg1
  unfold ConRon.Arena.targetClassMatch
  refine ErrClaim.bind_right run1 ?_
  simp only []
  -- `block_shape_member_names`
  cases h2 : callE p n "block_shape_member_names" [q] m1 with
  | error e2 =>
    rw [h2, tcmE.k_block_shape_member_names.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨rn, m2⟩ := q2
  rw [h2, tcmE.k_block_shape_member_names.arm1] at hW
  obtain ⟨s2, hs2, -, h2m⟩ := triple_of_callW (blockShapeMemberNames_spec p L.ha L.mnc L.mn n
    ⟨m1, Locals.init []⟩ q) (callW_of_callE h2)
  subst hs2
  dsimp only at h2m
  obtain ⟨hS2, hg2, -, hdn, htn⟩ := memberNamesW_stage h2m hS1 hbs1
  have hf2 := (memberNamesW_dec h2m hsz hS1.2.2.2.2.2 hbs1.dec
    (by have := hbs1.ptop; have := hS1.lt64 (Nat.le_refl _); omega) hbs1.2.1 hbs1.2.2).2.2.2.1
  have hP2 := hP1.fr (MFr.of_iw hf2)
  have hA2 := AFr.iw hf2 hA1
  have hC2 := hC1.of_pstep hS2 hA2 (PStep.refl hC1.check.state)
  -- `block_shape_lps`
  cases h3 : callE p n "block_shape_lps" [q] s2.mem with
  | error e3 =>
    rw [h3, tcmE.k_block_shape_lps.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨rl, m3⟩ := q3
  rw [h3, tcmE.k_block_shape_lps.arm1] at hW
  obtain ⟨s3, hs3, -, h3m⟩ := triple_of_callW (blockShapeLps_spec p L.ha L.erc L.eri L.lps n
    ⟨s2.mem, Locals.init []⟩ q) (callW_of_callE h3)
  subst hs3
  dsimp only at h3m
  obtain ⟨hS3, hg3, hdl, hbl⟩ := lpsW_ok' h3m hS2 ((hbs1.1.grow (decBS_mono _) hg2))
  have hP3 := hP2.fr (lpsW_mfr h3m)
  have hA3 := lpsW_afr h3m hA2
  have hC3 := hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state)
  -- `param_levels`
  cases h4 : callE p n "param_levels" [rl.headD 0, rl.tail.headD 0] s3.mem with
  | error e4 =>
    rw [h4, tcmE.k_param_levels.none] at hW
    cases hW
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h4)
  | ok q4 =>
  obtain ⟨rb, m4⟩ := q4
  obtain ⟨s4, hs4, -, h4m⟩ := triple_of_callW (plW_spec p L.ha L.ic L.sc L.sg L.pf L.pp L.ip L.plg L.pl L.il n
    ⟨s3.mem, Locals.init []⟩ (rl.headD 0) (rl.tail.headD 0)) (callW_of_callE h4)
  subst hs4
  dsimp only at h4m
  obtain ⟨blv, a4, run4, hS4, hg4, hH4, hdb⟩ := plW_ok dn vis fe n s3.mem s4.mem a1 _ _ bs.lps rb h4m hS3 hdl
    (hS3.lt64 hbl) hbl
  have hP4 := hP3.fr (plW_mfr h4m)
  have hA4 := plW_afr h4m hA3
  obtain ⟨q4', hbl4⟩ := ConRon.Bridge.Inductives.paramLevels_spec bs.lps pP.lps a1 a4 blv
    hC3.check.state (ConRon.Bridge.denoteNListE_ext c1.ext _ _
      (ConRon.Bridge.Inductives.BlockShape.lps_spec hsh)) run4
  have hC4 := hC3.of_pstep hS4 hA4 q4'
  refine ErrClaim.bind_right run4 ?_
  by_cases hw : pfl + ftl < pfl
  · rw [h4, tcmE.k_param_levels.abort1 p n vis fto ftl pfo pfl dso dsl edso edsl _ _ rb s4.mem hw] at hW
    cases hW; exact absurd rfl hk0
  rw [h4, tcmE.k_param_levels.arm1 p n vis fto ftl pfo pfl dso dsl edso edsl _ _ rb s4.mem hw] at hW
  have hd : (pfl + ftl).toNat = pfl.toNat + ftl.toNat := word_add_nowrap hw
  have hg14 := (hg2.trans hg3).trans hg4
  have hg04 : IWGrow s₀.mem s4.mem := hg1.trans hg14
  -- `target_holes`
  cases h5 : callE p n "target_holes" [fto, ftl, pfl] s4.mem with
  | error e5 =>
    rw [h5, tcmE.k_target_holes.none] at hW
    cases hW
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h5)
  | ok q5 =>
  obtain ⟨rh, m5⟩ := q5
  rw [h5, tcmE.k_target_holes.arm1] at hW
  obtain ⟨s5, hs5, -, h5m⟩ := triple_of_callW (targetHoles_spec p L.ff L.fp L.iff L.ic L.ha L.sc L.th n
    ⟨s4.mem, Locals.init []⟩ fto ftl pfl) (callW_of_callE h5)
  subst hs5
  dsimp only at h5m
  obtain ⟨holes, a5, run5, hS5, hg5, hdh, hbh⟩ := thW_ok dn vis fe n s4.mem s5.mem a4 fto ftl pfl rh formerTys h5m hS4
    (by rw [decHL_grow hg04 hftb]; exact hft) (hS.lt64 hftb) (by have := hg04.1; omega)
    (by rw [← hd]; exact (pfl + ftl).toNat_lt)
  have hP5 := hP4.fr (thW_mfr n h5m)
  have hA5 := thW_afr n h5m hA4
  have hlen : pfvs.length = pfl.toNat := hpf.len
  have hlenf : formerTys.length = ftl.toNat := decHL_length _ hft
  have hlenP : pfvs.length = pfvsP.length := ConRon.Bridge.Inductives.denoteEList_length hpfP
  have hlenfP : formerTys.length = formerTysP.length :=
    ConRon.Bridge.Inductives.denoteEList_length hftP
  have c14 := c1.trans (q4'.toCore hC1.check)
  rw [← hlen] at run5
  obtain ⟨q5', hhs⟩ := ConRon.Bridge.Inductives.targetHoles_spec formerTys formerTysP pfvs.length a4 a5
    holes hC4.check.state (denoteEList_ext c14.ext _ _ hftP) run5
  have hC5 := hC4.of_pstep hS5 hA5 q5'
  have hg05 := hg04.trans hg5
  have c15 := c14.trans (q5'.toCore hC4.check)
  refine ErrClaim.bind_right run5 ?_
  cases h6 : callE p n "target_params_def_eq" [vis, pfl + ftl, rn.headD 0, rn.tail.headD 0, rb.headD 0,
      rh.headD 0, rh.tail.headD 0, pfo, pfl, dso, dsl, edso, edsl] s5.mem with
  | error e6 =>
    rw [h6, tcmE.k_target_params_def_eq.none] at hW
    cases hW
    have hdP : (pfl + ftl).toNat = pfvsP.length + formerTysP.length := by
      rw [hd, ← hlen, ← hlenf, hlenP, hlenfP]
    have hg25 := (hg3.trans hg4).trans hg5
    rw [← hdb] at hbl4
    have hcl := CoreSpecE.of_callE (targetParamsDefEq_claim hq henv hnv hcE L.tp n (by omega) ⟨s5.mem, Locals.init []⟩
      a5 (pfl + ftl) (rn.headD 0) (rn.tail.headD 0) (rb.headD 0) (rh.headD 0) (rh.tail.headD 0) pfo pfl dso dsl
      edso edsl bs.memberNames holes pfvs ds eds hC5 hA5 hH4
      (by dsimp only; rw [decHL_grow hg25 (by omega)]; exact hdn) (by dsimp only; have := hg25.1; omega) (by dsimp only; exact hdh) (by dsimp only; exact hbh)
      (by exact hpf.grow hg05) (by exact hds.grow hg05) (by exact heds.grow hg05) hP5
      (namesP := pP.memberNames) (lvlsP := pP.lps.map ConLeche.Level.param)
      (holesP := ConLeche.targetHoles formerTysP pfvsP.length)
      ⟨ConRon.Bridge.denoteNListE_ext c15.ext _ _
          (ConRon.Bridge.Inductives.BlockShape.memberNames_spec hsh),
        ConRon.Bridge.denoteLs_ext hbl4 q5'.ext, by rw [← hlenP]; exact hhs⟩
      (denoteEList_ext c15.ext _ _ hpfP) (denoteEList_ext c15.ext _ _ hdsP)
      (denoteEList_ext c15.ext _ _ hedsP)
      (by
        rw [hdP]
        exact ConLeche.targetAbs_WScoped (ConLeche.Cached.targetHoles_WScoped hformer pfvsP.length))
      (fun x hx => by rw [hdP]; exact (hpw x hx).mono (by omega))) h6
    rw [hd, ← hlen, ← hlenf, hdb] at hcl
    exact hcl
  | ok q6 =>
  rw [h6, tcmE.k_target_params_def_eq.arm1] at hW
  cases hW

end sims

end L.Ind
