import ConAgua.Verdict.PosTopE4
import ConAgua.Verdict.PosTopEMono
import ConAgua.Verdict.IndA3
import ConAgua.Verdict.PosTopE2
import ConAgua.Verdict.PosTopE3
import ConAgua.Checker.NoVerdictTree

/-!
# `check_block_positivity`'s and `nest_seeds`' error claims, discharged (lane `verdicts-b`,
helper `ia2`, fork `top`)

`cbposW_okC`'s proof (`Positivity.lean`) on the model `cbpE`: `nest_uniform` (`nuE_claim`),
`nest_root` (`nrtE_claim`), `check_abs_ctor_sorts_all` (`iaaE_claim`); the other callees claim
nothing (`nvFns`). Then the generated statements `CheckBlockPositivityE` and `NestSeedsE`
(`IndA3.lean`), from the walk's claims (`NbOKE`, `NitE`) and `check_struct_field_sorts_i`'s
(`CheckStructFieldSortsIE`); the fuels below the ok refinement's by `callE_err_mono`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dCtx dCtors dOutss dState)

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

private theorem pos_mapM_mem' {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ x ∈ l, ∃ y, f x = some y
  | [], _, _, _, hx => absurd hx List.not_mem_nil
  | a :: l, _, h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, -⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, hy⟩
    · exact pos_mapM_mem' hys x hx

section sim
variable {p : Prog} (hq : KnotStageProg p) (hIlpf : IlpfF p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop) (hApd : ApdF p)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (eCsf : CheckStructFieldSortsIE p)
  (hCtE : ∀ n, n ≤ 2 ^ 62 → CtorsOKE p dn vis fe env n)

include hq hIlpf henv hOpf hLC hLT hApd hnv eCsf hCtE in
/-- **`check_block_positivity`'s error claim** (`cbposW_okC`'s hypotheses, the model at fuel
`n + 3`). -/
theorem cbpE_claim (hP : PosBlkProg p) {fs : List FnName} (_hclP : closedA p posFreeA posFreeC fs = true)
    (_hfa : "check_abs_ctor_sorts_all" ∈ fs) (n : Nat) (hn : n + 2 ≤ 2 ^ 62) {m : Mem} {a : AState}
    {q cvO cvL caO caL : Word} {P : BlockParts} {cvTas : List IConstantVal}
    {css : List (List (IConstantVal × Nat))} {pP : ConLeche.BlockParts}
    {cvsP : List ConLeche.ConstantVal} {cssP : List (List (ConLeche.ConstantVal × Nat))}
    {e : Err} (h : cbpE p (n + 3) m vis q cvO cvL caO caL = .error e) (hC : StageC dn vis fe env m a)
    (hqd : DecB (fun m => decBS m q.toNat) m P.shape) (hsrc : ShapeSrc m q)
    (hcv : PSlR decCVp cvTas cvO cvL m) (hcss : PSlR decCNSB css caO caL m) (hPM : PosMR m)
    (hA : AbsOK m) (hk : ∀ f ∈ posKeepCalleesC, AbsKeep p f)
    (hpP : ConRon.Bridge.Inductives.dParts a.store P = some pP)
    (hcvP : cvTas.mapM (Frontend.denoteCV a.store) = some cvsP)
    (hcssP : css.mapM (dCtors a.store) = some cssP)
    (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env)
    (hT : ∀ cv ∈ cvsP, ConLeche.Expr.WScoped 0 cv.type)
    (hct : ∀ cs ∈ cssP, ∀ c ∈ cs, ConLeche.Expr.WScoped 0 c.1.type) :
    ErrClaim (ConRon.Arena.checkBlockPositivity V fe P cvTas css) a e := by
  have hS := hC.stage
  have hpP0 := hpP
  simp only [ConRon.Bridge.Inductives.dParts, Option.map_eq_some_iff] at hpP
  obtain ⟨qP, hqP, rfl⟩ := hpP
  have hcl : ∀ cs ∈ cssP, ∀ c ∈ cs, c.1.type.hasFvar = false :=
    fun cs hcs c hc => ConLeche.Cached.ws0_hasFvar (hct cs hcs c hc)
  rw [cbpE.arm1] at h
  unfold ConRon.Arena.checkBlockPositivity
  -- the walk's context
  cases h1 : callE p (n + 2) "block_nest_ctx" [vis, q, cvO, cvL] m with
  | error e1 =>
    rw [h1, cbpE.k_block_nest_ctx.none] at h; cases h
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, cbpE.k_block_nest_ctx.arm1] at h
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (bnc_specC p hP.nck hP.nh hP.bnc (realCall p) (realCall_spec p) n _ vis q cvO cvL) (callW_of_callE h1)
  subst hs1
  obtain ⟨⟨c, holes⟩, a1, hrun1, hc1, hho1, hhob1, hS1, hg1, hin1, hsl1, hhi1, hpn1, hA1⟩ :=
    bncC_simA (realCall p) n hS hqd hsrc hcv
      (fun _ he => Sim.mono (opfSimRA (n := n + 1) hOpf he hS hA) fun _ _ _ _ h => ⟨h.1.1, h.2⟩) r1 s1.mem hW1
  obtain ⟨c1, ⟨ctxP, holesP⟩, ⟨hctx, hholes, hctxOk, hhw, hpar, -, hnh, -⟩, -⟩ :=
    ConRon.Bridge.Inductives.blockNestCtx_spec fe henv P.shape qP cvTas cvsP hT a a1 (c, holes)
      hC.check ⟨hqP, hcvP⟩ hrun1
  dsimp only at hctx hholes hhw hpar hnh
  refine ErrClaim.bind_right hrun1 ?_
  have hP1 : PosMR s1.mem := hPM.fr (bncC_mfr hOpf hW1)
  have hC1 : StageC dn vis fe env s1.mem a1 := hC.of_cstep hS1 hA1 c1
  have hU1 : UCtx dn vis fe s1.mem (r1.headD 0) c := ⟨hc1.get (decCtx_mono _), hin1, hsl1⟩
  obtain ⟨hlen, hcb1, hcss1⟩ := pos3_cssAt (hcss.grow decCNSB_mono hg1)
  have hcss1P := ConRon.Bridge.Inductives.dCtors_ext.list c1.ext _ _ hcssP
  have hPc : ∀ cs ∈ css, ∀ x ∈ cs, ∃ cvP, Frontend.denoteCV a1.store x.1 = some cvP := by
    intro cs hcs x hx
    obtain ⟨y, hy⟩ := pos_mapM_mem' hcss1P cs hcs
    obtain ⟨z, hz⟩ := pos_mapM_mem' hy x hx
    simp only [ConRon.Bridge.Inductives.dCtor, Option.map_eq_some_iff] at hz
    obtain ⟨cvP, hcvP', -⟩ := hz
    exact ⟨cvP, hcvP'⟩
  have hJI : ∀ (m : Mem) (a' : AState) (cv : Word) (cvv : IConstantVal),
      (fun m' a' => StageC dn vis fe env m' a' ∧ AbsOK m' ∧ ConRon.Arena.Ext a1.store a'.store) m a' →
      (fun cvv => ∃ cvP, Frontend.denoteCV a1.store cvv = some cvP) cvv →
      decCV (erecP m) cv.toNat = some cvv → ∀ (k' : Nat) (m1' : Mem) (a1' : AState) (r1' : List Word) (b : Bool),
      pdoW (k' + 3) m (rdW (m.arr64 IW) (r1.headD 0)) (rdW (m.arr64 IW) (r1.headD 0 + 1))
        (rdW (m.arr64 IW) (r1.headD 0 + 4)) (nhiW m (r1.headD 0) 0) (rdW (m.arr64 IW) (r1.headD 0 + 4))
        (rdW (m.arr64 EREC) (cv + 3)) = some (r1', m1') →
      (ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type).run a' = .ok (b, a1') →
      StageR dn vis fe m1' a1' → IlpRd (realCall p) dn vis fe (IlpBase m1' a1') :=
    fun _ a' _ cvv hJ hPx _ _ m1' a1' _ b hpd hrun hS1' => by
      obtain ⟨hCm, hAm, hxm⟩ := hJ
      obtain ⟨cvP, hcvP'⟩ := hPx
      obtain ⟨-, -, hty⟩ := ConRon.Bridge.Core.denoteCV_inv hcvP'
      obtain ⟨hcn, -⟩ := ConRon.Bridge.Inductives.dCtx_fields
        (ConRon.Bridge.Inductives.dCtx_ext _ hxm _ _ hctx)
      obtain ⟨p1', -⟩ := ConRon.Bridge.Inductives.piDomsOcc_spec c.names ctxP.names c.nP (c.hiAt 0) c.nP
        cvv.type cvP.type a' a1' b hCm.check.state ⟨hcn, ConRon.Bridge.denote_ext hty hxm⟩ hrun
      exact IlpRd.realC hIlpf (hCm.of_pstep hS1' (pdoW_afr _ _ _ _ _ _ _ _ _ _ hpd hAm) p1')
  have hJnu : ∀ (k : Nat) (m m' : Mem) (a' a'' : AState) (cv : Word) (cvv : IConstantVal) (r : List Word) (x : Bool),
      (fun m' a' => StageC dn vis fe env m' a' ∧ AbsOK m' ∧ ConRon.Arena.Ext a1.store a'.store) m a' →
      (fun cvv => ∃ cvP, Frontend.denoteCV a1.store cvv = some cvP) cvv →
      nuWf (realCall p) k m (r1.headD 0) cv = some (r, m') →
      (ConRon.Arena.nestUniformOk c cvv).run a' = .ok (x, a'') → StageR dn vis fe m' a'' → (NuAfr → AFr m m') →
      (fun m' a' => StageC dn vis fe env m' a' ∧ AbsOK m' ∧ ConRon.Arena.Ext a1.store a'.store) m' a'' :=
    fun _ _ _ a' a'' _ cvv _ _ hJ hPx _ hrun hS' hA' => by
      obtain ⟨hCm, hAm, hxm⟩ := hJ
      obtain ⟨cvP, hcvP'⟩ := hPx
      obtain ⟨c3, -⟩ := ConRon.Bridge.Inductives.nestUniformOk_spec (μ := V) (env := env) (fe := fe)
        env.find? c ctxP cvv cvP a' a'' _ hCm.check
        ⟨ConRon.Bridge.Inductives.dCtx_ext _ hxm _ _ hctx, ConRon.Bridge.denoteCV_ext hcvP' hxm⟩ hrun
      have hAm' := hA' nuAfr hAm
      exact ⟨hCm.of_cstep hS' hAm' c3, hAm', hxm.trans c3.ext⟩
  -- `nest_uniform`
  cases h2 : callE p (n + 2) "nest_uniform" [r1.headD 0, caO, caL] s1.mem with
  | error e2 =>
    rw [h2, cbpE.k_nest_uniform.none] at h; cases h
    refine ErrClaim.bind_left ?_
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    have hW2 := triple_of_callE_err (nuE_spec p hP.nuP (n + 2) ⟨s1.mem, Locals.init []⟩ (r1.headD 0) caO caL) h2
      (Err.code_ne_of_cls hk0)
    simp only at hW2
    exact nuE_claim hP.nu hP.nuCs hnv dn fe vis (r1.headD 0) c hhi1 _ _ hJI hJnu (n + 2) s1.mem a1 caO caL css _
      hW2 hS1 ⟨hC1, hA1, ConRon.Arena.Ext.refl _⟩ hPc hU1 hlen hcss1 hP1
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, cbpE.k_nest_uniform.arm1] at h
  obtain ⟨s2, hs2, -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (nestUniform_spec p hP.nu hP.nuCs hP.nuP (realCall p) (realCall_spec p) (n + 2) _ (r1.headD 0) caO caL)
    (callW_of_callE h2)
  subst hs2
  obtain ⟨a2, hrun2, hS2, hg2, hP2, hJ2⟩ := unW_ok dn fe vis (r1.headD 0) c hhi1 (realCall p)
    (fun m' a' => StageC dn vis fe env m' a' ∧ AbsOK m' ∧ ConRon.Arena.Ext a1.store a'.store)
    (fun cvv => ∃ cvP, Frontend.denoteCV a1.store cvv = some cvP) hJI hJnu
    (n + 2) s1.mem s2.mem a1 caO caL css hw2 hS1 ⟨hC1, hA1, ConRon.Arena.Ext.refl _⟩ hPc hU1 hlen hcss1 hP1
  obtain ⟨c2, -, -, -⟩ := ConRon.Bridge.Inductives.nestUniform_spec (μ := V) (env := env) (fe := fe)
    env.find? c ctxP css cssP a1 _ _ hC1.check
    ⟨hctx, hcss1P⟩ hrun2
  have hA2 : AbsOK s2.mem := hJ2.2.1
  have hC2 := hC1.of_cstep hS2 hA2 c2
  refine ErrClaim.bind_right hrun2 ?_
  -- the empty state
  cases h3 : callE p (n + 2) "check_block_positivity_init" [] s2.mem with
  | error e3 =>
    rw [h3, cbpE.k_check_block_positivity_init.none] at h; cases h
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, cbpE.k_check_block_positivity_init.arm1] at h
  obtain ⟨hS3, hg3, hf3, hns3⟩ := pos3_init hP (callW_of_callE h3) hS2
  have hA3 : AbsOK m3 := hk _ (by simp [posKeepCalleesC]) _ _ _ _ _ (callW_of_callE h3) hA2
  have hC3 := hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state)
  have hg13 := hg2.trans hg3
  -- the root frame
  have hx12 := c1.ext.trans c2.ext
  have hcssP2 := ConRon.Bridge.Inductives.dCtors_ext.list hx12 _ _ hcssP
  have hctx2 := ConRon.Bridge.Inductives.dCtx_ext _ c2.ext _ _ hctx
  have hholes2 := ConRon.Bridge.denoteEList_ext c2.ext _ _ hholes
  have hlenP : ctxP.names.length ≤ holesP.length := by
    rw [ConLeche.nestHoles_length hnh]; exact Nat.le_refl _
  cases h4 : callE p (n + 2) "nest_root" [vis, r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0, caO, caL,
      r3.headD 0, 0, 0] m3 with
  | error e4 =>
    rw [h4, cbpE.k_nest_root.none] at h; cases h
    refine ErrClaim.bind_left ?_
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    have hW4 := triple_of_callE_err (nrtE_spec p hP.rs.proot (n + 2) ⟨m3, Locals.init []⟩ vis (r1.headD 0)
      (r1.tail.headD 0) (r1.tail.tail.headD 0) caO caL (r3.headD 0) 0 0) h4 (Err.code_ne_of_cls hk0)
    simp only at hW4
    exact nrtE_claim hP.rs hnv hq hIlpf hLC dn vis fe henv hCtE (r1.headD 0) (r1.tail.headD 0)
      (r1.tail.tail.headD 0) c holes hctxOk (fun y hy => (hhw y hy).1) hlenP hpar (n + 2) hn m3 a2 caO caL
      (r3.headD 0) 0 0 css {} [] cssP {} [] _ hW4 hC3 (hU1.grow hg13) hhi1 hpn1
      (by rw [decHL_grow3 hg13 hhob1]; exact hho1) (Nat.le_trans hhob1 hg13.1) hlen
      (Nat.le_trans hcb1 hg13.1) (hcss1.grow hg13) hns3 (by simp [RootOutsB, DecB, decPL]) (by simp)
      (hP2.fr hf3) hA3 hctx2 hholes2 hcssP2 (by simp [dState]) rfl hcl
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, cbpE.k_nest_root.arm1] at h
  obtain ⟨s4, hs4, -, ⟨outs, ns⟩, a4, hrun4, hC4, hg4, hO4, hOb4, hns4, hP4, hA4, c3⟩ :=
    triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (nestRoot_refinesC hP.rs hq hIlpf hLC (n + 2) dn vis fe henv hn _ _ (r1.headD 0) (r1.tail.headD 0)
      (r1.tail.tail.headD 0) caO caL (r3.headD 0) 0 0 c holes css {} [] hC3 (hU1.grow hg13) hhi1 hpn1
      (by rw [decHL_grow3 hg13 hhob1]; exact hho1) (Nat.le_trans hhob1 hg13.1) hlen
      (Nat.le_trans hcb1 hg13.1) (hcss1.grow hg13) hns3 (by simp [RootOutsB, DecB, decPL]) (by simp)
      (hP2.fr hf3) hA3 hctxOk (fun y hy => (hhw y hy).1) hlenP hpar hctx2 hholes2 hcssP2
      (nsP := {}) (by simp [dState]) rfl hcl) (callW_of_callE h4)
  subst hs4
  obtain ⟨-, ⟨outsP, nsP⟩, ⟨houts, -, hwN⟩, -⟩ := ConRon.Bridge.Inductives.nestRoot_spec coreSpecV henv
    hctxOk holes holesP (fun y hy => (hhw y hy).1) hlenP hpar css cssP {} {} [] [] hcl _ a4 (outs, ns)
    hC3.check ⟨hctx2, hholes2, hcssP2, by simp [dState], rfl⟩ hrun4
  simp only [List.nil_append] at houts
  dsimp only at houts hwN
  have hS4 := hC4.stage
  have hg14 := hg13.trans hg4
  refine ErrClaim.bind_right hrun4 ?_
  -- `pin_word(53)`
  cases h5 : callE p (n + 2) "pin_word" [53] s4.mem with
  | error e5 =>
    rw [h5, cbpE.k_pin_word.none] at h; cases h
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, cbpE.k_pin_word.arm1] at h
  obtain ⟨s5, hs5, -, hm5, hz5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (pinWord_specV p hP.pin (n + 2) _ 53) (callW_of_callE h5)
  simp only at hm5 hz5 hs5
  rw [hs5] at hm5; subst hm5
  obtain ⟨hrunz, hzH⟩ := pinZero_stage hS4 hz5
  obtain ⟨-, hz⟩ := ConRon.Bridge.Inductives.zeroLevel_run hC4.check.pins hrunz
  refine ErrClaim.bind_right hrunz ?_
  -- `lvl_eq_true`
  have hg14' := hg14
  obtain ⟨huH, hue⟩ := installCtxWord9 (hc1.grow (decCtx_mono _) hg14) hS4.2.2.2.1
  cases h6 : callE p (n + 2) "lvl_eq_true" [rdW (s4.mem.arr64 IW) (r1.headD 0 + 9), r5.headD 0] s4.mem with
  | error e6 =>
    rw [h6, cbpE.k_lvl_eq_true.none] at h; cases h
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h6
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [h6, cbpE.k_lvl_eq_true.arm1] at h
  obtain ⟨s6, hs6', -, he6⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (eqTrue_specC p hP.eqt (realCall p) (realCall_spec p) (n + 2) _ _ _) (callW_of_callE h6)
  simp only at he6 hs6'
  rw [eqTrueC_succ] at he6
  rcases hs6 : realCall p (n + 1) "lvl_eq_c" [rdW (s4.mem.arr64 IW) (r1.headD 0 + 9), r5.headD 0] s4.mem with _ | ⟨r6', m6'⟩ <;> rw [hs6] at he6; · simp [eqTrueK] at he6
  rw [eqTrueK_some] at he6
  obtain ⟨hr6, hm6⟩ := Prod.mk.inj (Option.some.inj he6)
  rw [hs6'] at hm6
  subst hm6
  obtain ⟨namesP, lpsP, paramsP, sortP, hceq, -, -, -, hsort, -⟩ := ConRon.Bridge.Inductives.dCtx_inv hctx
  have hfind : ctxP.find? = env.find? := by rw [hceq]
  have hx14 := c2.ext.trans c3.ext
  have hsort' : ConRon.Arena.denoteL a4.store.ls (decI (rdW (s4.mem.arr64 IW) (r1.headD 0 + 9))) =
      some ctxP.sort := by
    rw [hue, hceq]; exact ConRon.Bridge.denoteL_ext hsort hx14
  obtain ⟨y, a6, hrun6, hC6, hg6, hy6, hA6, -⟩ :=
    lvlEqC_simC p hq.closed hLC (n + 1) hC4 hA4 _ _ huH hzH _ _ hsort' hz r6' m6' hs6
  have hS6 := hC6.stage
  have hP6 : PosMR m6' :=
    hP4.fr (MFr.of_frame (run_memFrame hq.closed (by decide) (run_of_callW hs6)).1 coreStageA_stage
      coreStageC_stage)
  obtain ⟨c5, -⟩ := ConRon.Bridge.Inductives.lvlEq?_crun hC4.check hsort' hz hrun6
  have hb6 : (r6.headD 0 != 0) = (y == some true) := by
    rw [← hr6]
    simp only [decLvlEq] at hy6
    rcases y with _ | _ | _ <;> simp_all
  rw [hue] at hrun6
  refine ErrClaim.bind_right hrun6 ?_
  -- the fields' universes at the holes
  have hg16 := hg14.trans hg6
  have hOb6 : (r4.headD 0).toNat + (r4.tail.headD 0).toNat ≤ iwTop m6' := Nat.le_trans hOb4 hg6.1
  have hx16 := hx14.trans c5.ext
  cases h7 : callE p (n + 2) "check_abs_ctor_sorts_all" [vis, r1.headD 0, r6.headD 0, caO, caL, r4.headD 0,
      r4.tail.headD 0] m6' with
  | ok q7 =>
    obtain ⟨r7, m7⟩ := q7
    rw [h7, cbpE.k_check_abs_ctor_sorts_all.arm1] at h
    cases h8 : callE p (n + 2) "check_block_positivity_nfs" [r4.headD 0, r4.tail.headD 0] m7 with
    | error e8 =>
      rw [h8, cbpE.k_check_block_positivity_nfs.none] at h; cases h
      exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h8
    | ok q8 => obtain ⟨r8, m8⟩ := q8; rw [h8, cbpE.k_check_block_positivity_nfs.arm1] at h; cases h
  | error e7 =>
  rw [h7, cbpE.k_check_abs_ctor_sorts_all.none] at h; cases h
  refine ErrClaim.bind_left ?_
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW7 := triple_of_callE_err (iaaE_spec p hP.abs.all (n + 2) ⟨m6', Locals.init []⟩ vis (r1.headD 0) (r6.headD 0)
    caO caL (r4.headD 0) (r4.tail.headD 0)) h7 (Err.code_ne_of_cls hk0)
  simp only at hW7
  exact iaaE_claim hq henv hOpf hLC hLT hnv eCsf hApd hP.abs (r1.headD 0) (r6.headD 0) c
    (y == some true) hb6 hhi1 (n + 2) hn m6' a6 caO caL (r4.headD 0) (r4.tail.headD 0) css outs cssP outsP
    hC6 hA6 (hc1.grow (decCtx_mono _) hg16) ((pos3_cns hcss).grow decCNS_mono (hg1.trans hg16))
    ⟨hO4.grow hg6, Or.inr hOb6⟩ (by rw [hfind]; exact ConRon.Bridge.Inductives.dCtx_ext _ hx16 _ _ hctx)
    (ConRon.Bridge.Inductives.dCtors_ext.list (c1.ext.trans hx16) _ _ hcssP)
    (ConRon.Bridge.Inductives.dOutss_ext c5.ext _ _ houts) hwN
    (ConRon.Bridge.denoteFEnv_mono (c1.ext.trans hx16) hfe) _ hW7

end sim

section claims
variable {p : Prog}

/-- **`check_block_positivity`'s error claim, discharged**: the generated statement
(`CheckBlockPositivityE`), from the walk's claims, `check_struct_field_sorts_i`'s and the
`nvFns` text; the fuels below `3` by `callE_err_mono`. -/
theorem checkBlockPositivityE_claim (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hNbE : ∀ dn vis fe env, ConLeche.EnvWF env → ∀ n, n ≤ 2 ^ 62 → NbOKE p dn vis fe env n)
    (eCsf : CheckStructFieldSortsIE p) : CheckBlockPositivityE p := by
  intro hq hIlpf dn vis fe env henv hOpf hLC hLT hApd hP fs hclP hfa s₀ a₀ q cvO cvL caO caL P cvTas css hC hqd
    hsrc hcv hcss hPM hA hk pP cvsP cssP hpP hcvP hcssP hfe hT hct F hF e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  obtain ⟨n, hn⟩ : ∃ n, max F 3 = n + 3 := ⟨max F 3 - 3, by omega⟩
  have he' := callE_err_mono (show F ≤ n + 3 by omega) he hk0
  have hW := triple_of_callE_err (cbpE_spec p hP.cbp (n + 3) ⟨s₀.mem, Locals.init []⟩ vis q cvO cvL caO caL) he'
    (Err.code_ne_of_cls hk0)
  simp only at hW
  exact cbpE_claim hq hIlpf henv hOpf hLC hLT hApd hnv eCsf
    (fun k hk => (hNbE dn vis fe env henv k hk).2.2.2.2.2.2.2.1) hP hclP hfa n (by omega) hW hC hqd hsrc hcv hcss hPM
    hA hk hpP hcvP hcssP hfe hT hct

/-- **`nest_seeds`' error claim, discharged**: the generated statement (`NestSeedsE`), from the
walk's claims (`KeyOKEc` of `NbOKE`, `NitE`) and the `nvFns` text. -/
theorem nestSeedsE_claim (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hNbE : ∀ dn vis fe env, ConLeche.EnvWF env → ∀ n, n ≤ 2 ^ 62 → NbOKE p dn vis fe env n)
    (hNit : ∀ dn vis fe env, ConLeche.EnvWF env → NitE p dn vis fe env) : NestSeedsE p := by
  intro hL hq hIlpf hLC dn vis fe env henv s₀ a₀ ctx sO sL ns c seeds NS hC hU hhi hsl hsd hns hP hA ctxP seedsP nsP
    hc hctx hseedsP hnsP hw F hF e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (nsdE_spec p hL.pseeds F ⟨s₀.mem, Locals.init []⟩ vis ctx sO sL ns) he
    (Err.code_ne_of_cls hk0)
  simp only at hW
  exact nsdE_claim hL hnv hq hIlpf hLC dn vis fe henv (fun k hk => (hNbE dn vis fe env henv k hk).2.2.2.2.1)
    (hNit dn vis fe env henv) ctx c hc F hF s₀.mem a₀ sO sL ns seeds NS seedsP nsP e hW hC hU hhi hsl hsd hns hP hA hctx
    hseedsP hnsP hw

end claims

end L.Ind
