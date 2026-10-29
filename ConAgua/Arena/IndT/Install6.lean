import ConAgua.Arena.IndT.Sum3
import ConAgua.Arena.IndRealSctC
import ConAgua.Arena.IndInstallSpec.PnfW
import ConAgua.Verdict.PosTopE1
import ConAgua.Verdict.PosTopEMono
import ConAgua.Arena.IndT.Install1

/-!
# `checkAbsCtorSorts`, `checkAbsCtorSortsAll` under `StageC` (lane `indstaget`)

The fields' universes at the holes, from `StageC` and con-ron's preconditions of
`checkAbsCtorSorts_specF` (the context, the constructors and their normal forms denote, the
normal forms scoped at the holes' depth, the environment denotes), the twin side transcribed from
that spec's proof: the level-parameter test (the stub's `StageR` contract;
`allLevelParamsDefined_run` and `coreStep_of_store` for the step), the holes' depth (L only), the
fields opened at the holes (`openPisAtFvarsF_run`), their sorts (`installSimFsortsC`, con-ron's
`checkStructFieldSortsI_spec` on its run for the `CoreStep`). `check_abs_ctor_sorts_one`,
`check_abs_ctor_sorts` and `check_abs_ctor_sorts_all` have one refinement each for both outcomes
over their unified models (`iao_ref`, `iac_ref`, `iaa_ref`; their errors:
`check_struct_field_sorts_i`'s, by `fsorts_ref`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop) (hApd : ApdF p)

/-- What `check_abs_ctor_sorts_one` and `check_abs_ctor_sorts` give (from `m`, `a`): the stage,
the growth, `AbsOK`, the core step. -/
structure IacPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m m' : Mem) (a a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'

include hq henv hOpf hLC hLT in
/-- **`check_abs_ctor_sorts_one` refines one constructor of `checkAbsCtorSorts`, both outcomes**
(twin side: one constructor of con-ron's `checkAbsCtorSorts_specF`'s proof, after the level test;
the errors: `check_struct_field_sorts_i`'s, by `fsorts_ref`). -/
theorem iao_ref (hsum : SumProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {ctx isP nF tyN hi : Word} {c : NestCtx} {b : Bool}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hc : DecB (fun m => decCtx m ctx.toNat) m c)
    (hty : H tyN) (hhi : hi.toNat = c.hiAt 0) (hb : (isP != 0) = b)
    {tyNP : ConLeche.Expr} {sortP : ConLeche.Level}
    (htyP : denoteE a.store (decI tyN) = some tyNP) (hW : ConLeche.Expr.WScoped (c.hiAt 0) tyNP)
    (hsP : denoteL a.store.ls c.sort = some sortP) (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    RefE (VerdictCtx p) (iaoE p n m vis ctx isP nF tyN hi) (absOneAM fe c b nF.toNat (decI tyN)) a
      (fun v _ a' => IacPost dn vis fe env m v.2 a a') := by
  rcases n with _ | n
  · rw [iaoE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  have hS := hC.stage
  obtain ⟨hs32, hse⟩ := installCtxWord9 hc hS.iw.iwSize
  by_cases hov : hi + nF < hi
  · rw [iaoE.abort1 p n m vis ctx isP nF tyN hi hov]; exact RefE.of_cls0 rfl
  rw [iaoE.arm1 p n m vis ctx isP nF tyN hi hov]
  unfold absOneAM
  rcases h1 : callW p n "open_pis_at_fvars_f" [nF, tyN, hi] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, iaoE.k_open_pis_at_fvars_f.none]; exact RefE.of_cls0 rfl
  rw [liftE_some]
  have hsim := opfSimRA (p := p) (n := n) (k := nF) (i := hi) hOpf hty hS hA
  rw [hhi] at hsim
  obtain ⟨x1, a1, hrun1, ⟨⟨hS1, hg1, hd1⟩, hr1⟩, hA1⟩ := hsim r1 m1 h1
  refine RefE.bind_right hrun1 ?_
  obtain ⟨p1, ho1⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC.check.state htyP hr1
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
  by_cases h0 : r1.headD 0 = 0
  · rw [iaoE.k_open_pis_at_fvars_f.abort1 p n vis isP nF hi _ r1 m1 h0]; exact RefE.of_cls0 rfl
  rw [iaoE.k_open_pis_at_fvars_f.arm1 p n vis isP nF hi _ r1 m1 h0]
  cases x1 with
  | none => exact absurd (show r1.headD 0 = 0 from hd1) h0
  | some fb =>
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨xsP, xP, hxq, hxs, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho1
  obtain ⟨h1', hfv, -⟩ := hd1
  obtain ⟨hfd, hfb⟩ := hfv
  have g1 : r1.getD 1 0 = r1.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r1.getD (1 + 1) 0 = r1.tail.tail.headD 0 := by
    rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  show RefE _ _ (checkStructFieldSortsI V fe b false c.sort (c.hiAt 0) fvs [] nF.toNat >>= fun _ => pure ()) a1 _
  have hfvsc := ConRon.Bridge.Inductives.openers_typeD_WScoped hxq hW
  have hsc : (rdW (m.arr64 IW) (ctx + 9)).toNat = (rdW (m.arr64 IW) (ctx + 9)).toNat := rfl
  rcases h2 : callE p n "check_struct_field_sorts_i" [vis, isP, 0, rdW (m.arr64 IW) (ctx + 9), hi,
      r1.tail.headD 0, r1.tail.tail.headD 0, 0, 0, nF] m1 with e2 | ⟨r2, m2⟩
  · rw [iaoE.k_check_struct_field_sorts_i.none]
    refine RefE.bind_left fun hG hk0 => ?_
    have h := RefE.run_err (fsortsE_spec p hsum.hcfs hsum.hcfg hsum.ha hsum.ad.ftd hsum.hfsb (n + 1)
      ⟨m1, Locals.init []⟩ vis isP 0 (rdW (m.arr64 IW) (ctx + 9)) hi _ _ 0 0 nF) hG.nv hG
      (fsorts_ref hq henv hLC hLT hsum.hg hsum.hpw hsum.het hsum.hcn n (by omega) m1 a1 isP 0
        (rdW (m.arr64 IW) (ctx + 9)) hi _ _ 0 0 nF fvs [] hC1 hA1 hfd hfb (by simp [decHL, hslice?]) (by simp) hs32
        (by rw [hse]; exact ConRon.Bridge.denoteL_ext hsP p1.ext)
        (by rw [← partsAddNoOv hov]; exact UInt64.toNat_lt _) hxs
        (fun i _ x hx => by rw [hhi]; exact hfvsc i x hx)) (callE_err_mono n.le_succ h2 hk0)
    rw [hse, hhi, hb, show ((0 : Word) != 0) = false from rfl] at h
    exact h hk0
  rw [iaoE.k_check_struct_field_sorts_i.arm1]
  have h := installSimFsortsC (dn := dn) (fe := fe) hq henv hLC hLT hsum n (by omega) isP 0
    (rdW (m.arr64 IW) (ctx + 9)) hi _ _ 0 0 nF hs32 fvs [] hC1 hA1
    (by rw [hse]; exact ConRon.Bridge.denoteL_ext hsP p1.ext) hfd hfb
    (by simp [decHL, hslice?]) (by simp)
    (by rw [← partsAddNoOv hov]; exact UInt64.toNat_lt _) hxs
    (fun i _ x hx => by rw [hhi]; exact hfvsc i x hx)
  rw [hse, hhi, hb, show ((0 : Word) != 0) = false from rfl] at h
  obtain ⟨u2, a2, hr2, hC2, hg2, -, -, hA2⟩ := h r2 m2 (callW_of_callE h2)
  refine RefE.bind_right hr2 (RefE.ret rfl ?_)
  obtain ⟨c2, -⟩ := ConRon.Bridge.Inductives.checkStructFieldSortsI_spec fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv b false c.sort sortP (c.hiAt 0) fvs [] xsP [] nF.toNat
    (fun i _ x hx => hfvsc i x hx) a1 a2 _ hC1.check
    ⟨ConRon.Bridge.denoteL_ext hsP p1.ext, hxs, rfl, ConRon.Bridge.denoteFEnv_mono p1.ext hfe⟩ hr2
  exact ⟨hC2, hg1.trans hg2, hA2, (p1.toCore hC.check).trans c2⟩

include hq henv hOpf hLC hLT hApd in
/-- **`check_abs_ctor_sorts` refines `checkAbsCtorSorts`, both outcomes** under `StageC` (twin
side: con-ron's `checkAbsCtorSorts_specF`'s proof; induction on the fuel). -/
theorem iac_ref (hP : AbsProg p) (ctx isP : Word) (c : NestCtx) (b : Bool) (hb : (isP != 0) = b)
    (hhi : c.hiAt 0 < 2 ^ 64) {ctxP : ConLeche.NestCtx} (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (co cl oo ol : Word) (cs : List (IConstantVal × Nat))
      (os : List (List NestFieldKind × EIdx)) (csP : List (ConLeche.ConstantVal × Nat))
      (osP : List (List ConLeche.NestFieldKind × ConLeche.Expr)),
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decCtx m ctx.toNat) m c →
    PSlR0 decCN cs co cl m → PSlR0 decKE os oo ol m →
    ConRon.Bridge.Inductives.dCtx a.store ctxP.find? c = some ctxP →
    ConRon.Bridge.Inductives.dCtors a.store cs = some csP →
    os.mapM (ConRon.Bridge.Inductives.dOut a.store) = some osP →
    (∀ o ∈ osP, ConLeche.Expr.WScoped (ctxP.hiAt 0) o.2) →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    RefE (VerdictCtx p) (iacE p n m vis ctx isP co cl oo ol)
      (ConRon.Arena.checkAbsCtorSorts V fe c b cs os) a (fun v _ a' => IacPost dn vis fe env m v.2 a a') := by
  induction n with
  | zero => intros; rw [iacE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a co cl oo ol cs os csP osP hC hA hc hcs hos hctxP hcsP hosP hws hfe
  have hS := hC.stage
  by_cases hcl : cl = 0
  · rw [iacE.arm1 p n m vis ctx isP co cl oo ol hcl, hcs.nil hcl]
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  by_cases hol : ol = 0
  · rw [iacE.arm2 p n m vis ctx isP co cl oo ol hcl hol, hos.nil hol]
    have : ConRon.Arena.checkAbsCtorSorts V fe c b cs [] = pure () := by
      cases cs <;> simp [ConRon.Arena.checkAbsCtorSorts]
    rw [this]
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  obtain ⟨qc, ⟨cv, nF⟩, cs', rfl, hwc, hqcb, hdc, hcs'⟩ := partsPSl_cons (hcs.pslr hcl) hcl
  obtain ⟨qo, ⟨ks, e⟩, os', rfl, hwo, hqob, hdo, hos'⟩ := partsPSl_cons (hos.pslr hol) hol
  obtain ⟨cP, csP', rfl, hcP, hcsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcsP
  obtain ⟨oP, osP', rfl, hoP, hosP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hosP
  obtain ⟨tyNP, htyNP, rfl⟩ : ∃ tyN, denoteE a.store e = some tyN ∧ oP = (ks.map ConRon.Bridge.Inductives.kindOf, tyN) := by
    simp only [ConRon.Bridge.Inductives.dOut, Option.map_eq_some_iff] at hoP
    obtain ⟨x, hx, rfl⟩ := hoP
    exact ⟨x, hx, rfl⟩
  have hWP : ConLeche.Expr.WScoped (ctxP.hiAt 0) tyNP := hws _ List.mem_cons_self
  obtain ⟨namesP, lpsP, paramsP, sortP, hceq, hnm, hlp, -, hsort, -⟩ := ConRon.Bridge.Inductives.dCtx_inv hctxP
  have hhiP : c.hiAt 0 = ctxP.hiAt 0 := by
    rw [hceq]
    simp [ConRon.Arena.NestCtx.hiAt, ConLeche.NestCtx.hiAt, ConRon.Bridge.denoteNList_length _ _ hnm]
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hqc' : (UInt64.ofNat qc : Word).toNat = qc := UInt64.toNat_ofNat_of_lt' hqcb
  have hqo' : (UInt64.ofNat qo : Word).toNat = qo := UInt64.toNat_ofNat_of_lt' hqob
  -- the words read
  have hcT : decCtx (truncM m) ctx.toNat = some c := hc
  obtain ⟨-, hlps, hnP, -, -, -, -⟩ := decCtx_some hcT
  obtain ⟨lo, ll, hlo, hll, hlpsd⟩ := decAt_some hlps
  have hlolt := partsIwLt hll
  obtain ⟨hwlo, hlob, -⟩ := partsIwRd hlo (w := ctx + 2) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨hwll, hllb, -⟩ := partsIwRd hll (w := ctx + 3) (by rw [UInt64.toNat_add]; simp; omega)
  have hdoT : decKE (truncM m) qo = some (ks, e) := hdo
  simp only [decKE, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hdoT
  obtain ⟨-, -, ee, hee, -, rfl⟩ := hdoT
  obtain ⟨heelt, hee'⟩ := rec2IwH_trunc hee
  obtain ⟨ew, hew, hew32, hewe⟩ := iwH_rdW_at (w := UInt64.ofNat qo) (k := 2) (by rw [hqo']; exact hee')
    hS.iw.iwSize
  rw [show (UInt64.ofNat 2 : Word) = 2 from rfl] at hew
  rw [iacE.arm3 p n m vis ctx isP co cl oo ol hcl hol, hwc, hwo, hwlo, hwll, hew]
  simp only [ConRon.Arena.checkAbsCtorSorts]
  have hlpsm : decHL m (UInt64.ofNat lo : Word).toNat (UInt64.ofNat ll : Word).toNat = some c.lps := by
    rw [UInt64.toNat_ofNat_of_lt' hlob, UInt64.toNat_ofNat_of_lt' hllb]
    exact DecB.get (f := fun m => (decHL m lo ll : Option (List NIdx))) (OMono.decHL _ _) hlpsd
  have hl' : Frontend.denoteNList a.store.ns c.lps = some ctxP.lps := by rw [hceq]; exact hlp
  have hsort' : denoteL a.store.ls c.sort = some ctxP.sort := by rw [hceq]; exact hsort
  -- the level parameters
  rcases h1 : callW p n "all_level_params_defined" [UInt64.ofNat lo, UInt64.ofNat ll, ew] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, iacE.k_all_level_params_defined.none]; exact RefE.of_cls0 rfl
  rw [liftE_some]
  have h := apdCall_simR hApd n (UInt64.ofNat lo) (UInt64.ofNat ll) ew hew32 c.lps hS hA
    hC.check.state hlpsm ⟨_, denoteNList_mapM hl'⟩
  rw [hewe] at h
  obtain ⟨ok, a1, hr1, hS1, hg1, ⟨hok1, -⟩, hA1, -⟩ := h r1 m1 h1
  obtain ⟨h1s, h1c, h1p, -⟩ := ConRon.Bridge.allLevelParamsDefined_run hC.check.state hl' htyNP hr1
  have c1 := ConRon.Bridge.Inductives.BI.coreStep_of_store hC.check h1s h1c h1p
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_check hS1 hA1 c1.ok c1.ext
  refine RefE.bind_right hr1 ?_
  by_cases h0 : r1.headD 0 = 0
  · rw [iacE.k_all_level_params_defined.abort1 p n vis ctx isP co cl oo ol _ _ r1 m1 h0]
    exact RefE.of_cls0 rfl
  have hokt : ok = true := by rw [← hok1]; simp only [bne_iff_ne, ne_eq, h0, not_false_eq_true]
  subst hokt
  rw [iacE.k_all_level_params_defined.arm1 p n vis ctx isP co cl oo ol _ _ r1 m1 h0]
  -- `NestCtx.hiAt`
  have hc1 : decCtx m1 ctx.toNat = some c := hc.stab (decCtx_mono _) m1 hg1
  have hnPlt := partsIwLt hnP
  rcases h2 : callW p n "nest_ctx_hi_at" [ctx, 0] m1 with _ | ⟨r2, m2⟩
  · rw [liftE_none, iacE.k_nest_ctx_hi_at.none]; exact RefE.of_cls0 rfl
  obtain ⟨s2, hs2, hpost2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (nestCtxHiAt_refines p hP.hiAt n _ ctx 0 c hc1 (by omega) (by omega)) h2
  obtain ⟨rfl, hr2⟩ := hpost2
  simp only at hs2; subst hs2
  rw [liftE_some, iacE.k_nest_ctx_hi_at.arm1, hr2, show (UInt64.toNat 0 : Nat) = 0 from rfl]
  -- the constructor's fields
  have hdcT : decCN (truncM m) qc = some (cv, nF) := hdc
  obtain ⟨-, hnF⟩ := decCN_some hdcT
  have hnFlt := partsIwLt hnF
  obtain ⟨hwnF, hnFb, -⟩ := partsIwRd hnF (w := UInt64.ofNat qc + 1) (by rw [UInt64.toNat_add, hqc']; simp; omega)
  have hwnF1 : rdW (m1.arr64 IW) (UInt64.ofNat qc + 1) = UInt64.ofNat nF := by
    rw [← hwnF]; simp only [rdW]; rw [show (UInt64.ofNat qc + 1 : Word).toNat = qc + 1 by
      rw [UInt64.toNat_add, hqc']; simp; omega, hg1.2.2.1 _ hnFlt]
  have hwe1 : rdW (m1.arr64 IW) (UInt64.ofNat qo + 2) = ew := by
    rw [← hew]; simp only [rdW]; rw [show (UInt64.ofNat qo + 2 : Word).toNat = qo + 2 by
      rw [UInt64.toNat_add, hqo']; simp; omega, hg1.2.2.1 _ heelt]
  rw [hwnF1, hwe1]
  refine RefE.of_run_eq (T' := absOneAM fe c b nF ee >>= fun _ => ConRon.Arena.checkAbsCtorSorts V fe c b cs' os')
    (by simp only [absOneAM, bind_assoc, pure_bind]; rfl) ?_
  have hhiw : (UInt64.ofNat (c.hiAt 0) : Word).toNat = c.hiAt 0 := UInt64.toNat_ofNat_of_lt' hhi
  have htyP1 : denoteE a1.store (decI ew) = some tyNP := by
    rw [hewe]; exact ConRon.Bridge.denote_ext htyNP c1.ext
  have hI := iao_ref (p := p) hq henv hOpf hLC hLT hP.sum n (by omega) hC1 hA1 (hc.grow (decCtx_mono _) hg1)
    hew32 hhiw hb htyP1 (by rw [hhiP]; exact hWP) (ConRon.Bridge.denoteL_ext hsort' c1.ext)
    (ConRon.Bridge.denoteFEnv_mono c1.ext hfe) (nF := UInt64.ofNat nF)
  rw [UInt64.toNat_ofNat_of_lt' hnFb, hewe] at hI
  rcases h3 : iaoE p n m1 vis ctx isP (UInt64.ofNat nF) ew (UInt64.ofNat (c.hiAt 0)) with e3 | ⟨r3, m3⟩ <;>
    rw [h3] at hI
  · rw [iacE.k_check_abs_ctor_sorts_one.none]; exact RefE.bind_left hI
  obtain ⟨u3, a3, hrun3, hC3, hg3, hA3, c3⟩ := hI
  refine RefE.bind_right hrun3 ?_
  rw [iacE.k_check_abs_ctor_sorts_one.arm1]
  have hg13 := hg1.trans hg3
  have c13 := c1.trans c3
  have hcP' : ConRon.Bridge.Inductives.dCtors a3.store cs' = some csP' :=
    ConRon.Bridge.Inductives.dCtors_ext c13.ext _ _ hcsP'
  have ih' := ih (by omega) m3 a3 (co + 1) (cl - 1) (oo + 1) (ol - 1) cs' os' csP' osP' hC3 hA3
    (hc.grow (decCtx_mono _) hg13)
    (PSlR0.grow decCN_mono (⟨hcs'.1, Or.inr hcs'.2⟩ : PSlR0 decCN cs' (co + 1) (cl - 1) m) hg13)
    (PSlR0.grow decKE_mono (⟨hos'.1, Or.inr hos'.2⟩ : PSlR0 decKE os' (oo + 1) (ol - 1) m) hg13)
    (ConRon.Bridge.Inductives.dCtx_ext _ c13.ext _ _ hctxP) hcP'
    (ConRon.Bridge.Inductives.dOut_ext.list c13.ext _ _ hosP')
    (fun y hy => hws y (List.mem_cons_of_mem _ hy)) (ConRon.Bridge.denoteFEnv_mono c13.ext hfe)
  rcases hx : iacE p n m3 vis ctx isP (co + 1) (cl - 1) (oo + 1) (ol - 1) with ε | ⟨r0, m0⟩ <;> rw [hx] at ih'
  · rw [iacE.k_check_abs_ctor_sorts.none]; exact ih'
  rw [iacE.k_check_abs_ctor_sorts.arm1]
  obtain ⟨y, a', hrun, hR⟩ := ih'
  exact RefE.ret hrun ⟨hR.stage, hg13.trans hR.grow, hR.abs, c13.trans hR.core⟩

include hq henv hOpf hLC hLT hApd in
/-- **`check_abs_ctor_sorts` refines `checkAbsCtorSorts`** under `StageC` (the denotations as
con-ron's `checkAbsCtorSorts_specF` asks): the context decoded below the tops with its holes'
bound below `2^64`, the constructors and their normal forms slices decoded below the tops. -/
@[refines ConRon.Arena.checkAbsCtorSorts]
theorem checkAbsCtorSorts_refinesC (hP : AbsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (ctx isP co cl oo ol : Word)
    (c : NestCtx) (b : Bool) (cs : List (IConstantVal × Nat)) (os : List (List NestFieldKind × EIdx))
    (hb : (isP != 0) = b) (hhi : c.hiAt 0 < 2 ^ 64) (hC : StageC dn vis fe env s₀.mem a₀)
    (hA : AbsOK s₀.mem)
    (hc : DecB (fun m => decCtx m ctx.toNat) s₀.mem c) (hcs : PSlR0 decCN cs co cl s₀.mem)
    (hos : PSlR0 decKE os oo ol s₀.mem) {ctxP : ConLeche.NestCtx}
    {csP : List (ConLeche.ConstantVal × Nat)}
    {osP : List (List ConLeche.NestFieldKind × ConLeche.Expr)}
    (hctxP : ConRon.Bridge.Inductives.dCtx a₀.store ctxP.find? c = some ctxP)
    (hcsP : ConRon.Bridge.Inductives.dCtors a₀.store cs = some csP)
    (hosP : os.mapM (ConRon.Bridge.Inductives.dOut a₀.store) = some osP)
    (hws : ∀ o ∈ osP, ConLeche.Expr.WScoped (ctxP.hiAt 0) o.2)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_abs_ctor_sorts" [vis, ctx, isP, co, cl, oo, ol]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkAbsCtorSorts V fe c b cs os) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.checkAbsCtorSorts V fe c b cs os) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (iacE_spec p hP.one hP.abs n s₀ vis ctx isP co cl oo ol)
    (iac_ref hq henv hOpf hLC hLT hApd hP ctx isP c b hb hhi n hn _ a₀ co cl oo ol cs os csP osP hC hA hc hcs hos
      hctxP hcsP hosP hws hfe)) ?_
  rintro r s' ⟨hl, u, a', hrun, hR⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, hR.abs⟩

include hq henv hOpf hLC hLT hApd in
/-- **`check_abs_ctor_sorts_all` refines `checkAbsCtorSortsAll`, both outcomes** under `StageC`
(twin side: con-ron's `checkAbsCtorSortsAll_specF`'s proof; induction on the fuel): every member
by `iac_ref`. -/
theorem iaa_ref (hP : AbsProg p) (ctx isP : Word) (c : NestCtx) (b : Bool) (hb : (isP != 0) = b)
    (hhi : c.hiAt 0 < 2 ^ 64) {ctxP : ConLeche.NestCtx} (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (so sl oo ol : Word) (css : List (List (IConstantVal × Nat)))
      (oss : List (List (List NestFieldKind × EIdx))) (cssP : List (List (ConLeche.ConstantVal × Nat)))
      (ossP : List (List (List ConLeche.NestFieldKind × ConLeche.Expr))),
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decCtx m ctx.toNat) m c →
    PSlR0 decCNS css so sl m → PSlR0 decKES oss oo ol m →
    ConRon.Bridge.Inductives.dCtx a.store ctxP.find? c = some ctxP →
    css.mapM (ConRon.Bridge.Inductives.dCtors a.store) = some cssP →
    ConRon.Bridge.Inductives.dOutss a.store oss = some ossP →
    (∀ os ∈ ossP, ∀ o ∈ os, ConLeche.Expr.WScoped (ctxP.hiAt 0) o.2) →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    RefE (VerdictCtx p) (iaaE p n m vis ctx isP so sl oo ol)
      (ConRon.Arena.checkAbsCtorSortsAll V fe c b css oss) a (fun v _ a' => IacPost dn vis fe env m v.2 a a') := by
  induction n with
  | zero => intros; rw [iaaE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a so sl oo ol css oss cssP ossP hC hA hc hcss hoss hctxP hcssP hossP hws hfe
  by_cases hsl : sl = 0
  · rw [iaaE.arm1 p n m vis ctx isP so sl oo ol hsl, hcss.nil hsl]
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  by_cases hol : ol = 0
  · rw [iaaE.arm2 p n m vis ctx isP so sl oo ol hsl hol, hoss.nil hol]
    have : ConRon.Arena.checkAbsCtorSortsAll V fe c b css [] = pure () := by
      cases css <;> simp [ConRon.Arena.checkAbsCtorSortsAll]
    rw [this]
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  obtain ⟨qc, cs, css', rfl, hwc, hqcb, hdc, hcss'⟩ := partsPSl_cons (hcss.pslr hsl) hsl
  obtain ⟨qo, os, oss', rfl, hwo, hqob, hdo, hoss'⟩ := partsPSl_cons (hoss.pslr hol) hol
  obtain ⟨csP, cssP', rfl, hcP, hcssP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcssP
  simp only [ConRon.Bridge.Inductives.dOutss] at hossP
  obtain ⟨osP, ossP', rfl, hoP, hossP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hossP
  have hqc' : (UInt64.ofNat qc : Word).toNat = qc := UInt64.toNat_ofNat_of_lt' hqcb
  have hqo' : (UInt64.ofNat qo : Word).toNat = qo := UInt64.toNat_ofNat_of_lt' hqob
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨co, cl, hco, hcl, hcd, hcb⟩ := partsAt decCN_mono (show decAt (truncM m)
    (decPL (truncM m) (decCN (truncM m))) qc = some cs from hdc)
  obtain ⟨oo2, ol2, hoo, hol2, hod, hob⟩ := partsAt decKE_mono (show decAt (truncM m)
    (decPL (truncM m) (decKE (truncM m))) qo = some os from hdo)
  have l1 := partsIwLt hcl; have l2 := partsIwLt hol2
  obtain ⟨w1, -, -⟩ := partsIwRd hco (w := UInt64.ofNat qc) hqc'
  obtain ⟨w2, -, -⟩ := partsIwRd hcl (w := UInt64.ofNat qc + 1) (by rw [UInt64.toNat_add, hqc']; simp; omega)
  obtain ⟨w3, -, -⟩ := partsIwRd hoo (w := UInt64.ofNat qo) hqo'
  obtain ⟨w4, -, -⟩ := partsIwRd hol2 (w := UInt64.ofNat qo + 1) (by rw [UInt64.toNat_add, hqo']; simp; omega)
  rw [UInt64.ofNat_toNat] at w1 w2 w3 w4
  rw [iaaE.arm3 p n m vis ctx isP so sl oo ol hsl hol, hwc, hwo, w1, w2, w3, w4]
  simp only [ConRon.Arena.checkAbsCtorSortsAll]
  have h1 := iac_ref hq henv hOpf hLC hLT hApd hP ctx isP c b hb hhi n (by omega) m a co cl oo2 ol2 cs os csP osP
    hC hA hc ⟨hcd, hcb⟩ ⟨hod, hob⟩ hctxP hcP hoP (hws osP List.mem_cons_self) hfe
  rcases h1' : iacE p n m vis ctx isP co cl oo2 ol2 with e1 | ⟨r1, m1⟩ <;> rw [h1'] at h1
  · rw [iaaE.k_check_abs_ctor_sorts.none]; exact RefE.bind_left h1
  obtain ⟨u1, a1, hrun1, hC1, hg1, hA1, c1⟩ := h1
  refine RefE.bind_right hrun1 ?_
  rw [iaaE.k_check_abs_ctor_sorts.arm1]
  have ih' := ih (by omega) m1 a1 (so + 1) (sl - 1) (oo + 1) (ol - 1) css' oss' cssP' ossP' hC1 hA1
    (hc.grow (decCtx_mono _) hg1)
    (PSlR0.grow decCNS_mono (⟨hcss'.1, Or.inr hcss'.2⟩ : PSlR0 decCNS css' (so + 1) (sl - 1) m) hg1)
    (PSlR0.grow (fun q => OMono.decAt (fun o l => OMono.decPL decKE_mono o l) q)
      (⟨hoss'.1, Or.inr hoss'.2⟩ : PSlR0 decKES oss' (oo + 1) (ol - 1) m) hg1)
    (ConRon.Bridge.Inductives.dCtx_ext _ c1.ext _ _ hctxP)
    (ConRon.Bridge.Inductives.dCtors_ext.list c1.ext _ _ hcssP')
    (ConRon.Bridge.Inductives.dOutss_ext c1.ext _ _ hossP')
    (fun y hy => hws y (List.mem_cons_of_mem _ hy)) (ConRon.Bridge.denoteFEnv_mono c1.ext hfe)
  rcases hx : iaaE p n m1 vis ctx isP (so + 1) (sl - 1) (oo + 1) (ol - 1) with ε | ⟨r0, m0⟩ <;> rw [hx] at ih'
  · rw [iaaE.k_check_abs_ctor_sorts_all.none]; exact ih'
  rw [iaaE.k_check_abs_ctor_sorts_all.arm1]
  obtain ⟨y, a', hrun, hR⟩ := ih'
  exact RefE.ret hrun ⟨hR.stage, hg1.trans hR.grow, hR.abs, c1.trans hR.core⟩

include hq henv hOpf hLC hLT hApd in
/-- **`check_abs_ctor_sorts_all` refines `checkAbsCtorSortsAll`** under `StageC` (the denotations
as con-ron's `checkAbsCtorSortsAll_specF` asks): every member's constructors and normal forms as
slices of `[off, len]` pointers decoded below the tops. -/
@[refines ConRon.Arena.checkAbsCtorSortsAll]
theorem checkAbsCtorSortsAll_refinesC (hP : AbsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (ctx isP so sl oo ol : Word)
    (c : NestCtx) (b : Bool) (css : List (List (IConstantVal × Nat)))
    (oss : List (List (List NestFieldKind × EIdx))) (hb : (isP != 0) = b) (hhi : c.hiAt 0 < 2 ^ 64)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hc : DecB (fun m => decCtx m ctx.toNat) s₀.mem c)
    (hcss : PSlR0 decCNS css so sl s₀.mem) (hoss : PSlR0 decKES oss oo ol s₀.mem)
    {ctxP : ConLeche.NestCtx} {cssP : List (List (ConLeche.ConstantVal × Nat))}
    {ossP : List (List (List ConLeche.NestFieldKind × ConLeche.Expr))}
    (hctxP : ConRon.Bridge.Inductives.dCtx a₀.store ctxP.find? c = some ctxP)
    (hcssP : css.mapM (ConRon.Bridge.Inductives.dCtors a₀.store) = some cssP)
    (hossP : ConRon.Bridge.Inductives.dOutss a₀.store oss = some ossP)
    (hws : ∀ os ∈ ossP, ∀ o ∈ os, ConLeche.Expr.WScoped (ctxP.hiAt 0) o.2)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_abs_ctor_sorts_all" [vis, ctx, isP, so, sl, oo, ol]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkAbsCtorSortsAll V fe c b css oss) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.checkAbsCtorSortsAll V fe c b css oss) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (iaaE_spec p hP.one hP.abs hP.all n s₀ vis ctx isP so sl oo ol)
    (iaa_ref hq henv hOpf hLC hLT hApd hP ctx isP c b hb hhi n hn _ a₀ so sl oo ol css oss cssP ossP hC hA hc hcss
      hoss hctxP hcssP hossP hws hfe)) ?_
  rintro r s' ⟨hl, u, a', hrun, hR⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, hR.abs⟩

end sims

end L.Ind
