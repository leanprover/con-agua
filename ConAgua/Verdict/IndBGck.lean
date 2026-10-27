import ConAgua.Arena.IndT.GenRec3
import ConAgua.Verdict.IndBRec6
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

/-!
# Error refinement of `gen_rec_check` (lane `verdicts-b`, helper `ib`)

Mirrors `gckW_simC`: the prep (its error claim a hypothesis, `hPrep`, in the twin's continuation
form; its ok case through `grpW_okC`), then `class_fe_r` and `flush_caches` (`closedNV`), the rules
(`classRecsRulesOk_claim`), the pops and the flush (`closedNV`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtorNf dMajor dClassGen dRec)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model gckE_spec (p : Prog) (hf : p.lookup "gen_rec_check" = some genRecCheckL)
  fns [hf ↦ gckE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

theorem ErrClaim.of_runB {α : Type} {T T' : AM α} {a a' : AState} {e : Err}
    (h : T.run a = T'.run a') (h' : ErrClaim T' a' e) : ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, by rw [h]; exact hce, hc⟩

section sims
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p)
  (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p) (hU : UceProg p)

include hkp henv hV hApd hCrk hIlpf hnv hcE hU in
/-- **`gen_rec_check`'s model error claim** (`gckW_simC`'s hypotheses). -/
theorem gckE_claim (P : GrcProg p) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR) (n : Nat) (hn : n ≤ 2 ^ 62) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp nested pO pL tO tL rd mO mL cO cL bO bL : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {cvTas : List IConstantVal} {block : List IConstantInfo}
    (hC : StageC dn vis fe env m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hpar : decHL m pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop m)
    (htbl : PSlR decNCN tbl tO tL m) (hrd : DecB (fun m => decCR m rd.toNat) m rdv)
    (hms : PSlR decTM ms mO mL m) (hcv : PSlR decCVp cvTas cO cL m)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block) (hlp : ClassesLp m mO mL)
    (hP : RcMR m) (hA : AbsOK m) (hkeep : ∀ f ∈ grcKeepCalleesC, AbsKeep p f)
    (hcoh : ConRon.Bridge.IFEnvCoh fe) (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env)
    {pP : ConLeche.BlockShape} {paramsP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {rdP : ConLeche.ClassRead} {MsP : List ConLeche.TargetMajor} {cvTasP : List ConLeche.ConstantVal}
    {blockP : List ConLeche.ConstantInfo}
    (hsh : dShape a.store bs = some pP) (hparP : Frontend.denoteEList a.store params = some paramsP)
    (htblP : tbl.mapM (dCtorNf a.store) = some tblP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a.store rdv = some rdP)
    (hmsP : ms.mapM (dMajor a.store) = some MsP)
    (hcvTP : cvTas.mapM (Frontend.denoteCV a.store) = some cvTasP)
    (hblkP : Frontend.denoteCIList a.store block = some blockP)
    (hT : ∀ cv ∈ cvTasP, ConLeche.Expr.WScoped 0 cv.type)
    (hMsT : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR)
    (hPrep : ∀ e, callE p n "gen_rec_check_prep"
        [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL] m = .error e →
      ∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        ErrClaim (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
          grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
            grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))) a e) :
    ∀ e, gckE p (n + 1) m vis pp nested pO pL tO tL rd mO mL cO cL bO bL = .error e →
      ErrClaim (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms cvTas block) a e := by
  intro e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  obtain ⟨hrd3, -, hrcD, hrcb, -⟩ := crWords hrd
  rw [gckE.arm1] at he
  rw [genRecCheck_split]
  cases h1 : callE p n "gen_rec_check_prep" [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL] m with
  | error e1 =>
    rw [h1, gckE.k_gen_rec_check_prep.none] at he
    cases he
    exact hPrep _ h1 _
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, gckE.k_gen_rec_check_prep.arm1] at he
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := by
    cases n with
    | zero =>
      obtain ⟨e', he', -⟩ := callE_zero p "gen_rec_check_prep"
        [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL] m
      rw [h1] at he'; cases he'
    | succ k => exact ⟨k, rfl⟩
  obtain ⟨s1, rfl, -, hw1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (grp_spec p P.prep n _ vis pp nested pO pL tO tL rd mO mL cO cL bO bL) (callW_of_callE h1)
  obtain ⟨G, cvGs, a1, hrunP, hC1, hg1, hG1, hns1, -, hcg1, hA1, hP1, c1', gP, cvGsP, hgP, hcvGs, hfrG, henvR⟩ :=
    grpW_okC hkp henv hV hApd hCrk hIlpf P hclR hfR n (by omega) hw1 hC hbs hrb hpar hparb htbl hrd hms hcv
      hblk hlp hP hA hkeep hsh hparP htblP hrdP hmsP hcvTP hblkP hT hMsT hfRc
  have hS1 := hC1.stage
  have e2 : rdW (s1.mem.arr64 IW) (rd + 2) = rdW (m.arr64 IW) (rd + 2) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  have e3 : rdW (s1.mem.arr64 IW) (rd + 3) = rdW (m.arr64 IW) (rd + 3) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  rw [e2, e3] at he
  refine ErrClaim.of_runB (hrunP (grcTwinR V fe bs rdv)) ?_
  unfold grcTwinR
  -- `class_fe_r`
  cases h2 : callE p (n + 1) "class_fe_r" [pp, r1.tail.headD 0, r1.tail.tail.headD 0, rdW (m.arr64 IW) (rd + 2),
      rdW (m.arr64 IW) (rd + 3), vis] s1.mem with
  | error e2 =>
    rw [h2, gckE.k_class_fe_r.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, gckE.k_class_fe_r.arm1] at he
  obtain ⟨s2, rfl, -, hS2, hg2, hpv2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (classFeR_refines p P.cfr (n + 1) _ a1 dn vis fe pp _ _ _ _ bs cvGs rdv.recCls hS1 (hbs.1.grow (decBS_mono _) hg1)
      hcg1 (hrcD.grow (OMono.decNL _ _) hg1)) (callW_of_callE h2)
  have hA2 := hkeep _ (by simp [grcKeepCalleesC]) _ _ _ _ _ (callW_of_callE h2) hA1
  have hsh1 := ConRon.Bridge.Inductives.dShape_ext c1'.ext _ _ hsh
  have hfeR : ConRon.Bridge.IFEnvOK (ConLeche.consBlockRecsBare pP 0
      ((cvGsP.zip rdv.recCls).map fun x => (x.1, x.2)) env) (ConRon.Arena.classFeR bs cvGs rdv.recCls fe).1 a1 :=
    (ConRon.Bridge.Inductives.GR.classFeR_go_ok hC1.check.state bs pP hsh1 (fun c => c) cvGs cvGsP rdv.recCls 0
      fe env [] hC1.check.ienv hcoh (ConRon.Bridge.denoteFEnv_mono c1'.ext hfe)
      (ConRon.Bridge.TablesStored.of_envWF henv) hcvGs).1
  have hvis : fe.visibleBelow = vis.toNat := hS.1.env.vis
  have hview : ((ConRon.Arena.classFeR bs cvGs rdv.recCls fe).1.restrictTo fe.visibleBelow).find? =
      fe.find? := by
    simp only [ConRon.Arena.classFeR]
    rw [ConRon.Bridge.Inductives.GR.classFeR_go_view bs fe.visibleBelow _ 0 fe [] (Nat.le_refl _)]
    · rfl
    · intro x hx
      obtain ⟨cP, hcP, hd⟩ := ConRon.Bridge.Inductives.mapM_option_mem hcvGs x.1 (List.of_mem_zip hx).1
      exact ConRon.Bridge.IFEnvOK.find?_none hC1.check.ienv (ConRon.Bridge.denoteCV_name hd) (hfrG cP hcP)
  have hie2R : ConRon.Bridge.IFEnvOK env
      ((ConRon.Arena.classFeR bs cvGs rdv.recCls fe).1.restrictTo fe.visibleBelow) a1 :=
    ConRon.Bridge.Inductives.RC.IFEnvOK.of_find? hC1.check.ienv hview
      (fun n => by simp only [IFEnv.rawTable?, IFEnv.restrictTo, ConRon.Arena.classFeR,
        ConRon.Bridge.Inductives.GR.classFeR_go_tbls bs _ 0 fe []])
  have hpop := ConRon.Bridge.Inductives.GR.classFeR_pop bs cvGs rdv.recCls fe
  generalize hfrr : ConRon.Arena.classFeR bs cvGs rdv.recCls fe = FR at hS2 hpv2 hfeR hie2R hpop
  obtain ⟨feR, prevs⟩ := FR
  simp only at hS2 hpv2 hfeR hie2R hpop
  dsimp only
  rw [hvis]
  refine ErrClaim.bind_right (flushCaches_run a1) ?_
  -- the flush into the rule-less recursors' environment
  cases h3 : callE p (n + 1) "flush_caches" [] s2.mem with
  | error e3 =>
    rw [h3, gckE.k_flush_caches.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, gckE.k_flush_caches.arm1] at he
  obtain ⟨s3, rfl, -, hfok, hfm⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (flushCaches_spec p P.flush (n + 1) _) (callW_of_callE h3)
  obtain ⟨hS3, hg3⟩ := flush_stage hS2 hfok
  rw [← hfm] at hS3 hg3
  have hg23 := hg2.trans hg3
  have hA3 : AbsOK s3.mem := by rw [hfm]; exact AFr.of_frame (flushMem_frame _) (by decide) (by decide) hA2
  have hg13 := hg1.trans hg23
  obtain ⟨hok11, hi11, -⟩ := (⟨hC1.check.state, hC1.check.pins, hfeR⟩ :
    ConRon.Bridge.Inductives.ReadOK _ feR a1).flush (μ := V) (flushCaches_run a1)
  have hC3 : StageC dn (r2.headD 0) feR (ConLeche.consBlockRecsBare pP 0
      ((cvGsP.zip rdv.recCls).map fun x => (x.1, x.2)) env) s3.mem { a1 with caches := Caches.empty } :=
    hC1.of_checkE hS3 hA3 hok11 (ConRon.Arena.Ext.refl _)
  have e2' : rdW (s3.mem.arr64 IW) (rd + 2) = rdW (m.arr64 IW) (rd + 2) :=
    partsRdIW_grow hg13 (by rw [UInt64.toNat_add]; simp; omega)
  have e3' : rdW (s3.mem.arr64 IW) (rd + 3) = rdW (m.arr64 IW) (rd + 3) :=
    partsRdIW_grow hg13 (by rw [UInt64.toNat_add]; simp; omega)
  rw [e2', e3'] at he
  have hcg3 := hcg1.grow hg23
  have hie : ConRon.Bridge.Inductives.IFEnvOKS env (feR.restrictTo vis.toNat)
      ({ a1 with caches := Caches.empty } : AState).store := by
    rw [← hvis]; exact hie2R.toS
  have henvR' := henvR (fun c => c)
  -- the rules
  cases h4 : callE p (n + 1) "class_recs_rules_ok" [vis, r2.headD 0, r1.headD 0, rdW (m.arr64 IW) (rd + 2),
      rdW (m.arr64 IW) (rd + 3), r1.tail.headD 0, r1.tail.tail.headD 0] s3.mem with
  | error e4 =>
    rw [h4, gckE.k_class_recs_rules_ok.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    exact CoreSpecE.of_callE (classRecsRulesOk_claim hkp hApd hnv hcE hU P.crr (n + 1) (by omega) ⟨s3.mem, Locals.init []⟩
      { a1 with caches := Caches.empty } henvR' vis (r2.headD 0) feR (r1.headD 0) _ _ _ _ G rdv.recCls cvGs hC3
      (hG1.grow (decCG_mono _) hg23) hns1 (hrcD.grow (OMono.decNL _ _) hg13) hrcb hcg3
      (hS3.lt64 hcg3.1) hA3 hgP hcvGs hie) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, gckE.k_class_recs_rules_ok.arm1] at he
  cases h5 : callE p (n + 1) "gen_rec_check_pop_all" [r2.headD 0, r2.tail.headD 0, r2.tail.tail.headD 0] m4 with
  | error e5 =>
    rw [h5, gckE.k_gen_rec_check_pop_all.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, gckE.k_gen_rec_check_pop_all.arm1] at he
  cases h6 : callE p (n + 1) "flush_caches" [] m5 with
  | error e6 =>
    rw [h6, gckE.k_flush_caches_2.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h6
  | ok q6 =>
  rw [h6, gckE.k_flush_caches_2.arm1] at he
  cases he

include hkp henv hV hApd hCrk hIlpf hnv hcE hU in
/-- **`gen_rec_check`'s error claim** (every fuel; `genRecCheck_refinesC`'s hypotheses), modulo the
prep's error claim `hPrep` (the twin's continuation form, at the call's fuel). -/
theorem genRecCheck_claim (P : GrcProg p) {fsR : List FnName}
    (hclR : closedA p rcFreeA rcFreeC fsR = true) (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR) (N : Nat)
    (hN : N ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {pp nested pO pL tO tL rd mO mL cO cL bO bL : Word} {bs : BlockShape} {params : List EIdx}
    {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead} {ms : List TargetMajor}
    {cvTas : List IConstantVal} {block : List IConstantInfo}
    (hC : StageC dn vis fe env s₀.mem a₀) (hbs : BSOK s₀.mem pp.toNat bs) (hrb : RecsB s₀.mem pp)
    (hpar : decHL s₀.mem pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop s₀.mem)
    (htbl : PSlR decNCN tbl tO tL s₀.mem) (hrd : DecB (fun m => decCR m rd.toNat) s₀.mem rdv)
    (hms : PSlR decTM ms mO mL s₀.mem) (hcv : PSlR decCVp cvTas cO cL s₀.mem)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) s₀.mem block) (hlp : ClassesLp s₀.mem mO mL)
    (hP : RcMR s₀.mem) (hA : AbsOK s₀.mem)
    (hkeep : ∀ f ∈ grcKeepCalleesC, AbsKeep p f) (hcoh : ConRon.Bridge.IFEnvCoh fe)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env)
    {pP : ConLeche.BlockShape} {paramsP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {rdP : ConLeche.ClassRead} {MsP : List ConLeche.TargetMajor} {cvTasP : List ConLeche.ConstantVal}
    {blockP : List ConLeche.ConstantInfo}
    (hsh : dShape a₀.store bs = some pP) (hparP : Frontend.denoteEList a₀.store params = some paramsP)
    (htblP : tbl.mapM (dCtorNf a₀.store) = some tblP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a₀.store rdv = some rdP)
    (hmsP : ms.mapM (dMajor a₀.store) = some MsP)
    (hcvTP : cvTas.mapM (Frontend.denoteCV a₀.store) = some cvTasP)
    (hblkP : Frontend.denoteCIList a₀.store block = some blockP)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.ClassMajScoped pP.nP M)
    (hT : ∀ cv ∈ cvTasP, ConLeche.Expr.WScoped 0 cv.type) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR)
    (hPrep : ∀ n, n + 1 ≤ N → ∀ e, callE p n "gen_rec_check_prep"
        [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL] s₀.mem = .error e →
      ∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        ErrClaim (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
          grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
            grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))) a₀ e) :
    CoreSpecE p N "gen_rec_check" [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL]
      (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms cvTas block) s₀ a₀ := by
  cases N with
  | zero => exact CoreSpecE.zero _ _ _ _ _ _
  | succ n =>
    refine CoreSpecE.of_runs fun e hc => ?_
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    exact gckE_claim hkp henv hV hApd hCrk hIlpf hnv hcE hU P hclR hfR n (by omega) hC hbs hrb hpar hparb htbl hrd
      hms hcv hblk hlp hP hA hkeep hcoh hfe hsh hparP htblP hrdP hmsP hcvTP hblkP hT
      (fun M hM => (hMs M hM).1) hfRc (hPrep n (by omega)) e
      (triple_of_callE_err (gckE_spec p P.grc (n + 1) s₀ vis pp nested pO pL tO tL rd mO mL cO cL bO bL) hc
        (Err.code_ne_of_cls hk0))

end sims

end L.Ind
