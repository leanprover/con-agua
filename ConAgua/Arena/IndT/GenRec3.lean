import ConAgua.Arena.IndT.GenRec2
import ConAgua.Arena.IndT.KeepC
import ConAgua.Arena.IndT.RecGen10

/-!
# `genRecCheck`, `checkBlockRec` under `StageC` (lane `indstaget`, helper `grc`)

`gen_rec_check`'s model (`gckW`, `IndInstallSpec41`) under `StageC`: the prep (`grpW_okC`, parts
`GenRec1`/`GenRec2`), then the pushes, the rules, the pops and the flushes; twin side con-ron's
`genRecCheck_spec`'s proof: the pushed index (`GR.classFeR_go_ok`; the constructors' view,
`GR.classFeR_go_view`, `RC.IFEnvOK.of_find?`), the flush into it (`ReadOK.flush`; the rules run
under `StageC` at the rule-less recursors' environment `consBlockRecsBare`, well formed by
`grpCW_okC`), the rules (`classRecsRulesOk_refinesC`, `classRecsRulesOk_spec`), the flush back
(`ReadOK.flush` at the entry index; the popped index answers alike, `GR.classFeR_pop`).
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dCtorNf dMajor dClassGen dRec)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- Two indexes that answer alike (con-ron's `GR.FEq`) find alike. -/
theorem feq_find {x y : IFEnv} (h : ConRon.Bridge.Inductives.GR.FEq x y) : x.find? = y.find? := by
  funext k
  simp only [IFEnv.find?, h.2.2.1 k, h.2.1]

section sims
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p)
  (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p)

include hkp henv hV hApd hCrk hIlpf in
/-- **`gen_rec_check_prep`'s model under `StageC`** (`grpW_ok`'s). -/
theorem grpW_okC (P : GrcProg p) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR) (n : Nat) (hn : n ≤ 2 ^ 62) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp nested pO pL tO tL rd mO mL cO cL bO bL : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {cvTas : List IConstantVal} {block : List IConstantInfo} {r : List Word} {m' : Mem}
    (h : grpW p n m vis pp nested pO pL tO tL rd mO mL cO cL bO bL = some (r, m'))
    (hC : StageC dn vis fe env m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hpar : decHL m pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop m)
    (htbl : PSlR decNCN tbl tO tL m) (hrd : DecB (fun m => decCR m rd.toNat) m rdv)
    (hms : PSlR decTM ms mO mL m) (hcv : PSlR decCVp cvTas cO cL m)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block) (hlp : ClassesLp m mO mL)
    (hP : RcMR m) (hA : AbsOK m) (hkeep : ∀ f ∈ grcKeepCalleesC, AbsKeep p f)
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
    (hMsT : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR) :
    ∃ G cvGs a', (∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
          grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
            grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))).run a = (k G cvGs).run a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ DecB (fun m => decCG m (r.headD 0).toNat) m' G ∧
      G.nP + G.slots.length < 2 ^ 64 ∧ G.slots = rdv.slots ∧ decCVS m' r.tail cvGs ∧ AbsOK m' ∧
      RcMR m' ∧ ConRon.Bridge.CoreStep V env fe a a' ∧
      ∃ (gP : ConLeche.ClassGen) (cvGsP : List ConLeche.ConstantVal), dClassGen a'.store G = some gP ∧
        cvGs.mapM (Frontend.denoteCV a'.store) = some cvGsP ∧ (∀ c ∈ cvGsP, env.find? c.name = none) ∧
        ∀ f : Nat → Nat, ConLeche.EnvWF (ConLeche.consBlockRecsBare pP 0
          ((cvGsP.zip rdv.recCls).map fun x => (x.1, f x.2)) env) := by
  unfold grpW at h
  obtain ⟨⟨rA, mA⟩, cA, h⟩ := of_K h rfl
  rw [grpKA_some] at h
  obtain ⟨⟨hsz5, hnpk, hns⟩, cvRis, aA, hrunA, hCA, hgA, hPA, hkA, hcsA, hAA, cA', cvRisP, hcvRP, hwRis⟩ :=
    grpAW_okC hkp henv hV hApd hCrk P hclR hfR n hn cA hC hbs hrb hrd hms hblk hP hA hkeep hsh hblkP
  have hszA : (mA.arr64 IW).size = (m.arr64 IW).size := hkA IW
  obtain ⟨G, cvGs, a', hrunB, hC', hg', hG', hns', hsl', hcg', hA', hR', cB, hrest⟩ := grpBW_okC hkp henv hApd hCrk hIlpf P n hn h
    hCA (hbs.grow hgA)
    (hrb.grow hgA (by have := hbs.ptop; omega)) (decHL_grow' hgA hparb hpar) (Nat.le_trans hparb hgA.1)
    (htbl.grow (fun q => decNCN_mono q) hgA) (hrd.grow (decCR_mono _) hgA) (hms.grow (fun q => decTM_mono q) hgA)
    (hcv.grow (fun q => OMono.decCVp q) hgA) (hlp.grow hms hgA hkA hC.stage.2.2.2.1) (csRes_decB hcsA) hns hnpk
    (by rw [hszA]; exact hsz5) hPA hAA hkeep
    (ConRon.Bridge.Inductives.dShape_ext cA'.ext _ _ hsh) (ConRon.Bridge.denoteEList_ext cA'.ext _ _ hparP)
    (ConRon.Bridge.Inductives.dCtorNf_ext.list cA'.ext _ _ htblP)
    (ConRon.Bridge.Inductives.dClassRead_ext cA'.ext _ _ hrdP)
    (ConRon.Bridge.Inductives.dMajor_ext.list cA'.ext _ _ hmsP)
    (ConRon.Bridge.Inductives.dExt_denoteCV.list cA'.ext _ _ hcvTP) hT hMsT hcvRP hwRis hclR hfRc
  exact ⟨G, cvGs, a', fun {β} k => by rw [hrunA]; exact hrunB k, hC', hgA.trans hg', hG', hns', hsl', hcg', hA',
    hR', cA'.trans cB, hrest⟩

include hkp henv hV hApd hCrk hIlpf in
/-- **`gen_rec_check`'s model refines `genRecCheck` under `StageC`** (`gckW_sim`'s): the view and
index handed back with con-ron's `CheckOK` at the entry environment, the twin's run a `CoreStep`. -/
theorem gckW_simC (P : GrcProg p) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
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
    (hMsT : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR) :
    Sim (gckW p n m vis pp nested pO pL tO tL rd mO mL cO cL bO bL)
      (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms cvTas block) a
      (fun r x m' a' => StageC dn (r.headD 0) x.1 env m' a' ∧ IWGrow m m' ∧ decRRS m' r.tail x.2 ∧
        AbsOK m' ∧ RcMR m' ∧ ConRon.Bridge.CoreStep V env fe a a') := by
  intro r m' h
  have hS := hC.stage
  unfold gckW at h
  obtain ⟨hrd3, -, hrcD, hrcb, -⟩ := crWords hrd
  -- the prep
  obtain ⟨⟨r1, m1⟩, c1, h⟩ := of_K h rfl
  rw [gckK1_some] at h
  rcases n with _ | n
  · rw [callW_zero] at c1; cases c1
  obtain ⟨s1, rfl, -, hw1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (grp_spec p P.prep n _ vis pp nested pO pL tO tL rd mO mL cO cL bO bL) c1
  obtain ⟨G, cvGs, a1, hrunP, hC1, hg1, hG1, hns1, -, hcg1, hA1, hP1, c1', gP, cvGsP, hgP, hcvGs, hfrG, henvR⟩ :=
    grpW_okC hkp henv hV hApd hCrk hIlpf P hclR hfR n (by omega) hw1 hC hbs hrb hpar hparb htbl hrd hms hcv hblk hlp hP hA
      hkeep hsh hparP htblP hrdP hmsP hcvTP hblkP hT hMsT hfRc
  have hS1 := hC1.stage
  have e2 : rdW (s1.mem.arr64 IW) (rd + 2) = rdW (m.arr64 IW) (rd + 2) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  have e3 : rdW (s1.mem.arr64 IW) (rd + 3) = rdW (m.arr64 IW) (rd + 3) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  rw [e2, e3] at h
  -- the pushes
  obtain ⟨⟨r2, m2⟩, c2, h⟩ := of_K h rfl
  rw [gckK2_some] at h
  obtain ⟨s2, rfl, -, hS2, hg2, hpv2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (classFeR_refines p P.cfr (n + 1) _ a1 dn vis fe pp _ _ _ _ bs cvGs rdv.recCls hS1 (hbs.1.grow (decBS_mono _) hg1)
      hcg1 (hrcD.grow (OMono.decNL _ _) hg1)) c2
  have hP2 := RcMR.ofClosed hclR (hfRc _ (by decide)) c2 hP1
  have hA2 := hkeep _ (by simp [grcKeepCalleesC]) _ _ _ _ _ c2 hA1
  -- the twin's pushed index, and the constructors' view inside it
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
  -- the flush into the rule-less recursors' environment
  obtain ⟨⟨r3, m3⟩, c3, h⟩ := of_K h rfl
  rw [gckK3_some] at h
  obtain ⟨s3, rfl, -, hfok, hfm⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (flushCaches_spec p P.flush (n + 1) _) c3
  have hP3 := RcMR.ofClosed hclR (hfRc _ (by decide)) c3 hP2
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
  -- the rules
  have e2' : rdW (s3.mem.arr64 IW) (rd + 2) = rdW (m.arr64 IW) (rd + 2) :=
    partsRdIW_grow hg13 (by rw [UInt64.toNat_add]; simp; omega)
  have e3' : rdW (s3.mem.arr64 IW) (rd + 3) = rdW (m.arr64 IW) (rd + 3) :=
    partsRdIW_grow hg13 (by rw [UInt64.toNat_add]; simp; omega)
  rw [e2', e3'] at h
  have hcg3 := hcg1.grow hg23
  have hie : ConRon.Bridge.Inductives.IFEnvOKS env (feR.restrictTo vis.toNat)
      ({ a1 with caches := Caches.empty } : AState).store := by
    rw [← hvis]; exact hie2R.toS
  have henvR' := henvR (fun c => c)
  obtain ⟨⟨r4, m4⟩, c4, h⟩ := of_K h rfl
  rw [gckK4_some] at h
  obtain ⟨s4, rfl, -, hok4, ⟨hC4, hg4, hd4⟩, hA4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (classRecsRulesOk_refinesC hkp hApd P.crr (n + 1) (by omega) _ _ henvR' vis (r2.headD 0) feR (r1.headD 0) _ _ _ _ G
      rdv.recCls cvGs hC3 (hG1.grow (decCG_mono _) hg23) hns1 (hrcD.grow (OMono.decNL _ _) hg13) hrcb hcg3
      (hS3.lt64 hcg3.1) hA3 hgP hcvGs hie) c4
  have hP4 := RcMR.ofClosed hclR (hfRc _ (by decide)) c4 hP3
  have hrun4 := AM.run_of_ok _ _ hok4
  obtain ⟨c12', -⟩ := ConRon.Bridge.Inductives.classRecsRulesOk_spec feR vis.toNat
    (ConRon.Bridge.CoreSpec.of_core rfl) henvR' G gP rdv.recCls cvGs cvGsP cvGs cvGsP rdv.recCls _ _ _
    hC3.check ⟨hgP, hcvGs, hcvGs, hie⟩ hrun4
  generalize AM.res (ConRon.Arena.classRecsRulesOk V vis.toNat feR G rdv.recCls cvGs cvGs rdv.recCls)
    { a1 with caches := Caches.empty } = out at hrun4 hd4
  generalize AM.st (ConRon.Arena.classRecsRulesOk V vis.toNat feR G rdv.recCls cvGs cvGs rdv.recCls)
    { a1 with caches := Caches.empty } = a4 at hrun4 hC4 c12'
  -- the pops
  obtain ⟨⟨r5, m5⟩, c5, h⟩ := of_K h rfl
  rw [gckK5_some] at h
  obtain ⟨s5, rfl, -, hS5, hg5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (genRecCheckPopAll_refines P.eix P.ers P.ept P.gpa (n + 1) _ a4 dn (r2.headD 0) feR _ _ prevs hC4.stage
      (hpv2.grow (hg3.trans hg4))) c5
  have hP5 := RcMR.ofClosed hclR (hfRc _ (by decide)) c5 hP4
  have hA5 := hkeep _ (by simp [grcKeepCalleesC]) _ _ _ _ _ c5 hA4
  -- the flush back
  obtain ⟨⟨r6, m6⟩, c6, h⟩ := of_K h rfl
  rw [gckK6_some] at h
  obtain ⟨s6, rfl, -, hfok6, hfm6⟩ := triple_of_callW (s₀ := ⟨s5.mem, Locals.init []⟩)
    (flushCaches_spec p P.flush (n + 1) _) c6
  have hP6 := RcMR.ofClosed hclR (hfRc _ (by decide)) c6 hP5
  obtain ⟨hS6, hg6⟩ := flush_stage hS5 hfok6
  have hA6 : AbsOK s6.mem := by rw [hfm6]; exact AFr.of_frame (flushMem_frame _) (by decide) (by decide) hA5
  rw [← hfm6] at hS6 hg6
  have hext12 : ConRon.Arena.Ext a.store a4.store := c1'.ext.trans c12'.ext
  have hpins12 : a4.pins = a.pins := c12'.pins.trans c1'.pins
  obtain ⟨hok13, -, -⟩ := (⟨c12'.ok.state, hC.check.pins.mono hext12 hpins12, hC.check.ienv.mono hext12⟩ :
    ConRon.Bridge.Inductives.ReadOK env fe a4).flush (μ := V) (flushCaches_run a4)
  have hok13' : ConRon.Bridge.CheckOK V env (prevs.foldr (fun x acc => acc.popTemp x.1 x.2) feR)
      { a4 with caches := Caches.empty } :=
    ⟨hok13.state, hok13.caches, hok13.pins,
      ConRon.Bridge.Inductives.RC.IFEnvOK.of_find? hok13.ienv (feq_find hpop)
        (fun n => by simp only [IFEnv.rawTable?, hpop.2.2.2])⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  refine ⟨(prevs.foldr (fun x acc => acc.popTemp x.1 x.2) feR, out), { a4 with caches := Caches.empty }, ?_,
    hC.of_checkE (by simpa using hS6) hA6 hok13' hext12, hg1.trans (hg23.trans (hg4.trans (hg5.trans hg6))),
    by have := hd4.grow (hg5.trans hg6); simp only [decRRS] at this ⊢; simpa using this, hA6, hP6,
    ⟨hok13, hext12, hpins12⟩⟩
  rw [genRecCheck_split, hrunP]
  simp only [grcTwinR, hfrr, StateT.run_bind, flushCaches_run, except_ok_bind, hvis, hrun4]
  rfl

include hkp henv hV hApd hCrk hIlpf in
/-- **`gen_rec_check(vis, p, nested, params.off, params.len, tbl.off, tbl.len, rd, ms.off, ms.len,
cvTas.off, cvTas.len, block.off, block.len)` refines `genRecCheck` under `StageC`**
(`genRecCheck_refines`' statement, `StageR` replaced by `StageC`): besides `genRecCheck_refines`'
hypotheses, the inputs' denotations and scoping as con-ron's `genRecCheck_spec` asks and the index
coherent (`IFEnvCoh`); after it, `StageC` at the returned view and index (con-ron's `CheckOK` at the
entry environment) and the twin's run a `CoreStep`. The program facts: `ValProg p` and `AbsKeep`
of `check_constant_val` (the stream's recursors, `classStreamRecs_refinesC`). Through
`block_large_elim_allowed`'s contract (`IndInstallSpec39`). -/
@[refines ConRon.Arena.genRecCheck]
theorem genRecCheck_refinesC (P : GrcProg p) {fsR : List FnName}
    (hclR : closedA p rcFreeA rcFreeC fsR = true) (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
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
    (hT : ∀ cv ∈ cvTasP, ConLeche.Expr.WScoped 0 cv.type) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "gen_rec_check"
      [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms cvTas block) a₀ ∧
      StageC dn (r.headD 0) (AM.res (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms cvTas
        block) a₀).1 env s'.mem (AM.st (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms
        cvTas block) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decRRS s'.mem r.tail (AM.res (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms cvTas
        block) a₀).2 ∧ AbsOK s'.mem ∧ RcMR s'.mem ∧
      ConRon.Bridge.CoreStep V env fe a₀ (AM.st (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl
        rdv ms cvTas block) a₀); ⊤⦄ := by
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  refine triple_post (gck_spec p P.grc n s₀ vis pp nested pO pL tO tL rd mO mL cO cL bO bL) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hok, hQ⟩ := Sim.run (gckW_simC hkp henv hV hApd hCrk hIlpf P hclR hfR n (by omega) hC hbs hrb hpar hparb htbl
    hrd hms hcv hblk hlp hP hA hkeep hcoh hfe hsh hparP htblP hrdP hmsP hcvTP hblkP hT
    (fun M hM => (hMs M hM).1) hfRc) hm
  exact ⟨hl, hok, hQ⟩

include hkp henv hV hApd hCrk hIlpf in
/-- **`check_block_rec` refines `checkBlockRec` under `StageC`** (through `genRecCheck_refinesC`;
`checkBlockRec_refines`' statement, `StageR` replaced by `StageC`, the twin's run a `CoreStep`). -/
@[refines ConRon.Arena.checkBlockRec]
theorem checkBlockRec_refinesC (hp : p.lookup "check_block_rec" = some checkBlockRec)
    (P : GrcProg p) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR)
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (pp nested pO pL tO tL rd mO mL bO bL cO cL : Word) (bs : BlockShape) (params : List EIdx)
    (tbl : List NestCtorNf) (rdv : ClassRead) (ms : List TargetMajor) (cvTas : List IConstantVal)
    (block : List IConstantInfo) (hC : StageC dn vis fe env s₀.mem a₀)
    (hpre : BSOK s₀.mem pp.toNat bs ∧
        decHL s₀.mem pO.toNat pL.toNat = some params ∧ pO.toNat + pL.toNat ≤ iwTop s₀.mem ∧
        PSlR decNCN tbl tO tL s₀.mem ∧ DecB (fun m => decCR m rd.toNat) s₀.mem rdv ∧
        PSlR decTM ms mO mL s₀.mem ∧ PSlR decCVp cvTas cO cL s₀.mem ∧
        DecB (fun m => decEBlk dn m bO.toNat bL.toNat) s₀.mem block)
    (hrb : RecsB s₀.mem pp) (hlp : ClassesLp s₀.mem mO mL) (hP : RcMR s₀.mem) (hA : AbsOK s₀.mem)
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
    (hT : ∀ cv ∈ cvTasP, ConLeche.Expr.WScoped 0 cv.type) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_rec"
      [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, bO, bL, cO, cL]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀ ∧
      StageC dn (r.headD 0)
        (AM.res (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀).1 env
        s'.mem (AM.st (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decRRS s'.mem r.tail
        (AM.res (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀).2 ∧
      AbsOK s'.mem ∧ RcMR s'.mem ∧
      ConRon.Bridge.CoreStep V env fe a₀
        (AM.st (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀); ⊤⦄ := by
  refine triple_post (icr_spec p hp n s₀ vis pp nested pO pL tO tL rd mO mL bO bL cO cL) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hbs, hpar, hparb, htbl, hrd, hms, hcv, hblk⟩ := hpre
  have hsim : Sim (icrW p n s₀.mem vis pp nested pO pL tO tL rd mO mL bO bL cO cL)
      (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀
      (fun r x m' a' => StageC dn (r.headD 0) x.1 env m' a' ∧ IWGrow s₀.mem m' ∧ decRRS m' r.tail x.2 ∧
        AbsOK m' ∧ RcMR m' ∧ ConRon.Bridge.CoreStep V env fe a₀ a') := by
    unfold icrW ConRon.Arena.checkBlockRec
    refine Sim.post (K := icrK) rfl (fun _ _ => rfl)
      (installSimCall (Q := fun r x m' a' => StageC dn (r.headD 0) x.1 env m' a' ∧ IWGrow s₀.mem m' ∧
        decRRS m' r.tail x.2 ∧ AbsOK m' ∧ RcMR m' ∧ ConRon.Bridge.CoreStep V env fe a₀ a')
        (genRecCheck_refinesC hkp henv hV hApd hCrk hIlpf P hclR hfR n hn ⟨s₀.mem, Locals.init []⟩ a₀ hC hbs hrb hpar hparb
          htbl hrd hms hcv hblk hlp hP hA hkeep hcoh hfe hsh hparP htblP hrdP hmsP hcvTP hblkP hMs hT hfRc)
        (fun r s' h => by obtain ⟨-, hok, hQ⟩ := h; exact ⟨hok, hQ⟩)) ?_
    rintro r x m a ⟨h1, h2, h3, h4, h6, h5⟩
    exact ⟨h1, h2, by simp only [decRRS] at h3 ⊢; simpa using h3, h4, h6, h5⟩
  obtain ⟨hok, hQ⟩ := Sim.run hsim hm
  exact ⟨hl, hok, hQ⟩

end sims

end L.Ind
