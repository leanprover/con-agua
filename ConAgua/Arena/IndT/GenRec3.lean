module

import ConAgua.Arena.IndT.StreamRecs
import ConAgua.Verdict.IndBRecPins
public import ConAgua.Arena.IndT.GenRec2
import ConAgua.Verdict.IndBRec6
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.IcvgW
import ConAgua.Arena.IndInstallSpec.InstallIwB
import ConAgua.Arena.IndInstallSpec.PapW
import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndInstallSpec.PosFreeMfr
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndT.GenRec1
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RecCheckSpec.CnfW
import ConAgua.Arena.RecGenSpec.CfhW
import ConAgua.Arena.RecGenSpec.Classes
import ConAgua.Arena.RecGenSpec.FlushStage
import ConAgua.Arena.RefWalk
import ConAgua.Arena.ScratchRefine
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.DeclBase
public import ConAgua.Arena.DeclValSpec
public import ConAgua.Arena.IndInstallSpec.GpbWSimF
public import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import all ConAgua.Arena.IndInstall

@[expose] public section

/-!
# `gen_rec_check_prep`, `gen_rec_check`: one model, one refinement each; `checkBlockRec`

`grp_ref`: `gen_rec_check_prep`'s first part (the capacity guards, `targetRecPins`, `classStreamRecs`,
the family and elimination guards) then `grpB_ref`, against the twin's prep in its continuation form.
`gck_ref`: `gen_rec_check`'s unified model (`gckE`) under `StageC`, both outcomes: the prep
(`grp_ref`), then the pushes, the rules, the pops and the flushes; twin side con-ron's
`genRecCheck_spec`'s proof: the pushed index (`GR.classFeR_go_ok`; the constructors' view,
`GR.classFeR_go_view`, `RC.IFEnvOK.of_find?`), the flush into it (`ReadOK.flush`; the rules run
under `StageC` at the rule-less recursors' environment `consBlockRecsBare`, well formed by
`grpC_ref`), the rules (`classRecsRulesOk_refinesC`, `classRecsRulesOk_spec`), the flush back
(`ReadOK.flush` at the entry index; the popped index answers alike, `GR.classFeR_pop`).
-/


noncomputable section

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

set_option experimental.vcgen true in
/-- **`gen_rec_check`'s unified model**: the prep by its unified model (`grpE`), the pushes, the
flushes and the pops (outside the verdict closure) lifted, the rules through their run (the ok half
reads the call's walk memos). -/
l_model gckE_spec (p : Prog) (P : GrcProg p)
  fns [P.grc ↦ gckE]
  specs [grpE_spec p P.prep n, callW_spec p n "class_fe_r", callW_spec p n "flush_caches",
    callW_spec p n "gen_rec_check_pop_all"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **`check_block_rec`'s unified model**: `gen_rec_check` by its unified model. -/
l_model icrE_spec (p : Prog) (P : GrcProg p) (hf : p.lookup "check_block_rec" = some checkBlockRec)
  fns [hf ↦ icrE list] specs [gckE_spec p P n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `gen_rec_check` gives besides the twin's index and rules `x` (from `m`, `a`): the stage at
the returned view, the growth, the rules' records, `AbsOK`, the walk memos, the core step. -/
structure GckPost (dn : NIdx → Option ConLeche.Name) (env : ConLeche.Env) (fe : IFEnv) (a : AState)
    (r : List Word) (m m' : Mem) (x : IFEnv × List (IConstantVal × TargetMajor × List EIdx)) (a' : AState) :
    Prop where
  stage : StageC dn (r.headD 0) x.1 env m' a'
  grow : IWGrow m m'
  rrs : decRRS m' r.tail x.2
  abs : AbsOK m'
  rc : RcMR m'
  core : ConRon.Bridge.CoreStep V env fe a a'

section sims
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p)
  (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p)

include hkp henv hV hApd hCrk hIlpf in
/-- **`gen_rec_check_prep` refines the twin's prep (`grcTwinA`, in its continuation form), both
outcomes**: the capacity guards, the pins (`trp_ref`), the stream's recursor types
(`classStreamRecs_refinesC` on the run), the family and elimination guards, then the second and
third parts (`grpB_ref`). -/
theorem grp_ref (P : GrcProg p) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR) (n : Nat) (hn : n + 1 ≤ 2 ^ 62) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp nested pO pL tO tL rd mO mL cO cL bO bL : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {cvTas : List IConstantVal} {block : List IConstantInfo}
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
    RefC (VerdictCtxU p) (grpE p (n + 1) m vis pp nested pO pL tO tL rd mO mL cO cL bO bL)
      (fun v => ∃ G cvGs a', (∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
          (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
            grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
              grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))).run a = (k G cvGs).run a') ∧
        GrpPost dn vis fe env pP rdv m a v.1 v.2 G cvGs a')
      (fun e => ∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        ErrClaim (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
          grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
            grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))) a e) := by
  have hS := hC.stage
  have hT64 : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hp8 := hbs.ptop
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.iw.iwSize
  have hbsD : decBS (truncM m) pp.toNat = some bs := hbs.1
  obtain ⟨-, hrecs, -, -, -, hlarge, -⟩ := decBS_some hbsD
  have hrecsP0 := (ConRon.Bridge.Inductives.dShape_inv hsh).2.1
  -- the capacity guards
  by_cases g1 : m.len64 IW + 5 < 5
  · rw [grpE.abort1 p n m vis pp nested pO pL tO tL rd mO mL cO cL bO bL g1]
    exact fun _ _ _ => ErrClaim.of_cls0 rfl
  by_cases g2 : rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (pp + 1) < rdW (m.arr64 IW) (pp + 4)
  · rw [grpE.abort2 p n m vis pp nested pO pL tO tL rd mO mL cO cL bO bL g1 g2]
    exact fun _ _ _ => ErrClaim.of_cls0 rfl
  by_cases g3 : rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (rd + 1) < rdW (m.arr64 IW) (pp + 4)
  · rw [grpE.abort3 p n m vis pp nested pO pL tO tL rd mO mL cO cL bO bL g1 g2 g3]
    exact fun _ _ _ => ErrClaim.of_cls0 rfl
  rw [grpE.arm1 p n m vis pp nested pO pL tO tL rd mO mL cO cL bO bL g1 g2 g3]
  have hcap : (m.arr64 IW).size + 5 < 2 ^ 64 ∧ bs.nP + bs.k < 2 ^ 64 ∧ bs.nP + rdv.slots.length < 2 ^ 64 := by
    obtain ⟨e4, hnP64, -, -⟩ := partsShapeWords (IWGrow.refl m) hbs.1 (by omega)
    have hkb : bs.k < 2 ^ 64 := by
      obtain ⟨o', l', -, hl', hg'⟩ := decAt_some (decBS_some hbsD).1
      have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
    have e1 : rdW (m.arr64 IW) (pp + 1) = UInt64.ofNat bs.k := partsShapeK hbs.dec (by omega)
    obtain ⟨-, hslD, -, -, -⟩ := crWords hrd
    have hsl := decPL_length _ (show decPL (truncM m) (decCS (truncM m)) _ _ = some rdv.slots from hslD)
    refine ⟨?_, ?_, ?_⟩
    · have g1' : ¬ (m.len64 IW + 5).toNat < (5 : Word).toNat := fun e => g1 (UInt64.lt_iff_toNat_lt.mpr e)
      rw [UInt64.toNat_add] at g1'
      simp only [Mem.len64] at g1'
      rw [UInt64.toNat_ofNat_of_lt' (by omega)] at g1'
      simp at g1'
      omega
    · have := word_add_noWrap g2
      rw [e4, e1, UInt64.toNat_ofNat_of_lt' hnP64, UInt64.toNat_ofNat_of_lt' hkb] at this
      exact this
    · have := word_add_noWrap g3
      rw [e4, UInt64.toNat_ofNat_of_lt' hnP64, ← hsl] at this
      exact this
  obtain ⟨hsz5, hnpk, hns⟩ := hcap
  -- `target_rec_pins`
  rcases c1 : callE p n "target_rec_pins" [pp, bO, bL] m with e1 | ⟨r1, m1⟩
  · rw [grpE.k_target_rec_pins.none]
    refine fun hG _ k => ?_
    unfold grcTwinA
    exact ErrClaim.bind_left (RefE.run_err (trpE_spec p P.rp.pins n ⟨m, Locals.init []⟩ pp bO bL) trivial
      ⟨hG.nv, hG.core⟩ (trp_ref P.rp n hS hbs.1 hblk) c1)
  rw [grpE.k_target_rec_pins.arm1]
  obtain ⟨s1, hs1, -, hok1, hS1, hg1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (targetRecPins_refines P.rp n _ a pp bO bL bs block hS hbs.1 hblk)
    (callW_mono (callW_of_callE c1) (Nat.le_add_right n 3))
  simp only at hs1 hS1 hg1; subst hs1
  have hrun1 := AM.run_of_ok _ a hok1
  generalize AM.st (ConRon.Arena.targetRecPins bs block) a = a1 at hrun1 hS1
  have hP1 := RcMR.ofClosed hclR (hfR _ (by decide)) (callW_of_callE c1) hP
  have hA1 := hkeep _ (by simp [grcKeepCalleesC]) _ _ _ _ _ (callW_of_callE c1) hA
  have hk1 := callW_keepW (callW_of_callE c1)
  obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.targetRecPins_spec bs pP block blockP a a1 _
    hC.check.state hC.check.pins ⟨hsh, hblkP⟩ hrun1
  have hC1 : StageC dn vis fe env s1.mem a1 := hC.of_pstep hS1 hA1 p1
  have c1' := p1.toCore hC.check
  -- `class_stream_recs`
  have hrecsP : PSlR decRS bs.recs (rdW (m.arr64 IW) (pp + 2)) (rdW (m.arr64 IW) (pp + 3)) m :=
    bpPSl decRS_mono hrecs hrb (by rw [UInt64.toNat_add]; simp; omega) (by rw [UInt64.toNat_add]; simp; omega)
  have hw2 : rdW (s1.mem.arr64 IW) (pp + 2) = rdW (m.arr64 IW) (pp + 2) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  have hw3 : rdW (s1.mem.arr64 IW) (pp + 3) = rdW (m.arr64 IW) (pp + 3) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  rw [hw2, hw3]
  have hrecs1 := hrecsP.grow (fun q => decRS_mono q) hg1
  have hrecs1P := ConRon.Bridge.Inductives.dRec_ext.list c1'.ext _ _ hrecsP0
  rcases c2 : callE p n "class_stream_recs" [vis, rdW (m.arr64 IW) (pp + 2), rdW (m.arr64 IW) (pp + 3)] s1.mem with
    e2 | ⟨r2, m2⟩
  · rw [grpE.k_class_stream_recs.none]
    refine fun hG _ k => ?_
    unfold grcTwinA
    refine ErrClaim.bind_right hrun1 (ErrClaim.bind_left ?_)
    exact CoreSpecE.of_callE (classStreamRecs_claim hkp henv hV hApd hCrk hG P.ia P.cpy P.slc P.csr n (by omega)
      ⟨s1.mem, Locals.init []⟩ a1 fe vis _ _ bs.recs pP.recs hC1 hA1 (rec3RecsOK_of_decB hrecs1.1 hrecs1.2)
      hrecs1P) c2
  obtain ⟨s2, hs2, -, hok2, hC2, hg2, hcs2, hA2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (classStreamRecs_refinesC hkp henv hV hApd hCrk P.cpy P.ia P.slc P.csr n (by omega) _ a1 fe vis _ _ bs.recs
      pP.recs hC1 hA1 (rec3RecsOK_of_decB hrecs1.1 hrecs1.2) hrecs1P) (callW_of_callE c2)
  simp only at hs2 hC2 hg2 hcs2 hA2; subst hs2
  have hrun2 := AM.run_of_ok _ a1 hok2
  obtain ⟨c2', cvRisP, ⟨hcvRis, hwRis⟩, -⟩ := ConRon.Bridge.Inductives.classStreamRecs_spec fe rfl
    (ConRon.Bridge.CoreSpec.of_core rfl) henv bs.recs pP.recs a1 _ _ hC1.check hrecs1P hrun2
  generalize AM.res (ConRon.Arena.classStreamRecs V fe bs.recs) a1 = cvRis at hrun2 hcs2 hcvRis
  generalize AM.st (ConRon.Arena.classStreamRecs V fe bs.recs) a1 = a2 at hrun2 hC2 hcvRis c2'
  have hS2 := hC2.stage
  have c12 := c1'.trans c2'
  have hP2 := RcMR.ofClosed hclR (hfR _ (by decide)) (callW_of_callE c2) hP1
  have hk2 := callW_keepW (callW_of_callE c2)
  have hg12 := hg1.trans hg2
  -- the family guard
  have hk : rdW (s2.mem.arr64 IW) (pp + 1) = UInt64.ofNat bs.k := by
    rw [partsRdIW_grow hg12 (by rw [UInt64.toNat_add]; simp; omega)]
    exact partsShapeK (hbs.dec) (by omega)
  by_cases hk0' : rdW (s2.mem.arr64 IW) (pp + 1) = 0
  · rw [grpE.k_class_stream_recs.abort1 p n vis pp nested pO pL tO tL rd mO mL cO cL r2 _ hk0']
    have hkz : bs.k = 0 := by
      have h0 : UInt64.ofNat bs.k = 0 := by rw [← hk]; exact hk0'
      have := congrArg UInt64.toNat h0
      rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hnpk)] at this
      simpa using this
    have hkb : (bs.k == 0) = true := by rw [hkz]; rfl
    refine fun _ _ k => ?_
    unfold grcTwinA
    refine ErrClaim.bind_right hrun1 (ErrClaim.bind_right hrun2 ?_)
    simp only [hkb, ite_true]
    exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
  have hkb : (bs.k == 0) = false := by
    cases e : bs.k with
    | zero => rw [e] at hk; exact absurd hk hk0'
    | succ _ => rfl
  -- the elimination guard
  have hL : (rdW (s2.mem.arr64 IW) (pp + 7) != 0) = bs.large := by
    rw [partsRdIW_grow hg12 (by rw [UInt64.toNat_add]; simp; omega)]
    exact installIwB (k := 7) hlarge hsz
  -- the rest, from a state `a4` the twin's prep reaches (`hrunA`)
  have fin : ∀ (a4 : AState), StageC dn vis fe env s2.mem a4 → ConRon.Bridge.CoreStep V env fe a a4 →
      cvRis.mapM (Frontend.denoteCV a4.store) = some cvRisP →
      (∀ {β : Type} (k : List IConstantVal → AM β),
        (grcTwinA V fe bs (nested != 0) ms block k).run a = (k cvRis).run a4) →
      RefC (VerdictCtxU p)
        (grpE.j1 p n vis pp pO pL tO tL rd mO mL cO cL (r2.headD 0) (r2.tail.headD 0) s2.mem)
        (fun v => ∃ G cvGs a', (∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
            (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
              grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
                grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))).run a = (k G cvGs).run a') ∧
          GrpPost dn vis fe env pP rdv m a v.1 v.2 G cvGs a')
        (fun e => ∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
          ErrClaim (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
            grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
              grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))) a e) := by
    intro a4 hC4 c4 hcvRis4 hrunA
    have hk4 := hk1.trans hk2
    refine RefC.mono (grpB_ref hkp henv hApd hCrk hIlpf P n (by omega) hC4 (hbs.grow hg12)
      (hrb.grow hg12 (by have := hbs.ptop; omega)) (decHL_grow' hg12 hparb hpar) (Nat.le_trans hparb hg12.iw)
      (htbl.grow (fun q => decNCN_mono q) hg12) (hrd.grow (decCR_mono _) hg12) (hms.grow (fun q => decTM_mono q) hg12)
      (hcv.grow (fun q => OMono.decCVp q) hg12) (hlp.grow hms hg12 hk4 hS.iw.iwSize) (csRes_decB hcs2) hns hnpk
      (by rw [hk4 IW]; exact hsz5) hP2 hA2 hkeep
      (ConRon.Bridge.Inductives.dShape_ext c4.ext _ _ hsh) (ConRon.Bridge.denoteEList_ext c4.ext _ _ hparP)
      (ConRon.Bridge.Inductives.dCtorNf_ext.list c4.ext _ _ htblP)
      (ConRon.Bridge.Inductives.dClassRead_ext c4.ext _ _ hrdP)
      (ConRon.Bridge.Inductives.dMajor_ext.list c4.ext _ _ hmsP)
      (ConRon.Bridge.Inductives.dExt_denoteCV.list c4.ext _ _ hcvTP) hT hMsT hcvRis4 hwRis hclR hfRc) ?_ ?_
    · rintro v ⟨G, cvGs, a', hrunB, hR⟩
      exact ⟨G, cvGs, a', fun k => (hrunA _).trans (hrunB k),
        { hR with grow := hg12.trans hR.grow, core := c4.trans hR.core }⟩
    · intro e _ hc _ k
      exact ErrClaim.of_run_eqW (hrunA _) (hc k)
  by_cases h7 : rdW (s2.mem.arr64 IW) (pp + 7) = 0
  · rw [grpE.k_class_stream_recs.arm3 p n vis pp nested pO pL tO tL rd mO mL cO cL r2 _ hk0' h7]
    have hl : bs.large = false := by rw [← hL, h7]; rfl
    exact fin a2 hC2 c12 hcvRis fun k => by
      simp only [grcTwinA, StateT.run_bind, hrun1, except_ok_bind, hrun2, hkb, hl, Bool.false_eq_true, ite_false]
  have hl : bs.large = true := by rw [← hL]; simpa using h7
  have hmsD : decPL s2.mem (decTM s2.mem) mO.toNat mL.toNat = some ms :=
    (hms.dec.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg12).get (OMono.decPL (fun q => decTM_mono q) _ _)
  have hmsb : mO.toNat + mL.toNat < 2 ^ 64 := hS.lt64 hms.bound
  have hsh2 := ConRon.Bridge.Inductives.dShape_ext c12.ext _ _ hsh
  have hsrc2 : ShapeSrc s2.mem pp := partsHsrc_grow hg12 (partsShapeFacts hbs.1 hbs.2.1).2.1 hbs.2.1
  have large : ∀ (nb : Word), (nb != 0) = (nested != 0 || ms.any (·.member.isNone)) →
      RefC (VerdictCtxU p)
        (grpE.j2 p n vis pp pO pL tO tL rd mO mL cO cL (r2.headD 0) (r2.tail.headD 0) nb s2.mem)
        (fun v => ∃ G cvGs a', (∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
            (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
              grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
                grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))).run a = (k G cvGs).run a') ∧
          GrpPost dn vis fe env pP rdv m a v.1 v.2 G cvGs a')
        (fun e => ∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
          ErrClaim (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
            grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
              grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))) a e) := by
    intro nb hnb
    rw [grpE.j2.arm1]
    rcases c4 : callW p n "block_large_elim_allowed" [pp, nb] s2.mem with _ | ⟨r4, m4⟩
    · rw [liftE_none, grpE.k_block_large_elim_allowed.none]; exact fun _ _ _ => ErrClaim.of_cls0 (by simp)
    rw [liftE_some]
    obtain ⟨al, a4, hr4, hC4, hm4, hd4, p4, -⟩ := blockLargeElimAllowed_simC P.ble n hC2 hA2
      (hbs.1.grow (decBS_mono _) hg12) hsrc2 hsh2 r4 m4 c4
    subst hm4
    have c3' := p4.toCore hC2.check
    rw [hnb] at hr4
    by_cases h0 : r4.headD 0 = 0
    · rw [grpE.k_block_large_elim_allowed.abort1 p n vis pp pO pL tO tL rd mO mL cO cL _ _ r4 _ h0]
      have hal : al = false := by rw [← hd4.1, h0]; rfl
      subst hal
      refine fun _ _ k => ?_
      unfold grcTwinA
      refine ErrClaim.bind_right hrun1 (ErrClaim.bind_right hrun2 ?_)
      simp only [hkb, hl, Bool.false_eq_true, ite_false, ite_true]
      refine ErrClaim.bind_right hr4 ?_
      simp only [Bool.false_eq_true, ite_false]
      exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
    rw [grpE.k_block_large_elim_allowed.arm1 p n vis pp pO pL tO tL rd mO mL cO cL _ _ r4 _ h0]
    have hal : al = true := by rw [← hd4.1]; simpa using h0
    subst hal
    exact fin a4 hC4 (c12.trans c3') (ConRon.Bridge.Inductives.dExt_denoteCV.list c3'.ext _ _ hcvRis) fun k => by
      simp only [grcTwinA, StateT.run_bind, hrun1, except_ok_bind, hrun2, hkb, hl, hr4, Bool.false_eq_true,
        ite_false, ite_true]
  by_cases hn0 : nested = 0
  · rw [grpE.k_class_stream_recs.arm1 p n vis pp nested pO pL tO tL rd mO mL cO cL r2 _ hk0' h7 hn0]
    rcases c3 : callW p n "gen_rec_check_any_no_member" [mO, mL] s2.mem with _ | ⟨r3, m3⟩
    · rw [liftE_none, grpE.k_gen_rec_check_any_no_member.none]; exact fun _ _ _ => ErrClaim.of_cls0 (by simp)
    rw [liftE_some, grpE.k_gen_rec_check_any_no_member.arm1]
    obtain ⟨s3, rfl, -, hm3, hany, -⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
      (genRecCheckAnyNoMember_refines p P.anm n _ mO mL ms hmsD hmsb hS2.iw.iwSize) c3
    rw [hm3]
    exact large _ (by rw [hany, hn0]; rfl)
  · rw [grpE.k_class_stream_recs.arm2 p n vis pp nested pO pL tO tL rd mO mL cO cL r2 _ hk0' h7 hn0]
    exact large nested (by rw [show (nested != 0) = true by simpa using hn0]; rfl)

include hkp henv hV hApd hCrk hIlpf in
/-- **`gen_rec_check` refines `genRecCheck`, both outcomes** under `StageC`: the prep (`grp_ref`),
the pushes, the rules (`classRecsRulesOk_refinesC` on the run, its claim), the pops and the flushes;
the view and index handed back with con-ron's `CheckOK` at the entry environment, the twin's run a
`CoreStep`. -/
theorem gck_ref (P : GrcProg p) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
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
    RefE (VerdictCtxU p) (gckE p (n + 1) m vis pp nested pO pL tO tL rd mO mL cO cL bO bL)
      (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms cvTas block) a
      (fun v x a' => GckPost dn env fe a v.1 m v.2 x a') := by
  have hS := hC.stage
  obtain ⟨hrd3, -, hrcD, hrcb, -⟩ := crWords hrd
  rw [gckE.arm1, genRecCheck_split]
  -- the prep
  rcases n with _ | n
  · rw [grpE.eq_1, gckE.k_gen_rec_check_prep.none]; exact RefE.of_cls0 Err.cls_outOfFuel
  have hR1 := grp_ref hkp henv hV hApd hCrk hIlpf P hclR hfR n hn hC hbs hrb hpar hparb htbl hrd hms hcv hblk hlp
    hP hA hkeep hsh hparP htblP hrdP hmsP hcvTP hblkP hT hMsT hfRc (nested := nested)
  rcases h1 : grpE p (n + 1) m vis pp nested pO pL tO tL rd mO mL cO cL bO bL with e1 | ⟨r1, m1⟩ <;>
    rw [h1] at hR1
  · rw [gckE.k_gen_rec_check_prep.none]; exact fun hG => hR1 hG _
  rw [gckE.k_gen_rec_check_prep.arm1]
  obtain ⟨G, cvGs, a1, hrunP, hR1'⟩ := hR1
  obtain ⟨hC1, hg1, hG1, hns1, -, hcg1, hA1, hP1, c1', gP, cvGsP, hgP, hcvGs, hfrG, henvR⟩ := hR1'
  dsimp only at hC1 hg1 hG1 hcg1 hA1 hP1
  have hS1 := hC1.stage
  have e2 : rdW (m1.arr64 IW) (rd + 2) = rdW (m.arr64 IW) (rd + 2) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  have e3 : rdW (m1.arr64 IW) (rd + 3) = rdW (m.arr64 IW) (rd + 3) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  rw [e2, e3]
  refine RefE.of_run_eq (hrunP (grcTwinR V fe bs rdv)) ?_
  -- the pushes
  rcases c2 : callW p (n + 1) "class_fe_r" [pp, r1.tail.headD 0, r1.tail.tail.headD 0, rdW (m.arr64 IW) (rd + 2),
      rdW (m.arr64 IW) (rd + 3), vis] m1 with _ | ⟨r2, m2⟩
  · rw [liftE_none, gckE.k_class_fe_r.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, gckE.k_class_fe_r.arm1]
  obtain ⟨s2, rfl, -, hS2, hg2, hpv2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
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
  have hvis : fe.visibleBelow = vis.toNat := hS.check.env.vis
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
  unfold grcTwinR
  generalize hfrr : ConRon.Arena.classFeR bs cvGs rdv.recCls fe = FR at hS2 hpv2 hfeR hie2R hpop ⊢
  obtain ⟨feR, prevs⟩ := FR
  simp only at hS2 hpv2 hfeR hie2R hpop
  dsimp only
  rw [hvis]
  refine RefE.bind_right (flushCaches_run a1) ?_
  -- the flush into the rule-less recursors' environment
  refine RefE.onlySim (fun _ => gckE.k_flush_caches.none ..) (fun _ _ h => h) fun r3 m3 c3 => ?_
  rw [gckE.k_flush_caches.arm1]
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
  rw [e2', e3']
  have hcg3 := hcg1.grow hg23
  have hie : ConRon.Bridge.Inductives.IFEnvOKS env (feR.restrictTo vis.toNat)
      ({ a1 with caches := Caches.empty } : AState).store := by
    rw [← hvis]; exact hie2R.toS
  have henvR' := henvR (fun c => c)
  rcases c4 : callE p (n + 1) "class_recs_rules_ok" [vis, r2.headD 0, r1.headD 0, rdW (m.arr64 IW) (rd + 2),
      rdW (m.arr64 IW) (rd + 3), r1.tail.headD 0, r1.tail.tail.headD 0] s3.mem with e4 | ⟨r4, m4⟩
  · rw [gckE.k_class_recs_rules_ok.none]
    exact RefE.bind_left fun hG => CoreSpecE.of_callE (classRecsRulesOk_claim hkp hApd hG.nv hG.core hG.uce
      P.crr (n + 1) (by omega) ⟨s3.mem, Locals.init []⟩
      { a1 with caches := Caches.empty } henvR' vis (r2.headD 0) feR (r1.headD 0) _ _ _ _ G rdv.recCls cvGs hC3
      (hG1.grow (decCG_mono _) hg23) hns1 (hrcD.grow (OMono.decNL _ _) hg13) hrcb hcg3
      (hS3.lt64 hcg3.1) hA3 hgP hcvGs hie) c4
  rw [gckE.k_class_recs_rules_ok.arm1]
  obtain ⟨s4, rfl, -, hok4, ⟨hC4, hg4, hd4⟩, hA4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (classRecsRulesOk_refinesC hkp hApd P.crr (n + 1) (by omega) _ _ henvR' vis (r2.headD 0) feR (r1.headD 0) _ _ _ _ G
      rdv.recCls cvGs hC3 (hG1.grow (decCG_mono _) hg23) hns1 (hrcD.grow (OMono.decNL _ _) hg13) hrcb hcg3
      (hS3.lt64 hcg3.1) hA3 hgP hcvGs hie) (callW_of_callE c4)
  have hP4 := RcMR.ofClosed hclR (hfRc _ (by decide)) (callW_of_callE c4) hP3
  have hrun4 := AM.run_of_ok _ _ hok4
  obtain ⟨c12', -⟩ := ConRon.Bridge.Inductives.classRecsRulesOk_spec feR vis.toNat
    (ConRon.Bridge.CoreSpec.of_core rfl) henvR' G gP rdv.recCls cvGs cvGsP cvGs cvGsP rdv.recCls _ _ _
    hC3.check ⟨hgP, hcvGs, hcvGs, hie⟩ hrun4
  generalize AM.res (ConRon.Arena.classRecsRulesOk V vis.toNat feR G rdv.recCls cvGs cvGs rdv.recCls)
    { a1 with caches := Caches.empty } = out at hrun4 hd4
  generalize AM.st (ConRon.Arena.classRecsRulesOk V vis.toNat feR G rdv.recCls cvGs cvGs rdv.recCls)
    { a1 with caches := Caches.empty } = a4 at hrun4 hC4 c12'
  refine RefE.bind_right hrun4 ?_
  -- the pops
  rcases c5 : callW p (n + 1) "gen_rec_check_pop_all" [r2.headD 0, r2.tail.headD 0, r2.tail.tail.headD 0] s4.mem
    with _ | ⟨r5, m5⟩
  · rw [liftE_none, gckE.k_gen_rec_check_pop_all.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, gckE.k_gen_rec_check_pop_all.arm1]
  obtain ⟨s5, rfl, -, hS5, hg5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (genRecCheckPopAll_refines P.eix P.ers P.ept P.gpa (n + 1) _ a4 dn (r2.headD 0) feR _ _ prevs hC4.stage
      (hpv2.grow (hg3.trans hg4))) c5
  have hP5 := RcMR.ofClosed hclR (hfRc _ (by decide)) c5 hP4
  have hA5 := hkeep _ (by simp [grcKeepCalleesC]) _ _ _ _ _ c5 hA4
  -- the flush back
  refine RefE.onlySim (fun _ => gckE.k_flush_caches_2.none ..) (fun _ _ h => h) fun r6 m6 c6 => ?_
  rw [gckE.k_flush_caches_2.arm1]
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
  refine RefE.ret (y := (prevs.foldr (fun x acc => acc.popTemp x.1 x.2) feR, out))
    (a' := { a4 with caches := Caches.empty }) (by simp only [StateT.run_bind, flushCaches_run]; rfl)
    ⟨hC.of_checkE (by simpa using hS6) hA6 hok13' hext12, hg1.trans (hg23.trans (hg4.trans (hg5.trans hg6))),
    by have := hd4.grow (hg5.trans hg6); simp only [decRRS] at this ⊢; simpa using this, hA6, hP6,
    ⟨hok13, hext12, hpins12⟩⟩

include hkp henv hV hApd hCrk hIlpf in
/-- **`gen_rec_check(vis, p, nested, params.off, params.len, tbl.off, tbl.len, rd, ms.off, ms.len,
cvTas.off, cvTas.len, block.off, block.len)` refines `genRecCheck` under `StageC`**
(`genRecCheck_refines`' statement, `StageR` replaced by `StageC`): besides `genRecCheck_refines`'
hypotheses, the inputs' denotations and scoping as con-ron's `genRecCheck_spec` asks and the index
coherent (`IFEnvCoh`); after it, `StageC` at the returned view and index (con-ron's `CheckOK` at the
entry environment) and the twin's run a `CoreStep`. The program facts: `ValProg p` and `AbsKeep`
of `check_constant_val` (the stream's recursors, `classStreamRecs_refinesC`). Through
`block_large_elim_allowed`'s contract (`IndInstallSpec/PapW`). -/
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
  refine triple_post (RefE.triple (gckE_spec p P (n + 1) s₀ vis pp nested pO pL tO tL rd mO mL cO cL bO bL)
    (gck_ref hkp henv hV hApd hCrk hIlpf P hclR hfR n (by omega) hC hbs hrb hpar hparb htbl hrd hms hcv hblk hlp
      hP hA hkeep hcoh hfe hsh hparP htblP hrdP hmsP hcvTP hblkP hT (fun M hM => (hMs M hM).1) hfRc)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hres, hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.rrs, hR.abs, hR.rc,
    by rw [hst]; exact hR.core⟩

include hkp henv hV hApd hCrk hIlpf in
/-- **`check_block_rec` refines `checkBlockRec`, both outcomes** (`gck_ref`, its result repacked). -/
theorem icr_ref
    (P : GrcProg p) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR)
    (N : Nat) (hN : N ≤ 2 ^ 62 + 1) (m : Mem) (a : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (pp nested pO pL tO tL rd mO mL bO bL cO cL : Word) (bs : BlockShape) (params : List EIdx)
    (tbl : List NestCtorNf) (rdv : ClassRead) (ms : List TargetMajor) (cvTas : List IConstantVal)
    (block : List IConstantInfo) (hC : StageC dn vis fe env m a)
    (hpre : BSOK m pp.toNat bs ∧
        decHL m pO.toNat pL.toNat = some params ∧ pO.toNat + pL.toNat ≤ iwTop m ∧
        PSlR decNCN tbl tO tL m ∧ DecB (fun m => decCR m rd.toNat) m rdv ∧
        PSlR decTM ms mO mL m ∧ PSlR decCVp cvTas cO cL m ∧
        DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block)
    (hrb : RecsB m pp) (hlp : ClassesLp m mO mL) (hP : RcMR m) (hA : AbsOK m)
    (hkeep : ∀ f ∈ grcKeepCalleesC, AbsKeep p f) (hcoh : ConRon.Bridge.IFEnvCoh fe)
    (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env)
    {pP : ConLeche.BlockShape} {paramsP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {rdP : ConLeche.ClassRead} {MsP : List ConLeche.TargetMajor} {cvTasP : List ConLeche.ConstantVal}
    {blockP : List ConLeche.ConstantInfo}
    (hsh : dShape a.store bs = some pP) (hparP : Frontend.denoteEList a.store params = some paramsP)
    (htblP : tbl.mapM (dCtorNf a.store) = some tblP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a.store rdv = some rdP)
    (hmsP : ms.mapM (dMajor a.store) = some MsP)
    (hcvTP : cvTas.mapM (Frontend.denoteCV a.store) = some cvTasP)
    (hblkP : Frontend.denoteCIList a.store block = some blockP)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.ClassMajScoped pP.nP M)
    (hT : ∀ cv ∈ cvTasP, ConLeche.Expr.WScoped 0 cv.type) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR) :
    RefE (VerdictCtxU p) (icrE p N m vis pp nested pO pL tO tL rd mO mL bO bL cO cL)
      (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a
      (fun v x a' => GckPost dn env fe a v.1 m v.2 x a') := by
  obtain ⟨hbs, hpar, hparb, htbl, hrd, hms, hcv, hblk⟩ := hpre
  rcases N with _ | _ | n
  · rw [icrE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  · rw [icrE.arm1, gckE.eq_1, icrE.k_gen_rec_check.none]; exact RefE.of_cls0 Err.cls_outOfFuel
  rw [icrE.arm1]
  exact RefE.tail_eq (k := icrE.k_gen_rec_check p)
    (f := fun v => ([v.1.headD 0, v.1.tail.headD 0, v.1.tail.tail.headD 0], v.2))
    (fun e => icrE.k_gen_rec_check.none p e) (fun v => icrE.k_gen_rec_check.arm1 p v.1 v.2) id rfl
    (fun v x a' h => ⟨h.stage, h.grow, by have := h.rrs; simp only [decRRS] at this ⊢; simpa using this, h.abs,
      h.rc, h.core⟩)
    (gck_ref hkp henv hV hApd hCrk hIlpf P hclR hfR n (by omega) hC hbs hrb hpar hparb htbl hrd hms hcv hblk hlp
      hP hA hkeep hcoh hfe hsh hparP htblP hrdP hmsP hcvTP hblkP hT (fun M hM => (hMs M hM).1) hfRc)

include hkp henv hV hApd hCrk hIlpf in
/-- **`check_block_rec` refines `checkBlockRec` under `StageC`** (`icr_ref`'s ok half;
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
  refine triple_post (RefE.triple (icrE_spec p P hp (n + 1) s₀ vis pp nested pO pL tO tL rd mO mL bO bL cO cL)
    (icr_ref hkp henv hV hApd hCrk hIlpf P hclR hfR (n + 1) (by omega) s₀.mem a₀ dn vis fe pp nested pO pL tO tL
      rd mO mL bO bL cO cL bs params tbl rdv ms cvTas block hC hpre hrb hlp hP hA hkeep hcoh hfe hsh hparP htblP
      hrdP hmsP hcvTP hblkP hMs hT hfRc)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hres, hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.rrs, hR.abs, hR.rc,
    by rw [hst]; exact hR.core⟩

end sims

end L.Ind

end
