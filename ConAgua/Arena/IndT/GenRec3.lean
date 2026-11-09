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
import ConAgua.Arena.IndT.BncAfr
public import ConAgua.Arena.IndPartsSpec.BmoW
import ConAgua.Arena.IndPartsSpec.Bf
import ConAgua.Arena.IndPartsSpec.BlockRecNameSetOk
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.IndPartsSpec.BrsW
import ConAgua.Arena.IndRealAbs
import ConAgua.Arena.IndRealPartsC1
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.RecCheckSpec.EraseFVarTys
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
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
import all ConAgua.Arena.RecGen

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
  have he : x.idx.isEmpty = y.idx.isEmpty := by
    apply Bool.eq_iff_iff.mpr
    simp only [Std.HashMap.isEmpty_iff_forall_not_mem, Std.HashMap.mem_iff_isSome_getElem?, h.2.1]
  simp only [IFEnv.find?, IFEnv.lookup, he, h.2.2.1, h.2.1]

set_option experimental.vcgen true in
/-- **`gen_rec_check`'s unified model**: the prep by its unified model (`grpE`), the pushes, the
flushes and the pops (outside the verdict closure) lifted, the rules through their run (the ok half
reads the call's walk memos). -/
l_model gckE_spec (p : Prog) (P : GrcProgE p)
  fns [P.grc ↦ gckE]
  specs [callW_spec p n "class_fe_r", callW_spec p n "block_shape_names_of", callW_spec p n "flush_caches",
    callW_spec p n "gen_rec_check_pop_all"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **`check_block_rec`'s unified model**: `gen_rec_check` by its unified model. -/
l_model icrE_spec (p : Prog) (P : GrcProgE p) (hf : p.lookup "check_block_rec" = some checkBlockRec)
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

section sims
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : CcvProg p)
  (hApd : ApdF p) (hCrk : CrKeep p) (hCrf : CrfF p) (hIlpf : IlpfF p)

include hkp henv hV hApd hCrk hCrf hIlpf in
/-- **`gen_rec_check_prep` refines the twin's prep (`grcTwinA`, in its continuation form), both
outcomes**: the capacity guards, the pins (`trp_ref`), the stream's recursor types
(`classStreamRecs_refinesC` on the run), the family and elimination guards, then the second and
third parts (`grpB_ref`). -/
theorem grp_ref (P : GrcProgE p) (hF : FtProg p) (hWt : WhnfTopE p) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR) (n : Nat) (hn : n + 1 ≤ 2 ^ 62) {dn : NIdx → Option ConLeche.Name} (hCs : CcvSims p dn)
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp nested pO pL tO tL rd mO mL bO bL : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {block : List IConstantInfo}
    (hC : StageC dn vis fe env m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hpar : decHL m pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop m)
    (htbl : PSlR decNCN tbl tO tL m) (hrd : DecB (fun m => decCR m rd.toNat) m rdv)
    (hms : PSlR decTM ms mO mL m)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block)
    (hP : RcMR m) (hA : AbsOK m) (hkeep : ∀ f ∈ grcKeepCalleesC, AbsKeep p f)
    {pP : ConLeche.BlockShape} {paramsP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {rdP : ConLeche.ClassRead} {MsP : List ConLeche.TargetMajor} {cvTasP : List ConLeche.ConstantVal}
    {blockP : List ConLeche.ConstantInfo}
    (hsh : dShape a.store bs = some pP) (hparP : Frontend.denoteEList a.store params = some paramsP)
    (htblP : tbl.mapM (dCtorNf a.store) = some tblP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a.store rdv = some rdP)
    (hmsP : ms.mapM (dMajor a.store) = some MsP)
    (hcvTP : bs.formers.mapM (Frontend.denoteCV a.store) = some cvTasP)
    (hblkP : Frontend.denoteCIList a.store block = some blockP)
    (hT : ∀ cv ∈ cvTasP, ConLeche.Expr.WScoped 0 cv.type)
    (hMsT : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR) :
    RefC (VerdictCtxU p) (grpE p (n + 1) m vis pp nested pO pL tO tL rd mO mL bO bL)
      (fun v => ∃ G cvGs a', (∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
          (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
            grcTwinB V fe bs tbl rdv ms (fun ms2 ctors ftc elim =>
              grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))).run a = (k G cvGs).run a') ∧
        GrpPost dn vis fe env pP rdv m a v.1 v.2 G cvGs a')
      (fun e => ∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        ErrClaim (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
          grcTwinB V fe bs tbl rdv ms (fun ms2 ctors ftc elim =>
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
  · rw [grpE.abort1 p n m vis pp nested pO pL tO tL rd mO mL bO bL g1]
    exact fun _ _ _ => ErrClaim.of_cls0 rfl
  by_cases g2 : rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (pp + 1) < rdW (m.arr64 IW) (pp + 4)
  · rw [grpE.abort2 p n m vis pp nested pO pL tO tL rd mO mL bO bL g1 g2]
    exact fun _ _ _ => ErrClaim.of_cls0 rfl
  by_cases g3 : rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (rd + 1) < rdW (m.arr64 IW) (pp + 4)
  · rw [grpE.abort3 p n m vis pp nested pO pL tO tL rd mO mL bO bL g1 g2 g3]
    exact fun _ _ _ => ErrClaim.of_cls0 rfl
  rw [grpE.arm1 p n m vis pp nested pO pL tO tL rd mO mL bO bL g1 g2 g3]
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
  have hA1 := hkeep _ (by simp [grcKeepCalleesC]) _ _ _ _ _ (callW_of_callE c1) hA
  have hk1 := callW_keepW (callW_of_callE c1)
  obtain ⟨p1, hF1⟩ := ConRon.Bridge.Inductives.targetRecPins_spec bs pP block blockP a a1 _
    hC.check.state hC.check.pins ⟨hsh, hblkP⟩ hrun1
  have hunR : ∀ rc ∈ pP.recs, ConLeche.reservedRecName rc.cvR.name = false := by
    obtain ⟨F1, hF1'⟩ := id hF1
    rw [ConLeche.targetRecPins_datF] at hF1'
    exact ConLeche.Cached.targetRecPins_unreserved hF1'
  have hC1o : StageC dn vis fe env s1.mem a1 := hC.of_pstep hS1 hA1 p1
  have c1' := p1.toCore hC.check
  -- `block_shape_formers`
  rcases cF : callW p n "block_shape_formers" [pp] s1.mem with _ | ⟨rF, mF⟩
  · rw [liftE_none, grpE.k_block_shape_formers.none]; exact fun _ _ _ => ErrClaim.of_cls0 (by simp)
  rw [liftE_some, grpE.k_block_shape_formers.arm1]
  have hfF : formersW n s1.mem pp = some (rF, mF) := by
    obtain ⟨s', hs, -, hW⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
      (blockShapeFormers_spec p P.nck.alloc P.nck.fieldCopy P.nck.formers n _ pp) cF
    rw [← hs]; exact hW
  have hbs1 := hbs.grow hg1
  obtain ⟨hq', hq9, hptr⟩ := partsShapeFacts hbs1.1 hbs1.2.1
  obtain ⟨hrF, hdF, hgF, hfrF, htF, hroomF⟩ := formersW_dec hfF hS1.iw.iwSize hS1.iw.ctl hq' hq9 hbs1.2.1
    (fun o l j v h1 h2 h3 h4 => by have := hptr o l j v h1 h2 h3 h4; omega)
  have hkbF : bs.k < 2 ^ 64 := by
    obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hq').1
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  have hkTF : (UInt64.ofNat bs.k : Word).toNat = bs.k := UInt64.toNat_ofNat_of_lt' hkbF
  have hcv : PSlR decCVp bs.formers (rdW (s1.mem.arr64 CTL) 200) (UInt64.ofNat bs.k) mF :=
    ⟨by rw [hkTF]; exact decPLcv_decB hdF (by omega), by rw [hkTF]; omega⟩
  subst hrF
  simp only [List.headD_cons, List.tail_cons]
  generalize rdW (s1.mem.arr64 CTL) 200 = cO at hcv
  generalize (UInt64.ofNat bs.k : Word) = cL at hcv
  have hSF : StageR vis fe mF a1 := stage_frame_iw hS1 hfrF hroomF
  have hAF : AbsOK mF := formersW_afr hfF hA1
  have hC1 : StageC dn vis fe env mF a1 := hC1o.of_pstep hSF hAF (PStep.refl hC1o.check.state)
  have hPF : RcMR mF := (RcMR.ofClosed hclR (hfR _ (by decide)) (callW_of_callE c1) hP).fr (MFr.of_iw hfrF)
  have hkF := callW_keepW cF
  have hg1o := hg1
  replace hg1 : IWGrow m mF := hg1o.trans hgF
  -- `class_stream_recs`
  have hrecsP : PSlR decRS bs.recs (rdW (m.arr64 IW) (pp + 2)) (rdW (m.arr64 IW) (pp + 3)) m :=
    bpPSl decRS_mono hrecs hrb (by rw [UInt64.toNat_add]; simp; omega) (by rw [UInt64.toNat_add]; simp; omega)
  have hw2 : rdW (mF.arr64 IW) (pp + 2) = rdW (m.arr64 IW) (pp + 2) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  have hw3 : rdW (mF.arr64 IW) (pp + 3) = rdW (m.arr64 IW) (pp + 3) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  rw [hw2, hw3]
  have hrecs1 := hrecsP.grow (fun q => decRS_mono q) hg1
  have hrecs1P := ConRon.Bridge.Inductives.dRec_ext.list c1'.ext _ _ hrecsP0
  rcases c2 : callE p n "class_stream_recs" [vis, rdW (m.arr64 IW) (pp + 2), rdW (m.arr64 IW) (pp + 3)] mF with
    e2 | ⟨r2, m2⟩
  · rw [grpE.k_class_stream_recs.none]
    refine fun hG _ k => ?_
    unfold grcTwinA
    refine ErrClaim.bind_right hrun1 (ErrClaim.bind_left ?_)
    exact CoreSpecE.of_callE (classStreamRecs_claim hkp henv hV hCrf hCs hApd hCrk hG P.ia P.cpy P.slc P.csr n (by omega)
      ⟨mF, Locals.init []⟩ a1 fe vis _ _ bs.recs pP.recs hC1 hAF (rec3RecsOK_of_decB hrecs1.1 hrecs1.2)
      hrecs1P) c2
  obtain ⟨s2, hs2, -, hok2, hC2, hg2, hcs2, hA2⟩ := triple_of_callW (s₀ := ⟨mF, Locals.init []⟩)
    (classStreamRecs_refinesC hkp henv hV hCrf hCs hApd hCrk P.cpy P.ia P.slc P.csr n (by omega) _ a1 fe vis _ _ bs.recs
      pP.recs hC1 hAF (rec3RecsOK_of_decB hrecs1.1 hrecs1.2) hrecs1P) (callW_of_callE c2)
  simp only at hs2 hC2 hg2 hcs2 hA2; subst hs2
  have hrun2 := AM.run_of_ok _ a1 hok2
  obtain ⟨c2', cvRisP, ⟨hcvRis, hwRis⟩, -⟩ := ConRon.Bridge.Inductives.classStreamRecs_spec fe
    (ConRon.Bridge.CoreSpec.of_core) henv bs.recs pP.recs a1 _ _ hC1.check hrecs1P hrun2
  generalize AM.res (ConRon.Arena.classStreamRecs V fe bs.recs) a1 = cvRis at hrun2 hcs2 hcvRis
  generalize AM.st (ConRon.Arena.classStreamRecs V fe bs.recs) a1 = a2 at hrun2 hC2 hcvRis c2'
  have hS2 := hC2.stage
  have c12 := c1'.trans c2'
  have hP2 := RcMR.ofClosed hclR (hfR _ (by decide)) (callW_of_callE c2) hPF
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
  have fin : ∀ (a4 : AState), StageC dn vis fe env s2.mem a4 → ConRon.Bridge.CoreStep env fe a a4 →
      cvRis.mapM (Frontend.denoteCV a4.store) = some cvRisP →
      (∀ {β : Type} (k : List IConstantVal → AM β),
        (grcTwinA V fe bs (nested != 0) ms block k).run a = (k cvRis).run a4) →
      RefC (VerdictCtxU p)
        (grpE.j1 p n vis pp pO pL tO tL rd mO mL cO cL (r2.headD 0) (r2.tail.headD 0) s2.mem)
        (fun v => ∃ G cvGs a', (∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
            (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
              grcTwinB V fe bs tbl rdv ms (fun ms2 ctors ftc elim =>
                grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))).run a = (k G cvGs).run a') ∧
          GrpPost dn vis fe env pP rdv m a v.1 v.2 G cvGs a')
        (fun e => ∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
          ErrClaim (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
            grcTwinB V fe bs tbl rdv ms (fun ms2 ctors ftc elim =>
              grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))) a e) := by
    intro a4 hC4 c4 hcvRis4 hrunA
    have hk4 := (hk1.trans hkF).trans hk2
    refine RefC.mono (grpB_ref hkp henv hApd hCrf hIlpf P hF hWt n (by omega) hCs hC4 (hbs.grow hg12)
      (hrb.grow hg12 (by have := hbs.ptop; omega)) (decHL_grow' hg12 hparb hpar) (Nat.le_trans hparb hg12.iw)
      (htbl.grow (fun q => decNCN_mono q) hg12) (hrd.grow (decCR_mono _) hg12) (hms.grow (fun q => decTM_mono q) hg12)
      (hcv.grow (fun q => OMono.decCVp q) hg2) (csRes_decB hcs2) hns hnpk
      (by rw [hk4 IW]; exact hsz5) hP2 hA2 hkeep
      (ConRon.Bridge.Inductives.dShape_ext c4.ext _ _ hsh) (ConRon.Bridge.denoteEList_ext c4.ext _ _ hparP)
      (ConRon.Bridge.Inductives.dCtorNf_ext.list c4.ext _ _ htblP)
      (ConRon.Bridge.Inductives.dClassRead_ext c4.ext _ _ hrdP)
      (ConRon.Bridge.Inductives.dMajor_ext.list c4.ext _ _ hmsP)
      (ConRon.Bridge.Inductives.dExt_denoteCV.list c4.ext _ _ hcvTP) hT hMsT hcvRis4 hwRis hunR hclR hfRc) ?_ ?_
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
              grcTwinB V fe bs tbl rdv ms (fun ms2 ctors ftc elim =>
                grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))).run a = (k G cvGs).run a') ∧
          GrpPost dn vis fe env pP rdv m a v.1 v.2 G cvGs a')
        (fun e => ∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
          ErrClaim (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
            grcTwinB V fe bs tbl rdv ms (fun ms2 ctors ftc elim =>
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

/-- `block_shape_names_of`'s model is an `IW` slice write (`sl_cons`). -/
theorem bsnW_iwFrame : ∀ (n : Nat) (m m' : Mem) (cto ctl : Word) (r : List Word),
    bsnW n m cto ctl = some (r, m') → MemFrame [IW] [200] m m'
  | 0, _, _, _, _, _, h => by simp [bsnW] at h
  | n + 1, m, m', cto, ctl, r, h => by
    by_cases hl : ctl = 0
    · rw [bsnW_nil n m cto ctl hl] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact MemFrame.refl _ _ _
    rw [bsnW_cons n m cto ctl hl] at h
    obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (by simp [bsnW.bsnK])
    rw [bsnK_some] at h
    rcases h2 : consW n m1 (erRd m1 (rdW (m1.arr64 IW) cto)) (r1.headD 0) (r1.tail.headD 0) with _ | ⟨r2, m2⟩ <;>
      rw [h2] at h
    · cases h
    rw [bgoK3_some] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact (bsnW_iwFrame n m m1 _ _ _ h1).trans (consW_iwFrame h2)

/-- A callee keeps the own rows' counters (`ownC`, what `gen_rec_check_pop_all`'s `PopOK` reads). -/
def OwnKeepF (p : Prog) (f : FnName) : Prop :=
  ∀ (n : Nat) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem), callW p n f vs m = some (r, m') →
    ownC m' = ownC m

/-- A callee keeps a well-formed `MAM` memo (`maMR`). -/
def MaKeepF (p : Prog) (f : FnName) : Prop :=
  ∀ (n : Nat) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem), callW p n f vs m = some (r, m') →
    (∃ mp, maMR m mp) → ∃ mp, maMR m' mp

theorem decPL_cvx {m : Mem} {o l : Nat} {xs : List IConstantVal} (h : decPL m (decCVX m) o l = some xs) :
    decPL m (decCVp m) o l = some xs := by
  rw [decPL_eq_bind] at h ⊢
  cases hn : decNL m o l with
  | none => rw [hn] at h; cases h
  | some ps =>
    rw [hn] at h
    simp only [Option.bind_some] at h ⊢
    clear hn
    revert xs
    induction ps with
    | nil => intro xs h; exact h
    | cons q ps ih =>
      intro xs h
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h ⊢
      obtain ⟨x, hx, ys, hys, rfl⟩ := h
      refine ⟨x, ?_, ys, ih hys, rfl⟩
      unfold decCVX at hx; split at hx
      · exact hx
      · cases hx

include hkp henv hV hApd hCrk hCrf hIlpf in
/-- **`gen_rec_check` refines `genRecCheck`, both outcomes** under `StageC` (twin side con-ron's
`genRecCheck_spec`'s proof): the prep through its call (`grp_ref`), the pushes (`class_fe_r`), the
pushed names (`block_shape_names_of`), the flush into the rule-less recursors' environment, the
rules (`classRecsRulesOk_refinesC` on the run, its claim), the pops and the flush back; the view
and index handed back with con-ron's `CheckOK` at the entry environment. -/
theorem gck_ref (P : GrcProgE p) (hF : FtProg p) (hWt : WhnfTopE p) {fsR : List FnName}
    (hclR : closedA p rcFreeA rcFreeC fsR = true) (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR) (n : Nat)
    (hn : n ≤ 2 ^ 62) {dn : NIdx → Option ConLeche.Name} (hCs : CcvSims p dn)
    (hMa : ∀ f ∈ ["gen_rec_check_prep", "class_fe_r", "block_shape_names_of", "flush_caches"], MaKeepF p f)
    (hOwn : OwnKeepF p "class_recs_rules_ok")
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp nested pO pL tO tL rd mO mL bO bL : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {block : List IConstantInfo}
    (hC : StageC dn vis fe env m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hpar : decHL m pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop m)
    (htbl : PSlR decNCN tbl tO tL m) (hrd : DecB (fun m => decCR m rd.toNat) m rdv)
    (hms : PSlR decTM ms mO mL m)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block)
    (hP : RcMR m) (hA : AbsOK m) (hma : ∃ mp, maMR m mp) (hkeep : ∀ f ∈ grcKeepCalleesC, AbsKeep p f)
    (hgate : ConRon.Bridge.TblGate fe)
    {pP : ConLeche.BlockShape} {paramsP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {rdP : ConLeche.ClassRead} {MsP : List ConLeche.TargetMajor}
    {blockP : List ConLeche.ConstantInfo}
    (hsh : dShape a.store bs = some pP) (hparP : Frontend.denoteEList a.store params = some paramsP)
    (htblP : tbl.mapM (dCtorNf a.store) = some tblP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a.store rdv = some rdP)
    (hmsP : ms.mapM (dMajor a.store) = some MsP)
    (hblkP : Frontend.denoteCIList a.store block = some blockP)
    (hT : ∀ cv ∈ pP.formers, ConLeche.Expr.WScoped 0 cv.type)
    (hMsT : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR) :
    RefE (VerdictCtxU p) (gckE p (n + 1) m vis pp nested pO pL tO tL rd mO mL bO bL)
      (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms block) a
      (fun v x a' => GckPost dn env fe a v.1 m v.2 x a') := by
  have hS := hC.stage
  obtain ⟨hrd3, -, hrcD, hrcb, -⟩ := crWords hrd
  rw [gckE.arm1, genRecCheck_split]
  -- the prep
  rcases n with _ | n
  · exact RefE.callE_zero (fun _ => gckE.k_gen_rec_check_prep.none ..)
  have hR1 := grp_ref hkp henv hV hApd hCrk hCrf hIlpf P hF hWt hclR hfR n (by omega) hCs hC hbs hrb hpar hparb
    htbl hrd hms hblk hP hA hkeep hsh hparP htblP hrdP hmsP (ConRon.Bridge.Inductives.dShape_formers hsh)
    hblkP hT hMsT hfRc (nested := nested)
  have hs1 := grpE_spec p P.prep (n + 1) ⟨m, Locals.init []⟩ vis pp nested pO pL tO tL rd mO mL bO bL
  rcases c1 : callE p (n + 1) "gen_rec_check_prep" [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, bO, bL] m
    with e1 | ⟨r1, m1⟩
  · rw [gckE.k_gen_rec_check_prep.none]
    intro hG
    by_cases h0 : e1.cls = 0
    · exact ErrClaim.of_cls0 h0
    have he := triple_of_callE_err hs1 c1 hG.nv h0
    simp only at he
    rw [he] at hR1
    exact hR1 hG _
  rw [gckE.k_gen_rec_check_prep.arm1]
  obtain ⟨s1', hs1m, -, hx1⟩ := triple_of_callE hs1 c1
  simp only at hx1
  rw [hx1, hs1m] at hR1
  have hma1 := hMa _ (by simp) _ _ _ _ _ (callW_of_callE c1) hma
  obtain ⟨G, cvGs, a1, hrunP, hR1'⟩ := hR1
  obtain ⟨hC1, hg1, hG1, hns1, -, hcg1, hA1, hP1, c1', gP, cvGsP, hgP, hcvGs, hfrG, hunG, henvR⟩ := hR1'
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
  obtain ⟨s2, rfl, -, hS2, hg2, hpv2, cs2, hcs2, hpop2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (classFeR_refines p P.cfr (n + 1) _ a1 vis fe pp _ _ _ _ bs cvGs rdv.recCls hS1 (hbs.1.grow (decBS_mono _) hg1)
      hcg1 (hrcD.grow (OMono.decNL _ _) hg1)) c2
  have hP2 := RcMR.ofClosed hclR (hfRc _ (by decide)) c2 hP1
  have hA2 := hkeep _ (by simp [grcKeepCalleesC]) _ _ _ _ _ c2 hA1
  have hma2 := hMa _ (by simp) _ _ _ _ _ c2 hma1
  -- the twin's pushed index
  have hsh1 := ConRon.Bridge.Inductives.dShape_ext c1'.ext _ _ hsh
  have hfeR := ConRon.Bridge.Inductives.GR.classFeR_go_ok hC1.check.state bs pP hsh1 (fun c => c) cvGs cvGsP
    rdv.recCls 0 fe env [] hC1.check.ienv hgate (ConRon.Bridge.TablesStored.of_envWF henv) hcvGs
  have hpop := ConRon.Bridge.Inductives.GR.classFeR_pop bs cvGs rdv.recCls fe
  unfold grcTwinR
  have hfeR' : ConRon.Bridge.IFEnvOK (ConLeche.consBlockRecsBare pP 0
      ((cvGsP.zip rdv.recCls).map fun x => (x.1, x.2)) env) (ConRon.Arena.classFeR bs cvGs rdv.recCls fe).1 a1 :=
    hfeR.1
  generalize hfrr : ConRon.Arena.classFeR bs cvGs rdv.recCls fe = FR at hS2 hpv2 hfeR' hpop ⊢
  obtain ⟨feR, prevs⟩ := FR
  simp only at hS2 hpv2 hfeR' hpop
  dsimp only
  -- the pushed names
  have hcgD := hcg1.grow hg2
  have hcvp : PSlR decCVp cvGs (r1.tail.headD 0) (r1.tail.tail.headD 0) s2.mem :=
    ⟨decPL_cvx (spl_decB hcgD), hcgD.1⟩
  -- the pushed names
  rcases c3 : callW p (n + 1) "block_shape_names_of" [r1.tail.headD 0, r1.tail.tail.headD 0] s2.mem with
    _ | ⟨r3, m3⟩
  · rw [liftE_none, gckE.k_block_shape_names_of.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, gckE.k_block_shape_names_of.arm1]
  have hb3 : bsnW (n + 1) s2.mem (r1.tail.headD 0) (r1.tail.tail.headD 0) = some (r3, m3) := by
    obtain ⟨s', hs, -, hW⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
      (bsn_spec p P.parts4 P.namesOf (n + 1) _ _ _) c3
    rw [← hs]; exact hW
  obtain ⟨hS3, hg3, hpu3, hpb3⟩ := bsnW_ok (n + 1) s2.mem m3 a1 _ _ cvGs r3 hb3 hS2 hcvp
  have hfr3 := bsnW_iwFrame _ _ _ _ _ _ hb3
  have hA3 : AbsOK m3 := bsnW_afr _ _ _ _ _ _ hb3 hA2
  have hP3 := hP2.fr (MFr.of_iw hfr3)
  have hma3 := hMa _ (by simp) _ _ _ _ _ c3 hma2
  have hown3 : ownC m3 = ownC s2.mem := ownC_iw hfr3
  -- the flush into the rule-less recursors' environment
  refine RefE.bind_right (flushCaches_run a1) ?_
  refine RefE.onlySim (fun _ => gckE.k_flush_caches.none ..) (fun _ _ h => h) fun r4 m4 c4 => ?_
  rw [gckE.k_flush_caches.arm1]
  obtain ⟨s4, rfl, -, hfok, hfm⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (flushCaches_spec p P.flush (n + 1) _) c4
  have hP4 := RcMR.ofClosed hclR (hfRc _ (by decide)) c4 hP3
  have hma4 := hMa _ (by simp) _ _ _ _ _ c4 hma3
  obtain ⟨hS4, hg4⟩ := flush_stage hS3 hfok
  rw [← hfm] at hS4 hg4
  have hA4 : AbsOK s4.mem := by rw [hfm]; exact AFr.of_frame (flushMem_frame _) (by decide) (by decide) hA3
  have hown4 : ownC s4.mem = ownC m3 := by
    rw [hfm]; exact ownC_frame (flushMem_frame _) (by simp) (by decide)
  have hg24 := hg3.trans hg4
  have hg14 := hg1.trans (hg2.trans hg24)
  obtain ⟨hok11, -, -⟩ := (⟨hC1.check.state, hC1.check.pins, hfeR'⟩ :
    ConRon.Bridge.Inductives.ReadOK _ feR a1).flush (flushCaches_run a1)
  have hC4 : StageC dn (r2.headD 0) feR (ConLeche.consBlockRecsBare pP 0
      ((cvGsP.zip rdv.recCls).map fun x => (x.1, x.2)) env) s4.mem { a1 with caches := Caches.empty } :=
    hC1.of_checkE hS4 hA4 hok11 (ConRon.Arena.Ext.refl _)
  -- the rules
  have e2' : rdW (s4.mem.arr64 IW) (rd + 2) = rdW (m.arr64 IW) (rd + 2) :=
    partsRdIW_grow hg14 (by rw [UInt64.toNat_add]; simp; omega)
  have e3' : rdW (s4.mem.arr64 IW) (rd + 3) = rdW (m.arr64 IW) (rd + 3) :=
    partsRdIW_grow hg14 (by rw [UInt64.toNat_add]; simp; omega)
  rw [e2', e3']
  have hcg4 := hcg1.grow (hg2.trans hg24)
  have henvR' := henvR (fun c => c)
  have hdp := ConRon.Bridge.Inductives.GR.domPass_consBlockRecsBare pP env cvGsP rdv.recCls (fun c => c) hunG
  have hpu4 : decHL s4.mem (r3.headD 0).toNat (r3.tail.headD 0).toNat = some (cvGs.map (·.name)) := by
    rw [decHL_grow hg4 hpb3]; exact hpu3
  have hpb4 : (r3.headD 0).toNat + (r3.tail.headD 0).toNat ≤ iwTop s4.mem := Nat.le_trans hpb3 hg4.iw
  have hG4 := hG1.grow (decCG_mono _) (hg2.trans hg24)
  have hrc4 := hrcD.grow (OMono.decNL _ _) hg14
  rcases c5 : callE p (n + 1) "class_recs_rules_ok" [r2.headD 0, r3.headD 0, r3.tail.headD 0, r1.headD 0,
      rdW (m.arr64 IW) (rd + 2), rdW (m.arr64 IW) (rd + 3), r1.tail.headD 0, r1.tail.tail.headD 0] s4.mem
    with e5 | ⟨r5, m5⟩
  · rw [gckE.k_class_recs_rules_ok.none]
    exact RefE.bind_left fun hG => CoreSpecE.of_callE (classRecsRulesOk_claim hkp hApd hG.nv hG.core hG.uce
      P.crrE (n + 1) (by omega) ⟨s4.mem, Locals.init []⟩ { a1 with caches := Caches.empty } henvR'
      (r2.headD 0) _ _ feR (cvGs.map (·.name)) (r1.headD 0) _ _ _ _ G rdv.recCls cvGs hC4 hG4 hns1 hrc4 hrcb
      hcg4 (hS4.lt64 hcg4.1) hA4 hgP hcvGs hpu4 hpb4 hma4) c5
  rw [gckE.k_class_recs_rules_ok.arm1]
  obtain ⟨s5, rfl, -, hok5, ⟨hC5, hg5, hd5⟩, hA5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (classRecsRulesOk_refinesC hkp hApd P.crrE (n + 1) (by omega) _ _ henvR' (r2.headD 0) _ _ feR
      (cvGs.map (·.name)) (r1.headD 0) _ _ _ _ G rdv.recCls cvGs hC4 hG4 hns1 hrc4 hrcb hcg4
      (hS4.lt64 hcg4.1) hA4 hgP hcvGs hpu4 hpb4 hma4) (callW_of_callE c5)
  have hP5 := RcMR.ofClosed hclR (hfRc _ (by decide)) (callW_of_callE c5) hP4
  have hown5 : ownC s5.mem = ownC s4.mem := hOwn _ _ _ _ _ (callW_of_callE c5)
  have hrun5 := AM.run_of_ok _ _ hok5
  obtain ⟨c12', -⟩ := ConRon.Bridge.Inductives.classRecsRulesOk_spec feR _ _ hdp ConRon.Bridge.CoreSpec.of_core henvR' G gP rdv.recCls cvGs cvGsP cvGs cvGsP
    rdv.recCls _ _ _ hC4.check ⟨hgP, hcvGs, hcvGs, ConRon.Bridge.Inductives.GR.names_denote hcvGs⟩ hrun5
  generalize AM.res (ConRon.Arena.classRecsRulesOk V feR (cvGs.map (·.name)) G rdv.recCls cvGs cvGs rdv.recCls)
    { a1 with caches := Caches.empty } = out at hrun5 hd5
  generalize AM.st (ConRon.Arena.classRecsRulesOk V feR (cvGs.map (·.name)) G rdv.recCls cvGs cvGs rdv.recCls)
    { a1 with caches := Caches.empty } = a5 at hrun5 hC5 c12'
  refine RefE.bind_right hrun5 ?_
  -- the pops
  rcases c6 : callW p (n + 1) "gen_rec_check_pop_all" [r2.headD 0, r2.tail.headD 0, r2.tail.tail.headD 0] s5.mem
    with _ | ⟨r6, m6⟩
  · rw [liftE_none, gckE.k_gen_rec_check_pop_all.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, gckE.k_gen_rec_check_pop_all.arm1]
  have hg25 := hg24.trans hg5
  obtain ⟨s6, rfl, -, hS6, hg6⟩ := triple_of_callW (s₀ := ⟨s5.mem, Locals.init []⟩)
    (genRecCheckPopAll_refines P.ers P.ept P.gpa (n + 1) _ a5 (r2.headD 0) feR _ _ prevs cs2 hC5.stage
      (hpv2.grow hg25) (hcs2.grow hg25) (by rw [hown5, hown4, hown3]; exact hpop2)) c6
  have hP6 := RcMR.ofClosed hclR (hfRc _ (by decide)) c6 hP5
  have hA6 := hkeep _ (by simp [grcKeepCalleesC]) _ _ _ _ _ c6 hA5
  -- the flush back
  refine RefE.onlySim (fun _ => gckE.k_flush_caches_2.none ..) (fun _ _ h => h) fun r7 m7 c7 => ?_
  rw [gckE.k_flush_caches_2.arm1]
  obtain ⟨s7, rfl, -, hfok7, hfm7⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (flushCaches_spec p P.flush (n + 1) _) c7
  have hP7 := RcMR.ofClosed hclR (hfRc _ (by decide)) c7 hP6
  obtain ⟨hS7, hg7⟩ := flush_stage hS6 hfok7
  have hA7 : AbsOK s7.mem := by rw [hfm7]; exact AFr.of_frame (flushMem_frame _) (by decide) (by decide) hA6
  rw [← hfm7] at hS7 hg7
  have hext12 : ConRon.Arena.Ext a.store a5.store := c1'.ext.trans c12'.ext
  have hpins12 : a5.pins = a.pins := c12'.pins.trans c1'.pins
  obtain ⟨hok13, -, -⟩ := (⟨c12'.ok.state, hC.check.pins.mono hext12 hpins12, hC.check.ienv.mono hext12⟩ :
    ConRon.Bridge.Inductives.ReadOK env fe a5).flush (flushCaches_run a5)
  have hok13' : ConRon.Bridge.CheckOK false env (prevs.foldr (fun x acc => acc.popTemp x.1 x.2) feR)
      { a5 with caches := Caches.empty } :=
    ⟨hok13.state, hok13.caches, hok13.pins, ConRon.Bridge.Inductives.GR.FEq.ifenv hpop hok13.ienv⟩
  refine RefE.ret (y := (prevs.foldr (fun x acc => acc.popTemp x.1 x.2) feR, out))
    (a' := { a5 with caches := Caches.empty }) (by simp only [StateT.run_bind, flushCaches_run]; rfl)
    ⟨hC.of_checkE (by simpa using hS7) hA7 hok13' hext12, hg14.trans (hg5.trans (hg6.trans hg7)),
    by have := hd5.grow (hg6.trans hg7); simp only [decRRS] at this ⊢; simpa using this, hA7, hP7⟩

include hkp henv hV hApd hCrk hCrf hIlpf in
/-- **`gen_rec_check(vis, p, nested, params.off, params.len, tbl.off, tbl.len, rd, ms.off, ms.len,
block.off, block.len)` refines `genRecCheck` under `StageC`** (`gck_ref`'s ok half): after it,
`StageC` at the returned view and index (con-ron's `CheckOK` at the entry environment). -/
@[refines ConRon.Arena.genRecCheck]
theorem genRecCheck_refinesC (P : GrcProgE p) (hF : FtProg p) (hWt : WhnfTopE p) {fsR : List FnName}
    (hclR : closedA p rcFreeA rcFreeC fsR = true) (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR)
    {dn : NIdx → Option ConLeche.Name} (hCs : CcvSims p dn)
    (hMa : ∀ f ∈ ["gen_rec_check_prep", "class_fe_r", "block_shape_names_of", "flush_caches"], MaKeepF p f)
    (hOwn : OwnKeepF p "class_recs_rules_ok") (hkeep : ∀ f ∈ grcKeepCalleesC, AbsKeep p f)
    (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR) (n : Nat) (hn : n ≤ 2 ^ 62)
    {vis : Word} {fe : IFEnv} {pp nested pO pL tO tL rd mO mL bO bL : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {block : List IConstantInfo} (s₀ : St) (a₀ : AState)
    (hC : StageC dn vis fe env s₀.mem a₀) (hbs : BSOK s₀.mem pp.toNat bs) (hrb : RecsB s₀.mem pp)
    (hpar : decHL s₀.mem pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop s₀.mem)
    (htbl : PSlR decNCN tbl tO tL s₀.mem) (hrd : DecB (fun m => decCR m rd.toNat) s₀.mem rdv)
    (hms : PSlR decTM ms mO mL s₀.mem) (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) s₀.mem block)
    (hP : RcMR s₀.mem) (hA : AbsOK s₀.mem) (hma : ∃ mp, maMR s₀.mem mp) (hgate : ConRon.Bridge.TblGate fe)
    {pP : ConLeche.BlockShape} {paramsP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {rdP : ConLeche.ClassRead} {MsP : List ConLeche.TargetMajor} {blockP : List ConLeche.ConstantInfo}
    (hsh : dShape a₀.store bs = some pP) (hparP : Frontend.denoteEList a₀.store params = some paramsP)
    (htblP : tbl.mapM (dCtorNf a₀.store) = some tblP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a₀.store rdv = some rdP)
    (hmsP : ms.mapM (dMajor a₀.store) = some MsP)
    (hblkP : Frontend.denoteCIList a₀.store block = some blockP)
    (hT : ∀ cv ∈ pP.formers, ConLeche.Expr.WScoped 0 cv.type)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.ClassMajScoped pP.nP M) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "gen_rec_check" [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, bO, bL]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms block) a₀ ∧
      StageC dn (r.headD 0) (AM.res (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms block) a₀).1 env s'.mem (AM.st (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms block) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ decRRS s'.mem r.tail (AM.res (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms block) a₀).2 ∧ AbsOK s'.mem ∧ RcMR s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (gckE_spec p P (n + 1) s₀ vis pp nested pO pL tO tL rd mO mL bO bL)
    (gck_ref hkp henv hV hApd hCrk hCrf hIlpf P hF hWt hclR hfR n hn hCs hMa hOwn hC hbs hrb hpar hparb htbl hrd hms hblk hP hA hma hkeep hgate hsh hparP htblP hrdP hmsP hblkP hT (fun M hM => (hMs M hM).1) hfRc)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hres, hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.rrs, hR.abs, hR.rc⟩

include hkp henv hV hApd hCrk hCrf hIlpf in
/-- **`check_block_rec` refines `checkBlockRec`, both outcomes** (`gck_ref`, its result repacked). -/
theorem icr_ref (P : GrcProgE p) (hF : FtProg p) (hWt : WhnfTopE p) {fsR : List FnName}
    (hclR : closedA p rcFreeA rcFreeC fsR = true) (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR)
    {dn : NIdx → Option ConLeche.Name} (hCs : CcvSims p dn)
    (hMa : ∀ f ∈ ["gen_rec_check_prep", "class_fe_r", "block_shape_names_of", "flush_caches"], MaKeepF p f)
    (hOwn : OwnKeepF p "class_recs_rules_ok") (hkeep : ∀ f ∈ grcKeepCalleesC, AbsKeep p f)
    (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR) (n : Nat) (hn : n ≤ 2 ^ 62)
    {vis : Word} {fe : IFEnv} {pp nested pO pL tO tL rd mO mL bO bL : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {block : List IConstantInfo} {m : Mem} {a : AState}
    (hC : StageC dn vis fe env m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hpar : decHL m pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop m)
    (htbl : PSlR decNCN tbl tO tL m) (hrd : DecB (fun m => decCR m rd.toNat) m rdv)
    (hms : PSlR decTM ms mO mL m) (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block)
    (hP : RcMR m) (hA : AbsOK m) (hma : ∃ mp, maMR m mp) (hgate : ConRon.Bridge.TblGate fe)
    {pP : ConLeche.BlockShape} {paramsP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {rdP : ConLeche.ClassRead} {MsP : List ConLeche.TargetMajor} {blockP : List ConLeche.ConstantInfo}
    (hsh : dShape a.store bs = some pP) (hparP : Frontend.denoteEList a.store params = some paramsP)
    (htblP : tbl.mapM (dCtorNf a.store) = some tblP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a.store rdv = some rdP)
    (hmsP : ms.mapM (dMajor a.store) = some MsP)
    (hblkP : Frontend.denoteCIList a.store block = some blockP)
    (hT : ∀ cv ∈ pP.formers, ConLeche.Expr.WScoped 0 cv.type)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.ClassMajScoped pP.nP M) :
    RefE (VerdictCtxU p) (icrE p (n + 2) m vis pp nested pO pL tO tL rd mO mL bO bL) (ConRon.Arena.checkBlockRec V fe bs (nested != 0) params tbl rdv ms block) a
      (fun v x a' => GckPost dn env fe a v.1 m v.2 x a') := by
  rw [icrE.arm1]
  exact RefE.tail_eq (k := icrE.k_gen_rec_check p)
    (f := fun v => ([v.1.headD 0, v.1.tail.headD 0, v.1.tail.tail.headD 0], v.2))
    (fun e => icrE.k_gen_rec_check.none p e) (fun v => icrE.k_gen_rec_check.arm1 p v.1 v.2) id rfl
    (fun v x a' h => ⟨h.stage, h.grow, by have := h.rrs; simp only [decRRS] at this ⊢; simpa using this, h.abs,
      h.rc⟩)
    (gck_ref hkp henv hV hApd hCrk hCrf hIlpf P hF hWt hclR hfR n hn hCs hMa hOwn hC hbs hrb hpar hparb htbl hrd hms hblk hP hA hma hkeep hgate hsh hparP htblP hrdP hmsP hblkP hT (fun M hM => (hMs M hM).1) hfRc)

include hkp henv hV hApd hCrk hCrf hIlpf in
/-- **`check_block_rec` refines `checkBlockRec` under `StageC`** (`icr_ref`'s ok half). -/
@[refines ConRon.Arena.checkBlockRec]
theorem checkBlockRec_refinesC (hp : p.lookup "check_block_rec" = some checkBlockRec) (P : GrcProgE p) (hF : FtProg p) (hWt : WhnfTopE p) {fsR : List FnName}
    (hclR : closedA p rcFreeA rcFreeC fsR = true) (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR)
    {dn : NIdx → Option ConLeche.Name} (hCs : CcvSims p dn)
    (hMa : ∀ f ∈ ["gen_rec_check_prep", "class_fe_r", "block_shape_names_of", "flush_caches"], MaKeepF p f)
    (hOwn : OwnKeepF p "class_recs_rules_ok") (hkeep : ∀ f ∈ grcKeepCalleesC, AbsKeep p f)
    (hfRc : ∀ f ∈ grcRcCallees, f ∈ fsR) (n : Nat) (hn : n ≤ 2 ^ 62)
    {vis : Word} {fe : IFEnv} {pp nested pO pL tO tL rd mO mL bO bL : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {block : List IConstantInfo}
    (s₀ : St) (a₀ : AState)
    (hC : StageC dn vis fe env s₀.mem a₀) (hbs : BSOK s₀.mem pp.toNat bs) (hrb : RecsB s₀.mem pp)
    (hpar : decHL s₀.mem pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop s₀.mem)
    (htbl : PSlR decNCN tbl tO tL s₀.mem) (hrd : DecB (fun m => decCR m rd.toNat) s₀.mem rdv)
    (hms : PSlR decTM ms mO mL s₀.mem) (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) s₀.mem block)
    (hP : RcMR s₀.mem) (hA : AbsOK s₀.mem) (hma : ∃ mp, maMR s₀.mem mp) (hgate : ConRon.Bridge.TblGate fe)
    {pP : ConLeche.BlockShape} {paramsP : List ConLeche.Expr} {tblP : List ConLeche.NestCtorNf}
    {rdP : ConLeche.ClassRead} {MsP : List ConLeche.TargetMajor} {blockP : List ConLeche.ConstantInfo}
    (hsh : dShape a₀.store bs = some pP) (hparP : Frontend.denoteEList a₀.store params = some paramsP)
    (htblP : tbl.mapM (dCtorNf a₀.store) = some tblP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a₀.store rdv = some rdP)
    (hmsP : ms.mapM (dMajor a₀.store) = some MsP)
    (hblkP : Frontend.denoteCIList a₀.store block = some blockP)
    (hT : ∀ cv ∈ pP.formers, ConLeche.Expr.WScoped 0 cv.type)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.ClassMajScoped pP.nP M) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "check_block_rec" [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, bO, bL]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockRec V fe bs (nested != 0) params tbl rdv ms block) a₀ ∧
      StageC dn (r.headD 0) (AM.res (ConRon.Arena.checkBlockRec V fe bs (nested != 0) params tbl rdv ms block) a₀).1 env s'.mem (AM.st (ConRon.Arena.checkBlockRec V fe bs (nested != 0) params tbl rdv ms block) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ decRRS s'.mem r.tail (AM.res (ConRon.Arena.checkBlockRec V fe bs (nested != 0) params tbl rdv ms block) a₀).2 ∧ AbsOK s'.mem ∧ RcMR s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (icrE_spec p P hp (n + 2) s₀ vis pp nested pO pL tO tL rd mO mL bO bL)
    (icr_ref hkp henv hV hApd hCrk hCrf hIlpf P hF hWt hclR hfR hCs hMa hOwn hkeep hfRc n hn hC hbs hrb hpar hparb
      htbl hrd hms hblk hP hA hma hgate hsh hparP htblP hrdP hmsP hblkP hT hMs)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hres, hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.rrs, hR.abs, hR.rc⟩

end sims

end L.Ind

end
