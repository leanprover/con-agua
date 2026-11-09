module

import ConAgua.Arena.IndT.IdxSorts
import ConAgua.Arena.IndT.GenRec3
public import ConAgua.Arena.IndT.ArmMemos
import ConAgua.Arena.IndRealSctC
import ConAgua.Arena.RecCheckSpec.BlockNestedBit
public import ConAgua.Arena.IndInstallSpec.BpRecBpassR
public import ConAgua.Arena.IndInstallSpec.ConsRecsTFSimOf
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConRon.Bridge.Inductives.BlockTail
import ConAgua.Arena.IndInstallSpec.ConsBlockCtors
import ConAgua.Arena.IndInstallSpec.IcvgW
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl
import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndInstallSpec.PosFreeMfr
import ConAgua.Arena.IndPartsSpec.BlockSplitRecs
import ConAgua.Arena.RecCheckSpec.CnfW
import ConAgua.Arena.RefWalk
import ConAgua.Arena.ScratchRefine
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.IndInstallSpec.GpbWSimF
public import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
public import ConAgua.Arena.IndT.GenRec2
public import ConRon.Bridge.Inductives.BlockTail
import all ConAgua.Arena.IndInstall

@[expose] public section

/-!
# `checkBlockTail` under `StageC` (lane `indstaget`)

`check_block_tail`'s model (over the program's own calls), from `StageC` at the formers' index
and the pass record's denotation (con-ron's `checkBlockTail_of`): the index binders' sorts
(`iisr_ref` through its run), the constructors consed (L only; con-ron's `consBlockCtors_spec`
gives the pushed index's reading), the flush entering them (`ReadOK.flush`: `StageC` at the pushed
index and environment), the recursor stage (`checkBlockRec_refinesC`), then the recursors consed
and the tables under `StageR` (no core call follows them).
-/


noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

set_option experimental.vcgen true in
/-- **`check_block_tail`'s unified model**: `block_shape_member_ctors`, `cons_block_ctors`, the
flush and the nested bit (outside the verdict closure) lifted; the index sorts, the recursor stage,
the stream's checks and the tables through their calls. -/
l_model ictlE_spec (p : Prog) (hP : TailProg p)
  fns [hP.tail ↦ ictlE]
  specs [callW_spec p n "block_shape_member_ctors", callW_spec p n "cons_block_ctors",
    callW_spec p n "flush_caches", callW_spec p n "block_nested_bit"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## The twin, split at the L calls -/

/-- `checkBlockTail`'s second half (the Rust's `check_block_tail_stream`): the K flags, the generated
family pushed in place, a flush, the stream's recursors against it, the pops, a flush. -/
def tailStreamT (mode : ConLeche.CheckMode) (p : BlockShape) (fe₂b : IFEnv)
    (out : List (IConstantVal × TargetMajor × List EIdx)) : AM IFEnv := do
  ConRon.Arena.streamKCheck p p.recs out
  let infos ← ConRon.Arena.blockRecInfosTF p 0 out
  let (feG, prevs) := ConRon.Arena.consBlockRecsTemp infos fe₂b []
  ConRon.Arena.flushCaches
  ConRon.Arena.streamRecsCheck mode feG p.recs out
  let fe₃ := prevs.foldr (fun (n, prev) acc => acc.popTemp n prev) feG
  ConRon.Arena.flushCaches
  pure fe₃

/-- **`checkBlockTail` at `check_block_tail`'s calls.** -/
theorem checkBlockTail_split (mode : ConLeche.CheckMode) (block : List IConstantInfo) (q : BlockPass) :
    ConRon.Arena.checkBlockTail mode block q = (do
      ConRon.Arena.checkBlockIdxSorts mode q.env1 q.p q.p.members
      let fe₂ := ConRon.Arena.consBlockCtors q.p.nP q.p.memberCtors q.env1
      ConRon.Arena.flushCaches
      let nested := ConRon.Arena.blockNestedBit q.p q.kinds
      let (fe₂b, out) ← ConRon.Arena.checkBlockRec mode fe₂ q.p nested q.params q.tbl q.rd q.cls block
      let fe₃ ← tailStreamT mode q.p fe₂b out
      ConRon.Arena.checkBlockTables q.p fe₃ q.p.members
      pure fe₃) := by
  simp only [ConRon.Arena.checkBlockTail, tailStreamT, bind_assoc, pure_bind]

/-! ## `check_block_tail_stream`'s contract -/

/-- What `check_block_tail_stream` gives (from `m`, `a`; at the constructors' environment `env₂`):
the stage at the returned view of the popped environment, con-ron's `EnvRel` there, the pools
grown, the memos, the twin's step. -/
structure TsPost (dn : NIdx → Option ConLeche.Name) (env₂ : ConLeche.Env) (m : Mem) (a : AState)
    (w : Word) (fe' : IFEnv) (m' : Mem) (a' : AState) : Prop where
  stage : StageC dn w fe' env₂ m' a'
  rel : ConRon.Bridge.Inductives.EnvRel env₂ fe' a'.store
  grow : IWGrow m m'
  abs : AbsOK m'
  rc : RcMR m'
  inst : ConRon.Bridge.Inductives.InstStep a a'

/-- **`check_block_tail_stream(p, fe2b, out.off, out.len)`'s contract**: `tailStreamT`, both
outcomes, from the stage at the recursor stage's environment `fe` (`EnvRel` to `env₂`, the
constructors' environment), the shape and the generated family decoded and denoted, and the
generated family's environment well formed (con-leche's `consBlockRecsT`). -/
def TsRefS (G : Prop) (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (vis : Word) (fe : IFEnv) (env₂ : ConLeche.Env) (m : Mem) (a : AState)
    (pp go gl : Word) (bs : BlockShape) (bsP : ConLeche.BlockShape)
    (gs : List (IConstantVal × TargetMajor × List EIdx))
    (gsP : List (ConLeche.ConstantVal × ConLeche.TargetMajor × List ConLeche.Expr)),
    StageC dn vis fe env₂ m a → AbsOK m → RcMR m →
    ConRon.Bridge.Inductives.EnvRel env₂ fe a.store →
    ConLeche.EnvWF (ConLeche.consBlockRecsT bsP 0 gsP env₂) →
    DecB (fun m => decBS m pp.toNat) m bs → RecsB m pp → pp.toNat + 3 < iwTop m →
    PSlR decRR gs go gl m →
    ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    gs.mapM (ConRon.Bridge.Inductives.dRecOut a.store) = some gsP →
    RefE G (callE p n "check_block_tail_stream" [pp, vis, go, gl] m) (tailStreamT V bs fe gs) a
      (fun rm fe' a' => TsPost dn env₂ m a (rm.1.headD 0) fe' rm.2 a')

/-- What `check_block_tail` gives besides the index `x` it returns, at the view `w` (from `m`): the
stage, the growth, the `hb` memo, `AbsOK`, the recursor stage's memos. -/
structure TailPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (w : Word) (x : IFEnv) (m' : Mem)
    (a' : AState) : Prop where
  stage : StageR w x m' a'
  grow : IWGrow m m'
  memo : HbMemo m'
  abs : AbsOK m'
  rc : RcMR m'

section sims
variable {p : Prog} (hkp : KnotStageProg p) {env₁ : ConLeche.Env} (henv₁ : ConLeche.EnvWF env₁)
  (hV : ValProg p)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
include hkp henv₁ hV hOpf hLC hLT hApd hCrk hIlpf in
/-- **`check_block_tail` refines `checkBlockTail`, both outcomes** (twin side con-ron's
`checkBlockTail_of`): the index sorts (`iisr_ref` through its run), the
constructors consed, the flush, the nested bit, then `check_block_tail_rec`'s model (no refinement
of its own: it is the tail's second half): the recursor stage (`icr_ref` on the run), the recursors
consed, the tables (`ctb_ref` on the run). -/
theorem tail_ref (hP : TailProg p) (L : CbrLook p) {fs : List FnName}
    (hfs : ∀ f ∈ tailCallees, f ∈ fs) (hcl : closedA p hbFreeA hbFreeC fs = true) (N : Nat)
    {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {m : Mem} {a : AState} {bO bL q : Word} {bp : BlockPass} {block : List IConstantInfo}
    (hN : N ≤ 2 ^ 62 + 1) (hC : StageC dn vis fe env₁ m a) (hq : BPassR vis fe m q bp)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block) (hM : HbMemo m) (hA : AbsOK m)
    (hkeep : ∀ f ∈ tailKeepCalleesC, AbsKeep p f) (hR : RcMR m)
    (hrb : RecsB m (rdW (m.arr64 IW) (q + 3)))
    (hlp : ClassesLp m (rdW (m.arr64 IW) (q + 15)) (rdW (m.arr64 IW) (q + 16)))
    (hcoh : ConRon.Bridge.IFEnvCoh fe) (hden : ConRon.Bridge.denoteFEnv a.store fe = some env₁)
    {qP : ConLeche.BlockPass ConLeche.Env}
    (hqP : ConRon.Bridge.Inductives.dPass a.store env₁ bp = some qP)
    {blockP : List ConLeche.ConstantInfo} (hbP : Frontend.denoteCIList a.store block = some blockP)
    (hTw : ∀ cv ∈ qP.cvTas, ConLeche.Expr.WScoped 0 cv.type)
    (henv₂ : ConLeche.EnvWF (ConLeche.consBlockCtors qP.p.nP qP.ctorsAs env₁))
    (hMs : ∀ M ∈ qP.cls, ConLeche.Cached.ClassMajScoped qP.p.nP M)
    (hfRc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR) {fsH : List FnName}
    (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true) (hfH : "check_block_tables" ∈ fsH) :
    RefE (VerdictCtxU p) (ictlE p N m bO bL q) (ConRon.Arena.checkBlockTail V block bp) a
      (fun v x a' => TailPost dn m v.1 x v.2 a') := by
  have hS := hC.stage
  obtain ⟨hdq, hB, hw0, hsrc⟩ := hq
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hq19 := hB.1
  have hk : ∀ k, k < 19 → (q + UInt64.ofNat k).toNat = q.toNat + k := fun k hk => tailToNat (by omega)
  -- the record
  have hdq' : decBPass fe (truncM m) q.toNat = some bp := hdq
  simp only [decBPass, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hdq'
  obtain ⟨cvTas, hcv, pw, hpw, bs, hbs, ctorsAs, hca, sss, hsss, kinds, hkd, nfs, hnfs, params, hpar, rdp,
    hrdp, rd, hrd, cls, hcls, tbl, htbl, rfl⟩ := hdq'
  -- con-ron's reading of the pass record
  obtain ⟨-, hcvP, hpP, hcaP, hssP, -, -, hpaP, hrdP, hclP, htbP⟩ :=
    ConRon.Bridge.Inductives.dPass_inv hqP
  obtain ⟨shP, hshP, hpPeq⟩ : ∃ shP, ConRon.Bridge.Inductives.dShape a.store bs = some shP ∧
      qP.p = ⟨shP⟩ := by
    simp only [ConRon.Bridge.Inductives.dParts, Option.map_eq_some_iff] at hpP
    obtain ⟨shP, h1, h2⟩ := hpP; exact ⟨shP, h1, h2.symm⟩
  obtain ⟨hmsP, -, hnPP, -, -, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hshP
  obtain ⟨hw3, hpwb⟩ := bpWord hpw (hk 3 (by decide))
  rw [show (q + UInt64.ofNat 3 : Word) = q + 3 from rfl] at hw3
  rw [hw3] at hsrc hrb
  have hpw' : (UInt64.ofNat pw : Word).toNat = pw := UInt64.toNat_ofNat_of_lt' hpwb
  have hbsD : DecB (fun m => decBS m (UInt64.ofNat pw : Word).toNat) m bs := by rw [hpw']; exact hbs
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some hbs
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hbsD hsrc
  have hpw9 : pw + 9 ≤ iwTop m := by rw [← hpw']; exact hq9
  -- the slices
  have hmss := bpPSl decMS_mono hmem (fun o l h1 h2 => hsrc o l (by rw [hpw']; exact h1) (by rw [hpw']; exact h2))
    (w := UInt64.ofNat pw) (w1 := UInt64.ofNat pw + 1) hpw'
    (by rw [UInt64.toNat_add, hpw']; simp; omega)
  have e : ∀ k : Nat, k < 19 → ∀ w : Word, w = q + UInt64.ofNat k → w.toNat = q.toNat + k :=
    fun k hk w hw => by rw [hw]; exact tailToNat (by omega)
  have hcvs := bpPSl (fun q => OMono.decCVp q) hcv (hB.2 1 (by simp)) (w := q + 1) (w1 := q + 2)
    (e 1 (by decide) _ rfl) (e 2 (by decide) _ rfl)
  have hcas := bpPSl decCNS_mono hca (hB.2 4 (by simp)) (w := q + 4) (w1 := q + 5)
    (e 4 (by decide) _ rfl) (e 5 (by decide) _ rfl)
  have hsss' := bpPSl decISS_mono hsss (hB.2 6 (by simp)) (w := q + 6) (w1 := q + 7)
    (e 6 (by decide) _ rfl) (e 7 (by decide) _ rfl)
  have hkfm : ∀ q, OMono (fun m => decLH m (decPL m (decLH m (decKL m))) q) :=
    fun q => OMono.decAt (fun o l => OMono.decPL (fun q => OMono.decAt (fun o l => decKL_mono o l) q) o l) q
  have hks := bpPSl hkfm hkd (hB.2 8 (by simp)) (w := q + 8) (w1 := q + 9)
    (e 8 (by decide) _ rfl) (e 9 (by decide) _ rfl)
  obtain ⟨hpd, hpb⟩ := bpHSl hpar (hB.2 12 (by simp)) (w := q + 12) (w1 := q + 13)
    (e 12 (by decide) _ rfl) (e 13 (by decide) _ rfl)
  obtain ⟨hw14, hrdb⟩ := bpWord hrdp (e 14 (by decide) _ rfl)
  have hrdD : DecB (fun m => decCR m (UInt64.ofNat rdp : Word).toNat) m rd := by
    rw [UInt64.toNat_ofNat_of_lt' hrdb]; exact hrd
  have hcls' := bpPSl (fun q => decTM_mono q) hcls (hB.2 15 (by simp)) (w := q + 15) (w1 := q + 16)
    (e 15 (by decide) _ rfl) (e 16 (by decide) _ rfl)
  have htbl' := bpPSl (fun q => decNCN_mono q) htbl (hB.2 17 (by simp)) (w := q + 17) (w1 := q + 18)
    (e 17 (by decide) _ rfl) (e 18 (by decide) _ rfl)
  -- `check_block_idx_sorts`
  rcases N with _ | n
  · rw [ictlE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  have hn : n ≤ 2 ^ 62 := by omega
  rw [ictlE.arm1, hw0, hw3]
  unfold ConRon.Arena.checkBlockTail
  dsimp only
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => rfl)
    (iisrE_spec p hP.idx hOpf n ⟨m, Locals.init []⟩ vis _ _ _ _ _) (fun hG => hG.nv) (fun hG => hG.toVerdictCtx)
    (iisr_ref hkp henv₁ hLC hLT hP.idx (UInt64.ofNat pw) bs n hn hC hA hbsD hsrc hmss hcvs hshP hcvP hTw hden)
    fun r1 s1 _ a1 c1 _ _ ⟨hC1, hg1, _, hA1, c1'⟩ => ?_
  dsimp only [ictlE.k_check_block_idx_sorts] at hC1 hg1 hA1 ⊢
  have d1 := callW_of_callE c1
  have hM1 : HbMemo s1.mem := HbMemo.ofClosed hcl (hfs _ (by decide)) d1 hM
  have hR1 : RcMR s1.mem := RcMR.ofClosed hclR (hfR _ (by decide)) d1 hR
  have hk1 : KeepW m s1.mem := callW_keepW d1
  have hS1 := hC1.stage
  -- `cons_block_ctors` (the twin's `fe₂`, a pure function)
  obtain ⟨hnp1, -, -, -⟩ := partsShapeWords hg1 hbsD hq9
  have hca1 := hcas.grow decCNS_mono hg1
  rw [partsRdIW_grow hg1 (w := q + 4) (by rw [e 4 (by decide) (q + 4) rfl]; omega),
    partsRdIW_grow hg1 (w := q + 5) (by rw [e 5 (by decide) (q + 5) rfl]; omega), hnp1]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r2 m2 c2 => ?_
  dsimp only [ictlE.k_cons_block_ctors]
  obtain ⟨s2, rfl, -, hS2, hg2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (consBlockCtors_refines p hP.recp hP.hci hP.hcs hP.hcbc n _ a1 dn fe _ _ _ vis ctorsAs hS1 hca1) c2
  have hM2 : HbMemo s2.mem := HbMemo.ofClosed hcl (hfs _ (by decide)) c2 hM1
  have hA2 : AbsOK s2.mem := hkeep _ (by simp [tailKeepCalleesC, grcKeepCalleesC]) _ _ _ _ _ c2 hA1
  have hR2 : RcMR s2.mem := RcMR.ofClosed hclR (hfR _ (by decide)) c2 hR1
  have hk2 := hk1.trans (callW_keepW c2)
  rw [UInt64.toNat_ofNat_of_lt' (partsShapeWords (IWGrow.refl m) hbsD hq9).2.1] at hS2
  obtain ⟨hcons, hconsOK⟩ := ConRon.Bridge.Inductives.consBlockCtors_spec a1.store bs.nP ctorsAs
    qP.ctorsAs fe env₁ (ConRon.Bridge.Inductives.dCtors_ext.list c1'.ext _ _ hcaP)
    (ConRon.Bridge.denoteFEnv_mono c1'.ext hden) hcoh
  -- the flush
  refine RefE.bindSim (fun _ => rfl) (tailSimFlush hP.flush n hS2 hM2) fun r3 _ m3 a3 c3 hrun3 ⟨hS3, hg3, hM3⟩ => ?_
  dsimp only [ictlE.k_flush_caches]
  have hR3 : RcMR m3 := RcMR.ofClosed hclR (hfR _ (by decide)) c3 hR2
  have hk3 := hk2.trans (callW_keepW c3)
  have hA3 : AbsOK m3 := by
    obtain ⟨s', rfl, -, -, hmem⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩) (flushCaches_spec p hP.flush n _) c3
    rw [hmem]; exact AFr.of_frame (flushMem_frame _) (by decide) (by decide) hA2
  obtain ⟨hck3, -, hst3⟩ := ConRon.Bridge.Inductives.ReadOK.flush (μ := V)
    (⟨c1'.ok.state, c1'.ok.pins, hconsOK c1'.ok.state.wf (ConRon.Bridge.TablesStored.of_envWF henv₁) c1'.ok.ienv.toS a1 rfl⟩ :
      ConRon.Bridge.Inductives.ReadOK _ _ a1) hrun3
  have hC3 := StageC.of_parts hS3 hck3 hA3
    (fun k x e => by rw [hst3]; exact c1'.ext.lss.ls.ns k x (hC.mem.dnN k x e))
  have hg03 := (hg1.trans hg2).trans hg3
  -- `block_nested_bit` (the twin's `nested`, a pure function)
  have hks3 := hks.grow hkfm hg03
  rw [partsRdIW_grow hg03 (w := q + 8) (by rw [e 8 (by decide) (q + 8) rfl]; omega),
    partsRdIW_grow hg03 (w := q + 9) (by rw [e 9 (by decide) (q + 9) rfl]; omega)]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r4 m4 c4 => ?_
  dsimp only [ictlE.k_block_nested_bit]
  obtain ⟨s4, rfl, hs4, hr4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (blockNestedBit_refines p hP.nf hP.ni hP.nm hP.nk hP.ng hP.nb n _ _ _ _ bs kinds hS3.iw.iwSize
      (DecB.get (decBS_mono _) (hbsD.grow (decBS_mono _) hg03)) (DecB.get (OMono.decPL hkfm _ _) hks3.1)) c4
  subst hs4
  have hnb : (r4.headD 0 != 0) = ConRon.Arena.blockNestedBit bs kinds := by
    rw [hr4]; cases ConRon.Arena.blockNestedBit bs kinds <;> rfl
  -- through `check_block_tail_rec`'s model
  rcases n with _ | k
  · rw [ictrE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  rw [ictrE.arm1]
  -- `check_block_rec`
  have hrd3 : rdW (m3.arr64 IW) (q + 14) = UInt64.ofNat rdp := by
    rw [partsRdIW_grow hg03 (w := q + 14) (by rw [e 14 (by decide) (q + 14) rfl]; omega)]; exact hw14
  have hbs3 := hbsD.grow (decBS_mono _) hg03
  have hsrc3 := partsHsrc_grow hg03 hq9 hsrc
  obtain ⟨-, -, hmv3⟩ := partsShapeFacts hbs3 hsrc3
  have hBS3 : BSOK m3 (UInt64.ofNat pw : Word).toNat bs :=
    ⟨hbs3, hsrc3, fun o l j v ho hl hj hv => by have := hmv3 o l j v ho hl hj hv; omega⟩
  have hrb3 : RecsB m3 (UInt64.ofNat pw) := hrb.grow hg03 (by rw [hpw']; omega)
  have r15 : rdW (m3.arr64 IW) (q + 15) = rdW (m.arr64 IW) (q + 15) :=
    partsRdIW_grow hg03 (by rw [e 15 (by decide) (q + 15) rfl]; omega)
  have r16 : rdW (m3.arr64 IW) (q + 16) = rdW (m.arr64 IW) (q + 16) :=
    partsRdIW_grow hg03 (by rw [e 16 (by decide) (q + 16) rfl]; omega)
  have hlp3 : ClassesLp m3 (rdW (m3.arr64 IW) (q + 15)) (rdW (m3.arr64 IW) (q + 16)) := by
    rw [r15, r16]; exact hlp.grow hcls' hg03 hk3 hS.iw.iwSize
  have hpre : BSOK m3 (UInt64.ofNat pw : Word).toNat bs ∧
      decHL m3 (rdW (m3.arr64 IW) (q + 12)).toNat (rdW (m3.arr64 IW) (q + 13)).toNat = some params ∧
      (rdW (m3.arr64 IW) (q + 12)).toNat + (rdW (m3.arr64 IW) (q + 13)).toNat ≤ iwTop m3 ∧
      PSlR decNCN tbl (rdW (m3.arr64 IW) (q + 17)) (rdW (m3.arr64 IW) (q + 18)) m3 ∧
      DecB (fun m => decCR m (rdW (m3.arr64 IW) (q + 14)).toNat) m3 rd ∧
      PSlR decTM cls (rdW (m3.arr64 IW) (q + 15)) (rdW (m3.arr64 IW) (q + 16)) m3 ∧
      PSlR decCVp cvTas (rdW (m3.arr64 IW) (q + 1)) (rdW (m3.arr64 IW) (q + 2)) m3 ∧
      DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m3 block := by
    have r : ∀ k, k < 19 → ∀ w : Word, w = q + UInt64.ofNat k → rdW (m3.arr64 IW) w = rdW (m.arr64 IW) w :=
      fun k hk w hw => partsRdIW_grow hg03 (by rw [e k hk w hw]; omega)
    refine ⟨hBS3, ?_, ?_, ?_, ?_, ?_, ?_, hblk.grow ?_ hg03⟩
    · rw [r 12 (by decide) (q + 12) rfl, r 13 (by decide) (q + 13) rfl]; exact (by rw [decHL_grow3 hg03 hpb]; exact hpd)
    · rw [r 12 (by decide) (q + 12) rfl, r 13 (by decide) (q + 13) rfl]; exact Nat.le_trans hpb hg03.iw
    · rw [r 17 (by decide) (q + 17) rfl, r 18 (by decide) (q + 18) rfl]; exact htbl'.grow (fun q => decNCN_mono q) hg03
    · rw [hrd3]; exact hrdD.grow (decCR_mono _) hg03
    · rw [r 15 (by decide) (q + 15) rfl, r 16 (by decide) (q + 16) rfl]; exact hcls'.grow (fun q => decTM_mono q) hg03
    · rw [r 1 (by decide) (q + 1) rfl, r 2 (by decide) (q + 2) rfl]; exact hcvs.grow (fun q => OMono.decCVp q) hg03
    · exact decEBlk_mono _ _ _
  have hx3 : Ext a.store a3.store := by rw [hst3]; exact c1'.ext
  have hnP : qP.p.nP = bs.nP := by rw [hpPeq]; exact hnPP.symm
  rw [hnP] at henv₂
  rw [hpPeq] at hMs
  have dd1 := ConRon.Bridge.Inductives.dShape_ext hx3 _ _ hshP
  have dd2 := ConRon.Bridge.denoteEList_ext hx3 _ _ hpaP
  have dd3 := ConRon.Bridge.Inductives.dCtorNf_ext.list hx3 _ _ htbP
  have dd4 := ConRon.Bridge.Inductives.dClassRead_ext hx3 _ _ hrdP
  have dd5 := ConRon.Bridge.Inductives.dMajor_ext.list hx3 _ _ hclP
  have dd6 : cvTas.mapM (Frontend.denoteCV a3.store) = some qP.cvTas :=
    ConRon.Bridge.Inductives.DExt.list (d := Frontend.denoteCV)
      (fun hx _ _ h => ConRon.Bridge.denoteCV_ext h hx) hx3 _ _ hcvP
  have dd7 := ConRon.Bridge.denoteCIList_mono hx3 _ _ hbP
  have hden₂ : ConRon.Bridge.denoteFEnv a3.store (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe) =
      some (ConLeche.consBlockCtors bs.nP qP.ctorsAs env₁) := by
    obtain ⟨e, h, rfl⟩ := hcons.denote; rw [hst3]; exact h
  have hfRc1 : ∀ f ∈ grcMemoCallees, f ∈ fsR := fun f hf => hfR f (by
    simp only [grcMemoCallees, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> decide)
  have hR5 := icr_ref hkp henv₂ hV hApd hCrk hIlpf hP.grc hclR hfRc1 k (by omega) m3 a3 dn _ _ _ _ _ _ _ _
    _ _ _ _ _ _ bs params tbl rd cls cvTas block hC3 hpre hrb3 hlp3 hR3 hA3
    (fun f hf => hkeep f (List.mem_append_right _ hf)) hcons.coh hden₂ dd1 dd2 dd3 dd4 dd5 dd6 dd7 hMs hTw
    (fun f hf => hfRc f (List.mem_append_left _ hf)) (nested := r4.headD 0)
  have hT5 := icrE_spec p hP.grc hP.crec k ⟨m3, Locals.init []⟩ (r2.headD 0) (UInt64.ofNat pw) (r4.headD 0)
    (rdW (m3.arr64 IW) (q + 12)) (rdW (m3.arr64 IW) (q + 13)) (rdW (m3.arr64 IW) (q + 17))
    (rdW (m3.arr64 IW) (q + 18)) (rdW (m3.arr64 IW) (q + 14)) (rdW (m3.arr64 IW) (q + 15))
    (rdW (m3.arr64 IW) (q + 16)) bO bL (rdW (m3.arr64 IW) (q + 1)) (rdW (m3.arr64 IW) (q + 2))
  rw [hnb] at hR5
  refine RefE.bindRun (s₀ := ⟨m3, Locals.init []⟩) (fun _ => rfl) hT5 (fun hG => hG.nv) id hR5
    fun r6 s5 ⟨fe2b, outs⟩ a5 c6 _ hrun5 hR5' => ?_
  dsimp only [ictrE.k_check_block_rec]
  have d6 := callW_of_callE c6
  have hC5' := hR5'.stage
  have hd5 := hR5'.rrs
  have hA5 := hR5'.abs
  have hg5 := hR5'.grow
  dsimp only at hC5' hd5 hA5 hg5
  have hM5 : HbMemo s5.mem := HbMemo.ofClosed hcl (hfs _ (by decide)) d6 hM3
  have hR5r : RcMR s5.mem := hR5'.rc
  have hS5 := hC5'.stage
  -- con-ron's recursor stage on the twin's run (the recursors' readings, their freshness)
  obtain ⟨cr3, outP, ⟨hcoh₂b, hfe₂b, hout, hfresh⟩, -⟩ :=
    ConRon.Bridge.Inductives.recStage (μ := V) rfl (ConRon.Bridge.CoreSpec.of_core rfl) _ _ ⟨bs⟩ ⟨shP⟩
      _ params qP.params tbl qP.tbl.toList rd qP.rd cls qP.cls cvTas qP.cvTas block blockP henv₂ hcons.coh hTw
      hMs a3 a5 _ hck3
      ⟨hden₂, by simp only [ConRon.Bridge.Inductives.dParts, ConRon.Bridge.Inductives.dShape_ext hx3 _ _ hshP]; rfl,
        dd2, dd3, dd4, dd5, dd6, dd7⟩ hrun5
  have x35 := cr3.ext
  -- `cons_block_recs_tf`
  rw [hS2.check.env.vis]
  refine RefE.bindSim (fun _ => rfl) (consRecsTFSim_of L hcl (hfs _ (by decide)) k dn (r6.headD 0)
    (r2.headD 0) (UInt64.ofNat pw) fe2b s5.mem a5 bs r6.tail outs hS5
    ((hbsD.grow (decBS_mono _) hg03).grow (decBS_mono _) hg5) hd5 hM5 hA5)
    fun r7 fe3 m7 a6 c7 hrun6 ⟨hS6, hg6, hM6, hA6⟩ => ?_
  dsimp only [ictrE.k_cons_block_recs_tf]
  have hR6 : RcMR m7 := RcMR.ofClosed hclR (hfRc _ (by simp)) c7 hR5r
  -- con-ron's recursors' cons on the twin's run: the store extended, the state and pins kept
  have hvis : fe2b.visibleBelow = (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe).visibleBelow := by
    rw [hcoh₂b.1, hcons.coh.1, hfe₂b]
  have hfind₂b : fe2b.find? = (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe).find? := by
    funext n; rw [hcoh₂b.find?, hcons.coh.find?, hfe₂b]
  have hraw₂b : ∀ n, fe2b.rawTable? n = (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe).rawTable? n := by
    intro n; rw [hcoh₂b.rawTable?, hcons.coh.rawTable?, hfe₂b]
  have hden₂b : ConRon.Bridge.denoteFEnv a5.store fe2b = some (ConLeche.consBlockCtors bs.nP qP.ctorsAs env₁) := by
    have h' := ConRon.Bridge.denoteFEnv_mono x35 hden₂
    simp only [ConRon.Bridge.denoteFEnv] at h' ⊢; rw [hfe₂b]; exact h'
  have x05 : Ext a.store a5.store := hx3.trans x35
  have hview : (fe2b.restrictTo (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe).visibleBelow).find?
      = (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe).find? := by
    rw [← hvis]; exact hfind₂b
  obtain ⟨c4'', -⟩ := ConRon.Bridge.Inductives.consBlockRecsTF_spec (μ := V)
    (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe).visibleBelow bs shP outs outP 0
    fe2b _ a5 a6 fe3 cr3.ok (ConRon.Bridge.Inductives.RC.IFEnvOK.of_find? cr3.ok.ienv hview hraw₂b)
    (Nat.le_of_eq hvis.symm) hcoh₂b hden₂b (ConRon.Bridge.Inductives.dShape_ext x05 _ _ hshP) hout hfresh
    (by rw [hS2.check.env.vis]; exact hrun6)
  have x06 : Ext a.store a6.store := x05.trans c4''.ext
  -- `check_block_tables`
  have hg06 := (hg03.trans hg5).trans hg6
  have r : ∀ k, k < 19 → ∀ w : Word, w = q + UInt64.ofNat k → rdW (m7.arr64 IW) w = rdW (m.arr64 IW) w :=
    fun k hk w hw => partsRdIW_grow hg06 (by rw [e k hk w hw]; omega)
  rw [partsRdIW_grow hg06 (w := UInt64.ofNat pw) (by rw [hpw']; omega),
    partsRdIW_grow hg06 (w := UInt64.ofNat pw + 1) (by rw [UInt64.toNat_add, hpw']; simp; omega),
    r 4 (by decide) (q + 4) rfl, r 5 (by decide) (q + 5) rfl, r 6 (by decide) (q + 6) rfl,
    r 7 (by decide) (q + 7) rfl]
  have hT8 := ctbE_spec p hP.tabs.tbl hP.tabs.one hP.tabs.tabs k ⟨m7, Locals.init []⟩ (UInt64.ofNat pw)
    (rdW (m.arr64 IW) (UInt64.ofNat pw)) (rdW (m.arr64 IW) (UInt64.ofNat pw + 1)) (rdW (m.arr64 IW) (q + 4))
    (rdW (m.arr64 IW) (q + 5)) (rdW (m.arr64 IW) (q + 6)) (rdW (m.arr64 IW) (q + 7)) (r7.headD 0)
  have hR8 := ctb_ref hP.tabs hApd dn (UInt64.ofNat pw) bs k (by omega) m7 a6 (r7.headD 0) fe3 _ _ _ _ _ _
      bs.members ctorsAs sss hS6 (hbsD.grow (decBS_mono _) hg06) (partsHsrc_grow hg06 hq9 hsrc)
      (hmss.grow decMS_mono hg06) (hcas.grow decCNS_mono hg06) (hsss'.grow decISS_mono hg06) hM6 hA6
      (fun f hf => hkeep f (by simp_all [tablesKeepCallees, tailKeepCalleesC, grcKeepCalleesC]))
      c4''.ok.state c4''.ok.pins ⟨shP, ConRon.Bridge.Inductives.dShape_ext x06 _ _ hshP⟩
      ⟨_, ConRon.Bridge.Inductives.dMember_ext.list x06 _ _ hmsP⟩
      ⟨_, ConRon.Bridge.Inductives.dCtors_ext.list x06 _ _ hcaP⟩
      ⟨_, ConRon.Bridge.Inductives.DExt.list (d := ConRon.Bridge.Inductives.denoteLLists)
        (fun hx x y h => ConRon.Bridge.Inductives.BI.denoteLLists_ext hx x y h) x06 _ _ hssP⟩
  rw [← bind_pure (ConRon.Arena.checkBlockTables _ _ _ _ _)]
  refine RefE.bindRun (s₀ := ⟨m7, Locals.init []⟩) (fun _ => rfl) hT8 (fun hG => hG.nv) (fun _ => trivial) hR8
    fun r8 s8 x a' c8 _ h1 h2 => ?_
  exact RefE.ret rfl ⟨h2.stage, hg06.trans h2.grow, h2.memo, h2.abs,
    RcMR.ofClosedHb hclH hfH (callW_of_callE c8) hR6 h2.memo⟩
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
include hkp henv₁ hV hOpf hLC hLT hApd hCrk hIlpf in
/-- **`check_block_tail` refines `checkBlockTail` under `StageC`** (`checkBlockTail_refines`'s;
twin side con-ron's `checkBlockTail_of`): from `StageC` at the formers' index and the pass record's
denotation; the post is `StageR` (no core call follows the tables). -/
@[refines ConRon.Arena.checkBlockTail]
theorem checkBlockTail_refinesC (hP : TailProg p) (L : CbrLook p) {fs : List FnName}
    (hfs : ∀ f ∈ tailCallees, f ∈ fs) (hcl : closedA p hbFreeA hbFreeC fs = true) (n : Nat)
    (hn : n ≤ 2 ^ 62) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (s₀ : St) (a₀ : AState) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {bO bL q : Word} {bp : BlockPass} {block : List IConstantInfo}
    (hC : StageC dn vis fe env₁ s₀.mem a₀) (hq : BPassR vis fe s₀.mem q bp)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) s₀.mem block) (hM : HbMemo s₀.mem)
    (hA : AbsOK s₀.mem) (hk : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (hR : RcMR s₀.mem) (hrb : RecsB s₀.mem (rdW (s₀.mem.arr64 IW) (q + 3)))
    (hlp : ClassesLp s₀.mem (rdW (s₀.mem.arr64 IW) (q + 15)) (rdW (s₀.mem.arr64 IW) (q + 16)))
    (hcoh : ConRon.Bridge.IFEnvCoh fe) (hden : ConRon.Bridge.denoteFEnv a₀.store fe = some env₁)
    {qP : ConLeche.BlockPass ConLeche.Env}
    (hqP : ConRon.Bridge.Inductives.dPass a₀.store env₁ bp = some qP)
    {blockP : List ConLeche.ConstantInfo} (hbP : Frontend.denoteCIList a₀.store block = some blockP)
    (hTw : ∀ cv ∈ qP.cvTas, ConLeche.Expr.WScoped 0 cv.type)
    (henv₂ : ConLeche.EnvWF (ConLeche.consBlockCtors qP.p.nP qP.ctorsAs env₁))
    (hMs : ∀ M ∈ qP.cls, ConLeche.Cached.ClassMajScoped qP.p.nP M)
    (hfRc : ∀ f ∈ grcRcCallees ++ ["cons_block_recs_tf"], f ∈ fsR) {fsH : List FnName}
    (hclH : closedA p rcHbFreeA rcHbFreeC fsH = true) (hfH : "check_block_tables" ∈ fsH) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_tail" [bO, bL, q]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockTail V block bp) a₀ ∧
      StageR (r.headD 0) (AM.res (ConRon.Arena.checkBlockTail V block bp) a₀) s'.mem
        (AM.st (ConRon.Arena.checkBlockTail V block bp) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ HbMemo s'.mem ∧ AbsOK s'.mem ∧ RcMR s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (ictlE_spec p hP (n + 1) s₀ bO bL q)
    (tail_ref hkp henv₁ hV hOpf hLC hLT hApd hCrk hIlpf hP L hfs hcl (n + 1) hclR hfR (by omega) hC hq hblk hM hA hk
      hR hrb hlp hcoh hden hqP hbP hTw henv₂ hMs hfRc hclH hfH)) ?_
  rintro r s' ⟨hl, x, a', run, hR'⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hres, hst]; exact hR'.stage, hR'.grow, hR'.memo, hR'.abs, hR'.rc⟩
-/

end sims

end L.Ind

end
