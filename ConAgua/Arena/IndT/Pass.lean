import ConAgua.Arena.IndT.Tail
import ConAgua.Arena.IndT.Install4
import ConAgua.Arena.IndT.Positivity
import ConAgua.Arena.IndT.RecGen21
import ConAgua.Arena.IndT.Install7
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# `check_block_pass`: one model, one refinement

`check_block_pass`' unified model (`icpE`) and its refinement for both outcomes (`pass_ref`;
`checkBlockPass_refinesC` is its ok half) from `StageC` at the entry index, with con-ron's
`checkBlockPass_of` run alongside: the formers (`checkBlockInds_refinesC`), the flush entering their
index (`ReadOK.flush`: `StageC` there), the constructors (`checkBlockCtors_refinesC`), the
positivity context (core-free, `StageR`; con-ron's `blockNestCtx_spec` for `CheckOK`), the classes
(`checkBlockClasses_refinesC`), the positivity check (`checkBlockPositivity_refinesC`), the seeds
(core-free), the nested seeds (`nestSeeds_refinesC`), the record. The post (`PassPost`) has
`StageC` at the formers' index and what `checkBlockTail_refinesC` takes (con-ron's
`checkBlockPass_of` on the whole run). The checks' error halves are their refinements' (`cbi_ref`,
`ict_ref`, `cbc_ref`, `cbp_ref`, `nsd_ref`) on the failing runs raised to the fixed fuel; `G` is
`CtsG`, which covers each of theirs.
-/


noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- What `checkBlockPass` hands the tail, con-ron's side (`checkBlockPass_of`'s post at the
formers' environment `env₁`). -/
def PassTwin (a a' : AState) (x : BlockPass) (env₁ : ConLeche.Env) : Prop :=
  ∃ qP : ConLeche.BlockPass ConLeche.Env, ConRon.Bridge.Inductives.InstStep a a' ∧
    ConRon.Bridge.IFEnvCoh x.env1 ∧ ConRon.Bridge.denoteFEnv a'.store x.env1 = some env₁ ∧
    ConLeche.EnvWF env₁ ∧ ConRon.Bridge.Inductives.dPass a'.store env₁ x = some qP ∧
    (∀ cv ∈ qP.cvTas, ConLeche.Expr.WScoped 0 cv.type) ∧
    ConLeche.EnvWF (ConLeche.consBlockCtors qP.p.nP qP.ctorsAs env₁) ∧
    (∀ M ∈ qP.cls, ConLeche.Cached.ClassMajScoped qP.p.nP M)

set_option experimental.vcgen true in
/-- **`check_block_pass`' unified model**: the flush, the positivity context, the classes' seeds and
the record (outside the verdict closure) lifted; the five checks through their runs (the ok half
reads the calls' walk memos, `PosMR.ofClosed`). -/
l_model icpE_spec (p : Prog) (hP : PassProg p)
  fns [hP.pass ↦ icpE]
  specs [callW_spec p n "flush_caches", callW_spec p n "block_nest_ctx", callW_spec p n "class_seeds",
    callW_spec p n "check_block_pass_rec"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `check_block_pass` gives besides the pass `x` it returns, a record at `w` (from `m`, `a`):
the stage at the formers' view, the growth, the record's layout, the walk memos, `AbsOK`, the
recursors' bound, the classes' layout; `StageC` at the formers' environment `env₁` and what the tail
takes (`PassTwin`). -/
structure PassPost (dn : NIdx → Option ConLeche.Name) (env : ConLeche.Env) (m : Mem) (p0 : Word)
    (a : AState) (w : Word) (x : BlockPass) (m' : Mem) (a' : AState) : Prop where
  stage : StageR dn (rdW (m'.arr64 IW) w) x.env1 m' a'
  grow : IWGrow m m'
  bpass : BPassR (rdW (m'.arr64 IW) w) x.env1 m' w x
  pos : PosMR m'
  abs : AbsOK m'
  recs : RecsB m p0 → RecsB m' (rdW (m'.arr64 IW) (w + 3))
  classes : ClassesLp m' (rdW (m'.arr64 IW) (w + 15)) (rdW (m'.arr64 IW) (w + 16))
  twin : ∃ env₁, StageC dn (rdW (m'.arr64 IW) w) x.env1 env₁ m' a' ∧ PassTwin a a' x env₁

section sims
variable {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p) (hIlpf : IlpfF p) (hLz : LzcF p)

include hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz in
/-- **`check_block_pass` refines `checkBlockPass`, both outcomes** under `StageC` (twin side
con-ron's `checkBlockPass_of`): each check's ok half by its `…_refinesC` on the call's run, its
error half by its refinement on the run (`RefE.run_err`, `CtsG`); the flush, the positivity
context, the seeds and the record are outside the verdict closure. -/
theorem pass_ref (hP : PassProg p) {fs : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs) (N : Nat)
    (hN : N ≤ 2 ^ 62) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState} {p0 isRec : Word} {bs : BlockShape} {b : Bool}
    (hC : StageC dn vis fe env m a) (hq : DecB (fun m => decBS m p0.toNat) m bs) (hsrc : ShapeSrc m p0)
    (hcx : ShapeCV m p0) (hb : (isRec != 0) = b) (hPm : PosMR m) (hA : AbsOK m)
    (hk : ∀ f ∈ passKeepCalleesC, AbsKeep p f)
    (hcoh : ConRon.Bridge.IFEnvCoh fe) (hden : ConRon.Bridge.denoteFEnv a.store fe = some env)
    {shP : ConLeche.BlockShape} (hshP : ConRon.Bridge.Inductives.dShape a.store bs = some shP)
    (hlpsDn : ∀ ms ∈ bs.members, ∀ k ∈ ms.cvT.levelParams, (dn k).isSome) :
    RefE (CtsG p) (icpE p N m vis p0 isRec) (ConRon.Arena.checkBlockPass V fe ⟨bs⟩ b) a
      (fun v x a' => PassPost dn env m p0 a v.1 x v.2 a') := by
  rcases N with _ | F
  · rw [icpE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  obtain ⟨n, hn, hle⟩ : ∃ n, n + 4 ≤ 2 ^ 62 ∧ F ≤ n + 3 := ⟨F - 3, by omega, by omega⟩
  rw [icpE.arm1]
  unfold ConRon.Arena.checkBlockPass
  have hcs : ConRon.Bridge.CoreSpec V ConRon.Arena.checkFuel := ConRon.Bridge.CoreSpec.of_core rfl
  have dnE : ∀ {st : ConRon.Arena.EStore}, ConRon.Arena.Ext a.store st →
      ∀ (k : NIdx) (x : ConLeche.Name), dn k = some x → denoteN st.ns k = some x :=
    fun hx k x e => hx.lss.ls.ns k x (hC.mem.dnN k x e)
  have hpP : ConRon.Bridge.Inductives.dParts a.store ⟨bs⟩ = some ⟨shP⟩ := by
    simp only [ConRon.Bridge.Inductives.dParts, hshP, Option.map_some]
  -- the formers
  refine RefE.bindRunLe hle (s₀ := ⟨m, Locals.init []⟩) (fun _ => icpE.k_check_block_inds.none ..)
    (cbiE_spec p hP.inds (n + 3) ⟨m, Locals.init []⟩ vis p0 isRec) (fun hG => hG.nv) id
    (cbi_ref hkp henv hV hOpf hLC hApd hCrk hLz hP.inds (n + 2) (by omega) hC hq hsrc hcx hb hA
      (fun f hf => hk f (List.mem_append_left _ (List.mem_append_right _ hf))) hshP hden hcoh hlpsDn)
    fun r1 s1 ⟨fe1, cvTas, bs1⟩ a1 c1 _ hrun1 ⟨⟨hS1, hg1, hcv1, hbs1, hsrc1⟩, hA1, hrb1, _⟩ => ?_
  rw [icpE.k_check_block_inds.arm1]
  obtain ⟨k1, ⟨env₁, cvTasP, p₁P⟩, ⟨hrel1, hOKS1, hcvs, hsh1, hT⟩, hF1⟩ :=
    ConRon.Bridge.Inductives.checkBlockInds_spec fe rfl hcs henv hcoh ⟨bs⟩ ⟨shP⟩ b a a1 _ hC.check
      ⟨hpP, hden⟩ hrun1
  dsimp only at hrel1 hOKS1 hcvs hsh1 hT hF1
  have henv₁ : ConLeche.EnvWF env₁ := by
    obtain ⟨F, hF⟩ := hF1
    rw [ConLeche.checkBlockInds_datF] at hF
    exact (ConLeche.direct_block_inds_wf henv hF).1
  have hden₁ : ConRon.Bridge.denoteFEnv a1.store fe1 = some env₁ := by
    obtain ⟨e, h, rfl⟩ := hrel1.denote; exact h
  have x01 : ConRon.Arena.Ext a.store a1.store := k1.ext
  have hP1 := PosMR.ofClosed hcl (hfs _ (by decide)) (callW_of_callE c1) hPm
  dsimp only at hS1 hcv1 hbs1 hsrc1 hA1 hrb1
  have hT1 : iwTop s1.mem < 2 ^ 64 := (rdW (s1.mem.arr64 CTL) 200).toNat_lt
  obtain ⟨-, hq9, hmemv⟩ := partsShapeFacts hbs1 hsrc1
  -- the flush
  refine RefE.bindLift (fun _ => icpE.k_flush_caches.none ..) fun r2 m2 c2 => ?_
  rw [icpE.k_flush_caches.arm1]
  obtain ⟨s2, hs2, -, hfok, hfm⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (flushCaches_spec p hP.flush (n + 3) _) (callW_mono c2 hle)
  simp only at hs2 hfok hfm
  subst hs2
  obtain ⟨hS2, hg2⟩ := flush_stage hS1 hfok
  rw [← hfm] at hS2 hg2
  have hP2 : PosMR s2.mem := by
    rw [hfm]; exact hP1.fr (MFr.of_frame (flushMem_frame s1.mem) (by simp) (by
      intro x hx; left; have := flushCtl_lt x hx; omega))
  have hA2 : AbsOK s2.mem := by rw [hfm]; exact AFr.of_frame (flushMem_frame s1.mem) (by decide) (by decide) hA1
  obtain ⟨c2', -, hst2⟩ := ConRon.Bridge.Inductives.ReadOK.flush (μ := V)
    (⟨k1.ok.state, k1.ok.pins, hOKS1 a1 rfl⟩ : ConRon.Bridge.Inductives.ReadOK env₁ fe1 a1)
    (show ConRon.Arena.flushCaches a1 = .ok ((), { a1 with caches := Caches.empty }) from rfl)
  have hC2 := StageC.of_parts hS2 c2' hA2 (dnE x01)
  refine ⟨_, _, flushCaches_run a1, ?_⟩
  generalize ha2 : ({ a1 with caches := Caches.empty } : AState) = a2 at hS2 hC2 c2' hst2 ⊢
  dsimp only
  simp only [BlockParts.complete]
  -- the constructors
  have hbs2 := hbs1.grow (decBS_mono _) hg2
  have hsrc2 := partsHsrc_grow hg2 hq9 hsrc1
  obtain ⟨hmemb, -, -, -, -, -, -⟩ := decBS_some (show decBS (truncM s2.mem) _ = _ from hbs2)
  have hq1 : (r1.tail.tail.tail.headD 0 + 1).toNat = (r1.tail.tail.tail.headD 0).toNat + 1 := by
    have h9 := hq9
    generalize r1.tail.tail.tail.headD 0 = w at h9 ⊢
    rw [UInt64.toNat_add]; simp; omega
  have hmss := bpPSl decMS_mono hmemb hsrc2 (w := r1.tail.tail.tail.headD 0)
    (w1 := r1.tail.tail.tail.headD 0 + 1) rfl hq1
  have hcv2 := hcv1.grow (fun q => OMono.decCVp q) hg2
  obtain ⟨hms1, -⟩ := ConRon.Bridge.Inductives.dShape_inv hsh1
  have x12 : ConRon.Arena.Ext a1.store a2.store := by rw [hst2]; exact ConRon.Arena.Ext.refl _
  have hsh2 := ConRon.Bridge.Inductives.dShape_ext x12 _ _ hsh1
  have hms2 := ConRon.Bridge.Inductives.dMember_ext.list x12 _ _ hms1
  have hcvs2 := ConRon.Bridge.Inductives.dExt_denoteCV.list x12 _ _ hcvs
  have hden₂ := ConRon.Bridge.denoteFEnv_mono x12 hden₁
  refine RefE.bindRunLe hle (s₀ := ⟨s2.mem, Locals.init []⟩) (fun _ => icpE.k_check_block_ctors.none ..)
    (ictE_spec p hP.ctors (n + 3) ⟨s2.mem, Locals.init []⟩ _ _ _ _ _ _ _) (fun hG => hG.nv)
    (fun hG => hG.toVerdictCtxU)
    (ict_ref hkp henv₁ hV hOpf hLC hLT hApd hCrk hP.ctors (n + 2) (by omega) s2.mem a2
      _ _ _ _ _ bs1 bs1.members cvTas hC2 hbs2 hsrc2 hmss hcv2 hA2 hsh2 hms2 hcvs2 hT c2'.ienv.toS hden₂)
    fun r3 s3 ⟨ctorsAs, sss⟩ a3 c3 _ hrun3 ⟨hC3, hg3, hca3, hss3, hcb3, hA3⟩ => ?_
  rw [icpE.k_check_block_ctors.arm1]
  obtain ⟨k3, ⟨ctorsAsP, sortsssP⟩, ⟨hca, hss⟩, hF3⟩ :=
    ConRon.Bridge.Inductives.checkBlockCtors_specF fe1 fe1 rfl hcs henv₁ bs1 p₁P env₁ bs1.members
      p₁P.members cvTas cvTasP hT a2 a3 _ c2'
      ⟨hsh2, hms2, hcvs2, hden₂, hden₂, c2'.ienv.toS⟩ hrun3
  dsimp only at hca hss hF3
  have x23 : ConRon.Arena.Ext a2.store a3.store := k3.ext
  have hS3 := hC3.stage
  have hP3 := PosMR.ofClosed hcl (hfs _ (by decide)) (callW_of_callE c3) hP2
  have hg13 := hg2.trans hg3
  -- the positivity context
  have hbs3 := hbs1.grow (decBS_mono _) hg13
  have hsrc3 := partsHsrc_grow hg13 hq9 hsrc1
  have hcv3 := hcv1.grow (fun q => OMono.decCVp q) hg13
  refine RefE.bindLift (fun _ => icpE.k_block_nest_ctx.none ..) fun r4 m4 c4 => ?_
  rw [icpE.k_block_nest_ctx.arm1]
  have d4 := callW_mono c4 hle
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (bnc_specC p hP.nck hP.nhl hP.bnc (realCall p) (realCall_spec p) (n + 1) _ _ _ _ _) d4
  obtain ⟨⟨c, holes⟩, a4, hrun4, hctx4, hho4, hhob4, hS4, hg4, hin4, hsl4, hhi4, hpn4, hA4⟩ :=
    bncC_simA (realCall p) (n + 1) hS3 hbs3 hsrc3 hcv3
      (fun _ he => Sim.mono (opfSimRA (n := n + 2) hOpf he hS3 hA3) fun _ _ _ _ h => ⟨h.1.1, h.2⟩)
      r4 s4.mem hW4
  refine ⟨_, _, hrun4, ?_⟩
  dsimp only
  have x13 : ConRon.Arena.Ext a1.store a3.store := x12.trans x23
  obtain ⟨k4, ⟨ctxP, holesP⟩, ⟨hctx, hholes, hctxOk, hhw, hpar, hlen, hnh, hnP⟩, hF4⟩ :=
    ConRon.Bridge.Inductives.blockNestCtx_spec (μ := V) fe1 henv₁ bs1 p₁P cvTas cvTasP hT a3 a4 _ k3.ok
      ⟨ConRon.Bridge.Inductives.dShape_ext x13 _ _ hsh1,
        ConRon.Bridge.Inductives.dExt_denoteCV.list x13 _ _ hcvs⟩ hrun4
  dsimp only at hctx hholes hctxOk hhw hpar hlen hnh hnP hF4
  have hparN := ConRon.Bridge.Inductives.BT.blockNestCtx_params_scoped hT hF4
  dsimp only at hparN
  have x34 : ConRon.Arena.Ext a3.store a4.store := k4.ext
  have x14 : ConRon.Arena.Ext a1.store a4.store := x13.trans x34
  obtain ⟨namesP, lpsP, paramsP, sortP, hctxEq, -, -, hparams, -, -⟩ :=
    ConRon.Bridge.Inductives.dCtx_inv hctx
  have hP4 := PosMR.ofClosed hcl (hfs _ (by decide)) d4 hP3
  have hC4 := StageC.of_parts hS4 k4.ok hA4 (dnE (x01.trans x14))
  have hg14 := hg13.trans hg4
  -- the classes
  have hT4 : iwTop s4.mem < 2 ^ 64 := (rdW (s4.mem.arr64 CTL) 200).toNat_lt
  have hbs4 := hbs1.grow (decBS_mono _) hg14
  have hsrc4 := partsHsrc_grow hg14 hq9 hsrc1
  obtain ⟨-, hq94, hmemv4⟩ := partsShapeFacts hbs4 hsrc4
  have hBS : BSOK s4.mem (r1.tail.tail.tail.headD 0).toNat bs1 :=
    ⟨hbs4, hsrc4, fun o l j v ho hl hj hv => by have := hmemv4 o l j v ho hl hj hv; omega⟩
  obtain ⟨-, hrcs, -, -, -, -, -⟩ := decBS_some (show decBS (truncM s4.mem) _ = _ from hbs4)
  obtain ⟨ro, rl, hro, hrl, hrd, hrb⟩ := partsAt decRS_mono hrcs
  have hp2 : (r1.tail.tail.tail.headD 0 + 2).toNat = (r1.tail.tail.tail.headD 0).toNat + 2 := by
    have h9 := hq94
    generalize r1.tail.tail.tail.headD 0 = w at h9 ⊢
    rw [UInt64.toNat_add]; simp; omega
  have hp3 : (r1.tail.tail.tail.headD 0 + 3).toNat = (r1.tail.tail.tail.headD 0).toNat + 2 + 1 := by
    have h9 := hq94
    generalize r1.tail.tail.tail.headD 0 = w at h9 ⊢
    rw [UInt64.toNat_add]; simp; omega
  obtain ⟨wro, -⟩ := bpWord hro hp2
  obtain ⟨wrl, -⟩ := bpWord hrl hp3
  have hRD : RecsDec s4.mem (rdW (s4.mem.arr64 IW) (r1.tail.tail.tail.headD 0 + 2))
      (rdW (s4.mem.arr64 IW) (r1.tail.tail.tail.headD 0 + 3)) bs1.recs := by
    rw [wro, wrl, UInt64.ofNat_toNat, UInt64.ofNat_toNat]
    refine ⟨hrd, ?_⟩
    rcases hrb with h0 | hb
    · subst h0; simpa using ro.toNat_lt
    · omega
  have hcdec : decCtx (truncM s4.mem) (r4.headD 0).toNat = some c := hctx4
  obtain ⟨-, -, -, -, hpar', -, -⟩ := decCtx_some hcdec
  obtain ⟨po, pl, hpo, hpl, hpd⟩ := decAt_some hpar'
  have hc10 : (r4.headD 0).toNat + 10 < iwTop s4.mem := hin4.1 10 (by omega)
  have hc7 : (r4.headD 0 + 7).toNat = (r4.headD 0).toNat + 7 := by
    have h10 := hc10
    generalize r4.headD 0 = w at h10 ⊢
    rw [UInt64.toNat_add]; simp; omega
  have hc8 : (r4.headD 0 + 8).toNat = (r4.headD 0).toNat + 7 + 1 := by
    have h10 := hc10
    generalize r4.headD 0 = w at h10 ⊢
    rw [UInt64.toNat_add]; simp; omega
  obtain ⟨wpo, hpob⟩ := bpWord hpo hc7
  obtain ⟨wpl, hplb⟩ := bpWord hpl hc8
  have hpoT : (UInt64.ofNat po : Word).toNat = po := UInt64.toNat_ofNat_of_lt' hpob
  have hplT : (UInt64.ofNat pl : Word).toNat = pl := UInt64.toNat_ofNat_of_lt' hplb
  have hpfD : DecB (fun m => (decHL m (rdW (s4.mem.arr64 IW) (r4.headD 0 + 7)).toNat
      (rdW (s4.mem.arr64 IW) (r4.headD 0 + 8)).toNat : Option (List EIdx))) s4.mem c.params := by
    rw [wpo, wpl, hpoT, hplT]; exact hpd
  have hpfb : (rdW (s4.mem.arr64 IW) (r4.headD 0 + 7)).toNat +
      (rdW (s4.mem.arr64 IW) (r4.headD 0 + 8)).toNat ≤ iwTop s4.mem := by
    rw [wpo, wpl, hpoT, hplT]
    rw [iwN_truncM (by omega)] at hpo
    rw [iwN_truncM (by omega)] at hpl
    exact hsl4 7 (by omega) po pl hpo hpl
  have hca4 := hca3.grow decCNS_mono hg4
  have hpl4 : ctxP.params.length = p₁P.nP := by rw [hlen, hnP]
  have hpfP : Frontend.denoteEList a4.store c.params = some ctxP.params := by rw [hctxEq]; exact hparams
  have hca4P := ConRon.Bridge.Inductives.dCtors_ext.list x34 _ _ hca
  have hsh4 := ConRon.Bridge.Inductives.dShape_ext x14 _ _ hsh1
  refine RefE.bindRunLe hle (s₀ := ⟨s4.mem, Locals.init []⟩) (fun _ => icpE.k_check_block_classes.none ..)
    (cbcE_spec p hP.cbc (n + 3) ⟨s4.mem, Locals.init []⟩ _ _ _ _ _ _) (fun hG => hG.nv)
    (fun hG => hG.toVerdictCtx)
    (cbc_ref hkp hIlpf hLC henv₁ hP.cbc hcl (hfs _ (by decide)) (hfs _ (by decide))
      (n + 2) (by omega) s4.mem a4 _ _ _ _ _ bs1 ctorsAs c.params hC4 hBS hsrc4 hRD hca4 hpfD hpfb hP4 hA4
      hOpf (hk _ (by simp [passKeepCalleesC, indsKeepCalleesC, posKeepCalleesC]))
      (hk _ (by simp [passKeepCalleesC, indsKeepCalleesC, posKeepCalleesC])) hpl4 hparN hsh4 hpfP hca4P)
    fun r5 s5 ⟨rd, ms⟩ a5 _ _ hrun5 ⟨hC5, hg5, hrd5, hms5, hP5, hA5, _⟩ => ?_
  rw [icpE.k_check_block_classes.arm1]
  obtain ⟨k5, ⟨rdP, msP⟩, ⟨hrdP, hmsP, hMsc⟩, hF5⟩ :=
    ConRon.Bridge.Inductives.classesStage hcs fe1 env₁ bs1 p₁P c.params ctxP.params ctorsAs ctorsAsP
      henv₁ hpl4 hparN a4 a5 _ k4.ok ⟨hsh4, hpfP, hca4P, ConRon.Bridge.denoteFEnv_mono x14 hden₁⟩ hrun5
  dsimp only at hrdP hmsP hMsc hF5
  have x45 : ConRon.Arena.Ext a4.store a5.store := k5.ext
  have x15 : ConRon.Arena.Ext a1.store a5.store := x14.trans x45
  have hg15 := hg14.trans hg5
  -- the positivity check
  have hbs5 := hbs1.grow (decBS_mono _) hg15
  have hsrc5 := partsHsrc_grow hg15 hq9 hsrc1
  have hcv5 := hcv1.grow (fun q => OMono.decCVp q) hg15
  have hcb5 := hcb3.grow decCNSB_mono (hg4.trans hg5)
  have hpP5 : ConRon.Bridge.Inductives.dParts a5.store ⟨bs1⟩ = some ⟨p₁P⟩ := by
    simp only [ConRon.Bridge.Inductives.dParts, ConRon.Bridge.Inductives.dShape_ext x15 _ _ hsh1,
      Option.map_some]
  have hcvs5 := ConRon.Bridge.Inductives.dExt_denoteCV.list x15 _ _ hcvs
  have hca5 := ConRon.Bridge.Inductives.dCtors_ext.list (x34.trans x45) _ _ hca
  have hden₅ := ConRon.Bridge.denoteFEnv_mono x15 hden₁
  have hct := ConRon.Bridge.Inductives.checkBlockCtors_types hF3
  refine RefE.bindRunLe hle (s₀ := ⟨s5.mem, Locals.init []⟩) (fun _ => icpE.k_check_block_positivity.none ..)
    (cbpE_spec p hP.pos (n + 3) ⟨s5.mem, Locals.init []⟩ _ _ _ _ _ _) (fun hG => hG.nv)
    (fun hG => ⟨hG.nv, hG.core, hG.whnf⟩)
    (cbp_ref hkp hIlpf henv₁ hOpf hLC hLT hApd hP.pos hcl (hfs _ (by decide)) n
      (by omega) hC5 hbs5 hsrc5 hcv5 hcb5 hP5 hA5 (fun f hf => hk f (List.mem_append_right _ hf))
      hpP5 hcvs5 hca5 hden₅ hT hct (P := ⟨bs1⟩))
    fun r6 s6 ⟨kinds, nfs, NS⟩ a6 _ _ hrun6 ⟨hC6, hg6, hP6, hA6, hks6, hnf6, hns6, _⟩ => ?_
  rw [icpE.k_check_block_positivity.arm1]
  obtain ⟨k6, ⟨kindsP, nfsP, posP⟩, ⟨hkinds, hnfs, hpos⟩, hF6⟩ :=
    ConRon.Bridge.Inductives.checkBlockPositivity_spec fe1 hcs henv₁ ⟨bs1⟩ ⟨p₁P⟩ cvTas cvTasP ctorsAs
      ctorsAsP hT hct a5 a6 _ k5.ok ⟨hpP5, hcvs5, hca5, hden₅⟩ hrun6
  dsimp only at hkinds hnfs hpos hF6
  have x56 : ConRon.Arena.Ext a5.store a6.store := k6.ext
  have hS6 := hC6.stage
  have hT6 : iwTop s6.mem < 2 ^ 64 := (rdW (s6.mem.arr64 CTL) 200).toNat_lt
  -- the classes' seeds
  have hU4 : UCtx dn (r1.headD 0) fe1 s4.mem (r4.headD 0) c :=
    ⟨hctx4.get (decCtx_mono _), hin4, hsl4⟩
  have hg46 := hg5.trans hg6
  have hU6 := hU4.grow hg46
  have hho6 : (decHL s6.mem (r4.tail.headD 0).toNat (r4.tail.tail.headD 0).toNat : Option (List EIdx)) =
      some holes := by rw [decHL_grow3 hg46 hhob4]; exact hho4
  have hms6 := hms5.grow (fun q => decTM_mono q) hg6
  refine RefE.bindLift (fun _ => icpE.k_class_seeds.none ..) fun r7 m7 c7 => ?_
  rw [icpE.k_class_seeds.arm1]
  have d7 := callW_mono c7 hle
  obtain ⟨s7, hs7, -, hok7, hS7, hg7, hsd7, hP7⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (classSeeds_refines hP.sds (n + 3) _ a6 dn (r1.headD 0) fe1 _ _ _ _ _ c holes ms hS6 hU6 hhi4 hho6
      (Nat.le_trans hhob4 hg46.iw) hms6 hP6) d7
  simp only at hs7 hS7 hg7 hsd7 hP7
  subst hs7
  have hA7 : AbsOK s7.mem := hk _ (by simp [passKeepCalleesC, indsKeepCalleesC, posKeepCalleesC]) _ _ _ _ _ d7 hA6
  refine ⟨_, _, AM.run_of_ok _ a6 hok7, ?_⟩
  have hrun7 := AM.run_of_ok _ a6 hok7
  generalize AM.res (ConRon.Arena.classSeeds c holes ms) a6 = seeds at hrun7 hsd7 ⊢
  generalize AM.st (ConRon.Arena.classSeeds c holes ms) a6 = a7 at hrun7 hS7 ⊢
  dsimp only
  have x46 : ConRon.Arena.Ext a4.store a6.store := x45.trans x56
  obtain ⟨p7, hseeds⟩ := ConRon.Bridge.Inductives.seedsStage c ctxP holes holesP ms msP env₁.find? a6 a7
    seeds k6.ok.state k6.ok.pins
    ⟨ConRon.Bridge.Inductives.dCtx_ext _ x46 _ _ hctx, ConRon.Bridge.denoteEList_ext x46 _ _ hholes,
      ConRon.Bridge.Inductives.dMajor_ext.list x56 _ _ hmsP⟩ hrun7
  have k7 := p7.toCore k6.ok
  have x67 : ConRon.Arena.Ext a6.store a7.store := k7.ext
  have hC7 := StageC.of_parts hS7 k7.ok hA7 (dnE (x01.trans (x14.trans (x46.trans x67))))
  -- the nested seeds
  have hU7 := hU6.grow hg7
  have hns7 := hns6.grow hg7 hT6
  have hdrop : (r6.drop 4).headD 0 = r6.tail.tail.tail.tail.headD 0 := by
    rcases r6 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl
  rw [hdrop] at hns7
  refine RefE.bindRun (s₀ := ⟨s7.mem, Locals.init []⟩) (fun _ => icpE.k_nest_seeds.none ..)
    (nsdE_spec p hP.rs F ⟨s7.mem, Locals.init []⟩ _ _ _ _ _) (fun hG => hG.nv)
    (fun hG => ⟨hG.nv, hG.core, hG.whnf⟩)
    (nsd_ref hP.rs hkp hIlpf hLC dn (r1.headD 0) fe1 henv₁ _ c hctxOk F
      (by omega) s7.mem a7 _ _ _ seeds NS _ _ hC7 hU7 hhi4 hsd7.2.1 hsd7.2.2.2 hns7 hP7 hA7
      (ConRon.Bridge.Inductives.dCtx_ext _ (x46.trans x67) _ _ hctx) hseeds
      (ConRon.Bridge.Inductives.dState_ext x67 _ _ hpos)
      (fun k hk x hx => by
        obtain ⟨M, hM, hMn, rfl⟩ := ConLeche.Cached.mem_classSeeds hk
        exact (ConLeche.nestSeedOf_ds hnh hlen (fun y hy => ConLeche.Expr.fvarB_le (by
          rw [hnP]; exact (((hMsc M hM).2.1 hMn).2 y hy).2)) x hx).2 (fun y hy => (hhw y hy).1) hpar))
    fun r8 s8 ns a8 _ _ hrun8 ⟨hC8, hg8, hns8, hP8, hA8, _⟩ => ?_
  rw [icpE.k_nest_seeds.arm1]
  have hS8 := hC8.stage
  have hT8 : iwTop s8.mem < 2 ^ 64 := (rdW (s8.mem.arr64 CTL) 200).toNat_lt
  obtain ⟨-, -, -, hnfsB⟩ := nsb_words hns8 hT8
  have htbl8 : PSlR decNCN ns.ctorNfs.toList (rdW (s8.mem.arr64 IW) (r8.headD 0 + 4))
      (rdW (s8.mem.arr64 IW) (r8.headD 0 + 5)) s8.mem := ⟨hnfsB, hns8.b4⟩
  have hg48 := (hg5.trans hg6).trans (hg7.trans hg8)
  have hw7 : rdW (s8.mem.arr64 IW) (r4.headD 0 + 7) = rdW (s4.mem.arr64 IW) (r4.headD 0 + 7) :=
    partsRdIW_grow hg48 (by rw [hc7]; omega)
  have hw8 : rdW (s8.mem.arr64 IW) (r4.headD 0 + 8) = rdW (s4.mem.arr64 IW) (r4.headD 0 + 8) :=
    partsRdIW_grow hg48 (by rw [hc8]; omega)
  -- the record (L only)
  refine RefE.onlySim (fun _ => icpE.k_check_block_pass_rec.none ..) (fun _ _ h => h) fun r9 m9 c9 => ?_
  rw [icpE.k_check_block_pass_rec.arm1]
  have d9 := callW_mono c9 hle
  have hA9 : AbsOK m9 := hk _ (by simp [passKeepCalleesC, indsKeepCalleesC, posKeepCalleesC]) _ _ _ _ _ d9 hA8
  obtain ⟨s9, hs9, -, hW9⟩ := triple_of_callW (s₀ := ⟨s8.mem, Locals.init []⟩)
    (icpr_spec p hP.prec (n + 2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) d9
  simp only at hs9 hW9
  subst hs9
  obtain ⟨q, hr9, hS9, hg9, hP9, hqt, hq19, hget⟩ := icprW_ok hP.ha hW9 hS8 hP8
  subst hr9
  have hg29 := hg3.trans (hg4.trans (hg5.trans (hg6.trans (hg7.trans (hg8.trans hg9)))))
  have hw0 : rdW (s9.mem.arr64 IW) q = r1.headD 0 := by
    have := hget 0 (by omega)
    simp only [Nat.add_zero, List.getElem?_cons_zero] at this
    simp only [rdW, this]; rfl
  have hBP := bpRec_bpassR (fe := fe1) hget hq19
    (hcv1.grow (fun q => OMono.decCVp q) (hg2.trans hg29)) (hbs1.grow (decBS_mono _) (hg2.trans hg29))
    (partsHsrc_grow (hg2.trans hg29) hq9 hsrc1)
    (hca3.grow decCNS_mono (hg4.trans (hg5.trans (hg6.trans (hg7.trans (hg8.trans hg9))))))
    (hss3.grow decISS_mono (hg4.trans (hg5.trans (hg6.trans (hg7.trans (hg8.trans hg9))))))
    (hks6.grow decKSS_mono (hg7.trans (hg8.trans hg9)))
    (hnf6.grow decNFS_mono (hg7.trans (hg8.trans hg9)))
    (by rw [hw7, hw8]; exact hpfD.grow (OMono.decHL _ _) (hg48.trans hg9))
    (by rw [hw7, hw8]; exact Nat.le_trans hpfb (hg48.trans hg9).iw)
    (hrd5.grow (decCR_mono _) (hg6.trans (hg7.trans (hg8.trans hg9))))
    (hms6.grow (fun q => decTM_mono q) (hg7.trans (hg8.trans hg9)))
    (htbl8.grow (fun q => decNCN_mono q) hg9)
  have hT9 : iwTop s9.mem < 2 ^ 64 := (rdW (s9.mem.arr64 CTL) 200).toNat_lt
  have hrw : ∀ j (hj : j < 19), rdW (s9.mem.arr64 IW) (q + UInt64.ofNat j) =
      [r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0, r1.tail.tail.tail.headD 0, r3.headD 0,
        r3.tail.headD 0, r3.tail.tail.headD 0, r3.tail.tail.tail.headD 0, r6.headD 0, r6.tail.headD 0,
        r6.tail.tail.headD 0, r6.tail.tail.tail.headD 0, rdW (s8.mem.arr64 IW) (r4.headD 0 + 7),
        rdW (s8.mem.arr64 IW) (r4.headD 0 + 8), r5.headD 0, r5.tail.headD 0, r5.tail.tail.headD 0,
        rdW (s8.mem.arr64 IW) (r8.headD 0 + 4), rdW (s8.mem.arr64 IW) (r8.headD 0 + 5)][j]'(by simpa using hj) := by
    intro j hj
    have e := hget j hj
    have hqj : (q + UInt64.ofNat j).toNat = q.toNat + j := tailToNat (by omega)
    rw [List.getElem?_eq_getElem (by simpa using hj)] at e
    simp only [rdW, hqj, e]; rfl
  have hr3 : rdW (s9.mem.arr64 IW) (q + 3) = r1.tail.tail.tail.headD 0 := hrw 3 (by omega)
  have hr15 : rdW (s9.mem.arr64 IW) (q + 15) = r5.tail.headD 0 := hrw 15 (by omega)
  have hr16 : rdW (s9.mem.arr64 IW) (q + 16) = r5.tail.tail.headD 0 := hrw 16 (by omega)
  have hms9 := hms6.grow (fun q => decTM_mono q) (hg7.trans (hg8.trans hg9))
  -- the whole run, and con-ron's `checkBlockPass_of` on it
  have hrunP : (ConRon.Arena.checkBlockPass V fe ⟨bs⟩ b).run a = .ok (⟨fe1, cvTas, ⟨bs1⟩, ctorsAs, sss,
      kinds, nfs, c.params, rd, ms, ns.ctorNfs.toList⟩, a8) := by
    rw [← ha2] at hrun3
    simp only [ConRon.Arena.checkBlockPass, StateT.run_bind, hrun1, except_ok_bind, BlockParts.complete,
      flushCaches_run, hrun3, hrun4, hrun5, hrun6, hrun7, hrun8]
    rfl
  obtain ⟨env₁', qP, i9, ck9, hrel9, henv₁', hq9P, hT9P, henv₂, hMs9, -⟩ :=
    ConRon.Bridge.Inductives.checkBlockPass_of (μ := V) rfl hcs (ConRon.Bridge.Inductives.classesStage hcs)
      ConRon.Bridge.Inductives.seedsStage henv hC.check hcoh hden hpP hrunP
  obtain ⟨e9, hden9, rfl⟩ := hrel9.denote
  refine RefE.ret (y := ⟨fe1, cvTas, ⟨bs1⟩, ctorsAs, sss, kinds, nfs, c.params, rd, ms, ns.ctorNfs.toList⟩)
    (a' := a8) rfl ⟨?_, hg1.trans (hg2.trans hg29), ?_, hP9, hA9, fun hrb => ?_, ?_, e9, ?_, qP, i9,
      hrel9.coh, hden9, henv₁', hq9P, hT9P, henv₂, hMs9⟩
  · simp only [List.headD_cons]; rw [hw0]; exact hS9
  · simp only [List.headD_cons]; rw [hw0]; exact hBP
  · simp only [List.headD_cons]; rw [hr3]
    exact (hrb1 hrb).grow (hg2.trans hg29) (by omega)
  · simp only [List.headD_cons]; rw [hr15, hr16]
    exact classesLp_of_decPL hms9.1 hS9.iw.er hS9.iw.iwSize
  · simp only [List.headD_cons]; rw [hw0]
    exact StageC.of_parts hS9 ck9 hA9 (dnE i9.ext)

include hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz in
/-- **`check_block_pass(vis, p0, isRec)` refines `checkBlockPass` under `StageC`**
(`checkBlockPass_refines`'s, from `StageC` at the entry index and con-ron's `checkBlockPass_of`
preconditions): besides `checkBlockPass_refines`' post, `StageC` at the formers' index and
environment `env₁` and what the tail takes of the pass (`PassTwin`). -/
@[refines ConRon.Arena.checkBlockPass]
theorem checkBlockPass_refinesC (hP : PassProg p) {fs : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs) (n : Nat)
    (hn : n + 4 ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {p0 isRec : Word} {bs : BlockShape} {b : Bool}
    (hC : StageC dn vis fe env s₀.mem a₀) (hq : DecB (fun m => decBS m p0.toNat) s₀.mem bs)
    (hsrc : ShapeSrc s₀.mem p0) (hcx : ShapeCV s₀.mem p0) (hb : (isRec != 0) = b)
    (hPm : PosMR s₀.mem) (hA : AbsOK s₀.mem) (hk : ∀ f ∈ passKeepCalleesC, AbsKeep p f)
    (hcoh : ConRon.Bridge.IFEnvCoh fe) (hden : ConRon.Bridge.denoteFEnv a₀.store fe = some env)
    {shP : ConLeche.BlockShape} (hshP : ConRon.Bridge.Inductives.dShape a₀.store bs = some shP)
    (hlpsDn : ∀ ms ∈ bs.members, ∀ k ∈ ms.cvT.levelParams, (dn k).isSome) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 4)) "check_block_pass" [vis, p0, isRec]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ x a', (ConRon.Arena.checkBlockPass V fe ⟨bs⟩ b).run a₀ = .ok (x, a') ∧
      (StageR dn (rdW (s'.mem.arr64 IW) (r.headD 0)) x.env1 s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧
      BPassR (rdW (s'.mem.arr64 IW) (r.headD 0)) x.env1 s'.mem (r.headD 0) x ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧
      (RecsB s₀.mem p0 → RecsB s'.mem (rdW (s'.mem.arr64 IW) (r.headD 0 + 3))) ∧
      ClassesLp s'.mem (rdW (s'.mem.arr64 IW) (r.headD 0 + 15)) (rdW (s'.mem.arr64 IW) (r.headD 0 + 16))) ∧
      ∃ env₁, StageC dn (rdW (s'.mem.arr64 IW) (r.headD 0)) x.env1 env₁ s'.mem a' ∧ PassTwin a₀ a' x env₁;
      ⊤⦄ := by
  refine triple_post (RefE.triple (icpE_spec p hP (n + 4) s₀ vis p0 isRec)
    (pass_ref hkp henv hV hOpf hLC hLT hApd hCrk hIlpf hLz hP hcl hfs (n + 4) hn hC hq hsrc hcx hb hPm hA hk
      hcoh hden hshP hlpsDn)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  exact ⟨hl, x, a', run, ⟨hR.stage, hR.grow, hR.bpass, hR.pos, hR.abs, hR.recs, hR.classes⟩, hR.twin⟩

end sims

end L.Ind

end
