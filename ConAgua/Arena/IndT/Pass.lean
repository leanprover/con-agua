module

public import ConAgua.Arena.IndT.BlockC
public import ConAgua.Arena.IndPosSpec.UCtx
public import ConAgua.Arena.RecGenSpec.DecNLAt
public import ConAgua.Arena.IndInstallSpec.IndsOut
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.IndPosSpec.CfW
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Arena.IndPosSpec.NestKeyMap
import ConAgua.Arena.IndInstallSpec.PnfW
import ConAgua.Arena.RecGenSpec.FlushStage
import ConAgua.Arena.ScratchRefine
import Std.WP.Tactic
import ConRon.Bridge.Inductives.BlockInstall
import ConRon.Bridge.Inductives.GenRec
import ConRon.Bridge.Inductives.Positivity
import ConRon.Bridge.Inductives.BlockTail
import ConRon.Bridge.Inductives.PosWalks
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndInstall

@[expose] public section

/-!
# `check_block_pass`'s composition from its callees' contracts (lane `ronsync2`, stage 3)

`check_block_pass(vis, p0, isRec)` (`IndInstall.lean`) calls, in order: `check_block_inds`,
`flush_caches`, `check_block_ctors`, `block_nest_ctx`, `check_block_classes`,
`check_block_positivity`, `class_seeds`, `nest_seeds`, `nest_out_kinds`, `check_block_pass_rec`.
Its unified model `icpE` reads every callee through its call (`callE`); each callee with a twin
step has a **contract at the call** here (`…RefS`, the style of `IndT/BlockC`), bundled as
`PassRefs`; the flush (`flushRefR`), `nest_out_kinds` (the identity) and the record
(`icprW_ok`) are proved here. `pass_ref` walks the model against `checkBlockPass` with con-ron's
lemmas between the steps (as `checkBlockPass_of`'s proof does: the callees' preconditions), its post
the memory's facts (`PassMem`); `passRefS_of` applies con-ron's `checkBlockPass_of` to the whole run
for `PassOut`'s twin facts.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups `check_block_pass`' composition reads itself. -/
structure PassLook (p : Prog) : Prop where
  pass : p.lookup "check_block_pass" = some L.Ind.checkBlockPass
  prec : p.lookup "check_block_pass_rec" = some L.Ind.checkBlockPassRec
  nok : p.lookup "nest_out_kinds" = some L.Ind.nestOutKinds
  ha : p.lookup "iw_alloc" = some iwAlloc
  flush : FlushProg p

set_option experimental.vcgen true in
/-- **`check_block_pass`' unified model**: every callee through its call. -/
l_model icpE_spec (p : Prog) (hP : PassLook p)
  fns [hP.pass ↦ icpE]
  specs []
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- `nest_out_kinds(o, l)` returns `(o, l)` and writes nothing. -/
theorem nok_spec (p : Prog) (hp : p.lookup "nest_out_kinds" = some L.Ind.nestOutKinds) (n : Nat)
    (s₀ : St) (o l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "nest_out_kinds" [o, l]
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = [o, l]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, L.Ind.nestOutKinds]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;> finish

/-! ## The state the steps carry -/

/-- **`StageC` at another view and environment** (a local copy of `IndT/GenRec1`'s
`StageC.of_checkE`): the stage relation there, `CheckOK` there, the memory's half from `AbsOK` and
the store's extension. -/
theorem StageC.ofView {dn : NIdx → Option ConLeche.Name} {vis vis' : Word} {fe fe' : IFEnv}
    {env env' : ConLeche.Env} {m m' : Mem} {a a' : AState} (h : StageC dn vis fe env m a)
    (hS : StageR vis' fe' m' a') (hA : AbsOK m') (hck : ConRon.Bridge.CheckOK false env' fe' a')
    (hx : ConRon.Arena.Ext a.store a'.store) : StageC dn vis' fe' env' m' a' :=
  ⟨hS, hck,
    ⟨hA.wk.2.1, hA.wk.2.2.1, hA.wk.2.2.2.1, hA.coreMemos,
      fun k x e => hx.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    hA.wk.2.2.2.2⟩

/-- What `check_block_pass` gives the memory (from `m`; the record at `w`): the stage at the
record's view (word `0`), the memos, `AbsOK`, the growth, the record decoded, the shape's (word `1`)
slices below the top (`ShapeSl`). -/
structure PassMem (m : Mem) (w : Word) (q : BlockPass) (m' : Mem) (a' : AState) : Prop where
  stage : StageR (rdW (m'.arr64 IW) w) q.env1 m' a'
  ind : IndMemos m'
  abs : AbsOK m'
  grow : IWGrow m m'
  record : BPassR (rdW (m'.arr64 IW) w) q.env1 m' w q
  shape : ShapeSl m' (rdW (m'.arr64 IW) (w + 1))

/-! ## The callees' contracts -/

section contracts
variable (G : Prop) (p : Prog) (dn : NIdx → Option ConLeche.Name)

/-- **`check_block_inds(vis, p, isRec)`'s contract**: `checkBlockInds`, both outcomes, from `BkSt`
and con-ron's `checkBlockInds_spec` preconditions; the formers' environment at the returned view
(`IndsOut`), the memos, `AbsOK`, the new shape's slices. (Its proof: `IndT/Install4`'s `cbi_ref`.) -/
def IndsRefS : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState)
    (pp isRec : Word) (bs : BlockShape) (bsP : ConLeche.BlockShape) (b : Bool),
    BkSt dn vis fe env m a → ConLeche.EnvWF env →
    DecB (fun m => decBS m pp.toNat) m bs → ShapeSl m pp →
    ConRon.Bridge.Inductives.dShape a.store bs = some bsP → (isRec != 0) = b →
    RefE G (callE p n "check_block_inds" [vis, pp, isRec] m) (ConRon.Arena.checkBlockInds V fe bs b) a
      (fun rm x a' => IndsOut m rm.1 x rm.2 a' ∧ IndMemos rm.2 ∧ AbsOK rm.2 ∧
        ShapeSl rm.2 (rm.1.tail.headD 0))

/-- **`check_block_ctors(vis, vis, p, ms.off, ms.len)`'s contract** (the members' slice the shape's
words `0, 1`): `checkBlockCtors` at one environment, both outcomes, from `BkSt` and con-ron's
`checkBlockCtors_specF` preconditions. (Its proof: `IndT/Install7`'s `ict_ref`.) -/
def CtorsRefS : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (vis : Word) (fe : IFEnv) (env env₀ : ConLeche.Env) (m : Mem)
    (a : AState) (pp : Word) (bs : BlockShape) (bsP : ConLeche.BlockShape),
    BkSt dn vis fe env m a → ConLeche.EnvWF env → DecB (fun m => decBS m pp.toNat) m bs → ShapeSl m pp →
    ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    (∀ ms ∈ bsP.members, ConLeche.Expr.WScoped 0 ms.cvT.type) →
    ConRon.Bridge.Inductives.IFEnvOKS env₀ fe a.store →
    RefE G (callE p n "check_block_ctors"
        [vis, vis, pp, rdW (m.arr64 IW) pp, rdW (m.arr64 IW) (pp + 1)] m)
      (ConRon.Arena.checkBlockCtors V fe fe bs bs.members) a
      (fun rm _ a' => BkSt dn vis fe env rm.2 a' ∧ IWGrow m rm.2)

/-- **`block_nest_ctx(p)`'s contract**: `blockNestCtx`, from `BkSt` and con-ron's
`blockNestCtx_spec` preconditions; the context record (`UCtx`, decoded below the tops) and the
holes' slice. -/
def BncRefS : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState)
    (pp : Word) (bs : BlockShape) (bsP : ConLeche.BlockShape),
    BkSt dn vis fe env m a → ConLeche.EnvWF env → DecB (fun m => decBS m pp.toNat) m bs → ShapeSl m pp →
    ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    (∀ cv ∈ bsP.formers, ConLeche.Expr.WScoped 0 cv.type) →
    RefE G (callE p n "block_nest_ctx" [pp] m) (ConRon.Arena.blockNestCtx bs) a
      (fun rm x a' => BkSt dn vis fe env rm.2 a' ∧ IWGrow m rm.2 ∧
        DecB (fun m => decCtx m (rm.1.headD 0).toNat) rm.2 x.1 ∧
        UCtx dn vis fe rm.2 (rm.1.headD 0) x.1 ∧
        (decHL rm.2 (rm.1.tail.headD 0).toNat (rm.1.tail.tail.headD 0).toNat : Option (List EIdx)) =
          some x.2 ∧
        (rm.1.tail.headD 0).toNat + (rm.1.tail.tail.headD 0).toNat ≤ iwTop rm.2 ∧
        x.1.hiAt 0 < 2 ^ 64 ∧ x.1.params.length + x.1.names.length < 2 ^ 64)

/-- **`check_block_classes(vis, p, params.off, params.len)`'s contract**: `checkBlockClasses`,
both outcomes, from `BkSt` and con-ron's `checkBlockClasses_spec` preconditions; the class read
and the majors' slice. -/
def ClsRefS : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState)
    (pp po pl : Word) (bs : BlockShape) (bsP : ConLeche.BlockShape) (params : List EIdx)
    (paramsP : List ConLeche.Expr),
    BkSt dn vis fe env m a → ConLeche.EnvWF env → DecB (fun m => decBS m pp.toNat) m bs →
    ShapeSl m pp →
    DecB (fun m => (decHL m po.toNat pl.toNat : Option (List EIdx))) m params →
    po.toNat + pl.toNat ≤ iwTop m →
    ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    Frontend.denoteEList a.store params = some paramsP → paramsP.length = bsP.nP →
    (∀ x ∈ paramsP, ConLeche.Expr.WScoped bsP.nP x) →
    RefE G (callE p n "check_block_classes" [vis, pp, po, pl] m)
      (ConRon.Arena.checkBlockClasses V fe bs params) a
      (fun rm x a' => BkSt dn vis fe env rm.2 a' ∧ IWGrow m rm.2 ∧
        DecB (fun m => decCR m (rm.1.headD 0).toNat) rm.2 x.1 ∧
        PSlR decTM x.2 (rm.1.tail.headD 0) (rm.1.tail.tail.headD 0) rm.2)

/-- **`check_block_positivity(vis, p)`'s contract**: `checkBlockPositivity`, both outcomes, from
`BkSt` and con-ron's `checkBlockPositivity_spec` preconditions; the outputs' slice read as their
kinds (`nest_out_kinds` is the identity on it) and the walk's state record. -/
def PosRefS : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState)
    (pp : Word) (bs : BlockShape) (bsP : ConLeche.BlockShape),
    BkSt dn vis fe env m a → ConLeche.EnvWF env → DecB (fun m => decBS m pp.toNat) m bs →
    ShapeSl m pp → ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    (∀ cv ∈ bsP.formers, ConLeche.Expr.WScoped 0 cv.type) →
    (∀ cs ∈ bsP.memberCtors, ∀ c ∈ cs, ConLeche.Expr.WScoped 0 c.1.type) →
    RefE G (callE p n "check_block_positivity" [vis, pp] m)
      (ConRon.Arena.checkBlockPositivity V fe bs) a
      (fun rm x a' => BkSt dn vis fe env rm.2 a' ∧ IWGrow m rm.2 ∧
        PSlR decKSS (ConRon.Arena.nestOutKinds x.1) (rm.1.headD 0) (rm.1.tail.headD 0) rm.2 ∧
        NSB rm.2 (rm.1.tail.tail.headD 0) x.2)

/-- **`class_seeds(ctx, holes.off, holes.len, ms.off, ms.len)`'s contract**: `classSeeds`, from
`BkSt`, the context, the holes and the majors; the stage (its `CheckOK` the composition's, by
con-ron's `classSeeds_spec`), the memos, the seeds' slice (`SdRes`). -/
def SeedsRefS : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState)
    (ctx hO hL mo ml : Word) (c : NestCtx) (holes : List EIdx) (ms : List TargetMajor),
    BkSt dn vis fe env m a → UCtx dn vis fe m ctx c → c.hiAt 0 < 2 ^ 64 →
    (decHL m hO.toNat hL.toNat : Option (List EIdx)) = some holes →
    hO.toNat + hL.toNat ≤ iwTop m → PSlR decTM ms mo ml m →
    RefE G (callE p n "class_seeds" [ctx, hO, hL, mo, ml] m) (ConRon.Arena.classSeeds c holes ms) a
      (fun rm x a' => StageR vis fe rm.2 a' ∧ IndMemos rm.2 ∧ AbsOK rm.2 ∧ IWGrow m rm.2 ∧
        SdRes rm.2 (rm.1.headD 0) (rm.1.tail.headD 0) x)

/-- **`nest_seeds(vis, ctx, seeds.off, seeds.len, ns)`'s contract**: `nestSeeds`, both outcomes,
from `BkSt` and con-ron's `nestSeeds_spec` preconditions; the walk's state record after. (Its
proof: the verdict area's `nsd_ref`, `Verdict/PosTopE4`.) -/
def NsdRefS : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState)
    (ctx so sl nsw : Word) (c : NestCtx) (ctxP : ConLeche.NestCtx) (seeds : List (NestKey × Nat))
    (ksP : List (ConLeche.NestKey × Nat)) (ns : NestState) (nsP : ConLeche.NestState),
    BkSt dn vis fe env m a → ConLeche.EnvWF env → UCtx dn vis fe m ctx c → c.hiAt 0 < 2 ^ 64 →
    SdRes m so sl seeds → NSB m nsw ns →
    ConRon.Bridge.Inductives.dCtx a.store env.find? c = some ctxP → ConLeche.NestCtxOk ctxP →
    seeds.mapM (ConRon.Bridge.Inductives.dSeed a.store) = some ksP →
    ConRon.Bridge.Inductives.dState a.store ns = some nsP →
    (∀ k ∈ ksP, ∀ x ∈ k.1.ds, ConLeche.Expr.WScoped (ctxP.hiAt 0) x) →
    RefE G (callE p n "nest_seeds" [vis, ctx, so, sl, nsw] m) (ConRon.Arena.nestSeeds V fe c seeds ns) a
      (fun rm x a' => BkSt dn vis fe env rm.2 a' ∧ IWGrow m rm.2 ∧ NSB rm.2 (rm.1.headD 0) x)

end contracts

/-- **`check_block_pass`'s callees' contracts.** -/
structure PassRefs (G : Prop) (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop where
  look : PassLook p
  inds : IndsRefS G p dn
  ctors : CtorsRefS G p dn
  bnc : BncRefS G p dn
  cls : ClsRefS G p dn
  pos : PosRefS G p dn
  seeds : SeedsRefS G p dn
  nsd : NsdRefS G p dn

/-! ## The composition -/

section comp
variable {G : Prop} {p : Prog} {dn : NIdx → Option ConLeche.Name}

/-- **`flush_caches()` at a view whose `CheckOK` holds for reads only** (`ReadOK`: after
`check_block_inds`, the caches still the entry index's): `BkGo` after it (con-ron's
`ReadOK.flush`), `StageC` rebuilt from an earlier one (`StageC.ofView`). -/
theorem flushRefR (hF : FlushProg p) (hGnv : G → closedNV p _root_.L.Checker.nvFns = true)
    {n : Nat} {vis vis₀ : Word} {fe fe₀ : IFEnv} {env env₀ : ConLeche.Env} {m m₀ : Mem}
    {a a₀ : AState} (h0 : StageC dn vis₀ fe₀ env₀ m₀ a₀) (hx : ConRon.Arena.Ext a₀.store a.store)
    (hS : StageR vis fe m a) (hI : IndMemos m) (hA : AbsOK m)
    (hR : ConRon.Bridge.Inductives.ReadOK env fe a) :
    RefE G (callE p n "flush_caches" [] m) ConRon.Arena.flushCaches a
      (fun rm _ a' => BkGo dn vis fe env m a rm.2 a') := by
  rcases c : callE p n "flush_caches" [] m with e | ⟨r, m'⟩
  · exact fun hG => ErrClaim.of_callE_nv (hGnv hG) (_root_.L.Checker.nv_mem (by decide +kernel)) c
  obtain ⟨s', rfl, -, hfok, hfm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (flushCaches_spec p hF n _) (callW_of_callE c)
  simp only at hfok hfm
  obtain ⟨cf, i1, -⟩ := ConRon.Bridge.Inductives.ReadOK.flush hR
    (show ConRon.Arena.flushCaches a = .ok ((), { a with caches := Caches.empty }) from rfl)
  obtain ⟨hS', hg⟩ := flush_stage hS hfok
  rw [← hfm] at hS' hg
  have hA' : AbsOK s'.mem := by
    rw [hfm]; exact AFr.of_frame (flushMem_frame m) (by decide) (by decide) hA
  have hI' : IndMemos s'.mem := by
    rw [hfm]
    exact hI.frame (flushMem_frame m) (by simp) (fun x hx => by
      have := flushCtl_lt x hx; have := flushCtl_ge x hx; omega)
  exact ⟨(), _, rfl, ⟨StageC.ofView h0 hS' hA' cf hx, hI', hA'⟩, hg, i1⟩

/-- **`nest_out_kinds`' call returns its arguments and writes nothing.** -/
theorem nok_callE (hp : p.lookup "nest_out_kinds" = some L.Ind.nestOutKinds) {n : Nat} {o l : Word}
    {m m' : Mem} {r : List Word} (h : callE p n "nest_out_kinds" [o, l] m = .ok (r, m')) :
    r = [o, l] ∧ m' = m := by
  rcases n with _ | n
  · obtain ⟨e, he, -⟩ := L.callE_zero p "nest_out_kinds" [o, l] m
    rw [he] at h; cases h
  obtain ⟨s', hs', hm, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (nok_spec p hp n _ o l)
    (callW_of_callE h)
  exact ⟨hr, hs' ▸ hm⟩

/-- **`check_block_pass_rec` writes only `IW` and the top** (`icprW_ok`'s frame). -/
theorem icprW_frame {p : Prog} (ha : p.lookup "iw_alloc" = some iwAlloc) {n : Nat}
    {vis : Word} {fe : IFEnv} {a : AState} {m m' : Mem}
    {r : List Word} {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : Word}
    (h : icprW p n m w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 = some (r, m'))
    (hS : StageR vis fe m a) : MemFrame [IW] [200] m m' := by
  unfold icprW at h
  rcases c1 : callW p n "iw_alloc" [11] m with _ | ⟨rq, m1⟩
  · rw [c1] at h; cases h
  rw [c1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s1, hs1, -, hal⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (iwAlloc_specW p ha n _ 11) c1
  simp only at hs1 hal
  subst hs1
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hS.iw.iwSize
  have hc : 200 < (m.arr64 CTL).size := hS.iw.ctl
  rw [bpMem_eq, hm1, hq]
  have hk : (11 : Word).toNat = [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10].length := rfl
  exact (recMem_post m [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10] 11 hk hc
    (by rw [← hq]; simpa using hroom) hS.iw.iwSize).2.2.1

/-- **`check_block_pass_rec`'s call**: `icprW_ok` and its frame. -/
theorem icpr_callE {p : Prog} (hp : p.lookup "check_block_pass_rec" = some L.Ind.checkBlockPassRec)
    (ha : p.lookup "iw_alloc" = some iwAlloc) {n : Nat} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {r : List Word} {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : Word}
    (h : callE p n "check_block_pass_rec" [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10] m = .ok (r, m'))
    (hS : StageR vis fe m a) (hP : PosMR m) :
    ∃ q : Word, r = [q] ∧ StageR vis fe m' a ∧ IWGrow m m' ∧ q.toNat + 11 ≤ iwTop m' ∧
      (∀ j (_hj : j < 11), (m'.arr64 IW)[q.toNat + j]? =
        [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10][j]?) ∧ MemFrame [IW] [200] m m' := by
  rcases n with _ | n
  · obtain ⟨e, he, -⟩ := L.callE_zero p "check_block_pass_rec" [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10] m
    rw [he] at h; cases h
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (icpr_spec p hp n _ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10) (callW_of_callE h)
  simp only at hW
  subst hs'
  obtain ⟨q, hr, hS', hg, -, -, hq, hget⟩ := icprW_ok ha hW hS hP
  exact ⟨q, hr, hS', hg, hq, hget, icprW_frame ha hW hS⟩

/-- **`check_block_pass`'s model refines `checkBlockPass`, both outcomes**, from its callees'
contracts: the twin's facts between the calls by con-ron's lemmas (`checkBlockPass_of`'s proof:
each callee's preconditions), the memory's by the contracts' posts; the post the memory's facts
(`PassMem`). -/
theorem pass_ref (R : PassRefs G p dn) (hGnv : G → closedNV p _root_.L.Checker.nvFns = true)
    {N : Nat} {vis p1 isRec : Word} {fe : IFEnv} {env : ConLeche.Env} {m : Mem} {a : AState}
    {bs : BlockShape} {bsP : ConLeche.BlockShape} {b : Bool}
    (hB : BkSt dn vis fe env m a) (henv : ConLeche.EnvWF env)
    (hrel : ConRon.Bridge.Inductives.EnvRel env fe a.store)
    (hq : DecB (fun m => decBS m p1.toNat) m bs) (hsl : ShapeSl m p1)
    (hdP : ConRon.Bridge.Inductives.dShape a.store bs = some bsP)
    (hdecl : ∀ ms ∈ bsP.members, ConLeche.MemberDeclaredWF env ms) (hb : (isRec != 0) = b)
    (hN : N ≤ 2 ^ 62) :
    RefE G (icpE p N m vis p1 isRec) (ConRon.Arena.checkBlockPass V fe bs b) a
      (fun v q a' => PassMem m v.1 q v.2 a') := by
  rcases N with _ | n
  · rw [icpE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  rw [icpE.arm1]
  unfold ConRon.Arena.checkBlockPass
  have hk : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel := ConRon.Bridge.CoreSpec.of_core
  -- the formers
  refine RefE.bindE (fun _ => icpE.k_check_block_inds.none ..) id
    (R.inds n (by omega) vis fe env m a p1 isRec bs bsP b hB henv hq hsl hdP hb)
    fun ⟨r1, m1⟩ ⟨fe1, bs1⟩ a1 hrun1 h1 => ?_
  obtain ⟨⟨hS1, hg1, hq1, -⟩, hI1, hA1, hsl1⟩ := h1
  rw [icpE.k_check_block_inds.arm1]
  obtain ⟨c1, ⟨env₁, p₁P⟩, ⟨hrel1, hsh1⟩, hF1⟩ := ConRon.Bridge.Inductives.checkBlockInds_spec fe hk
    henv bs bsP b a a1 _ hB.c.check ⟨hdP, hrel⟩ hrun1
  dsimp only at hrel1 hsh1 hF1 hS1 hq1 hsl1 hg1
  obtain ⟨F1, hF1'⟩ := id hF1
  rw [ConLeche.checkBlockInds_datF] at hF1'
  obtain ⟨henv₁, hTf⟩ := ConLeche.direct_block_inds_wf henv hdecl hF1'
  have hfor : p₁P.formers = bsP.formers := by
    show p₁P.members.map _ = bsP.members.map _
    rw [ConLeche.checkBlockInds_members hF1']
  have hT : ∀ cv ∈ p₁P.formers, ConLeche.Expr.WScoped 0 cv.type := fun cv hcv =>
    ConLeche.Expr.WScoped.of_not_hasFvar (hTf cv (hfor ▸ hcv))
  have hzT : ∀ ms ∈ p₁P.members, ConLeche.Expr.WScoped 0 ms.cvT.type :=
    fun ms hms => hT ms.cvT (List.mem_map_of_mem hms)
  obtain ⟨hms1, -⟩ := ConRon.Bridge.Inductives.dShape_inv hsh1
  -- the flush entering the formers' index
  refine RefE.bindE (fun _ => icpE.k_flush_caches.none ..) id
    (flushRefR R.look.flush hGnv hB.c c1.ext hS1 hI1 hA1 ⟨c1.ok.state, c1.ok.pins, hrel1.ifenv⟩)
    fun ⟨r2, m2⟩ _ a2 _ h2 => ?_
  rw [icpE.k_flush_caches.arm1]
  have x12 := h2.inst.ext
  have hB2 := h2.st
  -- the constructors
  have hq2 := hq1.grow (decBS_mono _) h2.grow
  have hsl2 := hsl1.grow' hq1 h2.grow
  have hsh2 := ConRon.Bridge.Inductives.dShape_ext x12 _ _ hsh1
  refine RefE.bindE (fun _ => icpE.k_check_block_ctors.none ..) id
    (R.ctors n (by omega) _ fe1 env₁ env₁ m2 a2 _ bs1 p₁P hB2 henv₁ hq2 hsl2 hsh2 hzT hB2.c.check.ienv.toS)
    fun ⟨r3, m3⟩ _ a3 hrun3 h3 => ?_
  obtain ⟨hB3, hg3⟩ := h3
  rw [icpE.k_check_block_ctors.arm1]
  obtain ⟨c3, _, -, hF3⟩ := ConRon.Bridge.Inductives.checkBlockCtors_specF fe1 fe1 hk henv₁ bs1 p₁P
    env₁ bs1.members p₁P.members hzT a2 a3 _ hB2.c.check
    ⟨hsh2, ConRon.Bridge.Inductives.dMember_ext.list x12 _ _ hms1, hB2.c.check.ienv.toS⟩ hrun3
  have hct := ConRon.Bridge.Inductives.checkBlockCtors_types hF3
  have x13 := x12.trans c3.ext
  -- the walk's context
  have g13 := h2.grow.trans hg3
  have hq3 := hq1.grow (decBS_mono _) g13
  have hsl3 := hsl1.grow' hq1 g13
  have hsh3 := ConRon.Bridge.Inductives.dShape_ext x13 _ _ hsh1
  refine RefE.bindE (fun _ => icpE.k_block_nest_ctx.none ..) id
    (R.bnc n (by omega) _ fe1 env₁ m3 a3 _ bs1 p₁P hB3 henv₁ hq3 hsl3 hsh3 hT)
    fun ⟨r4, m4⟩ ⟨c, holes⟩ a4 hrun4 h4 => ?_
  obtain ⟨hB4, hg4, hctx4, hU4, hho4, hhob4, hhi4, -⟩ := h4
  rw [icpE.k_block_nest_ctx.arm1]
  obtain ⟨c4, ⟨ctxP, holesP⟩, ⟨hctx, hholes, hctxOk, hhw, hpar, hlen, hnh, hnP⟩, hF4⟩ :=
    ConRon.Bridge.Inductives.blockNestCtx_spec fe1 henv₁ bs1 p₁P hT a3 a4 _ hB3.c.check hsh3 hrun4
  dsimp only at hctx hholes hctxOk hhw hpar hlen hnh hnP hF4 hctx4 hU4 hho4 hhob4 hhi4
  have hparN := ConRon.Bridge.Inductives.BT.blockNestCtx_params_scoped hT hF4
  dsimp only at hparN
  obtain ⟨namesP, lpsP, paramsP, sortP, _, hctxEq, -, -, hparams, -, -, _⟩ :=
    ConRon.Bridge.Inductives.dCtx_inv hctx
  have x14 := x13.trans c4.ext
  -- the parameters' slice (the context's words `7, 8`)
  have g14 := g13.trans hg4
  have hq4 := hq1.grow (decBS_mono _) g14
  have hsl4 := hsl1.grow' hq1 g14
  have hsh4 := ConRon.Bridge.Inductives.dShape_ext x14 _ _ hsh1
  have hcdec : decCtx (truncM m4) (r4.headD 0).toNat = some c := hctx4
  obtain ⟨-, -, -, -, hpar', -, -, -⟩ := decCtx_some hcdec
  obtain ⟨po, pl, hpo, hpl, hpd⟩ := decAt_some hpar'
  have hT4 : iwTop m4 < 2 ^ 64 := (rdW (m4.arr64 CTL) 200).toNat_lt
  have hc10 : (r4.headD 0).toNat + 10 < iwTop m4 := hU4.inn.1 10 (by omega)
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
  have hpfD : DecB (fun m => (decHL m (rdW (m4.arr64 IW) (r4.headD 0 + 7)).toNat
      (rdW (m4.arr64 IW) (r4.headD 0 + 8)).toNat : Option (List EIdx))) m4 c.params := by
    rw [wpo, wpl, hpoT, hplT]; exact hpd
  have hpfb : (rdW (m4.arr64 IW) (r4.headD 0 + 7)).toNat +
      (rdW (m4.arr64 IW) (r4.headD 0 + 8)).toNat ≤ iwTop m4 := by
    rw [wpo, wpl, hpoT, hplT]
    rw [iwN_truncM (by omega)] at hpo
    rw [iwN_truncM (by omega)] at hpl
    exact hU4.sl 7 (by omega) po pl hpo hpl
  have hpl4 : ctxP.params.length = p₁P.nP := by rw [hlen, hnP]
  have hpfP : Frontend.denoteEList a4.store c.params = some ctxP.params := by
    rw [hctxEq]; exact hparams
  -- the classes
  refine RefE.bindE (fun _ => icpE.k_check_block_classes.none ..) id
    (R.cls n (by omega) _ fe1 env₁ m4 a4 _ _ _ bs1 p₁P c.params ctxP.params hB4 henv₁ hq4 hsl4 hpfD
      hpfb hsh4 hpfP hpl4 hparN)
    fun ⟨r5, m5⟩ ⟨rd, ms⟩ a5 hrun5 h5 => ?_
  obtain ⟨hB5, hg5, hrd5, hms5⟩ := h5
  rw [icpE.k_check_block_classes.arm1]
  obtain ⟨c5, ⟨rdP, msP⟩, ⟨hrd, hmsP, hMsc⟩, hF5⟩ :=
    ConRon.Bridge.Inductives.checkBlockClasses_spec fe1 hk henv₁ bs1 p₁P c.params ctxP.params hpl4
      hparN a4 a5 _ hB4.c.check ⟨hsh4, hpfP⟩ hrun5
  dsimp only at hrd hmsP hMsc hF5 hrd5 hms5
  have x15 := x14.trans c5.ext
  -- the positivity check
  have g15 := g14.trans hg5
  have hq5 := hq1.grow (decBS_mono _) g15
  have hsl5 := hsl1.grow' hq1 g15
  have hsh5 := ConRon.Bridge.Inductives.dShape_ext x15 _ _ hsh1
  refine RefE.bindE (fun _ => icpE.k_check_block_positivity.none ..) id
    (R.pos n (by omega) _ fe1 env₁ m5 a5 _ bs1 p₁P hB5 henv₁ hq5 hsl5 hsh5 hT hct)
    fun ⟨r6, m6⟩ ⟨outs, pos⟩ a6 hrun6 h6 => ?_
  obtain ⟨hB6, hg6, hks6, hns6⟩ := h6
  rw [icpE.k_check_block_positivity.arm1]
  obtain ⟨c6, ⟨outsP, posP⟩, ⟨houts, hpos⟩, hF6⟩ :=
    ConRon.Bridge.Inductives.checkBlockPositivity_spec fe1 hk henv₁ bs1 p₁P hT hct a5 a6 _
      hB5.c.check hsh5 hrun6
  dsimp only at houts hpos hF6 hks6 hns6
  have x56 := c6.ext
  -- the seeds: every outside class
  have g46 := hg5.trans hg6
  have hU6 := hU4.grow g46
  have hho6 : (decHL m6 (r4.tail.headD 0).toNat (r4.tail.tail.headD 0).toNat : Option (List EIdx)) =
      some holes := by rw [decHL_grow3 g46 hhob4]; exact hho4
  have hms6 := hms5.grow (fun q => decTM_mono q) hg6
  refine RefE.bindE (fun _ => icpE.k_class_seeds.none ..) id
    (R.seeds n (by omega) _ fe1 env₁ m6 a6 _ _ _ _ _ c holes ms hB6 hU6 hhi4 hho6
      (Nat.le_trans hhob4 g46.iw) hms6)
    fun ⟨r7, m7⟩ seeds a7 hrun7 h7 => ?_
  obtain ⟨hS7, hI7, hA7, hg7, hsd7⟩ := h7
  rw [icpE.k_class_seeds.arm1]
  have x46 := c5.ext.trans x56
  obtain ⟨p7, hseeds⟩ := ConRon.Bridge.Inductives.classSeeds_spec env₁.find? c ctxP holes holesP ms
    msP a6 a7 seeds hB6.c.check.state hB6.c.check.pins
    ⟨ConRon.Bridge.Inductives.dCtx_ext _ x46 _ _ hctx, ConRon.Bridge.denoteEList_ext x46 _ _ hholes,
      ConRon.Bridge.Inductives.dMajor_ext.list x56 _ _ hmsP⟩ hrun7
  have c7 := p7.toCore hB6.c.check
  have x67 := c7.ext
  have hB7 : BkSt dn (r1.headD 0) fe1 env₁ m7 a7 := ⟨StageC.ofView hB6.c hS7 hA7 c7.ok x67, hI7, hA7⟩
  -- every outside class, walked from the root frame's state
  have hU7 := hU6.grow hg7
  have hns7 := hns6.grow hg7 (rdW (m6.arr64 CTL) 200).toNat_lt
  refine RefE.bindE (fun _ => icpE.k_nest_seeds.none ..) id
    (R.nsd n (by omega) _ fe1 env₁ m7 a7 _ _ _ _ c ctxP seeds _ pos posP hB7 henv₁ hU7 hhi4 hsd7 hns7
      (ConRon.Bridge.Inductives.dCtx_ext _ (x46.trans x67) _ _ hctx) hctxOk hseeds
      (ConRon.Bridge.Inductives.dState_ext x67 _ _ hpos)
      (fun k hk x hx => by
        obtain ⟨M, hM, hMn, rfl⟩ := ConLeche.Cached.mem_classSeeds hk
        exact (ConLeche.nestSeedOf_ds hnh hlen (fun y hy => ConLeche.Expr.fvarB_le (by
          rw [hnP]; exact (((hMsc M hM).2.1 hMn).2 y hy).2)) x hx).2 (fun y hy => (hhw y hy).1) hpar))
    fun ⟨r8, m8⟩ ns a8 _ h8 => ?_
  obtain ⟨hB8, hg8, hns8⟩ := h8
  rw [icpE.k_nest_seeds.arm1]
  -- the kinds (`nest_out_kinds`: the identity)
  refine RefE.onlyCall (fun _ => icpE.k_nest_out_kinds.none ..) hGnv
    (_root_.L.Checker.nv_mem (by decide +kernel)) fun r9 m9 c9 => ?_
  obtain ⟨rfl, hm9⟩ := nok_callE R.look.nok c9
  subst m9
  rw [icpE.k_nest_out_kinds.arm1]
  -- the record
  refine RefE.onlyCall (fun _ => icpE.k_check_block_pass_rec.none ..) hGnv
    (_root_.L.Checker.nv_mem (by decide +kernel)) fun r10 m10 c10 => ?_
  rw [icpE.k_check_block_pass_rec.arm1]
  obtain ⟨q, rfl, hS10, hg10, hq11, hget, hf10⟩ :=
    icpr_callE R.look.prec R.look.ha c10 hB8.c.stage hB8.ind.stage.pos
  have hT8 : iwTop m8 < 2 ^ 64 := (rdW (m8.arr64 CTL) 200).toNat_lt
  obtain ⟨-, -, -, hnfsB⟩ := nsb_words hns8 hT8
  have htbl8 : PSlR decNCN ns.ctorNfs.toList (rdW (m8.arr64 IW) (r8.headD 0 + 4))
      (rdW (m8.arr64 IW) (r8.headD 0 + 5)) m8 := ⟨hnfsB, hns8.b4⟩
  have g48 := (hg5.trans hg6).trans (hg7.trans hg8)
  have hw7 : rdW (m8.arr64 IW) (r4.headD 0 + 7) = rdW (m4.arr64 IW) (r4.headD 0 + 7) :=
    rdW_iw_grow g48 (by rw [hc7]; omega)
  have hw8 : rdW (m8.arr64 IW) (r4.headD 0 + 8) = rdW (m4.arr64 IW) (r4.headD 0 + 8) :=
    rdW_iw_grow g48 (by rw [hc8]; omega)
  have g1A := (g14.trans g48).trans hg10
  have g6A := (hg7.trans hg8).trans hg10
  have hT10 : iwTop m10 < 2 ^ 64 := (rdW (m10.arr64 CTL) 200).toNat_lt
  have hw0 : rdW (m10.arr64 IW) q = r1.headD 0 := by
    have := hget 0 (by omega)
    simp only [Nat.add_zero, List.getElem?_cons_zero] at this
    simp only [rdW, this]; rfl
  have hw1 : rdW (m10.arr64 IW) (q + 1) = r1.tail.headD 0 := by
    have e1 := hget 1 (by omega)
    have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    simp only [rdW, hq1, e1]; rfl
  have hslA := hsl1.grow' hq1 g1A
  refine RefE.ret rfl ⟨?_, ?_, AFr.of_frame hf10 (by decide) (by decide) hB8.abs, hg1.trans g1A, ?_, ?_⟩
  · simp only [List.headD_cons]; rw [hw0]; exact hS10
  · exact hB8.ind.frame hf10 (fun b hb => by simp at hb; subst hb; exact ⟨by decide, by decide, by decide⟩) (fun x hx => by simp at hx; subst hx; decide)
  · simp only [List.headD_cons]; rw [hw0]
    exact bpRec_bpassR hget hq11 (hq1.grow (decBS_mono _) g1A) hslA.1
      (hks6.grow (fun q => decKSS_mono q) g6A)
      (by rw [hw7, hw8]; exact hpfD.grow (OMono.decHL _ _) (g48.trans hg10))
      (by rw [hw7, hw8]; exact Nat.le_trans hpfb (g48.trans hg10).iw)
      (hrd5.grow (decCR_mono _) (hg6.trans g6A))
      (hms5.grow (fun q => decTM_mono q) (hg6.trans g6A))
      (htbl8.grow (fun q => decNCN_mono q) hg10)
  · simp only [List.headD_cons]; rw [hw1]; exact hslA

/-- **A refinement's post weakened with the twin's whole run at hand.** -/
theorem RefE.weakenRunP {α β : Type} {G : Prop} {x : Except Err α} {T : AM β} {a : AState}
    {R R' : α → β → AState → Prop} (h : RefE G x T a R)
    (hR : ∀ v y a', T.run a = .ok (y, a') → R v y a' → R' v y a') : RefE G x T a R' := by
  cases x with
  | error e => exact h
  | ok v => obtain ⟨y, a', h1, h2⟩ := h; exact ⟨y, a', h1, hR _ _ _ h1 h2⟩

/-- **`check_block_pass`'s contract from its callees'**: `pass_ref` through the call
(`RefE.ofCallE`), con-ron's `checkBlockPass_of` on the twin's whole run for `PassOut`'s twin
facts, `StageC` at the formers' index rebuilt from the entry's (`StageC.ofView`). -/
theorem passRefS_of (R : PassRefs G p dn) (hGnv : G → closedNV p _root_.L.Checker.nvFns = true) :
    PassRefS G p dn := by
  intro n hn vis fe env m a p1 isRec bs bsP b hB henv hrel hq hsl hdP hdecl hb
  have h := RefE.ofCallE (s₀ := ⟨m, Locals.init []⟩) (icpE_spec p R.look n _ vis p1 isRec) hGnv
    (pass_ref R hGnv hB henv hrel hq hsl hdP hdecl hb hn (N := n))
  refine RefE.weakenRunP h fun ⟨r, m'⟩ q a' hrun hR => ?_
  obtain ⟨s', hs', -, hM⟩ := hR
  simp only at hs'; subst hs'
  obtain ⟨env₁, qP, hi, hck, hrel1, henv1, hdq, hT, hcb, hMs, hpl, -⟩ :=
    ConRon.Bridge.Inductives.checkBlockPass_of ConRon.Bridge.CoreSpec.of_core henv hB.c.check hrel
      hdP hdecl hrun
  exact ⟨hM.grow, hi, ⟨env₁, qP, ⟨StageC.ofView hB.c hM.stage hM.abs hck hi.ext, hM.ind, hM.abs⟩,
    hrel1, henv1, hdq, hT, hcb, hMs, hpl⟩, hM.record, hM.shape⟩

end comp

end L.Ind

end
