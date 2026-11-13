module

public import ConAgua.Arena.BasisBlockC
public import ConAgua.Arena.IndArmLps
public import ConAgua.Arena.IndInstallSpec.BpRecBpassR
public import ConAgua.Arena.IndPartsSpec.PlW
public import ConRon.Bridge.Inductives.BlockTail
public import ConRon.Bridge.Checker.Inv
public import ConAgua.Arena.IndDeclConstsTable
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
import all ConAgua.Arena.IndInstall
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.IndInstallSpec.PosFreeMfr

@[expose] public section

/-!
# `check_block`'s composition from its callees' contracts (lane `ronsync2`, stage 3)

`check_block(vis, bo, bl, p0)` (`IndInstall.lean`) calls, in order: `check_block_names`,
`reduce_members`, `flush_caches`, `block_is_rec`, `block_shape_with_members`, `check_block_pass`,
`check_block_tail`, `block_recs`, `block_tables`, `ifenv_push_delta`. Its unified model `icbE`
reads every callee through its call (`callE`); each callee has a **contract at the call** here
(`…RefS`, the style of `CbbRef`/`BlockRefS`), and `blockRefS_of` proves `check_block`'s contract
`BlockRefS` from them: the twin's `checkBlock` split at the same points (`checkBlock_split`,
`cbNamesT` the names' guards), the twin's facts between the steps by con-ron's lemmas
(`checkBlock_bridge`'s steps), the memory's by the contracts' posts.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The twin, split at the L calls -/

/-- `checkBlock`'s opening guards (`check_block_names`): the distinct constructor and member
names, no member at a `Bool` constructor's name. -/
def cbNamesT (p₀ : BlockShape) : AM Unit :=
  if !ConRon.Arena.nameNodup (p₀.allCtors.map (·.1.name)) || !ConRon.Arena.nameNodup p₀.memberNames then
    ConRon.Arena.fail (.invalid "direct rec: duplicate constructor")
  else do
    let bt ← ConRon.Arena.pinBoolTrue
    let bf ← ConRon.Arena.pinBoolFalse
    if p₀.memberNames.contains bt || p₀.memberNames.contains bf then
      ConRon.Arena.fail (.invalid "direct rec: a family at a `Bool` constructor's name")
    else pure ()

/-- **`checkBlock` at `check_block`'s calls.** -/
theorem checkBlock_split (mode : ConLeche.CheckMode) (fe : IFEnv) (block : List IConstantInfo)
    (p₀ : BlockShape) :
    ConRon.Arena.checkBlock mode fe block p₀ = (do
      cbNamesT p₀
      let ms ← ConRon.Arena.reduceMembers mode fe p₀.nP p₀.members
      ConRon.Arena.flushCaches
      let isRec ← ConRon.Arena.blockIsRec p₀
      let q ← ConRon.Arena.checkBlockPass mode fe { p₀ with members := ms } isRec
      let Q ← ConRon.Arena.unwrapOr (← ConRon.Arena.blockTables p₀ p₀.members)
        (.internal "direct structure: projection bodies")
      let fe₂ ← ConRon.Arena.checkBlockTail mode block q Q
      let recs ← ConRon.Arena.blockRecs p₀ p₀.recs
      pure (fe₂.pushDelta recs Q)) := by
  unfold ConRon.Arena.checkBlock cbNamesT
  dsimp only
  split
  · exact (L.Arena.fail_bindAM _ _).symm
  · simp only [bind_assoc]
    congr 1; funext bt; congr 1; funext bf
    split
    · exact (L.Arena.fail_bindAM _ _).symm
    · simp only [pure_bind]

/-! ## The model -/

/-- The lookup of `check_block`. -/
structure CbLook (p : Prog) : Prop where
  cb : p.lookup "check_block" = some L.Ind.checkBlock

set_option experimental.vcgen true in
/-- **`check_block`'s unified model**: every callee through its call. -/
l_model icbE_spec (p : Prog) (hP : CbLook p)
  fns [hP.cb ↦ icbE]
  specs []
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


/-! ## The state the steps carry -/

/-- `StageC` with the inductive arm's memos and `AbsOK`: what `check_block`'s steps up to the
tail carry. -/
structure BkSt (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) : Prop where
  c : StageC dn vis fe env m a
  ind : IndMemos m
  abs : AbsOK m

/-- One step of `check_block` before the pass: the state carried, the pools grown, the twin's
store extended and its pins kept. -/
structure BkGo (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (m' : Mem) (a' : AState) : Prop where
  st : BkSt dn vis fe env m' a'
  grow : IWGrow m m'
  inst : ConRon.Bridge.Inductives.InstStep a a'

/-- The memory facts after the tail (no twin invariant is carried past it). -/
structure BkMem (m : Mem) : Prop where
  ind : IndMemos m
  core : CoreMemos m
  abs : AbsOK m

theorem BkSt.mem {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
    {m : Mem} {a : AState} (h : BkSt dn vis fe env m a) : BkMem m :=
  ⟨h.ind, h.c.stageT.twin.memos, h.abs⟩

/-! ## The callees' contracts -/

section contracts
variable (G : Prop) (p : Prog) (dn : NIdx → Option ConLeche.Name)

/-- **`check_block_names(p0)`'s contract**: the names' guards (`cbNamesT`), both outcomes. -/
def NamesRefS : Prop :=
  ∀ (n : Nat) (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState) (p0 : Word)
    (bs : BlockShape) (bsP : ConLeche.BlockShape), BkSt dn vis fe env m a →
    DecB (fun m => decBS m p0.toNat) m bs → ShapeSl m p0 →
    ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    RefE G (callE p n "check_block_names" [p0] m) (cbNamesT bs) a
      (fun rm _ a' => BkGo dn vis fe env m a rm.2 a')

/-- **`reduce_members(vis, nP, ms.off, ms.len)`'s contract**: `reduceMembers`, both outcomes, the
reduced members a slice below the top. -/
def RmRefS : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState)
    (nP mo ml : Word) (mss : List MemberShape) (msP : List ConLeche.MemberShape),
    BkSt dn vis fe env m a → ConLeche.EnvWF env →
    DecB (fun m => decPL m (decMSB m) mo.toNat ml.toNat) m mss → mo.toNat + ml.toNat ≤ iwTop m →
    mss.mapM (ConRon.Bridge.Inductives.dMember a.store) = some msP →
    RefE G (callE p n "reduce_members" [vis, nP, mo, ml] m)
      (ConRon.Arena.reduceMembers V fe nP.toNat mss) a
      (fun rm ms a' => BkGo dn vis fe env m a rm.2 a' ∧
        DecB (fun m => decPL m (decMSB m) (rm.1.headD 0).toNat (rm.1.tail.headD 0).toNat) rm.2 ms ∧
        (rm.1.headD 0).toNat + (rm.1.tail.headD 0).toNat ≤ iwTop rm.2)

/-- **`flush_caches()`'s contract** under `BkSt`. -/
def FlushRefS : Prop :=
  ∀ (n : Nat) (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState),
    BkSt dn vis fe env m a →
    RefE G (callE p n "flush_caches" [] m) ConRon.Arena.flushCaches a
      (fun rm _ a' => BkGo dn vis fe env m a rm.2 a')

/-- **`block_is_rec(p0)`'s contract**: official's `is_rec`, its flag the returned word. -/
def BirRefS : Prop :=
  ∀ (n : Nat) (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState) (p0 : Word)
    (bs : BlockShape) (bsP : ConLeche.BlockShape), BkSt dn vis fe env m a →
    DecB (fun m => decBS m p0.toNat) m bs → ShapeSl m p0 →
    ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    RefE G (callE p n "block_is_rec" [p0] m) (ConRon.Arena.blockIsRec bs) a
      (fun rm b a' => BkGo dn vis fe env m a rm.2 a' ∧ (rm.1.headD 0 != 0) = b)

/-- **`block_shape_with_members(p0, ms.off, ms.len)`'s contract**: a fresh shape record of
`{ bs with members := ms }` (the twin has no step). -/
def BswmRefS : Prop :=
  ∀ (n : Nat) (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState) (p0 mo ml : Word)
    (bs : BlockShape) (ms : List MemberShape), BkSt dn vis fe env m a →
    DecB (fun m => decBS m p0.toNat) m bs → ShapeSl m p0 →
    DecB (fun m => decPL m (decMSB m) mo.toNat ml.toNat) m ms → mo.toNat + ml.toNat ≤ iwTop m →
    RefE G (callE p n "block_shape_with_members" [p0, mo, ml] m) (pure ()) a
      (fun rm _ a' => BkGo dn vis fe env m a rm.2 a' ∧
        DecB (fun m => decBS m (rm.1.headD 0).toNat) rm.2 { bs with members := ms } ∧
        ShapeSl rm.2 (rm.1.headD 0))

/-- What `check_block_pass` hands the tail (from `m`, `a`; the record at `w`): the pools grown,
the twin's step, `BkSt` at the formers' index (whose view is the record's word `0`) and con-ron's
`checkBlockPass_of` facts there, the record decoded, the shape's (word `1`) slices below the top (`ShapeSl`). -/
structure PassOut (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (w : Word)
    (q : BlockPass) (m' : Mem) (a' : AState) : Prop where
  grow : IWGrow m m'
  inst : ConRon.Bridge.Inductives.InstStep a a'
  twin : ∃ (env₁ : ConLeche.Env) (qP : ConLeche.BlockPass ConLeche.Env),
    BkSt dn (rdW (m'.arr64 IW) w) q.env1 env₁ m' a' ∧
    ConRon.Bridge.Inductives.EnvRel env₁ q.env1 a'.store ∧ ConLeche.EnvWF env₁ ∧
    ConRon.Bridge.Inductives.dPass a'.store env₁ q = some qP ∧
    (∀ cv ∈ qP.p.formers, ConLeche.Expr.WScoped 0 cv.type) ∧
    ConLeche.EnvWF (ConLeche.consBlockCtors qP.p.nP qP.p.ctorGroups env₁) ∧
    (∀ M ∈ qP.cls, ConLeche.Cached.ClassMajScoped qP.p.nP M) ∧ qP.params.length = qP.p.nP
  record : BPassR (rdW (m'.arr64 IW) w) q.env1 m' w q
  shape : ShapeSl m' (rdW (m'.arr64 IW) (w + 1))

/-- **`check_block_pass(vis, p, isRec)`'s contract**: `checkBlockPass`, both outcomes, from
`BkSt` and `checkBlockPass_of`'s preconditions. -/
def PassRefS : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState) (p1 isRec : Word)
    (bs : BlockShape) (bsP : ConLeche.BlockShape) (b : Bool), BkSt dn vis fe env m a →
    ConLeche.EnvWF env → ConRon.Bridge.Inductives.EnvRel env fe a.store →
    DecB (fun m => decBS m p1.toNat) m bs → ShapeSl m p1 →
    ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    (∀ ms ∈ bsP.members, ConLeche.MemberDeclaredWF env ms) → (isRec != 0) = b →
    RefE G (callE p n "check_block_pass" [vis, p1, isRec] m) (ConRon.Arena.checkBlockPass V fe bs b) a
      (fun rm q a' => PassOut dn m a (rm.1.headD 0) q rm.2 a')

/-- What `check_block_tail` gives (from `m`, `a`): the stage at the returned view, the memory's
facts, the pools grown, the twin's step. -/
structure TailOut (m : Mem) (a : AState) (w : Word) (fe' : IFEnv) (m' : Mem) (a' : AState) : Prop where
  stage : StageR w fe' m' a'
  mem : BkMem m'
  grow : IWGrow m m'
  inst : ConRon.Bridge.Inductives.InstStep a a'

/-- **`check_block_tail(bo, bl, q)`'s contract**: `checkBlockTail`, both outcomes, from
`check_block_pass`'s out (`PassOut`'s parts) and the block. -/
def TailRefS : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (vis : Word) (env₁ : ConLeche.Env) (m : Mem) (a : AState) (bO bL w : Word)
    (block : List IConstantInfo) (blockP : List ConLeche.ConstantInfo) (q : BlockPass)
    (qP : ConLeche.BlockPass ConLeche.Env),
    BkSt dn vis q.env1 env₁ m a → BPassR vis q.env1 m w q → ShapeSl m (rdW (m.arr64 IW) (w + 1)) →
    DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block → bO.toNat + bL.toNat < 2 ^ 64 →
    Frontend.denoteCIList a.store block = some blockP → BlockLpsDn dn block →
    ConRon.Bridge.Inductives.EnvRel env₁ q.env1 a.store → ConLeche.EnvWF env₁ →
    ConRon.Bridge.Inductives.dPass a.store env₁ q = some qP →
    (∀ cv ∈ qP.p.formers, ConLeche.Expr.WScoped 0 cv.type) →
    ConLeche.EnvWF (ConLeche.consBlockCtors qP.p.nP qP.p.ctorGroups env₁) →
    (∀ M ∈ qP.cls, ConLeche.Cached.ClassMajScoped qP.p.nP M) → qP.params.length = qP.p.nP →
    q.p.nP + 1 < 2 ^ 64 →
    ∀ (tO tL : Word) (Q : List IProjTable), decPL m (decTbl (erecP m)) tO.toNat tL.toNat = some Q →
    tO.toNat + tL.toNat ≤ iwTop m → TblsOK a.store Q →
    RefE G (callE p n "check_block_tail" [bO, bL, w, tO, tL] m) (ConRon.Arena.checkBlockTail V block q Q) a
      (fun rm fe' a' => TailOut m a (rm.1.headD 0) fe' rm.2 a')

/-- **`block_recs(p, rs.off, rs.len)`'s contract**: `blockRecs`, its records an `IW` slice. -/
def BrRefS : Prop :=
  ∀ (n : Nat) (vis : Word) (fe : IFEnv) (m : Mem) (a : AState) (pp ro rl : Word) (bs : BlockShape)
    (rcs : List RecShape), StageR vis fe m a → BkMem m →
    DecB (fun m => decBS m pp.toNat) m bs → PSlR0 decRS rcs ro rl m →
    RefE G (callE p n "block_recs" [pp, ro, rl] m) (ConRon.Arena.blockRecs bs rcs) a
      (fun rm cis a' => StageR vis fe rm.2 a' ∧ BkMem rm.2 ∧ IWGrow m rm.2 ∧
        decPL rm.2 (decCI (erecP rm.2)) (rm.1.headD 0).toNat (rm.1.tail.headD 0).toNat = some cis ∧
        (rm.1.headD 0).toNat + (rm.1.tail.headD 0).toNat ≤ iwTop rm.2)

/-- **`block_tables(p, ms.off, ms.len)`'s contract**: `blockTables`, its tables an `IW` slice
(the parameter count bounded, as `struct_proj_bodies` needs). It runs between the pass and the
tail, so it carries `BkSt` (con-ron's `blockTables_run`: a `PStep`). -/
def BtRefS : Prop :=
  ∀ (n : Nat) (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState) (pp mo ml : Word)
    (bs : BlockShape) (bsP : ConLeche.BlockShape) (mss : List MemberShape)
    (msP : List ConLeche.MemberShape), BkSt dn vis fe env m a → bs.nP + 1 < 2 ^ 64 →
    DecB (fun m => decBS m pp.toNat) m bs → PSlR0 decMS mss mo ml m →
    ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    mss.mapM (ConRon.Bridge.Inductives.dMember a.store) = some msP →
    RefE G (callE p n "block_tables" [pp, mo, ml] m) (ConRon.Arena.blockTables bs mss) a
      (fun rm ts a' => BkGo dn vis fe env m a rm.2 a' ∧ BtsR rm.2 rm.1 ts)

/-- **`ifenv_push_delta(vis, L.off, L.len, Q.off, Q.len)`'s contract**: the view of
`fe.pushDelta L Q` (the twin has no step). -/
def PdRefS : Prop :=
  ∀ (n : Nat) (vis : Word) (fe : IFEnv) (m : Mem) (a : AState) (lo ll qo ql : Word)
    (cis : List IConstantInfo) (ts : List IProjTable), StageR vis fe m a → BkMem m →
    decPL m (decCI (erecP m)) lo.toNat ll.toNat = some cis → lo.toNat + ll.toNat ≤ iwTop m →
    decPL m (decTbl (erecP m)) qo.toNat ql.toNat = some ts → qo.toNat + ql.toNat ≤ iwTop m →
    RefE G (callE p n "ifenv_push_delta" [vis, lo, ll, qo, ql] m) (pure ()) a
      (fun rm _ a' => a' = a ∧ StageR (rm.1.headD 0) (fe.pushDelta cis ts) rm.2 a ∧ BkMem rm.2 ∧
        IWGrow m rm.2)

end contracts

/-- **`check_block`'s callees' contracts.** -/
structure CbRefs (G : Prop) (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop where
  look : CbLook p
  names : NamesRefS G p dn
  rm : RmRefS G p dn
  flush : FlushRefS G p dn
  bir : BirRefS G p dn
  bswm : BswmRefS G p dn
  pass : PassRefS G p dn
  tail : TailRefS G p dn
  br : BrRefS G p
  bt : BtRefS G p dn
  pd : PdRefS G p

/-- **`check_block`'s contract** (what `cid_ref` takes): on the shape `block_shape` read
(`ShapeR`'s `some` case) of a block that denotes, from `StageC` at the recogniser's state (whose
store extends the fold's, `FoldOK` at `a₀`, the pins the same), the arm's memos and the block's
level-parameter names, the call refines `checkBlock .verified fe block bs`, both outcomes (the
error half under `G`). The parameter count is bounded (`blockShape?_nP_lt`). -/
def BlockRefS (G : Prop) (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (vis bO bL p0 : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem)
    (a a₀ : AState) (bs : BlockShape) (bsP : ConLeche.BlockShape) (block : List IConstantInfo)
    (blockP : List ConLeche.ConstantInfo),
    StageC dn vis fe env m a → ConRon.Bridge.FoldOK env fe a₀ → ConRon.Arena.Ext a₀.store a.store →
    a.pins = a₀.pins →
    DecB (fun m => decBS m p0.toNat) m bs → ShapeSl m p0 →
    DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block → bO.toNat + bL.toNat < 2 ^ 64 →
    Frontend.denoteCIList a.store block = some blockP →
    ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    (∀ ms ∈ bsP.members, ms.declared = ms.cvT) → BlockLpsDn dn block → bs.nP + 1 < 2 ^ 64 →
    IndMemos m → AbsOK m →
    RefE G (callE p n "check_block" [vis, bO, bL, p0] m) (ConRon.Arena.checkBlock V fe block bs) a
      (fun rm fe' a' => CidPost dn m (rm.1.headD 0) fe' rm.2 a')


/-! ## The shape record's words -/

/-- **A shape record's slices grow with the pools.** -/
theorem ShapeSl.grow' {m m' : Mem} {p0 : Word} {bs : BlockShape} (h : ShapeSl m p0)
    (hq : DecB (fun m => decBS m p0.toNat) m bs) (hg : IWGrow m m') : ShapeSl m' p0 := by
  have hqt : decBS (truncM m) p0.toNat = some bs := hq
  obtain ⟨hmem, hrc, -⟩ := decBS_some hqt
  obtain ⟨o, l, ho, hl, -⟩ := partsAt decMS_mono hmem
  obtain ⟨o2, l2, ho2, hl2, -⟩ := partsAt decRS_mono hrc
  have h1 := (L.Ind.iwN_truncM_some hl).1
  have h3 := (L.Ind.iwN_truncM_some hl2).1
  obtain ⟨ms, hmsB⟩ := h.2.2
  refine ⟨fun o l ho hl => ?_, fun o l ho hl => ?_, ms,
    hmsB.grow (OMono.decAt (fun o l => OMono.decPL decMSB_mono o l) _) hg⟩
  · rw [iwN_grow hg (by omega)] at ho; rw [iwN_grow hg (by omega)] at hl
    exact Nat.le_trans (h.1 o l ho hl) hg.iw
  · rw [iwN_grow hg (by omega)] at ho; rw [iwN_grow hg (by omega)] at hl
    exact Nat.le_trans (h.2.1 o l ho hl) hg.iw

theorem decBPass_mono (fe : IFEnv) (q : Nat) : OMono (fun m => decBPass fe m q) := by
  unfold decBPass decLH
  repeat' (first
    | exact OMono.const _
    | apply decBS_mono
    | apply decKL_mono
    | apply decCR_mono
    | apply decTM_mono
    | apply decNCN_mono
    | apply OMono.iwN
    | apply OMono.decHL
    | apply OMono.decAt
    | apply OMono.decPL
    | apply OMono.bind
    | intro _
    )

/-- **The pass's record grows with the pools**, and the shape it points at. -/
theorem BPassR.grow {vis : Word} {fe : IFEnv} {m m' : Mem} {q : Word} {bp : BlockPass}
    (h : BPassR vis fe m q bp) (hs : ShapeSl m (rdW (m.arr64 IW) (q + 1))) (hg : IWGrow m m') :
    BPassR vis fe m' q bp ∧ ShapeSl m' (rdW (m'.arr64 IW) (q + 1)) := by
  obtain ⟨hd, hb, hv, hsrc⟩ := h
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hb1 := hb.1
  have e1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
  have hd' : decBPass fe (truncM m) q.toNat = some bp := hd
  simp only [decBPass, bind, Option.bind_eq_some_iff] at hd'
  obtain ⟨v, hv1, bs', hbs, -⟩ := hd'
  obtain ⟨hw, -⟩ := bpWord hv1 (w := q + 1) e1
  obtain ⟨-, -, hnP, -⟩ := decBS_some hbs
  have hv4 := (L.Ind.iwN_truncM_some hnP).1
  have hvl : v < 2 ^ 64 := by omega
  have ew : (rdW (m.arr64 IW) (q + 1)).toNat = v := by rw [hw]; exact UInt64.toNat_ofNat_of_lt' hvl
  have er1 : rdW (m'.arr64 IW) (q + 1) = rdW (m.arr64 IW) (q + 1) := rdW_iw_grow hg (by omega)
  refine ⟨⟨hd.grow (decBPass_mono fe _) hg, BPassB.grow hg hb, by rw [rdW_iw_grow hg (by omega)]; exact hv,
    ?_⟩, ?_⟩
  · intro o l h1 h2
    rw [er1, iwN_grow hg (by omega)] at h1
    rw [er1, iwN_grow hg (by omega)] at h2
    exact Nat.le_trans (hsrc o l h1 h2) hg.iw
  · rw [er1]
    exact hs.grow' (show decBS (truncM m) (rdW (m.arr64 IW) (q + 1)).toNat = some bs' by rw [ew]; exact hbs) hg

/-- The level parameters' names of a shape that denotes. -/
theorem lps_names_of_dShape {st : EStore} {bs : BlockShape} {pP : ConLeche.BlockShape}
    (h : ConRon.Bridge.Inductives.dShape st bs = some pP) :
    ∃ ks, bs.lps.mapM (denoteN st.lss.ls.ns) = some ks := by
  simp only [ConRon.Bridge.Inductives.dShape, bind, Option.bind_eq_some_iff] at h
  obtain ⟨ms, hms, -⟩ := h
  unfold BlockShape.lps
  match hm : bs.members, hms with
  | [], _ => exact ⟨[], rfl⟩
  | m0 :: _, hms =>
    obtain ⟨y, -, -, hy, -⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hms
    simp only [ConRon.Bridge.Inductives.dMember, bind, Option.bind_eq_some_iff] at hy
    obtain ⟨c, hc, -⟩ := hy
    exact denoteCV_lps hc

/-- **The shape's members, decoded with their constructor slices' bounds.** -/
theorem ShapeSl.membersB {m : Mem} {p0 : Word} {bs : BlockShape} (hq : DecB (fun m => decBS m p0.toNat) m bs)
    (hsl : ShapeSl m p0) : DecB (fun m => decAt m (decPL m (decMSB m)) p0.toNat) m bs.members := by
  obtain ⟨ms, hms⟩ := hsl.2.2
  have hmem := (decBS_some (show decBS (truncM m) p0.toNat = some bs from hq)).1
  have h1 : decAt (truncM m) (decPL (truncM m) (decMS (truncM m))) p0.toNat = some ms := by
    have h : decAt (truncM m) (decPL (truncM m) (decMSB (truncM m))) p0.toNat = some ms := hms
    simp only [decAt, bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨o, ho, l, hl, hd⟩ := h
    exact ⟨o, ho, l, hl, decPL_decMSB hd⟩
  rw [hmem] at h1; cases h1; exact hms

/-- `bsAt`'s members, with their constructor slices' bounds. -/
theorem bsAtB {m : Mem} {p0 : Word} {bs : BlockShape} (hq : DecB (fun m => decBS m p0.toNat) m bs)
    (hsl : ShapeSl m p0) :
    DecB (fun m' => decPL m' (decMSB m') (rdW (m.arr64 IW) p0).toNat (rdW (m.arr64 IW) (p0 + 1)).toNat)
      m bs.members := by
  obtain ⟨o, l, ho, hl, hdm, -⟩ := partsAt decMSB_mono (ShapeSl.membersB hq hsl)
  obtain ⟨e0, -⟩ := iwRd (o := p0) (w := 0) (by simpa using ho)
  obtain ⟨e1, -⟩ := iwRd (o := p0) (w := 1) (by simpa using hl)
  simp only [UInt64.add_zero] at e0
  rw [UInt64.toNat_inj.mp e0, UInt64.toNat_inj.mp e1]; exact hdm

/-- **What `check_block` reads off the shape record**: the members' and the recursors' slices
(words `0‥3`) and the parameter count (word `4`). -/
theorem bsAt {m : Mem} {p0 : Word} {bs : BlockShape} (hq : DecB (fun m => decBS m p0.toNat) m bs)
    (hsl : ShapeSl m p0) :
    DecB (fun m' => decPL m' (decMS m') (rdW (m.arr64 IW) p0).toNat (rdW (m.arr64 IW) (p0 + 1)).toNat)
        m bs.members ∧
      (rdW (m.arr64 IW) p0).toNat + (rdW (m.arr64 IW) (p0 + 1)).toNat ≤ iwTop m ∧
      PSlR0 decRS bs.recs (rdW (m.arr64 IW) (p0 + 2)) (rdW (m.arr64 IW) (p0 + 3)) m ∧
      (rdW (m.arr64 IW) (p0 + 4)).toNat = bs.nP := by
  have hqt : decBS (truncM m) p0.toNat = some bs := hq
  obtain ⟨hmem, hrc, hnP, -⟩ := decBS_some hqt
  obtain ⟨o, l, ho, hl, hdm, -⟩ := partsAt decMS_mono hmem
  obtain ⟨o2, l2, ho2, hl2, hdr, hob2⟩ := partsAt decRS_mono hrc
  obtain ⟨e0, -⟩ := iwRd (o := p0) (w := 0) (by simpa using ho)
  obtain ⟨e1, -⟩ := iwRd (o := p0) (w := 1) (by simpa using hl)
  obtain ⟨e2, -⟩ := iwRd (o := p0) (w := 2) (by simpa using ho2)
  obtain ⟨e3, -⟩ := iwRd (o := p0) (w := 3) (by simpa using hl2)
  obtain ⟨e4, -⟩ := iwRd (o := p0) (w := 4) (by simpa using hnP)
  simp only [UInt64.add_zero] at e0
  have f0 : rdW (m.arr64 IW) p0 = o := UInt64.toNat_inj.mp e0
  have f1 : rdW (m.arr64 IW) (p0 + 1) = l := UInt64.toNat_inj.mp e1
  have f2 : rdW (m.arr64 IW) (p0 + 2) = o2 := UInt64.toNat_inj.mp e2
  have f3 : rdW (m.arr64 IW) (p0 + 3) = l2 := UInt64.toNat_inj.mp e3
  rw [f0, f1, f2, f3]
  exact ⟨hdm, hsl.1 _ _ (L.Ind.iwN_truncM_some ho).2 (L.Ind.iwN_truncM_some hl).2, ⟨hdr, hob2⟩, e4⟩

/-! ## The composition -/

/-- **A callee the twin has no step for, read through its call by a contract at `pure ()`**, then
the rest. -/
theorem RefE.bindNone {α β ρ : Type} {G G' : Prop} {a : AState} {R : α → β → AState → Prop}
    {K : Except Err ρ → Except Err α} (hK : ∀ e, K (.error e) = .error e) (hG : G → G')
    {x : Except Err ρ} {T : AM β} {Q : ρ → Unit → AState → Prop} (h1 : RefE G' x (pure ()) a Q)
    (h2 : ∀ v, Q v () a → RefE G (K (.ok v)) T a R) : RefE G (K x) T a R := by
  cases x with
  | error e =>
    rw [hK]
    have h := RefE.bind_left (α := α) (R := R) (G := G) (a := a) (x := (pure () : AM Unit))
      (f := fun _ => T) (e := e) (fun hg => h1 (hG hg))
    rwa [pure_bind] at h
  | ok v =>
    obtain ⟨y, a1, hr, hQ⟩ := h1
    have e : ((), a) = (y, a1) := Except.ok.inj hr
    cases e
    exact h2 v hQ

/-- **The same as the model's last step**, its ok arm returning `f v`, the twin's `pure y`. -/
theorem RefE.lastNone {α β ρ : Type} {G G' : Prop} {a : AState} {R : α → β → AState → Prop}
    {K : Except Err ρ → Except Err α} (hK : ∀ e, K (.error e) = .error e) {f : ρ → α}
    (hK' : ∀ v, K (.ok v) = .ok (f v)) (hG : G → G') {x : Except Err ρ} {y : β}
    {Q : ρ → Unit → AState → Prop} (h1 : RefE G' x (pure ()) a Q)
    (h2 : ∀ v, Q v () a → R (f v) y a) : RefE G (K x) (pure y) a R :=
  RefE.bindNone hK hG h1 fun v hQ => by rw [hK']; exact RefE.ret rfl (h2 v hQ)

/-- **`checkBlockInds` keeps the parameter count** (`withSort` changes the sort alone). -/
theorem checkBlockInds_nP {mode : ConLeche.CheckMode} {fe : IFEnv} {bs : BlockShape} {isRec : Bool}
    {s s' : AState} {r : IFEnv × BlockShape}
    (h : ConRon.Arena.checkBlockInds mode fe bs isRec s = .ok (r, s')) : r.2.nP = bs.nP := by
  unfold ConRon.Arena.checkBlockInds at h
  rcases hm : bs.members with _ | ⟨ms₀, rest⟩ <;> simp only [hm] at h
  · exact nomatch h
  obtain ⟨⟨_, _⟩, _, -, h⟩ := ConRon.Bridge.AM.bind_ok h
  obtain ⟨_, _, -, h⟩ := ConRon.Bridge.AM.bind_ok h
  obtain ⟨_, _, -, h⟩ := ConRon.Bridge.AM.bind_ok h
  obtain ⟨p₁, _, hw, h⟩ := ConRon.Bridge.AM.bind_ok h
  obtain ⟨rfl, -⟩ := ConRon.Bridge.AM.pure_ok h
  unfold BlockShape.withSort at hw
  obtain ⟨_, _, -, hw⟩ := ConRon.Bridge.AM.bind_ok hw
  obtain ⟨_, _, -, hw⟩ := ConRon.Bridge.AM.bind_ok hw
  obtain ⟨rfl, -⟩ := ConRon.Bridge.AM.pure_ok hw
  rfl

/-- **`checkBlockPass` keeps the parameter count** (its shape is `checkBlockInds`'). -/
theorem checkBlockPass_nP {mode : ConLeche.CheckMode} {fe : IFEnv} {bs : BlockShape} {isRec : Bool}
    {s s' : AState} {q : BlockPass}
    (h : ConRon.Arena.checkBlockPass mode fe bs isRec s = .ok (q, s')) : q.p.nP = bs.nP := by
  unfold ConRon.Arena.checkBlockPass at h
  obtain ⟨⟨fe₁, p₁⟩, _, h1, h⟩ := ConRon.Bridge.AM.bind_ok h
  have e := checkBlockInds_nP h1
  obtain ⟨_, _, -, h⟩ := ConRon.Bridge.AM.bind_ok h
  obtain ⟨_, _, -, h⟩ := ConRon.Bridge.AM.bind_ok h
  obtain ⟨⟨_, _⟩, _, -, h⟩ := ConRon.Bridge.AM.bind_ok h
  obtain ⟨⟨_, _⟩, _, -, h⟩ := ConRon.Bridge.AM.bind_ok h
  obtain ⟨⟨_, _⟩, _, -, h⟩ := ConRon.Bridge.AM.bind_ok h
  obtain ⟨_, _, -, h⟩ := ConRon.Bridge.AM.bind_ok h
  obtain ⟨_, _, -, h⟩ := ConRon.Bridge.AM.bind_ok h
  obtain ⟨rfl, -⟩ := ConRon.Bridge.AM.pure_ok h
  exact e

section comp
variable {G : Prop} {p : Prog} {dn : NIdx → Option ConLeche.Name}


/-- **`check_block`'s model refines `checkBlock`, both outcomes**, from its callees' contracts:
the twin split at the calls (`checkBlock_split`), its facts between them as con-ron's
`checkBlock_bridge` derives them (`reduceMembers_spec`, `reduceMembers_inv`, `dShape_members`). -/
theorem cb_ref (R : CbRefs G p dn) {N : Nat} {vis bO bL p0 : Word} {fe : IFEnv} {env : ConLeche.Env}
    {m : Mem} {a a₀ : AState} {bs : BlockShape} {bsP : ConLeche.BlockShape}
    {block : List IConstantInfo} {blockP : List ConLeche.ConstantInfo}
    (hC : StageC dn vis fe env m a) (hfold : ConRon.Bridge.FoldOK env fe a₀)
    (hx : ConRon.Arena.Ext a₀.store a.store)
    (hq : DecB (fun m => decBS m p0.toNat) m bs) (hsl : ShapeSl m p0)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block) (hbb : bO.toNat + bL.toNat < 2 ^ 64)
    (hbP : Frontend.denoteCIList a.store block = some blockP)
    (hdP : ConRon.Bridge.Inductives.dShape a.store bs = some bsP)
    (hd : ∀ ms ∈ bsP.members, ms.declared = ms.cvT) (hlpd : BlockLpsDn dn block)
    (hnPb : bs.nP + 1 < 2 ^ 64) (hIM : IndMemos m) (hA : AbsOK m) (hN : N ≤ 2 ^ 62) :
    RefE G (icbE p N m vis bO bL p0) (ConRon.Arena.checkBlock V fe block bs) a
      (fun v fe' a' => CidPost dn m v.1 fe' v.2 a') := by
  rcases N with _ | n
  · rw [icbE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  rw [icbE.arm1, checkBlock_split]
  have hB0 : BkSt dn vis fe env m a := ⟨hC, hIM, hA⟩
  have henv := hfold.envWF
  have hrel : ConRon.Bridge.Inductives.EnvRel env fe a.store :=
    (ConRon.Bridge.Inductives.EnvRel.ofCheck hfold.check hfold.gate hfold.envWF).mono hx
  have hk : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel := ConRon.Bridge.CoreSpec.of_core
  obtain ⟨hms₀, -, hnP₀, -⟩ := ConRon.Bridge.Inductives.dShape_inv hdP
  -- the names
  refine RefE.bindE (fun _ => icbE.k_check_block_names.none ..) id
    (R.names n vis fe env m a p0 bs bsP hB0 hq hsl hdP) fun ⟨r1, m1⟩ _ a1 _ h1 => ?_
  rw [icbE.k_check_block_names.arm1]
  have hq1 := hq.grow (decBS_mono _) h1.grow
  have hsl1 := hsl.grow' hq h1.grow
  obtain ⟨-, hbm1, -, e4⟩ := bsAt hq1 hsl1
  have hdm1 := bsAtB hq1 hsl1
  -- the members at their telescopes
  have hR2 := R.rm n (by omega) vis fe env m1 a1 (rdW (m1.arr64 IW) (p0 + 4)) (rdW (m1.arr64 IW) p0)
    (rdW (m1.arr64 IW) (p0 + 1)) bs.members bsP.members h1.st henv hdm1 hbm1
    (ConRon.Bridge.Inductives.dMember_ext.list h1.inst.ext _ _ hms₀)
  rw [e4] at hR2
  refine RefE.bindE (fun _ => icbE.k_reduce_members.none ..) id hR2 fun ⟨r2, m2⟩ ms a2 hrun2 h2 => ?_
  obtain ⟨h2, hdms, hbms⟩ := h2
  rw [icbE.k_reduce_members.arm1]
  obtain ⟨c1, msP, hms', hF1⟩ := ConRon.Bridge.Inductives.reduceMembers_spec fe hk henv bs.nP
    bs.members bsP.members a1 a2 ms h1.st.c.check
    (ConRon.Bridge.Inductives.dMember_ext.list h1.inst.ext _ _ hms₀) hrun2
  rw [hnP₀] at hF1
  obtain ⟨F1, hF1'⟩ := id hF1
  rw [ConLeche.reduceMembers_datF] at hF1'
  obtain ⟨hAt, -⟩ := ConLeche.reduceMembers_inv hd hF1'
  -- the flush
  refine RefE.bindE (fun _ => icbE.k_flush_caches.none ..) id
    (R.flush n vis fe env m2 a2 h2.st) fun ⟨r3, m3⟩ _ a3 _ h3 => ?_
  rw [icbE.k_flush_caches.arm1]
  -- official's `is_rec`
  have g13 := (h1.grow.trans h2.grow).trans h3.grow
  have x13 := (h1.inst.trans h2.inst).trans h3.inst
  have hq3 := hq.grow (decBS_mono _) g13
  have hsl3 := hsl.grow' hq g13
  refine RefE.bindE (fun _ => icbE.k_block_is_rec.none ..) id
    (R.bir n vis fe env m3 a3 p0 bs bsP h3.st hq3 hsl3
      (ConRon.Bridge.Inductives.dShape_ext x13.ext _ _ hdP)) fun ⟨r4, m4⟩ b a4 _ h4 => ?_
  obtain ⟨h4, hb4⟩ := h4
  rw [icbE.k_block_is_rec.arm1]
  -- the shape at the reduced members
  have g14 := g13.trans h4.grow
  have g24 := h3.grow.trans h4.grow
  refine RefE.bindNone (fun _ => icbE.k_block_shape_with_members.none ..) id
    (R.bswm n vis fe env m4 a4 p0 _ _ bs ms h4.st (hq.grow (decBS_mono _) g14) (hsl.grow' hq g14)
      (hdms.grow (OMono.decPL decMSB_mono _ _) g24) (Nat.le_trans hbms g24.iw))
    fun ⟨r5, m5⟩ h5 => ?_
  obtain ⟨h5, hq5, hsl5⟩ := h5
  rw [icbE.k_block_shape_with_members.arm1]
  -- the pass
  have x25 := (h3.inst.trans h4.inst).trans h5.inst
  have x05 := (h1.inst.trans c1.toInst).trans x25
  refine RefE.bindE (fun _ => icbE.k_check_block_pass.none ..) id
    (R.pass n (by omega) vis fe env m5 a4 _ _ { bs with members := ms } { bsP with members := msP } b h5.st henv
      (hrel.mono x05.ext) hq5 hsl5
      (ConRon.Bridge.Inductives.BT.dShape_members (ConRon.Bridge.Inductives.dShape_ext x05.ext _ _ hdP)
        (ConRon.Bridge.Inductives.dMember_ext.list x25.ext _ _ hms'))
      (fun m hm => (hAt m hm).declaredWF) hb4) fun ⟨r6, m6⟩ q a6 hrun6 h6 => ?_
  rw [icbE.k_check_block_pass.arm1]
  -- the projection tables, read off the block once
  obtain ⟨env₁, qP, hB6, hrel6, henv₁, hq6, hT6, henv₂, hMs, hpl⟩ := h6.twin
  have g16 := (g14.trans h5.grow).trans h6.grow
  have x06 := x05.trans h6.inst
  have hq6' := hq.grow (decBS_mono _) g16
  obtain ⟨hdm6, hbm6, -, -⟩ := bsAt hq6' (hsl.grow' hq g16)
  refine RefE.bindE (fun _ => icbE.k_block_tables.none ..) id
    (R.bt n _ q.env1 env₁ m6 a6 p0 _ _ bs bsP bs.members bsP.members hB6 hnPb hq6' ⟨hdm6, .inr hbm6⟩
      (ConRon.Bridge.Inductives.dShape_ext x06.ext _ _ hdP)
      (ConRon.Bridge.Inductives.dMember_ext.list x06.ext _ _ hms₀))
    fun ⟨r7, m7⟩ oQ a7 hrun7 h7 => ?_
  obtain ⟨h7, hts7⟩ := h7
  cases oQ with
  | none => rw [icbE.k_block_tables.abort1 _ _ _ _ _ _ _ _ hts7]; exact RefE.of_cls0 rfl
  | some Q =>
  obtain ⟨ht1, hdQ, hbQ⟩ := hts7
  rw [icbE.k_block_tables.arm1 _ _ _ _ _ _ _ _ (by rw [ht1]; decide)]
  simp only [ConRon.Arena.unwrapOr, pure_bind]
  -- the checks after it
  have g17 := g16.trans h7.grow
  have x07 := x06.trans h7.inst
  obtain ⟨hBP7, hSl7⟩ := h6.record.grow h6.shape h7.grow
  have hTb : TblsOK a7.store Q := by
    obtain ⟨ks, hks⟩ := lps_names_of_dShape (ConRon.Bridge.Inductives.dShape_ext x07.ext _ _ hdP)
    intro t ht
    obtain ⟨e1, e2⟩ := blockTables_tbls bs bs.members a6 a7 Q hrun7 t ht
    exact ⟨⟨ks, by rw [e1]; exact hks⟩, by rw [e2]; exact hnPb⟩
  refine RefE.bindE (fun _ => icbE.k_check_block_tail.none ..) id
    (R.tail n (by omega) _ env₁ m7 a7 bO bL _ block blockP q qP h7.st hBP7 hSl7
      (hblk.grow (decEBlk_mono _ _ _) g17) hbb
      (ConRon.Bridge.denoteCIList_mono x07.ext _ _ hbP) hlpd (hrel6.mono h7.inst.ext) henv₁
      (ConRon.Bridge.Inductives.dPass_ext h7.inst.ext hq6) hT6 henv₂ hMs hpl
      (by rw [checkBlockPass_nP hrun6]; exact hnPb) _ _ Q hdQ hbQ hTb)
    fun ⟨r8, m8⟩ fe₂ a8 _ h8 => ?_
  rw [icbE.k_check_block_tail.arm1]
  -- the block's recursors
  have g18 := g17.trans h8.grow
  have hq8 := hq.grow (decBS_mono _) g18
  obtain ⟨-, -, hrs8, -⟩ := bsAt hq8 (hsl.grow' hq g18)
  refine RefE.bindE (fun _ => icbE.k_block_recs.none ..) id
    (R.br n _ fe₂ m8 a8 p0 _ _ bs bs.recs h8.stage h8.mem hq8 hrs8) fun ⟨r9, m9⟩ recs a9 _ h9 => ?_
  obtain ⟨hS9, hM9, hg9, hd9, hb9⟩ := h9
  rw [icbE.k_block_recs.arm1]
  -- the install
  have g79 := h8.grow.trans hg9
  refine RefE.lastNone (fun _ => icbE.k_ifenv_push_delta.none ..) (fun _ => icbE.k_ifenv_push_delta.arm1 ..) id
    (R.pd n _ fe₂ m9 a9 _ _ _ _ recs Q hS9 hM9 hd9 hb9 (decPL_tbl_grow g79 hbQ hdQ)
      (Nat.le_trans hbQ g79.iw)) fun ⟨r10, m10⟩ h10 => ?_
  obtain ⟨-, hS10, hM10, hg10⟩ := h10
  exact ⟨hS10, hM10.core, ((g18.trans hg9).trans hg10), hM10.ind⟩

/-- **`check_block`'s contract from its callees'.** -/
theorem blockRefS_of (R : CbRefs G p dn) (hGnv : G → closedNV p _root_.L.Checker.nvFns = true) :
    BlockRefS G p dn := by
  intro n hn vis bO bL p0 fe env m a a₀ bs bsP block blockP hC hfold hx _ hq hsl hblk hbb hbP hdP hd
    hlpd hnPb hIM hA
  have h := RefE.ofCallE (s₀ := ⟨m, Locals.init []⟩) (icbE_spec p R.look n _ vis bO bL p0) hGnv
    (cb_ref R hC hfold hx hq hsl hblk hbb hbP hdP hd hlpd hnPb hIM hA hn (N := n))
  exact L.Arena.RefE.mono h fun ⟨r, m'⟩ y a' h => by obtain ⟨s', hs', -, hR⟩ := h; simp only at hs'; subst hs'; exact hR

end comp

end L.Ind

end
