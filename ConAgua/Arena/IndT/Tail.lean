module

public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConRon.Bridge.Inductives.BlockTail
import ConAgua.Checker.NoVerdictTree
public import ConRon.Bridge.Inductives.BlockTail
import all ConAgua.Arena.IndInstall
public import ConAgua.Arena.IndInstallSpec.Icvg
public import ConAgua.Arena.IndInstallSpec.GrcProg

@[expose] public section

/-!
# `check_block_tail`'s model and the stream half's contract (lane `ronsync2`, stage 3)

`ictlE`: `check_block_tail`'s unified model (the index sorts, the recursor stage, the stream half
and the tables through their calls; the members' constructors, their cons, the flush and the
nested bit lifted). `tailStreamT`: the twin's second half (the Rust's `check_block_tail_stream`),
`checkBlockTail_split` the twin at the L calls. `TsRefS`/`TsPost`: `check_block_tail_stream`'s
contract. The refinement is `IndT/TailRef`'s `tail_ref` (con-ron's `checkBlockTail_of`).
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
theorem checkBlockTail_split (mode : ConLeche.CheckMode) (block : List IConstantInfo) (q : BlockPass)
    (Q : List IProjTable) :
    ConRon.Arena.checkBlockTail mode block q Q = (do
      ConRon.Arena.checkBlockIdxSorts mode q.env1 q.p q.p.members
      let fe₂ := ConRon.Arena.consBlockCtors q.p.nP q.p.memberCtors q.env1
      ConRon.Arena.flushCaches
      let nested := ConRon.Arena.blockNestedBit q.p q.kinds
      let (fe₂b, out) ← ConRon.Arena.checkBlockRec mode fe₂ q.p nested q.params q.tbl q.rd q.cls block
      let fe₃ ← tailStreamT mode q.p fe₂b out
      ConRon.Arena.checkBlockTables fe₃ Q
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

end L.Ind

end
