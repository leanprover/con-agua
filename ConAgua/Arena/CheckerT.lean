module

public import ConAgua.Arena.IndArmLps
public import ConAgua.Arena.DeclAndPinIndRef
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Checker.Fold
import all ConAgua.Arena.CheckerL
import all ConAgua.Arena.DeclStep
public import ConAgua.Arena.QuotAtT
public import ConAgua.Arena.KnotEntry
public import ConAgua.Arena.IndMemoFns
public import ConAgua.Arena.Checker

@[expose] public section

/-!
# Phase A under `StageT` (lane `loopt2`)

Phase A's step runs its callees from `StageT`: at each loop head the twin's invariants `TwinOK`
come from the fold's (`TwinFold`, con-ron's `FoldOK`) and the memory's half (`TwinMem`: three
sizes, the core's memos `CoreMemos`, the name decoder's readbacks), which the fold carries
(`LoopMem`, `CoreMemos`). The bracket's opening keeps `TwinOK` (`TwinOK.flush`, `TwinOK.enter`);
`install_value` and `check_decl`'s arms end with the stage relation at their environment and
`CoreMemos` (`iv_ref`, `cdt_ref`); the bracket's closing is a leaf (`LeafClosed`: it writes no
core memo); the whole step writes the loop's write set (`LoopClosed`), so `LoopMem` comes back.

`check_decl`'s arms run from `StageT` (`checkDeclThm_loopT`, `…Opaque…`, `…Defn…`, `…Axiom…`,
`…Quot…`), the inductive one through its contract `IndArmSpec` (lane `indproofs4`'s eventual top
theorem, a field of `LoopCallees`).

Beside `CoreMemos` the fold carries the inductive arm's memos `IndMemos` (`LoopT.lean`): the arm's
contract takes and gives them back; every other callee keeps them by the write set of `imFns`
with `consts_resolve_ffast` a trusted leaf (`IndMemoClosed`, `invoke_indMemos`).

Moved here from `Checker.lean` and `DeclStepGo.lean`: `install_step_go`, `install_step`,
`install_decl_step` and the fold (their `StageR`-only versions are gone).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt DeclAtF IndDeclAt CVAt dw decCIs)

local notation "V" => ConLeche.CheckMode.verified

open ConRon.Bridge (FoldOK PersDecl PExt PinsDenote PersPinSets)

/-! ## The inductive records -/

/-- Step functions whose write set the loop takes from the program (`StepIn`) beyond the texts'
lists: the inductive records' path (the `And` pin's test, the block's copy into `EREC`, the
inductive arm) and the definition arm (its gates' write sets are the texts'; the arm's own is
here). -/
def indFns : List FnName :=
  ["and_pin_ok", "ind_block_to_erec", "check_ind_decl", "check_decl_defn"]

/-- **The front's inductive blocks have the front's shape** (`FrontBlock`: the constants the
front's `installIndD` builds), a fact about the parsed records alone. -/
def FrontDecls (ds : Array IDeclaration) : Prop :=
  ∀ i (h : i < ds.size) b nP, ds[i] = .indDecl b nP → FrontBlock b

/-- **The block's level-parameter handles have decoder names**: `L.Ind.BlockLpsDn dn block`
(`Arena/IndArmLps.lean`), what `cid_ref` takes; the loop has it from `DeclsLpsDn`. -/
abbrev BlockLpsDnA (dn : NIdx → Option ConLeche.Name) (block : List IConstantInfo) : Prop :=
  L.Ind.BlockLpsDn dn block

/-- **Every inductive record's level-parameter handles have decoder names** (`BlockLpsDnA`), a
fact about the records and the loop's decoder alone: the loop's start discharges it from the
records' denotation and persistence in the start store, whose persistent names `dn` is
(`declsLpsDn_dnOf`, `LoopStart.lean`). -/
def DeclsLpsDn (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration) : Prop :=
  ∀ i (h : i < ds.size) b nP, ds[i] = .indDecl b nP → BlockLpsDnA dn b

/-- The program hypotheses phase A under `StageT` takes beyond `DeclCallees`: the core's entry
points (`KnotStageProg`), the leaves' and the loop's write sets, and for the inductive records the
`And` pin's inductive arm, the write set of `indFns` and the inductive arm's contract. -/
structure LoopCallees (dn : NIdx → Option ConLeche.Name) (p : Prog) : Prop
    extends DeclCallees dn p where
  knot : KnotStageProg p
  leaf : LeafClosed p
  loop : LoopClosed p
  andInd : AndPinIndProg p
  indIn : StepIn p indFns
  /-- The loop's callees outside the inductive arm keep the inductive memos (`IndMemoClosed`,
  with `consts_resolve_ffast` a leaf: its model `crfF`). -/
  indMemo : IndMemoClosed p
  /-- `Quot`'s `sortZ` name has a handle under `dn` (the quotient readers' precondition). -/
  quotDn : QuotDn dn

/-! ## Two triples on one call -/

theorem triple_and {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {s₀ : St}
    {Q R : List Word → St → Prop}
    (h1 : ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs ⦃fun r s' => Q r s'; ⊤⦄)
    (h2 : ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs ⦃fun r s' => R r s'; ⊤⦄) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs ⦃fun r s' => Q r s' ∧ R r s'; ⊤⦄ :=
  M.triple_of_run fun _ _ _ hs hrun =>
    ⟨M.of_run (P := fun s => s = s₀) hs hrun h1, M.of_run (P := fun s => s = s₀) hs hrun h2⟩

/-! ## `check_decl`'s model (its refinement: `DeclCheckT.lean`) -/

/-- **`check_decl_kind`'s unified model**: the arms and `check_ind_decl` through their runs (their
contracts read them). -/
l_model checkDeclKind_specE (p : Prog) (hf : p.lookup "check_decl_kind" = some checkDeclKindL)
  fns [hf ↦ checkDeclKindE]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`check_decl`'s unified model**: the inductive branch's block copy, the flush and the reserved
names' check (outside the verdict closure) lifted; `check_decl_kind` by its model. -/
l_model checkDecl_specE (p : Prog) (hf : p.lookup "check_decl" = some checkDeclL)
    (hk : p.lookup "check_decl_kind" = some checkDeclKindL)
  fns [hf ↦ checkDeclE]
  specs [callW_spec p n "ind_block_to_erec", checkDeclKind_specE p hk n, callW_spec p n "flush_caches",
    callW_spec p n "basis_names_ok", callW_spec p n "basis_names_error"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


end L.Arena
