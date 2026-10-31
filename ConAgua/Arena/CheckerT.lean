import ConAgua.Arena.LoopT
import ConAgua.Arena.IndArmLps
import ConAgua.Arena.DeclAndPinIndRef
import ConAgua.Arena.AndPinScratch
import ConAgua.Arena.DeclDefnT
import ConAgua.Arena.DeclAxQuotT
import ConAgua.Arena.DeclNatSubAll
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

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

/-- **The inductive arm's contract**: `check_ind_decl(vis, o, l, w)` on an inductive block copied
into `EREC` (`ind_block_to_erec`'s post: the slice `o`, `l` decoding to `block`, below the top),
from `StageT` and the twin's fold invariant, refines `checkDecl`'s `.indDecl` case, back to the
stage relation at the returned view, the core's memos well formed, the pools grown; the
inductive stage's memos (`IndMemos`: the stage memos, `instantiate1Lift`'s and
`consts_resolve_ffast`'s) well formed before and after. This is lane
`indproofs4`'s top theorem for phase 8 (the stage relation and the memos' well-formedness before
and after the arm), with the twin facts the loop has at the arm (`StateOK`, `FoldOK`, the record's
denotation, the block's front shape) added as premises; it is a field of `LoopCallees` until
that theorem lands. -/
def IndArmSpec (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (pins : List INatOpPinSet) (n : Nat), n ≤ 2 ^ 62 → ∀ (m m' : Mem) (a : AState) (vis : Word)
    (fe : IFEnv) (env : ConLeche.Env) (block : List IConstantInfo) (nP : Nat) (o l w : Word)
    (r : List Word), l.toNat = block.length → w.toNat = nP →
    decCIs (erecP m) dn o.toNat l.toNat = some block → o.toNat + l.toNat ≤ erTop m →
    FrontBlock block → StageT dn vis fe m a → ConRon.Bridge.StateOK a → FoldOK V env fe a →
    (∃ x, Frontend.denoteDecl a.store (.indDecl block nP) = some x) → BlockLpsDnA dn block →
    IndMemos m → callW p n "check_ind_decl" [vis, o, l, w] m = some (r, m') →
    ∃ fe' a', (checkDecl V pins fe (.indDecl block nP)).run a = .ok (fe', a') ∧
      StageR dn (r.headD 0) fe' m' a' ∧ CoreMemos m' ∧ IWGrow m m' ∧ IndMemos m'

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
  indArm : IndArmSpec p dn
  /-- The loop's callees outside the inductive arm keep the inductive memos (`IndMemoClosed`,
  with `consts_resolve_ffast` a leaf: its model `crfF`). -/
  indMemo : IndMemoClosed p
  crf : L.Ind.CrfF p
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

/-- **A leaf keeps `CoreMemos`** (its call closure writes no core memo, `LeafClosed`). -/
theorem triple_leafMemos {p : Prog} (hL : LeafClosed p) {f : FnName} (hf : f ∈ leafFns) {n : Nat}
    {vs : List Word} {s₀ : St} {Q : List Word → St → Prop}
    (h : ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs ⦃fun r s' => Q r s'; ⊤⦄)
    (hc : CoreMemos s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs ⦃fun r s' => Q r s' ∧ CoreMemos s'.mem; ⊤⦄ :=
  triple_post (triple_and h (invoke_memFrame hL n hf vs s₀)) fun _ _ ⟨hq, hf', _⟩ =>
    ⟨hq, hc.frame hf' leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp⟩

/-- `TwinOK` across a leaf. -/
theorem TwinOK.leaf {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {m m' : Mem} {a : AState}
    (h : TwinOK dn m a fe) (hf : MemFrame leafA leafC m m') : TwinOK dn m' a fe :=
  h.frame hf leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp

/-! ## `check_decl`'s arms under `StageT` -/

section arms
variable {p : Prog} (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration)

/-- The shape of an arm's spec at the loop's relation under `StageT`, for the record `d`: from
`StageT`, the twin's fold invariant, the record's and the pin variants' denotations, back to the
loop's relation and the core's memos. -/
def ArmSpecT (p : Prog) (f : FnName) (d : IDeclaration) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (i : Word), i.toNat < ds.size → ds[i.toNat]? = some d →
    ConRon.Bridge.StateOK a₀ → LoopR pins dn s₀.mem a₀ vis fe pend ds →
    StageT dn vis fe s₀.mem a₀ → (∃ env, FoldOK V env fe a₀) →
    (∃ x, Frontend.denoteDecl a₀.store d = some x) → (∃ pinsP, PinsDenote a₀.store pins pinsP) →
    L.Stubs.CrOK s₀.mem →
  ⦃fun s => s = s₀⦄ invoke p (exec p n) f [i, vis]
  ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkDecl V pins fe d) a₀ ∧
    LoopR pins dn s'.mem (AM.st (checkDecl V pins fe d) a₀) (r.headD 0)
      (AM.res (checkDecl V pins fe d) a₀) pend ds ∧ CoreMemos s'.mem; ⊤⦄

/-- **`check_decl_thm` under `StageT`** (`cdt_ref`'s ok half). -/
theorem checkDeclThm_loopT (hA : ArmProg p) (hV : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (hp : p.lookup "check_decl_thm" = some checkDeclThm) (cv : IConstantVal)
    (v : EIdx) :
    ArmSpecT pins dn ds p "check_decl_thm" (.thmDecl cv v) := by
  intro n hn s₀ a₀ vis fe pend i hi hd _ hR hS hF hden _ hCr
  have hd' : ds[i.toNat] = .thmDecl cv v := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨env, hF⟩ := hF
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl] at hx
  split at hx
  rotate_left
  · cases hx
  rename_i c e hc he
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, fe', a', hrun', hP⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (RefE.triple (checkDeclThm_specE p hV hp n s₀ i vis)
      (cdt_ref (pins := pins) hV hq hap hkp hn hS hR.decls hi hd' hF hc hCr))
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (hA.closed.memFrame n (f := "check_decl_thm") (by decide) [i, vis] s₀)
  subst hs
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok, ?_, hP.memos⟩
  rw [hst, hres]
  exact hR.of_step hP.stage hf (IWGrow.erecPExt hP.grow)

/-- **`check_decl_opaque` under `StageT`** (`cdo_ref`). -/
theorem checkDeclOpaque_loopT (hA : ArmProg p) (hV : ValProg p) (hC : CrpProg p)
    (hq : KnotStageProg p) (hcl : LeafClosed p) (hlc : LoopClosed p) (hap : ApdF p) (hkp : CrKeep p)
    (hdn : DnInj dn) (hp : p.lookup "check_decl_opaque" = some checkDeclOpaque) (cv : IConstantVal) (v : EIdx) :
    ArmSpecT pins dn ds p "check_decl_opaque" (.opaqueDecl cv v) := by
  intro n hn s₀ a₀ vis fe pend i hi hd _ hR hS hF hden _ hCr
  apply M.triple_of_run
  intro s r s' hs hrun
  have hd' : ds[i.toNat] = .opaqueDecl cv v := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨env, hF⟩ := hF
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl] at hx
  split at hx
  rotate_left
  · cases hx
  rename_i c e hc he
  obtain ⟨hloc, fe', a', hrun', hQ⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (RefE.triple (checkDeclOpaque_specE p hp n s₀ i vis)
      (cdo_ref (pins := pins) hV hC hq hcl hlc hap hkp hdn n hn hS hR.decls hi hd' hF hc he hCr))
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (hA.closed.memFrame n (f := "check_decl_opaque") (by decide) [i, vis] s₀)
  subst hs
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok, ?_, hQ.memos⟩
  rw [hst, hres]
  exact hR.of_step hQ.stage hf (IWGrow.erecPExt hQ.grow)

/-- **`check_decl_defn` under `StageT`** (`cdf_ref`: the structural-`Nat` gate and the
`Nat.div`-family pin gate under `StageC`). -/
@[refines_part ConRon.Arena.checkDecl "the definition arm, under StageT"]
theorem checkDeclDefn_loopT (hA : ArmProg p) (hV : ValProg p) (hG : DefnProgT p pins)
    (hq : KnotStageProg p) (hcl : LeafClosed p) (hlc : LoopClosed p) (hin : StepIn p indFns)
    (hap : ApdF p) (hkp : CrKeep p) (hdn : DnInj dn) (cv : IConstantVal) (v : EIdx)
    (hh : ConLeche.ReducibilityHint) :
    ArmSpecT pins dn ds p "check_decl_defn" (.defnDecl cv v hh) := by
  intro n hn s₀ a₀ vis fe pend i hi hd _ hR hS hF hden hPD hCr
  apply M.triple_of_run
  intro s r s' hs hrun
  have hd' : ds[i.toNat] = .defnDecl cv v hh := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨env, hF⟩ := hF
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl] at hx
  split at hx
  rotate_left
  · cases hx
  rename_i c e hc he
  obtain ⟨hloc, fe', a', hrun', hQ⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (RefE.triple (checkDeclDefn_specE p hG.df n s₀ i vis)
      (cdf_ref hA hV hG hq hcl hlc hap hkp hdn n hn hS hR.pinsets hR.decls hi hd' hF hc he hPD hCr))
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (hin.memFrame n (f := "check_decl_defn") (by decide) [i, vis] s₀)
  subst hs
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok, ?_, hQ.memos⟩
  rw [hst, hres]
  exact hR.of_step hQ.stage hf (IWGrow.erecPExt hQ.grow)

/-- **`check_decl_axiom` under `StageT`** (`cda_ref`'s ok half). -/
@[refines_part ConRon.Arena.checkDecl "the axiom arm, under StageT"]
theorem checkDeclAxiom_loopT (hA : ArmProg p) (hX : AxProg p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hap : ApdF p) (hkp : CrKeep p) (hdn : DnInj dn) (hQd : QuotDn dn)
    (cv : IConstantVal) :
    ArmSpecT pins dn ds p "check_decl_axiom" (.axiomDecl cv) := by
  intro n hn s₀ a₀ vis fe pend i hi hd hok hR hS hF hden _ hCr
  have hd' : ds[i.toNat] = .axiomDecl cv := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
  obtain ⟨c, hc, -⟩ := hx
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, fe', a', hrun', hP⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (RefE.triple (checkDeclAxiom_specE p hX n s₀ i vis)
      (cda_ref (pins := pins) hX hq hcl hap hkp hdn hQd hn hS hR.decls hi hd' hok hc hF hCr))
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (hA.closed.memFrame n (f := "check_decl_axiom") (by decide) [i, vis] s₀)
  subst hs
  obtain ⟨hok', hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok', ?_, hP.memos⟩
  rw [hst, hres]
  exact hR.of_step hP.stage hf (IWGrow.erecPExt hP.grow)

/-- **`check_decl_quot` under `StageT`** (`cdq_ref`'s ok half; the core's memos kept, the arm
being a leaf). -/
@[refines_part ConRon.Arena.checkDecl "the quotient arm, under StageT"]
theorem checkDeclQuot_loopT (hA : ArmProg p) (hQ : QuotProg p) (hRp : RecProg p)
    (hcl : LeafClosed p) (hdn : DnInj dn) (hQd : QuotDn dn) (k : ConLeche.QuotKind)
    (cv : IConstantVal) :
    ArmSpecT pins dn ds p "check_decl_quot" (.quotDecl k cv) := by
  intro n hn s₀ a₀ vis fe pend i hi hd hok hR hS _ hden _ _
  have hd' : ds[i.toNat] = .quotDecl k cv := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  have hcvD : ∃ c, Frontend.denoteCV a₀.store cv = some c := by
    obtain ⟨x, hx⟩ := hden
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
    obtain ⟨c, hc, -⟩ := hx
    exact ⟨c, hc⟩
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, fe', a', hrun', hR'⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (RefE.triple (checkDeclQuot_specE p hQ hRp n s₀ i vis)
      (cdq_ref (pins := pins) hQ hdn n hS.stage hR.decls hi hd' hok (hQd.namesDn hS.twin.mem) hcvD))
  obtain ⟨-, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun (callW_spec p n "check_decl_quot" [i, vis] s₀)
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (hA.closed.memFrame n (f := "check_decl_quot") (by decide) [i, vis] s₀)
  subst hs
  obtain ⟨hok', hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok', ?_, leaf_memos hcl (leaf_mem _ rfl) hW hS.twin.memos⟩
  rw [hst, hres]
  exact hR.of_step hR'.stage hf (IWGrow.erecPExt hR'.grow)

end arms

/-! ## `check_decl` under `StageT` -/

section cd
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

/-- **What `check_decl` refines under `StageT`**: `checkDecl` from the loop's relation and
`StageT`, back to the loop's relation and the core's memos. -/
def CheckDeclSpecT : Prop :=
    ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv)
      (pend : Array PendingCheck) (i : Word), i.toNat < ds.size → ConRon.Bridge.StateOK a₀ →
      LoopR pins dn s₀.mem a₀ vis fe pend ds → StageT dn vis fe s₀.mem a₀ →
      (∃ env, FoldOK V env fe a₀) → (∃ x, Frontend.denoteDecl a₀.store (dsAt ds i) = some x) →
      (∃ pinsP, PinsDenote a₀.store pins pinsP) → IndMemos s₀.mem →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_decl" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkDecl mode pins fe (dsAt ds i)) a₀ ∧
      LoopR pins dn s'.mem (AM.st (checkDecl mode pins fe (dsAt ds i)) a₀) (r.headD 0)
        (AM.res (checkDecl mode pins fe (dsAt ds i)) a₀) pend ds ∧ CoreMemos s'.mem ∧
      IndMemos s'.mem; ⊤⦄

end cd

/-- **`check_decl`'s unified model**: the inductive branch's block copy (outside the verdict
closure) lifted; the arms and `check_ind_decl` through their runs (their contracts read them). -/
l_model checkDecl_specE (p : Prog) (hf : p.lookup "check_decl" = some checkDeclL)
  fns [hf ↦ checkDeclE] specs [callW_spec p n "ind_block_to_erec"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- A call of a function with a step's write set (`StepIn`) keeps the memory outside it. -/
theorem stepIn_callW {p : Prog} {fs : List FnName} (h : StepIn p fs) {f : FnName} (hf : f ∈ fs)
    {n : Nat} {args : List Word} {m m' : Mem} {r : List Word}
    (hc : callW p n f args m = some (r, m')) : MemFrame stepA stepC m m' := by
  obtain ⟨s', hs', hfr, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (h.memFrame n hf args _) hc
  rw [← hs']; exact hfr

section cdRef
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/-- **The shape of an arm's error spec** (`ArmSpecT`'s error half): a failing run of the arm on
record `d` claims the twin's `checkDecl` failure from the same state. -/
def ArmSpecE (f : FnName) (d : IDeclaration) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a₀ : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (i : Word), i.toNat < ds.size → ds[i.toNat]? = some d →
    ConRon.Bridge.StateOK a₀ → LoopR pins dn m a₀ vis fe pend ds →
    StageT dn vis fe m a₀ → (∃ env, FoldOK V env fe a₀) →
    (∃ x, Frontend.denoteDecl a₀.store d = some x) → (∃ pinsP, PinsDenote a₀.store pins pinsP) →
    L.Stubs.CrOK m → ∀ e, callE p n f [i, vis] m = .error e →
    ErrClaim (checkDecl V pins fe d) a₀ e

/-- The arms' error claims, for every record of the kind. -/
structure ArmsE : Prop where
  axiom_ : ∀ cv, ArmSpecE pins dn ds p "check_decl_axiom" (.axiomDecl cv)
  defn : ∀ cv v hh, ArmSpecE pins dn ds p "check_decl_defn" (.defnDecl cv v hh)
  thm : ∀ cv v, ArmSpecE pins dn ds p "check_decl_thm" (.thmDecl cv v)
  opaque_ : ∀ cv v, ArmSpecE pins dn ds p "check_decl_opaque" (.opaqueDecl cv v)
  quot : ∀ k cv, ArmSpecE pins dn ds p "check_decl_quot" (.quotDecl k cv)

end cdRef

/-- **`check_ind_decl`'s error claim** (the inductive arm's contract, error half of
`IndArmSpec`): a failing run claims the twin's `checkDecl` failure. -/
def IndArmSpecE (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (pins : List INatOpPinSet) (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (vis : Word)
    (fe : IFEnv) (env : ConLeche.Env) (block : List IConstantInfo) (nP : Nat) (o l w : Word),
    l.toNat = block.length → w.toNat = nP →
    decCIs (erecP m) dn o.toNat l.toNat = some block → o.toNat + l.toNat ≤ erTop m →
    FrontBlock block → StageT dn vis fe m a → ConRon.Bridge.StateOK a → FoldOK V env fe a →
    (∃ x, Frontend.denoteDecl a.store (.indDecl block nP) = some x) → BlockLpsDnA dn block →
    IndMemos m → ∀ e, callE p n "check_ind_decl" [vis, o, l, w] m = .error e →
    ErrClaim (checkDecl V pins fe (.indDecl block nP)) a e

/-- What the error arms of `check_decl` assume: the arms' claims and the inductive arm's. -/
structure CdG (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
    (p : Prog) : Prop where
  arms : ArmsE pins dn ds p
  ind : IndArmSpecE p dn

/-- What `check_decl` gives besides the twin's run, a view `w` and the memory `m'`: the loop's
relation and the memos. -/
structure CdPost (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
    (pend : Array PendingCheck) (w : Word) (x : IFEnv) (m' : Mem) (a' : AState) : Prop where
  loop : LoopR pins dn m' a' w x pend ds
  core : CoreMemos m'
  ind : IndMemos m'

/-- An arm through its run: the ok half by its contract (`ArmSpecT`), the error half by its claim. -/
theorem cd_arm {p : Prog} {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {f : FnName} {d : IDeclaration} (hA : ArmSpecT pins dn ds p f d)
    (hE : CdG pins dn ds p → ArmSpecE pins dn ds p f d)
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {pend : Array PendingCheck} {i : Word} (hi : i.toNat < ds.size)
    (hd : ds[i.toNat]? = some d) (hok : ConRon.Bridge.StateOK a)
    (hR : LoopR pins dn m a vis fe pend ds) (hS : StageT dn vis fe m a)
    (hF : ∃ env, FoldOK V env fe a) (hden : ∃ x, Frontend.denoteDecl a.store d = some x)
    (hPD : ∃ pinsP, PinsDenote a.store pins pinsP) (hcl : IndMemoClosed p) (hcrf : L.Ind.CrfF p)
    (hf : f ∈ imFns) (hIM : IndMemos m) :
    RefE (CdG pins dn ds p) (checkDeclE.k_check_ind_decl p (callE p n f [i, vis] m))
      (checkDecl V pins fe d) a (fun v x a' => CdPost pins dn ds pend v.1 x v.2 a') := by
  rcases c : callE p n f [i, vis] m with e | ⟨r, m'⟩
  · rw [checkDeclE.k_check_ind_decl.none]
    exact fun hG => hE hG n hn m a vis fe pend i hi hd hok hR hS hF hden hPD hIM.cr e c
  rw [checkDeclE.k_check_ind_decl.arm1]
  have h1 := callW_of_callE c
  have hIM' := callW_indMemos hcl hcrf hf h1 hIM
  obtain ⟨s', hs', -, hok', hL, hc⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (hA n hn ⟨m, Locals.init []⟩ a vis fe pend i hi hd hok hR hS hF hden hPD hIM.cr) h1
  subst hs'
  exact RefE.ret (AM.run_of_ok _ _ hok') ⟨by simpa using hL, hc, hIM'⟩

/-- **`check_decl` refines `checkDecl` under `StageT`, both outcomes**, for the front's record
kinds: each arm by its `StageT` theorem and its claim (`CdG`), the inductive one by its contracts
(`IndArmSpec`, `IndArmSpecE`) after `ind_block_to_erec` copies the record's block into `EREC`
(`indBlockToErec_ok`; it writes only `EREC` and its top, so `TwinOK` and the pin flag stay); the
loop's relation after it by the write set of `indFns`. -/
theorem cd_ref {p : Prog} (hP : CheckDeclProg p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hlc : LoopClosed p) (hib : IbeProg p) (hin : StepIn p indFns)
    (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (hdn : DnInj dn)
    (hQd : QuotDn dn) (hia : IndArmSpec p dn) (hicl : IndMemoClosed p) (hcrf : L.Ind.CrfF p)
    (ds : Array IDeclaration) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds)
    {N : Nat} (hN : N ≤ 2 ^ 62 + 1) {m : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {pend : Array PendingCheck} {i : Word} (hi : i.toNat < ds.size) (hok : ConRon.Bridge.StateOK a)
    (hR : LoopR pins dn m a vis fe pend ds) (hS : StageT dn vis fe m a)
    (hF : ∃ env, FoldOK V env fe a) (hden : ∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x)
    (hPD : ∃ pinsP, PinsDenote a.store pins pinsP) (hIM : IndMemos m) :
    RefE (CdG pins dn ds p) (checkDeclE p N m i vis) (checkDecl V pins fe (dsAt ds i)) a
      (fun v x a' => CdPost pins dn ds pend v.1 x v.2 a') := by
  have hdecl := hR.decls.recs i.toNat hi
  have hds : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
  have hd : ds[i.toNat]? = some ds[i.toNat] := Array.getElem?_eq_getElem hi
  rw [hds] at hden ⊢
  have h1 := hR.decls.room
  have h2 := hR.decls.dsize
  have hw0 : rdW (m.arr64 DECL) (1 + 8 * i) = dw (m.arr64 DECL) i.toNat 0 :=
    rdW_dw _ (by omega) (by decide) (by decide)
  rcases N with _ | n
  · rw [checkDeclE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  have hn' : n ≤ 2 ^ 62 := by omega
  generalize hdi : ds[i.toNat] = d at hdecl hd hden
  cases d with
  | axiomDecl cv =>
    rw [checkDeclE.arm2 _ _ _ _ _ (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1])]
    exact cd_arm (checkDeclAxiom_loopT pins dn ds hP.arm hP.axp hq hcl hP.crp.apd ⟨hicl, hcrf⟩ hdn hQd cv)
      (fun hG => hG.arms.axiom_ cv) hn' hi hd hok hR hS hF hden hPD hicl hcrf (im_mem _ rfl) hIM
  | defnDecl cv v hh =>
    rw [checkDeclE.arm3 _ _ _ _ _ (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1])]
    exact cd_arm (checkDeclDefn_loopT pins dn ds hP.arm hP.val
        ⟨hP.df, hP.natSub, hP.natGate, hP.natCert, hP.natText,
          divGateSpecC hP.dm hq hcl hP.dgClosed (substC0_of hP.natSub.toNatSubProg)
            (substCAll_of ⟨hP.natSub.toNatSubProg, hP.dm.lSubstConstAll⟩) ⟨hicl, hcrf⟩ pins⟩
        hq hcl hlc hin hP.crp.apd ⟨hicl, hcrf⟩ hdn cv v hh)
      (fun hG => hG.arms.defn cv v hh) hn' hi hd hok hR hS hF hden hPD hicl hcrf (im_mem _ rfl) hIM
  | thmDecl cv v =>
    rw [checkDeclE.arm4 _ _ _ _ _ (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1])]
    exact cd_arm (checkDeclThm_loopT pins dn ds hP.arm hP.val hq hP.crp.apd ⟨hicl, hcrf⟩ hP.th cv v)
      (fun hG => hG.arms.thm cv v) hn' hi hd hok hR hS hF hden hPD hicl hcrf (im_mem _ rfl) hIM
  | opaqueDecl cv v =>
    rw [checkDeclE.arm5 _ _ _ _ _ (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1])]
    exact cd_arm (checkDeclOpaque_loopT pins dn ds hP.arm hP.val hP.crp hq hcl hlc hP.crp.apd ⟨hicl, hcrf⟩ hdn
        hP.op cv v)
      (fun hG => hG.arms.opaque_ cv v) hn' hi hd hok hR hS hF hden hPD hicl hcrf (im_mem _ rfl) hIM
  | quotDecl k cv =>
    rw [checkDeclE.arm6 _ _ _ _ _ (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1])]
    exact cd_arm (checkDeclQuot_loopT pins dn ds hP.arm hP.quot hP.val.rcp hcl hdn hQd k cv)
      (fun hG => hG.arms.quot k cv) hn' hi hd hok hR hS hF hden hPD hicl hcrf (im_mem _ rfl) hIM
  | indDecl block nP =>
    rw [checkDeclE.arm1 _ _ _ _ _ (by rw [hw0, hdecl.1])]
    have hdecl' : IndDeclAt (m.arr64 DECL) (m.arr64 DLP) i.toNat block nP := by
      have := hR.decls.recs i.toNat hi
      rw [hdi] at this; exact this
    have hFB := hFD _ hi _ _ hdi
    have hlpd := hLD _ hi _ _ hdi
    have hD : (m.arr64 DECL).size < 2 ^ 63 := hR.decls.dsize
    have hP' : (m.arr64 DLP).size < 2 ^ 63 := hR.decls.psize
    refine RefE.onlySim (fun _ => checkDeclE.k_ind_block_to_erec.none ..) (fun _ _ h => h) fun r1 m1 c1 => ?_
    rw [checkDeclE.k_ind_block_to_erec.arm1]
    obtain ⟨hS1, hg1, hf1, -, hl1, hdec1, htop1⟩ := indBlockToErec_ok hib c1 hS.stage hdecl' hFB hD hP'
    have hT1 : StageT dn vis fe m1 a :=
      ⟨hS1, hS.twin.frame hf1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        by rw [pinW_frame hf1 (by decide)]; exact hS.flag⟩
    have hfs1 := stepIn_callW hin (by decide) c1
    have hIM1 : IndMemos m1 :=
      hIM.frame hf1 (fun b hb => by simp at hb; subst hb; decide) (fun x hx => by simp at hx; subst hx; decide)
    have hw : (rdW (m1.arr64 DECL) (5 + 8 * i)).toNat = nP := by
      rw [hf1.1 DECL (by decide) (by decide)]
      have h0 : dw (m.arr64 DECL) i.toNat 0 ≠ 0 := by rw [hdecl'.1]; decide
      rw [rdW_dwI hD h0 rfl (by decide)]
      exact hdecl'.2.1
    obtain ⟨env, hFo⟩ := hF
    rcases c2 : callE p n "check_ind_decl"
        [vis, r1.headD 0, r1.tail.headD 0, rdW (m1.arr64 DECL) (5 + 8 * i)] m1 with e2 | ⟨r2, m2⟩
    · rw [checkDeclE.k_check_ind_decl.none]
      exact fun hG => hG.ind pins n hn' m1 a vis fe env block nP _ _ _ hl1 hw hdec1 htop1 hFB hT1 hok hFo
        hden hlpd hIM1 e2 c2
    rw [checkDeclE.k_check_ind_decl.arm1]
    have d2 := callW_of_callE c2
    obtain ⟨fe', a', hrun, hS2, hcm, hg2, hIM2⟩ := hia pins n hn' m1 m2 a vis fe env block nP _ _ _ r2 hl1
      hw hdec1 htop1 hFB hT1 hok hFo hden hlpd hIM1 d2
    have hfs2 := stepIn_callW hin (by decide) d2
    exact RefE.ret hrun ⟨by simpa using hR.of_step hS2 (hfs1.trans hfs2) (IWGrow.erecPExt (hg1.trans hg2)),
      hcm, hIM2⟩
  | basisDecl _ => exact hdecl.elim

/-- **`check_decl` refines `checkDecl` under `StageT`**, for the front's record kinds: the ok half
of `cd_ref`. -/
@[refines_part ConRon.Arena.checkDecl "the front's records (kinds 1-6), under StageT, the inductive arm by IndArmSpec"]
theorem checkDecl_loopT {p : Prog} (hP : CheckDeclProg p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hlc : LoopClosed p) (hib : IbeProg p) (hin : StepIn p indFns)
    (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (hdn : DnInj dn)
    (hQd : QuotDn dn) (hia : IndArmSpec p dn) (hicl : IndMemoClosed p) (hcrf : L.Ind.CrfF p)
    (ds : Array IDeclaration) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) :
    CheckDeclSpecT V pins dn ds p := by
  intro n hn s₀ a₀ vis fe pend i hi hok hR hS hF hden hPD hIM
  refine triple_post (RefE.triple (checkDecl_specE p hP.cd n s₀ i vis)
    (cd_ref hP hq hcl hlc hib hin pins dn hdn hQd hia hicl hcrf ds hFD hLD (by omega) hi hok hR hS hF hden hPD
      hIM)) ?_
  rintro r s' ⟨hl, x, a', run, hR'⟩
  obtain ⟨hok', hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok', by rw [hst, hres]; exact hR'.loop, hR'.core, hR'.ind⟩

/-! ## `install_value` and `install_step_go` under `StageT` -/

/-- A record `install_value` takes (`IvArgs`) whose declaration denotes has its constant denote. -/
theorem ivArgs_denoteCV {st : EStore} {ck vk : Word} {d : IDeclaration} (hk : IvArgs ck vk d)
    {x : ConLeche.Declaration} (h : Frontend.denoteDecl st d = some x) :
    ∃ c, Frontend.denoteCV st (stepCV d) = some c := by
  cases d with
  | defnDecl cv v hh | thmDecl cv v | opaqueDecl cv v =>
    simp only [Frontend.denoteDecl] at h
    split at h
    · rename_i c _ hc _
      exact ⟨c, hc⟩
    · cases h
  | axiomDecl _ | quotDecl _ _ | indDecl _ _ | basisDecl _ => exact hk.elim

/-! ## The callees' specs at the loop's relation -/

section loopSpecs
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

/-- **`install_value` refines `ivT`** under `StageT`, at the loop's relation (`iv_ref`). -/
theorem installValue_loopT (hP : IvProg p) (hC : CvgProg p) (hap : ApdF p) (hkp : CrKeep p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
      (i ck vk : Word), i.toNat < ds.size → IvArgs ck vk (dsAt ds i) →
      LoopR pins dn s₀.mem a₀ vis fe pend ds → StageT dn vis fe s₀.mem a₀ →
      (∃ env, FoldOK V env fe a₀) → (∃ x, Frontend.denoteDecl a₀.store (dsAt ds i) = some x) →
      L.Stubs.CrOK s₀.mem →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_value" [i, vis, ck, vk]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ivT fe (dsAt ds i)) a₀ ∧
      LoopR pins dn s'.mem (AM.st (ivT fe (dsAt ds i)) a₀) (r.headD 0)
        (AM.res (ivT fe (dsAt ds i)) a₀).1 pend ds ∧
      (AM.res (ivT fe (dsAt ds i)) a₀).2 = decVG (erecP s'.mem) (r.tail.headD 0).toNat ∧
      (AM.res (ivT fe (dsAt ds i)) a₀).2 ≠ none ∧ CoreMemos s'.mem; ⊤⦄ := by
  intro n s₀ a₀ vis fe pend i ck vk hi hk hR hS hF hden hCr
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, x, a', hrun', hQ⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (RefE.triple (installValue_specE p hP n s₀ i vis ck vk)
      (iv_ref hP.recP hC hap hkp n hS hR.decls hi hk hF (ivArgs_denoteCV hk hden.choose_spec) hCr))
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (hP.closed.memFrame n (f := "install_value") (by decide) [i, vis, ck, vk] s₀)
  subst hs
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok, ?_, by rw [hres]; exact hQ.vg, by rw [hres]; exact hQ.some, hQ.memos⟩
  rw [hst, hres]
  exact hR.of_step hQ.stage hf (IWGrow.erecPExt hQ.grow)

end loopSpecs

/-- **`install_step_go`'s unified model**: the scratch reset and the pin test (outside the verdict
closure) lifted, `check_decl` by its unified model, `install_value` through its run (the inductive
memos read it). -/
l_model installStepGo_specE (p : Prog) (hG : IstgProg p) (hcd : p.lookup "check_decl" = some checkDeclL)
  fns [hG.go ↦ installStepGoE]
  specs [callW_spec p n "iw_reset", callW_spec p n "pin_in", checkDecl_specE p hcd n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 1600000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


/-! ## `install_step_go` refines `installStepGo`, both outcomes -/

section istg
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/-- What the error arms of `install_step_go` assume: `check_decl`'s (`CdG`) and `install_value`'s
(`IvCtx`). -/
structure IstgG : Prop where
  cd : CdG pins dn ds p
  iv : IvCtx p

/-- What `install_step_go` gives besides the twin's run, its three words `r` and the memory `m'`:
the loop's relation at the new view and environment, the value group out of the flag and record,
the memos. -/
structure IstgPost (pend : Array PendingCheck) (r : List Word) (x : IFEnv × Option ValueGroup) (m' : Mem)
    (a' : AState) : Prop where
  loop : LoopR pins dn m' a' (r.headD 0) x.1 pend ds
  vg : x.2 = vgOut m' (r.tail.headD 0) (r.tail.tail.headD 0)
  some : r.tail.headD 0 ≠ 0 → x.2 ≠ none
  core : CoreMemos m'
  ind : IndMemos m'

variable {pins dn ds p}

/-- The `check_decl` branch: `cd_ref`, against a twin that runs as `cdT`. -/
theorem istg_cd {n : Nat} {m0 : Mem} {a : AState} {vis : Word} {fe : IFEnv} {pend : Array PendingCheck}
    {i : Word} {d : IDeclaration} {T : AM (IFEnv × Option ValueGroup)}
    (h : RefE (CdG pins dn ds p) (checkDeclE p n m0 i vis) (checkDecl V pins fe d) a
      (fun v x a' => CdPost pins dn ds pend v.1 x v.2 a'))
    (hT : T.run a = (cdT V pins fe d).run a) :
    RefE (IstgG pins dn ds p) (installStepGoE.k_check_decl p (checkDeclE p n m0 i vis)) T a
      (fun v x a' => IstgPost pins dn ds pend v.1 x v.2 a') := by
  rcases hx : checkDeclE p n m0 i vis with e | ⟨w, m'⟩
  · rw [installStepGoE.k_check_decl.none]
    rw [hx] at h
    exact fun hG => ErrClaim.of_run_eqW hT (ErrClaim.bind_left (h hG.cd))
  rw [installStepGoE.k_check_decl.arm1]
  rw [hx] at h
  obtain ⟨y, a', hy, hR⟩ := h
  exact RefE.ret (hT.trans (cdT_run hy)) ⟨by simpa using hR.loop, by simp [vgOut], by simp, hR.core, hR.ind⟩

/-- The `install_value` branch: `iv_ref` on the call's run, against a twin that runs as `ivT`. -/
theorem istg_iv (hP : IvProg p) (hC : CvgProg p) (hcl : IndMemoClosed p) (hcrf : L.Ind.CrfF p)
    (hap : ApdF p) {n : Nat} {m0 : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {pend : Array PendingCheck} {i ck vk : Word}
    {T : AM (IFEnv × Option ValueGroup)} (hi : i.toNat < ds.size) (hk : IvArgs ck vk (dsAt ds i))
    (hR : LoopR pins dn m0 a vis fe pend ds) (hS : StageT dn vis fe m0 a) (hIM : IndMemos m0)
    (hF : ∃ env, FoldOK V env fe a) (hden : ∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x)
    (hT : T.run a = (ivT fe (dsAt ds i)).run a) :
    RefE (IstgG pins dn ds p) (installStepGoE.k_install_value p (callE p n "install_value" [i, vis, ck, vk] m0))
      T a (fun v x a' => IstgPost pins dn ds pend v.1 x v.2 a') := by
  have hT8 := installValue_specE p hP n ⟨m0, Locals.init []⟩ i vis ck vk
  have hR8 := iv_ref hP.recP hC hap ⟨hcl, hcrf⟩ n hS hR.decls hi hk hF (ivArgs_denoteCV hk hden.choose_spec)
    hIM.cr
  rcases c : callE p n "install_value" [i, vis, ck, vk] m0 with e | ⟨rv, m'⟩
  · rw [installStepGoE.k_install_value.none]
    exact fun hG => ErrClaim.of_run_eqW hT (RefE.run_err hT8 hG.iv.nv hG.iv hR8 c)
  rw [installStepGoE.k_install_value.arm1]
  have hc := callW_of_callE c
  have hIM' := callW_indMemos hcl hcrf (im_mem _ rfl) hc hIM
  obtain ⟨s', hs', -, hok, hL, hvg, hne, hcm⟩ := triple_of_callW (s₀ := ⟨m0, Locals.init []⟩)
    (installValue_loopT pins dn ds p hP hC hap ⟨hcl, hcrf⟩ n ⟨m0, Locals.init []⟩ a vis fe pend i ck vk
      hi hk hR hS hF hden hIM.cr) hc
  have hrun := AM.run_of_ok _ _ hok
  subst hs'
  refine RefE.ret (hT.trans hrun) ⟨by simpa using hL, ?_, fun _ => hne, hcm, hIM'⟩
  simp only [List.headD_cons, List.tail_cons, vgOut, show (1 : Word) ≠ 0 by decide, ite_false]
  exact hvg

/-- **`install_step_go` refines `installStepGo` under `StageT`, both outcomes**: the scratch reset,
then by the record's kind (and for the pinnable ones `pin_in`'s answer) `check_decl` (`cd_ref`, its
model inlined) or `install_value` (`iv_ref` on the run). -/
theorem istg_ref (hdc : LoopCallees dn p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) {N : Nat}
    (hN : N ≤ 2 ^ 62 + 1) {m : Mem} {a : AState} {vis : Word} {fe : IFEnv} {pend : Array PendingCheck}
    {i : Word} (hi : i.toNat < ds.size) (hok0 : ConRon.Bridge.StateOK a) (hFo : ∃ env, FoldOK V env fe a)
    (hR : LoopR pins dn m a vis fe pend ds) (hTw : TwinOK dn m a fe) (hfl : pinW m 0 ≠ 0)
    (hden : ∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x)
    (hPD : ∃ pinsP, PinsDenote a.store pins pinsP) (hIM : IndMemos m) :
    RefE (IstgG pins dn ds p) (installStepGoE p N m i vis) (installStepGo V pins fe (dsAt ds i)) a
      (fun v x a' => IstgPost pins dn ds pend v.1 x v.2 a') := by
  rcases N with _ | n
  · rw [installStepGoE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [installStepGoE.arm1]
  refine RefE.onlySim (fun _ => installStepGoE.k_iw_reset.none ..) (fun _ _ h => h) fun r0 m0' c0 => ?_
  obtain ⟨s0, hs0, -, hW0⟩ := triple_of_callW (iwReset_specW p hdc.istg.reset n ⟨m, Locals.init []⟩) c0
  rw [show iwResetW m = some ([], m.set64 CTL 200 0) from rfl] at hW0
  simp only [Option.some.injEq, Prod.mk.injEq] at hW0
  obtain ⟨-, hm0⟩ := hW0
  have hm0' : m0' = m.set64 CTL 200 0 := hs0.symm.trans hm0.symm
  subst hm0'
  have hR0 := hR.reset
  have hS0 : StageT dn vis fe (m.set64 CTL 200 0) a :=
    ⟨⟨hR0.check, hR0.iw⟩,
      hTw.frame (MemFrame.setCtl m 200 0) ⟨by simp, by simp⟩ ⟨by decide, by decide⟩
        ⟨by simp, by simp, by simp⟩ ⟨by decide, by decide, by decide⟩ ⟨by simp, by simp, by simp⟩
        ⟨by decide, by decide, by decide⟩,
      by rw [pinW_frame (MemFrame.setCtl m 200 0) (by simp)]; exact hfl⟩
  have hIM0 := hIM.setCtl 200 0 (by decide)
  generalize m.set64 CTL 200 0 = m0 at hR0 hS0 hIM0 ⊢
  have hdecl : DeclAtF (m0.arr64 DECL) (m0.arr64 DLP) i.toNat (dsAt ds i) := by
    have := hR0.decls.recs i.toNat hi
    simpa [dsAt, Array.getD, hi] using this
  have h1 := hR0.decls.room
  have h2 := hR0.decls.dsize
  have hw0 : rdW (m0.arr64 DECL) (1 + 8 * i) = dw (m0.arr64 DECL) i.toNat 0 := by
    have : (1 + 8 * i).toNat = 1 + 8 * i.toNat + 0 := by
      rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
    simp [rdW, dw, this]
  have hw1 : rdW (m0.arr64 DECL) (2 + 8 * i) = dw (m0.arr64 DECL) i.toNat 1 := by
    have : (2 + 8 * i).toNat = 1 + 8 * i.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
    simp [rdW, dw, this]
  have hCD := cd_ref hdc.cd hdc.knot hdc.leaf hdc.loop hdc.andInd.toIbeProg hdc.indIn pins dn hdc.dninj hdc.quotDn
    hdc.indArm hdc.indMemo hdc.crf ds hFD hLD (N := n) (by omega) hi hok0 hR0 hS0 hFo hden hPD hIM0
  have hIV := fun {ck vk : Word} {T : AM (IFEnv × Option ValueGroup)} (hk : IvArgs ck vk (dsAt ds i))
      (hT : T.run a = (ivT fe (dsAt ds i)).run a) =>
    istg_iv (pend := pend) hdc.iv hdc.cvg hdc.indMemo hdc.crf hdc.cd.crp.apd (n := n) hi hk hR0 hS0 hIM0 hFo hden hT
  generalize hd : dsAt ds i = d at hdecl hCD hIV
  -- the pinned-name test, for the two pinnable kinds
  have pinT : ∀ {cv : IConstantVal} {k hi' c : Word}, CVAt (m0.arr64 DECL) (m0.arr64 DLP) i.toNat cv →
      pinInW n m0 (dw (m0.arr64 DECL) i.toNat 1 &&& 4294967295) k hi' = some c →
      1 ≤ k.toNat → k ≤ hi' → hi'.toNat ≤ 52 →
      PinsFull m0 a.pins ∧ ((c ≠ 0) ↔ ((List.range' k.toNat (hi'.toNat - k.toNat)).map
        fun j => (decI (pinW m0 j) : NIdx)).contains cv.name = true) := by
    intro cv k hi' c hcv hp hk1 hk hk2
    have hF := hR0.check.pins.full (pinInW_flag hp)
    refine ⟨hF, ?_⟩
    rw [pinIn_contains hF hp (mask_lt _) hk1 hk hk2, decI_mask, hcv.1]
  -- `pin_in` through its model
  have pinC : ∀ {k hi' : Word} {r : List Word} {m1 : Mem},
      callW p n "pin_in" [rdW (m0.arr64 DECL) (2 + 8 * i) &&& 4294967295, k, hi'] m0 = some (r, m1) →
      m1 = m0 ∧ pinInW n m0 (dw (m0.arr64 DECL) i.toNat 1 &&& 4294967295) k hi' = some (r.headD 0) := by
    intro k hi' r m1 hc
    obtain ⟨s', hs', -, hm', hW⟩ := triple_of_callW (s₀ := ⟨m0, Locals.init []⟩)
      (pinIn_specW p hdc.istg.pin n _ _ k hi') hc
    rw [hw1] at hW
    exact ⟨hs'.symm.trans hm', hW⟩
  cases d with
  | axiomDecl cv =>
    obtain ⟨hk, -⟩ := hdecl
    rw [installStepGoE.k_iw_reset.arm4 _ _ _ _ _ _ (by rw [hw0, hk]; decide) (by rw [hw0, hk]; decide)
      (by rw [hw0, hk]; decide)]
    exact istg_cd hCD rfl
  | quotDecl k cv =>
    obtain ⟨hk, -⟩ := hdecl
    rw [installStepGoE.k_iw_reset.arm4 _ _ _ _ _ _ (by rw [hw0, hk]; decide) (by rw [hw0, hk]; decide)
      (by rw [hw0, hk]; decide)]
    exact istg_cd hCD rfl
  | indDecl b nP =>
    have hk : dw (m0.arr64 DECL) i.toNat 0 = 6 := hdecl.1
    rw [installStepGoE.k_iw_reset.arm4 _ _ _ _ _ _ (by rw [hw0, hk]; decide) (by rw [hw0, hk]; decide)
      (by rw [hw0, hk]; decide)]
    exact istg_cd hCD rfl
  | thmDecl cv v =>
    obtain ⟨hk, -⟩ := hdecl
    rw [installStepGoE.k_iw_reset.arm2 _ _ _ _ _ _ (by rw [hw0, hk]; decide) (by rw [hw0, hk])]
    exact hIV ⟨rfl, rfl⟩ rfl
  | defnDecl cv v hint =>
    obtain ⟨hk, hcv, -⟩ := hdecl
    rw [installStepGoE.k_iw_reset.arm1 _ _ _ _ _ _ (by rw [hw0, hk])]
    refine RefE.onlySim (fun _ => installStepGoE.k_pin_in.none ..) (fun _ _ h => h) fun rp m1 cp => ?_
    obtain ⟨rfl, hp⟩ := pinC cp
    obtain ⟨hF, hiff⟩ := pinT hcv hp (by decide) (by decide) (by decide)
    rw [installStepGo]
    refine RefE.bind_right (natOpNames_run hF) (RefE.bind_right (natDivModNames_run hF) ?_)
    rw [pinnedDefn_contains]
    by_cases hc0 : rp.headD 0 ≠ 0
    · rw [installStepGoE.k_pin_in.arm1 _ _ _ _ _ _ hc0]
      exact RefE.ite_pos (hiff.mp hc0) (istg_cd hCD rfl)
    · rw [installStepGoE.k_pin_in.arm2 _ _ _ _ _ _ (Decidable.not_not.mp hc0)]
      exact RefE.ite_neg (mt hiff.mpr hc0) (hIV ⟨rfl, rfl⟩ rfl)
  | opaqueDecl cv v =>
    obtain ⟨hk, hcv, -⟩ := hdecl
    rw [installStepGoE.k_iw_reset.arm3 _ _ _ _ _ _ (by rw [hw0, hk]; decide) (by rw [hw0, hk]; decide)
      (by rw [hw0, hk])]
    refine RefE.onlySim (fun _ => installStepGoE.k_pin_in_2.none ..) (fun _ _ h => h) fun rp m1 cp => ?_
    obtain ⟨rfl, hp⟩ := pinC cp
    obtain ⟨hF, hiff⟩ := pinT hcv hp (by decide) (by decide) (by decide)
    rw [installStepGo]
    refine RefE.bind_right (reduceOpNames_run hF) ?_
    by_cases hc0 : rp.headD 0 ≠ 0
    · rw [installStepGoE.k_pin_in_2.arm1 _ _ _ _ _ _ hc0]
      exact RefE.ite_pos (hiff.mp hc0) (istg_cd hCD rfl)
    · rw [installStepGoE.k_pin_in_2.arm2 _ _ _ _ _ _ (Decidable.not_not.mp hc0)]
      exact RefE.ite_neg (mt hiff.mpr hc0) (hIV ⟨rfl, rfl⟩ rfl)
  | basisDecl _ => exact absurd hdecl id

end istg

/-! ## `install_step_go` refines `installStepGo` -/

section spec
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

/-- **`install_step_go` refines `installStepGo`** under `StageT` (the ok half of `istg_ref`): the
new view and environment, the value group out of the flag and record, the core's memos well
formed. -/
@[refines ConRon.Arena.installStepGo]
theorem installStepGo_specT (hm : mode = .verified) (hdc : LoopCallees dn p) (hFD : FrontDecls ds)
    (hLD : DeclsLpsDn dn ds) :
    ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv)
      (pend : Array PendingCheck) (i : Word) (_hi : i.toNat < ds.size), ConRon.Bridge.StateOK a₀ →
      (∃ env, FoldOK V env fe a₀) →
      LoopR pins dn s₀.mem a₀ vis fe pend ds → TwinOK dn s₀.mem a₀ fe → pinW s₀.mem 0 ≠ 0 →
      (∃ x, Frontend.denoteDecl a₀.store (dsAt ds i) = some x) →
      (∃ pinsP, PinsDenote a₀.store pins pinsP) → IndMemos s₀.mem →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_step_go" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installStepGo mode pins fe (dsAt ds i)) a₀ ∧
      LoopR pins dn s'.mem (AM.st (installStepGo mode pins fe (dsAt ds i)) a₀) (r.headD 0)
        (AM.res (installStepGo mode pins fe (dsAt ds i)) a₀).1 pend ds ∧
      (AM.res (installStepGo mode pins fe (dsAt ds i)) a₀).2 =
        vgOut s'.mem (r.tail.headD 0) (r.tail.tail.headD 0) ∧
      (r.tail.headD 0 ≠ 0 → (AM.res (installStepGo mode pins fe (dsAt ds i)) a₀).2 ≠ none) ∧
      CoreMemos s'.mem ∧ IndMemos s'.mem; ⊤⦄ := by
  subst hm
  intro n hn s₀ a₀ vis fe pend i _hi hok0 hF hR hTw hfl hden hPD hIM
  refine triple_post (RefE.triple (installStepGo_specE p hdc.istg hdc.cd.cd n s₀ i vis)
    (istg_ref hdc hFD hLD (by omega) _hi hok0 hF hR hTw hfl hden hPD hIM)) ?_
  rintro r s' ⟨hloc, x, a', hrun, hR'⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hloc, hok, by rw [hst, hres]; exact hR'.loop, by rw [hres]; exact hR'.vg,
    fun h => by rw [hres]; exact hR'.some h, hR'.core, hR'.ind⟩

end spec

/-! ## The bracket under `StageT`: `TwinOK` across the opening, `CoreMemos` across the closing -/

section bracket
variable (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration) (p : Prog)
  (hb : BracketProg p)
include hb

/-- **`flush_caches` keeps `TwinOK`** (and the loop's relation, the pin flag). -/
theorem flush_loopW {pins : List INatOpPinSet} (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word)
    (fe : IFEnv) (pend : Array PendingCheck) (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds)
    (hTw : TwinOK dn s₀.mem a₀ fe) (hfl : pinW s₀.mem 0 ≠ 0) (hIM : IndMemos s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "flush_caches" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok flushCaches a₀ ∧
      LoopR pins dn s'.mem (AM.st flushCaches a₀) vis fe pend ds ∧
      TwinOK dn s'.mem (AM.st flushCaches a₀) fe ∧ pinW s'.mem 0 ≠ 0 ∧ IndMemos s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hL⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (flush_loop dn ds p hb n s₀ a₀ vis fe pend hR)
  obtain ⟨-, -, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun (flushCaches_spec p hb.fl n s₀)
  subst hs
  have hf : MemFrame [PT0] flushCtl s.mem s'.mem := by rw [hm]; exact (flushMem_frame _).mono (by simp) (by simp)
  refine ⟨hloc, hok, hL, ?_, by rw [pinW_frame hf (by decide)]; exact hfl, hIM.frame hf (by decide)
    (fun x h => by simp [flushCtl] at h; rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)⟩
  rw [flushCaches_st]
  exact (hTw.frameLo hf (by decide) (fun x h => by simp [flushCtl] at h; rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)).flush

/-- **`scratch_enter` keeps `TwinOK`** from a loop head (the store well formed, the scratch tier
off). -/
theorem enter_loopW {pins : List INatOpPinSet} (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word)
    (fe : IFEnv) (pend : Array PendingCheck) (hwf : StoreWF a₀.store)
    (hoff : a₀.store.scratchOn = false) (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds)
    (hTw : TwinOK dn s₀.mem a₀ fe) (hfl : pinW s₀.mem 0 ≠ 0) (hIM : IndMemos s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "scratch_enter" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok enterScratch a₀ ∧
      LoopR pins dn s'.mem (AM.st enterScratch a₀) vis fe pend ds ∧
      TwinOK dn s'.mem (AM.st enterScratch a₀) fe ∧ pinW s'.mem 0 ≠ 0 ∧ IndMemos s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hL⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (enter_loop dn ds p hb n s₀ a₀ vis fe pend hR)
  obtain ⟨-, -, -, -, -, -, -, -, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchEnter_spec p hb.se hb.sr hb.bm hb.lf hb.im hb.fm n s₀)
  subst hs
  have hf : MemFrame scrArrs ((0 :: resetCtl) ++ memoCtl) s.mem s'.mem := by rw [hm]; exact enterMem_frame _
  refine ⟨hloc, hok, hL, ?_, by rw [pinW_frame hf (by decide)]; exact hfl, hIM.frame hf (by decide)
    (fun x h => by
      simp [resetCtl, scratchCnts, memoCtl, SCB] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        <;> decide)⟩
  rw [enterScratch_st]
  exact (hTw.frameLo hf (by decide) (fun x h => by
    simp [resetCtl, scratchCnts, memoCtl, SCB] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      <;> decide)).enter hwf hoff

end bracket

section leaves
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/-- `is_none` keeps the core's memos (a leaf). -/
theorem isNone_refinesC (hlc : LeafClosed p) (hcl : IndMemoClosed p) (hcrf : L.Ind.CrfF p)
    (hb : BracketProg p)
    (hp : p.lookup "is_none" = some isNoneL) (n : Nat) (s₀ : St) (a₀ : AState)
    (vis v2 nt : Word) (fe' : IFEnv) (pend : Array PendingCheck)
    (hR : LoopR pins dn s₀.mem a₀ v2 fe' pend ds) (hc : CoreMemos s₀.mem)
    (hIM : IndMemos s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "is_none" [vis, v2, nt]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (isNoneT vis.toNat nt.toNat fe' pend) a₀ ∧
      LoopR pins dn s'.mem (AM.st (isNoneT vis.toNat nt.toNat fe' pend) a₀) v2
        (AM.res (isNoneT vis.toNat nt.toNat fe' pend) a₀).1
        (AM.res (isNoneT vis.toNat nt.toNat fe' pend) a₀).2 ds ∧
      CoreMemos s'.mem ∧ IndMemos s'.mem; ⊤⦄ :=
  triple_post (triple_and (triple_leafMemos hlc (leaf_mem _ rfl)
      (isNone_refines pins dn ds p hb hp n s₀ a₀ vis v2 nt fe' pend hR) hc)
      (invoke_indMemos hcl hcrf n (im_mem _ rfl) _ s₀))
    fun _ _ ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩ => ⟨h1, h2, h3, h4, h5 hIM⟩

/-- `is_some` keeps the core's memos (a leaf). -/
theorem isSome_refinesC (hlc : LeafClosed p) (hcl : IndMemoClosed p) (hcrf : L.Ind.CrfF p)
    (hb : BracketProg p)
    (hpp : p.lookup "pend_push" = some pendPushL)
    (hp : p.lookup "is_some" = some isSomeL) (n : Nat) (s₀ : St) (a₀ : AState)
    (i vis v2 nt g : Word) (fe' : IFEnv) (pend : Array PendingCheck) (vg : ValueGroup)
    (hg : decVG (erecP s₀.mem) g.toNat = some vg)
    (hR : LoopR pins dn s₀.mem a₀ v2 fe' pend ds) (hc : CoreMemos s₀.mem)
    (hIM : IndMemos s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "is_some" [i, vis, v2, nt, g]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (isSomeT i.toNat vis.toNat nt.toNat fe' pend vg) a₀ ∧
      LoopR pins dn s'.mem (AM.st (isSomeT i.toNat vis.toNat nt.toNat fe' pend vg) a₀) v2
        (AM.res (isSomeT i.toNat vis.toNat nt.toNat fe' pend vg) a₀).1
        (AM.res (isSomeT i.toNat vis.toNat nt.toNat fe' pend vg) a₀).2 ds ∧ CoreMemos s'.mem ∧
      IndMemos s'.mem; ⊤⦄ :=
  triple_post (triple_and (triple_leafMemos hlc (leaf_mem _ rfl)
      (isSome_refines pins dn ds p hb hpp hp n s₀ a₀ i vis v2 nt g fe' pend vg hg hR) hc)
      (invoke_indMemos hcl hcrf n (im_mem _ rfl) _ s₀))
    fun _ _ ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩ => ⟨h1, h2, h3, h4, h5 hIM⟩

/-- `andPinOk` on a one-constant record (or a basis record) leaves the twin state alone. -/
theorem andPinOk_st_one {pd : IDeclaration} {a : AState} (hp : ConRon.Bridge.PinsOK a)
    (hpd : ∀ b k, pd ≠ .indDecl b k) (hok : AM.ok (andPinOk pd) a) : AM.st (andPinOk pd) a = a := by
  have hrun := AM.run_of_ok _ _ hok
  generalize AM.res (andPinOk pd) a = b at hrun
  generalize AM.st (andPinOk pd) a = a' at hrun ⊢
  cases pd with
  | indDecl b k => exact absurd rfl (hpd b k)
  | basisDecl _ =>
    simp only [andPinOk] at hrun
    exact (ConRon.Bridge.AM.pure_ok hrun).2
  | _ => exact ConRon.Bridge.andPinNameFree_run hp hrun

/-- **`and_pin_ok` keeps `TwinOK`** (a leaf), the pin flag, the scratch tier's flag and the
twin's fold invariant: on a one-constant record the twin state is unchanged; on an inductive block
(`andPinOkInd_refines`) the store grows (con-ron's `andPinOk_run`: `StateOK`, `Ext`, caches and
pins kept), so `TwinOK` by `TwinOK.of_grow` and `FoldOK` by `FoldOK.step`. -/
theorem andPinOk_refinesT (hlc : LeafClosed p) (hp : p.lookup "and_pin_ok" = some andPinOkL)
    (hai : AndPinIndProg p) (hrom : L.Rom.RomRefs p) (hin : StepIn p indFns) (hFD : FrontDecls ds)
    (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
    (i : Word) (hi : i.toNat < ds.size) (hok : ConRon.Bridge.StateOK a₀)
    (hpk : ConRon.Bridge.PinsOK a₀)
    (hoff : a₀.store.scratchOn = false) (hF : ∃ env, FoldOK V env fe a₀)
    (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds)
    (hTw : TwinOK dn s₀.mem a₀ fe) (hfl : pinW s₀.mem 0 ≠ 0)
    (hden : ∃ x, Frontend.denoteDecl a₀.store (dsAt ds i) = some x) (hpd : PersDecl (dsAt ds i))
    (hPD : ∃ pinsP, PinsDenote a₀.store pins pinsP) (hpps : PersPinSets pins)
    (hcl : IndMemoClosed p) (hcrf : L.Ind.CrfF p) (hIM : IndMemos s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "and_pin_ok" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (andPinOk (dsAt ds i)) a₀ ∧
      LoopR pins dn s'.mem (AM.st (andPinOk (dsAt ds i)) a₀) vis fe pend ds ∧
      AM.res (andPinOk (dsAt ds i)) a₀ = (r.headD 0 != 0) ∧
      TwinOK dn s'.mem (AM.st (andPinOk (dsAt ds i)) a₀) fe ∧ pinW s'.mem 0 ≠ 0 ∧
      (AM.st (andPinOk (dsAt ds i)) a₀).store.scratchOn = false ∧
      (∃ env, FoldOK V env fe (AM.st (andPinOk (dsAt ds i)) a₀)) ∧
      (∃ x, Frontend.denoteDecl (AM.st (andPinOk (dsAt ds i)) a₀).store (dsAt ds i) = some x) ∧
      (∃ pinsP, PinsDenote (AM.st (andPinOk (dsAt ds i)) a₀).store pins pinsP) ∧
      IndMemos s'.mem; ⊤⦄ := by
  have hI := invoke_indMemos hcl hcrf n (f := "and_pin_ok") (im_mem _ rfl) [i] s₀
  by_cases hind : ∃ b k, dsAt ds i = .indDecl b k
  · obtain ⟨b, k, e⟩ := hind
    have e' : ds[i.toNat] = .indDecl b k := by
      have : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
      rw [← this]; exact e
    have hdecl : IndDeclAt (s₀.mem.arr64 DECL) (s₀.mem.arr64 DLP) i.toNat b k := by
      have := hR.decls.recs i.toNat hi
      rw [e'] at this; exact this
    rw [e] at hden hpd ⊢
    refine triple_post (triple_and (triple_and
      (andPinOkInd_refines hai (hrom.andPin dn vis fe) i b k n s₀ a₀
        ⟨⟨hR.check, hR.iw⟩, hdecl, hFD _ hi _ _ e', hok, hR.decls.dsize, hR.decls.psize⟩)
      (invoke_memFrame hlc n (leaf_mem _ rfl) [i] s₀)) (triple_and (hin.memFrame n (by decide) [i] s₀) hI))
      fun r s' ⟨⟨⟨h1, h2, hS', hg, hdec⟩, hf, _⟩, ⟨hfs, _⟩, hIMf⟩ => ?_
    have hrun := AM.run_of_ok _ _ h2
    obtain ⟨x, hx⟩ := hden
    obtain ⟨hok', hext, hc, hpins⟩ := ConRon.Bridge.andPinOk_run hok hpk hx hrun
    obtain ⟨env, hFo⟩ := hF
    refine ⟨h1, h2, hR.of_step hS' hfs (IWGrow.erecPExt hg), hdec.1.symm,
      hTw.of_grow hok'.wf hext hc hpins (by rw [hf.size]; exact hTw.erec)
        (by rw [hf.size]; exact hTw.spn) (by rw [hf.size]; exact hTw.bstk)
        (hTw.memos.frame hf leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp), ?_,
      by rw [andPinOk_scratch hok hpk hrun]; exact hoff,
      ⟨env, hFo.step (hFo.check.mono hok' hext hc hpins) hext hpins⟩,
      ⟨x, ConRon.Bridge.denoteDecl_pext (PExt.of_ext hext) hpd hx⟩,
      hPD.imp fun q h => PinsDenote.pmono (PExt.of_ext hext) _ _ hpps h, hIMf hIM⟩
    simp only [pinW, hf.arr PINS leafA_pins (by decide)]; exact hfl
  have hpd' : ∀ b k, dsAt ds i ≠ .indDecl b k := fun b k e => hind ⟨b, k, e⟩
  refine triple_post (triple_and (andPinOk_refines (pins := pins) dn ds p hp n s₀ a₀ vis fe pend i hi hpd' hR)
    (triple_and (invoke_memFrame hlc n (leaf_mem _ rfl) [i] s₀) hI)) fun r s' ⟨⟨h1, h2, h3, h4⟩, ⟨hf, _⟩, hIMf⟩ => ?_
  have e := andPinOk_st_one hpk hpd' h2
  refine ⟨h1, h2, h3, h4, by rw [e]; exact hTw.leaf hf, ?_, by rw [e]; exact hoff,
    by rw [e]; exact hF, by rw [e]; exact hden, by rw [e]; exact hPD, hIMf hIM⟩
  simp only [pinW, hf.arr PINS leafA_pins (by decide)]; exact hfl

end leaves

/-! ## `install_step` and `install_decl_step`: one model and one refinement each -/

/-- **`install_step`'s unified model**: the table count, the flush, the bracket's opening and the
two promotions (outside the verdict closure) lifted; `install_step_go` by its unified model. -/
l_model installStep_specE (p : Prog) (hf : p.lookup "install_step" = some installStepL)
  (hG : IstgProg p) (hcd : p.lookup "check_decl" = some checkDeclL)
  fns [hf ↦ installStepE]
  specs [callW_spec p n "tbl_cnt", callW_spec p n "flush_caches", callW_spec p n "scratch_enter",
    installStepGo_specE p hG hcd n, callW_spec p n "is_none", callW_spec p n "is_some"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`install_decl_step`'s unified model**: the `And` pin (outside the verdict closure) lifted,
`install_step` by its unified model. -/
l_model installDeclStep_specE (p : Prog) (hf : p.lookup "install_decl_step" = some installDeclStepL)
  (hi : p.lookup "install_step" = some installStepL) (hG : IstgProg p)
  (hcd : p.lookup "check_decl" = some checkDeclL)
  fns [hf ↦ installDeclStepE]
  specs [callW_spec p n "and_pin_ok", installStep_specE p hi hG hcd n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `install_step` gives besides the twin's run, its view `r` and the memory `m'`: the loop's
relation at the new view, environment and pending list, the memos. -/
structure IstPost (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
    (ds : Array IDeclaration) (r : Word) (x : IFEnv × Array PendingCheck) (m' : Mem) (a' : AState) :
    Prop where
  loop : LoopR pins dn m' a' r x.1 x.2 ds
  core : CoreMemos m'
  ind : IndMemos m'

section ist
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
  {p : Prog}

/-- **`install_step` refines `installStep` under `StageT`, both outcomes**: the table count, the
flush and the bracket's opening keep `TwinOK`; `install_step_go` by `istg_ref` (its model
inlined); then the promotion of the value group's arm. -/
theorem ist_ref (hdc : LoopCallees dn p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds)
    (hb : BracketProg p) (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL) {N : Nat}
    (hN : N ≤ 2 ^ 62 + 1) {m : Mem} {a : AState} {i vis : Word} {fe : IFEnv}
    {pend : Array PendingCheck} (hi : i.toNat < ds.size) (hok : ConRon.Bridge.StateOK a)
    (hoff : a.store.scratchOn = false) (hR : LoopR pins dn m a vis fe pend ds)
    (hTw : TwinOK dn m a fe) (hfl : pinW m 0 ≠ 0) (hF : ∃ env, FoldOK V env fe a)
    (hden : ∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x) (hpd : PersDecl (dsAt ds i))
    (hPD : ∃ pinsP, PinsDenote a.store pins pinsP) (hpps : PersPinSets pins) (hIM : IndMemos m) :
    RefE (IstgG pins dn ds p) (installStepE p N m i vis)
      (installStep V pins i.toNat fe pend (dsAt ds i)) a
      (fun v x a' => IstPost pins dn ds v.1 x v.2 a') := by
  rcases N with _ | n
  · rw [installStepE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  rw [installStepE.arm1, installStep_eq]
  refine RefE.onlySim (fun _ => installStepE.k_tbl_cnt.none ..) (fun _ _ h => h) fun r0 m0 c0 => ?_
  rw [installStepE.k_tbl_cnt.arm1]
  obtain ⟨s0, rfl, hm0, -, hnt⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (tblCnt_spec p (hb.pr.get "tbl_cnt") n _) c0
  have hnt' : rdW (m.arr64 CTL) 133 = r0.headD 0 := hnt.symm
  rw [hm0]
  refine RefE.onlySim (fun _ => installStepE.k_flush_caches.none ..) (fun _ _ h => h) fun r1 m1 c1 => ?_
  rw [installStepE.k_flush_caches.arm1]
  obtain ⟨s1, rfl, -, hokF, hLF, hTF, hflF, hIMF⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (flush_loopW (pins := pins) dn ds p hb n _ a vis fe pend hR hTw hfl hIM) c1
  refine RefE.bind_right (AM.run_of_ok _ _ hokF) ?_
  have hwf' : StoreWF (AM.st flushCaches a).store := by rw [flushCaches_st]; exact hok.wf
  have hoff' : (AM.st flushCaches a).store.scratchOn = false := by rw [flushCaches_st]; exact hoff
  refine RefE.onlySim (fun _ => installStepE.k_scratch_enter.none ..) (fun _ _ h => h) fun r2 m2 c2 => ?_
  rw [installStepE.k_scratch_enter.arm1]
  obtain ⟨s2, rfl, -, hokE, hLE, hTE, hflE, hIME⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (enter_loopW (pins := pins) dn ds p hb n _ (AM.st flushCaches a) vis fe pend hwf' hoff' hLF hTF
      hflF hIMF) c2
  refine RefE.bind_right (AM.run_of_ok _ _ hokE) ?_
  have hFe : ∃ env, FoldOK V env fe (AM.st enterScratch (AM.st flushCaches a)) := by
    obtain ⟨env, h⟩ := hF
    exact ⟨env, by rw [enterScratch_st, flushCaches_st]; exact h.enter⟩
  have hde : ∃ x, Frontend.denoteDecl (AM.st enterScratch (AM.st flushCaches a)).store
      (dsAt ds i) = some x := by
    obtain ⟨x, h⟩ := hden
    exact ⟨x, by
      rw [enterScratch_st, flushCaches_st]
      exact ConRon.Bridge.denoteDecl_pext (PExt.enterScratch hok.wf) hpd h⟩
  have hPDe : ∃ pinsP, PinsDenote (AM.st enterScratch (AM.st flushCaches a)).store pins pinsP := by
    obtain ⟨q, h⟩ := hPD
    exact ⟨q, by
      rw [enterScratch_st, flushCaches_st]
      exact PinsDenote.pmono (PExt.enterScratch hok.wf) _ _ hpps h⟩
  have h3 := istg_ref (pend := pend) hdc hFD hLD (N := n) (by omega) hi (TwinFold.enterAM hok) hFe
    hLE hTE hflE hde hPDe hIME
  rcases c3 : installStepGoE p n s2.mem i vis with e3 | ⟨r3, m3⟩
  · rw [installStepE.k_install_step_go.none]
    rw [c3] at h3
    exact RefE.bind_left h3
  rw [c3] at h3
  obtain ⟨y, a3, hy, hP3⟩ := h3
  refine RefE.bind_right hy ?_
  rw [hR.vis, hR.check.env.tables_length, hnt']
  by_cases hf : r3.tail.headD 0 = 0
  · rw [installStepE.k_install_step_go.arm1 _ _ _ _ _ _ _ hf]
    have hy2 : y.2 = none := by simp only [hP3.vg, vgOut]; exact ite_eq_left hf
    rw [installStepK_none _ _ _ _ _ hy2]
    refine RefE.onlySim (fun _ => installStepE.k_is_none.none ..) (fun _ _ h => h) fun r4 m4 c4 => ?_
    rw [installStepE.k_is_none.arm1, installStepE.j1.arm1]
    obtain ⟨s4, rfl, -, hok4, hL4, hcm4, hIM4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (isNone_refinesC pins dn ds p hdc.leaf hdc.indMemo hdc.crf hb hpn n _ a3 vis (r3.headD 0)
        (r0.headD 0) y.1 pend hP3.loop hP3.core hP3.ind) c4
    exact RefE.ret (AM.run_of_ok _ _ hok4) ⟨hL4, hcm4, hIM4⟩
  · rw [installStepE.k_install_step_go.arm2 _ _ _ _ _ _ _ hf]
    obtain ⟨vg, hvg⟩ := Option.ne_none_iff_exists'.mp (hP3.some hf)
    have hg : decVG (erecP m3) (r3.tail.tail.headD 0).toNat = some vg := by
      rw [← hvg]; simp only [hP3.vg, vgOut]; exact (ite_eq_right hf).symm
    rw [installStepK_some _ _ _ _ _ vg hvg]
    rcases c4 : callW p n "is_some" [i, vis, r3.headD 0, r0.headD 0, r3.tail.tail.headD 0] m3 with
      _ | ⟨r4, m4⟩
    · rw [liftE_none, installStepE.k_is_none.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some, installStepE.k_is_none.arm1, installStepE.j1.arm1]
    obtain ⟨s4, rfl, -, hok4, hL4, hcm4, hIM4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (isSome_refinesC pins dn ds p hdc.leaf hdc.indMemo hdc.crf hb hpp hps n _ a3 i vis (r3.headD 0)
        (r0.headD 0) (r3.tail.tail.headD 0) y.1 pend vg hg hP3.loop hP3.core hP3.ind) c4
    exact RefE.ret (AM.run_of_ok _ _ hok4) ⟨hL4, hcm4, hIM4⟩

/-- **`install_decl_step` refines `installDeclStep` under `StageT`, both outcomes**: the twin
reports failures as values, so an ok value is the twin's `.ok` at the next position (with the step's
environment and pending list `x`) and an error the twin's failure, in the monad or as a value. A
rejected `And` pin is the twin's value failure at the position; `install_step` by `ist_ref` (its
model inlined). -/
theorem ids_ref (hdc : LoopCallees dn p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds)
    (hb : BracketProg p) (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL) {N : Nat}
    (hN : N ≤ 2 ^ 62 + 1) {m : Mem} {a : AState} {i vis : Word} {fe : IFEnv}
    {pend : Array PendingCheck} (hi : i.toNat < ds.size) (hT : TwinFold pins ds fe pend a)
    (hR : LoopR pins dn m a vis fe pend ds) (hTw : TwinOK dn m a fe) (hfl : pinW m 0 ≠ 0)
    (hIM : IndMemos m) :
    RefC (IstgG pins dn ds p) (installDeclStepE p N m i vis)
      (fun v => ∃ x a', (installDeclStep V pins (i.toNat, fe, pend) (dsAt ds i)).run a =
        .ok (.ok (i.toNat + 1, x), a') ∧ IstPost pins dn ds v.1 x v.2 a')
      (ErrClaimV (installDeclStep V pins (i.toNat, fe, pend) (dsAt ds i)) a) := by
  have hpk : ConRon.Bridge.PinsOK a := by obtain ⟨_, hF, _⟩ := hT.fold; exact hF.check.pins
  have hF0 : ∃ env, FoldOK V env fe a := by obtain ⟨env, hF, _⟩ := hT.fold; exact ⟨env, hF⟩
  have e0 : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
  have hden0 : ∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x := by
    rw [e0]; exact hT.denote hi
  have hpd : PersDecl (dsAt ds i) := by rw [e0]; exact hT.pd _ (by simp)
  rcases N with _ | n
  · rw [installDeclStepE.eq_1]; exact fun _ => ErrClaimV.of_cls0 Err.cls_outOfFuel
  rw [installDeclStepE.arm1]
  rcases c0 : callW p n "and_pin_ok" [i] m with _ | ⟨r0, m0⟩
  · rw [liftE_none, installDeclStepE.k_and_pin_ok.none]; exact fun _ => ErrClaimV.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s0, rfl, -, hokA, hLA, hresA, hTwA, hflA, hoffA, hFA, hdenA, hPDA, hIMA⟩ :=
    triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (andPinOk_refinesT pins dn ds p hdc.leaf hdc.and_pin_ok hdc.andInd hdc.cd.crp.red.rom hdc.indIn
        hFD n _ a vis fe pend i hi hT.stateOK hpk hT.off hF0 hR hTw hfl hden0 hpd hT.pinsD hT.pp
        hdc.indMemo hdc.crf hIM) c0
  have hrunA := AM.run_of_ok _ _ hokA
  by_cases hz : r0.headD 0 = 0
  · rw [installDeclStepE.k_and_pin_ok.abort1 p _ _ _ _ _ hz]
    have hres : AM.res (andPinOk (dsAt ds i)) a = false := by rw [hresA, hz]; rfl
    rw [hres] at hrunA
    refine fun _ _ => .inr ⟨.invalid "`And` must be the standard `And`", i.toNat, AState.abandoned, ?_, rfl⟩
    show (match (andPinOk (dsAt ds i)).run a with
      | .ok (true, s₁) => _
      | .ok (false, _) => _
      | .error e => _) = _
    rw [hrunA]
  rw [installDeclStepE.k_and_pin_ok.arm1 p _ _ _ _ _ hz]
  have hres : AM.res (andPinOk (dsAt ds i)) a = true := by rw [hresA]; exact bne_iff_ne.mpr hz
  rw [hres] at hrunA
  have hokA' : ConRon.Bridge.StateOK (AM.st (andPinOk (dsAt ds i)) a) := by
    rw [e0]; exact hT.andPinAM hi (by rw [← e0]; exact hokA)
  have h1 := ist_ref (pend := pend) hdc hFD hLD hb hpp hpn hps (N := n) (by omega) hi hokA' hoffA hLA
    hTwA hflA hFA hdenA hpd hPDA hT.pp hIMA
  have hrun : (installDeclStep V pins (i.toNat, fe, pend) (dsAt ds i)).run a =
      (match (installStep V pins i.toNat fe pend (dsAt ds i)).run (AM.st (andPinOk (dsAt ds i)) a) with
        | .ok ((fe', pend'), s') => .ok (.ok (i.toNat + 1, fe', pend'), s')
        | .error e => .ok (.error (e, i.toNat), AState.abandoned)) := by
    show (match (andPinOk (dsAt ds i)).run a with
      | .ok (true, s₁) => _
      | .ok (false, _) => _
      | .error e => _) = _
    rw [hrunA]; rfl
  rcases c1 : installStepE p n s0.mem i vis with e1 | ⟨r1, m1⟩
  · rw [c1] at h1
    refine fun hG hk0 => ?_
    obtain ⟨ce, hce, hcl⟩ := h1 hG hk0
    exact .inr ⟨ce, i.toNat, AState.abandoned, by rw [hrun, hce], hcl⟩
  rw [c1] at h1
  obtain ⟨⟨fe', pend'⟩, a', hx, hP⟩ := h1
  exact ⟨(fe', pend'), a', by rw [hrun, hx], hP⟩

end ist

/-! ## Phase A's step and fold under `StageT` -/

section skel
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

/-- **`install_step` refines `installStep`** under `StageT` (`ist_ref`'s ok half; the core's memos
come back). -/
@[refines ConRon.Arena.installStep]
theorem installStep_refines (hm : mode = .verified) (hdc : LoopCallees dn p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) (hb : BracketProg p) (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hp : p.lookup "install_step" = some installStepL) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (i vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (hi : i.toNat < ds.size)
    (hok : ConRon.Bridge.StateOK a₀) (hoff : a₀.store.scratchOn = false)
    (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds) (hTw : TwinOK dn s₀.mem a₀ fe)
    (hfl : pinW s₀.mem 0 ≠ 0) (hF : ∃ env, FoldOK V env fe a₀)
    (hden : ∃ x, Frontend.denoteDecl a₀.store (dsAt ds i) = some x) (hpd : PersDecl (dsAt ds i))
    (hPD : ∃ pinsP, PinsDenote a₀.store pins pinsP) (hpps : PersPinSets pins)
    (hIM : IndMemos s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_step" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ CoreMemos s'.mem ∧ IndMemos s'.mem ∧ AM.ok (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀ ∧
      LoopR pins dn s'.mem (AM.st (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀) (r.headD 0) (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀).1 (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀).2 ds; ⊤⦄ := by
  subst hm
  refine triple_post (RefE.triple (installStep_specE p hp hdc.istg hdc.cd.cd n s₀ i vis)
    (ist_ref hdc hFD hLD hb hpp hpn hps (by omega) hi hok hoff hR hTw hfl hF hden hpd hPD hpps hIM)) ?_
  rintro r s' ⟨hloc, x, a', hrun, hP⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hloc, hP.core, hP.ind, hok, by rw [hst, hres]; exact hP.loop⟩

/-- `install_decl_step` is one of the loop's functions. -/
theorem installDeclStep_loop : "install_decl_step" ∈ loopFns := loop_mem _ rfl

/-- **`install_decl_step` refines `installDeclStep`** under `StageT` (`ids_ref`'s ok half): a
returning run is the twin's `.ok` with the position advanced; the memory's half of the twin's
invariants (`LoopMem`, `CoreMemos`) comes back (the loop's write set, the twin's persistent tier only
growing). -/
@[refines ConRon.Arena.installDeclStep]
theorem installDeclStep_refines (hm : mode = .verified) (hb : BracketProg p) (hdc : LoopCallees dn p)
    (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds)
    (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hpi : p.lookup "install_step" = some installStepL)
    (hp : p.lookup "install_decl_step" = some installDeclStepL) (n : Nat) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState)
    (i vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (hi : i.toNat < ds.size)
    (hT : TwinFold pins ds fe pend a₀) (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds)
    (hM : LoopMem dn s₀.mem a₀) (hc : CoreMemos s₀.mem) (hIM : IndMemos s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_decl_step" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ x a', (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)).run a₀ =
        .ok (.ok (i.toNat + 1, x), a') ∧ LoopR pins dn s'.mem a' (r.headD 0) x.1 x.2 ds ∧
      LoopMem dn s'.mem a' ∧ CoreMemos s'.mem ∧ IndMemos s'.mem; ⊤⦄ := by
  subst hm
  have hTw : TwinOK dn s₀.mem a₀ fe := by
    obtain ⟨_, hF, _⟩ := hT.fold
    exact TwinOK.of_check hF.check ⟨hM.erec, hM.spn, hM.bstk, hc, fun k x e => (hM.dnP k x e).2⟩
  have h := ids_ref hdc hFD hLD hb hpp hpn hps (N := n) (by omega) hi hT hR hTw hM.flag hIM
  have ht := RefC.triple (installDeclStep_specE p hp hpi hdc.istg hdc.cd.cd n s₀ i vis) h
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hl, x, a', hrun', hP⟩ := M.of_run' (P := fun s => s = s₀) hs hrun ht
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (invoke_memFrame hdc.loop n installDeclStep_loop [i, vis] s₀)
  subst hs
  have e : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
  have hpx := (hT.step_pext hi (by rw [← e]; exact hrun')).2
  exact ⟨hl, x, a', hrun', hP.loop, hM.step hf hpx, hP.core, hP.ind⟩

theorem drop_cons_dsAt (ds : Array IDeclaration) (i : Word) (hi : i.toNat < ds.size)
    (h1 : (i + 1).toNat = i.toNat + 1) :
    ds.toList.drop i.toNat = dsAt ds i :: ds.toList.drop (i + 1).toNat := by
  rw [h1, List.drop_eq_getElem_cons (by simpa using hi)]
  simp [dsAt, hi]

/-- What `install_fold_go` from record `k` ends with: phase A's fold from `(k, fe, pend)` over the
records from `k` succeeds with every record installed, related to the memory `m` at view `v`. -/
def FoldPost (m : Mem) (a : AState) (v : Word) (k : Nat) (fe : IFEnv) (pend : Array PendingCheck) :
    Prop :=
  AM.ok (installFold mode pins (k, fe, pend) (ds.toList.drop k)) a ∧
    FoldOut pins dn m (AM.st (installFold mode pins (k, fe, pend) (ds.toList.drop k)) a) v ds
      (AM.res (installFold mode pins (k, fe, pend) (ds.toList.drop k)) a) ∧
    LoopMem dn m (AM.st (installFold mode pins (k, fe, pend) (ds.toList.drop k)) a) ∧ CoreMemos m ∧
    IndMemos m

/-- `install_fold_go`'s spec at fuel `n`. -/
def FoldGoSpec (n : Nat) : Prop :=
  ∀ (s₀ : St) (a₀ : AState) (i cnt vis : Word) (fe : IFEnv) (pend : Array PendingCheck),
    i.toNat ≤ ds.size → cnt.toNat = ds.size → TwinFold pins ds fe pend a₀ →
    LoopR pins dn s₀.mem a₀ vis fe pend ds → LoopMem dn s₀.mem a₀ → CoreMemos s₀.mem →
    IndMemos s₀.mem →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_fold_go" [i, cnt, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ FoldPost mode pins dn ds s'.mem a₀ (r.headD 0) i.toNat fe pend; ⊤⦄

/-! ## `install_fold_go` / `install_fold_next`: one model and one refinement -/

/-- **`install_fold_go`'s unified model** (`install_fold_next` through its run: the two are
mutually recursive). -/
l_model installFoldGo_specE (p : Prog) (hf : p.lookup "install_fold_go" = some installFoldGoL)
  fns [hf ↦ installFoldGoE] grind [arena_grind] unified

/-- **`install_fold_next`'s unified model** (`install_decl_step` and `install_fold_go` through their
runs: the fold's invariant reads the step's write set). -/
l_model installFoldNext_specE (p : Prog) (hf : p.lookup "install_fold_next" = some installFoldNextL)
  fns [hf ↦ installFoldNextE] grind [arena_grind] unified

/-- A record's step failure (in the monad or as a value) is the fold's failure. -/
theorem installFold_fails_head {pins : List INatOpPinSet}
    {q : Nat × IFEnv × Array PendingCheck} {d : IDeclaration} {rest : List IDeclaration}
    {a : AState} {c : Word} (h : TwinFailsV (installDeclStep mode pins q d) a c) :
    TwinFailsV (installFold mode pins q (d :: rest)) a c := by
  rcases h with ⟨ce, hce, hc⟩ | ⟨ce, k, a', hce, hc⟩
  · refine .inl ⟨ce, ?_, hc⟩
    simp only [installFold, StateT.run_bind, hce]; rfl
  · refine .inr ⟨ce, k, a', ?_, hc⟩
    simp only [installFold, StateT.run_bind, hce, exc_ok_bind]; rfl

/-- `install_fold_go`'s refinement at fuel `n`, both outcomes: from the fold's invariants at record
`i`, an ok value ends in `FoldPost`; an error claims that phase A over the records from `i` fails
(a record's failure, as a value). -/
def FoldGoRef (n : Nat) : Prop :=
  ∀ (m : Mem) (a₀ : AState) (i cnt vis : Word) (fe : IFEnv) (pend : Array PendingCheck),
    i.toNat ≤ ds.size → cnt.toNat = ds.size → TwinFold pins ds fe pend a₀ →
    LoopR pins dn m a₀ vis fe pend ds → LoopMem dn m a₀ → CoreMemos m → IndMemos m →
    RefC (IstgG pins dn ds p) (installFoldGoE p n m i cnt vis)
      (fun v => FoldPost mode pins dn ds v.2 a₀ v.1 i.toNat fe pend)
      (ErrClaimV (installFold mode pins (i.toNat, fe, pend) (ds.toList.drop i.toNat)) a₀)

/-- `install_fold_next`'s, the same (`i` below the count). -/
def FoldNextRef (n : Nat) : Prop :=
  ∀ (m : Mem) (a₀ : AState) (i cnt vis : Word) (fe : IFEnv) (pend : Array PendingCheck),
    i.toNat < ds.size → cnt.toNat = ds.size → TwinFold pins ds fe pend a₀ →
    LoopR pins dn m a₀ vis fe pend ds → LoopMem dn m a₀ → CoreMemos m → IndMemos m →
    RefC (IstgG pins dn ds p) (installFoldNextE p n m i cnt vis)
      (fun v => FoldPost mode pins dn ds v.2 a₀ v.1 i.toNat fe pend)
      (ErrClaimV (installFold mode pins (i.toNat, fe, pend) (ds.toList.drop i.toNat)) a₀)

section fold
variable (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hpi : p.lookup "install_step" = some installStepL)
    (hpd : p.lookup "install_decl_step" = some installDeclStepL)
    (hpg : p.lookup "install_fold_go" = some installFoldGoL)
    (hpx : p.lookup "install_fold_next" = some installFoldNextL) (hsz : ds.size < 2 ^ 63)
    (hb : BracketProg p) (hdc : LoopCallees dn p) (hm : mode = .verified) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds)
include hpp hpn hps hpi hpd hpg hpx hsz hb hdc hm hFD hLD

/-- **`install_fold_go` and `install_fold_next` refine `installFold` from record `i` on, both
outcomes**, by one induction on the fuel over the two models: `install_decl_step`'s ok run is the
twin's step (`installDeclStep_refines`), its failure the twin's step failure (`ids_ref`); the
rest's outcome is the induction hypothesis's. -/
theorem fold_ref (n : Nat) (hn : n ≤ 2 ^ 62) :
    FoldGoRef mode pins dn ds p n ∧ FoldNextRef mode pins dn ds p n := by
  subst hm
  induction n with
  | zero =>
    constructor <;> intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ <;>
      simp only [installFoldGoE, installFoldNextE, RefC_error] <;>
      exact fun _ => ErrClaimV.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  have ih := ih (by omega)
  have hn' : n ≤ 2 ^ 62 := by omega
  constructor
  · intro m a₀ i cnt vis fe pend hi hc hT hR hM hcm him
    by_cases g1 : i = cnt
    · rw [installFoldGoE.arm1 p n m i cnt vis g1]
      have e : ds.toList.drop i.toNat = [] := by simp [g1, hc]
      have := installFold_nil_ok .verified pins (i.toNat, fe, pend) a₀
      simp only [RefC_ok, FoldPost, e]
      refine ⟨this.1, ?_, ?_, hcm, him⟩
      · rw [this.2.1, this.2.2]; exact ⟨by rw [g1, hc], hR⟩
      · rw [this.2.1]; exact hM
    rw [installFoldGoE.arm2 p n m i cnt vis g1]
    have hlt : i.toNat < ds.size := by
      have : i.toNat ≠ cnt.toNat := fun e => g1 (UInt64.toNat_inj.mp e)
      omega
    have hs := installFoldNext_specE p hpx n ⟨m, Locals.init []⟩ i cnt vis
    have hr := ih.2 m a₀ i cnt vis fe pend hlt hc hT hR hM hcm him
    cases h1 : callE p n "install_fold_next" [i, cnt, vis] m with
    | error e1 =>
      rw [installFoldGoE.k_install_fold_next.none]
      exact fun hE => RefC.run_err hs (fun _ h0 => ErrClaimV.of_cls0 h0) trivial hE hr h1
    | ok q =>
      obtain ⟨r, m₁⟩ := q
      rw [installFoldGoE.k_install_fold_next.arm1]
      obtain ⟨s', rfl, -, hpost⟩ := RefC.run_ok hs hr h1
      exact hpost
  · intro m a₀ i cnt vis fe pend hi hc hT hR hM hcm him
    have h1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hd := drop_cons_dsAt ds i hi h1
    have e : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
    rw [installFoldNextE.arm1]
    cases hc1 : callE p n "install_decl_step" [i, vis] m with
    | error e1 =>
      rw [installFoldNextE.k_install_decl_step.none]
      intro hE hk0
      have hTw : TwinOK dn m a₀ fe := by
        obtain ⟨_, hF, _⟩ := hT.fold
        exact TwinOK.of_check hF.check ⟨hM.erec, hM.spn, hM.bstk, hcm, fun k x e => (hM.dnP k x e).2⟩
      rw [hd]
      exact installFold_fails_head .verified (RefC.run_err
        (installDeclStep_specE p hpd hpi hdc.istg hdc.cd.cd n ⟨m, Locals.init []⟩ i vis)
        (fun _ h0 => ErrClaimV.of_cls0 h0) hE.iv.nv hE
        (ids_ref hdc hFD hLD hb hpp hpn hps (N := n) (by omega) hi hT hR hTw hM.flag him) hc1 hk0)
    | ok q =>
    obtain ⟨r, m₁⟩ := q
    rw [installFoldNextE.k_install_decl_step.arm1]
    obtain ⟨s', hs', -, x, a', hrun, hR', hM', hcm', him'⟩ := triple_of_callE
      (installDeclStep_refines .verified pins dn ds p rfl hb hdc hFD hLD hpp hpn hps hpi hpd n hn'
        ⟨m, Locals.init []⟩ a₀ i vis fe pend hi hT hR hM hcm him) hc1
    subst hs'
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
    have hT' : TwinFold pins ds x.1 x.2 a' := (hT.step_pext hi (by rw [← e]; exact hrun)).1
    have hs := installFoldGo_specE p hpg n ⟨s'.mem, Locals.init []⟩ (i + 1) cnt (r.headD 0)
    have hr := ih.1 s'.mem a' (i + 1) cnt (r.headD 0) x.1 x.2 (by omega) hc hT' hR' hM' hcm' him'
    rw [h1] at hr
    cases hc2 : callE p n "install_fold_go" [i + 1, cnt, r.headD 0] s'.mem with
    | error e2 =>
      rw [installFoldNextE.k_install_fold_go.none]
      intro hE hk0
      have hf := RefC.run_err hs (fun _ h0 => ErrClaimV.of_cls0 h0) trivial hE hr hc2 hk0
      rw [hd, h1]
      have ec := installFold_cons .verified pins (i.toNat, fe, pend) (i.toNat + 1, x) (dsAt ds i)
        (ds.toList.drop (i.toNat + 1)) a₀ hok hres
      unfold TwinFailsV at hf ⊢
      rw [ec, hst]; exact hf
    | ok q2 =>
    obtain ⟨r2, m₂⟩ := q2
    rw [installFoldNextE.k_install_fold_go.arm1]
    obtain ⟨s'', rfl, -, hp⟩ := RefC.run_ok hs hr hc2
    obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := hp
    rw [← hst] at hp1 hp2 hp3
    have := installFold_cons_ok .verified pins (i.toNat, fe, pend) (i.toNat + 1, x) (dsAt ds i)
      (ds.toList.drop (i.toNat + 1)) a₀ hok hres hp1
    rw [h1] at hd
    refine ⟨?_, ?_, ?_, hp4, hp5⟩
    · rw [hd]; exact this.1
    · rw [hd, this.2.1, this.2.2]; exact hp2
    · rw [hd, this.2.1]; exact hp3

/-- **`install_fold_go` refines `installFold`** from record `i` on (`fold_ref`'s ok half). -/
@[refines ConRon.Arena.installFold]
theorem installFoldGo_refines (n : Nat) (hn : n ≤ 2 ^ 62) : FoldGoSpec mode pins dn ds p n := by
  intro s₀ a₀ i cnt vis fe pend hi hc hT hR hM hcm him
  exact (RefC.triple (installFoldGo_specE p hpg n s₀ i cnt vis)
    ((fold_ref mode pins dn ds p hpp hpn hps hpi hpd hpg hpx hsz hb hdc hm hFD hLD n hn).1
      s₀.mem a₀ i cnt vis fe pend hi hc hT hR hM hcm him) :)

end fold

end skel

end L.Arena
