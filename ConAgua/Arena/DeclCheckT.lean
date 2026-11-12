module

public import ConAgua.Arena.CheckerT
public import ConAgua.Arena.DeclCrpT
import all ConAgua.Arena.DeclStep
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.DeclDefnT
public import ConAgua.Arena.LoopT
public import ConAgua.Arena.DeclBasisNames
public import ConAgua.Arena.DeclKindTwin
import ConAgua.Arena.DeclKindEnvOne
import ConAgua.Arena.IndKindEnvProof
import ConRon.Bridge.Checker.Fold
import ConRon.Bridge.Checker.Hyp
import ConRon.Bridge.Inductives.Decl
import ConAgua.Arena.RecGenSpec.FlushStage
public import ConAgua.Arena.ScratchRefine

@[expose] public section

/-!
# `check_decl` refines `checkDecl`: the job's call (lane `ronsync2`, stage 3)

con-ron #143: a record's check is a job (`recordJob`, `StreamIndex.lean`): the `And` pin, then
`checkDecl mode pins (I.view k) pd`, in L `check_decl(k, 0)` (`record_job`, `CheckerL.lean`) at
the job relation `LoopR pins m a vis fe ds` (`DeclBase.lean`: the checker state at the own
layer's view `vis` of `fe`, the front's records, the pools, the pin variants), with the twin's
invariants `StageT` beside it.

* `CheckDeclSpecT`, `checkDecl_loopT`: the ok half, as a triple on `check_decl(i, vis)`.
* `cd_ref`: both outcomes (`RefE`): an ok run is the twin's with `CdPost` after it (the job
  relation at the returned view, the core's and the inductive arm's memos), a failing run claims
  the twin's failure under `CdG` (the arms' error claims and the inductive arm's).

Each one-constant arm runs from `ArmSpecT` (its ok half) and `ArmSpecE` (its error claim); the
inductive arm through its contracts `IndArmSpec`/`IndArmSpecE` (the inductive stage's top
theorems) after `ind_block_to_erec` copied the block into `EREC`.

The program facts are one bundle, `CdProg dn p`, so that the statements stay as they are while
the arms' proofs change what they take.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt DeclAtF IndDeclAt CVAt dw)

local notation "V" => ConLeche.CheckMode.verified

open ConRon.Bridge (FoldOK PinsDenote)

/-! ## The arms' contracts -/

section arms
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)

/-- **The shape of an arm's spec at the job relation under `StageT`**, for the record `d`: from
the job relation, `StageT`, the twin's fold invariant, the record's and the pin variants'
denotations and the inductive arm's memos, back to the job relation at the returned view and the
memos. -/
def ArmSpecT (p : Prog) (f : FnName) (d : IDeclaration) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv)
    (i : Word), i.toNat < ds.size → ds[i.toNat]? = some d →
    ConRon.Bridge.StateOK a₀ → LoopR pins s₀.mem a₀ vis fe ds →
    StageT dn vis fe s₀.mem a₀ → (∃ env, FoldOK env fe a₀) →
    (∃ x, Frontend.denoteDecl a₀.store d = some x) → (∃ pinsP, PinsDenote a₀.store pins pinsP) →
    IndMemos s₀.mem →
  ⦃fun s => s = s₀⦄ invoke p (exec p n) f [i, vis]
  ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkDeclKind V pins fe d) a₀ ∧
    LoopR pins s'.mem (AM.st (checkDeclKind V pins fe d) a₀) (r.headD 0)
      (AM.res (checkDeclKind V pins fe d) a₀) ds ∧ CoreMemos s'.mem ∧ IndMemos s'.mem ∧
    IWGrow s₀.mem s'.mem; ⊤⦄

/-- **The shape of an arm's error claim** (`ArmSpecT`'s error half): a failing run of the arm on
record `d` claims the twin's `checkDecl` failure from the same state. -/
def ArmSpecE (p : Prog) (f : FnName) (d : IDeclaration) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a₀ : AState) (vis : Word) (fe : IFEnv)
    (i : Word), i.toNat < ds.size → ds[i.toNat]? = some d →
    ConRon.Bridge.StateOK a₀ → LoopR pins m a₀ vis fe ds →
    StageT dn vis fe m a₀ → (∃ env, FoldOK env fe a₀) →
    (∃ x, Frontend.denoteDecl a₀.store d = some x) → (∃ pinsP, PinsDenote a₀.store pins pinsP) →
    IndMemos m → ∀ e, callE p n f [i, vis] m = .error e →
    ErrClaim (checkDeclKind V pins fe d) a₀ e

/-- The one-constant arms' contracts, ok halves. -/
structure ArmsT (p : Prog) : Prop where
  axiom_ : ∀ cv, ArmSpecT pins dn ds p "check_decl_axiom" (.axiomDecl cv)
  defn : ∀ cv v hh, ArmSpecT pins dn ds p "check_decl_defn" (.defnDecl cv v hh)
  thm : ∀ cv v, ArmSpecT pins dn ds p "check_decl_thm" (.thmDecl cv v)
  opaque_ : ∀ cv v, ArmSpecT pins dn ds p "check_decl_opaque" (.opaqueDecl cv v)
  quot : ∀ k cv, ArmSpecT pins dn ds p "check_decl_quot" (.quotDecl k cv)

/-- The one-constant arms' error claims. -/
structure ArmsE (p : Prog) : Prop where
  axiom_ : ∀ cv, ArmSpecE pins dn ds p "check_decl_axiom" (.axiomDecl cv)
  defn : ∀ cv v hh, ArmSpecE pins dn ds p "check_decl_defn" (.defnDecl cv v hh)
  thm : ∀ cv v, ArmSpecE pins dn ds p "check_decl_thm" (.thmDecl cv v)
  opaque_ : ∀ cv v, ArmSpecE pins dn ds p "check_decl_opaque" (.opaqueDecl cv v)
  quot : ∀ k cv, ArmSpecE pins dn ds p "check_decl_quot" (.quotDecl k cv)

end arms

/-! ## The one-constant arms -/

section armsT
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}

/-- **`check_decl_quot` under `StageT`** (`cdq_ref`'s ok half): the job relation after it by its
write set, the core's memos from `check_quot_record`, the inductive arm's by `imFns`' frame. -/
@[refines_part ConRon.Arena.checkDecl "the quotient arm, under StageT"]
theorem checkDeclQuot_loopT {p : Prog} (hQ : QuotArmProg p) (hQs : QuotSims p dn)
    (hin : StepIn p ["check_decl_quot"]) (hIc : IndMemoClosed p) (hIl : IndLeaves p)
    (k : ConLeche.QuotKind) (cv : IConstantVal) :
    ArmSpecT pins dn ds p "check_decl_quot" (.quotDecl k cv) := by
  intro n hn s₀ a₀ vis fe i hi hd hok hR hS hF hden _ hIM
  have hd' : ds[i.toNat] = .quotDecl k cv := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
  obtain ⟨c, hc, -⟩ := hx
  obtain ⟨env, hF⟩ := hF
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, fe', a', hrun', hP⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (RefE.triple (checkDeclQuot_specE p hQ.cdq hQ.rcp hQ.cqr.cqr hQ.cqr.basis n s₀ i vis)
      (cdq_ref (pins := pins) hQ hQs n hS hR.decls hi hd' hok hF.check.readOK hc))
  obtain ⟨-, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (callW_spec p n "check_decl_quot" [i, vis] s₀)
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (hin.memFrame n (f := "check_decl_quot") (by simp) [i, vis] s₀)
  subst hs
  obtain ⟨hok', hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok', ?_, hP.memos, callW_indMemos hIc hIl (im_mem _ rfl) hW hIM, hP.grow⟩
  rw [hst, hres]
  exact hR.of_step hP.stage hf (L.Ind.IWGrow.ext hP.grow)

/-- **`check_decl_axiom` under `StageT`** (`cda_ref`'s ok half): the job relation after it by its
write set, the core's memos from the arm's post, the inductive arm's by `imFns`' frame. -/
@[refines_part ConRon.Arena.checkDecl "the axiom arm, under StageT"]
theorem checkDeclAxiom_loopT {p : Prog} (hX : AxArmProg p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p)
    (hC : CcvSims p dn) (hQs : QuotSims p dn) (hdn : DnInj dn)
    (hin : StepIn p ["check_decl_axiom"]) (hIc : IndMemoClosed p) (hIl : IndLeaves p)
    (cv : IConstantVal) :
    ArmSpecT pins dn ds p "check_decl_axiom" (.axiomDecl cv) := by
  intro n hn s₀ a₀ vis fe i hi hd hok hR hS hF hden _ hIM
  have hd' : ds[i.toNat] = .axiomDecl cv := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
  obtain ⟨c, hc, -⟩ := hx
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, fe', a', hrun', hP⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (RefE.triple (checkDeclAxiom_specE p hX n s₀ i vis)
      (cda_ref (pins := pins) hX hq hcl hap hkp hcrf hC hQs hdn hn hS hR.decls hi hd' hok hc hF
        hIM.cr))
  obtain ⟨-, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (callW_spec p n "check_decl_axiom" [i, vis] s₀)
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (hin.memFrame n (f := "check_decl_axiom") (by simp) [i, vis] s₀)
  subst hs
  obtain ⟨hok', hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok', ?_, hP.memos, callW_indMemos hIc hIl (im_mem _ rfl) hW hIM, hP.grow⟩
  rw [hst, hres]
  exact hR.of_step hP.stage hf (L.Ind.IWGrow.ext hP.grow)

/-- **`check_decl_thm` under `StageT`** (`cdt_ref`'s ok half), as the axiom arm. -/
@[refines_part ConRon.Arena.checkDecl "the theorem arm, under StageT"]
theorem checkDeclThm_loopT {p : Prog} (hX : ThmArmProg p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p)
    (hC : CcvSims p dn) (hin : StepIn p ["check_decl_thm"]) (hIc : IndMemoClosed p)
    (hIl : IndLeaves p) (cv : IConstantVal) (v : EIdx) :
    ArmSpecT pins dn ds p "check_decl_thm" (.thmDecl cv v) := by
  intro n hn s₀ a₀ vis fe i hi hd hok hR hS hF hden _ hIM
  have hd' : ds[i.toNat] = .thmDecl cv v := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl] at hx
  obtain ⟨c, hc⟩ : ∃ c, Frontend.denoteCV a₀.store cv = some c := by
    revert hx; cases Frontend.denoteCV a₀.store cv <;> simp
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, fe', a', hrun', hP⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (RefE.triple (checkDeclThm_specE p hX n s₀ i vis)
      (cdt_ref (pins := pins) hX hq hcl hap hkp hcrf hC hn hS hR.decls hi hd' hc hF hIM.cr))
  obtain ⟨-, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (callW_spec p n "check_decl_thm" [i, vis] s₀)
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (hin.memFrame n (f := "check_decl_thm") (by simp) [i, vis] s₀)
  subst hs
  obtain ⟨hok', hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok', ?_, hP.memos, callW_indMemos hIc hIl (im_mem _ rfl) hW hIM, hP.grow⟩
  rw [hst, hres]
  exact hR.of_step hP.stage hf (L.Ind.IWGrow.ext hP.grow)

/-- **`check_decl_opaque` under `StageT`** (`cdo_ref`'s ok half), as the theorem arm. -/
@[refines_part ConRon.Arena.checkDecl "the opaque arm, under StageT"]
theorem checkDeclOpaque_loopT {p : Prog} (hX : OpqArmProg p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p)
    (hC : CcvSims p dn) (hin : StepIn p ["check_decl_opaque"]) (hIc : IndMemoClosed p)
    (hIl : IndLeaves p) (cv : IConstantVal) (v : EIdx) :
    ArmSpecT pins dn ds p "check_decl_opaque" (.opaqueDecl cv v) := by
  intro n hn s₀ a₀ vis fe i hi hd hok hR hS hF hden _ hIM
  have hd' : ds[i.toNat] = .opaqueDecl cv v := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨y, hy⟩ := hden
  simp only [Frontend.denoteDecl] at hy
  obtain ⟨c, hc⟩ : ∃ c, Frontend.denoteCV a₀.store cv = some c := by
    revert hy; cases Frontend.denoteCV a₀.store cv <;> simp
  obtain ⟨x, hx⟩ : ∃ x, denoteE a₀.store v = some x := by
    revert hy; rw [hc]; cases denoteE a₀.store v <;> simp
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, fe', a', hrun', hP⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (RefE.triple (checkDeclOpaque_specE p hX n s₀ i vis)
      (cdo_ref (pins := pins) hX hq hcl hap hkp hcrf hC hn hS hR.decls hi hd' hc hx hF hIM.cr))
  obtain ⟨-, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (callW_spec p n "check_decl_opaque" [i, vis] s₀)
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (hin.memFrame n (f := "check_decl_opaque") (by simp) [i, vis] s₀)
  subst hs
  obtain ⟨hok', hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok', ?_, hP.memos, callW_indMemos hIc hIl (im_mem _ rfl) hW hIM, hP.grow⟩
  rw [hst, hres]
  exact hR.of_step hP.stage hf (L.Ind.IWGrow.ext hP.grow)

/-- **`check_decl_defn` under `StageT`** (`cdf_ref`'s ok half), as the theorem arm; the variant
records from the job relation (`LoopR.pinsets`). -/
@[refines_part ConRon.Arena.checkDecl "the definition arm, under StageT"]
theorem checkDeclDefn_loopT {p : Prog} (hX : DefnProgT p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p)
    (hC : CcvSims p dn) (hin : StepIn p ["check_decl_defn"])
    (hIc : IndMemoClosed p) (hIl : IndLeaves p) (cv : IConstantVal) (v : EIdx)
    (hh : ConLeche.ReducibilityHint) :
    ArmSpecT pins dn ds p "check_decl_defn" (.defnDecl cv v hh) := by
  intro n hn s₀ a₀ vis fe i hi hd _ hR hS hF hden hPD hIM
  have hd' : ds[i.toNat] = .defnDecl cv v hh := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨y, hy⟩ := hden
  obtain ⟨c, x, hc, hx⟩ : ∃ c x, Frontend.denoteCV a₀.store cv = some c ∧
      denoteE a₀.store v = some x := by
    simp only [Frontend.denoteDecl] at hy
    revert hy
    cases Frontend.denoteCV a₀.store cv <;> cases denoteE a₀.store v <;> simp
  obtain ⟨env, hF⟩ := hF
  obtain ⟨pinsP, hPD⟩ := hPD
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, fe', a', hrun', hP⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (RefE.triple (checkDeclDefn_specE p hX n s₀ i vis)
      (cdf_ref hX hq hcl hap hkp hcrf hC hn hS hR.pinsets hR.decls hi hd' hF hc hx hPD hIM.cr))
  obtain ⟨-, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (callW_spec p n "check_decl_defn" [i, vis] s₀)
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (hin.memFrame n (f := "check_decl_defn") (by simp) [i, vis] s₀)
  subst hs
  obtain ⟨hok', hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok', ?_, hP.memos, callW_indMemos hIc hIl (im_mem _ rfl) hW hIM, hP.grow⟩
  rw [hst, hres]
  exact hR.of_step hP.stage hf (L.Ind.IWGrow.ext hP.grow)

end armsT

/-! ## The inductive arm's contracts -/

/-- **The inductive arm's contract**: `check_ind_decl(vis, o, l, w)` on an inductive block copied
into `EREC` (`ind_block_to_erec`'s post: the slice `o`, `l` decoding to `block`, below the top),
from `StageT` and the twin's fold invariant, refines `checkDeclKind`'s `.indDecl` case (the
declared parameter count, the reader, the one route), back to the stage relation at the returned
view, the core's memos, the pools grown, the inductive stage's memos. The inductive stage's top
theorem. -/
def IndArmSpec (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (pins : List INatOpPinSet) (n : Nat), n ≤ 2 ^ 62 → ∀ (m m' : Mem) (a : AState) (vis : Word)
    (fe : IFEnv) (env : ConLeche.Env) (block : List IConstantInfo) (nP : Nat) (o l w : Word)
    (r : List Word), l.toNat = block.length → w.toNat = nP →
    L.Front.decCIsR (erecP m) o.toNat l.toNat = some block → o.toNat + l.toNat < 2 ^ 64 →
    FrontBlock block → StageT dn vis fe m a → ConRon.Bridge.StateOK a → FoldOK env fe a →
    (∃ x, Frontend.denoteDecl a.store (.indDecl block nP) = some x) → BlockLpsDnA dn block →
    (∃ pinsP, PinsDenote a.store pins pinsP) →
    IndMemos m → callW p n "check_ind_decl" [vis, o, l, w] m = some (r, m') →
    ∃ fe' a', (checkDeclKind V pins fe (.indDecl block nP)).run a = .ok (fe', a') ∧
      StageR (r.headD 0) fe' m' a' ∧ CoreMemos m' ∧ IWGrow m m' ∧ IndMemos m'

/-- **`check_ind_decl`'s error claim** (`IndArmSpec`'s error half): a failing run claims the
twin's `checkDeclKind` failure. -/
def IndArmSpecE (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (pins : List INatOpPinSet) (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (vis : Word)
    (fe : IFEnv) (env : ConLeche.Env) (block : List IConstantInfo) (nP : Nat) (o l w : Word),
    l.toNat = block.length → w.toNat = nP →
    L.Front.decCIsR (erecP m) o.toNat l.toNat = some block → o.toNat + l.toNat < 2 ^ 64 →
    FrontBlock block → StageT dn vis fe m a → ConRon.Bridge.StateOK a → FoldOK env fe a →
    (∃ x, Frontend.denoteDecl a.store (.indDecl block nP) = some x) → BlockLpsDnA dn block →
    (∃ pinsP, PinsDenote a.store pins pinsP) →
    IndMemos m → ∀ e, callE p n "check_ind_decl" [vis, o, l, w] m = .error e →
    ErrClaim (checkDeclKind V pins fe (.indDecl block nP)) a e

/-! ## The declaration's own checks: the twin's side -/

/-- **What a declaration's own checks keep of the twin's state** (con-ron's
`Arena.checkDeclKind_bridge`, its `DeclKindOut` but the con-leche run): from the fold invariant,
the pin variants' and the record's denotations, a well-formed state, the store extended, the pins
the same. The core's and the inductive stage's bridge theorems discharge it (`CoreSpec`,
`IndSpec`). -/
def DeclKindSpec : Prop :=
  ∀ {pins : List INatOpPinSet} {env : ConLeche.Env} {fe fe' : IFEnv} {s s' : AState}
    {pd : IDeclaration} {d : ConLeche.Declaration},
    FoldOK env fe s → (∃ pinsP, PinsDenote s.store pins pinsP) →
    Frontend.denoteDecl s.store pd = some d →
    checkDeclKind V pins fe pd s = .ok (fe', s') →
    ConRon.Bridge.StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins

/-- **`DeclKindSpec` holds**: con-ron's `Arena.checkDeclKind_bridge` at the core's and the
inductive stage's specs (`CoreSpec.of_core`, `indSpec_of_bridge`). -/
theorem declKindSpec : DeclKindSpec := by
  intro pins env fe fe' s s' pd d hok hPD hd hrun
  obtain ⟨pinsP, hP⟩ := hPD
  have o := ConRon.Bridge.Arena.checkDeclKind_bridge (pinsP := pinsP) ConRon.Bridge.CoreSpec.of_core
    ConRon.Bridge.Inductives.indSpec_of_bridge hok hP hd hrun
  exact ⟨o.state, o.ext, o.pins⟩

/-! ## `check_decl` -/

/-- The arrays `check_decl`'s callees after the block's copy write: a step's (`stepA`) but the
pin table. -/
def kindA : List TieredArray := stepA.filter fun b => b != PINS

theorem kindA_sub : ∀ b ∈ kindA, b ∈ stepA := fun _ h => (List.mem_filter.mp h).1

theorem kindA_pins : (PINS : TieredArray) ∉ kindA := fun h => by
  have := (List.mem_filter.mp h).2; simp at this

/-- **`check_decl`'s callees after the block's copy**: the arms, the inductive arm, the flush and
the reserved names' check. -/
def kindFns : List FnName :=
  ["check_decl_axiom", "check_decl_defn", "check_decl_thm", "check_decl_opaque", "check_decl_quot",
   "check_ind_decl", "flush_caches", "basis_names_ok"]

/-- **The write set of `kindFns`**: a step's (`stepA`, `stepC`) but the pin table. -/
def KindIn (p : Prog) : Prop :=
  ∃ F : List FnName, (∀ f ∈ kindFns, f ∈ F) ∧ closedA p kindA stepC F = true

/-- A call of `kindFns` writes `kindA`/`stepC` only. -/
theorem KindIn.frame {p : Prog} (h : KindIn p) {f : FnName} (hf : f ∈ kindFns) {n : Nat}
    {vs : List Word} {m m' : Mem} {r : List Word} (hc : callW p n f vs m = some (r, m')) :
    MemFrame kindA stepC m m' := by
  obtain ⟨F, hF, hcl⟩ := h
  exact (run_memFrame hcl (hF f hf) (run_of_callW hc)).1

/-- **The program facts `check_decl`'s refinement takes**: the lookups, the copy of a block into
`EREC` (`IbeProg`), the write sets the job relation is carried across, the arms' contracts and the
inductive arm's, the flush's and the reserved names' check's program facts. -/
structure CdProg (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
    (ds : Array IDeclaration) (p : Prog) : Prop where
  cd : CheckDeclProg p
  ibe : IbeProg p
  indIn : StepIn p indFns
  kindIn : KindIn p
  indMemo : IndMemoClosed p
  indLeaves : IndLeaves p
  arms : ArmsT pins dn ds p
  ind : IndArmSpec p dn
  fl : FlushProg p
  bno : L.Ind.BnoProg p

/-- What the error arms of `check_decl` assume: the arms' claims and the inductive arm's. -/
structure CdG (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
    (ds : Array IDeclaration) (p : Prog) : Prop where
  arms : ArmsE pins dn ds p
  ind : IndArmSpecE p dn

/-- What `check_decl` gives besides the twin's run, a view `w` and the memory `m'`: the job
relation and the memos. -/
structure CdPost (pins : List INatOpPinSet) (ds : Array IDeclaration) (m : Mem) (w : Word)
    (x : IFEnv) (m' : Mem) (a' : AState) : Prop where
  loop : LoopR pins m' a' w x ds
  core : CoreMemos m'
  ind : IndMemos m'
  /-- `check_decl` only grows the pools. -/
  grow : IWGrow m m'

/-- What `check_decl_kind` gives: `check_decl`'s post and its write set. -/
structure CdkPost (pins : List INatOpPinSet) (ds : Array IDeclaration) (m : Mem) (w : Word)
    (x : IFEnv) (m' : Mem) (a' : AState) : Prop extends CdPost pins ds m w x m' a' where
  frame : MemFrame kindA stepC m m'

section cd
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet)
  (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration) (p : Prog)

/-- **What `check_decl` refines under `StageT`** (the job's call, `record_job`'s
`check_decl(k, 0)` at `fe = I.view k`): `checkDecl` from the job relation and `StageT`, back to
the job relation at the returned view and the memos. -/
def CheckDeclSpecT : Prop :=
    ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv)
      (i : Word), i.toNat < ds.size → ConRon.Bridge.StateOK a₀ →
      LoopR pins s₀.mem a₀ vis fe ds → StageT dn vis fe s₀.mem a₀ →
      (∃ env, FoldOK env fe a₀) → (∃ x, Frontend.denoteDecl a₀.store (dsAt ds i) = some x) →
      (∃ pinsP, PinsDenote a₀.store pins pinsP) → IndMemos s₀.mem →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_decl" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkDecl mode pins fe (dsAt ds i)) a₀ ∧
      LoopR pins s'.mem (AM.st (checkDecl mode pins fe (dsAt ds i)) a₀) (r.headD 0)
        (AM.res (checkDecl mode pins fe (dsAt ds i)) a₀) ds ∧ CoreMemos s'.mem ∧
      IndMemos s'.mem ∧ IWGrow s₀.mem s'.mem; ⊤⦄

end cd

/-- An arm through its run: the ok half by its contract (`ArmSpecT`), the error half by its
claim. -/
theorem cd_arm {p : Prog} {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {f : FnName} {d : IDeclaration} (hA : ArmSpecT pins dn ds p f d)
    (hE : CdG pins dn ds p → ArmSpecE pins dn ds p f d) (hK : KindIn p) (hf : f ∈ kindFns)
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {i : Word} (hi : i.toNat < ds.size)
    (hd : ds[i.toNat]? = some d) (hok : ConRon.Bridge.StateOK a)
    (hR : LoopR pins m a vis fe ds) (hS : StageT dn vis fe m a)
    (hF : ∃ env, FoldOK env fe a) (hden : ∃ x, Frontend.denoteDecl a.store d = some x)
    (hPD : ∃ pinsP, PinsDenote a.store pins pinsP) (hIM : IndMemos m) :
    RefE (CdG pins dn ds p) (checkDeclKindE.k_check_ind_decl p (callE p n f [i, vis] m))
      (checkDeclKind V pins fe d) a (fun v x a' => CdkPost pins ds m v.1 x v.2 a') := by
  rcases c : callE p n f [i, vis] m with e | ⟨r, m'⟩
  · rw [checkDeclKindE.k_check_ind_decl.none]
    exact fun hG => hE hG n hn m a vis fe i hi hd hok hR hS hF hden hPD hIM e c
  rw [checkDeclKindE.k_check_ind_decl.arm1]
  have h1 := callW_of_callE c
  obtain ⟨s', hs', -, hok', hL, hc, hIM', hG'⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (hA n hn ⟨m, Locals.init []⟩ a vis fe i hi hd hok hR hS hF hden hPD hIM) h1
  subst hs'
  exact RefE.ret (AM.run_of_ok _ _ hok') ⟨⟨by simpa using hL, hc, hIM', by simpa using hG'⟩,
    hK.frame hf h1⟩

/-- **`check_decl_kind(i, vis, bo, bl)` refines `checkDeclKind` under `StageT`, both outcomes**,
for the front's record kinds: each arm by its contract (`CdProg.arms`) and its claim (`CdG`), the
inductive one by its contracts (`IndArmSpec`, `IndArmSpecE`) on the block's `EREC` copy
`(bo, bl)`; the job relation after it by the write set of `indFns`. -/
@[refines_part ConRon.Arena.checkDeclKind "check_decl_kind(i, vis, bo, bl): the front's records (kinds 1-6), under StageT, both outcomes"]
theorem cdk_ref {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {p : Prog} (hP : CdProg pins dn ds p) (hFD : FrontDecls ds)
    (hLD : DeclsLpsDn dn ds)
    {N : Nat} (hN : N ≤ 2 ^ 62 + 1) {m : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {i bo bl : Word} (hi : i.toNat < ds.size) (hok : ConRon.Bridge.StateOK a)
    (hR : LoopR pins m a vis fe ds) (hS : StageT dn vis fe m a)
    (hF : ∃ env, FoldOK env fe a) (hden : ∃ x, Frontend.denoteDecl a.store ds[i.toNat] = some x)
    (hPD : ∃ pinsP, PinsDenote a.store pins pinsP) (hIM : IndMemos m)
    (hB : ∀ block nP, ds[i.toNat] = .indDecl block nP →
      L.Front.decCIsR (erecP m) bo.toNat bl.toNat = some block ∧ bo.toNat + bl.toNat < 2 ^ 64 ∧
        bl.toNat = block.length) :
    RefE (CdG pins dn ds p) (checkDeclKindE p N m i vis bo bl) (checkDeclKind V pins fe ds[i.toNat]) a
      (fun v x a' => CdkPost pins ds m v.1 x v.2 a') := by
  have hdecl := hR.decls.recs i.toNat hi
  have hd : ds[i.toNat]? = some ds[i.toNat] := Array.getElem?_eq_getElem hi
  have h1 := hR.decls.room
  have h2 := hR.decls.dsize
  have hw0 : rdW (m.arr64 DECL) (1 + 8 * i) = dw (m.arr64 DECL) i.toNat 0 :=
    rdW_dw _ (by omega) (by decide) (by decide)
  rcases N with _ | n
  · rw [checkDeclKindE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  have hn' : n ≤ 2 ^ 62 := by omega
  generalize hdi : ds[i.toNat] = d at hdecl hd hden hB
  cases d with
  | axiomDecl cv =>
    rw [checkDeclKindE.arm2 _ _ _ _ _ _ _ (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1])]
    exact cd_arm (hP.arms.axiom_ cv) (fun hG => hG.arms.axiom_ cv) hP.kindIn (by decide) hn' hi hd
      hok hR hS hF hden hPD hIM
  | defnDecl cv v hh =>
    rw [checkDeclKindE.arm3 _ _ _ _ _ _ _ (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1])]
    exact cd_arm (hP.arms.defn cv v hh) (fun hG => hG.arms.defn cv v hh) hP.kindIn (by decide) hn'
      hi hd hok hR hS hF hden hPD hIM
  | thmDecl cv v =>
    rw [checkDeclKindE.arm4 _ _ _ _ _ _ _ (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1])]
    exact cd_arm (hP.arms.thm cv v) (fun hG => hG.arms.thm cv v) hP.kindIn (by decide) hn' hi hd
      hok hR hS hF hden hPD hIM
  | opaqueDecl cv v =>
    rw [checkDeclKindE.arm5 _ _ _ _ _ _ _ (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1])]
    exact cd_arm (hP.arms.opaque_ cv v) (fun hG => hG.arms.opaque_ cv v) hP.kindIn (by decide) hn'
      hi hd hok hR hS hF hden hPD hIM
  | quotDecl k cv =>
    rw [checkDeclKindE.arm6 _ _ _ _ _ _ _ (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1])]
    exact cd_arm (hP.arms.quot k cv) (fun hG => hG.arms.quot k cv) hP.kindIn (by decide) hn' hi hd
      hok hR hS hF hden hPD hIM
  | indDecl block nP =>
    rw [checkDeclKindE.arm1 _ _ _ _ _ _ _ (by rw [hw0, hdecl.1])]
    have hdecl' : IndDeclAt (m.arr64 DECL) (m.arr64 DLP) i.toNat block nP := by
      have := hR.decls.recs i.toNat hi
      rw [hdi] at this; exact this
    have hFB := hFD _ hi _ _ hdi
    have hlpd := hLD _ hi _ _ hdi
    have hD : (m.arr64 DECL).size < 2 ^ 63 := hR.decls.dsize
    obtain ⟨hdec, htop, hl⟩ := hB block nP rfl
    have hw : (rdW (m.arr64 DECL) (5 + 8 * i)).toNat = nP := by
      have h0 : dw (m.arr64 DECL) i.toNat 0 ≠ 0 := by rw [hdecl'.1]; decide
      rw [rdW_dwI hD h0 rfl (by decide)]
      exact hdecl'.2.1
    obtain ⟨env, hFo⟩ := hF
    rcases c2 : callE p n "check_ind_decl" [vis, bo, bl, rdW (m.arr64 DECL) (5 + 8 * i)] m with
      e2 | ⟨r2, m2⟩
    · rw [checkDeclKindE.k_check_ind_decl.none]
      exact fun hG => hG.ind pins n hn' m a vis fe env block nP _ _ _ hl hw hdec htop hFB hS
        hok hFo hden hlpd hPD hIM e2 c2
    rw [checkDeclKindE.k_check_ind_decl.arm1]
    have d2 := callW_of_callE c2
    obtain ⟨fe', a', hrun, hS2, hcm, hg2, hIM2⟩ := hP.ind pins n hn' m m2 a vis fe env block nP
      _ _ _ r2 hl hw hdec htop hFB hS hok hFo hden hlpd hPD hIM d2
    have hfk := hP.kindIn.frame (by decide) d2
    have hL2 := hR.of_step hS2 (hfk.mono kindA_sub (fun _ h => h)) (L.Ind.IWGrow.ext hg2)
    exact RefE.ret hrun ⟨⟨by simpa using hL2, hcm, hIM2, hg2⟩, hfk⟩

theorem not_flushCtl_lo {x : Word} (h : x.toNat < 64) : x ∉ flushCtl := fun hx => by
  have := flushCtl_ge x hx; omega

theorem not_flushCtl_hi {x : Word} (h : 128 ≤ x.toNat) : x ∉ flushCtl := fun hx => by
  have := flushCtl_lt x hx; omega

/-- **The core's memos across the flush** (it writes the caches' `CTL` words `64‥127` only). -/
theorem CoreMemos.flush {m : Mem} (h : CoreMemos m) : CoreMemos (flushMem m) :=
  CoreMemos.frame (flushMem_frame m) ⟨by simp, by simp⟩
    ⟨not_flushCtl_lo (by decide), not_flushCtl_lo (by decide)⟩ h ⟨by simp, by simp, by simp⟩
    ⟨not_flushCtl_hi (by decide), not_flushCtl_hi (by decide), not_flushCtl_hi (by decide)⟩
    ⟨by simp, by simp, by simp⟩
    ⟨not_flushCtl_lo (by decide), not_flushCtl_lo (by decide), not_flushCtl_lo (by decide)⟩
    (by simp) (not_flushCtl_hi (by decide))

/-- **The inductive stage's memos across the flush.** -/
theorem IndMemos.flush {m : Mem} (h : IndMemos m) : IndMemos (flushMem m) :=
  h.frame (flushMem_frame m) (fun _ hb => by simp at hb) fun x hx => by
    have := flushCtl_ge x hx; have := flushCtl_lt x hx
    exact ⟨by omega, by omega, .inl (by omega)⟩

/-- **`check_decl` refines `checkDecl` under `StageT`, both outcomes**, for the front's record
kinds (con-ron's `Arena.checkDecl_bridge`'s decomposition): an inductive block copied into `EREC`
(`ind_block_to_erec`, `indBlockToErec_ok`), the declaration's own checks (`cdk_ref`), the flush
(`flush_stage`; `TwinOK` at the returned environment by `TwinOK.of_kind`, the environment's growth
`oneKind_envGrowDen`/`indKindEnv`), then the reserved names' check (`bno_sim`) and its failure's
reason (`bne_sim`). -/
@[refines_part ConRon.Arena.checkDecl "check_decl(i, vis): the front's records (kinds 1-6), under StageT, both outcomes"]
theorem cd_ref {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {p : Prog} (hP : CdProg pins dn ds p) (hFD : FrontDecls ds)
    (hLD : DeclsLpsDn dn ds)
    {N : Nat} (hN : N ≤ 2 ^ 62 + 1) {m : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {i : Word} (hi : i.toNat < ds.size) (hok : ConRon.Bridge.StateOK a)
    (hR : LoopR pins m a vis fe ds) (hS : StageT dn vis fe m a)
    (hF : ∃ env, FoldOK env fe a) (hden : ∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x)
    (hPD : ∃ pinsP, PinsDenote a.store pins pinsP) (hIM : IndMemos m) :
    RefE (CdG pins dn ds p) (checkDeclE p N m i vis) (checkDecl V pins fe (dsAt ds i)) a
      (fun v x a' => CdPost pins ds m v.1 x v.2 a') := by
  have hdecl := hR.decls.recs i.toNat hi
  have hds : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
  rw [hds] at hden ⊢
  have h1 := hR.decls.room
  have h2 := hR.decls.dsize
  have hw0 : rdW (m.arr64 DECL) (1 + 8 * i) = dw (m.arr64 DECL) i.toNat 0 :=
    rdW_dw _ (by omega) (by decide) (by decide)
  rcases N with _ | n
  · rw [checkDeclE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  have hn' : n ≤ 2 ^ 62 + 1 := by omega
  obtain ⟨env, hFo⟩ := hF
  obtain ⟨dd, hdd⟩ := hden
  -- after the block's copy: the record's checks, the flush, the reserved names
  suffices H : ∀ (bo bl : Word) (m1 : Mem), LoopR pins m1 a vis fe ds → StageT dn vis fe m1 a →
      IndMemos m1 → IWGrow m m1 → MemFrame stepA stepC m m1 →
      L.Ind.BnoArgs ds[i.toNat] (rdW (m.arr64 DECL) (1 + 8 * i))
        (rdW (m.arr64 DECL) (2 + 8 * i) &&& 4294967295) bo bl m1 →
      (∀ block nP, ds[i.toNat] = .indDecl block nP →
        L.Front.decCIsR (erecP m1) bo.toNat bl.toNat = some block ∧ bo.toNat + bl.toNat < 2 ^ 64 ∧
          bl.toNat = block.length) →
      RefE (CdG pins dn ds p) (checkDeclE.j1 p n i vis (rdW (m.arr64 DECL) (1 + 8 * i)) bo bl m1)
        (checkDecl V pins fe ds[i.toNat]) a (fun v x a' => CdPost pins ds m v.1 x v.2 a') by
    have hw1 : rdW (m.arr64 DECL) (2 + 8 * i) = dw (m.arr64 DECL) i.toNat 1 :=
      rdW_dw _ (by omega) (by decide) (by decide)
    have hname : ∀ cv, L.Front.CVAt (m.arr64 DECL) (m.arr64 DLP) i.toNat cv →
        L.Ind.NameW (rdW (m.arr64 DECL) (2 + 8 * i) &&& 4294967295) cv := fun cv hcv =>
      ⟨by rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide),
        by rw [decI_mask, hw1]; exact hcv.1⟩
    generalize hdi : ds[i.toNat] = d at hdecl hdd H ⊢
    cases d with
    | indDecl block nP =>
      have h6 : rdW (m.arr64 DECL) (1 + 8 * i) = 6 := by rw [hw0]; exact hdecl.1
      rw [checkDeclE.arm1 _ _ _ _ _ h6]
      have hFB := hFD _ hi _ _ hdi
      have hD : (m.arr64 DECL).size < 2 ^ 63 := hR.decls.dsize
      have hP' : (m.arr64 DLP).size < 2 ^ 63 := hR.decls.psize
      refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r1 m1 c1 => ?_
      rw [checkDeclE.k_ind_block_to_erec.arm1]
      obtain ⟨hS1, hg1, hf1, -, hl1, hdec1, htop1⟩ :=
        indBlockToErec_ok hP.ibe c1 hS.stage hdecl hFB hD hP'
      have hT1 : StageT dn vis fe m1 a :=
        ⟨hS1, hS.twin.frame hf1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          by rw [pinW_frame hf1 (by decide)]; exact hS.flag⟩
      obtain ⟨F, hFs, hFcl⟩ := hP.indIn
      have hfs1 := (run_memFrame hFcl (hFs _ (by decide)) (run_of_callW c1)).1
      have hIM1 : IndMemos m1 :=
        hIM.frame hf1 (fun b hb => by simp at hb; rcases hb with rfl | rfl <;> decide)
          (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> decide)
      refine H _ _ m1 (hR.of_step hS1 hfs1 (L.Ind.IWGrow.ext hg1)) hT1 hIM1 hg1 hfs1
        ⟨h6, hdec1, htop1⟩ fun b nP' e => ?_
      obtain ⟨rfl, rfl⟩ := IDeclaration.indDecl.inj e
      exact ⟨hdec1, htop1, hl1⟩
    | _ =>
      have h6 : rdW (m.arr64 DECL) (1 + 8 * i) ≠ 6 := by
        rw [hw0, hdecl.1]; decide
      rw [checkDeclE.arm2 _ _ _ _ _ h6]
      refine H 0 0 m hR hS hIM (IWGrow.refl _) (MemFrame.refl _ _ _) ?_ fun _ _ e => by cases e
      first
      | exact ⟨by rw [hw0, hdecl.1], hname _ hdecl.2.1⟩
      | exact ⟨by rw [hw0, hdecl.1], hname _ hdecl.2⟩
      | exact (show rdW (m.arr64 DECL) (1 + 8 * i) = 5 by rw [hw0, hdecl.1])
  intro bo bl m1 hR1 hT1 hIM1 hg1 hfs1 hA1 hB1
  have hDm1 : m1.arr64 DECL = m.arr64 DECL := hfs1.arr _ step_keeps.1 (by decide)
  rw [checkDeclE.j1]
  unfold ConRon.Arena.checkDecl
  -- `check_decl_kind`
  refine RefE.bindE (fun _ => rfl) id
    (cdk_ref hP hFD hLD (N := n) hn' hi hok hR1 hT1 ⟨env, hFo⟩ ⟨dd, hdd⟩ hPD hIM1 hB1)
    fun v fe2 a2 hrun2 hQ => ?_
  obtain ⟨vis2, m2⟩ := v
  rw [checkDeclE.k_check_decl_kind.arm1]
  obtain ⟨hok2, hx2, hp2⟩ := declKindSpec hFo hPD hdd hrun2
  have hf12 := hQ.frame
  have hS2 : StageR vis2 fe2 m2 a2 := ⟨hQ.loop.check, hQ.loop.iw⟩
  -- the environment's growth
  have hgrow : EnvGrowDen a2.store fe fe2 := by
    generalize hdi : ds[i.toNat] = d at hdd hrun2
    cases d with
    | indDecl block nP =>
      simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hdd
      obtain ⟨bP, hbP, -⟩ := hdd
      exact indKindEnv hFo hbP hrun2
    | axiomDecl cv =>
      simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hdd
      obtain ⟨c, hc, -⟩ := hdd
      exact oneKind_envGrowDen hFo hc hx2 (.inl rfl) hrun2
    | defnDecl cv v h =>
      simp only [Frontend.denoteDecl] at hdd
      split at hdd
      · exact oneKind_envGrowDen hFo (by assumption) hx2 (.inr (.inl ⟨v, h, rfl⟩)) hrun2
      · cases hdd
    | thmDecl cv v =>
      simp only [Frontend.denoteDecl] at hdd
      split at hdd
      · exact oneKind_envGrowDen hFo (by assumption) hx2 (.inr (.inr (.inl ⟨v, rfl⟩))) hrun2
      · cases hdd
    | opaqueDecl cv v =>
      simp only [Frontend.denoteDecl] at hdd
      split at hdd
      · exact oneKind_envGrowDen hFo (by assumption) hx2 (.inr (.inr (.inr (.inl ⟨v, rfl⟩)))) hrun2
      · cases hdd
    | quotDecl k cv =>
      simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hdd
      obtain ⟨c, hc, -⟩ := hdd
      exact oneKind_envGrowDen hFo hc hx2 (.inr (.inr (.inr (.inr ⟨k, rfl⟩)))) hrun2
  -- `flush_caches`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r3 m3 c3 => ?_
  rw [checkDeclE.k_flush_caches.arm1]
  try dsimp only
  refine RefE.bind_right (flushCaches_run a2) ?_
  obtain ⟨s3, rfl, -, hfok, hm3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (flushCaches_spec p hP.fl n _) c3
  simp only at hm3 hfok
  rw [hm3]
  clear c3
  have hf23 := flushMem_frame m2
  obtain ⟨hS3, hg3⟩ := L.Ind.flush_stage hS2 hfok
  have hok3 : ConRon.Bridge.StateOK ({ a2 with caches := Caches.empty } : AState) := ⟨hok2.wf⟩
  have hrd3 : ConRon.Bridge.ReadOK ({ a2 with caches := Caches.empty } : AState) :=
    ⟨by intro k x hk; simp [Caches.empty] at hk, by intro k x hk; simp [Caches.empty] at hk,
      by intro k x hk; simp [Caches.empty] at hk⟩
  have hpo3 : ConRon.Bridge.PinsOK ({ a2 with caches := Caches.empty } : AState) := hFo.check.pins.mono hx2 hp2
  have hf13 : MemFrame kindA stepC m1 (flushMem m2) :=
    hf12.trans (hf23.mono (fun _ h => by simp at h) (fun x h => by
      have := flushCtl_lt x h; have := flushCtl_ge x h
      simp only [stepC, List.mem_map, List.mem_filter, List.mem_range]
      exact ⟨x.toNat, ⟨by omega, by simp; omega⟩, by simp⟩))
  have hM3 : CoreMemos (flushMem m2) := hQ.core.flush
  have hT3 : StageT dn vis2 fe2 (flushMem m2) ({ a2 with caches := Caches.empty } : AState) := by
    refine ⟨hS3, TwinOK.of_kind hS.twin hok2.wf hx2 rfl hp2 ?_ ?_ ?_ hM3 hgrow, ?_⟩
    · rw [hf13.size]; exact hT1.twin.erec
    · rw [hf13.size]; exact hT1.twin.spn
    · rw [hf13.size]; exact hT1.twin.bstk
    · rw [pinW_frame hf13 kindA_pins]; exact hT1.flag
  have hD3 : (flushMem m2).arr64 DECL = m.arr64 DECL := by
    rw [hf13.arr _ (fun h => step_keeps.1 (kindA_sub _ h)) (by decide), hDm1]
  have hden3 : ∃ x, Frontend.denoteDecl ({ a2 with caches := Caches.empty } : AState).store ds[i.toNat] = some x :=
    ⟨dd, ConRon.Bridge.Frontend.denoteDecl_ext hx2 hdd⟩
  have hA3 : L.Ind.BnoArgs ds[i.toNat] (rdW (m.arr64 DECL) (1 + 8 * i))
      (rdW ((flushMem m2).arr64 DECL) (2 + 8 * i) &&& 4294967295) bo bl (flushMem m2) := by
    rw [hD3]
    have he13 : ArrExt (erecP m1) (erecP (flushMem m2)) := (hQ.grow.trans hg3).ext
    revert hA1
    cases ds[i.toNat] with
    | indDecl block nP =>
      rintro ⟨hk, hb1, hb2⟩; exact ⟨hk, L.Ind.decCIsR_ext he13 hb1, hb2⟩
    | _ => exact id
  -- `basis_names_ok`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r4 m4 c4 => ?_
  obtain ⟨b4, a4, hrun4, hT4, hg4, hR4, hb4⟩ :=
    L.Ind.bno_sim hP.bno hT3 hok3 hrd3 hpo3 hA3 hden3 r4 m4 c4
  refine RefE.bind_right hrun4 ?_
  have hf34 := hP.kindIn.frame (by decide) c4
  have hIM4 : IndMemos m4 :=
    callW_indMemos hP.indMemo hP.indLeaves (im_mem _ rfl) c4 hQ.ind.flush
  have hg14 : IWGrow m1 m4 := hQ.grow.trans (hg3.trans hg4)
  by_cases h0 : r4.headD 0 = 0
  · -- the reserved names' failure
    rw [checkDeclE.k_basis_names_ok.arm1 _ _ _ _ _ _ _ _ h0]
    have hb : b4 = false := by cases b4 <;> simp_all
    subst hb
    simp only [Bool.false_eq_true, ite_false]
    have hA4 : L.Ind.BnoArgs ds[i.toNat] (rdW (m.arr64 DECL) (1 + 8 * i))
        (rdW ((flushMem m2).arr64 DECL) (2 + 8 * i) &&& 4294967295) bo bl m4 := by
      revert hA3
      cases ds[i.toNat] with
      | indDecl block nP =>
        rintro ⟨hk, hb1, hb2⟩; exact ⟨hk, L.Ind.decCIsR_ext hg4.ext hb1, hb2⟩
      | _ => exact id
    refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r5 m5 c5 => ?_
    obtain ⟨ce, a5, hrun5, -, -, hcls⟩ := L.Ind.bne_sim hP.bno hT4 hR4.ok hR4.read hA4
      ⟨dd, ConRon.Bridge.Frontend.denoteDecl_ext (hx2.trans hR4.ext) hdd⟩ r5 m5 c5
    refine RefE.bind_right hrun5 ?_
    simp only [checkDeclE.k_basis_names_error]
    by_cases e1 : r5.headD 0 = R_RESERVED_BASIS_NAME_THE
    · rw [ite_eq_left e1]; exact fun _ => ErrClaim.fail_abort a5 ce (by rw [hcls]; decide)
    rw [ite_eq_right e1]
    by_cases e2 : r5.headD 0 = R_RESERVED_BASIS_NAME_IN
    · rw [ite_eq_left e2]; exact fun _ => ErrClaim.fail_abort a5 ce (by rw [hcls]; decide)
    rw [ite_eq_right e2]; exact fun _ => ErrClaim.fail_abort a5 ce (by rw [hcls]; decide)
  · -- passed
    rw [checkDeclE.k_basis_names_ok.arm2 _ _ _ _ _ _ _ _ h0]
    have hb : b4 = true := hb4.mp h0
    subst hb
    simp only [ite_true]
    exact RefE.ret rfl ⟨hR1.of_step hT4.stage ((hf13.trans hf34).mono kindA_sub (fun _ h => h))
      hg14.ext, hT4.twin.memos, hIM4, hg1.trans hg14⟩

/-- **`check_decl` refines `checkDecl` under `StageT`**, for the front's record kinds: the ok
half of `cd_ref`. -/
@[refines_part ConRon.Arena.checkDecl "check_decl(i, vis): the front's records (kinds 1-6), under StageT"]
theorem checkDecl_loopT {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {p : Prog} (hP : CdProg pins dn ds p) (hFD : FrontDecls ds)
    (hLD : DeclsLpsDn dn ds) :
    CheckDeclSpecT V pins dn ds p := by
  intro n hn s₀ a₀ vis fe i hi hok hR hS hF hden hPD hIM
  refine triple_post (RefE.triple (checkDecl_specE p hP.cd.cd hP.cd.ckd n s₀ i vis)
    (cd_ref hP hFD hLD (by omega) hi hok hR hS hF hden hPD hIM)) ?_
  rintro r s' ⟨hl, x, a', run, hR'⟩
  obtain ⟨hok', hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok', by rw [hst, hres]; exact hR'.loop, hR'.core, hR'.ind, hR'.grow⟩

end L.Arena
