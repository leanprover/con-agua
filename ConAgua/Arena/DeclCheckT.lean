module

public import ConAgua.Arena.CheckerT
public import ConAgua.Arena.DeclCrpT
import all ConAgua.Arena.DeclStep
import ConAgua.Arena.QuotRulesT
import ConAgua.Checker.QuotFns
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.RefWalk

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
  ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkDecl V pins fe d) a₀ ∧
    LoopR pins s'.mem (AM.st (checkDecl V pins fe d) a₀) (r.headD 0)
      (AM.res (checkDecl V pins fe d) a₀) ds ∧ CoreMemos s'.mem ∧ IndMemos s'.mem ∧
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
    ErrClaim (checkDecl V pins fe d) a₀ e

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
  exact hR.of_step hP.stage hf (IWGrow.erecPExt hP.grow)

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
  exact hR.of_step hP.stage hf (IWGrow.erecPExt hP.grow)

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
  exact hR.of_step hP.stage hf (IWGrow.erecPExt hP.grow)

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
  exact hR.of_step hP.stage hf (IWGrow.erecPExt hP.grow)

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
  exact hR.of_step hP.stage hf (IWGrow.erecPExt hP.grow)

end armsT

/-! ## The inductive arm's contracts -/

/-- **The inductive arm's contract**: `check_ind_decl(vis, o, l, w)` on an inductive block copied
into `EREC` (`ind_block_to_erec`'s post: the slice `o`, `l` decoding to `block`, below the top),
from `StageT` and the twin's fold invariant, refines `checkDecl`'s `.indDecl` case (the pinned
blocks first, then the declared parameter count and the one route), back to the stage relation
at the returned view, the core's memos, the pools grown, the inductive stage's memos. The
inductive stage's top theorem. -/
def IndArmSpec (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (pins : List INatOpPinSet) (n : Nat), n ≤ 2 ^ 62 → ∀ (m m' : Mem) (a : AState) (vis : Word)
    (fe : IFEnv) (env : ConLeche.Env) (block : List IConstantInfo) (nP : Nat) (o l w : Word)
    (r : List Word), l.toNat = block.length → w.toNat = nP →
    L.Front.decCIsR (erecP m) o.toNat l.toNat = some block → o.toNat + l.toNat ≤ erTop m →
    FrontBlock block → StageT dn vis fe m a → ConRon.Bridge.StateOK a → FoldOK env fe a →
    (∃ x, Frontend.denoteDecl a.store (.indDecl block nP) = some x) → BlockLpsDnA dn block →
    (∃ pinsP, PinsDenote a.store pins pinsP) →
    IndMemos m → callW p n "check_ind_decl" [vis, o, l, w] m = some (r, m') →
    ∃ fe' a', (checkDecl V pins fe (.indDecl block nP)).run a = .ok (fe', a') ∧
      StageR (r.headD 0) fe' m' a' ∧ CoreMemos m' ∧ IWGrow m m' ∧ IndMemos m'

/-- **`check_ind_decl`'s error claim** (`IndArmSpec`'s error half): a failing run claims the
twin's `checkDecl` failure. -/
def IndArmSpecE (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (pins : List INatOpPinSet) (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (vis : Word)
    (fe : IFEnv) (env : ConLeche.Env) (block : List IConstantInfo) (nP : Nat) (o l w : Word),
    l.toNat = block.length → w.toNat = nP →
    L.Front.decCIsR (erecP m) o.toNat l.toNat = some block → o.toNat + l.toNat ≤ erTop m →
    FrontBlock block → StageT dn vis fe m a → ConRon.Bridge.StateOK a → FoldOK env fe a →
    (∃ x, Frontend.denoteDecl a.store (.indDecl block nP) = some x) → BlockLpsDnA dn block →
    (∃ pinsP, PinsDenote a.store pins pinsP) →
    IndMemos m → ∀ e, callE p n "check_ind_decl" [vis, o, l, w] m = .error e →
    ErrClaim (checkDecl V pins fe (.indDecl block nP)) a e

/-! ## `check_decl` -/

/-- **The program facts `check_decl`'s refinement takes**: the lookups, the copy of a block into
`EREC` (`IbeProg`), the write sets the job relation is carried across, the arms' contracts and the
inductive arm's. -/
structure CdProg (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
    (ds : Array IDeclaration) (p : Prog) : Prop where
  cd : CheckDeclProg p
  ibe : IbeProg p
  indIn : StepIn p indFns
  indMemo : IndMemoClosed p
  arms : ArmsT pins dn ds p
  ind : IndArmSpec p dn

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
    (hE : CdG pins dn ds p → ArmSpecE pins dn ds p f d)
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {i : Word} (hi : i.toNat < ds.size)
    (hd : ds[i.toNat]? = some d) (hok : ConRon.Bridge.StateOK a)
    (hR : LoopR pins m a vis fe ds) (hS : StageT dn vis fe m a)
    (hF : ∃ env, FoldOK env fe a) (hden : ∃ x, Frontend.denoteDecl a.store d = some x)
    (hPD : ∃ pinsP, PinsDenote a.store pins pinsP) (hIM : IndMemos m) :
    RefE (CdG pins dn ds p) (checkDeclE.k_check_ind_decl p (callE p n f [i, vis] m))
      (checkDecl V pins fe d) a (fun v x a' => CdPost pins ds m v.1 x v.2 a') := by
  rcases c : callE p n f [i, vis] m with e | ⟨r, m'⟩
  · rw [checkDeclE.k_check_ind_decl.none]
    exact fun hG => hE hG n hn m a vis fe i hi hd hok hR hS hF hden hPD hIM e c
  rw [checkDeclE.k_check_ind_decl.arm1]
  have h1 := callW_of_callE c
  obtain ⟨s', hs', -, hok', hL, hc, hIM', hG'⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (hA n hn ⟨m, Locals.init []⟩ a vis fe i hi hd hok hR hS hF hden hPD hIM) h1
  subst hs'
  exact RefE.ret (AM.run_of_ok _ _ hok') ⟨by simpa using hL, hc, hIM', by simpa using hG'⟩

/-- **`check_decl` refines `checkDecl` under `StageT`, both outcomes**, for the front's record
kinds: each arm by its contract (`CdProg.arms`) and its claim (`CdG`), the inductive one by its
contracts (`IndArmSpec`, `IndArmSpecE`) after `ind_block_to_erec` copies the record's block into
`EREC` (`indBlockToErec_ok`; it writes only `EREC` and its top, so `TwinOK` and the pin flag
stay); the job relation after it by the write set of `indFns`. -/
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
    exact cd_arm (hP.arms.axiom_ cv) (fun hG => hG.arms.axiom_ cv) hn' hi hd hok hR hS hF hden
      hPD hIM
  | defnDecl cv v hh =>
    rw [checkDeclE.arm3 _ _ _ _ _ (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1])]
    exact cd_arm (hP.arms.defn cv v hh) (fun hG => hG.arms.defn cv v hh) hn' hi hd hok hR hS hF
      hden hPD hIM
  | thmDecl cv v =>
    rw [checkDeclE.arm4 _ _ _ _ _ (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1])]
    exact cd_arm (hP.arms.thm cv v) (fun hG => hG.arms.thm cv v) hn' hi hd hok hR hS hF hden
      hPD hIM
  | opaqueDecl cv v =>
    rw [checkDeclE.arm5 _ _ _ _ _ (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1])]
    exact cd_arm (hP.arms.opaque_ cv v) (fun hG => hG.arms.opaque_ cv v) hn' hi hd hok hR hS hF
      hden hPD hIM
  | quotDecl k cv =>
    rw [checkDeclE.arm6 _ _ _ _ _ (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide) (by rw [hw0, hdecl.1]; decide)
      (by rw [hw0, hdecl.1])]
    exact cd_arm (hP.arms.quot k cv) (fun hG => hG.arms.quot k cv) hn' hi hd hok hR hS hF hden
      hPD hIM
  | indDecl block nP =>
    rw [checkDeclE.arm1 _ _ _ _ _ (by rw [hw0, hdecl.1])]
    have hdecl' : IndDeclAt (m.arr64 DECL) (m.arr64 DLP) i.toNat block nP := by
      have := hR.decls.recs i.toNat hi
      rw [hdi] at this; exact this
    have hFB := hFD _ hi _ _ hdi
    have hlpd := hLD _ hi _ _ hdi
    have hD : (m.arr64 DECL).size < 2 ^ 63 := hR.decls.dsize
    have hP' : (m.arr64 DLP).size < 2 ^ 63 := hR.decls.psize
    obtain ⟨F, hFs, hFcl⟩ := hP.indIn
    refine RefE.onlySim (fun _ => checkDeclE.k_ind_block_to_erec.none ..) (fun _ _ h => h)
      fun r1 m1 c1 => ?_
    rw [checkDeclE.k_ind_block_to_erec.arm1]
    obtain ⟨hS1, hg1, hf1, -, hl1, hdec1, htop1⟩ :=
      indBlockToErec_ok hP.ibe c1 hS.stage hdecl' hFB hD hP'
    have hT1 : StageT dn vis fe m1 a :=
      ⟨hS1, hS.twin.frame hf1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        by rw [pinW_frame hf1 (by decide)]; exact hS.flag⟩
    have hfs1 := (run_memFrame hFcl (hFs _ (by decide)) (run_of_callW c1)).1
    have hIM1 : IndMemos m1 :=
      hIM.frame hf1 (fun b hb => by simp at hb; subst hb; decide)
        (fun x hx => by simp at hx; subst hx; decide)
    have hw : (rdW (m1.arr64 DECL) (5 + 8 * i)).toNat = nP := by
      rw [hf1.1 DECL (by decide) (by decide)]
      have h0 : dw (m.arr64 DECL) i.toNat 0 ≠ 0 := by rw [hdecl'.1]; decide
      rw [rdW_dwI hD h0 rfl (by decide)]
      exact hdecl'.2.1
    obtain ⟨env, hFo⟩ := hF
    rcases c2 : callE p n "check_ind_decl"
        [vis, r1.headD 0, r1.tail.headD 0, rdW (m1.arr64 DECL) (5 + 8 * i)] m1 with e2 | ⟨r2, m2⟩
    · rw [checkDeclE.k_check_ind_decl.none]
      exact fun hG => hG.ind pins n hn' m1 a vis fe env block nP _ _ _ hl1 hw hdec1 htop1 hFB hT1
        hok hFo hden hlpd hPD hIM1 e2 c2
    rw [checkDeclE.k_check_ind_decl.arm1]
    have d2 := callW_of_callE c2
    obtain ⟨fe', a', hrun, hS2, hcm, hg2, hIM2⟩ := hP.ind pins n hn' m1 m2 a vis fe env block nP
      _ _ _ r2 hl1 hw hdec1 htop1 hFB hT1 hok hFo hden hlpd hPD hIM1 d2
    have hfs2 := (run_memFrame hFcl (hFs _ (by decide)) (run_of_callW d2)).1
    have hL2 := hR.of_step hS2 (hfs1.trans hfs2) (IWGrow.erecPExt (hg1.trans hg2))
    exact RefE.ret hrun ⟨by simpa using hL2, hcm, hIM2, hg1.trans hg2⟩

/-- **`check_decl` refines `checkDecl` under `StageT`**, for the front's record kinds: the ok
half of `cd_ref`. -/
@[refines_part ConRon.Arena.checkDecl "check_decl(i, vis): the front's records (kinds 1-6), under StageT"]
theorem checkDecl_loopT {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {p : Prog} (hP : CdProg pins dn ds p) (hFD : FrontDecls ds)
    (hLD : DeclsLpsDn dn ds) :
    CheckDeclSpecT V pins dn ds p := by
  intro n hn s₀ a₀ vis fe i hi hok hR hS hF hden hPD hIM
  refine triple_post (RefE.triple (checkDecl_specE p hP.cd.cd n s₀ i vis)
    (cd_ref hP hFD hLD (by omega) hi hok hR hS hF hden hPD hIM)) ?_
  rintro r s' ⟨hl, x, a', run, hR'⟩
  obtain ⟨hok', hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok', by rw [hst, hres]; exact hR'.loop, hR'.core, hR'.ind, hR'.grow⟩

end L.Arena
