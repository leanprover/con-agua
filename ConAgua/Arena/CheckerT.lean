import ConAgua.Arena.LoopT
import ConAgua.Arena.StageC
import ConAgua.Arena.DeclArmT

/-!
# Phase A under `StageT` (lane `loopt2`)

Phase A's step runs its callees from `StageT`: at each loop head the twin's invariants `TwinOK`
come from the fold's (`TwinFold`, con-ron's `FoldOK`) and the memory's half (`TwinMem`: three
sizes, the core's memos `CoreMemos`, the name decoder's readbacks), which the fold carries
(`LoopMem`, `CoreMemos`). The bracket's opening keeps `TwinOK` (`TwinOK.flush`, `TwinOK.enter`);
`install_value` and `check_decl`'s arms end with the stage relation at their environment and
`CoreMemos` (`ivW_genT`, `cdtW_okT`); the bracket's closing is a leaf (`LeafClosed`: it writes no
core memo); the whole step writes the loop's write set (`LoopClosed`), so `LoopMem` comes back.

`check_decl`'s arms but the theorem arm run through their `StageR` specs (`DeclCheckLoop.lean`)
and the interim contract `stubArm_keepsCoreMemos` (`sorry`, listed in the census): that they keep
`CoreMemos`. Their `StageT`/`StageC` versions replace it (`docs/design/loopt2.md`).

Moved here from `Checker.lean` and `DeclStepGo.lean`: `install_step_go`, `install_step`,
`install_decl_step`, the fold and `install_then_check` (their `StageR`-only versions are gone).
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsR DeclAt CVAt dw)

local notation "V" => ConLeche.CheckMode.verified

/-- The program hypotheses phase A under `StageT` takes beyond `DeclCallees`: the core's entry
points (`KnotStageProg`), the leaves' and the loop's write sets. -/
structure LoopCallees (dn : NIdx → Option ConLeche.Name) (p : Prog) : Prop
    extends DeclCallees dn p where
  knot : KnotStageProg p
  leaf : LeafClosed p
  loop : LoopClosed p

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

/-- The arm `check_decl` dispatches a one-constant record to, for the arms not yet under
`StageT`. -/
def StubArm : IDeclaration → FnName → Prop
  | .axiomDecl _, f => f = "check_decl_axiom"
  | .defnDecl _ _ _, f => f = "check_decl_defn"
  | .opaqueDecl _ _, f => f = "check_decl_opaque"
  | .quotDecl _ _, f => f = "check_decl_quot"
  | _, _ => False

/-- **Interim contract** (lane `loopt2`, `sorry`, listed in the census' sorry sources): the arms of
`check_decl` not yet under `StageT` (axiom, definition, opaque, quotient), run from `StageT` on
their record, keep the core's memos well formed. Their `StageT`/`StageC` versions (the way
`cdtW_okT` does the theorem arm) replace it. -/
theorem stubArm_keepsCoreMemos (hP : CheckDeclProg p) {d : IDeclaration} {f : FnName}
    (hf : StubArm d f) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (vis : Word)
    (fe : IFEnv) (pend : Array PendingCheck) (i : Word) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat]? = some d) (hok : ConRon.Bridge.StateOK a₀)
    (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds) (hS : StageT dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f [i, vis] ⦃fun _ s' => CoreMemos s'.mem; ⊤⦄ := by
  sorry

/-- The shape of an arm's spec at the loop's relation under `StageT`, for the record `d`: from
`StageT`, back to the loop's relation and the core's memos. -/
def ArmSpecT (p : Prog) (f : FnName) (d : IDeclaration) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (i : Word), i.toNat < ds.size → ds[i.toNat]? = some d →
    ConRon.Bridge.StateOK a₀ → LoopR pins dn s₀.mem a₀ vis fe pend ds →
    StageT dn vis fe s₀.mem a₀ →
  ⦃fun s => s = s₀⦄ invoke p (exec p n) f [i, vis]
  ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkDecl V pins fe d) a₀ ∧
    LoopR pins dn s'.mem (AM.st (checkDecl V pins fe d) a₀) (r.headD 0)
      (AM.res (checkDecl V pins fe d) a₀) pend ds ∧ CoreMemos s'.mem; ⊤⦄

/-- An arm's `StageR` spec and the interim contract. -/
theorem ArmSpec.withMemos (hP : CheckDeclProg p) {f : FnName} {d : IDeclaration}
    (hA : ArmSpec pins dn ds p f d) (hf : StubArm d f) : ArmSpecT pins dn ds p f d :=
  fun n hn s₀ a₀ vis fe pend i hi hd hok hR hS =>
    triple_post (triple_and (hA n s₀ a₀ vis fe pend i hi hd hok hR)
      (stubArm_keepsCoreMemos pins dn ds hP hf n hn s₀ a₀ vis fe pend i hi hd hok hR hS))
      fun _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩

/-- **`check_decl_thm` under `StageT`** (`cdtW_okT`). -/
theorem checkDeclThm_loopT (hA : ArmProg p) (hV : ValProg p) (hq : KnotStageProg p)
    (hp : p.lookup "check_decl_thm" = some checkDeclThm) (cv : IConstantVal) (v : EIdx) :
    ArmSpecT pins dn ds p "check_decl_thm" (.thmDecl cv v) := by
  intro n hn s₀ a₀ vis fe pend i hi hd _ hR hS
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun (cdt_specW p hp hV.rcp n s₀ i vis)
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (hA.closed.memFrame n (f := "check_decl_thm") (by decide) [i, vis] s₀)
  subst hs
  have hd' : ds[i.toNat] = .thmDecl cv v := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨fe', a', hrun', hS', hcm, hg'⟩ := cdtW_okT (pins := pins) hV hq hn hW hS hR.decls hi hd'
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok, ?_, hcm⟩
  rw [hst, hres]
  exact hR.of_step hS' hf (IWGrow.erecPExt hg')

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
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_decl" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkDecl mode pins fe (dsAt ds i)) a₀ ∧
      LoopR pins dn s'.mem (AM.st (checkDecl mode pins fe (dsAt ds i)) a₀) (r.headD 0)
        (AM.res (checkDecl mode pins fe (dsAt ds i)) a₀) pend ds ∧ CoreMemos s'.mem; ⊤⦄

end cd

/-- An arm's run through `callW`, under `StageT`. -/
theorem arm_callWT {p : Prog} {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {f : FnName} {d : IDeclaration} (hA : ArmSpecT pins dn ds p f d)
    {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {pend : Array PendingCheck} {i : Word} {r : List Word} (hi : i.toNat < ds.size)
    (hd : ds[i.toNat]? = some d) (hok : ConRon.Bridge.StateOK a)
    (hR : LoopR pins dn m a vis fe pend ds) (hS : StageT dn vis fe m a)
    (h : cdRet (callW p n f [i, vis] m) = some (r, m')) :
    AM.ok (checkDecl V pins fe d) a ∧
      LoopR pins dn m' (AM.st (checkDecl V pins fe d) a) (r.headD 0) (AM.res (checkDecl V pins fe d) a)
        pend ds ∧ CoreMemos m' := by
  cases h1 : callW p n f [i, vis] m with
  | none => rw [h1] at h; cases h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, cdRet_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s', hs', -, hok, hL, hc⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (hA n hn ⟨m, Locals.init []⟩ a vis fe pend i hi hd hok hR hS) h1
  subst hs'
  exact ⟨hok, by simpa using hL, hc⟩

/-- **`check_decl` refines `checkDecl` under `StageT`**, for the front's record kinds: the theorem
arm by `cdtW_okT`, the others by their `StageR` specs and the interim contract
`stubArm_keepsCoreMemos`. -/
@[refines_part ConRon.Arena.checkDecl "one-constant records (the front's kinds 1-5), under StageT"]
theorem checkDecl_loopT {p : Prog} (hP : CheckDeclProg p) (hq : KnotStageProg p)
    (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (hdn : DnInj dn)
    (ds : Array IDeclaration) : CheckDeclSpecT V pins dn ds p := by
  intro n hn s₀ a₀ vis fe pend i hi hok hR hS
  refine triple_post (cd_specW p hP.cd n s₀ i vis) ?_
  rintro r s' ⟨hl, h⟩
  refine ⟨hl, ?_⟩
  have hdecl := hR.decls.recs i.toNat hi
  have hds : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
  have hd : ds[i.toNat]? = some ds[i.toNat] := Array.getElem?_eq_getElem hi
  rw [hds]
  have h1 := hR.decls.room
  have h2 := hR.decls.dsize
  have hw0 : rdW (s₀.mem.arr64 DECL) (1 + 8 * i) = dw (s₀.mem.arr64 DECL) i.toNat 0 :=
    rdW_dw _ (by omega) (by decide) (by decide)
  cases n with
  | zero => simp [cdW] at h
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [cdW_step, hw0] at h
  generalize hdi : ds[i.toNat] = d at hdecl hd
  cases d with
  | axiomDecl cv =>
    rw [hdecl.1] at h
    simp only [cdSel, show (1 : Word) ≠ 6 by decide, if_false, if_true] at h
    exact arm_callWT ((checkDeclAxiom_loop pins dn ds hP hdn cv).withMemos pins dn ds hP rfl)
      hn' hi hd hok hR hS h
  | defnDecl cv v hh =>
    rw [hdecl.1] at h
    simp only [cdSel, show (2 : Word) ≠ 6 by decide, show (2 : Word) ≠ 1 by decide, if_false,
      if_true] at h
    exact arm_callWT ((checkDeclDefn_loop pins dn ds hP hdn cv v hh).withMemos pins dn ds hP rfl)
      hn' hi hd hok hR hS h
  | thmDecl cv v =>
    rw [hdecl.1] at h
    simp only [cdSel, show (3 : Word) ≠ 6 by decide, show (3 : Word) ≠ 1 by decide,
      show (3 : Word) ≠ 2 by decide, if_false, if_true] at h
    exact arm_callWT (checkDeclThm_loopT pins dn ds hP.arm hP.val hq hP.th cv v)
      hn' hi hd hok hR hS h
  | opaqueDecl cv v =>
    rw [hdecl.1] at h
    simp only [cdSel, show (4 : Word) ≠ 6 by decide, show (4 : Word) ≠ 1 by decide,
      show (4 : Word) ≠ 2 by decide, show (4 : Word) ≠ 3 by decide, if_false, if_true] at h
    exact arm_callWT ((checkDeclOpaque_loop pins dn ds hP hdn cv v).withMemos pins dn ds hP rfl)
      hn' hi hd hok hR hS h
  | quotDecl k cv =>
    rw [hdecl.1] at h
    simp only [cdSel, show (5 : Word) ≠ 6 by decide, show (5 : Word) ≠ 1 by decide,
      show (5 : Word) ≠ 2 by decide, show (5 : Word) ≠ 3 by decide, show (5 : Word) ≠ 4 by decide,
      if_false, if_true] at h
    exact arm_callWT ((checkDeclQuot_loop pins dn ds hP hdn k cv).withMemos pins dn ds hP rfl)
      hn' hi hd hok hR hS h
  | indDecl _ _ => exact hdecl.elim
  | basisDecl _ => exact hdecl.elim

end L.Arena
