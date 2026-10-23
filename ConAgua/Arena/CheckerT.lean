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

/-! ## `install_value` and `install_step_go` under `StageT` -/

/-- **`install_value` refines `ivT`** at the model level. -/
theorem ivW_okT {p : Prog} (hRp : RecProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {i ck vk : Word} {r : List Word}
    {ds : Array IDeclaration} (h : ivW p n m i vis ck vk = some (r, m'))
    (hS : StageT dn vis fe m a) (hD : DeclsR (m.arr64 DECL) (m.arr64 DLP) ds)
    (hi : i.toNat < ds.size) (hk : IvArgs ck vk (dsAt ds i)) :
    ∃ x a', (ivT fe (dsAt ds i)).run a = .ok (x, a') ∧ StageR dn (r.headD 0) x.1 m' a' ∧
      CoreMemos m' ∧ IWGrow m m' ∧ x.2 = decVG (erecP m') (r.tail.headD 0).toNat ∧ x.2 ≠ none := by
  have hd : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
  rw [hd] at hk ⊢
  cases hdi : ds[i.toNat] with
  | defnDecl cv v hint =>
    rw [hdi] at hk
    obtain ⟨rfl, rfl⟩ := hk
    obtain ⟨a2, a3, hrun2, hg3, -, hS', hcm, hg', hvg⟩ :=
      ivW_genT (ci := .defnInfo cv v hint) (k := .defn) hRp h hS hD hi (by rw [hdi]; rfl) rfl
    rw [hdi] at hrun2 hg3 hvg
    have hrun3 := hg3 (by decide)
    simp only [stepCV, stepVal] at hrun2 hrun3
    refine ⟨(fe.push (.defnInfo cv v hint), some ⟨.defn, cv, v⟩), a3, ?_, hS', hcm, hg',
      by simpa [stepCV, stepVal] using hvg.symm, by simp⟩
    simp only [ivT, StateT.run_bind, hrun2, exc_ok_bind', hrun3, stepCV, stepVal]
    rfl
  | thmDecl cv v =>
    rw [hdi] at hk
    obtain ⟨rfl, rfl⟩ := hk
    obtain ⟨a2, a3, hrun2, -, ha3, hS', hcm, hg', hvg⟩ :=
      ivW_genT (ci := .thmInfo cv) (k := .thm) hRp h hS hD hi (by rw [hdi]; rfl) rfl
    rw [hdi] at hrun2 hvg
    have := ha3 rfl
    subst this
    simp only [stepCV, stepVal] at hrun2
    refine ⟨(fe.push (.thmInfo cv), some ⟨.thm, cv, v⟩), a3, ?_, hS', hcm, hg',
      by simpa [stepCV, stepVal] using hvg.symm, by simp⟩
    simp only [ivT, StateT.run_bind, hrun2, exc_ok_bind', stepCV, stepVal]
    rfl
  | opaqueDecl cv v =>
    rw [hdi] at hk
    obtain ⟨rfl, rfl⟩ := hk
    obtain ⟨a2, a3, hrun2, hg3, -, hS', hcm, hg', hvg⟩ :=
      ivW_genT (ci := .axiomInfo cv) (k := .opaque) hRp h hS hD hi (by rw [hdi]; rfl) rfl
    rw [hdi] at hrun2 hg3 hvg
    have hrun3 := hg3 (by decide)
    simp only [stepCV, stepVal] at hrun2 hrun3
    refine ⟨(fe.push (.axiomInfo cv), some ⟨.opaque, cv, v⟩), a3, ?_, hS', hcm, hg',
      by simpa [stepCV, stepVal] using hvg.symm, by simp⟩
    simp only [ivT, StateT.run_bind, hrun2, exc_ok_bind', hrun3, stepCV, stepVal]
    rfl
  | axiomDecl _ => rw [hdi] at hk; exact hk.elim
  | quotDecl _ _ => rw [hdi] at hk; exact hk.elim
  | indDecl _ _ => rw [hdi] at hk; exact hk.elim
  | basisDecl _ => rw [hdi] at hk; exact hk.elim

/-! ## The callees' specs at the loop's relation -/

section loopSpecs
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

/-- **`install_value` refines `ivT`** under `StageT`, at the loop's relation (`ivW_okT`). -/
theorem installValue_loopT (hP : IvProg p) (hC : CvgProg p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
      (i ck vk : Word), i.toNat < ds.size → IvArgs ck vk (dsAt ds i) →
      LoopR pins dn s₀.mem a₀ vis fe pend ds → StageT dn vis fe s₀.mem a₀ →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_value" [i, vis, ck, vk]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ivT fe (dsAt ds i)) a₀ ∧
      LoopR pins dn s'.mem (AM.st (ivT fe (dsAt ds i)) a₀) (r.headD 0)
        (AM.res (ivT fe (dsAt ds i)) a₀).1 pend ds ∧
      (AM.res (ivT fe (dsAt ds i)) a₀).2 = decVG (erecP s'.mem) (r.tail.headD 0).toNat ∧
      (AM.res (ivT fe (dsAt ds i)) a₀).2 ≠ none ∧ CoreMemos s'.mem; ⊤⦄ := by
  intro n s₀ a₀ vis fe pend i ck vk hi hk hR hS
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (iv_specW p hP.iv hP.recP hP.ih hC n s₀ i vis ck vk)
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (hP.closed.memFrame n (f := "install_value") (by decide) [i, vis, ck, vk] s₀)
  subst hs
  obtain ⟨x, a', hrun', hS', hcm, hg', hvg, hne⟩ := ivW_okT hP.recP hW hS hR.decls hi hk
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok, ?_, by rw [hres]; exact hvg, by rw [hres]; exact hne, hcm⟩
  rw [hst, hres]
  exact hR.of_step hS' hf (IWGrow.erecPExt hg')

end loopSpecs

/-! ## The relational lemma of `install_step_go` -/

section istgOk
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

/-- What a run of the step body leaves, against the twin's `T`. -/
def IstgPost (pend : Array PendingCheck) (T : AM (IFEnv × Option ValueGroup)) (a : AState)
    (m' : Mem) (r : List Word) : Prop :=
  ∃ x a', T.run a = .ok (x, a') ∧ LoopR pins dn m' a' (r.headD 0) x.1 pend ds ∧
    x.2 = vgOut m' (r.tail.headD 0) (r.tail.tail.headD 0) ∧ (r.tail.headD 0 ≠ 0 → x.2 ≠ none) ∧
    CoreMemos m'

theorem istg_cd (hCD : CheckDeclSpecT mode pins dn ds p) {n : Nat} (hn : n ≤ 2 ^ 62) {m0 m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {pend : Array PendingCheck} {i : Word} {rc r : List Word}
    {T : AM (IFEnv × Option ValueGroup)} (hi : i.toNat < ds.size) (hok0 : ConRon.Bridge.StateOK a)
    (hR : LoopR pins dn m0 a vis fe pend ds) (hS : StageT dn vis fe m0 a)
    (hc : callW p n "check_decl" [i, vis] m0 = some (rc, m'))
    (hr : istgCD (some (rc, m')) = some (r, m'))
    (hT : T.run a = (cdT mode pins fe (dsAt ds i)).run a) :
    IstgPost pins dn ds pend T a m' r := by
  simp only [istgCD, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, -⟩ := hr
  obtain ⟨s', hs', -, hok, hL, hcm⟩ := triple_of_callW (s₀ := ⟨m0, Locals.init []⟩)
    (hCD n hn ⟨m0, Locals.init []⟩ a vis fe pend i hi hok0 hR hS) hc
  have hrun := AM.run_of_ok _ _ hok
  refine ⟨_, _, hT.trans (cdT_run hrun), ?_, ?_, ?_, hs' ▸ hcm⟩
  · simpa [hs'] using hL
  · simp [vgOut]
  · simp

theorem istg_iv (hP : IvProg p) (hC : CvgProg p) {n : Nat} {m0 m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {pend : Array PendingCheck} {i ck vk : Word} {rv r : List Word}
    {T : AM (IFEnv × Option ValueGroup)} (hi : i.toNat < ds.size) (hk : IvArgs ck vk (dsAt ds i))
    (hR : LoopR pins dn m0 a vis fe pend ds) (hS : StageT dn vis fe m0 a)
    (hc : callW p n "install_value" [i, vis, ck, vk] m0 = some (rv, m'))
    (hr : istgIV (some (rv, m')) = some (r, m')) (hT : T.run a = (ivT fe (dsAt ds i)).run a) :
    IstgPost pins dn ds pend T a m' r := by
  simp only [istgIV, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, -⟩ := hr
  obtain ⟨s', hs', -, hok, hL, hvg, hne, hcm⟩ := triple_of_callW (s₀ := ⟨m0, Locals.init []⟩)
    (installValue_loopT pins dn ds p hP hC n ⟨m0, Locals.init []⟩ a vis fe pend i ck vk hi hk hR hS) hc
  have hrun := AM.run_of_ok _ _ hok
  subst hs'
  refine ⟨_, _, hT.trans hrun, by simpa using hL, ?_, fun _ => hne, hcm⟩
  simp only [List.headD_cons, List.tail_cons, vgOut, show (1 : Word) ≠ 0 by decide, if_false]
  exact hvg

theorem istgW_ok (hm : mode = .verified) (hCD : CheckDeclSpecT mode pins dn ds p) (hP : IvProg p) (hC : CvgProg p) {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {pend : Array PendingCheck} {i : Word} {r : List Word}
    (h : istgW p n m i vis = some (r, m')) (hR : LoopR pins dn m a vis fe pend ds)
    (hTw : TwinOK dn m a fe) (hfl : pinW m 0 ≠ 0)
    (hi : i.toNat < ds.size) (hok0 : ConRon.Bridge.StateOK a) :
    IstgPost pins dn ds pend (installStepGo mode pins fe (dsAt ds i)) a m' r := by
  cases n with
  | zero => simp [istgW] at h
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [istgW_step, show iwResetW m = some ([], m.set64 CTL 200 0) from rfl, istgK0_some] at h
  have hR0 := hR.reset
  have hS0 : StageT dn vis fe (m.set64 CTL 200 0) a :=
    ⟨⟨hR0.check, hR0.iw⟩,
      hTw.frame (MemFrame.setCtl m 200 0) ⟨by simp, by simp⟩ ⟨by decide, by decide⟩
        ⟨by simp, by simp, by simp⟩ ⟨by decide, by decide, by decide⟩ ⟨by simp, by simp, by simp⟩
        ⟨by decide, by decide, by decide⟩,
      by rw [pinW_frame (MemFrame.setCtl m 200 0) (by simp)]; exact hfl⟩
  generalize m.set64 CTL 200 0 = m0 at h hR0 hS0
  have hdecl : DeclAt (m0.arr64 DECL) (m0.arr64 DLP) i.toNat (dsAt ds i) := by
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
  rw [hw0, hw1] at h
  generalize hd : dsAt ds i = d at hdecl
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
  cases d with
  | axiomDecl cv =>
    obtain ⟨hk, -⟩ := hdecl
    rw [hk] at h
    simp only [show (1 : Word) ≠ 2 by decide, show (1 : Word) ≠ 3 by decide,
      show (1 : Word) ≠ 4 by decide, if_false] at h
    cases hc : callW p n "check_decl" [i, vis] m0 with
    | none => rw [hc] at h; simp [istgCD] at h
    | some rcm =>
    obtain ⟨rc, m1⟩ := rcm
    rw [hc] at h
    have hm1 : m1 = m' := by simp [istgCD] at h; exact h.2
    subst hm1
    rw [← hd]
    exact istg_cd mode pins dn ds p hCD hn' hi hok0 hR0 hS0 hc h (by rw [hd]; rfl)
  | quotDecl k cv =>
    obtain ⟨hk, -⟩ := hdecl
    rw [hk] at h
    simp only [show (5 : Word) ≠ 2 by decide, show (5 : Word) ≠ 3 by decide,
      show (5 : Word) ≠ 4 by decide, if_false] at h
    cases hc : callW p n "check_decl" [i, vis] m0 with
    | none => rw [hc] at h; simp [istgCD] at h
    | some rcm =>
    obtain ⟨rc, m1⟩ := rcm
    rw [hc] at h
    have hm1 : m1 = m' := by simp [istgCD] at h; exact h.2
    subst hm1
    rw [← hd]
    exact istg_cd mode pins dn ds p hCD hn' hi hok0 hR0 hS0 hc h (by rw [hd]; rfl)
  | thmDecl cv v =>
    obtain ⟨hk, -⟩ := hdecl
    rw [hk] at h
    simp only [show (3 : Word) ≠ 2 by decide, if_false, if_true] at h
    cases hc : callW p n "install_value" [i, vis, 2, 1] m0 with
    | none => rw [hc] at h; simp [istgIV] at h
    | some rvm =>
    obtain ⟨rv, m1⟩ := rvm
    rw [hc] at h
    have hm1 : m1 = m' := by simp [istgIV] at h; exact h.2
    subst hm1
    rw [← hd]
    exact istg_iv pins dn ds p hP hC hi (by rw [hd]; exact ⟨rfl, rfl⟩) hR0 hS0 hc h (by rw [hd]; rfl)
  | defnDecl cv v hint =>
    obtain ⟨hk, hcv, -⟩ := hdecl
    rw [hk] at h
    simp only [if_true] at h
    cases hp : pinInW n m0 (dw (m0.arr64 DECL) i.toNat 1 &&& 4294967295) 15 30 with
    | none => rw [hp] at h; simp [istgPin] at h
    | some c =>
    rw [hp, istgPin_some] at h
    obtain ⟨hF, hiff⟩ := pinT hcv hp (by decide) (by decide) (by decide)
    have hT := installStepGo_defn mode pins fe hF cv v hint
    rw [pinnedDefnL_eq] at hT
    by_cases hc0 : c ≠ 0
    · rw [if_pos hc0] at h
      have hpin : ((List.range' 15 15).map fun j => (decI (pinW m0 j) : NIdx)).contains cv.name =
          true := hiff.mp hc0
      rw [if_pos hpin] at hT
      cases hc : callW p n "check_decl" [i, vis] m0 with
      | none => rw [hc] at h; simp [istgCD] at h
      | some rcm =>
      obtain ⟨rc, m1⟩ := rcm
      rw [hc] at h
      have hm1 : m1 = m' := by simp [istgCD] at h; exact h.2
      subst hm1
      rw [← hd]
      exact istg_cd mode pins dn ds p hCD hn' hi hok0 hR0 hS0 hc h (by rw [hd]; exact hT)
    · rw [if_neg hc0] at h
      have hpin : ¬ ((List.range' 15 15).map fun j => (decI (pinW m0 j) : NIdx)).contains cv.name =
          true := fun h' => hc0 (hiff.mpr h')
      rw [if_neg hpin] at hT
      cases hc : callW p n "install_value" [i, vis, 1, 0] m0 with
      | none => rw [hc] at h; simp [istgIV] at h
      | some rvm =>
      obtain ⟨rv, m1⟩ := rvm
      rw [hc] at h
      have hm1 : m1 = m' := by simp [istgIV] at h; exact h.2
      subst hm1
      rw [← hd]
      exact istg_iv pins dn ds p hP hC hi (by rw [hd]; exact ⟨rfl, rfl⟩) hR0 hS0 hc h (by rw [hd]; exact hT)
  | opaqueDecl cv v =>
    obtain ⟨hk, hcv, -⟩ := hdecl
    rw [hk] at h
    simp only [show (4 : Word) ≠ 2 by decide, show (4 : Word) ≠ 3 by decide, if_false,
      if_true] at h
    cases hp : pinInW n m0 (dw (m0.arr64 DECL) i.toNat 1 &&& 4294967295) 44 46 with
    | none => rw [hp] at h; simp [istgPin] at h
    | some c =>
    rw [hp, istgPin_some] at h
    obtain ⟨hF, hiff⟩ := pinT hcv hp (by decide) (by decide) (by decide)
    have hT := installStepGo_opaque mode pins fe hF cv v
    by_cases hc0 : c ≠ 0
    · rw [if_pos hc0] at h
      have hpin : ((List.range' 44 2).map fun j => (decI (pinW m0 j) : NIdx)).contains cv.name =
          true := hiff.mp hc0
      rw [if_pos (show (pinnedOpaqueL m0).contains cv.name = true from hpin)] at hT
      cases hc : callW p n "check_decl" [i, vis] m0 with
      | none => rw [hc] at h; simp [istgCD] at h
      | some rcm =>
      obtain ⟨rc, m1⟩ := rcm
      rw [hc] at h
      have hm1 : m1 = m' := by simp [istgCD] at h; exact h.2
      subst hm1
      rw [← hd]
      exact istg_cd mode pins dn ds p hCD hn' hi hok0 hR0 hS0 hc h (by rw [hd]; exact hT)
    · rw [if_neg hc0] at h
      have hpin : ¬ ((List.range' 44 2).map fun j => (decI (pinW m0 j) : NIdx)).contains cv.name =
          true := fun h' => hc0 (hiff.mpr h')
      rw [if_neg (show ¬ (pinnedOpaqueL m0).contains cv.name = true from hpin)] at hT
      cases hc : callW p n "install_value" [i, vis, 0, 2] m0 with
      | none => rw [hc] at h; simp [istgIV] at h
      | some rvm =>
      obtain ⟨rv, m1⟩ := rvm
      rw [hc] at h
      have hm1 : m1 = m' := by simp [istgIV] at h; exact h.2
      subst hm1
      rw [← hd]
      exact istg_iv pins dn ds p hP hC hi (by rw [hd]; exact ⟨rfl, rfl⟩) hR0 hS0 hc h (by rw [hd]; exact hT)
  | indDecl _ _ => exact absurd hdecl id
  | basisDecl _ => exact absurd hdecl id

end istgOk

/-! ## `install_step_go` refines `installStepGo` -/

section spec
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

/-- **`install_step_go` refines `installStepGo`** under `StageT` (through `check_decl`'s spec,
`CheckDeclSpecT`, and `install_value`'s, `installValue_loopT`): the new view and environment, the
value group out of the flag and record, the core's memos well formed. -/
@[refines ConRon.Arena.installStepGo]
theorem installStepGo_specT (hm : mode = .verified) (hCD : CheckDeclSpecT mode pins dn ds p)
    (hG : IstgProg p) (hP : IvProg p) (hC : CvgProg p) :
    ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv)
      (pend : Array PendingCheck) (i : Word) (hi : i.toNat < ds.size), ConRon.Bridge.StateOK a₀ →
      LoopR pins dn s₀.mem a₀ vis fe pend ds → TwinOK dn s₀.mem a₀ fe → pinW s₀.mem 0 ≠ 0 →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_step_go" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installStepGo mode pins fe (dsAt ds i)) a₀ ∧
      LoopR pins dn s'.mem (AM.st (installStepGo mode pins fe (dsAt ds i)) a₀) (r.headD 0)
        (AM.res (installStepGo mode pins fe (dsAt ds i)) a₀).1 pend ds ∧
      (AM.res (installStepGo mode pins fe (dsAt ds i)) a₀).2 =
        vgOut s'.mem (r.tail.headD 0) (r.tail.tail.headD 0) ∧
      (r.tail.headD 0 ≠ 0 → (AM.res (installStepGo mode pins fe (dsAt ds i)) a₀).2 ≠ none) ∧
      CoreMemos s'.mem; ⊤⦄ := by
  intro n hn s₀ a₀ vis fe pend i hi hok0 hR hTw hfl
  refine triple_post (istg_specW p hG n s₀ i vis) ?_
  rintro r s' ⟨hloc, hW⟩
  obtain ⟨x, a', hrun, hL, hvg, hne, hcm⟩ :=
    istgW_ok mode pins dn ds p hm hCD hP hC hn hW hR hTw hfl hi hok0
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hloc, hok, by rw [hst, hres]; exact hL, by rw [hres]; exact hvg,
    fun h => by rw [hres]; exact hne h, hcm⟩

end spec


/-! ## The bracket under `StageT`: `TwinOK` across the opening, `CoreMemos` across the closing -/

section bracket
variable (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration) (p : Prog)
  (hb : BracketProg p)
include hb

/-- **`flush_caches` keeps `TwinOK`** (and the loop's relation, the pin flag). -/
theorem flush_loopW {pins : List INatOpPinSet} (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word)
    (fe : IFEnv) (pend : Array PendingCheck) (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds)
    (hTw : TwinOK dn s₀.mem a₀ fe) (hfl : pinW s₀.mem 0 ≠ 0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "flush_caches" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok flushCaches a₀ ∧
      LoopR pins dn s'.mem (AM.st flushCaches a₀) vis fe pend ds ∧
      TwinOK dn s'.mem (AM.st flushCaches a₀) fe ∧ pinW s'.mem 0 ≠ 0; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hL⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (flush_loop dn ds p hb n s₀ a₀ vis fe pend hR)
  obtain ⟨-, -, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun (flushCaches_spec p hb.fl n s₀)
  subst hs
  have hf : MemFrame [] flushCtl s.mem s'.mem := by rw [hm]; exact flushMem_frame _
  refine ⟨hloc, hok, hL, ?_, by rw [pinW_frame hf (by simp)]; exact hfl⟩
  rw [flushCaches_st]
  exact (hTw.frameLo hf (fun x h => by simp [flushCtl] at h; rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)).flush

/-- **`scratch_enter` keeps `TwinOK`** from a loop head (the store well formed, the scratch tier
off). -/
theorem enter_loopW {pins : List INatOpPinSet} (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word)
    (fe : IFEnv) (pend : Array PendingCheck) (hwf : StoreWF a₀.store)
    (hoff : a₀.store.scratchOn = false) (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds)
    (hTw : TwinOK dn s₀.mem a₀ fe) (hfl : pinW s₀.mem 0 ≠ 0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "scratch_enter" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok enterScratch a₀ ∧
      LoopR pins dn s'.mem (AM.st enterScratch a₀) vis fe pend ds ∧
      TwinOK dn s'.mem (AM.st enterScratch a₀) fe ∧ pinW s'.mem 0 ≠ 0; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hok, hL⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (enter_loop dn ds p hb n s₀ a₀ vis fe pend hR)
  obtain ⟨-, -, -, -, -, -, -, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchEnter_spec p hb.se hb.sr hb.bm hb.lf hb.im hb.fm n s₀)
  subst hs
  have hf : MemFrame [] (resetCtl ++ memoCtl) s.mem s'.mem := by rw [hm]; exact enterMem_frame _
  refine ⟨hloc, hok, hL, ?_, by rw [pinW_frame hf (by simp)]; exact hfl⟩
  rw [enterScratch_st]
  exact (hTw.frameLo hf (fun x h => by
    simp [resetCtl, scratchCnts, memoCtl, SCB] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      <;> decide)).enter hwf hoff

end bracket

section leaves
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/-- `is_none` keeps the core's memos (a leaf). -/
theorem isNone_refinesC (hlc : LeafClosed p) (hb : BracketProg p)
    (hp : p.lookup "is_none" = some isNoneL) (n : Nat) (s₀ : St) (a₀ : AState)
    (vis v2 : Word) (fe' : IFEnv) (pend : Array PendingCheck)
    (hR : LoopR pins dn s₀.mem a₀ v2 fe' pend ds) (hc : CoreMemos s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "is_none" [vis, v2]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (isNoneT vis.toNat fe' pend) a₀ ∧
      LoopR pins dn s'.mem (AM.st (isNoneT vis.toNat fe' pend) a₀) v2
        (AM.res (isNoneT vis.toNat fe' pend) a₀).1 (AM.res (isNoneT vis.toNat fe' pend) a₀).2 ds ∧
      CoreMemos s'.mem; ⊤⦄ :=
  triple_post (triple_leafMemos hlc (leaf_mem _ rfl)
      (isNone_refines pins dn ds p hb hp n s₀ a₀ vis v2 fe' pend hR) hc)
    fun _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩

/-- `is_some` keeps the core's memos (a leaf). -/
theorem isSome_refinesC (hlc : LeafClosed p) (hb : BracketProg p)
    (hpp : p.lookup "pend_push" = some pendPushL)
    (hp : p.lookup "is_some" = some isSomeL) (n : Nat) (s₀ : St) (a₀ : AState)
    (i vis v2 g : Word) (fe' : IFEnv) (pend : Array PendingCheck) (vg : ValueGroup)
    (hg : decVG (erecP s₀.mem) g.toNat = some vg)
    (hR : LoopR pins dn s₀.mem a₀ v2 fe' pend ds) (hc : CoreMemos s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "is_some" [i, vis, v2, g]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (isSomeT i.toNat vis.toNat fe' pend vg) a₀ ∧
      LoopR pins dn s'.mem (AM.st (isSomeT i.toNat vis.toNat fe' pend vg) a₀) v2
        (AM.res (isSomeT i.toNat vis.toNat fe' pend vg) a₀).1
        (AM.res (isSomeT i.toNat vis.toNat fe' pend vg) a₀).2 ds ∧ CoreMemos s'.mem; ⊤⦄ :=
  triple_post (triple_leafMemos hlc (leaf_mem _ rfl)
      (isSome_refines pins dn ds p hb hpp hp n s₀ a₀ i vis v2 g fe' pend vg hg hR) hc)
    fun _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩

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

/-- **`and_pin_ok` keeps `TwinOK`** (a leaf, the twin state unchanged on the front's records), the
pin flag and the scratch tier's flag. -/
theorem andPinOk_refinesT (hlc : LeafClosed p) (hp : p.lookup "and_pin_ok" = some andPinOkL)
    (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
    (i : Word) (hi : i.toNat < ds.size) (hpk : ConRon.Bridge.PinsOK a₀)
    (hoff : a₀.store.scratchOn = false) (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds)
    (hTw : TwinOK dn s₀.mem a₀ fe) (hfl : pinW s₀.mem 0 ≠ 0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "and_pin_ok" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (andPinOk (dsAt ds i)) a₀ ∧
      LoopR pins dn s'.mem (AM.st (andPinOk (dsAt ds i)) a₀) vis fe pend ds ∧
      AM.res (andPinOk (dsAt ds i)) a₀ = (r.headD 0 != 0) ∧
      TwinOK dn s'.mem (AM.st (andPinOk (dsAt ds i)) a₀) fe ∧ pinW s'.mem 0 ≠ 0 ∧
      (AM.st (andPinOk (dsAt ds i)) a₀).store.scratchOn = false; ⊤⦄ := by
  have hpd : ∀ b k, dsAt ds i ≠ .indDecl b k := by
    intro b k e
    have := hR.decls.recs i.toNat hi
    have e' : ds[i.toNat]?.getD default = .indDecl b k := by simpa [dsAt, Array.getD, hi] using e
    simp only [Array.getElem?_eq_getElem hi, Option.getD_some] at e'
    rw [e'] at this; exact this
  refine triple_post (triple_and (andPinOk_refines (pins := pins) dn ds p hp n s₀ a₀ vis fe pend i hi hR)
    (invoke_memFrame hlc n (leaf_mem _ rfl) [i] s₀)) fun r s' ⟨⟨h1, h2, h3, h4⟩, hf, _⟩ => ?_
  have e := andPinOk_st_one hpk hpd h2
  refine ⟨h1, h2, h3, h4, by rw [e]; exact hTw.leaf hf, ?_, by rw [e]; exact hoff⟩
  simp only [pinW, hf.1 PINS leafA_pins (by decide)]; exact hfl

end leaves

/-! ## Phase A's step and fold under `StageT` -/

section skel
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

/-- `install_step`, stated over the pieces of `installStep` (`installStep_ok` assembles them). -/
theorem installStep_pieces (hm : mode = .verified) (hdc : LoopCallees dn p) (hb : BracketProg p) (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hp : p.lookup "install_step" = some installStepL) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (i vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (hi : i.toNat < ds.size)
    (hok : ConRon.Bridge.StateOK a₀) (hoff : a₀.store.scratchOn = false)
    (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds) (hTw : TwinOK dn s₀.mem a₀ fe)
    (hfl : pinW s₀.mem 0 ≠ 0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_step" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ CoreMemos s'.mem ∧ AM.ok flushCaches a₀ ∧ AM.ok enterScratch (AM.st flushCaches a₀) ∧ AM.ok (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)) ∧
      AM.ok (installStepK i.toNat vis.toNat pend (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))) (AM.st (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))) ∧ LoopR pins dn s'.mem (AM.st (installStepK i.toNat vis.toNat pend (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))) (AM.st (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))) (r.headD 0) (AM.res (installStepK i.toNat vis.toNat pend (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))) (AM.st (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))).1
        (AM.res (installStepK i.toNat vis.toNat pend (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))) (AM.st (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))).2 ds; ⊤⦄ := by
  have hK0 : (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).2 = none → (installStepK i.toNat vis.toNat pend (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))) = isNoneT vis.toNat (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).1 pend :=
    fun h => installStepK_none _ _ _ _ h
  have hK1 : (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).2 ≠ none → (installStepK i.toNat vis.toNat pend (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀)))) = isSomeT i.toNat vis.toNat (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).1 pend ((AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).2.getD default) := by
    intro h
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp h
    rw [installStepK_some _ _ _ _ x hx, hx]; rfl
  have hsome : (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).2 ≠ none →
      (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).2 =
        some ((AM.res (installStepGo mode pins fe (dsAt ds i))
          (AM.st enterScratch (AM.st flushCaches a₀))).2.getD default) := by
    intro h; obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp h; rw [hx]; rfl
  have hwf' : StoreWF (AM.st flushCaches a₀).store := by rw [flushCaches_st]; exact hok.wf
  have hoff' : (AM.st flushCaches a₀).store.scratchOn = false := by rw [flushCaches_st]; exact hoff
  rw [invoke_eq _ hp]
  simp only [callFn, installStepL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hn' : n ≤ 2 ^ 62 := by omega
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        (flush_loopW (pins := pins) dn ds p hb n · a₀ vis fe pend),
        (enter_loopW (pins := pins) dn ds p hb n · (AM.st flushCaches a₀) vis fe pend hwf' hoff'),
        (installStepGo_specT mode pins dn ds p hm (hm ▸ checkDecl_loopT hdc.cd hdc.knot pins dn hdc.dninj ds) hdc.istg hdc.iv hdc.cvg n hn' · (AM.st enterScratch (AM.st flushCaches a₀)) · fe pend · · (TwinFold.enterAM hok)),
        (isNone_refinesC pins dn ds p hdc.leaf hb hpn n · (AM.st (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))) · · (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).1 pend),
        (isSome_refinesC pins dn ds p hdc.leaf hb hpp hps n · (AM.st (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))) · · · · (AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).1 pend ((AM.res (installStepGo mode pins fe (dsAt ds i)) (AM.st enterScratch (AM.st flushCaches a₀))).2.getD default))] <;>
      -- the view `vis` is read after three calls: four `LocEq` hops (depth, not search)
      finish (gen := 20) [vgOut]

/-- **`install_step` refines `installStep`** under `StageT` (the core's memos come back). -/
@[refines ConRon.Arena.installStep]
theorem installStep_refines (hm : mode = .verified) (hdc : LoopCallees dn p) (hb : BracketProg p) (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hp : p.lookup "install_step" = some installStepL) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (i vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (hi : i.toNat < ds.size)
    (hok : ConRon.Bridge.StateOK a₀) (hoff : a₀.store.scratchOn = false)
    (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds) (hTw : TwinOK dn s₀.mem a₀ fe)
    (hfl : pinW s₀.mem 0 ≠ 0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_step" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ CoreMemos s'.mem ∧ AM.ok (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀ ∧
      LoopR pins dn s'.mem (AM.st (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀) (r.headD 0) (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀).1 (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) a₀).2 ds; ⊤⦄ := by
  have hv := hR.vis
  refine triple_post (installStep_pieces mode pins dn ds p hm hdc hb hpp hpn hps hp n hn s₀ a₀ i vis fe pend hi hok hoff hR hTw hfl)
    fun r s' ⟨hl, hcm, h1, h2, h3, h4, h5⟩ => ?_
  rw [← hv] at h4 h5
  obtain ⟨o, st, rs⟩ := installStep_ok mode pins i.toNat fe pend (dsAt ds i) a₀ h1 h2 h3 h4
  exact ⟨hl, hcm, o, by rw [st, rs]; exact h5⟩

/-- **`install_decl_step` refines `installDeclStep`**: a returning run is the twin's `.ok` with
the position advanced. -/
@[refines ConRon.Arena.installDeclStep]
theorem installDeclStep_core (hm : mode = .verified) (hb : BracketProg p) (hdc : LoopCallees dn p)
    (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hpi : p.lookup "install_step" = some installStepL)
    (hp : p.lookup "install_decl_step" = some installDeclStepL) (n : Nat) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState)
    (i vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (hi : i.toNat < ds.size)
    (hT : TwinFold pins ds fe pend a₀) (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds)
    (hTw : TwinOK dn s₀.mem a₀ fe) (hfl : pinW s₀.mem 0 ≠ 0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_decl_step" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ CoreMemos s'.mem ∧ AM.ok (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ ∧
      AM.res (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ = .ok (i.toNat + 1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2) ∧
      LoopR pins dn s'.mem (AM.st (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀) (r.headD 0) (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1 (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2 ds; ⊤⦄ := by
  have hok := installDeclStep_ok mode pins (i.toNat, fe, pend) (dsAt ds i) a₀
  have hokA : AM.ok (andPinOk (dsAt ds i)) a₀ → ConRon.Bridge.StateOK (AM.st (andPinOk (dsAt ds i)) a₀) := by
    have e : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
    rw [e]; exact hT.andPinAM hi
  have hpk : ConRon.Bridge.PinsOK a₀ := by obtain ⟨_, hF, _⟩ := hT.fold; exact hF.check.pins
  rw [invoke_eq _ hp]
  simp only [callFn, installDeclStepL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hn' : n ≤ 2 ^ 62 := by omega
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        (andPinOk_refinesT pins dn ds p hdc.leaf hdc.and_pin_ok n · a₀ vis fe pend · · hpk hT.off),
        (installStep_refines mode pins dn ds p hm hdc hb hpp hpn hps hpi n hn' · (AM.st (andPinOk (dsAt ds i)) a₀) · · fe pend ·)] <;>
      finish

set_option maxRecDepth 8000 in
/-- `install_decl_step` is one of the loop's functions. -/
theorem installDeclStep_loop : "install_decl_step" ∈ loopFns := List.mem_of_getElem? (i := 615) rfl

/-- **`install_decl_step` refines `installDeclStep`** under `StageT`: a returning run is the
twin's `.ok` with the position advanced; the memory's half of the twin's invariants (`LoopMem`,
`CoreMemos`) comes back (the loop's write set, the twin's persistent tier only growing). -/
@[refines ConRon.Arena.installDeclStep]
theorem installDeclStep_refines (hm : mode = .verified) (hb : BracketProg p) (hdc : LoopCallees dn p)
    (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hpi : p.lookup "install_step" = some installStepL)
    (hp : p.lookup "install_decl_step" = some installDeclStepL) (n : Nat) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState)
    (i vis : Word) (fe : IFEnv) (pend : Array PendingCheck) (hi : i.toNat < ds.size)
    (hT : TwinFold pins ds fe pend a₀) (hR : LoopR pins dn s₀.mem a₀ vis fe pend ds)
    (hM : LoopMem dn s₀.mem a₀) (hc : CoreMemos s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_decl_step" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ ∧
      AM.res (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ = .ok (i.toNat + 1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2) ∧
      LoopR pins dn s'.mem (AM.st (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀) (r.headD 0) (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1 (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2 ds ∧
      LoopMem dn s'.mem (AM.st (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀) ∧
      CoreMemos s'.mem; ⊤⦄ := by
  have hTw : TwinOK dn s₀.mem a₀ fe := by
    obtain ⟨_, hF, _⟩ := hT.fold
    exact TwinOK.of_check hF.check ⟨hM.erec, hM.spn, hM.bstk, hc, fun k x e => (hM.dnP k x e).2⟩
  refine triple_post (triple_and
      (installDeclStep_core mode pins dn ds p hm hb hdc hpp hpn hps hpi hp n hn s₀ a₀ i vis fe pend hi
        hT hR hTw hM.flag)
      (invoke_memFrame hdc.loop n installDeclStep_loop [i, vis] s₀))
    fun r s' ⟨⟨hl, hcm, ho, hres, hL⟩, hf, _⟩ => ?_
  have e : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
  have hx : ConRon.Bridge.PExt a₀.store
      (AM.st (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀).store := by
    have hrun := AM.run_of_ok _ _ ho
    rw [hres] at hrun
    subst hm
    rw [e] at hrun ⊢
    exact (hT.step_pext hi hrun).2
  exact ⟨hl, ho, hres, hL, hM.step hf hx, hcm⟩

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
      (AM.res (installFold mode pins (k, fe, pend) (ds.toList.drop k)) a)

/-- `install_fold_go`'s spec at fuel `n`. -/
def FoldGoSpec (n : Nat) : Prop :=
  ∀ (s₀ : St) (a₀ : AState) (i cnt vis : Word) (fe : IFEnv) (pend : Array PendingCheck),
    i.toNat ≤ ds.size → cnt.toNat = ds.size → TwinFold pins ds fe pend a₀ →
    LoopR pins dn s₀.mem a₀ vis fe pend ds → LoopMem dn s₀.mem a₀ → CoreMemos s₀.mem →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_fold_go" [i, cnt, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ FoldPost mode pins dn ds s'.mem a₀ (r.headD 0) i.toNat fe pend; ⊤⦄

/-- `install_fold_next`'s spec at fuel `n`. -/
def FoldNextSpec (n : Nat) : Prop :=
  ∀ (s₀ : St) (a₀ : AState) (i cnt vis : Word) (fe : IFEnv) (pend : Array PendingCheck),
    i.toNat < ds.size → cnt.toNat = ds.size → TwinFold pins ds fe pend a₀ →
    LoopR pins dn s₀.mem a₀ vis fe pend ds → LoopMem dn s₀.mem a₀ → CoreMemos s₀.mem →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_fold_next" [i, cnt, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ FoldPost mode pins dn ds s'.mem a₀ (r.headD 0) i.toNat fe pend; ⊤⦄

section fold
variable (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hpi : p.lookup "install_step" = some installStepL)
    (hpd : p.lookup "install_decl_step" = some installDeclStepL)
    (hpg : p.lookup "install_fold_go" = some installFoldGoL)
    (hpx : p.lookup "install_fold_next" = some installFoldNextL) (hsz : ds.size < 2 ^ 63)
    (hb : BracketProg p) (hdc : LoopCallees dn p) (hm : mode = .verified)
include hpp hpn hps hpi hpd hpg hpx hsz hb hdc hm

theorem foldGo_step (n : Nat) (ih : FoldNextSpec mode pins dn ds p n) :
    FoldGoSpec mode pins dn ds p (n + 1) := by
  unfold FoldNextSpec at ih
  intro s₀ a₀ i cnt vis fe pend hi hc hT hR hM hcm
  have hlt : i ≠ cnt → i.toNat < ds.size := fun h => by
    have : i.toNat ≠ cnt.toNat := fun e => h (UInt64.toNat_inj.mp e)
    omega
  have hnil : i = cnt → FoldPost mode pins dn ds s₀.mem a₀ vis i.toNat fe pend := fun h => by
    have e : ds.toList.drop i.toNat = [] := by simp [h, hc]
    have := installFold_nil_ok mode pins (i.toNat, fe, pend) a₀
    simp only [FoldPost, e]
    refine ⟨this.1, ?_⟩
    rw [this.2.1, this.2.2]; exact ⟨by rw [h, hc], hR⟩
  have hmem : ∀ m : Mem, m = s₀.mem → FoldPost mode pins dn ds s₀.mem a₀ vis i.toNat fe pend →
      FoldPost mode pins dn ds m a₀ vis i.toNat fe pend := fun m h p => h ▸ p
  have hsz' : i = cnt → i.toNat = ds.size := fun h => by rw [h, hc]
  rw [invoke_eq _ hpg]
  simp only [callFn, installFoldGoL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (ih · a₀ · · · fe pend)] <;>
    finish

theorem foldNext_step (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (ih : FoldGoSpec mode pins dn ds p n) :
    FoldNextSpec mode pins dn ds p (n + 1) := by
  unfold FoldGoSpec at ih
  intro s₀ a₀ i cnt vis fe pend hi hc hT hR hM hcm
  have hn' : n ≤ 2 ^ 62 := by omega
  have h1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hstep : AM.ok (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ →
      AM.res (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ = .ok (i.toNat + 1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2) →
      TwinFold pins ds (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1
        (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2
        (AM.st (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀) := by
    have e : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
    subst hm; rw [e]
    exact hT.stepAM hi
  have h2 : (i + 1).toNat ≤ ds.size := by omega
  have hcons : ∀ (m : Mem) (v j : Word), j = i + 1 → AM.ok (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ → AM.res (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ = .ok (i.toNat + 1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2) →
      FoldPost mode pins dn ds m (AM.st (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀) v j.toNat (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1
        (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2 →
      FoldPost mode pins dn ds m a₀ v i.toNat fe pend := by
    intro m v j hj hok hres hp
    rw [hj, h1] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have e := drop_cons_dsAt ds i hi h1
    rw [h1] at e
    have := installFold_cons_ok mode pins (i.toNat, fe, pend) (i.toNat + 1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2) (dsAt ds i)
      (ds.toList.drop (i.toNat + 1)) a₀ hok hres hp1
    refine ⟨?_, ?_⟩
    · rw [e]; exact this.1
    · rw [e, this.2.1, this.2.2]; exact hp2
  have hloc : ∀ (s : St) (m : Mem) (rs : List Word), LocEq s { mem := m, loc := Locals.init [i, cnt, vis] } →
      (s.setLocs [3] rs).loc 0 = i ∧ (s.setLocs [3] rs).loc 1 = cnt := by
    intro s m rs h; grind [lang_grind]
  have hpre : ∀ (s : St) (rs : List Word) (A : AState) (fe' : IFEnv) (pend' : Array PendingCheck),
      LoopR pins dn s.mem A (rs.headD 0) fe' pend' ds →
      LoopR pins dn (s.setLocs [3] rs).mem A ((s.setLocs [3] rs).loc 3) fe' pend' ds := by
    intro s rs A fe' pend' h; simpa [St.setLocs, St.setLoc] using h
  have hmemL : ∀ (s : St) (rs : List Word), (s.setLocs [4] rs).mem = s.mem := by
    intro s rs; simp [St.setLocs, St.setLoc]
  have hmem3 : ∀ (s : St) (rs : List Word), (s.setLocs [3] rs).mem = s.mem := by
    intro s rs; simp [St.setLocs, St.setLoc]
  have hret : ∀ (s : St) (rs : List Word),
      (Sig.ret [(s.setLocs [4] rs).loc 4]).retVal.headD 0 = rs.headD 0 := by
    intro s rs; simp [St.setLocs, St.setLoc, Sig.retVal, Sig.retOr]
  have inner : ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "install_fold_next" [i, cnt, vis]
      ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ ∧ AM.res (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀ = .ok (i.toNat + 1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1, (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2) ∧
        FoldPost mode pins dn ds s'.mem (AM.st (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀) (r.headD 0) (i + 1).toNat
          (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1 (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2; ⊤⦄ := by
    rw [invoke_eq _ hpx]
    simp only [callFn, installFoldNextL]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, Locals.init,
        (installDeclStep_refines mode pins dn ds p hm hb hdc hpp hpn hps hpi hpd n hn' · a₀ · · fe pend ·),
        (ih · (AM.st (installDeclStep mode pins (i.toNat, fe, pend) (dsAt ds i)) a₀) · · · (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).1 (AM.res (installStep mode pins i.toNat fe pend (dsAt ds i)) (AM.st (andPinOk (dsAt ds i)) a₀)).2)] <;>
      finish
  exact triple_post inner fun r s' ⟨h0, h1, h2, h3⟩ => ⟨h0, hcons _ _ (i + 1) rfl h1 h2 h3⟩

/-- **`install_fold_go` refines `installFold`** from record `i` on (and `install_fold_next`
for one step and the rest). -/
@[refines ConRon.Arena.installFold]
theorem installFoldGo_refines (n : Nat) (hn : n ≤ 2 ^ 62) :
    FoldGoSpec mode pins dn ds p n ∧ FoldNextSpec mode pins dn ds p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ a₀ i cnt vis fe pend _ _ _ _ _ _; rw [invoke_eq _ hpg]; simp only [callFn]
      vcgen [exec] <;> grind
    · intro s₀ a₀ i cnt vis fe pend _ _ _ _ _ _; rw [invoke_eq _ hpx]; simp only [callFn]
      vcgen [exec] <;> grind
  | succ n ih =>
    have ih := ih (by omega)
    exact ⟨foldGo_step mode pins dn ds p hpp hpn hps hpi hpd hpg hpx hsz hb hdc hm n ih.2,
      foldNext_step mode pins dn ds p hpp hpn hps hpi hpd hpg hpx hsz hb hdc hm n hn ih.1⟩

end fold


/-- **`install_then_check` refines `installThenCheck`**: a returning run is the twin's accepting
fold, its environment related at the returned view. Phase A under `StageT` (from the loop's start
facts: `TwinFold`, `LoopMem`, `CoreMemos`), phase B from the stub specs (`Checker.lean`). -/
theorem installThenCheck_refines (hm : mode = .verified) (hb : BracketProg p) (hdc : LoopCallees dn p)
    (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hpi : p.lookup "install_step" = some installStepL)
    (hpd : p.lookup "install_decl_step" = some installDeclStepL)
    (hpg : p.lookup "install_fold_go" = some installFoldGoL)
    (hpx : p.lookup "install_fold_next" = some installFoldNextL)
    (hpc : p.lookup "check_pending" = some checkPendingL)
    (hpcg : p.lookup "check_pending_go" = some checkPendingGoL)
    (hpcx : p.lookup "check_pending_next" = some checkPendingNextL)
    (hp : p.lookup "install_then_check" = some installThenCheckL) (n : Nat) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState)
    (hT : TwinFold pins ds (mkIFEnv IEnv.empty) #[] a₀)
    (hR : LoopR pins dn s₀.mem a₀ 0 (mkIFEnv IEnv.empty) #[] ds)
    (hM : LoopMem dn s₀.mem a₀) (hc : CoreMemos s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_then_check" []
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installThenCheck mode pins ds) a₀ ∧ AM.res (installThenCheck mode pins ds) a₀ = .ok (foldFe (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) ∧
      LoopR pins dn s'.mem (AM.st (installThenCheck mode pins ds) a₀) (r.headD 0) (foldFe (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) (foldPend (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) ds; ⊤⦄ := by
  have hsz : ds.size < 2 ^ 63 := by have := hR.decls.dsize; have := hR.decls.room; omega
  have hcnt : ∀ (h : 0 < (s₀.mem.arr64 DECL).size), ((s₀.mem.arr64 DECL)[0]).toNat = ds.size := by
    intro h; have := hR.decls.count; simpa [h] using this
  have hc : ∀ (m : Mem) (a : AState) (v : Word) (fe : IFEnv) (pend : Array PendingCheck),
      LoopR pins dn m a v fe pend ds → ∀ (h : 130 < (m.arr64 CTL).size),
      ((m.arr64 CTL)[130]).toNat = pend.size := by
    intro m a v fe pend h h1
    have := h.pend.count; simp only [pendCount] at this; rwa [rdW_eq _ _ 130 rfl h1] at this
  have hcB : ∀ (m : Mem) (a : AState) (v : Word), FoldOut pins dn m a v ds (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) →
      ∀ (h : 130 < (m.arr64 CTL).size), ((m.arr64 CTL)[130]).toNat = (foldPend (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)).size :=
    fun m a v h h1 => hc m a v _ _ (FoldOut.eq h).2 h1
  have hLB : ∀ (m : Mem) (a : AState) (v : Word), FoldOut pins dn m a v ds (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) →
      (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) = .ok (ds.size, foldFe (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀), foldPend (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) ∧ LoopR pins dn m a v (foldFe (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) (foldPend (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) ds :=
    fun m a v h => FoldOut.eq h
  have hFP : ∀ (m : Mem) (v : Word), FoldPost mode pins dn ds m a₀ v (UInt64.toNat 0)
      (mkIFEnv IEnv.empty) #[] → AM.ok (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀ ∧ FoldOut pins dn m (AM.st (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) v ds (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) := by
    intro m v h; simpa [FoldPost] using h
  have inner : ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_then_check" []
      ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀ ∧ (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) = .ok (ds.size, foldFe (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀), foldPend (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) ∧
        PendPost mode pins dn ds (foldFe (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) (foldPend (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) s'.mem (AM.st (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) (r.headD 0) 0; ⊤⦄ := by
    rw [invoke_eq _ hp]
    simp only [callFn, installThenCheckL]
    cases n with
    | zero => vcgen [exec] <;> grind
    | succ n =>
      sym only [lang_grind, arena_grind] =>
        vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
          ((installFoldGo_refines mode pins dn ds p hpp hpn hps hpi hpd hpg hpx hsz hb hdc hm n (by omega)).1 · a₀ · · ·
            (mkIFEnv IEnv.empty) #[]),
          ((checkPendingGo_refines mode pins dn ds p (foldFe (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) (foldPend (AM.res (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀)) hpc hpcg hpcx hb hm hdc.cvg n).1 ·
            (AM.st (installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList) a₀) · · ·)] <;>
        finish
  exact triple_post inner fun r s' ⟨h0, h1, h2, h3⟩ => by
    obtain ⟨o, st, rs⟩ := installThenCheck_ok mode pins ds a₀ _ _ _ h1 h2 h3.1 h3.2.1
    exact ⟨h0, o, rs, by rw [st]; exact h3.2.2⟩


end skel

end L.Arena
