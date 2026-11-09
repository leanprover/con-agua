module

import ConAgua.Arena.DeclArmT
import ConAgua.Arena.DeclCanonInfo
public import ConAgua.Arena.DeclArmAxiom
public import ConAgua.Arena.QuotAtT
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.DeclTwin
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.RefWalk
import ConAgua.Arena.StageC
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Checker.Arms
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Basis
public import ConAgua.Arena.LeafFns
public import ConAgua.Verdict.DeclValsE
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# The axiom arm, both outcomes, under `StageT` (lane `loopt3`, helper `loopt3-axq`)

`check_decl_axiom`'s unified model and refinement `cda_ref`, from `StageT` back to the stage
relation and the core's memos (option (a), replacing the interim contract
`stubArm_keepsCoreMemos`; the quotient arm `check_decl_quot` is `cdq_ref`, `DeclArmQuot.lean`,
and keeps the memos as a leaf).

Every call of the two arms but `check_constant_val` is a leaf of the declaration loop (`leafFns`:
`erec_ci`, the ROM block reader, `quot_pin_hit`, `check_basis_decl`, `ci_canon_eq`,
`std_axiom_ok`, `trust_compiler_ok`, `of_reduce_ax_ok`, `env_push`; `pin_at` is pure). So no
`TwinOK` or con-ron `CheckOK` has to be carried past a core call: the core's memos are kept by the
leaves' frame (`LeafClosed`) and by `erec_ci`'s (`erecCiW_frame`), and given by the one core call,
the constant check, under `StageT` (`ccv_ref`: `TwinOK` at its entry from the arm's `StageT`
across `erec_ci`'s frame). The twin's `StateOK` is needed only at the arm's entry (the ROM
reader, the canonical comparisons), where the loop has it.

The quotient readers' precondition `NamesDn dn a quotNames` (journal `loopt2`, landing 5) comes
from the loop-start fact `QuotDn dn` (`Quot`'s `sortZ` name `u` has a handle under the record
pool's name decoder) and `TwinOK`'s `den.dnN` (that handle reads back to `u` in the twin's name
store); the quotient record's `denoteCV` from the record's denotation (`TwinFold.den`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)

local notation "V" => ConLeche.CheckMode.verified

/-- `erec_ci` keeps the core's memos. -/
theorem erecCiW_memos {n : Nat} {m m' : Mem} {i ck : Word} {r : List Word}
    (h : erecCiW n m i ck = some (r, m')) (hM : CoreMemos m) : CoreMemos m' :=
  hM.frame (erecCiW_frame h) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩

/-- A leaf call keeps the core's memos. -/
theorem leaf_memos {p : Prog} (hcl : LeafClosed p) {f : FnName} (hf : f ∈ leafFns) {k : Nat}
    {args : List Word} {x y : Mem} {rx : List Word} (hc : callW p k f args x = some (rx, y))
    (hM : CoreMemos x) : CoreMemos y :=
  hM.frame (callW_leafFrame hcl hf hc) leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp

/-- **The model of `check_decl_quot(i, vis)`, both outcomes**: `erec_ci` through its run,
`check_quot_record` by its unified model. -/
l_model checkDeclQuot_specE (p : Prog) (hp : p.lookup "check_decl_quot" = some checkDeclQuot)
  (hRp : RecProg p) (hc : p.lookup "check_quot_record" = some checkQuotRecordL) (hB : BasisProg p)
  fns [hp ↦ checkDeclQuotE]
  specs [erecCi_specW p hRp n, checkQuotRecord_specE p hc hB n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `StageT` across `erec_ci(i, 0)` on an axiom or a quotient record (`erecCiW_okA` with the
twin's invariants by `erec_ci`'s frame). -/
theorem erecCiW_okAT {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {i : Word} {r : List Word} {ds : Array IDeclaration}
    {cv : IConstantVal}
    (h : erecCiW n m i 0 = some (r, m')) (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hcv : L.Front.CVAt (m.arr64 DECL) (m.arr64 DLP) i.toNat cv) :
    StageT dn vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') (r.headD 0).toNat = some (.axiomInfo cv) ∧
      decCV (erecP m') ((r.headD 0).toNat + 1) = some cv := by
  obtain ⟨hS', hg, h1, h2, -⟩ := erecCiW_okA h hS.stage hD hi hcv
  have hf := erecCiW_frame h
  exact ⟨⟨hS', hS.twin.frame hf ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩,
    by simp only [pinW, hf.arr PINS (by decide) (by decide)]; exact hS.flag⟩, hg, h1, h2⟩

/-- The lookups of the quotient arm. -/
structure QuotArmProg (p : Prog) : Prop where
  cdq : p.lookup "check_decl_quot" = some checkDeclQuot
  rcp : RecProg p
  cqr : QuotRecProg p
  leaf : LeafClosed p

/-- **`check_decl_quot(i, vis)` refines the quotient arm of `checkDecl`, both outcomes**, under
`StageT`: the record's constant into `EREC` (`erec_ci(i, 0)`), then `check_quot_record` at the
record's slot (`cqr_ref`). -/
theorem cdq_ref {p : Prog} (hQ : QuotArmProg p) {dn : NIdx → Option ConLeche.Name}
    (hQs : QuotSims p dn) {vis : Word} {fe : IFEnv} {a : AState} (n : Nat) {m : Mem} {i : Word}
    {ds : Array IDeclaration} {pins : List INatOpPinSet} {k : ConLeche.QuotKind}
    {cv : IConstantVal} (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .quotDecl k cv) (hok : ConRon.Bridge.StateOK a)
    (hr : ConRon.Bridge.ReadOK a) {c : ConLeche.ConstantVal}
    (hden : Frontend.denoteCV a.store cv = some c) :
    RefE True (checkDeclQuotE p n m i vis) (checkDecl V pins fe (.quotDecl k cv)) a
      (fun v fe' a' => CqrPost m v.1 v.2 fe' a') := by
  have hdecl := hD.recs i.toNat hi
  rw [hd] at hdecl
  obtain ⟨-, hcvAt, hk⟩ := hdecl
  have h1r := hD.room
  have h2r := hD.dsize
  have hkw : rdW (m.arr64 DECL) (7 + 8 * i) = L.Front.dw (m.arr64 DECL) i.toNat 6 :=
    rdW_dw _ (by omega) (by decide) (by decide)
  cases n with
  | zero => rw [checkDeclQuotE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [checkDeclQuotE.eq_2, hkw]
  have hsel : ∀ (kw : Word) (J : Word → Except Err (Word × Mem)),
      (if kw = 1 then J 0 else if kw = 2 then J 1 else if kw = 3 then J 2 else J 3) =
        J (slotOfW kw) := by
    intro kw J; unfold slotOfW
    by_cases h1 : kw = 1 <;> by_cases h2 : kw = 2 <;> by_cases h3 : kw = 3 <;> simp [h1, h2, h3]
  rw [hsel (L.Front.dw (m.arr64 DECL) i.toNat 6) (fun ks => checkDeclQuotE.j1 p n i vis ks m),
    slotOfW_eq, hk, checkDeclQuotE.j1.arm1]
  refine RefE.onlySim (fun _ => checkDeclQuotE.k_erec_ci.none ..) (fun _ _ h => h) fun r1 m1 h1 => ?_
  rw [checkDeclQuotE.k_erec_ci.arm1]
  obtain ⟨hS1, hg1, -, hcv1⟩ := erecCiW_okAT h1 hS hD hi hcvAt
  have hq1 : (r1.headD 0 + 1).toNat = (r1.headD 0).toNat + 1 := by
    obtain ⟨w, hw, -⟩ := decCV_name hcv1
    exact toNat_add_small _ 1 (L.Arena.erecP_lt64 hw)
  exact RefE.weakenP (cqr_ref hQ.cqr hQ.leaf hQs n k hS1 hok hr (by rw [hq1]; exact hcv1) hden)
    fun v fe' a' h => ⟨h.stage, hg1.trans h.grow, h.memos⟩

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The model of `check_decl_axiom(i, vis)`, both outcomes**: the leaves and pin reads
(outside the verdict closure) lifted, `check_constant_val` by its unified model. -/
l_model checkDeclAxiom_specE (p : Prog) (hX : AxProg p)
  fns [hX.cda ↦ checkDeclAxiomE]
  specs [erecCi_specW p hX.val.rcp n, pinAt_specW p hX.quot.pa n, callW_spec p n "rom_basis_decls",
    callW_spec p n "ci_canon_eq", checkConstantVal_specE p hX.val n, callW_spec p n "std_axiom_ok",
    callW_spec p n "env_push", callW_spec p n "trust_compiler_ok",
    callW_spec p n "of_reduce_ax_ok"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]
-/

/-- What the axiom arm gives besides the twin's environment `fe'` (from `m`): the stage relation
over the result word, the core's memos, the growth. -/
structure CdaPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (r : Word) (m' : Mem) (fe' : IFEnv)
    (a' : AState) : Prop where
  stage : StageR r fe' m' a'
  memos : CoreMemos m'
  grow : IWGrow m m'

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The axiom arm refines `checkDecl`'s `.axiomDecl` arm, both outcomes** (con-ron's
`checkDecl_bridge_axiom`'s decomposition), under `StageT`: `Quot.sound` against the pinned block
(installing nothing), else the constant check (`ccv_ref`) and the five recognised axioms;
`propext`/`choice` of another shape and every other axiom decline (the latter after the name's
readback, from the fold invariant), `sorryAx` is skipped. Every other call is a leaf (the core's
memos by its frame). -/
theorem cda_ref {p : Prog} (hX : AxProg p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hap : ApdF p) (hkp : CrKeep p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    (hQd : QuotDn dn) {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem}
    {i : Word} {ds : Array IDeclaration} {pins : List INatOpPinSet} {cv : IConstantVal}
    (hS : StageT dn vis fe m a) (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds)
    (hi : i.toNat < ds.size) (hd : ds[i.toNat] = .axiomDecl cv) (hok : ConRon.Bridge.StateOK a)
    {c : ConLeche.ConstantVal} (hcvd : Frontend.denoteCV a.store cv = some c)
    (hF : ∃ env, ConRon.Bridge.FoldOK V env fe a) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkDeclAxiomE p n m i vis) (checkDecl V pins fe (.axiomDecl cv)) a
      (fun v fe' a' => CdaPost dn m v.1 v.2 fe' a') := by
  sorry

-/

end L.Arena
