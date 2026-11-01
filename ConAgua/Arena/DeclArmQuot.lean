module

import ConAgua.Arena.DeclTwin
public import ConAgua.Arena.DeclBasisSpec2
import ConAgua.Arena.DeclCanonConst
import ConAgua.Arena.DeclCanonSpec2
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclValRef
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.DeclCanonView2
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# The quotient pin: `quot_pin_hit(k, q)` (lane `decls3`)

`quotPinHit k cv`: the record is the pinned quotient block's constant at its own slot, compared at
`toConstantVal` up to the canonical form (`cv_canon_eq`, helper `decls3-canon`'s
`cvCanonEq_refines`, which compares literals by handle: `LitInj`, from the twin state's
well-formedness `StateOK`, lane `decls4`). Through the ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

section model
variable (p : Prog)

/-- After the comparison. -/
def qphK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([r3.headD 0], m3)

/-- After `ci_to_cv`. -/
def qphK2 (n : Nat) (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => qphK3 (callW p n "cv_canon_eq" [q, r2.headD 0] m2)

/-- After the block's read. -/
def qphK1 (n : Nat) (k q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.tail.headD 0 ≤ k then some ([0], m1)
    else qphK2 p n q (callW p n "ci_to_cv" [rdW (m1.arr64 IW) (r1.headD 0 + k)] m1)

/-- **The model of `quot_pin_hit(k, q)`.** -/
def qphW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, k, q => qphK1 p n k q (callW p n "rom_basis_decls" [4] m)

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (k q : Word) (r1 r2 r3 : List Word)
theorem qphW_step : qphW p (n + 1) m k q = qphK1 p n k q (callW p n "rom_basis_decls" [4] m) := rfl
theorem qphK1_some : qphK1 p n k q (some (r1, m1)) =
    if r1.tail.headD 0 ≤ k then some ([0], m1)
    else qphK2 p n q (callW p n "ci_to_cv" [rdW (m1.arr64 IW) (r1.headD 0 + k)] m1) := rfl
theorem qphK2_some : qphK2 p n q (some (r2, m2)) =
    qphK3 (callW p n "cv_canon_eq" [q, r2.headD 0] m2) := rfl
theorem qphK3_some : qphK3 (some (r3, m3)) = some ([r3.headD 0], m3) := rfl
end arms

grind_pattern [ind_grind] qphW_step => qphW p (n + 1) m k q
grind_pattern [ind_grind] qphK1_some => qphK1 p n k q (some (r1, m1))
grind_pattern [ind_grind] qphK2_some => qphK2 p n q (some (r2, m2))
grind_pattern [ind_grind] qphK3_some => qphK3 (some (r3, m3))

theorem qph_specW (hp : p.lookup "quot_pin_hit" = some quotPinHitL) (n : Nat) (s₀ : St)
    (k q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "quot_pin_hit" [k, q]
    ⦃fun r s' => LocEq s' s₀ ∧ qphW p n s₀.mem k q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, quotPinHitL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "rom_basis_decls", callW_spec p n "ci_to_cv",
        callW_spec p n "cv_canon_eq"] <;>
      finish (gen := 20) [rdW_eq]

end model

/-- The pool's size bound canon's comparisons take (`LitR`'s `PoolOK`). -/
theorem poolSmall_of_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {m : Mem} {a : AState} (h : StageR dn vis fe m a) : PoolSmall m := by
  have := h.check.arena.base.lit.1.cap
  unfold PoolSmall; omega

theorem slot_lt (k : ConLeche.QuotKind) : k.slot < 5 := by cases k <;> decide

/-- **`quot_pin_hit(k, q)` refines `quotPinHit`** at the model level. -/
theorem qphW_ok {p : Prog} (hC : CanonProg p) (hR : L.Rom.RomRefs p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal} {k : ConLeche.QuotKind}
    (hW : qphW p n m (UInt64.ofNat k.slot) q = some (r, m')) (hS : StageR dn vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) (hok : ConRon.Bridge.StateOK a)
    (hN : L.Rom.NamesDn dn a L.Rom.quotNames) :
    ∃ b a', (quotPinHit k cv).run a = .ok (b, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      decW0B m' r b := by
  have hks : (UInt64.ofNat k.slot).toNat = k.slot :=
    UInt64.toNat_ofNat_of_lt' (by have := slot_lt k; rw [UInt64_size_eq]; omega)
  cases n with
  | zero => simp [qphW] at hW
  | succ n =>
  rw [qphW_step] at hW
  cases h1 : callW p n "rom_basis_decls" [4] m with
  | none => rw [h1] at hW; cases hW
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, qphK1_some] at hW
  obtain ⟨blk, a1, hrun1, hS1, hg1, hD1, hr1⟩ := hR.quot dn vis fe n m a r1 m1 ⟨hS, hok, hN⟩ h1
  have hrun1' : (BasisKind.decls .quotK).run a = .ok (blk, a1) := hrun1
  have hok1 := (ConRon.Bridge.BasisKind.decls_run hok hrun1').1
  have hlen : blk.length = (r1.tail.headD 0).toNat := decPL_length (truncM m1) hD1
  generalize r1.headD 0 = o at hW hD1 hlen
  generalize r1.tail.headD 0 = l at hW hD1 hlen
  by_cases hl : l ≤ UInt64.ofNat k.slot
  · rw [ite_eq_left hl] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hn : blk[k.slot]? = none := by
      apply List.getElem?_eq_none; rw [hlen]
      have := UInt64.le_iff_toNat_le.mp hl; omega
    refine ⟨false, a1, ?_, hS1, hg1, by simp [decW0B]⟩
    simp only [quotPinHit, StateT.run_bind, hrun1', exc_ok_bind', hn]
    rfl
  rw [ite_eq_right hl] at hW
  have hlt : k.slot < (l).toNat := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hl); omega
  obtain ⟨v, ci, hv, hci, hget⟩ := decPL_get _ _ _ hD1 k.slot hlt
  -- the pointer word
  have hvm : iwN m1 (o.toNat + k.slot) = some v :=
    (IWGrow.refl m1).truncExt.1.nat? hv
  obtain ⟨w, hw, rfl⟩ : ∃ w, (iwA m1)[o.toNat + k.slot]? = some w ∧ w.toNat = v := by
    simp only [iwN, nat?, Option.map_eq_some_iff] at hvm; exact hvm
  have hob : o.toNat + k.slot < 2 ^ 64 := by
    have := (Array.getElem?_eq_some_iff.mp hw).1; have := hS1.iw.iwSize; simp only [iwA] at *; omega
  have hidx : (o + UInt64.ofNat k.slot).toNat = o.toNat + k.slot := by
    rw [UInt64.toNat_add, hks]; simp; omega
  have ew : rdW (m1.arr64 IW) (o + UInt64.ofNat k.slot) = w := by
    simp only [rdW, hidx]; simp only [iwA] at hw; simp [hw]
  rw [ew] at hW
  have hciP : decCI (erecP m1) dn w.toNat = some ci := ArrExt.decCI (truncM_erecP m1) hci
  -- `ci_to_cv`
  cases h2 : callW p n "ci_to_cv" [w] m1 with
  | none => rw [h2] at hW; cases hW
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, qphK2_some] at hW
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, hcv2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (ciToCv_refines p hC dn vis fe w ci n ⟨m1, Locals.init []⟩ a1 ⟨hS1, hciP⟩) h2
  subst hs2
  simp only [AM.res_pure, AM.st_pure] at hS2 hcv2
  -- `cv_canon_eq`
  cases h3 : callW p n "cv_canon_eq" [q, r2.headD 0] s2.mem with
  | none => rw [h3] at hW; cases hW
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, qphK3_some] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl⟩ := hW
  have hg12 := hg1.trans hg2
  obtain ⟨s3, hs3, -, hok3, ⟨⟨hS3, hg3, hd3⟩, -⟩, -⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (cvCanonEq_refines p hC dn vis fe q (r2.headD 0) cv ci.toConstantVal n ⟨s2.mem, Locals.init []⟩
      a1 ⟨hS2, ArrExt.decCV (IWGrow.erecPExt hg12) hq, hcv2, poolSmall_of_stage hS2,
        fun x y l hx hy => hok1.view_inj hx hy⟩) h3
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  refine ⟨_, _, ?_, hS3, hg12.trans hg3, hd3⟩
  simp only [quotPinHit, StateT.run_bind, hrun1', exc_ok_bind', hget]
  exact hrun3

/-! ## The quotient arm `check_decl_quot(i, vis)` -/

open L.Front (DECL DLP DeclsF DeclAt CVAt dw quotW)

/-- The slot word `check_decl_quot` computes from the record's kind word. -/
def slotOfW (kw : Word) : Word := if kw = 1 then 0 else if kw = 2 then 1 else if kw = 3 then 2 else 3

theorem slotOfW_eq (kw : Word) : slotOfW kw = UInt64.ofNat (quotW kw).slot := by
  unfold slotOfW quotW
  by_cases h1 : kw = 1 <;> by_cases h2 : kw = 2 <;> by_cases h3 : kw = 3 <;> simp_all <;> rfl

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups of the quotient arm. -/
structure QuotProg (p : Prog) : Prop where
  canon : CanonProg p
  rom : L.Rom.RomRefs p
  basis : BasisProg p
  qph : p.lookup "quot_pin_hit" = some quotPinHitL
  cbd : p.lookup "check_basis_decl" = some checkBasisDeclL
  pa : p.lookup "pin_at" = some pinAtL
  cdq : p.lookup "check_decl_quot" = some checkDeclQuot

/-- **The model of `check_decl_quot(i, vis)`, both outcomes**: `erec_ci` and `quot_pin_hit`
(outside the verdict closure) lifted, `check_basis_decl` by its unified model. -/
l_model checkDeclQuot_specE (p : Prog) (hQ : QuotProg p) (hRp : RecProg p)
  fns [hQ.cdq ↦ checkDeclQuotE]
  specs [erecCi_specW p hRp n, qph_specW p hQ.qph n, checkBasisDecl_specE p hQ.basis hQ.pa hQ.cbd n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem checkDecl_quot_shape (pins : List INatOpPinSet) (fe : IFEnv) (k : ConLeche.QuotKind)
    (cv : IConstantVal) :
    checkDecl V pins fe (.quotDecl k cv) =
      (quotPinHit k cv >>= fun b => if b = true then
        (match k with | .type => checkBasisDecl fe .quotK | _ => pure fe)
        else fail (.notImplemented (match k with
          | .sound => "quotient soundness axiom mismatch"
          | _ => "quotient declaration mismatch"))) := rfl

/-- **`check_decl_quot(i, vis)` refines the quotient arm of `checkDecl`, both outcomes**
(con-ron's `checkDecl_bridge_quot`): the record against the pinned block's constant at its slot
(`quot_pin_hit`), then for `Quot` itself the block's install (`cbd_ref`). -/
theorem cdq_ref {p : Prog} (hQ : QuotProg p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    {vis : Word} {fe : IFEnv} {a : AState} (n : Nat) {m : Mem} {i : Word}
    {ds : Array IDeclaration} {pins : List INatOpPinSet} {k : ConLeche.QuotKind}
    {cv : IConstantVal} (hS : StageR dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .quotDecl k cv) (hok : ConRon.Bridge.StateOK a)
    (hN : L.Rom.NamesDn dn a L.Rom.quotNames)
    (hcvD : ∃ c, ConRon.Arena.Frontend.denoteCV a.store cv = some c) :
    RefE True (checkDeclQuotE p n m i vis) (checkDecl V pins fe (.quotDecl k cv)) a
      (fun v fe' a' => IbdPost dn m v.1 v.2 fe' a') := by
  have hdecl := hD.recs i.toNat hi
  rw [hd] at hdecl
  obtain ⟨-, hcvAt, hk⟩ := hdecl
  have h1r := hD.room
  have h2r := hD.dsize
  have hkw : rdW (m.arr64 DECL) (7 + 8 * i) = dw (m.arr64 DECL) i.toNat 6 :=
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
  rw [hsel (dw (m.arr64 DECL) i.toNat 6) (fun ks => checkDeclQuotE.j1 p n i vis ks m),
    slotOfW_eq, hk, checkDeclQuotE.j1.arm1, checkDecl_quot_shape]
  refine RefE.onlySim (fun _ => checkDeclQuotE.k_erec_ci.none ..) (fun _ _ h => h) fun r1 m1 h1 => ?_
  rw [checkDeclQuotE.k_erec_ci.arm1]
  obtain ⟨hS1, hg1, -, hcv1, htop1⟩ := erecCiW_okA h1 hS hD hi hcvAt
  have hqb : (r1.headD 0).toNat + 8 < 2 ^ 64 := by
    have := hS1.iw.er; have := hS1.iw.erSize; omega
  have hq1 : (r1.headD 0 + 1).toNat = (r1.headD 0).toNat + 1 := toNat_add_small _ 1 (by omega)
  -- `quot_pin_hit`
  rcases h2 : qphW p n m1 (UInt64.ofNat k.slot) (r1.headD 0 + 1) with _ | ⟨r2, m2⟩
  · rw [liftE_none, checkDeclQuotE.k_quot_pin_hit.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨b, a2, hrun2, hS2, hg2, hd2⟩ :=
    qphW_ok hQ.canon hQ.rom h2 hS1 (by rw [hq1]; exact hcv1) hok hN
  obtain ⟨c, hc⟩ := hcvD
  have hrun2' : quotPinHit k cv a = .ok (b, a2) := hrun2
  obtain ⟨hok2, hx2, -⟩ := ConRon.Bridge.quotPinHit_run hok hc hrun2'
  refine RefE.bind_right hrun2 ?_
  by_cases z2 : r2.headD 0 = 0
  · rw [checkDeclQuotE.k_quot_pin_hit.abort1 p _ _ _ _ _ z2]
    have hb : b = false := by rw [← hd2.1]; simpa using z2
    rw [hb]
    exact RefE.ite_neg (by decide) fun _ => ErrClaim.fail _ _ rfl
  have hb : b = true := by rw [← hd2.1]; simpa using z2
  rw [hb]
  refine RefE.ite_pos rfl ?_
  by_cases ht : UInt64.ofNat k.slot = 0
  · rw [checkDeclQuotE.k_quot_pin_hit.arm1 p _ _ _ _ _ z2 ht]
    have hk0 : k = .type := by
      cases k <;> simp_all [ConLeche.QuotKind.slot] <;> exact absurd ht (by decide)
    subst hk0
    exact (cbd_ref (k := 4) hQ.basis hQ.canon hQ.rom hdn n (by decide) hS2
      (fun _ => ⟨hok2, L.Rom.NamesDn.ext hN hx2⟩)).mono
      fun _ _ _ hR => ⟨hR.stage, hg1.trans (hg2.trans hR.grow)⟩
  rw [checkDeclQuotE.k_quot_pin_hit.arm2 p _ _ _ _ _ z2 ht]
  refine RefE.ret (y := fe) (a' := a2) ?_ ⟨by simpa using hS2, hg1.trans hg2⟩
  cases k with
  | type => exact absurd rfl ht
  | ctor | lift | ind | sound => rfl

end L.Arena
