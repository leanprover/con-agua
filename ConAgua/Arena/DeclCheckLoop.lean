import ConAgua.Arena.DeclArmAxiom
import ConAgua.Arena.DeclArmDefn
import ConAgua.Arena.DeclNatGateSpec
import ConAgua.Arena.DeclDivMod10
import ConAgua.Arena.DeclNatSubAll

/-!
# `check_decl`'s arms at the loop's relation (lane `decls3`)

`check_decl(i, vis)` reads the record's kind word and calls one arm (`DeclStep.lean`). Under the
front's records (`DeclsR`: every record is an axiom, definition, theorem, opaque or quotient,
`DeclAt`) the kind is `1`‥`5`, so the inductive branch (kind `6`, lane `induct`'s
`check_ind_decl`) is never taken here; it becomes reachable with the front's inductive records
(lane `indproofs2`).

Each arm's spec at the loop's relation is a theorem, all five proved: the theorem arm
(`DeclArmLoop.lean`), the opaque arm (`DeclArmOpaque.lean`), the quotient and axiom arms (the
canonical comparisons, which need the twin state well formed: `StateOK`, a hypothesis of
`ArmSpec`, from the fold's `TwinFold`, lane `decls4`), and the definition arm through the gates'
specs (`DefnProg`: `NatGateSpec`, `DivGateSpec`). The callees' own stub specs (the ROM readers,
`lvl_eq_c`) are `sorry`. The dispatcher's refinement is `CheckerT.lean`'s `checkDecl_loopT` (under
`StageT`, lane `loopt2`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsR DeclAt CVAt dw)

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups `check_decl`'s proof takes. -/
structure CheckDeclProg (p : Prog) : Prop where
  cd : p.lookup "check_decl" = some checkDeclL
  ax : p.lookup "check_decl_axiom" = some checkDeclAxiom
  df : p.lookup "check_decl_defn" = some checkDeclDefn
  th : p.lookup "check_decl_thm" = some checkDeclThm
  op : p.lookup "check_decl_opaque" = some checkDeclOpaque
  qu : p.lookup "check_decl_quot" = some checkDeclQuot
  arm : ArmProg p
  val : ValProg p
  crp : CrpProg p
  quot : QuotProg p
  axp : AxProg p
  /-- The definition arm's structural-`Nat` gate: its program (`DeclNatGateSpec.lean`'s
  `natGateSpec` proves `NatGateSpec` from these). -/
  natSub : NatSubProg' p
  natGate : p.lookup "defn_nat_gate" = some defnNatGate
  natCert : p.lookup "defn_nat_cert" = some defnNatCert
  natText : StepIn p natGateFns
  /-- The definition arm's `Nat.div`-family pin gate (helper `decls3-divmod`'s `divGateSpecD`
  proves `DivGateSpec` from these, with the walks' refinements `substC0_of`, `substCAll_of`): its
  program and its text's write set. -/
  dm : DmProg10 p
  dgClosed : StepIn p dgFns

/-- `subst_const0` at the walk fuel: helper `decls3-nat`'s `sc0_ref`. -/
theorem substC0_of {p : Prog} (hN : NatSubProg p) :
    ∀ dn vis fe, SubstC0 p dn vis fe :=
  fun _ _ _ nm r h hn hr hh k m a res m' hS hc =>
    sc0_ref hN nm r coreWalkFuel 4000000000 rfl h k m a res m' hS hn hr hh hc

/-! ## The arms not proved yet -/

section pending
variable {p : Prog} (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration)

/-- The shape of an arm's spec at the loop's relation, for the record `d` at `i`. -/
def ArmSpec (p : Prog) (f : FnName) (d : IDeclaration) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
    (i : Word), i.toNat < ds.size → ds[i.toNat]? = some d → ConRon.Bridge.StateOK a₀ →
    LoopR pins dn s₀.mem a₀ vis fe pend ds →
  ⦃fun s => s = s₀⦄ invoke p (exec p n) f [i, vis]
  ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkDecl V pins fe d) a₀ ∧
    LoopR pins dn s'.mem (AM.st (checkDecl V pins fe d) a₀) (r.headD 0)
      (AM.res (checkDecl V pins fe d) a₀) pend ds; ⊤⦄

/-- `check_decl_axiom` (`DeclArmAxiom.lean`). Open: `dn` reading `Quot`'s `u` back from the twin's
store (`NamesDn dn a₀ quotNames`, for the quotient block's reader; lane `loopt2`'s `TwinOK`). -/
theorem checkDeclAxiom_loop (hP : CheckDeclProg p) (hdn : DnInj dn) (cv : IConstantVal) :
    ArmSpec pins dn ds p "check_decl_axiom" (.axiomDecl cv) :=
  fun n s₀ a₀ vis fe pend i hi hd hok hR =>
    checkDeclAxiom_loop' hP.arm hP.axp pins dn hdn ds n s₀ a₀ vis fe pend i cv hi hd hok sorry hR

/-- `check_decl_defn` (`DeclArmDefn.lean`; through the gates' specs, `DefnProg`, a field of
`CheckDeclProg`). -/
theorem checkDeclDefn_loop (hP : CheckDeclProg p) (hdn : DnInj dn) (cv : IConstantVal) (v : EIdx)
    (h : ConLeche.ReducibilityHint) :
    ArmSpec pins dn ds p "check_decl_defn" (.defnDecl cv v h) :=
  fun n s₀ a₀ vis fe pend i hi hd _ hR =>
    checkDeclDefn_loop' hP.arm hP.val pins
      ⟨hP.df, natGateSpec hP.natSub hP.natGate hP.natCert hP.natText pins,
        divGateSpecD hP.dm pins (substC0_of hP.natSub.toNatSubProg) (substCAll_of ⟨hP.natSub.toNatSubProg, hP.dm.lSubstConstAll⟩) hP.dgClosed⟩
      dn hdn ds n s₀ a₀ vis fe pend i cv v h hi hd hR

/-- `check_decl_opaque` (`DeclArmOpaque.lean`). -/
theorem checkDeclOpaque_loop (hP : CheckDeclProg p) (hdn : DnInj dn) (cv : IConstantVal)
    (v : EIdx) : ArmSpec pins dn ds p "check_decl_opaque" (.opaqueDecl cv v) :=
  fun n s₀ a₀ vis fe pend i hi hd _ hR =>
    checkDeclOpaque_loop' hP.arm hP.val hP.crp hP.op pins dn hdn ds n s₀ a₀ vis fe pend i cv v hi hd hR

/-- `check_decl_quot` (`DeclArmQuot.lean`). Open: `NamesDn dn a₀ quotNames` (as
`checkDeclAxiom_loop`) and the declaration's constant value denoting in the twin's store. -/
theorem checkDeclQuot_loop (hP : CheckDeclProg p) (hdn : DnInj dn) (k : ConLeche.QuotKind)
    (cv : IConstantVal) : ArmSpec pins dn ds p "check_decl_quot" (.quotDecl k cv) :=
  fun n s₀ a₀ vis fe pend i hi hd hok hR =>
    checkDeclQuot_loop' hP.arm hP.val.rcp hP.quot pins dn hdn ds n s₀ a₀ vis fe pend i k cv hi hd hok sorry sorry hR

end pending

/-! ## The dispatcher -/

section model
variable (p : Prog)

/-- After an arm: its view word. -/
def cdRet : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

/-- The inductive branch (kind `6`). -/
def cdInd (n : Nat) (i vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    cdRet (callW p n "check_ind_decl"
      [vis, r1.headD 0, r1.tail.headD 0, rdW (m1.arr64 DECL) (5 + 8 * i)] m1)

/-- The dispatch on the kind word `k`. -/
def cdSel (n : Nat) (m : Mem) (i vis k : Word) : Option (List Word × Mem) :=
  if k = 6 then cdInd p n i vis (callW p n "ind_block_to_erec" [i] m)
  else if k = 1 then cdRet (callW p n "check_decl_axiom" [i, vis] m)
  else if k = 2 then cdRet (callW p n "check_decl_defn" [i, vis] m)
  else if k = 3 then cdRet (callW p n "check_decl_thm" [i, vis] m)
  else if k = 4 then cdRet (callW p n "check_decl_opaque" [i, vis] m)
  else if k = 5 then cdRet (callW p n "check_decl_quot" [i, vis] m)
  else none

/-- **The model of `check_decl(i, vis)`.** -/
def cdW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, i, vis => cdSel p n m i vis (rdW (m.arr64 DECL) (1 + 8 * i))

section arms
variable (n : Nat) (m m1 : Mem) (i vis k : Word) (r r1 : List Word)
theorem cdW_step : cdW p (n + 1) m i vis = cdSel p n m i vis (rdW (m.arr64 DECL) (1 + 8 * i)) := rfl
theorem cdRet_some : cdRet (some (r, m)) = some ([r.headD 0], m) := rfl
theorem cdInd_some : cdInd p n i vis (some (r1, m1)) =
    cdRet (callW p n "check_ind_decl"
      [vis, r1.headD 0, r1.tail.headD 0, rdW (m1.arr64 DECL) (5 + 8 * i)] m1) := rfl
end arms

grind_pattern [ind_grind] cdW_step => cdW p (n + 1) m i vis
grind_pattern [ind_grind] cdRet_some => cdRet (some (r, m))
grind_pattern [ind_grind] cdInd_some => cdInd p n i vis (some (r1, m1))

theorem cd_specW (hp : p.lookup "check_decl" = some checkDeclL) (n : Nat) (s₀ : St) (i vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_decl" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ cdW p n s₀.mem i vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkDeclL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "ind_block_to_erec", callW_spec p n "check_ind_decl",
        callW_spec p n "check_decl_axiom", callW_spec p n "check_decl_defn",
        callW_spec p n "check_decl_thm", callW_spec p n "check_decl_opaque",
        callW_spec p n "check_decl_quot"] <;>
      finish (gen := 20) [cdSel, rdW_eq]

end model

end L.Arena
