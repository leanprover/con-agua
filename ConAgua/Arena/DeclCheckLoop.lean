import ConAgua.Arena.DeclArmAxiom
import ConAgua.Arena.DeclArmDefn
import ConAgua.Arena.DeclNatGateSpec
import ConAgua.Arena.DeclDivMod10
import ConAgua.Arena.DeclNatSubAll

/-!
# `check_decl`'s arms at the loop's relation (lane `decls3`)

`check_decl(i, vis)` reads the record's kind word and calls one arm (`DeclStep.lean`). This file
has the program bundle `CheckDeclProg` the arms' proofs take and `substC0_of`. The arms' specs at
the loop's relation are the `StageT` ones in `CheckerT.lean` (`checkDecl_loopT`, lanes `loopt2`,
`loopt3`); their `StageR` versions (`ArmSpec`, with the quotient readers' preconditions open) are
gone with the interim contract.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt CVAt dw)

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
