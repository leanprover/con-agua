module

public import ConAgua.Arena.LdRd
public import ConAgua.Rom.CIReadSpec
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import ConAgua.Arena.DeclNatBase
import all ConAgua.Rom.CIRead

@[expose] public section

/-!
# The ROM constant readers' word models (helper `decls4-rom`)

One model per function of `romCIProg` (`CIRead.lean`), each calling its callees through `callW`
(lane `whnf`'s "a call as a function of the memory"; `DeclNatBase.lean`'s `ntBW`), so no model is
recursive and every spec is one `vcgen`. `rom_u64` is read as its value `u64W rom i` (its range
check matters only in the decoder direction). The relational lemmas (`CIReadRef*.lean`) unfold
these models one call at a time, by induction on the L fuel.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-- **An `ntBW` step that returned**: its callee returned. -/
theorem ntBW_inv {β : Type} {mo : Option (List Word × Mem)} {k : List Word → Mem → Option β} {x : β}
    (h : ntBW mo k = some x) : ∃ r m, mo = some (r, m) ∧ k r m = some x := by
  match mo, h with
  | some (r, m), h => exact ⟨r, m, rfl, h⟩

section models
variable (p : Prog) (n : Nat)

/-- A `rom_u64` read through `callW`. -/
abbrev rdU (m : Mem) (i : Word) (k : Word → Mem → Option (List Word × Mem)) :
    Option (List Word × Mem) :=
  ntBW (callW p n "rom_u64_c" [i] m) fun r m' => k (r.headD 0) m'

/-- An `erec_put(a, v)` through `callW`. -/
abbrev putE (m : Mem) (a v : Word) (k : Mem → Option (List Word × Mem)) :
    Option (List Word × Mem) :=
  ntBW (callW p n "erec_put" [a, v] m) fun _ m' => k m'








/-- A rule's level slice (fires `1`, `2`): the position after. -/
def ruleLvlW (m : Mem) (q r : Word) : Option (List Word × Mem) :=
  rdU p n m q fun l1 m0 =>
  ntBW (callW p n "erec_alloc" [l1] m0) fun r1 m1 =>
  putE p n m1 (r + 4) (r1.headD 0) fun m1a =>
  putE p n m1a (r + 5) l1 fun m1b =>
  ntBW (callW p n "rci_lvls_to" [q + 8, r1.headD 0, l1] m1b) fun r2 m2 =>
  some ([r2.headD 0], m2)

/-- A nested rule's pin slice (fire `1`): the position after. -/
def rulePinW (m : Mem) (q r : Word) : Option (List Word × Mem) :=
  rdU p n m q fun l2 m0 =>
  ntBW (callW p n "erec_alloc" [l2] m0) fun r3 m3 =>
  putE p n m3 (r + 6) (r3.headD 0) fun m3a =>
  putE p n m3a (r + 7) l2 fun m3b =>
  ntBW (callW p n "rom_exprs_to_c" [q + 8, r3.headD 0, l2] m3b) fun r4 m4 =>
  some ([r4.headD 0], m4)

/-- `rci_rule(q, r)`. -/
def ruleW (m : Mem) (q r : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "rom_name_c" [q] m) fun r1 m1 =>
  putE p n m1 r (r1.headD 0) fun m1' =>
  rdU p n m1' (r1.tail.headD 0) fun x1 m2 => putE p n m2 (r + 1) x1 fun m2' =>
  rdU p n m2' (r1.tail.headD 0 + 8) fun f m3 => putE p n m3 (r + 3) f fun m3' =>
  putE p n m3' (r + 4) 0 fun m4 => putE p n m4 (r + 5) 0 fun m5 =>
  putE p n m5 (r + 6) 0 fun m6 => putE p n m6 (r + 7) 0 fun m7 =>
  ruleTailW p n m7 (r1.tail.headD 0 + 16) r f
where
  /-- The fire's slices, then the right-hand side. -/
  ruleTailW (p : Prog) (n : Nat) (m : Mem) (q r f : Word) : Option (List Word × Mem) :=
    ntBW (if f = 1 ∨ f = 2 then ruleLvlW p n m q r else some ([q], m)) fun r2 m2 =>
    ntBW (if f = 1 then rulePinW p n m2 (r2.headD 0) r else some ([r2.headD 0], m2)) fun r3 m3 =>
    ntBW (callW p n "rom_expr_c" [r3.headD 0] m3) fun r4 m4 =>
    putE p n m4 (r + 8) (r4.headD 0) fun m5 =>
    some ([r4.tail.headD 0], m5)


/-- A constant record's size by its kind word. -/
def ciSize (k : Word) : Option Word :=
  if k = 0 then some 5 else if k = 2 then some 5 else if k = 1 then some 8 else if k = 3 then some 20
  else if k = 4 then some 7 else if k = 5 then some 10 else none

/-- The definition's parts. -/
def ciDefnW (m : Mem) (pp q : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "rom_expr_c" [q] m) fun r1 m1 =>
  putE p n m1 (pp + 5) (r1.headD 0) fun m1' =>
  rdU p n m1' (r1.tail.headD 0) fun x1 m2 => putE p n m2 (pp + 6) x1 fun m2' =>
  rdU p n m2' (r1.tail.headD 0 + 8) fun x2 m3 => putE p n m3 (pp + 7) x2 fun m3' =>
  some ([r1.tail.headD 0 + 16], m3')

/-- The constructor's numbers. -/
def ciCtorW (m : Mem) (pp q : Word) : Option (List Word × Mem) :=
  rdU p n m q fun x1 m1 => putE p n m1 (pp + 5) x1 fun m1' =>
  rdU p n m1' (q + 8) fun x2 m2 => putE p n m2 (pp + 6) x2 fun m2' =>
  some ([q + 16], m2')

/-- The recursor's numbers and rules. -/
def ciRecW (m : Mem) (pp q : Word) : Option (List Word × Mem) :=
  rdU p n m q fun x1 m1 => putE p n m1 (pp + 5) x1 fun m1' =>
  rdU p n m1' (q + 8) fun x2 m2 => putE p n m2 (pp + 6) x2 fun m2' =>
  rdU p n m2' (q + 16) fun x3 m3 => putE p n m3 (pp + 9) x3 fun m3' =>
  rdU p n m3' (q + 24) fun l m4 =>
  ntBW (callW p n "erec_alloc" [11 * l] m4) fun r1 m5 =>
  putE p n m5 (pp + 7) (r1.headD 0) fun m5a =>
  putE p n m5a (pp + 8) l fun m5b =>
  callW p n "rci_rules_to" [q + 32, r1.headD 0, l] m5b

/-- The kind's parts after the constant value (at `q`, record `pp`). -/
def ciTailW (m : Mem) (k pp q : Word) : Option (List Word × Mem) :=
  if k = 1 then ciDefnW p n m pp q
  else if k = 3 then callW p n "rci_caps" [q, pp + 5] m
  else if k = 4 then ciCtorW p n m pp q
  else if k = 5 then ciRecW p n m pp q
  else some ([q], m)

/-- `rci_ci(q)`. -/
def ciW (m : Mem) (q : Word) : Option (List Word × Mem) :=
  rdU p n m q fun k m0 =>
  match ciSize k with
  | none => none
  | some sz =>
  ntBW (callW p n "erec_alloc" [sz] m0) fun r1 m1 =>
  putE p n m1 (r1.headD 0) k fun m1' =>
  ntBW (callW p n "rci_cv" [q + 8, r1.headD 0 + 1] m1') fun r2 m2 =>
  ntBW (ciTailW p n m2 k (r1.headD 0) (r2.headD 0)) fun r3 m3 =>
  some ([r1.headD 0, r3.headD 0], m3)








end models

/-! ## The generated models and specs (`pfuel`: the model at `n`, the spec at `exec p (n + 1)`) -/

l_model slot_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rci_slot ↦ slotW list]
  specs [callW_spec p n "rom_u64_c"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model fresh_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rci_fresh ↦ freshW list]
  specs [callW_spec p n "rset_clear"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model namesTo_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rci_names_to ↦ namesToW list]
  specs [callW_spec p n "rom_name_c", callW_spec p n "erec_put", callW_spec p n "rci_names_to"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model lvlsTo_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rci_lvls_to ↦ lvlsToW list]
  specs [callW_spec p n "rom_level_c", callW_spec p n "erec_put", callW_spec p n "rci_lvls_to"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model nameSl_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rci_name_sl ↦ nameSlW list]
  specs [callW_spec p n "rom_u64_c", callW_spec p n "erec_alloc", callW_spec p n "erec_put", callW_spec p n "rci_names_to"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model cv_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rci_cv ↦ cvW list]
  specs [callW_spec p n "rom_name_c", callW_spec p n "erec_put", callW_spec p n "rci_name_sl", callW_spec p n "rom_expr_c"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model caps_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rci_caps ↦ capsW list]
  specs [callW_spec p n "rom_u64_c", callW_spec p n "erec_put", callW_spec p n "rom_name_c", callW_spec p n "rci_name_sl"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model rulesTo_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rci_rules_to ↦ rulesToW list]
  specs [callW_spec p n "rci_rule", callW_spec p n "rci_rules_to"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model blockTo_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rci_block_to ↦ blockToW list]
  specs [callW_spec p n "rci_ci", callW_spec p n "rci_block_to"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model block_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rci_block ↦ blockW list]
  specs [callW_spec p n "rci_slot", callW_spec p n "rom_u64_c", callW_spec p n "rci_fresh", callW_spec p n "iw_alloc", callW_spec p n "rci_block_to"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model basis_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rom_basis_decls ↦ basisW list]
  specs [callW_spec p n "rci_block"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model andPin_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rom_and_pin ↦ andPinW list]
  specs [callW_spec p n "rci_block"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model ciEntry_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rom_ci ↦ ciEntryW list]
  specs [callW_spec p n "rci_slot", callW_spec p n "rci_fresh", callW_spec p n "rci_ci"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model cvEntry_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rom_cv ↦ cvEntryW list]
  specs [callW_spec p n "rci_slot", callW_spec p n "erec_alloc", callW_spec p n "rci_fresh", callW_spec p n "rci_cv"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model exprPin_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rom_expr_pin ↦ exprPinW list]
  specs [callW_spec p n "rci_slot", callW_spec p n "rci_fresh", callW_spec p n "rom_expr_c"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

/-! ## The specs: each function computes its model -/

section specs
variable (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p) (n : Nat) (s₀ : St)
include hL

/-- The common preamble: unfold the call and the body. -/
local macro "rci_pre " fd:term : tactic => `(tactic| (
  rw [invoke_eq _ $fd]
  simp only [callFn, rciSlot, rciFresh, rciNamesTo, rciLvlsTo, rciNameSl, rciCv, rciCaps, rciRule,
    rciRulesTo, rciCi, rciBlockTo, rciBlock, romBasisDeclsL, romCiL, romCvL,
    romExprPinL, romAndPinL]))








set_option maxHeartbeats 4000000 in
theorem rule_specW (q rr : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_rule" [q, rr]
    ⦃fun r s' => LocEq s' s₀ ∧ ruleW p n s₀.mem q rr = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_rule
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, st64,
    callW_spec p n "rom_u64_c", callW_spec p n "rom_name_c", callW_spec p n "erec_put", callW_spec p n "erec_alloc", callW_spec p n "rci_lvls_to", callW_spec p n "rom_exprs_to_c", callW_spec p n "rom_expr_c"]
  all_goals subst_vars
  all_goals (try simp only [LocEq] at *)
  all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    Locals.init_cons_zero, Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq] at *)
  all_goals grind (gen := 30) (instances := 10000) [lang_grind, arena_grind, ruleW, ruleW.ruleTailW, ruleLvlW, rulePinW, ntBW]


set_option maxHeartbeats 4000000 in
theorem ci_specW (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_ci" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ ciW p n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_ci
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, st64,
    callW_spec p n "rom_u64_c", callW_spec p n "erec_alloc", callW_spec p n "erec_put", callW_spec p n "rci_cv", callW_spec p n "rom_expr_c", callW_spec p n "rci_caps", callW_spec p n "rci_rules_to"]
  all_goals subst_vars
  all_goals (try simp only [LocEq] at *)
  all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    Locals.init_cons_zero, Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq] at *)
  all_goals grind (gen := 30) (instances := 10000) [lang_grind, arena_grind, ciW, ciTailW, ciDefnW, ciCtorW, ciRecW, ciSize, ntBW]








end specs

end L.Rom
