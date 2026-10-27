import ConAgua.Arena.LdRd
import ConAgua.Rom.CIReadSpec
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

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
  ntBW (callW p n "rom_u64" [i] m) fun r m' => k (r.headD 0) m'

/-- `rci_slot(s)`. -/
def slotW (m : Mem) (s : Word) : Option (List Word × Mem) :=
  rdU p n m (ciOff + 8 * s) fun x m1 => some ([ciOff + x], m1)

/-- `rci_fresh()`. -/
def freshW (m : Mem) : Option (List Word × Mem) :=
  ntBW (callW p n "rset_clear" [] ((m.set64 CTL 131 0).set64 CTL 132 0)) fun _ m1 => some ([0], m1)

/-- `rci_names_to(q, o, k)`. -/
def namesToW (m : Mem) (q o k : Word) : Option (List Word × Mem) :=
  if k = 0 then some ([q], m) else
  ntBW (callW p n "rom_name" [q] m) fun r1 m1 =>
  ntBW (callW p n "rci_names_to" [r1.tail.headD 0, o + 1, k - 1] (m1.set64 EREC o (r1.headD 0)))
    fun r2 m2 => some ([r2.headD 0], m2)

/-- `rci_name_sl(q, d)`. -/
def nameSlW (m : Mem) (q d : Word) : Option (List Word × Mem) :=
  rdU p n m q fun c m0 =>
  ntBW (callW p n "erec_alloc" [c] m0) fun r1 m1 =>
  ntBW (callW p n "rci_names_to" [q + 8, r1.headD 0, c]
    ((m1.set64 EREC d (r1.headD 0)).set64 EREC (d + 1) c)) fun r2 m2 =>
  some ([r2.headD 0], m2)

/-- `rci_cv(q, p)`. -/
def cvW (m : Mem) (q pp : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "rom_name" [q] m) fun r1 m1 =>
  ntBW (callW p n "rci_name_sl" [r1.tail.headD 0, pp + 1] (m1.set64 EREC pp (r1.headD 0))) fun r2 m2 =>
  ntBW (callW p n "rom_expr" [r2.headD 0] m2) fun r3 m3 =>
  some ([r3.tail.headD 0], m3.set64 EREC (pp + 3) (r3.headD 0))

/-- `rci_caps(q, c)`: the eight numbers. -/
def capsW (m : Mem) (q c : Word) : Option (List Word × Mem) :=
  rdU p n m q fun x0 m0 =>
  rdU p n (m0.set64 EREC c x0) (q + 8) fun x1 m1 =>
  rdU p n (m1.set64 EREC (c + 2) x1) (q + 16) fun x2 m2 =>
  rdU p n (m2.set64 EREC (c + 3) x2) (q + 24) fun x3 m3 =>
  rdU p n (m3.set64 EREC (c + 4) x3) (q + 32) fun x4 m4 =>
  rdU p n (m4.set64 EREC (c + 5) x4) (q + 40) fun x5 m5 =>
  rdU p n (m5.set64 EREC (c + 6) x5) (q + 48) fun x6 m6 =>
  rdU p n (m6.set64 EREC (c + 12) x6) (q + 56) fun x7 m7 =>
  capsTailW p n (m7.set64 EREC (c + 7) x7) q c
where
  /-- The names. -/
  capsTailW (p : Prog) (n : Nat) (m : Mem) (q c : Word) : Option (List Word × Mem) :=
    ntBW (callW p n "rom_name" [q + 64] m) fun r1 m1 =>
    ntBW (callW p n "rci_name_sl" [r1.tail.headD 0, c + 10] (m1.set64 EREC (c + 1) (r1.headD 0)))
      fun r2 m2 =>
    ntBW (callW p n "rci_name_sl" [r2.headD 0, c + 13] m2) fun r3 m3 =>
    ntBW (callW p n "rci_name_sl" [r3.headD 0, c + 8] m3) fun r4 m4 =>
    some ([r4.headD 0], m4)

/-- A rule's nested fire: the level slice, then the pin slice; the position after. -/
def ruleNestW (m : Mem) (q r : Word) : Option (List Word × Mem) :=
  rdU p n m q fun l1 m0 =>
  ntBW (callW p n "erec_alloc" [l1] m0) fun r1 m1 =>
  ntBW (callW p n "rci_lvls_to" [q + 8, r1.headD 0, l1]
    ((m1.set64 EREC (r + 4) (r1.headD 0)).set64 EREC (r + 5) l1)) fun r2 m2 =>
  rdU p n m2 (r2.headD 0) fun l2 m2' =>
  ntBW (callW p n "erec_alloc" [l2] m2') fun r3 m3 =>
  ntBW (callW p n "rom_exprs_to" [r2.headD 0 + 8, r3.headD 0, l2]
    ((m3.set64 EREC (r + 6) (r3.headD 0)).set64 EREC (r + 7) l2)) fun r4 m4 =>
  some ([r4.headD 0], m4)

/-- `rci_rule(q, r)`. -/
def ruleW (m : Mem) (q r : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "rom_name" [q] m) fun r1 m1 =>
  rdU p n (m1.set64 EREC r (r1.headD 0)) (r1.tail.headD 0) fun x1 m2 =>
  rdU p n (m2.set64 EREC (r + 1) x1) (r1.tail.headD 0 + 8) fun x2 m3 =>
  rdU p n (m3.set64 EREC (r + 2) x2) (r1.tail.headD 0 + 16) fun x3 m4 =>
  rdU p n (m4.set64 EREC (r + 9) x3) (r1.tail.headD 0 + 24) fun x4 m5 =>
  rdU p n (m5.set64 EREC (r + 10) x4) (r1.tail.headD 0 + 32) fun f m6 =>
  ruleTailW p n ((((((m6.set64 EREC (r + 3) f).set64 EREC (r + 4) 0).set64 EREC (r + 5) 0).set64 EREC
    (r + 6) 0).set64 EREC (r + 7) 0)) (r1.tail.headD 0 + 40) r f
where
  /-- The fire's slices (nested), then the right-hand side. -/
  ruleTailW (p : Prog) (n : Nat) (m : Mem) (q r f : Word) : Option (List Word × Mem) :=
    ntBW (if f = 1 then ruleNestW p n m q r else some ([q], m)) fun r2 m2 =>
    ntBW (callW p n "rom_expr" [r2.headD 0] m2) fun r3 m3 =>
    some ([r3.tail.headD 0], m3.set64 EREC (r + 8) (r3.headD 0))

/-- `rci_rules_to(q, o, k)`. -/
def rulesToW (m : Mem) (q o k : Word) : Option (List Word × Mem) :=
  if k = 0 then some ([q], m) else
  ntBW (callW p n "rci_rule" [q, o] m) fun r1 m1 =>
  ntBW (callW p n "rci_rules_to" [r1.headD 0, o + 11, k - 1] m1) fun r2 m2 =>
  some ([r2.headD 0], m2)

/-- A constant record's size by its kind word. -/
def ciSize (k : Word) : Option Word :=
  if k = 0 then some 5 else if k = 2 then some 5 else if k = 1 then some 8 else if k = 3 then some 20
  else if k = 4 then some 7 else if k = 5 then some 9 else none

/-- The definition's parts. -/
def ciDefnW (m : Mem) (pp q : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "rom_expr" [q] m) fun r1 m1 =>
  rdU p n (m1.set64 EREC (pp + 5) (r1.headD 0)) (r1.tail.headD 0) fun x1 m2 =>
  rdU p n (m2.set64 EREC (pp + 6) x1) (r1.tail.headD 0 + 8) fun x2 m3 =>
  some ([r1.tail.headD 0 + 16], m3.set64 EREC (pp + 7) x2)

/-- The constructor's numbers. -/
def ciCtorW (m : Mem) (pp q : Word) : Option (List Word × Mem) :=
  rdU p n m q fun x1 m1 =>
  rdU p n (m1.set64 EREC (pp + 5) x1) (q + 8) fun x2 m2 =>
  some ([q + 16], m2.set64 EREC (pp + 6) x2)

/-- The recursor's numbers and rules. -/
def ciRecW (m : Mem) (pp q : Word) : Option (List Word × Mem) :=
  rdU p n m q fun x1 m1 =>
  rdU p n (m1.set64 EREC (pp + 5) x1) (q + 8) fun x2 m2 =>
  rdU p n (m2.set64 EREC (pp + 6) x2) (q + 16) fun l m3 =>
  ntBW (callW p n "erec_alloc" [11 * l] m3) fun r1 m4 =>
  callW p n "rci_rules_to" [q + 24, r1.headD 0, l]
    ((m4.set64 EREC (pp + 7) (r1.headD 0)).set64 EREC (pp + 8) l)

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
  ntBW (callW p n "rci_cv" [q + 8, r1.headD 0 + 1] (m1.set64 EREC (r1.headD 0) k))
    fun r2 m2 =>
  ntBW (ciTailW p n m2 k (r1.headD 0) (r2.headD 0)) fun r3 m3 =>
  some ([r1.headD 0, r3.headD 0], m3)

/-- `rci_block_to(q, o, k)`. -/
def blockToW (m : Mem) (q o k : Word) : Option (List Word × Mem) :=
  if k = 0 then some ([q], m) else
  ntBW (callW p n "rci_ci" [q] m) fun r1 m1 =>
  ntBW (callW p n "rci_block_to" [r1.tail.headD 0, o + 1, k - 1] (m1.set64 IW o (r1.headD 0)))
    fun r2 m2 => some ([r2.headD 0], m2)

/-- `rci_block(s)`. -/
def blockW (m : Mem) (s : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "rci_slot" [s] m) fun r1 m1 =>
  rdU p n m1 (r1.headD 0) fun c m1' =>
  ntBW (callW p n "rci_fresh" [] m1') fun _ m2 =>
  ntBW (callW p n "iw_alloc" [c] m2) fun r3 m3 =>
  ntBW (callW p n "rci_block_to" [r1.headD 0 + 8, r3.headD 0, c] m3) fun _ m4 =>
  some ([r3.headD 0, c], m4)

/-- `rom_basis_decls(kind)` and `rom_basis_decls_a(kind)` (slot `kind + off`). -/
def basisW (m : Mem) (k off : Word) : Option (List Word × Mem) :=
  if 5 ≤ k then none else
  ntBW (callW p n "rci_block" [k + off] m) fun r m1 => some ([r.headD 0, r.tail.headD 0], m1)

/-- `rom_and_pin()`. -/
def andPinW (m : Mem) : Option (List Word × Mem) :=
  ntBW (callW p n "rci_block" [30] m) fun r m1 => some ([r.headD 0, r.tail.headD 0], m1)

/-- `rom_ci(id)`. -/
def ciEntryW (m : Mem) (id : Word) : Option (List Word × Mem) :=
  if 8 ≤ id then none else
  ntBW (callW p n "rci_slot" [10 + id] m) fun r1 m1 =>
  ntBW (callW p n "rci_fresh" [] m1) fun _ m2 =>
  ntBW (callW p n "rci_ci" [r1.headD 0] m2) fun r3 m3 => some ([r3.headD 0], m3)

/-- `rom_cv(id)`. -/
def cvEntryW (m : Mem) (id : Word) : Option (List Word × Mem) :=
  if 10 ≤ id then none else
  ntBW (callW p n "rci_slot" [18 + id] m) fun r1 m1 =>
  ntBW (callW p n "erec_alloc" [4] m1) fun r2 m2 =>
  ntBW (callW p n "rci_fresh" [] m2) fun _ m3 =>
  ntBW (callW p n "rci_cv" [r1.headD 0, r2.headD 0] m3) fun _ m4 => some ([r2.headD 0], m4)

/-- `rom_expr_pin(id)`. -/
def exprPinW (m : Mem) (id : Word) : Option (List Word × Mem) :=
  if 2 ≤ id then none else
  ntBW (callW p n "rci_slot" [28 + id] m) fun r1 m1 =>
  ntBW (callW p n "rci_fresh" [] m1) fun _ m2 =>
  ntBW (callW p n "rom_expr" [r1.headD 0] m2) fun r3 m3 => some ([r3.headD 0], m3)

end models

/-! ## The specs: each function computes its model -/

section specs
variable (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p) (n : Nat) (s₀ : St)
include hL

/-- The common preamble: unfold the call and the body. -/
local macro "rci_pre " fd:term : tactic => `(tactic| (
  rw [invoke_eq _ $fd]
  simp only [callFn, rciSlot, rciFresh, rciNamesTo, rciLvlsTo, rciNameSl, rciCv, rciCaps, rciRule,
    rciRulesTo, rciCi, rciBlockTo, rciBlock, romBasisDeclsL, romBasisDeclsAL, romCiL, romCvL,
    romExprPinL, romAndPinL]))

theorem slot_specW (s : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_slot" [s]
    ⦃fun r s' => LocEq s' s₀ ∧ slotW p n s₀.mem s = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_slot
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rom_u64"] <;>
    finish (gen := 30) (instances := 10000) [slotW, ntBW]

theorem fresh_specW :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_fresh" []
    ⦃fun r s' => LocEq s' s₀ ∧ freshW p n s₀.mem = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_fresh
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rom_u64", callW_spec p n "rset_clear"] <;>
    finish (gen := 30) (instances := 10000) [freshW, ntBW]

theorem namesTo_specW (q o k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_names_to" [q, o, k]
    ⦃fun r s' => LocEq s' s₀ ∧ namesToW p n s₀.mem q o k = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_names_to
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rom_u64", callW_spec p n "rom_name", callW_spec p n "rci_names_to"] <;>
    finish (gen := 30) (instances := 10000) [namesToW, ntBW]

theorem nameSl_specW (q d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_name_sl" [q, d]
    ⦃fun r s' => LocEq s' s₀ ∧ nameSlW p n s₀.mem q d = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_name_sl
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rom_u64", callW_spec p n "erec_alloc", callW_spec p n "rci_names_to"] <;>
    finish (gen := 30) (instances := 10000) [nameSlW, ntBW]

theorem cv_specW (q pp : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_cv" [q, pp]
    ⦃fun r s' => LocEq s' s₀ ∧ cvW p n s₀.mem q pp = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_cv
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rom_u64", callW_spec p n "rom_name", callW_spec p n "rci_name_sl", callW_spec p n "rom_expr"] <;>
    finish (gen := 30) (instances := 10000) [cvW, ntBW]

theorem caps_specW (q c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_caps" [q, c]
    ⦃fun r s' => LocEq s' s₀ ∧ capsW p n s₀.mem q c = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_caps
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rom_u64", callW_spec p n "rom_name", callW_spec p n "rci_name_sl"] <;>
    finish (gen := 30) (instances := 10000) [capsW, capsW.capsTailW, ntBW]

set_option maxHeartbeats 4000000 in
theorem rule_specW (q rr : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_rule" [q, rr]
    ⦃fun r s' => LocEq s' s₀ ∧ ruleW p n s₀.mem q rr = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_rule
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, st64, callW_spec p n "rom_u64",
    callW_spec p n "rom_name", callW_spec p n "erec_alloc", callW_spec p n "rci_lvls_to",
    callW_spec p n "rom_exprs_to", callW_spec p n "rom_expr"]
  all_goals subst_vars
  all_goals (try simp only [LocEq] at *)
  all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    Locals.init_cons_zero, Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq] at *)
  all_goals grind (gen := 30) (instances := 10000) [lang_grind, arena_grind, ruleW, ruleW.ruleTailW, ruleNestW,
    ntBW]

theorem rulesTo_specW (q o k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_rules_to" [q, o, k]
    ⦃fun r s' => LocEq s' s₀ ∧ rulesToW p n s₀.mem q o k = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_rules_to
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rom_u64", callW_spec p n "rci_rule", callW_spec p n "rci_rules_to"] <;>
    finish (gen := 30) (instances := 10000) [rulesToW, ntBW]

set_option maxHeartbeats 4000000 in
theorem ci_specW (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_ci" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ ciW p n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_ci
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, st64, callW_spec p n "rom_u64",
    callW_spec p n "erec_alloc", callW_spec p n "rci_cv", callW_spec p n "rom_expr", callW_spec p n "rci_caps",
    callW_spec p n "rci_rules_to"]
  all_goals subst_vars
  all_goals (try simp only [LocEq] at *)
  all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    Locals.init_cons_zero, Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq] at *)
  all_goals grind (gen := 30) (instances := 10000) [lang_grind, arena_grind, ciW, ciTailW, ciDefnW, ciCtorW,
    ciRecW, ciSize, ntBW]

theorem blockTo_specW (q o k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_block_to" [q, o, k]
    ⦃fun r s' => LocEq s' s₀ ∧ blockToW p n s₀.mem q o k = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_block_to
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rom_u64", callW_spec p n "rci_ci", callW_spec p n "rci_block_to"] <;>
    finish (gen := 30) (instances := 10000) [blockToW, ntBW]

theorem block_specW (s : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_block" [s]
    ⦃fun r s' => LocEq s' s₀ ∧ blockW p n s₀.mem s = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_block
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rom_u64", callW_spec p n "rci_slot", callW_spec p n "rci_fresh", callW_spec p n "iw_alloc", callW_spec p n "rci_block_to"] <;>
    finish (gen := 30) (instances := 10000) [blockW, ntBW]

theorem basis_specW (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_basis_decls" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ basisW p n s₀.mem k 0 = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rom_basis_decls
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rom_u64", callW_spec p n "rci_block"] <;>
    finish (gen := 30) (instances := 10000) [basisW, ntBW]

theorem basisA_specW (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_basis_decls_a" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ basisW p n s₀.mem k 5 = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rom_basis_decls_a
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rom_u64", callW_spec p n "rci_block"] <;>
    finish (gen := 30) (instances := 10000) [basisW, ntBW]

theorem andPin_specW  :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_and_pin" []
    ⦃fun r s' => LocEq s' s₀ ∧ andPinW p n s₀.mem = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rom_and_pin
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rom_u64", callW_spec p n "rci_block"] <;>
    finish (gen := 30) (instances := 10000) [andPinW, ntBW]

theorem ciEntry_specW (id : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_ci" [id]
    ⦃fun r s' => LocEq s' s₀ ∧ ciEntryW p n s₀.mem id = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rom_ci
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rom_u64", callW_spec p n "rci_slot", callW_spec p n "rci_fresh", callW_spec p n "rci_ci"] <;>
    finish (gen := 30) (instances := 10000) [ciEntryW, ntBW]

theorem cvEntry_specW (id : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_cv" [id]
    ⦃fun r s' => LocEq s' s₀ ∧ cvEntryW p n s₀.mem id = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rom_cv
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rom_u64", callW_spec p n "rci_slot", callW_spec p n "erec_alloc", callW_spec p n "rci_fresh", callW_spec p n "rci_cv"] <;>
    finish (gen := 30) (instances := 10000) [cvEntryW, ntBW]

theorem exprPin_specW (id : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_expr_pin" [id]
    ⦃fun r s' => LocEq s' s₀ ∧ exprPinW p n s₀.mem id = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rom_expr_pin
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rom_u64", callW_spec p n "rci_slot", callW_spec p n "rci_fresh", callW_spec p n "rom_expr"] <;>
    finish (gen := 30) (instances := 10000) [exprPinW, ntBW]

end specs

end L.Rom
