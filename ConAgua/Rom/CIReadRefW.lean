import ConAgua.Rom.CIReadSpec
import ConAgua.Arena.DeclNatBase

/-!
# The ROM constant readers' word models (helper `decls4-rom`)

One model per function of `romCIProg` (`CIRead.lean`), each calling its callees through `callW`
(lane `whnf`'s "a call as a function of the memory"; `DeclNatBase.lean`'s `ntBW`), so no model is
recursive and every spec is one `vcgen`. `rom_u64` is read as its value `u64W rom i` (its range
check matters only in the decoder direction). The relational lemmas (`CIReadRef*.lean`) unfold
these models one call at a time, by induction on the L fuel.
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

section models
variable (rom : List UInt8) (p : Prog) (n : Nat)

/-- `rci_slot(s)`. -/
def slotW (m : Mem) (s : Word) : Option (List Word × Mem) :=
  some ([ciOff + u64W rom (ciOff + 8 * s)], m)

/-- `rci_fresh()`. -/
def freshW (m : Mem) : Option (List Word × Mem) :=
  ntBW (callW p n "rset_clear" [] ((m.set64 CTL 131 0).set64 CTL 132 0)) fun _ m1 => some ([0], m1)

/-- `rci_names_to(q, o, k)`. -/
def namesToW (m : Mem) (q o k : Word) : Option (List Word × Mem) :=
  if k = 0 then some ([q], m) else
  ntBW (callW p n "rom_name" [q] m) fun r1 m1 =>
  ntBW (callW p n "rci_names_to" [r1.tail.headD 0, o + 1, k - 1] (m1.set64 EREC o (r1.headD 0)))
    fun r2 m2 => some ([r2.headD 0], m2)

/-- `rci_lvls_to(q, o, k)`. -/
def lvlsToW (m : Mem) (q o k : Word) : Option (List Word × Mem) :=
  if k = 0 then some ([q], m) else
  ntBW (callW p n "rom_level" [q] m) fun r1 m1 =>
  ntBW (callW p n "rci_lvls_to" [r1.tail.headD 0, o + 1, k - 1] (m1.set64 EREC o (r1.headD 0)))
    fun r2 m2 => some ([r2.headD 0], m2)

/-- `rci_name_sl(q, d)`. -/
def nameSlW (m : Mem) (q d : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "erec_alloc" [u64W rom q] m) fun r1 m1 =>
  ntBW (callW p n "rci_names_to" [q + 8, r1.headD 0, u64W rom q]
    ((m1.set64 EREC d (r1.headD 0)).set64 EREC (d + 1) (u64W rom q))) fun r2 m2 =>
  some ([r2.headD 0], m2)

/-- `rci_cv(q, p)`. -/
def cvW (m : Mem) (q pp : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "rom_name" [q] m) fun r1 m1 =>
  ntBW (callW p n "rci_name_sl" [r1.tail.headD 0, pp + 1] (m1.set64 EREC pp (r1.headD 0))) fun r2 m2 =>
  ntBW (callW p n "rom_expr" [r2.headD 0] m2) fun r3 m3 =>
  some ([r3.tail.headD 0], m3.set64 EREC (pp + 3) (r3.headD 0))

/-- The eight number words of an inductive's capabilities. -/
def capsNums (m : Mem) (q c : Word) : Mem :=
  (((((((m.set64 EREC c (u64W rom q)).set64 EREC (c + 2) (u64W rom (q + 8))).set64 EREC (c + 3)
    (u64W rom (q + 16))).set64 EREC (c + 4) (u64W rom (q + 24))).set64 EREC (c + 5)
    (u64W rom (q + 32))).set64 EREC (c + 6) (u64W rom (q + 40))).set64 EREC (c + 12)
    (u64W rom (q + 48))).set64 EREC (c + 7) (u64W rom (q + 56))

/-- `rci_caps(q, c)`. -/
def capsW (m : Mem) (q c : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "rom_name" [q + 64] (capsNums rom m q c)) fun r1 m1 =>
  ntBW (callW p n "rci_name_sl" [r1.tail.headD 0, c + 10] (m1.set64 EREC (c + 1) (r1.headD 0)))
    fun r2 m2 =>
  ntBW (callW p n "rci_name_sl" [r2.headD 0, c + 13] m2) fun r3 m3 =>
  ntBW (callW p n "rci_name_sl" [r3.headD 0, c + 8] m3) fun r4 m4 =>
  some ([r4.headD 0], m4)

/-- A rule's head words (after its constructor name). -/
def ruleHead (m : Mem) (h q r : Word) : Mem :=
  (((((((((m.set64 EREC r h).set64 EREC (r + 1) (u64W rom q)).set64 EREC (r + 2)
    (u64W rom (q + 8))).set64 EREC (r + 9) (u64W rom (q + 16))).set64 EREC (r + 10)
    (u64W rom (q + 24))).set64 EREC (r + 3) (u64W rom (q + 32))).set64 EREC (r + 4) 0).set64 EREC
    (r + 5) 0).set64 EREC (r + 6) 0).set64 EREC (r + 7) 0

/-- A rule's nested fire: the level slice, then the pin slice; the position after. -/
def ruleNestW (m : Mem) (q r : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "erec_alloc" [u64W rom q] m) fun r1 m1 =>
  ntBW (callW p n "rci_lvls_to" [q + 8, r1.headD 0, u64W rom q]
    ((m1.set64 EREC (r + 4) (r1.headD 0)).set64 EREC (r + 5) (u64W rom q))) fun r2 m2 =>
  ntBW (callW p n "erec_alloc" [u64W rom (r2.headD 0)] m2) fun r3 m3 =>
  ntBW (callW p n "rom_exprs_to" [r2.headD 0 + 8, r3.headD 0, u64W rom (r2.headD 0)]
    ((m3.set64 EREC (r + 6) (r3.headD 0)).set64 EREC (r + 7) (u64W rom (r2.headD 0)))) fun r4 m4 =>
  some ([r4.headD 0], m4)

/-- `rci_rule(q, r)`. -/
def ruleW (m : Mem) (q r : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "rom_name" [q] m) fun r1 m1 =>
  ntBW (if u64W rom (r1.tail.headD 0 + 32) = 1 then
      ruleNestW rom p n (ruleHead rom m1 (r1.headD 0) (r1.tail.headD 0) r) (r1.tail.headD 0 + 40) r
    else some ([r1.tail.headD 0 + 40], ruleHead rom m1 (r1.headD 0) (r1.tail.headD 0) r)) fun r2 m2 =>
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
  if k = 0 ∨ k = 2 then some 5 else if k = 1 then some 8 else if k = 3 then some 20
  else if k = 4 then some 7 else if k = 5 then some 9 else none

/-- The kind's parts after the constant value (at `q`, record `pp`). -/
def ciTailW (m : Mem) (k pp q : Word) : Option (List Word × Mem) :=
  if k = 1 then
    ntBW (callW p n "rom_expr" [q] m) fun r1 m1 =>
    some ([r1.tail.headD 0 + 16], ((m1.set64 EREC (pp + 5) (r1.headD 0)).set64 EREC (pp + 6)
      (u64W rom (r1.tail.headD 0))).set64 EREC (pp + 7) (u64W rom (r1.tail.headD 0 + 8)))
  else if k = 3 then callW p n "rci_caps" [q, pp + 5] m
  else if k = 4 then
    some ([q + 16], (m.set64 EREC (pp + 5) (u64W rom q)).set64 EREC (pp + 6) (u64W rom (q + 8)))
  else if k = 5 then
    ntBW (callW p n "erec_alloc" [11 * u64W rom (q + 16)]
      ((m.set64 EREC (pp + 5) (u64W rom q)).set64 EREC (pp + 6) (u64W rom (q + 8)))) fun r1 m1 =>
    callW p n "rci_rules_to" [q + 24, r1.headD 0, u64W rom (q + 16)]
      ((m1.set64 EREC (pp + 7) (r1.headD 0)).set64 EREC (pp + 8) (u64W rom (q + 16)))
  else some ([q], m)

/-- `rci_ci(q)`. -/
def ciW (m : Mem) (q : Word) : Option (List Word × Mem) :=
  match ciSize (u64W rom q) with
  | none => none
  | some sz =>
  ntBW (callW p n "erec_alloc" [sz] m) fun r1 m1 =>
  ntBW (callW p n "rci_cv" [q + 8, r1.headD 0 + 1] (m1.set64 EREC (r1.headD 0) (u64W rom q)))
    fun r2 m2 =>
  ntBW (ciTailW rom p n m2 (u64W rom q) (r1.headD 0) (r2.headD 0)) fun r3 m3 =>
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
  ntBW (callW p n "rci_fresh" [] m1) fun _ m2 =>
  ntBW (callW p n "iw_alloc" [u64W rom (r1.headD 0)] m2) fun r3 m3 =>
  ntBW (callW p n "rci_block_to" [r1.headD 0 + 8, r3.headD 0, u64W rom (r1.headD 0)] m3) fun _ m4 =>
  some ([r3.headD 0, u64W rom (r1.headD 0)], m4)

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
    ⦃fun r s' => LocEq s' s₀ ∧ slotW rom s₀.mem s = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_slot
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n] <;>
    finish [slotW, ntBW]

theorem fresh_specW :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_fresh" []
    ⦃fun r s' => LocEq s' s₀ ∧ freshW p n s₀.mem = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_fresh
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "rset_clear"] <;>
    finish [freshW, ntBW]

theorem namesTo_specW (q o k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_names_to" [q, o, k]
    ⦃fun r s' => LocEq s' s₀ ∧ namesToW p n s₀.mem q o k = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_names_to
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "rom_name", callW_spec p n "rci_names_to"] <;>
    finish [namesToW, ntBW]

theorem lvlsTo_specW (q o k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_lvls_to" [q, o, k]
    ⦃fun r s' => LocEq s' s₀ ∧ lvlsToW p n s₀.mem q o k = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_lvls_to
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "rom_level", callW_spec p n "rci_lvls_to"] <;>
    finish [lvlsToW, ntBW]

theorem nameSl_specW (q d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_name_sl" [q, d]
    ⦃fun r s' => LocEq s' s₀ ∧ nameSlW rom p n s₀.mem q d = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_name_sl
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "erec_alloc", callW_spec p n "rci_names_to"] <;>
    finish [nameSlW, ntBW]

theorem cv_specW (q pp : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_cv" [q, pp]
    ⦃fun r s' => LocEq s' s₀ ∧ cvW p n s₀.mem q pp = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_cv
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "rom_name", callW_spec p n "rci_name_sl", callW_spec p n "rom_expr"] <;>
    finish [cvW, ntBW]

theorem caps_specW (q c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_caps" [q, c]
    ⦃fun r s' => LocEq s' s₀ ∧ capsW rom p n s₀.mem q c = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_caps
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "rom_name", callW_spec p n "rci_name_sl"] <;>
    finish [capsW, ntBW]

theorem rule_specW (q r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_rule" [q, r]
    ⦃fun r s' => LocEq s' s₀ ∧ ruleW rom p n s₀.mem q r = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_rule
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "rom_name", callW_spec p n "erec_alloc", callW_spec p n "rci_lvls_to", callW_spec p n "rom_exprs_to", callW_spec p n "rom_expr"] <;>
    finish [ruleW, ntBW]

theorem rulesTo_specW (q o k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_rules_to" [q, o, k]
    ⦃fun r s' => LocEq s' s₀ ∧ rulesToW p n s₀.mem q o k = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_rules_to
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "rci_rule", callW_spec p n "rci_rules_to"] <;>
    finish [rulesToW, ntBW]

theorem ci_specW (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_ci" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ ciW rom p n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_ci
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "erec_alloc", callW_spec p n "rci_cv", callW_spec p n "rom_expr", callW_spec p n "rci_caps", callW_spec p n "rci_rules_to"] <;>
    finish [ciW, ntBW]

theorem blockTo_specW (q o k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_block_to" [q, o, k]
    ⦃fun r s' => LocEq s' s₀ ∧ blockToW p n s₀.mem q o k = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_block_to
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "rci_ci", callW_spec p n "rci_block_to"] <;>
    finish [blockToW, ntBW]

theorem block_specW (s : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rci_block" [s]
    ⦃fun r s' => LocEq s' s₀ ∧ blockW rom p n s₀.mem s = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rci_block
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "rci_slot", callW_spec p n "rci_fresh", callW_spec p n "iw_alloc", callW_spec p n "rci_block_to"] <;>
    finish [blockW, ntBW]

theorem basis_specW (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_basis_decls" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ basisW p n s₀.mem k 0 = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rom_basis_decls
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "rci_block"] <;>
    finish [basisW, ntBW]

theorem basisA_specW (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_basis_decls_a" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ basisW p n s₀.mem k 5 = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rom_basis_decls_a
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "rci_block"] <;>
    finish [basisW, ntBW]

theorem andPin_specW  :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_and_pin" []
    ⦃fun r s' => LocEq s' s₀ ∧ andPinW p n s₀.mem = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rom_and_pin
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "rci_block"] <;>
    finish [andPinW, ntBW]

theorem ciEntry_specW (id : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_ci" [id]
    ⦃fun r s' => LocEq s' s₀ ∧ ciEntryW p n s₀.mem id = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rom_ci
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "rci_slot", callW_spec p n "rci_fresh", callW_spec p n "rci_ci"] <;>
    finish [ciEntryW, ntBW]

theorem cvEntry_specW (id : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_cv" [id]
    ⦃fun r s' => LocEq s' s₀ ∧ cvEntryW p n s₀.mem id = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rom_cv
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "rci_slot", callW_spec p n "erec_alloc", callW_spec p n "rci_fresh", callW_spec p n "rci_cv"] <;>
    finish [cvEntryW, ntBW]

theorem exprPin_specW (id : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_expr_pin" [id]
    ⦃fun r s' => LocEq s' s₀ ∧ exprPinW p n s₀.mem id = some (r, s'.mem); ⊤⦄ := by
  rci_pre hL.rom_expr_pin
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      romU64_spec rom p hL.rom_u64 n, callW_spec p n "rci_slot", callW_spec p n "rci_fresh", callW_spec p n "rom_expr"] <;>
    finish [exprPinW, ntBW]

end specs

end L.Rom
