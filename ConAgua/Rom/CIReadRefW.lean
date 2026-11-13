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
recursive and every spec is one `vcgen`: all generated (`l_model … pfuel`, lane mgen3). The
relational lemmas (`CIReadRef*.lean`) unfold these models one call at a time, by induction on the
L fuel; `rom_u64` is read as its value `u64W rom i` there (`u64_some`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

section models
variable (p : Prog) (n : Nat)

/-- An `erec_put(a, v)` through `callW`. -/
abbrev putE (m : Mem) (a v : Word) (k : Mem → Option (List Word × Mem)) :
    Option (List Word × Mem) :=
  ntBW (callW p n "erec_put" [a, v] m) fun _ m' => k m'

/-- A constant record's size by its kind word: the sizes `rci_ci` allocates (the refinements'
table of the kinds). -/
def ciSize (k : Word) : Option Word :=
  if k = 0 then some 5 else if k = 2 then some 5 else if k = 1 then some 8 else if k = 3 then some 20
  else if k = 4 then some 8 else if k = 5 then some 10 else none

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

l_model rule_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rci_rule ↦ ruleW list]
  specs [callW_spec p n "rom_u64_c", callW_spec p n "rom_name_c", callW_spec p n "erec_put", callW_spec p n "erec_alloc", callW_spec p n "rci_lvls_to", callW_spec p n "rom_exprs_to_c", callW_spec p n "rom_expr_c"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model rulesTo_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rci_rules_to ↦ rulesToW list]
  specs [callW_spec p n "rci_rule", callW_spec p n "rci_rules_to"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model ci_specW (rom : List UInt8) (p : Prog) (hL : RomCIProg rom p)
  fns [hL.rci_ci ↦ ciW list]
  specs [callW_spec p n "rom_u64_c", callW_spec p n "erec_alloc", callW_spec p n "erec_put", callW_spec p n "rci_cv", callW_spec p n "rom_expr_c", callW_spec p n "rci_caps", callW_spec p n "rci_rules_to", callW_spec p n "rom_name_c"]
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

end L.Rom
