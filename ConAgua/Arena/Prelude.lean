import ConAgua.Arena.RomCI
import ConAgua.Rom.CIEnc

/-!
# The program's ROM: the pinned names, then the startup walk's item stream

`romData` is the one constant byte string of the checker program (`rom.c8[i]`): the 51 pinned
names and the 16 reserved basis names (`intern_reserved_pins`, offset `0`), then the structured
constants of the ROM stubs (`romCIData`, offset `ciOff`, `ConAgua/Rom/CIEnc.lean`; read by
`rom_ci`, `rom_basis_decls`, …), then the item stream of `internAllPins` (`intern_all_pins`,
offset `allPinsOff`; the variant list follows it in the pin-data buffer). The pin list is free (the final
theorem holds at every pin list, `ConAgua/Final/Twin.lean`). The ROM itself carries no
`Nat`-operation pin variant (`romPins = []`): the checker's variants are an input, the pin-data
buffer's list after `romData` (`L.Rom.internAllPinsPB`, DESIGN.md "The pin data as an input"); the
item stream here is the startup walk's part that does not depend on them.
-/

open ConRon.Arena

namespace L.Rom

open L.Arena

/-- The pin variants in the ROM's own item stream: none (the variants are the pin-data buffer's). -/
def romPins : List ConLeche.NatOpPinSet := []

/-- The program's ROM. -/
def romData : List UInt8 :=
  encNames pinNames ++ (encNames reservedBasisNameValues ++ (romCIData ++ encItems [] (itemsAllPins romPins)))

/-- Where the structured constants start. -/
def ciOff : Word := UInt64.ofNat (encNames pinNames ++ encNames reservedBasisNameValues).length

/-- Where the startup walk's items start. -/
def allPinsOff : Word :=
  UInt64.ofNat (encNames pinNames ++ encNames reservedBasisNameValues ++ romCIData).length

/-- `intern_all_pins_rom()`: the ROM-only pin stage (superseded by `L.Rom.internAllPinsPB`, the program's `intern_all_pins`; renamed by lane integrate so that one name has one body). -/
-- con-ron: ConRon/Arena/Checker.lean:312-342 ConRon.Arena.internAllPins
@[l_impl ConRon.Arena.internAllPins]
def internAllPinsL : FunDecl := internAllPinsAt allPinsOff

/-- `rom_expr(pos)` as the program has it (the expression ROM reader at the program's ROM). -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:194-256 ConRon.Arena.Frontend.internExprGo
@[l_impl ConRon.Arena.Frontend.internExprGo]
def romExprL : FunDecl := romExpr romData

set_option maxRecDepth 100000 in
theorem romData_len : romData.length < 2 ^ 63 := by decide +kernel

end L.Rom

namespace L.Rom
open L.Arena

set_option maxRecDepth 100000 in
theorem allPins_fits : (itemsAllPins romPins).all itemFits = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem pinNames_fit : pinNames.all nameFits = true ∧ reservedBasisNameValues.all nameFits = true := by
  decide +kernel

end L.Rom

namespace L.Rom
open L.Arena
open Std.WP
open scoped Lean.Order

theorem romData_split : romData =
    (encNames pinNames ++ encNames reservedBasisNameValues ++ romCIData) ++ encItems [] (itemsAllPins romPins) := by
  simp [romData]

theorem allPinsOff_toNat :
    allPinsOff.toNat = (encNames pinNames ++ encNames reservedBasisNameValues ++ romCIData).length := by
  have := romData_len
  simp only [romData, List.length_append] at this
  simp only [allPinsOff, List.length_append, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

end L.Rom
