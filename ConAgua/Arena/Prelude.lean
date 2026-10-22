import ConAgua.Arena.RomCI
import ConAgua.Arena.RomPins
import ConAgua.Rom.CIEnc
import ConAgua.Census.Attr

/-!
# The program's ROM: the pinned names, then the startup walk's item stream

`romData` is the one constant byte string of the checker program (`rom.c8[i]`): the 51 pinned
names and the 16 reserved basis names (`intern_reserved_pins`, offset `0`), then the structured
constants of the ROM stubs (`romCIData`, offset `ciOff`, `ConAgua/Rom/CIEnc.lean`; read by
`rom_ci`, `rom_basis_decls`, …), then the item stream of `internAllPins` (`intern_all_pins`,
offset `allPinsOff`; the variant list follows it in the pin-data buffer). The pin list is free (the final
theorem holds at every pin list, `ConAgua/Final/Twin.lean`); the ROM carries **no** `Nat`-operation
pin variant for now (`[]`): every pinned `Nat.div`-family definition is then declined (a
completeness loss, never a soundness one), until the ROM embeds a variant.
-/

open ConRon.Arena

namespace L.Rom

open L.Arena

/-- The pin variants the program carries. -/
def romPins : List ConLeche.NatOpPinSet := []

/-- The program's ROM. -/
def romData : List UInt8 :=
  encNames pinNames ++ (encNames reservedBasisNameValues ++ (romCIData ++ encItems [] (itemsAllPins romPins)))

/-- Where the structured constants start. -/
def ciOff : Word := UInt64.ofNat (encNames pinNames ++ encNames reservedBasisNameValues).length

/-- Where the startup walk's items start. -/
def allPinsOff : Word :=
  UInt64.ofNat (encNames pinNames ++ encNames reservedBasisNameValues ++ romCIData).length

/-- `intern_all_pins()` as the program has it. -/
-- con-ron: ConRon/Arena/Checker.lean:309-339 ConRon.Arena.internAllPins
@[l_impl ConRon.Arena.internAllPins]
def internAllPinsL : FunDecl := internAllPinsAt allPinsOff

/-- `rom_expr(pos)` as the program has it (the expression ROM reader at the program's ROM). -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:189-251 ConRon.Arena.Frontend.internExprGo
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
theorem allPins_noProj : AllPinsNoProj := by unfold AllPinsNoProj; decide +kernel

set_option maxRecDepth 100000 in
theorem pinNames_fit : pinNames.all nameFits = true ∧ reservedBasisNameValues.all nameFits = true := by
  decide +kernel

end L.Rom

namespace L.Rom
open L.Arena
open Std.WP
open scoped Lean.Order

theorem romData_ok : RomOK romData := romData_len

theorem romData_split : romData =
    (encNames pinNames ++ encNames reservedBasisNameValues ++ romCIData) ++ encItems [] (itemsAllPins romPins) := by
  simp [romData]

theorem allPinsOff_toNat :
    allPinsOff.toNat = (encNames pinNames ++ encNames reservedBasisNameValues ++ romCIData).length := by
  have := romData_len
  simp only [romData, List.length_append] at this
  simp only [allPinsOff, List.length_append, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

/-- **The program's `intern_reserved_pins` refines `internReservedPins`.** -/
theorem internReservedPins_rom (p : Prog) (hL : IrpProg romData 0 p) (n : Nat) (s₀ : St) (a₀ : AState)
    (hA : ArenaD s₀.mem a₀) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_reserved_pins" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok internReservedPins a₀ ∧
      ArenaD s'.mem (AM.st internReservedPins a₀) ∧ PinsFull s'.mem (AM.st internReservedPins a₀).pins ∧
      pinW s'.mem 0 ≠ 0 ∧ MemFrame PinA StoreC s₀.mem s'.mem; ⊤⦄ :=
  internReservedPins_refines romData 0 p hL romData_ok (romCIData ++ encItems [] (itemsAllPins romPins))
    (by simp [romData])
    pinNames_fit.1 pinNames_fit.2
    n s₀ a₀ hA

/-- **The program's `intern_all_pins` refines `internAllPins romPins`'s store effect.** -/
theorem internAllPins_rom (p : Prog) (hL : ItemsProg romData p)
    (hp : p.lookup "intern_all_pins" = some internAllPinsL) (n : Nat) (s₀ : St) (a₀ : AState)
    (hA : ArenaD s₀.mem a₀) (hP : PinsReadyP a₀) (hst : (stkTop s₀.mem).toNat < 2 ^ 61) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_all_pins" []
    ⦃fun _ s' => LocEq s' s₀ ∧ ∃ v a', (internAllPins romPins).run a₀ = .ok (v, a') ∧
      ArenaD s'.mem a' ∧ MemFrame ExprA ExprC s₀.mem s'.mem; ⊤⦄ :=
  internAllPins_refines romData allPinsOff p hL hp romData_ok romPins allPins_noProj allPins_fits []
    (by rw [allPinsOff_toNat, romData_split, List.drop_left]; simp)
    n s₀ a₀ hA hP hst

end L.Rom
