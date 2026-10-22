import ConAgua.Arena.DeclAndPinIndCopy2
import ConAgua.Arena.DeclCanonInfo
import ConAgua.Arena.DeclArmQuot
import ConAgua.Rom.CIReadSpec

/-!
# The `And` pin's inductive arm, part 3: `and_pin_ok(i)` refines `andPinOk (.indDecl block nP)`

`and_pin_ok`'s whole model (`apW`): the flag; for kind `6` the name test over the block
(`and_block_named`, `abnW_eq`), the parameter count, then the block copied (`ind_block_to_erec`,
`indBlockToErec_ok`; `er_to_iw`) and compared with the ROM's pinned `And` block (`rom_and_pin`,
a hypothesis: `RomAndPinRef`, helper `decls4-rom`) by `canon_eq_list` (`canonEqList_refines`,
which compares literals by handle: `LitInj`, from the twin state's `StateOK`). The one-constant
kinds are `andPinW` (`DeclAndPin.lean`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Front (DECL DLP trunc decCIs IndDeclAt dw)
open L.Ind (erTop iwTop StageR IWGrow decW0B erToIwW erToIw iwAlloc erCopy)

/-! ## The model -/

section model
variable (p : Prog)

/-- After the comparison. -/
def apK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => some ([r4.headD 0], m4)

/-- After `rom_and_pin`. -/
def apK3 (n : Nat) (r2 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => apK4 (callW p n "canon_eq_list"
      [r2.headD 0, r2.tail.headD 0, r3.headD 0, r3.tail.headD 0] m3)

/-- After `er_to_iw`. -/
def apK2 (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => apK3 p n r2 (callW p n "rom_and_pin" [] m2)

/-- After `ind_block_to_erec`. -/
def apK1 (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => apK2 p n (callW p n "er_to_iw" [r1.headD 0, r1.tail.headD 0] m1)

/-- **The model of `and_pin_ok(i)`**, every record kind. -/
def apW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, i =>
    if rdW (m.arr64 PINS) 0 = 0 then none
    else if rdW (m.arr64 DECL) (1 + 8 * i) = 6 then
      if abnW m (rdW (m.arr64 DECL) (3 + 8 * i)) (rdW (m.arr64 DECL) (4 + 8 * i)).toNat = 0 then
        some ([1], m)
      else if rdW (m.arr64 DECL) (5 + 8 * i) ≠ 2 then some ([0], m)
      else apK1 p n (callW p n "ind_block_to_erec" [i] m)
    else some ([andPinW m i], m)

section arms
variable (n : Nat) (m m1 m2 m3 m4 : Mem) (i : Word) (r1 r2 r3 r4 : List Word)
theorem apK1_some : apK1 p n (some (r1, m1)) =
    apK2 p n (callW p n "er_to_iw" [r1.headD 0, r1.tail.headD 0] m1) := rfl
theorem apK2_some : apK2 p n (some (r2, m2)) = apK3 p n r2 (callW p n "rom_and_pin" [] m2) := rfl
theorem apK3_some : apK3 p n r2 (some (r3, m3)) = apK4 (callW p n "canon_eq_list"
    [r2.headD 0, r2.tail.headD 0, r3.headD 0, r3.tail.headD 0] m3) := rfl
theorem apK4_some : apK4 (some (r4, m4)) = some ([r4.headD 0], m4) := rfl
theorem apW_step : apW p (n + 1) m i =
    if rdW (m.arr64 PINS) 0 = 0 then none
    else if rdW (m.arr64 DECL) (1 + 8 * i) = 6 then
      if abnW m (rdW (m.arr64 DECL) (3 + 8 * i)) (rdW (m.arr64 DECL) (4 + 8 * i)).toNat = 0 then
        some ([1], m)
      else if rdW (m.arr64 DECL) (5 + 8 * i) ≠ 2 then some ([0], m)
      else apK1 p n (callW p n "ind_block_to_erec" [i] m)
    else some ([andPinW m i], m) := rfl
end arms

grind_pattern [ind_grind] apK1_some => apK1 p n (some (r1, m1))
grind_pattern [ind_grind] apK2_some => apK2 p n (some (r2, m2))
grind_pattern [ind_grind] apK3_some => apK3 p n r2 (some (r3, m3))
grind_pattern [ind_grind] apK4_some => apK4 (some (r4, m4))
grind_pattern [ind_grind] apW_step => apW p (n + 1) m i

theorem andPinOk_specA (hp : p.lookup "and_pin_ok" = some andPinOkL)
    (hab : p.lookup "and_block_named" = some andBlockNamed) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "and_pin_ok" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ apW p n s₀.mem i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, andPinOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        andBlockNamed_specW p hab n,
        callW_spec p n "ind_block_to_erec", callW_spec p n "er_to_iw", callW_spec p n "rom_and_pin",
        callW_spec p n "canon_eq_list"] <;>
      finish (gen := 20) [andPinW, lo32, rdW_eq]

end model

end L.Arena
