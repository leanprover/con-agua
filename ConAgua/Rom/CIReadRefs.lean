import ConAgua.Rom.CIReadRefData

/-!
# The ROM constant readers refine the twin (helper `decls4-rom`)

The six entries of `CIRead.lean` against `CIReadSpec.lean`'s statements: `rom_ci`, `rom_cv`,
`rom_expr_pin`, `rom_and_pin`, and `rom_basis_decls`/`rom_basis_decls_a` for the four kinds
`basisPinHit` tries (`eqK`, `natK`, `emptyK`, `falseK`). The quotient kind (`4`) is open: its block
holds `Quot`, whose `sortZ` is `.ifAllZero [u]`, and `decCaps` reads the name `u` back through
`dn`, which `StageR` does not relate to the store (`CIReadRefCaps.lean`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-! ## The region's entries and the twin's values, by index -/

theorem ciEntries_ci (i : Nat) (hi : i < 8) :
    ciEntries[10 + i]'(by rw [ciEntries_len]; omega) = (encCI [] (romCiVals[i]'(by simp [romCiVals]; omega))).1 := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | _ + 8, h => exact absurd h (by omega)

theorem ciEntries_cv (i : Nat) (hi : i < 10) :
    ciEntries[18 + i]'(by rw [ciEntries_len]; omega) = (encCV [] (romCvVals[i]'(by simp [romCvVals]; omega))).1 := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | _ + 10, h => exact absurd h (by omega)

theorem ciEntries_ex (i : Nat) (hi : i < 2) :
    ciEntries[28 + i]'(by rw [ciEntries_len]; omega) =
      (encExprM [] (romExprVals[i]'(by simp [romExprVals]; omega))).1 := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | _ + 2, h => exact absurd h (by omega)

theorem ciEntries_b (i : Nat) (hi : i < 5) :
    ciEntries[i]'(by rw [ciEntries_len]; omega) =
      encBlock (ConLeche.BasisKind.decls (basisKinds[i]'(by simp [basisKinds]; omega))) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | _ + 5, h => exact absurd h (by omega)

theorem ciEntries_bA (i : Nat) (hi : i < 5) :
    ciEntries[5 + i]'(by rw [ciEntries_len]; omega) =
      encBlock (ConLeche.BasisKind.declsA (basisKinds[i]'(by simp [basisKinds]; omega))) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | _ + 5, h => exact absurd h (by omega)

theorem ciEntries_and : ciEntries[30]'(by rw [ciEntries_len]; omega) = encBlock ConLeche.andPin := rfl

theorem romCiT_eq (i : Nat) (hi : i < 8) :
    romCiT i = ConRon.Arena.internCI (romCiVals[i]'(by simp [romCiVals]; omega)) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | _ + 8, h => exact absurd h (by omega)

theorem romCvT_eq (i : Nat) (hi : i < 10) :
    romCvT i = ConRon.Arena.internCV (romCvVals[i]'(by simp [romCvVals]; omega)) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | _ + 10, h => exact absurd h (by omega)

theorem romExprT_eq (i : Nat) (hi : i < 2) :
    romExprT i = ConRon.Arena.internExpr (romExprVals[i]'(by simp [romExprVals]; omega)) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | _ + 2, h => exact absurd h (by omega)

theorem basisOfW_eq (i : Nat) (hi : i < 5) : basisOfW i = basisKinds[i]'(by simp [basisKinds]; omega) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | _ + 5, h => exact absurd h (by omega)

theorem word_add_toNat (c : Nat) (w : Word) (h : c + w.toNat < 2 ^ 64) :
    (UInt64.ofNat c + w).toNat = c + w.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']; simp; omega

end L.Rom
