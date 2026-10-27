import ConAgua.Rom.CIReadRefLayout
import ConAgua.Rom.CIReadRefBlock

/-!
# The ROM constant readers: the pinned values fit (helper `decls4-rom`)

Every constant, constant value and expression of the structured region fits its encoding and is
of a kind the readers handle (`ciFits`). No constant has `sortZ` names (`ciZ`, `blkZ`) but the
quotient blocks' `Quot`, whose `sortZ` is `.ifAllZero [u]` (`quotNames`, see `CIReadRefCaps.lean`).
Kernel evaluation, seconds.
-/

namespace L.Rom

set_option maxRecDepth 100000 in
theorem romCiVals_fit : romCiVals.all (fun c => ciFits c && (ciZ c).isEmpty) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem romCvVals_fit : romCvVals.all cvFits = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem romExprVals_fit : romExprVals.all exprFits = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem basisDecls_fit : ∀ (i : Nat) (hi : i < 4),
    (ConLeche.BasisKind.decls (basisKinds[i]'(by simp [basisKinds]; omega))).all ciFits = true ∧
      (ConLeche.BasisKind.decls (basisKinds[i]'(by simp [basisKinds]; omega))).length < 2 ^ 63 ∧
      blkZ (ConLeche.BasisKind.decls (basisKinds[i]'(by simp [basisKinds]; omega))) = []
  | 0, _ => by decide +kernel +revert
  | 1, _ => by decide +kernel +revert
  | 2, _ => by decide +kernel +revert
  | 3, _ => by decide +kernel +revert
  | _ + 4, h => absurd h (by omega)

set_option maxRecDepth 100000 in
theorem basisDeclsA_fit : ∀ (i : Nat) (hi : i < 4),
    (ConLeche.BasisKind.declsA (basisKinds[i]'(by simp [basisKinds]; omega))).all ciFits = true ∧
      (ConLeche.BasisKind.declsA (basisKinds[i]'(by simp [basisKinds]; omega))).length < 2 ^ 63 ∧
      blkZ (ConLeche.BasisKind.declsA (basisKinds[i]'(by simp [basisKinds]; omega))) = []
  | 0, _ => by decide +kernel +revert
  | 1, _ => by decide +kernel +revert
  | 2, _ => by decide +kernel +revert
  | 3, _ => by decide +kernel +revert
  | _ + 4, h => absurd h (by omega)

set_option maxRecDepth 100000 in
theorem andPin_fit : ConLeche.andPin.all ciFits = true ∧ ConLeche.andPin.length < 2 ^ 63 ∧
    blkZ ConLeche.andPin = [] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The raw quotient block fits; its `sortZ` names are `quotNames`. -/
theorem basisDeclsQ_fit : (ConLeche.BasisKind.decls .quotK).all ciFits = true ∧
    (ConLeche.BasisKind.decls .quotK).length < 2 ^ 63 ∧ blkZ (ConLeche.BasisKind.decls .quotK) = quotNames := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The annotated quotient block fits; its `sortZ` names are `quotNames`. -/
theorem basisDeclsAQ_fit : (ConLeche.BasisKind.declsA .quotK).all ciFits = true ∧
    (ConLeche.BasisKind.declsA .quotK).length < 2 ^ 63 ∧ blkZ (ConLeche.BasisKind.declsA .quotK) = quotNames := by
  decide +kernel

end L.Rom
