import ConAgua.Rom.CIReadRefLayout

/-!
# The ROM constant readers: the pinned values fit (helper `decls4-rom`)

Every constant, constant value and expression of the structured region fits its encoding and is
of a kind the readers handle (`ciFits`), except the quotient blocks: `Quot`'s `sortZ` is
`.ifAllZero [u]` (see `CIReadRefCaps.lean`). Kernel evaluation, seconds.
-/

namespace L.Rom

set_option maxRecDepth 100000 in
theorem romCiVals_fit : romCiVals.all ciFits = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem romCvVals_fit : romCvVals.all cvFits = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem romExprVals_fit : romExprVals.all exprFits = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem basisDecls_fit :
    ((basisKinds.take 4).map fun k => (ConLeche.BasisKind.decls k).all ciFits) = [true, true, true, true] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem basisDeclsA_fit :
    ((basisKinds.take 4).map fun k => (ConLeche.BasisKind.declsA k).all ciFits) = [true, true, true, true] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem andPin_fit : ConLeche.andPin.all ciFits = true := by decide +kernel

end L.Rom
