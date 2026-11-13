module

public import ConRon.Arena.Core

@[expose] public section

/-!
# TEMPORARY compile shim (lane ronsync4, stage 3a): the removed `natOpResult` and `natBinOpName`

con-ron's #556 P-N replaced the name dispatch `natOpResult` by `natBinOpOfName?` and
`natBinOpResult`. Until the `Nat` area is ported, the old function (con-ron 4ca283d1, verbatim) keeps
the modules that state facts about it compiling. The `Nat` port deletes this file.
-/

namespace ConRon.Arena

open ConLeche

/-- TEMPORARY: con-ron 4ca283d1's `natOpResult` (removed upstream). -/
def natOpResult (c : NIdx) (a b : Nat) : AM (Option EIdx) := do
  let pr ← natPredName; let ad ← natAddName; let su ← natSubName
  let mu ← natMulName; let po ← natPowName; let be ← natBeqName
  let bl ← natBleName; let di ← natDivName; let mo ← natModName
  let gc ← natGcdName; let la ← natLandName; let lo ← natLorName
  let xo ← natXorName; let sl ← natShiftLeftName; let sr ← natShiftRightName
  if c == pr then do let x ← internE (.lit (.natVal (a - 1))); pure (some x)
  else if c == ad then litNatSized (a + b)
  else if c == su then litNatSized (a - b)
  else if c == mu then litNatSized (a * b)
  else if c == po then do
    powGuard a b
    let x ← internE (.lit (.natVal (a ^ b))); pure (some x)
  else if c == di then do let x ← internE (.lit (.natVal (a / b))); pure (some x)
  else if c == mo then do let x ← internE (.lit (.natVal (a % b))); pure (some x)
  else if c == gc then do
    let x ← internE (.lit (.natVal (Nat.gcd a b))); pure (some x)
  else if c == la then do
    let x ← internE (.lit (.natVal (Nat.land a b))); pure (some x)
  else if c == lo then do
    let x ← internE (.lit (.natVal (Nat.lor a b))); pure (some x)
  else if c == xo then do
    let x ← internE (.lit (.natVal (Nat.xor a b))); pure (some x)
  else if c == sl then do
    shiftLeftGuard a b
    let x ← internE (.lit (.natVal (Nat.shiftLeft a b))); pure (some x)
  else if c == sr then do
    let x ← internE (.lit (.natVal (Nat.shiftRight a b))); pure (some x)
  else if c == be then do
    let n ← if a = b then boolTrueName else boolFalseName
    let x ← constE n
    pure (some x)
  else if c == bl then do
    let n ← if a <= b then boolTrueName else boolFalseName
    let x ← constE n
    pure (some x)
  else pure none

/-- TEMPORARY: con-ron 4ca283d1's `natBinOpName` (removed upstream). -/
def natBinOpName (c : NIdx) : AM Bool := do
  let ad ← natAddName; let su ← natSubName; let mu ← natMulName
  let po ← natPowName; let be ← natBeqName; let bl ← natBleName
  let di ← natDivName; let mo ← natModName; let gc ← natGcdName
  let la ← natLandName; let lo ← natLorName; let xo ← natXorName
  let sl ← natShiftLeftName; let sr ← natShiftRightName
  pure (c == ad || c == su || c == mu || c == po || c == be || c == bl ||
    c == di || c == mo || c == gc || c == la || c == lo || c == xo ||
    c == sl || c == sr)

end ConRon.Arena
