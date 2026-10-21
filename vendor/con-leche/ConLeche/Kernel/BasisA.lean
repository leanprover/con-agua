module

public import ConLeche.Kernel.Basis
public import ConLeche.Kernel.BasisGen

@[expose] public section

/-!
# The stored basis blocks

The pinned basis declarations as the installation stores them,
computed from the raw pins (`ConLeche/Kernel/Basis/*`) while this
module elaborates — see `ConLeche/Kernel/BasisGen.lean` for the command
and the recipe (a recursor's rules carry the install-computed fields;
everything else is the raw pin).  These are the constants the
installation stores (`installBasisDecl`) and the model proofs read.

The blocks are computed in one run, in install order, so a recursor's
rules read the constructor stored before it — exactly the order
`checkDecl` installs them in.

This module sits ABOVE `ConLeche.Kernel.TypeChecker` (the command's
recipe uses the installer's rule-field computations), while
`ConLeche.Kernel.Basis` — the raw pins, all the kernel core needs —
sits below it.  That is the whole reason the two are separate modules.
-/

namespace ConLeche

#stored_basis over []
  | eqA := eqRaw
  | eqReflA := eqReflRaw
  | eqRecA := eqRecRaw
  | natA := natRaw
  | natZeroA := natZeroRaw
  | natSuccA := natSuccRaw
  | natRecA := natRecRaw
  | emptyA := emptyRaw
  | emptyRecA := emptyRecRaw
  | falseA := falseRaw
  | falseRecA := falseRecRaw
  | quotA := quotRaw
  | quotMkA := quotMkRaw
  | quotLiftA := quotLiftRaw
  | quotIndA := quotIndRaw
  | quotSoundA := quotSoundRaw

/-- The stored constants of one basis block, in dependency order. -/
def BasisKind.declsA : BasisKind → List ConstantInfo
  | .eqK => [eqA, eqReflA, eqRecA]
  | .natK => [natA, natZeroA, natSuccA, natRecA]
  | .emptyK => [emptyA, emptyRecA]
  | .falseK => [falseA, falseRecA]
  | .quotK => [quotA, quotMkA, quotLiftA, quotIndA, quotSoundA]

end ConLeche
