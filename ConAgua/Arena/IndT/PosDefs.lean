import ConRon.Bridge.Inductives.Positivity

/-!
# The positivity walk under `StageC`: the constructors' shared preconditions

`CtorsPre`: the twin-side facts every constructor walk of a frame shares (con-ron's
`nestCtors_spec`'s preconditions). The block's refinements are stated in `Verdict/PosE.lean`.
-/


open ConRon.Arena

namespace L.Ind

/-- The twin-side facts every constructor walk of a frame shares (con-ron's `nestCtors_spec`'s). -/
structure CtorsPre (st : EStore) (us : LsIdx) (ds : List EIdx) (names : List NIdx) (holes : List EIdx)
    (hi : Nat) (usP : List ConLeche.Level) (dsP : List ConLeche.Expr) (namesP : List ConLeche.Name)
    (holesP : List ConLeche.Expr) : Prop where
  hus : denoteLs st.lss us = some usP
  hds : Frontend.denoteEList st ds = some dsP
  hnames : Frontend.denoteNList st.ns names = some namesP
  hholes : Frontend.denoteEList st holes = some holesP
  wds : ∀ d ∈ dsP, ConLeche.Expr.WScoped hi d
  wholes : ∀ x ∈ holesP, ConLeche.Expr.WScoped hi x
  hlen : namesP.length ≤ holesP.length


end L.Ind
