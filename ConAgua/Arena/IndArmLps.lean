module

public import ConRon.Arena.Env

@[expose] public section

/-!
# The block's level-parameter handles have decoder names (lane `indproofs4`)

What the inductive arm takes of the stage's name decoder `dn` beyond `DnInj`: every
level-parameter handle of the block's type formers has a `dn` name (`BlockLpsDn`), what the
block's check (`BlockRefS`) reads the formers' levels with. The loop discharges it where `dn` is the start store's persistent
`denoteN` (the record's denotation names every handle; the front's handles are persistent).
-/

open ConRon.Arena

namespace L.Ind

/-- Every level-parameter handle of the block's type formers has a `dn` name. -/
def BlockLpsDn (dn : NIdx → Option ConLeche.Name) (block : List IConstantInfo) : Prop :=
  ∀ (cv : IConstantVal) (caps : IIndCaps), IConstantInfo.indInfo cv caps ∈ block →
    ∀ k ∈ cv.levelParams, (dn k).isSome

end L.Ind
