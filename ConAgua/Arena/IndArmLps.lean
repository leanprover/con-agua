import ConRon.Arena.Env

/-!
# The block's level-parameter handles have decoder names (lane `indproofs4`)

What the inductive arm takes of the stage's name decoder `dn` beyond `DnInj`: every
level-parameter handle of the block's type formers has a `dn` name (`BlockLpsDn`), so the
universe zero-ness facts the block's sorts read back are stated in `dn`'s names (`SortDn`,
`IndRealSortDn.lean`). The loop discharges it where `dn` is the start store's persistent
`denoteN` (the record's denotation names every handle; the front's handles are persistent).
-/

open ConRon.Arena

namespace L.Ind

/-- Every level-parameter handle of the block's type formers has a `dn` name. -/
def BlockLpsDn (dn : NIdx → Option ConLeche.Name) (block : List IConstantInfo) : Prop :=
  ∀ (cv : IConstantVal) (caps : IIndCaps), IConstantInfo.indInfo cv caps ∈ block →
    ∀ k ∈ cv.levelParams, (dn k).isSome

end L.Ind
