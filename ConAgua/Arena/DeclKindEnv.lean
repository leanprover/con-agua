module

public import ConRon.Arena.CheckDecl
public import ConRon.Arena.Denote
public import ConRon.Bridge.Checker.Inv

@[expose] public section

/-!
# What a declaration's own checks add to the environment (lane `ronsync3`)

`checkDecl`'s reserved names' check runs after `checkDeclKind`, at the environment `fe'` the
kind's check returns. L's side of that check runs under `StageT` at `fe'`, whose `StoreDen`
asks that every entry's level lists read back in the twin's store. `EnvGrowDen st fe fe'`: `fe'`
is `fe` with entries added whose level lists read back in `st`. `IndKindEnv` is that fact for
the inductive arm (`checkBlock`'s install), a twin-level statement proved beside the inductive
stage's bridges; the one-constant arms' is proved in `DeclKindEnvOne.lean`.
-/

namespace L.Arena

open ConRon.Arena

/-- A constant's level parameters, and a recursor's rules' fired levels, read back in `st`. -/
def CiLvlDen (st : EStore) (ci : IConstantInfo) : Prop :=
  (∃ ks, ci.toConstantVal.levelParams.mapM (denoteN st.ns) = some ks) ∧
  ∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules → ∀ r ∈ rules,
    (∀ lvls pins, r.fire = .nested lvls pins → ∀ u ∈ lvls, ∃ L, denoteL st.ls u = some L) ∧
    (∀ lvls, r.fire = .levels lvls → ∀ u ∈ lvls, ∃ L, denoteL st.ls u = some L)

/-- **`fe'` is `fe` with entries added whose level lists read back in `st`** (constants and
projection tables). -/
structure EnvGrowDen (st : EStore) (fe fe' : IFEnv) : Prop where
  find : ∀ c ci, fe'.find? c = some ci → fe.find? c = some ci ∨ CiLvlDen st ci
  tbl : ∀ c t, fe'.findTable? c = some t →
    fe.findTable? c = some t ∨ ∃ ks, t.levelParams.mapM (denoteN st.ns) = some ks

/-- **The inductive arm adds only entries whose level lists read back**: an accepted
`checkDeclKind` on an inductive block, from the twin's fold invariant and the block's
denotation, returns an environment that grows `fe` by `EnvGrowDen` in the final store. -/
def IndKindEnv : Prop :=
  ∀ {env : ConLeche.Env} {mode : ConLeche.CheckMode} {pins : List INatOpPinSet} {fe fe' : IFEnv}
    {block : List IConstantInfo} {nP : Nat} {s s' : AState} {b : List ConLeche.ConstantInfo},
    ConRon.Bridge.FoldOK env fe s → Frontend.denoteCIList s.store block = some b →
    checkDeclKind mode pins fe (.indDecl block nP) s = .ok (fe', s') →
    EnvGrowDen s'.store fe fe'

end L.Arena
