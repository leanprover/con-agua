import ConAgua.Arena.DerRel
import ConAgua.Arena.Keeps
import ConRon.Arena.Env

/-!
# The relation by tier, over projections of the state

Lane `scale` found that one flat bundle over `AState` costs more per writer the more fields it
has (faster than linearly), and that a group stated over `AState` gets no twin-side frame by
unfolding. So the relation is a few groups, each over the **projection** of the state it reads,
each owning a disjoint range of arrays and `CTL` words, each with **one** group frame lemma:

| group | over | arrays | `CTL` words | status |
|---|---|---|---|---|
| `ArenaR` (store tier, `ArenaRel.lean`) | `a.store` (19 tables, pool) | `storeArrs` ⊆ 0‥40 | `storeCtl` ⊆ 0‥41 | done |
| `MemosR` (walk memos, nested in `ArenaR`) | `a.memos` | 24, 41, 47, 48; 49‥55 reserved | 24, 25, 42‥47; 48‥61 reserved | 4 of 10 memos |
| `DerR` (derived columns, `DerRel.lean`) | `a.store` | 42‥46 | – | 5 compound tables |
| `StateDR` (front, `Front/StateDR.lean`) | the parse state | 64‥66; 67‥95 reserved | 64‥95 reserved | lane `front2` |
| `CoreR` | `a.caches` | 96‥127 | 96‥127 | stub |
| `PinsR` | `a.pins` | 128‥131 | – | stub |
| `EnvR` | a view `vis` of `fe : IFEnv` (an argument) | 132‥143 | 128‥135 | stub |
| argument relations (`PMemo`, `pend`, saved `ModeMemos`, walk-local memos) | arguments | 144‥191 | 136‥191 | not yet |

`ArenaD = ArenaR ∧ DerR` stays the walks' tier. `CheckR` is the whole relation. A walk changes
only arrays below 64 (`WriteSets.lean`) and only `store`/`memos` (`Keeps cp`, `Keeps.lean`), so
`CheckR.of_walk` carries the upper tiers across it with no lemma about the walk. The stubs have
no fields yet: they claim nothing, and their frame lemmas are already the ones a real relation
over the reserved range will have.
-/

namespace L.Arena

open ConRon.Arena

/-- The words of a range, `lo ≤ x < hi`, apart from a writer. -/
def AvoidA (lo hi : Nat) (A : List ArrId) : Prop := ∀ b ∈ A, b < lo ∨ hi ≤ b
def AvoidC (lo hi : Nat) (C : List Word) : Prop := ∀ x ∈ C, x.toNat < lo ∨ hi ≤ x.toNat

instance (lo hi : Nat) (A : List ArrId) : Decidable (AvoidA lo hi A) := by unfold AvoidA; infer_instance

/-- A writer of arrays and words below `k` avoids every range starting at `k` or above. -/
theorem AvoidA.of_lt {k lo hi : Nat} {A : List ArrId} (hA : ∀ b ∈ A, b < k) (hk : k ≤ lo) :
    AvoidA lo hi A := fun b hb => .inl (Nat.lt_of_lt_of_le (hA b hb) hk)
theorem AvoidC.of_lt {k lo hi : Nat} {C : List Word} (hC : ∀ x ∈ C, x.toNat < k) (hk : k ≤ lo) :
    AvoidC lo hi C := fun x hx => .inl (Nat.lt_of_lt_of_le (hC x hx) hk)

set_option linter.unusedVariables false

/-! ## The per-declaration caches: arrays 96‥127, `CTL` 96‥127 -/

/-- **The core tier** (tier D: `flushCaches` per declaration): the 14 caches of `Caches` as
`MemoRG`s (and the eager-depth banks), over `a.caches`. Stub. -/
structure CoreR (m : Mem) (c : Caches) : Prop

theorem CoreR.frame {A : List ArrId} {C : List Word} {m m' : Mem} {c : Caches}
    (hA : AvoidA 96 128 A) (hC : AvoidC 96 128 C) (hf : MemFrame A C m m') (h : CoreR m c) :
    CoreR m' c := ⟨⟩

/-! ## The pin table: arrays 128‥131 -/

/-- **The pins** (global, filled once by `internAllPins`): a fixed word array, over `a.pins`. Stub. -/
structure PinsR (m : Mem) (p : Pins) : Prop

theorem PinsR.frame {A : List ArrId} {C : List Word} {m m' : Mem} {p : Pins}
    (hA : AvoidA 128 132 A) (hf : MemFrame A C m m') (h : PinsR m p) : PinsR m' p := ⟨⟩

/-! ## The environment: arrays 132‥143, `CTL` 128‥135 -/

/-- **The environment index** seen through a view `vis` (the declarations below the counter
`vis`; several views of one index are live at once), stated through `find?`. `fe` is an argument
of the checker, not part of `AState`, so a walk keeps it trivially. Stub. -/
structure EnvR (m : Mem) (vis : Word) (fe : IFEnv) : Prop

theorem EnvR.frame {A : List ArrId} {C : List Word} {m m' : Mem} {vis : Word} {fe : IFEnv}
    (hA : AvoidA 132 144 A) (hC : AvoidC 128 136 C) (hf : MemFrame A C m m') (h : EnvR m vis fe) :
    EnvR m' vis fe := ⟨⟩

/-! ## The whole relation -/

/-- **The relation, by tier.** -/
structure CheckR (m : Mem) (a : AState) (vis : Word) (fe : IFEnv) : Prop where
  arena : ArenaD m a
  core : CoreR m a.caches
  pins : PinsR m a.pins
  env : EnvR m vis fe

/-- **The upper tiers across a walk**: a run whose L write set is below 64 (every walk,
`WriteSets.lean`) and whose twin side keeps `cp` (every walk, `Keeps.lean`) keeps `CoreR`,
`PinsR` and `EnvR`; the walk's own theorem gives `ArenaD`. -/
theorem CheckR.of_walk {m m' : Mem} {a a' : AState} {vis : Word} {fe : IFEnv} {A : List ArrId}
    {C : List Word} (hR : CheckR m a vis fe) (hD : ArenaD m' a') (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b < 64) (hC : ∀ x ∈ C, x.toNat < 64) (hk : cp a' = cp a) :
    CheckR m' a' vis fe := by
  have hc : a'.caches = a.caches := congrArg Prod.fst hk
  have hp : a'.pins = a.pins := congrArg Prod.snd hk
  refine ⟨hD, ?_, ?_, hR.env.frame (.of_lt hA (by decide)) (.of_lt hC (by decide)) hf⟩
  · rw [hc]; exact hR.core.frame (.of_lt hA (by decide)) (.of_lt hC (by decide)) hf
  · rw [hp]; exact hR.pins.frame (.of_lt hA (by decide)) hf

end L.Arena
