import ConAgua.Arena.EnvRec
import ConAgua.Arena.Tiers
import ConRon.Arena.Core

/-!
# Stored levels read back: the invariant the knot's level readers need (lane `defeq2`)

The twin compares and substitutes levels on their **readbacks** (`readLevelM`, `readLevelsM`,
`readNamesM`, `denoteL`/`denoteLs`/`denoteN`), and a readback of a dangling handle fails. L works
on the handles themselves and never reads back (deviation D13), so an L run that succeeds refines
the twin's only where the handles L compares do read back. Which handles those are:

* a `sort` node's level (`quick_sort`, `proof_irrel`, `PropRead`'s `residualPW`);
* a `const` node's level list (`spine_cmp`, `struct_eta_cert_tail`, `PropRead`'s `substPWAt`);
* the pinned zero level (`proof_irrel`, `infer_proj`);
* the names in the twin's name readback cache (`readNC`: `readNameM` answers a hit unchecked;
  `field_sort_zero`, `PropRead`);
* a projection table's structure sort, its fields' sorts and its level parameters
  (`infer_proj`), read from the table records in `EREC` (`decTbl`).

`StoreDen m a` states all five. **It is meant as one field of `CoreS`** (`CoreS.den`, the twin's
store being well formed: `StoreWF` gives the first four, the environment loader the fifth);
until that field exists the knot takes `CoreDen` (`DefEqKnot.lean`) as a hypothesis.

Maintenance, when it is a field: the twin's store only grows inside the core (`Ext`), so an old
handle keeps its readback; the two clauses over node views need a proof only where a `sort` or a
`const` node is interned (its level or list came from a node that reads back, or was built from
ones that do); `zero` and `proj` follow from `Ext` and from `EREC` being kept; `readN` where the
name cache is written (`readNameM`, which caches a readback).
-/

open ConRon.Arena

namespace L.Arena

/-- **Stored levels read back** (see the module note). -/
structure StoreDen (m : Mem) (a : AState) : Prop where
  sort : ∀ (h : EIdx) (u : LIdx), a.store.view h = some (.sort u) →
    ∃ l, denoteL a.store.ls u = some l
  constLs : ∀ (h : EIdx) (c : NIdx) (us : LsIdx), a.store.view h = some (.const c us) →
    ∃ ls, denoteLs a.store.lss us = some ls
  zero : ∃ l, denoteL a.store.ls a.pins.zeroLevel = some l
  readN : ∀ (h : NIdx) (x : ConLeche.Name), a.caches.readNC[h]? = some x →
    denoteN a.store.ns h = some x
  /-- A projection table record's levels read back. -/
  proj : ∀ (q : Nat) (tbl : IProjTable), decTbl (m.arr64 EREC) q = some tbl →
    (∃ l, denoteL a.store.ls tbl.structSort = some l) ∧
    (∀ i, i < tbl.numFields → ∃ l, denoteL a.store.ls (tbl.guards.getD i default) = some l) ∧
    (∃ ks, tbl.levelParams.mapM (denoteN a.store.ns) = some ks)

end L.Arena
