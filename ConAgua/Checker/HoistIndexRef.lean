import ConAgua.Checker.HoistRefBase

/-!
# The hoist's name index refines `nameIndex` (lane `front4`)

`hoist_index_go` (each position's names `hoist_ins`-ed into the memo `HNIX`, the first position
declaring a name winning) against `nameIndex ds idx k` (`insertNames`), and `hoist_ix` against the
map's lookup.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-- **`hoist_ix` is the lookup**: the position `+ 1`, or `0`. -/
theorem hoistIx_ok (m m' : Mem) (w r : Word) (idx : Std.HashMap NIdx Nat) (hR : NixR m idx)
    (hw : w.toNat < 2 ^ 32) (h : hIxW m w = some (r, m')) :
    m' = m ∧ r = tgW idx[(decI w : NIdx)]? := by
  sorry

/-- **`hoist_index_go` builds `nameIndex`** from position `k` on (the stream `ds` in the order
`ord`, below `2 ^ 60` records). -/
theorem hoistIndexGo_ok (n : Nat) (m m' : Mem) (ord c k r : Word) (ds : Array IDeclaration)
    (idx : Std.HashMap NIdx Nat) (hO : OrdR m ord ds) (hc : ds.size = c.toNat)
    (hc60 : c.toNat < 2 ^ 60) (hord : ord.toNat + c.toNat < 2 ^ 64) (hk : k ≤ c)
    (hR : NixR m idx) (h : hIndexGoW n m ord c k = some (r, m')) :
    NixR m' (nameIndex ds idx k.toNat) ∧ MemFrame [HNIX] [75, 76] m m' := by
  sorry

/-- The name index's positions are positions of the stream. -/
theorem nameIndex_lt (ds : Array IDeclaration) (idx : Std.HashMap NIdx Nat) (k : Nat)
    (h : ∀ (n : NIdx) (j : Nat), idx[n]? = some j → j < ds.size) :
    ∀ (n : NIdx) (j : Nat), (nameIndex ds idx k)[n]? = some j → j < ds.size := by
  sorry

end L.Checker
