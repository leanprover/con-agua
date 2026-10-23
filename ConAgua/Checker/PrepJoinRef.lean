import ConAgua.Checker.PrepLeafRef

/-!
# `prelude_join` (lane `front4`)

`DECL` := the prelude's records (`PDECL`, `np` of them), then the stream's (`DECL`'s `ns`): the
stream's records shifted up by `np` (the last first), `PDECL`'s copied below them, the count
`np + ns`.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-- **`prelude_join`**: returns `np = PDECL[0]`; record `r < np` of `DECL` after is record `r` of
`PDECL`, record `np + r` (`r < ns`) is record `r` of `DECL` before; `DECL[0] = np + ns`; only
`DECL` changes, and it keeps its size. -/
theorem pPJoin_ok (n : Nat) (m m' : Mem) (np : Word) (h : pPJoinW n m = some (np, m')) :
    np = rdW (m.arr64 PDECL) 0 ∧ np.toNat < 2 ^ 59 ∧ (rdW (m.arr64 DECL) 0).toNat < 2 ^ 59 ∧
    1 + 8 * (np.toNat + (rdW (m.arr64 DECL) 0).toNat) ≤ (m.arr64 DECL).size ∧
    (∀ r < np.toNat, ∀ k < 8, dw (m'.arr64 DECL) r k = dw (m.arr64 PDECL) r k) ∧
    (∀ r < (rdW (m.arr64 DECL) 0).toNat, ∀ k < 8,
      dw (m'.arr64 DECL) (np.toNat + r) k = dw (m.arr64 DECL) r k) ∧
    (rdW (m'.arr64 DECL) 0).toNat = np.toNat + (rdW (m.arr64 DECL) 0).toNat ∧
    MemFrame [DECL] [] m m' := by
  sorry

end L.Checker
