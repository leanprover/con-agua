import ConAgua.Checker.Prelude
import ConAgua.Checker.HoistRef

/-!
# `prepare_prelude`'s leaves: `decl_declares`, `decl_key`, `prep_find` (lane `front4`)

Against `declares`, `preludeKey` and the `findIdx` of `pick`, over the records of `DECL`
(`DeclAtF`, with `RecOK`).
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-- What the prepare stage's other passes keep: the arrays and `CTL` words from `64` on (the
records, the pool, the pins, the hoist's memos), every array's size. -/
def HighFr (m m' : Mem) : Prop :=
  (∀ b : ArrId, 64 ≤ b → m'.arr64 b = m.arr64 b) ∧
    (∀ x : Word, 64 ≤ x.toNat → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x) ∧
    (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧ m'.words.size = m.words.size

/-- **`decl_declares(i, w)` is `declares (decI w) d`** for the record `i` representing `d`. -/
theorem pDecl_ok (n : Nat) (m : Mem) (i w r : Word) (d : IDeclaration)
    (hD : DeclAtF (m.arr64 DECL) (m.arr64 DLP) i.toNat d) (hok : RecOK (m.arr64 DECL) (m.arr64 DLP) i.toNat)
    (hi : i.toNat < 2 ^ 59) (hw : w.toNat < 2 ^ 32) (h : pDeclW n m i w = some r) :
    (r ≠ 0 ↔ declares (decI w) d = true) := by
  sorry

/-- **`decl_key(i)` is `preludeKey d`**: the key word (below `2 ^ 32`), the twin's state after
(interning the anonymous name for an empty block), the store relation; nothing from array and
`CTL` word `64` on changes, and the pins stay. -/
theorem pKey_ok (m m' : Mem) (a : AState) (i r : Word) (d : IDeclaration)
    (hD : DeclAtF (m.arr64 DECL) (m.arr64 DLP) i.toNat d) (hok : RecOK (m.arr64 DECL) (m.arr64 DLP) i.toNat)
    (hi : i.toNat < 2 ^ 59) (hA : ArenaR m a) (h : pKeyW m i = some (r, m')) :
    ∃ a', (preludeKey d).run a = .ok (decI r, a') ∧ r.toNat < 2 ^ 32 ∧ ArenaR m' a' ∧
      HighFr m m' ∧ a'.pins = a.pins := by
  sorry

/-- **`prep_find(mk, n, w, j)`** is the first record `x ∈ [j, n)` with `IW[mk + x] = 0` that
declares `decI w`, plus one; `0` when there is none. -/
theorem pFind_ok (n : Nat) (m : Mem) (dsAll : Array IDeclaration) (mk nw w j r : Word)
    (hD : ∀ x (h : x < dsAll.size), DeclAtF (m.arr64 DECL) (m.arr64 DLP) x dsAll[x] ∧
      RecOK (m.arr64 DECL) (m.arr64 DLP) x)
    (hn : nw.toNat = dsAll.size) (hn59 : nw.toNat < 2 ^ 59) (hmk : mk.toNat + nw.toNat < 2 ^ 64)
    (hw : w.toNat < 2 ^ 32) (h : pFindW n m mk nw w j = some r) :
    (r = 0 → ∀ x (hx : x < dsAll.size), j.toNat ≤ x → rdW (m.arr64 IW) (mk + UInt64.ofNat x) = 0 →
      declares (decI w) dsAll[x] = false) ∧
    (r ≠ 0 → ∃ hx : r.toNat - 1 < dsAll.size, j.toNat ≤ r.toNat - 1 ∧
      rdW (m.arr64 IW) (mk + UInt64.ofNat (r.toNat - 1)) = 0 ∧ declares (decI w) dsAll[r.toNat - 1] = true ∧
      ∀ x (hx : x < dsAll.size), j.toNat ≤ x → x < r.toNat - 1 →
        rdW (m.arr64 IW) (mk + UInt64.ofNat x) = 0 → declares (decI w) dsAll[x] = false) := by
  sorry

end L.Checker
