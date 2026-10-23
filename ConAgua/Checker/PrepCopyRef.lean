import ConAgua.Checker.PrepLeafRef

/-!
# `prepare_prelude`'s rewrite of `DECL` (lane `front4`)

`prep_copy` copies the records `ord[0 ‥ c)` (eight words each) to the slice `t`, `prep_back` copies
the slice back to `DECL[1 ..]`: record `i` of `DECL` after is record `ord[i]` before.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-- **The rewrite**: after `prep_copy` and `prep_back`, the eight words of record `i < c` are
those of record `ord[i]` before; nothing else but `IW[t ‥ t + 8 c)` and `DECL[1 ‥ 1 + 8 c)`
changes. -/
theorem pCopyBack_ok (fuel₁ fuel₂ : Nat) (m m₁ m₂ : Mem) (ord c t z₁ z₂ : Word)
    (hrec : ∀ i < c.toNat, (rdW (m.arr64 IW) (ord + UInt64.ofNat i)).toNat < 2 ^ 59 ∧
      1 + 8 * (rdW (m.arr64 IW) (ord + UInt64.ofNat i)).toNat + 8 ≤ (m.arr64 DECL).size)
    (hc : 1 + 8 * c.toNat ≤ (m.arr64 DECL).size) (hc59 : c.toNat < 2 ^ 59)
    (hord : ord.toNat + c.toNat ≤ t.toNat) (ht : t.toNat + 8 * c.toNat ≤ (m.arr64 IW).size)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hDsz : (m.arr64 DECL).size < 2 ^ 64)
    (h₁ : pCopyW fuel₁ m ord c t 0 = some (z₁, m₁)) (h₂ : pBackW fuel₂ m₁ t c 0 = some (z₂, m₂)) :
    (∀ i < c.toNat, ∀ k < 8,
      dw (m₂.arr64 DECL) i k = dw (m.arr64 DECL) (rdW (m.arr64 IW) (ord + UInt64.ofNat i)).toNat k) ∧
    MemFrame [IW, DECL] [] m m₂ ∧
    (m₂.arr64 DECL)[0]? = (m.arr64 DECL)[0]? ∧
    (∀ x : Nat, (x < 1 ∨ 1 + 8 * c.toNat ≤ x) → (m₂.arr64 DECL)[x]? = (m.arr64 DECL)[x]?) ∧
    ∀ x : Nat, (x < t.toNat ∨ t.toNat + 8 * c.toNat ≤ x) → (m₂.arr64 IW)[x]? = (m.arr64 IW)[x]? := by
  sorry

end L.Checker
