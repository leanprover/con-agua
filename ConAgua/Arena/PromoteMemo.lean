import ConRon.Arena.Promote
import ConAgua.Arena.Promote

/-!
# The promotion memo's relation `PMemoR`

The twin's `PMemo` (four `HashMap`s, handle → handle) is the four memos of `Promote.lean`
(`pnSch`, `plSch`, `plsSch`, `peSch`: arrays 146‥149, `CTL` 140‥147): keys one handle word,
values persistent handle words.
-/

open ConRon.Arena

namespace L.Arena

/-! ## The promotion memo: four memos of the library (`Promote.lean`) -/

/-- A promotion memo's keys: one handle word (below `2^32`), the second key word `0`. -/
def hKey (k : IdxKind) : MemoKey (Idx k) where
  dk k1 _ := decI k1
  ek x := (x.word.toUInt64, 0)
  ok k1 k2 := k1.toNat < 2 ^ 32 ∧ k2 = 0
  ek_dk k1 k2 h := by
    have e : (decI k1 : Idx k).word.toUInt64 = k1 := (word_decI _ k1 h.1).mpr rfl
    simp only [e, h.2]
  ok_tomb k1 k2 h e := by subst e; exact absurd h.1 (by decide)

/-- A promotion memo's values: a handle word below `2^32` of the **persistent** tier (every
promoted handle is persistent), denoting the entry. Independent of the memory. -/
def VP (k : IdxKind) (_ : Mem) (w : Word) (v : Idx k) : Prop :=
  v = decI w ∧ w.toNat < 2 ^ 32 ∧ tierW w = 0

/-- **The promotion memo** (an argument relation, arrays 146‥149, `CTL` 140‥147): the twin's four
`PMemo` maps are the four memos. -/
structure PMemoR (m : Mem) (pm : PMemo) : Prop where
  n : MemoRV pnSch (hKey .name) (VP .name) m pm.nM
  l : MemoRV plSch (hKey .level) (VP .level) m pm.lM
  ls : MemoRV plsSch (hKey .levels) (VP .levels) m pm.lsM
  e : MemoRV peSch (hKey .expr) (VP .expr) m pm.eM

/-- **The promotion memo's frame**: a writer of other arrays and other `CTL` words keeps it. -/
theorem PMemoR.frame {A : List ArrId} {C : List Word} {m m' : Mem} {pm : PMemo}
    (hA : ∀ b ∈ A, b < 146 ∨ 149 < b) (hC : ∀ x ∈ C, x.toNat < 140 ∨ 147 < x.toNat)
    (hf : MemFrame A C m m') (h : PMemoR m pm) : PMemoR m' pm :=
  ⟨memoRV_frame pnSch ⟨by decide, by decide⟩ _ _ A C (fun h => by have := hA _ h; revert this; decide)
      (fun h => by have := hC _ h; simp at this) m m' hf (fun _ _ h => h) _ h.n,
    memoRV_frame plSch ⟨by decide, by decide⟩ _ _ A C (fun h => by have := hA _ h; revert this; decide)
      (fun h => by have := hC _ h; simp at this) m m' hf (fun _ _ h => h) _ h.l,
    memoRV_frame plsSch ⟨by decide, by decide⟩ _ _ A C (fun h => by have := hA _ h; revert this; decide)
      (fun h => by have := hC _ h; simp at this) m m' hf (fun _ _ h => h) _ h.ls,
    memoRV_frame peSch ⟨by decide, by decide⟩ _ _ A C (fun h => by have := hA _ h; revert this; decide)
      (fun h => by have := hC _ h; simp at this) m m' hf (fun _ _ h => h) _ h.e⟩

end L.Arena
