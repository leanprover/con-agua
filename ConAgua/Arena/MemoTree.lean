import ConAgua.Arena.LevelHeapRel
import ConRon.Arena.Handle

/-!
# Tree-valued memo entries: `MemoRV` with a decoder that reads memory

con-ron's `readLC`/`readNC`/`readLsC` caches map a handle to a **tree** (`Level`, `Name`,
`List Level`). In L the value word of such an entry is a pointer, and what it denotes depends on
memory: here a level pointer of lane `levels`' heap (`LevelHeap.lean`: a store handle or a heap
node), decoded by `LvR N m p l`. The memo library's `MemoRV` takes such a value relation; what an
instance proves is that the relation is **stable**:

* under the memo's own writes (`VStable`, for `memoRV_set`/`memoRV_erase`): `lvNodeW` reads none
  of the memo's array or words (`lvNodeW_congr`), so every view stays and `LvR.of_view` applies;
* under the heap's growth (`lh_mk`, `HeapExt` from `lhMkW_ext`), for `memoRV_frame`.

The instance here is a test schema (`ltSch`, array 100, `CTL[100]`, inside the `CoreR` range but
not claimed by `CoreR`); the `readLC` cache proper is `CoreR`'s, when that tier gets its fields.
With lane `levels`' pointers a store handle is a valid level pointer, so `readLC` can store the
handle itself (no copy), and the relation is the same.
-/

open ConRon.Arena

namespace L.Arena

open ConLeche

/-- `LvR` needs only the views (`HeapExt.view`, without `HeapExt`'s frame of the other arrays,
which a memo write breaks). -/
theorem LvR.of_view {N : Word → Name → Prop} {m m' : Mem}
    (hv : ∀ p, lvNodeW m p ≠ [] → lvNodeW m' p = lvNodeW m p) {p : Word} {l : Level}
    (h : LvR N m p l) : LvR N m' p l := by
  induction h with
  | zero h0 => exact .zero (by rw [hv _ (by simp [h0])]; exact h0)
  | succ h0 _ ih => exact .succ (by rw [hv _ (by simp [h0])]; exact h0) ih
  | max h0 _ _ ih1 ih2 => exact .max (by rw [hv _ (by simp [h0])]; exact h0) ih1 ih2
  | imax h0 _ _ ih1 ih2 => exact .imax (by rw [hv _ (by simp [h0])]; exact h0) ih1 ih2
  | param h0 hn => exact .param (by rw [hv _ (by simp [h0])]; exact h0) hn

/-! ## A test instance: a level-valued memo keyed by level handles -/

end L.Arena
