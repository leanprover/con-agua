import ConAgua.Arena.MemoBank
import ConAgua.Arena.LevelHeapRel

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

/-- **What `lvNodeW` reads**: the heap and the four level record arrays, the scratch flag, the
level counts (`CTL` words below 16) and the heap top. -/
theorem lvNodeW_congr (m m' : Mem)
    (ha : ∀ A, A = LH ∨ A = SREC ∨ A = MREC ∨ A = IREC ∨ A = PREC → m'.arr64 A = m.arr64 A)
    (hc : ∀ k : Word, k.toNat < 16 ∨ k = 192 → rdW (m'.arr64 CTL) k = rdW (m.arr64 CTL) k)
    (p : Word) : lvNodeW m' p = lvNodeW m p := by
  have ht := tierW_lt p
  have c : ∀ b : Word, b.toNat ≤ 14 → rdW (m'.arr64 CTL) (b + tierW p) =
      rdW (m.arr64 CTL) (b + tierW p) := fun b hb => hc _ (.inl (by
        rw [UInt64.toNat_add]; omega))
  simp only [lvNodeW, ha LH (by simp), ha SREC (by simp), ha MREC (by simp), ha IREC (by simp),
    ha PREC (by simp), hc 192 (.inr rfl), hc 1 (.inl (by decide)), c 6 (by decide),
    c 8 (by decide), c 10 (by decide), c 12 (by decide), c 14 (by decide)]

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

/-- A memo schema `lvNodeW` does not read: its array is not a level array or the heap, its words
are at or above 16 and not the heap top. -/
structure TreeSafe (S : MemoSch) : Prop where
  arr : S.arr ≠ LH ∧ S.arr ≠ SREC ∧ S.arr ≠ MREC ∧ S.arr ≠ IREC ∧ S.arr ≠ PREC
  cs : 16 ≤ S.cs.toNat ∧ S.cs.toNat + 1 < 192

/-- **Level pointers are a stable value relation** for a memo `lvNodeW` does not read. -/
theorem lvR_stable (N : Word → Name → Prop) (S : MemoSch) (hS : S.WF) (hT : TreeSafe S) :
    VStable S (fun m p l => LvR N m p l) := by
  intro m m' hf w l h
  refine LvR.of_view (fun p _ => lvNodeW_congr m m' (fun A hA => hf.1 A ?_ ?_) (fun k hk => hf.2.1 k ?_) p) h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hT.arr
    simp only [List.mem_singleton]
    rcases hA with rfl | rfl | rfl | rfl | rfl <;> grind
  · rcases hA with rfl | rfl | rfl | rfl | rfl <;> decide
  · have := hT.cs
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    have e : (S.cs + 1).toNat = S.cs.toNat + 1 := by
      rw [UInt64.toNat_add]; have := hS.cs; simp; omega
    constructor <;> intro hk' <;> subst hk' <;> rcases hk with hk | hk
    · omega
    · have := congrArg UInt64.toNat hk; simp at this; omega
    · rw [e] at hk; omega
    · have := congrArg UInt64.toNat hk; rw [e] at this; simp at this; omega

/-- **Level pointers survive the heap's growth** (and any writer that keeps every view). -/
theorem memoRV_heapExt {κ : Type} [BEq κ] [Hashable κ] (N : Word → Name → Prop) (S : MemoSch)
    (hS : S.WF) (K : MemoKey κ) (A : List ArrId) (C : List Word) (hA : S.arr ∉ A) (hC : S.cs ∉ C)
    (m m' : Mem) (hf : MemFrame A C m m') (he : HeapExt m m') (mp : Std.HashMap κ Level)
    (hR : MemoRV S K (fun m p l => LvR N m p l) m mp) :
    MemoRV S K (fun m p l => LvR N m p l) m' mp :=
  memoRV_frame S hS K _ A C hA hC m m' hf (fun _ _ h => LvR.mono he h) mp hR

/-! ## A test instance: a level-valued memo keyed by level handles -/

/-- A level-valued memo (the shape of `readLC`): array 100, stamp `CTL[100]`. -/
abbrev ltSch : MemoSch := ⟨100, 100⟩

theorem ltSch_wf : ltSch.WF := ⟨by decide, by decide⟩
theorem ltSch_safe : TreeSafe ltSch := ⟨by decide, by decide⟩

/-- Level-handle keys (one word below `2^32`). -/
def lvKey : MemoKey LIdx where
  dk k1 _ := decI k1
  ek x := (x.word.toUInt64, 0)
  ok k1 k2 := k1.toNat < 2 ^ 32 ∧ k2 = 0
  ek_dk k1 k2 h := by
    simp only [h.2, Prod.mk.injEq, and_true]
    exact (word_decI (decI (k := .level) k1) k1 h.1).mpr rfl
  ok_tomb k1 k2 h e := by subst e; exact absurd h.1 (by decide)

/-- `find; put` of a level pointer `p` denoting `l` is `readLC`'s insert. -/
theorem lt_set (N : Word → Name → Prop) (m m' : Mem) (mp : Std.HashMap LIdx Level)
    (hR : MemoRV ltSch lvKey (fun m p l => LvR N m p l) m mp) (h p : Word) (hh : h.toNat < 2 ^ 32)
    (l : Level) (hl : LvR N m p l) (hs : msetG ltSch m h 0 p = some m') :
    MemoRV ltSch lvKey (fun m p l => LvR N m p l) m' (mp.insert (decI h) l) :=
  memoRV_set ltSch ltSch_wf lvKey _ (lvR_stable N ltSch ltSch_wf ltSch_safe) m mp hR h 0 p
    ⟨hh, rfl⟩ l hl m' hs

/-- A hit is `readLC`'s cached level, denoted by the slot's pointer in the current memory. -/
theorem lt_hit (N : Word → Name → Prop) (m : Mem) (mp : Std.HashMap LIdx Level)
    (hR : MemoRV ltSch lvKey (fun m p l => LvR N m p l) m mp) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hr : mfindG ltSch m h 0 ≠ []) (hf : (mfindG ltSch m h 0).headD 0 ≠ 0) :
    ∃ l, mp[(decI h : LIdx)]? = some l ∧ LvR N m (mvG ltSch m ((mfindG ltSch m h 0).tail.headD 0)) l :=
  memoRV_hit ltSch lvKey _ m mp hR h 0 hr hf ⟨hh, rfl⟩

end L.Arena
