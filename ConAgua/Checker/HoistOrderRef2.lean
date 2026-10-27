import ConAgua.Checker.HoistRefBase
import ConRon.Arena.Frontend.NatOpGround

/-!
# The hoist's order, on lists (lane `front4`)

The pure side of `hoistApply_ok` (`HoistOrderRef.lean`):

* `posT T t a b`: the positions `a ≤ k < b` moved to `t`, ascending — one bucket of `hoist_bucket`,
  the list `hoist_chain` walks.
* `nxW T j k`: the word `hoist_bucket` leaves in `nx[j]` after positions `0 ‥ k`.
* `emitL T C p`: the order `hoist_emit` writes from position `p` on (`blk`: per position, its
  bucket then itself unless it moved).
* `emitL_eq_hoistOrder`: that order is `applyHoist`'s merge sort, the unique sorted permutation
  (keys pairwise distinct).
-/

open ConRon.Arena ConRon.Arena.Frontend

namespace L.Checker

/-! ## Buckets -/

/-- The positions `a ≤ k < b` with target `t`, ascending. -/
def posT (T : Std.HashMap Nat Nat) (t a b : Nat) : List Nat :=
  (List.range' a (b - a)).filter (fun k => T[k]? == some t)

theorem mem_posT {T : Std.HashMap Nat Nat} {t a b k : Nat} :
    k ∈ posT T t a b ↔ a ≤ k ∧ k < b ∧ T[k]? = some t := by
  simp only [posT, List.mem_filter, List.mem_range'_1, beq_iff_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩

theorem posT_empty (T : Std.HashMap Nat Nat) (t a b : Nat) (h : b ≤ a) : posT T t a b = [] := by
  simp [posT, show b - a = 0 by omega]

theorem posT_succ (T : Std.HashMap Nat Nat) (t a b : Nat) (h : a ≤ b) :
    posT T t a (b + 1) = posT T t a b ++ (if T[b]? = some t then [b] else []) := by
  simp only [posT, show b + 1 - a = (b - a) + 1 by omega, List.range'_concat, List.filter_append]
  rw [show a + 1 * (b - a) = b by omega]
  by_cases hb : T[b]? = some t <;> simp [hb]

theorem posT_succ_ne (T : Std.HashMap Nat Nat) (t a b : Nat) (h : T[b]? ≠ some t) :
    posT T t a (b + 1) = posT T t a b := by
  by_cases hab : a ≤ b
  · rw [posT_succ _ _ _ _ hab]; simp [h]
  · rw [posT_empty _ _ _ _ (by omega), posT_empty _ _ _ _ (by omega)]

theorem posT_succ_eq (T : Std.HashMap Nat Nat) (t a b : Nat) (h : T[b]? = some t) (hab : a ≤ b) :
    posT T t a (b + 1) = posT T t a b ++ [b] := by
  rw [posT_succ _ _ _ _ hab]; simp [h]

theorem posT_left (T : Std.HashMap Nat Nat) (t a b : Nat) (h : a < b) :
    posT T t a b = (if T[a]? = some t then [a] else []) ++ posT T t (a + 1) b := by
  simp only [posT, show b - a = (b - (a + 1)) + 1 by omega, List.range'_succ, List.filter_cons]
  by_cases ha : T[a]? = some t <;> simp [ha]

theorem posT_split (T : Std.HashMap Nat Nat) (t a x b : Nat) (h1 : a ≤ x) (h2 : x ≤ b) :
    posT T t a b = posT T t a x ++ posT T t x b := by
  simp only [posT, ← List.filter_append]
  rw [show b - a = (x - a) + (b - x) by omega, ← List.range'_append_1,
    show a + (x - a) = x by omega]

/-- A bucket from its first element on. -/
theorem posT_head (T : Std.HashMap Nat Nat) (t a b x : Nat) (h : (posT T t a b).head? = some x) :
    posT T t a b = x :: posT T t (x + 1) b := by
  have hx : x ∈ posT T t a b := List.mem_of_head? h
  obtain ⟨h1, h2, h3⟩ := mem_posT.1 hx
  have hs := posT_split T t a x b h1 (by omega)
  rw [posT_left T t x b h2] at hs; simp only [h3, ↓reduceIte] at hs
  cases hl : posT T t a x with
  | nil => rw [hs, hl]; rfl
  | cons y ys =>
    have hy : y ∈ posT T t a x := by rw [hl]; exact List.mem_cons_self
    have := (mem_posT.1 hy).2.1
    rw [hs, hl] at h
    simp at h
    omega

/-- The last element of a bucket is its largest. -/
theorem posT_le_last (T : Std.HashMap Nat Nat) (t a : Nat) :
    ∀ (k l y : Nat), (posT T t a k).getLast? = some l → y ∈ posT T t a k → y ≤ l := by
  intro k
  induction k with
  | zero => intro l y _ hy; simp [posT] at hy
  | succ k ih =>
    intro l y hl hy
    by_cases hab : a ≤ k
    · by_cases hk : T[k]? = some t
      · rw [posT_succ_eq _ _ _ _ hk hab] at hl hy
        simp at hl
        have := (mem_posT.1 (show y ∈ posT T t a (k + 1) by
          rw [posT_succ_eq _ _ _ _ hk hab]; exact hy)).2.1
        omega
      · rw [posT_succ_ne _ _ _ _ hk] at hl hy
        exact ih l y hl hy
    · rw [posT_empty _ _ _ _ (by omega)] at hy; simp at hy

/-! ## The `nx` words -/

/-- The word `nx[j]` after `hoist_bucket` saw positions `0 ‥ k`: the next position after `j` with
`j`'s target, plus one, or `0`. -/
def nxW (T : Std.HashMap Nat Nat) (j k : Nat) : Word :=
  match T[j]? with
  | some t => tgW (posT T t (j + 1) k).head?
  | none => 0

theorem nxW_some (T : Std.HashMap Nat Nat) (j k t : Nat) (h : T[j]? = some t) :
    nxW T j k = tgW (posT T t (j + 1) k).head? := by
  simp [nxW, h]

theorem nxW_none (T : Std.HashMap Nat Nat) (j k : Nat) (h : T[j]? = none) : nxW T j k = 0 := by
  simp [nxW, h]

theorem nxW_zero (T : Std.HashMap Nat Nat) (j : Nat) : nxW T j 0 = 0 := by
  cases h : T[j]? with
  | none => exact nxW_none T j 0 h
  | some t => rw [nxW_some T j 0 t h, posT_empty _ _ _ _ (by omega)]; rfl

/-- A step of `hoist_bucket` keeps `nx[j]` unless `j` is the last of `k`'s bucket. -/
theorem nxW_step (T : Std.HashMap Nat Nat) (j k : Nat)
    (hk : ∀ t, T[k]? = some t → T[j]? = some t → j < k → (posT T t 0 k).getLast? ≠ some j) :
    nxW T j (k + 1) = nxW T j k := by
  cases hj : T[j]? with
  | none => rw [nxW_none T j _ hj, nxW_none T j _ hj]
  | some t =>
    rw [nxW_some T j _ t hj, nxW_some T j _ t hj]
    by_cases hkt : T[k]? = some t
    · by_cases hjk : j < k
      · have hk' := hk t hkt hj hjk
        have hjm : j ∈ posT T t 0 k := mem_posT.2 ⟨by omega, hjk, hj⟩
        cases hl : (posT T t 0 k).getLast? with
        | none => simp at hl; rw [hl] at hjm; simp at hjm
        | some l =>
          have hle := posT_le_last T t 0 k l j hl hjm
          have hne : j ≠ l := fun e => hk' (e ▸ hl)
          have hlm : l ∈ posT T t (j + 1) k := by
            have := mem_posT.1 (List.mem_of_getLast? hl)
            exact mem_posT.2 ⟨by omega, this.2.1, this.2.2⟩
          rw [posT_succ_eq _ _ _ _ hkt (by omega), List.head?_append]
          cases hh : (posT T t (j + 1) k).head? with
          | none => simp at hh; rw [hh] at hlm; simp at hlm
          | some z => rfl
      · rw [posT_empty _ _ _ _ (by omega), posT_empty _ _ _ _ (by omega)]
    · rw [posT_succ_ne _ _ _ _ hkt]

/-- The step of `hoist_bucket` that appends `k` after the last `l` of its bucket. -/
theorem nxW_last (T : Std.HashMap Nat Nat) (k t l : Nat) (hk : T[k]? = some t)
    (hl : (posT T t 0 k).getLast? = some l) : nxW T l (k + 1) = tgW (some k) := by
  have hlm := mem_posT.1 (List.mem_of_getLast? hl)
  rw [nxW_some T l _ t hlm.2.2, posT_succ_eq _ _ _ _ hk (by omega)]
  have he : posT T t (l + 1) k = [] := by
    cases hc : posT T t (l + 1) k with
    | nil => rfl
    | cons y ys =>
      have hy : y ∈ posT T t (l + 1) k := by rw [hc]; exact List.mem_cons_self
      have hy' := mem_posT.1 hy
      have := posT_le_last T t 0 k l y hl (mem_posT.2 ⟨by omega, hy'.2.1, hy'.2.2⟩)
      omega
  rw [he]; rfl

theorem head_step (T : Std.HashMap Nat Nat) (t k : Nat) (h : T[k]? ≠ some t ∨ posT T t 0 k ≠ []) :
    (posT T t 0 (k + 1)).head? = (posT T t 0 k).head? := by
  by_cases hk : T[k]? = some t
  · rw [posT_succ_eq _ _ _ _ hk (by omega), List.head?_append]
    have hne : posT T t 0 k ≠ [] := by simpa [hk] using h
    cases hh : (posT T t 0 k).head? with
    | none => simp at hh; exact absurd hh hne
    | some z => rfl
  · rw [posT_succ_ne _ _ _ _ hk]

theorem head_new (T : Std.HashMap Nat Nat) (t k : Nat) (hk : T[k]? = some t)
    (h : posT T t 0 k = []) : (posT T t 0 (k + 1)).head? = some k := by
  rw [posT_succ_eq _ _ _ _ hk (by omega), h]; rfl

theorem last_step_eq (T : Std.HashMap Nat Nat) (t k : Nat) (hk : T[k]? = some t) :
    (posT T t 0 (k + 1)).getLast? = some k := by
  rw [posT_succ_eq _ _ _ _ hk (by omega)]; simp

/-! ## The emitted order -/

/-- Position `p`'s block: the positions moved to `p`, then `p` itself unless it moved. -/
def blk (T : Std.HashMap Nat Nat) (C p : Nat) : List Nat :=
  posT T p 0 C ++ (if T[p]? = none then [p] else [])

/-- The order `hoist_emit` writes from position `p` on. -/
def emitL (T : Std.HashMap Nat Nat) (C p : Nat) : List Nat :=
  (List.range' p (C - p)).flatMap (blk T C)

theorem emitL_left (T : Std.HashMap Nat Nat) (C p : Nat) (h : p < C) :
    emitL T C p = blk T C p ++ emitL T C (p + 1) := by
  simp only [emitL, show C - p = (C - (p + 1)) + 1 by omega, List.range'_succ, List.flatMap_cons]

theorem emitL_end (T : Std.HashMap Nat Nat) (C p : Nat) (h : C ≤ p) : emitL T C p = [] := by
  simp [emitL, show C - p = 0 by omega]

/-! ## Sorting -/

/-- The strict lexicographic order on keys (`hoistLt`'s body). -/
def lexB (x y : Nat × Nat × Nat) : Bool :=
  x.1 < y.1 || (x.1 == y.1 && (x.2.1 < y.2.1 || (x.2.1 == y.2.1 && x.2.2 < y.2.2)))

theorem hoistLt_eq (T : Std.HashMap Nat Nat) (a b : Nat) :
    hoistLt T a b = lexB (hoistKey T a) (hoistKey T b) := rfl

theorem lexB_trans (x y z : Nat × Nat × Nat) (h1 : lexB y x = false) (h2 : lexB z y = false) :
    lexB z x = false := by
  obtain ⟨x1, x2, x3⟩ := x; obtain ⟨y1, y2, y3⟩ := y; obtain ⟨z1, z2, z3⟩ := z
  simp only [lexB, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne, ne_eq] at *
  omega

theorem lexB_total (x y : Nat × Nat × Nat) (h1 : lexB x y = false) (h2 : lexB y x = false) :
    x = y := by
  obtain ⟨x1, x2, x3⟩ := x; obtain ⟨y1, y2, y3⟩ := y
  simp only [lexB, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne, ne_eq] at *
  simp only [Prod.mk.injEq]
  omega

theorem lexB_asymm (x y : Nat × Nat × Nat) (h : lexB x y = true) : lexB y x = false := by
  obtain ⟨x1, x2, x3⟩ := x; obtain ⟨y1, y2, y3⟩ := y
  simp only [lexB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne,
    ne_eq] at *
  omega

theorem hoistKey_inj (T : Std.HashMap Nat Nat) (a b : Nat) (h : hoistKey T a = hoistKey T b) :
    a = b := by
  have ha : (hoistKey T a).2.2 = a := by unfold hoistKey; split <;> rfl
  have hb : (hoistKey T b).2.2 = b := by unfold hoistKey; split <;> rfl
  rw [← ha, ← hb, h]

theorem hoistKey_some (T : Std.HashMap Nat Nat) (k t : Nat) (h : T[k]? = some t) :
    hoistKey T k = (t, 0, k) := by
  simp [hoistKey, h]

theorem hoistKey_none (T : Std.HashMap Nat Nat) (k : Nat) (h : T[k]? = none) :
    hoistKey T k = (k, 1, k) := by
  simp [hoistKey, h]

/-- Two permutations of each other, both sorted by an asymmetric relation, are equal. -/
theorem eq_of_perm_pairwise {α : Type} {R : α → α → Prop} (hasym : ∀ a b, R a b → ¬ R b a) :
    ∀ {l1 l2 : List α}, l1.Perm l2 → l1.Pairwise R → l2.Pairwise R → l1 = l2
  | [], l2, hp, _, _ => hp.nil_eq
  | a :: l1, [], hp, _, _ => absurd hp.symm.nil_eq (by simp)
  | a :: l1, b :: l2, hp, h1, h2 => by
    by_cases hab : a = b
    · subst hab
      rw [eq_of_perm_pairwise hasym hp.cons_inv (List.pairwise_cons.1 h1).2
        (List.pairwise_cons.1 h2).2]
    · have hb : b ∈ l1 := by
        have := hp.symm.subset List.mem_cons_self
        simp only [List.mem_cons] at this
        exact this.resolve_left (Ne.symm hab)
      have ha : a ∈ l2 := by
        have := hp.subset List.mem_cons_self
        simp only [List.mem_cons] at this
        exact this.resolve_left hab
      exact absurd ((List.pairwise_cons.1 h2).1 a ha) (hasym _ _ ((List.pairwise_cons.1 h1).1 b hb))

/-- The merge sort is sorted by the strict order. -/
theorem hoistOrder_sorted (T : Std.HashMap Nat Nat) (C : Nat) :
    ((List.range C).mergeSort (fun a b => !hoistLt T b a)).Pairwise
      (fun a b => hoistLt T a b = true) := by
  have hle := List.pairwise_mergeSort (le := fun a b => !hoistLt T b a)
    (fun a b c h1 h2 => by
      simp only [Bool.not_eq_true', hoistLt_eq] at *
      exact lexB_trans _ _ _ h1 h2)
    (fun a b => by
      simp only [Bool.or_eq_true, Bool.not_eq_true', hoistLt_eq]
      cases h : lexB (hoistKey T b) (hoistKey T a)
      · exact Or.inl rfl
      · exact Or.inr (lexB_asymm _ _ h))
    (List.range C)
  have hnd : ((List.range C).mergeSort (fun a b => !hoistLt T b a)).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.2 List.nodup_range
  refine (hle.and hnd).imp ?_
  intro a b ⟨h1, h2⟩
  simp only [Bool.not_eq_true', hoistLt_eq] at h1 ⊢
  cases h : lexB (hoistKey T a) (hoistKey T b)
  · exact absurd (hoistKey_inj T a b (lexB_total _ _ h h1)) h2
  · rfl

theorem mem_blk (T : Std.HashMap Nat Nat) (C p x : Nat) :
    x ∈ blk T C p ↔ (x < C ∧ T[x]? = some p) ∨ (x = p ∧ T[p]? = none) := by
  simp only [blk, List.mem_append, mem_posT]
  by_cases h : T[p]? = none <;> simp [h] <;> omega

theorem blk_sorted (T : Std.HashMap Nat Nat) (C p : Nat) :
    (blk T C p).Pairwise (fun a b => hoistLt T a b = true) := by
  simp only [blk]
  refine List.pairwise_append.2 ⟨?_, ?_, ?_⟩
  · refine ((List.pairwise_lt_range' (s := 0) (n := C - 0)).filter _).imp_of_mem ?_
    intro a b ha hb hab
    rw [hoistLt_eq, hoistKey_some T a p (mem_posT.1 ha).2.2, hoistKey_some T b p (mem_posT.1 hb).2.2]
    simp [lexB, hab]
  · split <;> simp
  · intro a ha b hb
    split at hb
    · next hp =>
      simp only [List.mem_singleton] at hb; rw [hb]
      rw [hoistLt_eq, hoistKey_some T a p (mem_posT.1 ha).2.2, hoistKey_none T p hp]
      simp [lexB]
    · simp at hb

theorem blk_key (T : Std.HashMap Nat Nat) (C p x : Nat) (h : x ∈ blk T C p) :
    (hoistKey T x).1 = p := by
  rcases (mem_blk T C p x).1 h with ⟨_, hx⟩ | ⟨hxp, hx⟩
  · rw [hoistKey_some T x p hx]
  · subst hxp; rw [hoistKey_none T x hx]

theorem emitL_sorted (T : Std.HashMap Nat Nat) (C : Nat) :
    (emitL T C 0).Pairwise (fun a b => hoistLt T a b = true) := by
  simp only [emitL]
  refine List.pairwise_flatMap.2 ⟨fun p _ => blk_sorted T C p, ?_⟩
  refine (List.pairwise_lt_range' (s := 0) (n := C - 0)).imp ?_
  intro p1 p2 hp x hx y hy
  rw [hoistLt_eq]
  have h1 := blk_key T C p1 x hx
  have h2 := blk_key T C p2 y hy
  simp [lexB, h1, h2, hp]

theorem mem_emitL (T : Std.HashMap Nat Nat) (C x : Nat)
    (hlt : ∀ (k t : Nat), T[k]? = some t → t < k) : x ∈ emitL T C 0 ↔ x < C := by
  simp only [emitL, List.mem_flatMap, List.mem_range'_1, mem_blk]
  constructor
  · rintro ⟨p, hp, (⟨h, _⟩ | ⟨rfl, _⟩)⟩ <;> omega
  · intro hx
    cases h : T[x]? with
    | none => exact ⟨x, by omega, Or.inr ⟨rfl, h⟩⟩
    | some t => exact ⟨t, by have := hlt x t h; omega, Or.inl ⟨hx, rfl⟩⟩

theorem emitL_perm (T : Std.HashMap Nat Nat) (C : Nat)
    (hlt : ∀ (k t : Nat), T[k]? = some t → t < k) : (emitL T C 0).Perm (List.range C) := by
  have hnd : (emitL T C 0).Nodup := (emitL_sorted T C).imp (fun {a b} h e => by
    subst e; rw [hoistLt_eq] at h; have := lexB_asymm _ _ h; rw [h] at this; cases this)
  refine (List.perm_ext_iff_of_nodup hnd List.nodup_range).2 fun x => ?_
  rw [mem_emitL T C x hlt, List.mem_range]

/-- **L's order is `applyHoist`'s merge sort.** -/
theorem emitL_eq_sort (T : Std.HashMap Nat Nat) (C : Nat)
    (hlt : ∀ (k t : Nat), T[k]? = some t → t < k) :
    emitL T C 0 = (List.range C).mergeSort (fun a b => !hoistLt T b a) :=
  eq_of_perm_pairwise (R := fun a b => hoistLt T a b = true)
    (fun a b h h' => by rw [hoistLt_eq] at h h'; rw [lexB_asymm _ _ h] at h'; cases h')
    ((emitL_perm T C hlt).trans (List.mergeSort_perm _ _).symm) (emitL_sorted T C)
    (hoistOrder_sorted T C)

theorem emitL_length (T : Std.HashMap Nat Nat) (C : Nat)
    (hlt : ∀ (k t : Nat), T[k]? = some t → t < k) : (emitL T C 0).length = C := by
  rw [(emitL_perm T C hlt).length_eq, List.length_range]

end L.Checker
