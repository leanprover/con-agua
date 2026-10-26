module

public import ConAgua.Arena.LevelHeap
public import ConLeche.Kernel.Level
import ConAgua.Census.Attr

@[expose] public section

/-!
# Level pointers and `Level` values: the decoder `LvR`

`LvR N m p l`: in memory `m`, the level pointer `p` (a store handle or a heap node, `LevelHeap.lean`)
denotes the level `l`. An inductive relation, so it needs no fuel and no termination argument: it
holds exactly along finite views. Names are related by a parameter `N : Word → Name → Prop`,
functional and injective (`NameRel`): under `ArenaR`, the store's name readback
(`LevelArena.lean`). The `zero` and `succ` views carry `0` in their unused fields, which is what
`lv_eq`'s uniform recursion needs (a zero node compares its fields by the pointer shortcut).

* `LvR.fn`: a pointer denotes at most one level.
* `HeapExt m m'`: every view of `m` is a view of `m'`; `LvR.mono` carries the relation across it,
  `lhMkW_ext` gives it for an allocation.
* `lvEqW_ok`: `lv_eq` is `decide (l = r)` (`Level.beq`).
-/


namespace L.Arena

open ConLeche

/-- A name decoder: functional and injective (so name words compare as names). -/
structure NameRel (N : Word → Name → Prop) : Prop where
  fn : ∀ w n n', N w n → N w n' → n = n'
  inj : ∀ w w' n, N w n → N w' n → w = w'

/-- **The decoder**: `p` denotes `l` in `m`. -/
inductive LvR (N : Word → Name → Prop) (m : Mem) : Word → Level → Prop
  | zero {p : Word} : lvNodeW m p = [0, 0, 0] → LvR N m p .zero
  | succ {p a : Word} {l : Level} : lvNodeW m p = [1, a, 0] → LvR N m a l → LvR N m p (.succ l)
  | max {p a b : Word} {l r : Level} :
      lvNodeW m p = [2, a, b] → LvR N m a l → LvR N m b r → LvR N m p (.max l r)
  | imax {p a b : Word} {l r : Level} :
      lvNodeW m p = [3, a, b] → LvR N m a l → LvR N m b r → LvR N m p (.imax l r)
  | param {p a b : Word} {n : Name} : lvNodeW m p = [4, a, b] → N a n → LvR N m p (.param n)

variable {N : Word → Name → Prop} {m m' : Mem}

theorem LvR.fn (hN : NameRel N) {p : Word} {l l' : Level} (h : LvR N m p l) (h' : LvR N m p l') :
    l = l' := by
  induction h generalizing l' with
  | zero hv => cases h' <;> simp_all
  | succ hv _ ih =>
    cases h' with
    | succ hv' h1 => rw [hv] at hv'; simp at hv'; subst hv'; rw [ih h1]
    | _ => simp_all
  | max hv _ _ ih1 ih2 =>
    cases h' with
    | max hv' h1 h2 => rw [hv] at hv'; simp at hv'; obtain ⟨rfl, rfl⟩ := hv'; rw [ih1 h1, ih2 h2]
    | _ => simp_all
  | imax hv _ _ ih1 ih2 =>
    cases h' with
    | imax hv' h1 h2 => rw [hv] at hv'; simp at hv'; obtain ⟨rfl, rfl⟩ := hv'; rw [ih1 h1, ih2 h2]
    | _ => simp_all
  | param hv hn =>
    cases h' with
    | param hv' hn' => rw [hv] at hv'; simp at hv'; obtain ⟨rfl, rfl⟩ := hv'; rw [hN.fn _ _ _ hn hn']
    | _ => simp_all

/-- The view of a related pointer, by constructor. -/
theorem LvR.view {p : Word} {l : Level} (h : LvR N m p l) : lvNodeW m p ≠ [] := by
  cases h <;> simp_all

/-! ## Heap growth -/

/-- Every view of `m` is a view of `m'`. -/
structure HeapExt (m m' : Mem) : Prop where
  view : ∀ p, lvNodeW m p ≠ [] → lvNodeW m' p = lvNodeW m p
  /-- The word arrays other than the heap and `CTL` are untouched. -/
  arr : ∀ A : ArrId, A ≠ LH → A ≠ CTL → m'.arr64 A = m.arr64 A
  /-- The `CTL` words other than the heap top are untouched. -/
  ctl : ∀ k : Word, k ≠ 192 → rdW (m'.arr64 CTL) k = rdW (m.arr64 CTL) k
  /-- No array changes its size. -/
  size : ∀ b : ArrId, (m'.arr64 b).size = (m.arr64 b).size
  wsize : m'.words.size = m.words.size
  /-- The heap top does not move down, and the heap below it stays. -/
  top : (htop m).toNat ≤ (htop m').toNat
  lh : ∀ k : Word, k.toNat < (htop m).toNat → rdW (m'.arr64 LH) k = rdW (m.arr64 LH) k

theorem HeapExt.refl (m : Mem) : HeapExt m m :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl, Nat.le_refl _,
    fun _ _ => rfl⟩

theorem HeapExt.trans {m₁ m₂ m₃ : Mem} (h₁ : HeapExt m₁ m₂) (h₂ : HeapExt m₂ m₃) :
    HeapExt m₁ m₃ :=
  ⟨fun p hp => by rw [h₂.view p (by rw [h₁.view p hp]; exact hp), h₁.view p hp],
    fun A a b => by rw [h₂.arr A a b, h₁.arr A a b], fun k hk => by rw [h₂.ctl k hk, h₁.ctl k hk],
    fun b => by rw [h₂.size b, h₁.size b], by rw [h₂.wsize, h₁.wsize], Nat.le_trans h₁.top h₂.top,
    fun k hk => by rw [h₂.lh k (Nat.lt_of_lt_of_le hk h₁.top), h₁.lh k hk]⟩

theorem LvR.mono (he : HeapExt m m') {p : Word} {l : Level} (h : LvR N m p l) : LvR N m' p l := by
  induction h with
  | zero hv => exact .zero (by rw [he.view _ (by simp [hv])]; exact hv)
  | succ hv _ ih => exact .succ (by rw [he.view _ (by simp [hv])]; exact hv) ih
  | max hv _ _ ih1 ih2 => exact .max (by rw [he.view _ (by simp [hv])]; exact hv) ih1 ih2
  | imax hv _ _ ih1 ih2 => exact .imax (by rw [he.view _ (by simp [hv])]; exact hv) ih1 ih2
  | param hv hn => exact .param (by rw [he.view _ (by simp [hv])]; exact hv) hn

theorem rdW_set64L (m : Mem) (a b : ArrId) (k v x : Word) :
    rdW ((m.set64 a k v).arr64 b) x =
      if b = a ∧ k = x ∧ k.toNat < (m.arr64 a).size then v else rdW (m.arr64 b) x := by
  by_cases h : b = a
  · subst h
    rw [Mem.arr64_set64_same]
    simp only [rdW, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hk : k = x
    · subst hk; by_cases hs : k.toNat < (m.arr64 b).size <;> simp [hs]
    · have : k.toNat ≠ x.toNat := fun e => hk (UInt64.toNat_inj.mp e)
      simp [this, hk]
  · rw [Mem.arr64_set64_ne _ _ _ _ _ h]; simp [h]

theorem size_set64L (m : Mem) (a b : ArrId) (k v : Word) :
    ((m.set64 a k v).arr64 b).size = (m.arr64 b).size := by
  by_cases h : b = a
  · subst h; rw [Mem.arr64_set64_same]; simp
  · rw [Mem.arr64_set64_ne _ _ _ _ _ h]

/-- What `lvNodeW` reads stays put: the store's level arrays, the `CTL` words other than the
heap top, and the heap below the top, which does not move down. -/
structure HeapFrame (m m' : Mem) : Prop where
  arr : ∀ A : ArrId, A ≠ CTL → A ≠ LH → m'.arr64 A = m.arr64 A
  ctl : ∀ k : Word, k ≠ 192 → rdW (m'.arr64 CTL) k = rdW (m.arr64 CTL) k
  top : (htop m).toNat ≤ (htop m').toNat
  lh : ∀ k : Word, k.toNat < (htop m).toNat → rdW (m'.arr64 LH) k = rdW (m.arr64 LH) k
  size : ∀ b : ArrId, (m'.arr64 b).size = (m.arr64 b).size
  wsize : m'.words.size = m.words.size

theorem tierW_lt (p : Word) : (tierW p).toNat ≤ 1 := by
  have h : tierW p ≤ 1 := UInt64.and_le_right
  rw [UInt64.le_iff_toNat_le] at h; simpa using h

theorem ctl_ne (c : Word) (hc : c.toNat ≤ 14) (p : Word) : c + tierW p ≠ 192 := by
  intro h
  have := congrArg UInt64.toNat h
  have ht := tierW_lt p
  rw [UInt64.toNat_add] at this
  simp at this
  omega

/-- A heap pointer is at least `2^32`. -/
theorem heap_ge (p : Word) (hb : ¬ p >>> 32 = 0) : 4294967296 ≤ p.toNat := by
  rcases Nat.lt_or_ge p.toNat 4294967296 with hc | hc
  · exfalso; apply hb; apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; omega
  · exact hc

/-- Offsets of a heap pointer: no wrap-around. -/
theorem heap_off (p k : Word) (hb : ¬ p >>> 32 = 0) (hk : k.toNat ≤ 3) :
    (p - 4294967296 + k).toNat = p.toNat - 4294967296 + k.toNat := by
  have hpn := heap_ge p hb
  have hpl := p.toNat_lt
  have hq : (p - 4294967296).toNat = p.toNat - 4294967296 := by
    rw [UInt64.toNat_sub_of_le]
    · rfl
    · rw [UInt64.le_iff_toNat_le]; simpa using hpn
  rw [UInt64.toNat_add, hq]; simp; omega

theorem lvNodeW_heap (m : Mem) (p : Word) (hb : ¬ p >>> 32 = 0) :
    lvNodeW m p = if rdW (m.arr64 CTL) 192 < p - 4294967296 + 3 then []
      else [rdW (m.arr64 LH) (p - 4294967296), rdW (m.arr64 LH) (p - 4294967296 + 1),
        rdW (m.arr64 LH) (p - 4294967296 + 2)] := by
  simp only [lvNodeW, hb, ne_eq, not_false_eq_true, ↓reduceIte]

theorem heap_sub (p : Word) (hb : ¬ p >>> 32 = 0) :
    (p - 4294967296).toNat = p.toNat - 4294967296 := by
  have hpn := heap_ge p hb
  rw [UInt64.toNat_sub_of_le]
  · rfl
  · rw [UInt64.le_iff_toNat_le]; simpa using hpn

theorem heap_below (x p : Word) (hb : ¬ p >>> 32 = 0) (hlt0 : ¬ x < p - 4294967296 + 3) :
    (p - 4294967296).toNat + 3 ≤ x.toNat := by
  have hk := heap_off p 3 hb (by simp)
  have e3 : UInt64.toNat 3 = 3 := rfl
  rw [UInt64.lt_iff_toNat_lt, hk, e3] at hlt0
  rw [heap_sub p hb]
  omega

theorem HeapFrame.heap (h : HeapFrame m m') (p : Word) (hb : ¬ p >>> 32 = 0)
    (hp : lvNodeW m p ≠ []) : lvNodeW m' p = lvNodeW m p := by
  rw [lvNodeW_heap m p hb] at hp ⊢
  rw [lvNodeW_heap m' p hb]
  have hlt0 : ¬ rdW (m.arr64 CTL) 192 < p - 4294967296 + 3 := fun e => hp (by rw [if_pos e])
  have hlt := heap_below _ p hb hlt0
  have ht := h.top
  simp only [htop] at ht
  have h3 : ¬ rdW (m'.arr64 CTL) 192 < p - 4294967296 + 3 := by
    have hk := heap_off p 3 hb (by simp)
    have e3 : UInt64.toNat 3 = 3 := rfl
    rw [UInt64.lt_iff_toNat_lt, hk, e3, ← heap_sub p hb]
    omega
  have hq := heap_sub p hb
  have h1 := heap_off p 1 hb (by simp)
  have h2 := heap_off p 2 hb (by simp)
  have e1 : UInt64.toNat 1 = 1 := rfl
  have e2 : UInt64.toNat 2 = 2 := rfl
  rw [e1] at h1
  rw [e2] at h2
  rw [if_neg h3, if_neg hlt0, h.lh _ (by simp only [htop]; omega),
    h.lh _ (by simp only [htop]; omega), h.lh _ (by simp only [htop]; omega)]

theorem HeapFrame.ext (h : HeapFrame m m') : HeapExt m m' := by
  refine ⟨fun p hp => ?_, fun A a b => h.arr A b a, h.ctl, h.size, h.wsize, h.top, h.lh⟩
  by_cases hb : p >>> 32 = 0
  · simp only [lvNodeW, hb, ne_eq, not_true_eq_false, ↓reduceIte]
    have c1 : rdW (m'.arr64 CTL) 1 = rdW (m.arr64 CTL) 1 := h.ctl 1 (by simp)
    have c8 : tcnt m' ZERO (tierW p) = tcnt m ZERO (tierW p) := h.ctl _ (ctl_ne 8 (by simp) p)
    have c6 : tcnt m' SUCC (tierW p) = tcnt m SUCC (tierW p) := h.ctl _ (ctl_ne 6 (by simp) p)
    have c10 : tcnt m' MAX (tierW p) = tcnt m MAX (tierW p) := h.ctl _ (ctl_ne 10 (by simp) p)
    have c12 : tcnt m' IMAX (tierW p) = tcnt m IMAX (tierW p) := h.ctl _ (ctl_ne 12 (by simp) p)
    have c14 : tcnt m' PARAM (tierW p) = tcnt m PARAM (tierW p) := h.ctl _ (ctl_ne 14 (by simp) p)
    have aS : m'.arr64 SREC = m.arr64 SREC := h.arr SREC (by decide) (by decide)
    have aM : m'.arr64 MREC = m.arr64 MREC := h.arr MREC (by decide) (by decide)
    have aI : m'.arr64 IREC = m.arr64 IREC := h.arr IREC (by decide) (by decide)
    have aP : m'.arr64 PREC = m.arr64 PREC := h.arr PREC (by decide) (by decide)
    have aS' : m'.arr64 (SREC + 256) = m.arr64 (SREC + 256) := h.arr _ (by decide) (by decide)
    have aM' : m'.arr64 (MREC + 256) = m.arr64 (MREC + 256) := h.arr _ (by decide) (by decide)
    have aI' : m'.arr64 (IREC + 256) = m.arr64 (IREC + 256) := h.arr _ (by decide) (by decide)
    have aP' : m'.arr64 (PREC + 256) = m.arr64 (PREC + 256) := h.arr _ (by decide) (by decide)
    simp only [c1, c8, c6, c10, c12, c14, tfld_arr_eq (R := SUCC) aS aS',
      tfld_arr_eq (R := MAX) aM aM', tfld_arr_eq (R := IMAX) aI aI', tfld_arr_eq (R := PARAM) aP aP']
  · exact h.heap p hb hp

/-! ## `lh_mk` -/

section lhMem
variable (m : Mem) (o g a b : Word) (hl : o.toNat + 2 < (m.arr64 LH).size)
  (hc : 192 < (m.arr64 CTL).size) (ho : o.toNat < 2 ^ 40)

theorem lhMem_arr (A : ArrId) (h1 : A ≠ CTL) (h2 : A ≠ LH) : (lhMem m o g a b).arr64 A = m.arr64 A := by
  simp only [lhMem]
  rw [Mem.arr64_set64_ne _ _ _ _ _ h1, Mem.arr64_set64_ne _ _ _ _ _ h2,
    Mem.arr64_set64_ne _ _ _ _ _ h2, Mem.arr64_set64_ne _ _ _ _ _ h2]

include hc in
theorem lhMem_ctl (k : Word) :
    rdW ((lhMem m o g a b).arr64 CTL) k = if k = 192 then o + 3 else rdW (m.arr64 CTL) k := by
  simp only [lhMem, rdW_set64L, size_set64L]
  have h1 : (CTL : ArrId) ≠ LH := by decide
  by_cases hk : k = 192
  · subst hk; simp [hc]
  · simp [hk, Ne.symm hk, h1]

include hl ho in
theorem lhMem_lh (k : Word) :
    rdW ((lhMem m o g a b).arr64 LH) k =
      if k = o + 2 then b else if k = o + 1 then a else if k = o then g else rdW (m.arr64 LH) k := by
  have h1 : (LH : ArrId) ≠ CTL := by decide
  have e1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (o + 2).toNat = o.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have s2 : (o + 2).toNat < (m.arr64 LH).size := by omega
  have s1 : (o + 1).toNat < (m.arr64 LH).size := by omega
  have s0 : o.toNat < (m.arr64 LH).size := by omega
  simp only [lhMem, rdW_set64L, size_set64L, h1, false_and, ↓reduceIte, true_and, s2, s1, s0,
    and_true]
  by_cases k2 : k = o + 2
  · subst k2; simp
  · by_cases k1 : k = o + 1
    · subst k1; simp [Ne.symm k2]
    · by_cases k0 : k = o
      · subst k0; simp [Ne.symm k2, Ne.symm k1]
      · simp [Ne.symm k2, Ne.symm k1, Ne.symm k0, k2, k1, k0]

end lhMem

/-- An allocation keeps every view, and the new pointer views as the node written. -/
theorem lhMkW_ext {g a b r : Word} (h : lhMkW m g a b = some (r, m')) :
    HeapExt m m' ∧ lvNodeW m' r = [g, a, b] ∧ (htop m').toNat = (htop m).toNat + 3 := by
  simp only [lhMkW] at h
  split at h
  · simp at h
  · rename_i hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simp only [not_or, UInt64.not_le, ne_eq, Decidable.not_not, Nat.not_le] at hc
    obtain ⟨h40, hlen, hctl⟩ := hc
    have ht : (htop m).toNat < 2 ^ 40 := by
      have := congrArg UInt64.toNat h40
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow] at this
      omega
    have hl : (htop m).toNat + 2 < (m.arr64 LH).size := by
      rw [UInt64.lt_iff_toNat_lt] at hlen
      simp [Mem.len64] at hlen
      have := Nat.mod_le (m.arr64 LH).size 18446744073709551616
      have : (UInt64.toNat (htop m) + 2) % 18446744073709551616 = UInt64.toNat (htop m) + 2 :=
        Nat.mod_eq_of_lt (by omega)
      omega
    have ek : ∀ j : Word, j.toNat ≤ 3 → (htop m + j).toNat = (htop m).toNat + j.toNat := by
      intro j hj; rw [UInt64.toNat_add]; simp; omega
    have e3 : (htop m + 3).toNat = (htop m).toNat + 3 := ek 3 (by decide)
    have htop' : htop (lhMem m (htop m) g a b) = htop m + 3 := by
      simp only [htop]; rw [lhMem_ctl _ _ _ _ _ hctl]; simp
    refine ⟨HeapFrame.ext ⟨fun A h1 h2 => lhMem_arr _ _ _ _ _ A h1 h2,
      fun k hk => by rw [lhMem_ctl _ _ _ _ _ hctl, if_neg hk], by rw [htop', e3]; omega,
      fun k hk => ?_, fun b => by simp only [lhMem, size_set64L],
      by simp only [lhMem, Mem.words_size_set64]⟩, ?_, by rw [htop', e3]⟩
    · rw [lhMem_lh _ _ _ _ _ hl ht]
      have n2 : k ≠ htop m + 2 := fun e => by rw [e, ek 2 (by decide)] at hk; simp at hk; omega
      have n1 : k ≠ htop m + 1 := fun e => by rw [e, ek 1 (by decide)] at hk; simp at hk; omega
      have n0 : k ≠ htop m := fun e => by rw [e] at hk; omega
      simp [n2, n1, n0]
    · have hb : ¬ (htop m + 4294967296) >>> 32 = 0 := by
        intro e
        have := congrArg UInt64.toNat e
        simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_add] at this
        simp at this; omega
      have hs : htop m + 4294967296 - 4294967296 = htop m := by simp
      simp only [lvNodeW, hb, ne_eq, not_false_eq_true, ↓reduceIte, hs]
      rw [show rdW ((lhMem m (htop m) g a b).arr64 CTL) 192 = htop m + 3 from htop']
      simp only [UInt64.lt_irrefl, ↓reduceIte]
      rw [lhMem_lh _ _ _ _ _ hl ht, lhMem_lh _ _ _ _ _ hl ht, lhMem_lh _ _ _ _ _ hl ht]
      have n21 : htop m + 1 ≠ htop m + 2 := by simp
      have n20 : htop m ≠ htop m + 2 := by
        intro e; have := congrArg UInt64.toNat e; rw [ek 2 (by decide)] at this; simp at this
      have n10 : htop m ≠ htop m + 1 := by
        intro e; have := congrArg UInt64.toNat e; rw [ek 1 (by decide)] at this; simp at this
      simp [n21, n20, n10]

/-! ## `lv_eq` is structural equality -/

theorem lvEqW_zz (n : Nat) (x : Word) (h : lvEqW n m 0 0 = some x) : x = 1 := by
  cases n with
  | zero => simp [lvEqW] at h
  | succ n => rw [lvEqW_refl] at h; simp at h; exact h.symm

/-- The view fields of a related pointer. -/
theorem lv_fields {p : Word} {g a b : Word} (h : lvNodeW m p = [g, a, b]) :
    lvG m p = g ∧ lvA m p = a ∧ lvB m p = b := by
  simp [lvG, lvA, lvB, h]

/-- **`lv_eq` decides equality of the denoted levels.** -/
@[refines ConLeche.Level.beq]
theorem lvEqW_ok (hN : NameRel N) (n : Nat) : ∀ (p q : Word) (l r : Level) (x : Word),
    LvR N m p l → LvR N m q r → lvEqW n m p q = some x → x = if Level.beq l r then 1 else 0 := by
  induction n with
  | zero => intro p q l r x _ _ h; simp [lvEqW] at h
  | succ n ih =>
    intro p q l r x hl hr hx
    simp only [Level.beq, decide_eq_true_eq]
    by_cases hpq : p = q
    · subst hpq
      rw [lvEqW_refl] at hx; simp at hx
      rw [hl.fn hN hr] at *; simp [hx]
    · have tagne : ∀ {g h : Word}, g ≠ h → lvG m p = g → lvG m q = h → x = 0 := by
        intro g h gh hg hh
        rw [lvEqW_tag n m p q hpq (by rw [hg, hh]; exact gh)] at hx; simp at hx; exact hx.symm
      have hrec : ∀ {g : Word}, lvG m p = g → lvG m q = g → g ≠ 4 →
          ∃ y, lvEqW n m (lvA m p) (lvA m q) = some y ∧
            (y = 0 → x = 0) ∧ (y ≠ 0 → lvEqW n m (lvB m p) (lvB m q) = some x) := by
        intro g hg hh h4
        rw [lvEqW_rec n m p q hpq (by rw [hg, hh]) (by rw [hg]; exact h4)] at hx
        cases e : lvEqW n m (lvA m p) (lvA m q) with
        | none => rw [e] at hx; simp [eqK] at hx
        | some y =>
          rw [e] at hx
          refine ⟨y, rfl, fun hy => ?_, fun hy => ?_⟩
          · subst hy; rw [eqK_zero] at hx; simp at hx; exact hx.symm
          · rw [eqK_ne _ _ _ _ _ hy] at hx; exact hx
      cases hl with
      | zero hv =>
        obtain ⟨g1, -, -⟩ := lv_fields hv
        cases hr with
        | zero hv' =>
          obtain ⟨g2, a2, b2⟩ := lv_fields hv'
          obtain ⟨-, a1, b1⟩ := lv_fields hv
          obtain ⟨y, hy, h0, h1⟩ := hrec g1 g2 (by decide)
          rw [a1, a2] at hy; have := lvEqW_zz n y hy
          rw [b1, b2] at h1; exact (lvEqW_zz n x (h1 (by rw [this]; decide))).trans (by simp)
        | succ hv' _ | max hv' _ _ | imax hv' _ _ | param hv' _ => simp [tagne (by decide) g1 (lv_fields hv').1]
      | succ hv hl1 =>
        obtain ⟨g1, a1, b1⟩ := lv_fields hv
        cases hr with
        | succ hv' hr1 =>
          obtain ⟨g2, a2, b2⟩ := lv_fields hv'
          obtain ⟨y, hy, h0, h1⟩ := hrec g1 g2 (by decide)
          rw [a1, a2] at hy
          have hy' := ih _ _ _ _ _ hl1 hr1 hy
          simp only [Level.beq, decide_eq_true_eq] at hy'
          rename_i l1 _ r1
          by_cases e : l1 = r1
          · subst e; simp at hy'; rw [b1, b2] at h1
            simp [lvEqW_zz n x (h1 (by rw [hy']; decide))]
          · simp [e] at hy'; simp [h0 hy', e]
        | zero hv' | max hv' _ _ | imax hv' _ _ | param hv' _ => simp [tagne (by decide) g1 (lv_fields hv').1]
      | max hv hl1 hl2 | imax hv hl1 hl2 =>
        obtain ⟨g1, a1, b1⟩ := lv_fields hv
        cases hr with
        | max hv' hr1 hr2 | imax hv' hr1 hr2 =>
          first
          | simp [tagne (by decide) g1 (lv_fields hv').1]
          | rename_i l1 l2 _ _ r1 r2
            obtain ⟨g2, a2, b2⟩ := lv_fields hv'
            obtain ⟨y, hy, h0, h1⟩ := hrec g1 g2 (by decide)
            rw [a1, a2] at hy
            have hy' := ih _ _ _ _ _ hl1 hr1 hy
            simp only [Level.beq, decide_eq_true_eq] at hy'
            by_cases e : l1 = r1
            · simp [e] at hy'; rw [b1, b2] at h1
              have := ih _ _ _ _ _ hl2 hr2 (h1 (by rw [hy']; decide))
              simp only [Level.beq, decide_eq_true_eq] at this
              rw [this]; simp [e]
            · simp [e] at hy'; simp [h0 hy', e]
        | zero hv' | succ hv' _ | param hv' _ => simp [tagne (by decide) g1 (lv_fields hv').1]
      | @param _ w1 _ n1 hv hn =>
        obtain ⟨g1, a1, -⟩ := lv_fields hv
        cases hr with
        | @param _ w2 _ n2 hv' hn' =>
          obtain ⟨g2, a2, -⟩ := lv_fields hv'
          rw [lvEqW_param n m p q hpq (by rw [g1, g2]) g1] at hx
          simp only [Option.some.injEq] at hx
          rw [a1, a2] at hx
          by_cases e : w1 = w2
          · subst e; rw [hN.fn _ _ _ hn hn']; simp at hx ⊢; exact hx.symm
          · have : n1 ≠ n2 := fun h => e (hN.inj _ _ _ hn (h ▸ hn'))
            simp [e] at hx; simp [this, hx]
        | zero hv' | succ hv' _ | max hv' _ _ | imax hv' _ _ => simp [tagne (by decide) g1 (lv_fields hv').1]

end L.Arena
