import ConAgua.Front.NatDec
import ConAgua.Arena.LitRefine
import ConAgua.Front.ExprIface
import ConAgua.Scan.LeafLink
import ConAgua.Scan.Link
import ConAgua.Census.Attr

/-!
# `nat_dec` reads con-leche's `natVal`

The facts about the models of `ConAgua.Front.NatDec`, by hand: the chunk loop reads the decimal
value of its digits (`chunkN_val`), the multiply-add pass multiplies (`madW_val`), the chunk loop
keeps the slice normalised and denoting the digits read so far (`decW_val`); and con-leche's
`readNatAt` at a digit run is that decimal value (`readNatAt_decN`). `natDec_spec`: on a literal
the scanner accepted (`NatValR`), `nat_dec(c, d)` appends the normalised limbs of its value.
-/

open Std.WP
open scoped Lean.Order
open L.Arena


namespace L.Front

open L.Scan.Utf8 (byteW)

/-! ## Decimal values -/

/-- The decimal value of the `k` digits of `b` at `i`. -/
def decN (b : Array UInt8) (i : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => decN b i k * 10 + ((b.getD (i + k) 0).toNat - 48)

/-- The `k` bytes at `i` are digits. -/
def Digits (b : Array UInt8) (i k : Nat) : Prop :=
  ∀ j, j < k → 48 ≤ (b.getD (i + j) 0).toNat ∧ (b.getD (i + j) 0).toNat ≤ 57

theorem decN_lt (b : Array UInt8) (i : Nat) : ∀ k, Digits b i k → decN b i k < 10 ^ k
  | 0, _ => by simp [decN]
  | k + 1, h => by
    have ih := decN_lt b i k (fun j hj => h j (by omega))
    have := h k (by omega)
    simp only [decN, Nat.pow_succ]
    omega

theorem decN_append (b : Array UInt8) (i a : Nat) : ∀ k,
    decN b i (a + k) = decN b i a * 10 ^ k + decN b (i + a) k
  | 0 => by simp [decN]
  | k + 1 => by
    rw [← Nat.add_assoc, decN, decN_append b i a k, decN, Nat.pow_succ, Nat.add_assoc i a k]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem digits_mono (b : Array UInt8) (i k k' : Nat) (h : Digits b i k) (hk : k' ≤ k) :
    Digits b i k' := fun j hj => h j (by omega)

theorem digits_shift (b : Array UInt8) (i a k : Nat) (h : Digits b i (a + k)) :
    Digits b (i + a) k := fun j hj => by rw [Nat.add_assoc]; exact h (a + j) (by omega)

/-! ## The chunk -/

theorem digit_word (x : UInt8) : 48 ≤ x.toNat → x.toNat ≤ 57 →
    ((x.toUInt64 - 48) &&& 255).toNat = x.toNat - 48 := by
  revert x; decide

theorem chunkN_val (b : Array UInt8) (i k : Word) (hk : k.toNat ≤ 19)
    (hi : i.toNat + k.toNat < 2 ^ 64) (hd : Digits b i.toNat k.toNat) :
    ∀ (j ch pw : Word), j ≤ k → ch.toNat = decN b i.toNat j.toNat → pw.toNat = 10 ^ j.toNat →
      (chunkN b i k j ch pw).1.toNat = decN b i.toNat k.toNat ∧
      (chunkN b i k j ch pw).2.toNat = 10 ^ k.toNat := by
  intro j ch pw
  fun_induction chunkN b i k j ch pw with
  | case1 j ch pw h ih =>
    intro hj hch hpw
    have hjk := UInt64.lt_iff_toNat_lt.mp h
    have hj1 : (j + 1).toNat = j.toNat + 1 := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]; simp
    have hij : (i + j).toNat = i.toNat + j.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hdj := hd j.toNat hjk
    have hlt := decN_lt b i.toNat (j.toNat + 1) (digits_mono _ _ _ _ hd (by omega))
    have h10 : 10 ^ (j.toNat + 1) ≤ 10 ^ 19 := Nat.pow_le_pow_right (by decide) (by omega)
    apply ih (UInt64.le_iff_toNat_le.mpr (by omega))
    · have hbyte : ((byteW b (i + j) - 48) &&& 255).toNat = (b.getD (i.toNat + j.toNat) 0).toNat - 48 := by
        simp only [byteW, hij]
        exact digit_word _ hdj.1 hdj.2
      have : decN b i.toNat j.toNat * 10 + ((b.getD (i.toNat + j.toNat) 0).toNat - 48) < 2 ^ 64 := by
        simp only [decN] at hlt; omega
      rw [hj1, UInt64.toNat_add, UInt64.toNat_mul, hbyte, hch, decN]
      simp only [UInt64.reduceToNat]
      omega
    · have : 10 ^ j.toNat * 10 < 2 ^ 64 := by rw [← Nat.pow_succ]; omega
      rw [hj1, UInt64.toNat_mul, hpw]; simp only [UInt64.reduceToNat]
      rw [Nat.mod_eq_of_lt this, Nat.pow_succ]
  | case2 j ch pw h =>
    intro hj hch hpw
    have : j = k := UInt64.le_antisymm hj (UInt64.not_lt.mp h)
    subst this
    exact ⟨hch, hpw⟩

/-! ## The multiply-add pass -/

theorem madHi_split (x w y : Word) :
    (x * w + y).toNat + (madHi x w y).toNat * 2 ^ 64 = x.toNat * w.toNat + y.toNat := by
  have hx := x.toNat_lt; have hw := w.toNat_lt; have hy := y.toNat_lt
  have hP : x.toNat * w.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  unfold madHi
  have e1 : (x * w + y).toNat = (x.toNat * w.toNat % 2 ^ 64 + y.toNat) % 2 ^ 64 := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]
  generalize x.toNat * w.toNat = P at hP e1 ⊢
  have hc : (x * w + y < y) ↔ 2 ^ 64 ≤ P % 2 ^ 64 + y.toNat := by
    rw [UInt64.lt_iff_toNat_lt, e1]; omega
  by_cases h : x * w + y < y
  · have := hc.mp h
    rw [ite_eq_left h, e1, UInt64.toNat_add, UInt64.toNat_ofNat']
    simp only [UInt64.reduceToNat]
    omega
  · have : P % 2 ^ 64 + y.toNat < 2 ^ 64 := Nat.lt_of_not_le fun h' => h (hc.mpr h')
    rw [ite_eq_right h, e1, UInt64.toNat_add, UInt64.toNat_ofNat']
    simp only [UInt64.reduceToNat]
    omega

theorem madW_val (o n w : Word) (ho : o.toNat < 2 ^ 41) :
    ∀ (m : Mem) (y i : Word),
      (o &&& 1099511627775).toNat + n.toNat ≤ (m.arr64 (tierA 0 (o >>> 40))).size →
      (m.arr64 (tierA 0 (o >>> 40))).size ≤ 2 ^ 40 → i ≤ n →
      PFrame m (madW m o n w y i).1 ∧
      (∀ x, x < o.toNat + i.toNat ∨ o.toNat + n.toNat ≤ x →
        (vpool (madW m o n w y i).1)[x]? = (vpool m)[x]?) ∧
      pv (vpool (madW m o n w y i).1) o.toNat n.toNat + (madW m o n w y i).2.toNat * wt n.toNat +
          pv (vpool m) o.toNat i.toNat * w.toNat =
        pv (vpool m) o.toNat n.toNat * w.toNat + pv (vpool m) o.toNat i.toNat +
          y.toNat * wt i.toNat := by
  intro m y i
  fun_induction madW m o n w y i with
  | case1 m y i h ih =>
    intro hS hS40 hi
    have hin := UInt64.lt_iff_toNat_lt.mp h
    have hI := tag_idx_lt o
    have hsp := tag_split o
    have htr := tag_tier_le o ho
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]; simp
    have hoi : (o + i).toNat = o.toNat + i.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hIi : ((o &&& 1099511627775) + i).toNat = (o &&& 1099511627775).toNat + i.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hb : o.toNat + i.toNat < (vpool m).size := by rw [vpool_size]; omega
    have hrd : prd m (o + i) = (vpool m)[o.toNat + i.toNat] := by
      rw [← vpool_getD m (o + i) (by omega), hoi, getElem?_pos (vpool m) _ hb, Option.getD_some]
    rw [hrd] at ih ⊢
    generalize hx : (vpool m)[o.toNat + i.toNat] = x at ih ⊢
    have hp1 : vpool (m.set64 (tierA 0 (o >>> 40)) ((o &&& 1099511627775) + i) (x * w + y)) =
        (vpool m).set! (o.toNat + i.toNat) (x * w + y) := by
      rw [vpool_stidx m o i _ ho (by rw [hIi]; omega) hS40 (by omega), hoi]
    obtain ⟨hf, hag, hv⟩ := ih (by rw [Mem.size_arr64_set64]; exact hS)
      (by rw [Mem.size_arr64_set64]; exact hS40) (UInt64.le_iff_toNat_le.mpr (by omega))
    rw [hp1, hi1] at hag hv
    refine ⟨PFrame.trans (PFrame.set64 _ _ _ (PFrame.refl _)) hf, fun z hz => ?_, ?_⟩
    · rw [hag z (by omega), Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      simp only [show o.toNat + i.toNat ≠ z by omega, ite_false]
    · have E1 := pv_set_mid (vpool m) o.toNat n.toNat i.toNat 0 (o.toNat + i.toNat) (x * w + y)
        (by simp) (by omega) hb
      have E2 := pv_set_succ (vpool m) o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat)
        (x * w + y) rfl rfl hb
      have E3 := madHi_split x w y
      have hw1 : wt (i.toNat + 1) = wt i.toNat * 2 ^ 64 := wt_succ _ _ rfl
      rw [hx] at E1
      simp only [wt_zero, Nat.mul_one] at E1
      rw [hw1] at hv
      generalize pv ((vpool m).set! (o.toNat + i.toNat) (x * w + y)) o.toNat n.toNat = A1 at E1 hv
      generalize pv ((vpool m).set! (o.toNat + i.toNat) (x * w + y)) o.toNat (i.toNat + 1) = B1 at E2 hv
      grind
  | case2 m y i h =>
    intro hS hS40 hi
    have : i = n := UInt64.le_antisymm hi (UInt64.not_lt.mp h)
    subst this
    refine ⟨PFrame.refl _, fun _ _ => rfl, ?_⟩
    simp only
    omega

/-! ## The chunk loop -/

/-- The top limb of `n` is zero: the slice denotes less than `wt (n - 1)`. -/
theorem pv_top_zero (p : Array Word) (o n : Nat) (hn : 0 < n) (h : p[o + (n - 1)]?.getD 0 = 0) :
    pv p o n < wt (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pv, Nat.add_sub_cancel] at h ⊢
  rw [h]; simpa using pv_lt p o k

theorem dec_step (b : Array UInt8) (c d top : Word) (ht : top.toNat < 2 ^ 41)
    (hdig : Digits b c.toNat (d.toNat - c.toNat)) (m : Mem) (n i : Word) (r : Mem × Word)
    (hr : r = madW m top n (chunkN b i (decK i d) 0 0 1).2 (chunkN b i (decK i d) 0 0 1).1 0)
    (hS40 : (m.arr64 (tierA 0 (top >>> 40))).size ≤ 2 ^ 40) (hci : c ≤ i) (h : i < d)
    (htn : (top &&& 1099511627775).toNat + n.toNat ≤ (m.arr64 (tierA 0 (top >>> 40))).size) :
    PFrame m r.1 ∧
    (∀ x, x < top.toNat ∨ top.toNat + n.toNat ≤ x → (vpool r.1)[x]? = (vpool m)[x]?) ∧
    c ≤ i + decK i d ∧ i + decK i d ≤ d ∧
    pv (vpool r.1) top.toNat n.toNat + r.2.toNat * wt n.toNat =
      pv (vpool m) top.toNat n.toNat * 10 ^ (decK i d).toNat + decN b i.toNat (decK i d).toNat ∧
    decN b c.toNat ((i + decK i d).toNat - c.toNat) =
      decN b c.toNat (i.toNat - c.toNat) * 10 ^ (decK i d).toNat + decN b i.toNat (decK i d).toNat ∧
    1 ≤ 10 ^ (decK i d).toNat := by
  obtain ⟨hk0, hkd, hik, hk19⟩ := decK_pos i d h
  have hci' := UInt64.le_iff_toNat_le.mp hci
  have hdi := UInt64.lt_iff_toNat_lt.mp h
  have hdk : Digits b i.toNat (decK i d).toNat := by
    have := digits_shift b c.toNat (i.toNat - c.toNat) (decK i d).toNat
      (digits_mono _ _ _ _ hdig (by omega))
    rwa [show c.toNat + (i.toNat - c.toNat) = i.toNat by omega] at this
  obtain ⟨hch, hpw⟩ := chunkN_val b i (decK i d) hk19 (by have := d.toNat_lt; omega) hdk 0 0 1
    (UInt64.le_iff_toNat_le.mpr (by simp)) (by simp [decN]) (by simp)
  obtain ⟨hf, hag, hv⟩ := madW_val top n (chunkN b i (decK i d) 0 0 1).2 ht m
    (chunkN b i (decK i d) 0 0 1).1 0 htn hS40 (UInt64.le_iff_toNat_le.mpr (by simp))
  subst hr
  simp only [UInt64.toNat_zero, Nat.add_zero, pv_zero, Nat.zero_mul, wt_zero, Nat.mul_one, hch, hpw] at hv hag
  refine ⟨hf, hag, UInt64.le_iff_toNat_le.mpr (by omega), UInt64.le_iff_toNat_le.mpr (by omega),
    by omega, ?_, Nat.one_le_pow _ _ (by decide)⟩
  have := decN_append b c.toNat (i.toNat - c.toNat) (decK i d).toNat
  rw [show c.toNat + (i.toNat - c.toNat) = i.toNat by omega,
    show i.toNat - c.toNat + (decK i d).toNat = (i + decK i d).toNat - c.toNat by omega] at this
  exact this

theorem decW_val (b : Array UInt8) (c d top : Word) (ht : top.toNat < 2 ^ 41)
    (hdig : Digits b c.toNat (d.toNat - c.toNat)) :
    ∀ (m : Mem) (n i : Word) (m' : Mem) (n' : Word),
      (m.arr64 (tierA 0 (top >>> 40))).size ≤ 2 ^ 40 → c ≤ i → i ≤ d →
      (top &&& 1099511627775).toNat + n.toNat ≤ (m.arr64 (tierA 0 (top >>> 40))).size →
      pv (vpool m) top.toNat n.toNat = decN b c.toNat (i.toNat - c.toNat) →
      Norm (vpool m) top.toNat n.toNat →
      decW b m top n i d = some (m', n') →
      PFrame m m' ∧ Agree (vpool m') (vpool m) top.toNat ∧
      (top &&& 1099511627775).toNat + n'.toNat ≤ (m'.arr64 (tierA 0 (top >>> 40))).size ∧
      pv (vpool m') top.toNat n'.toNat = decN b c.toNat (d.toNat - c.toNat) ∧
      Norm (vpool m') top.toNat n'.toNat := by
  have hI := tag_idx_lt top
  have hsp := tag_split top
  have htr := tag_tier_le top ht
  intro m n i
  fun_induction decW b m top n i d with
  | case4 m n i h =>
    intro m' n' hS40 hci hid htn hv hN heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have : i = d := UInt64.le_antisymm hid (UInt64.not_lt.mp h)
    subst this
    exact ⟨PFrame.refl _, fun _ _ => rfl, htn, hv, hN⟩
  | case1 m n i h hc hfull =>
    intro m' n' _ _ _ _ _ _ heq; cases heq
  | case2 m n i h hc hroom ih =>
    intro m' n' hS40 hci hid htn hv hN heq
    obtain ⟨hf, hag, hc1, hc2, hval, happ, _⟩ := dec_step b c d top ht hdig m n i _ rfl hS40 hci h htn
    generalize madW m top n (chunkN b i (decK i d) 0 0 1).2 (chunkN b i (decK i d) 0 0 1).1 0 = r
      at hf hag hval hc hroom ih heq
    obtain ⟨m₁, cy⟩ := r
    simp only at hf hag hval hc hroom ih heq
    have hsz : (m₁.arr64 (tierA 0 (top >>> 40))).size = (m.arr64 (tierA 0 (top >>> 40))).size :=
      PFrame.tsize _ hf
    have hlen : (m₁.len64 (tierA 0 (top >>> 40))).toNat = (m₁.arr64 (tierA 0 (top >>> 40))).size := by
      simp only [Mem.len64]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
    have hIn : ((top &&& 1099511627775) + n).toNat = (top &&& 1099511627775).toNat + n.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hroom' : (top &&& 1099511627775).toNat + n.toNat < (m₁.arr64 (tierA 0 (top >>> 40))).size := by
      rw [UInt64.le_iff_toNat_le, hlen, hIn] at hroom; omega
    have htn' : (top + n).toNat = top.toNat + n.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hn1 : (n + 1).toNat = n.toNat + 1 := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simp; omega)]; simp
    have hvb : top.toNat + n.toNat < (vpool m₁).size := by rw [vpool_size]; omega
    have hp2 : vpool (m₁.set64 (tierA 0 (top >>> 40)) ((top &&& 1099511627775) + n) cy) =
        (vpool m₁).set! (top.toNat + n.toNat) cy := by
      rw [vpool_stidx m₁ top n cy ht (by rw [hIn]; exact hroom') (by omega) (by omega), htn']
    have hE := pv_set_succ (vpool m₁) top.toNat n.toNat (n.toNat + 1) (top.toNat + n.toNat) cy
      rfl rfl hvb
    obtain ⟨hf', hag', htn'', hv', hN'⟩ := ih m' n' (by rw [Mem.size_arr64_set64]; omega)
      (UInt64.le_trans hci (UInt64.le_of_lt (by
        have := decK_pos i d h; exact UInt64.lt_iff_toNat_lt.mpr (by omega)))) hc2
      (by rw [Mem.size_arr64_set64, hn1]; omega)
      (by rw [hp2, hn1, hE, hval, hv, happ])
      (by
        intro _
        rw [hp2, hn1, Nat.add_sub_cancel, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        simp only [ite_true, hvb]
        simpa using hc)
      heq
    refine ⟨PFrame.trans (PFrame.trans hf (PFrame.set64 _ _ _ (PFrame.refl _))) hf',
      fun z hz => ?_, htn'', hv', hN'⟩
    rw [hag' z hz, hp2, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp only [show top.toNat + n.toNat ≠ z by omega, ite_false]
    exact hag z (.inl hz)
  | case3 m n i h hc ih =>
    intro m' n' hS40 hci hid htn hv hN heq
    obtain ⟨hf, hag, hc1, hc2, hval, happ, hpw1⟩ := dec_step b c d top ht hdig m n i _ rfl hS40 hci h htn
    generalize madW m top n (chunkN b i (decK i d) 0 0 1).2 (chunkN b i (decK i d) 0 0 1).1 0 = r
      at hf hag hval hc ih heq
    obtain ⟨m₁, cy⟩ := r
    simp only [ne_eq, Decidable.not_not] at hf hag hval hc ih heq
    subst hc
    simp only [UInt64.toNat_zero, Nat.zero_mul, Nat.add_zero] at hval
    have hsz : (m₁.arr64 (tierA 0 (top >>> 40))).size = (m.arr64 (tierA 0 (top >>> 40))).size :=
      PFrame.tsize _ hf
    have hv1 : pv (vpool m₁) top.toNat n.toNat =
        decN b c.toNat ((i + decK i d).toNat - c.toNat) := by rw [hval, hv, happ]
    obtain ⟨hf', hag', htn'', hv', hN'⟩ := ih m' n' (by omega) hc1 hc2 (by omega) hv1
      (by
        intro hn0 hz
        have h1 := pv_ge _ _ _ hn0 hN
        have h2 := pv_top_zero _ _ _ hn0 (by simpa using hz)
        have : pv (vpool m) top.toNat n.toNat ≤
            pv (vpool m) top.toNat n.toNat * 10 ^ (decK i d).toNat :=
          Nat.le_mul_of_pos_right _ hpw1
        omega)
      heq
    exact ⟨PFrame.trans hf hf', fun z hz => by rw [hag' z hz]; exact hag z (.inl hz),
      htn'', hv', hN'⟩

/-! ## `nat_dec` -/

theorem rdW_ctl_top (m : Mem) : rdW (m.arr64 CTL) 0 = m.top := by
  simp [rdW, Mem.top]

/-- **What `nat_dec(c, d)` does**, on digits `[c, d)`: the pool grows by the normalised limbs of
their decimal value, at the old top. -/
theorem natDecW_val (b : Array UInt8) (m m' : Mem) (c d : Word) (r : List Word)
    (hp : PoolOK m) (hcd : c ≤ d) (hdig : Digits b c.toNat (d.toNat - c.toNat))
    (h : natDecW b m c d = some (r, m')) :
    ∃ l, r = [m.top, l] ∧ Grows m m' ∧ SliceOK m' m.top l ∧
      Norm (vpool m') m.top.toNat l.toNat ∧
      pv (vpool m') m.top.toNat l.toNat = decN b c.toNat (d.toNat - c.toNat) := by
  have hsm := hp.small
  have h41 := hp.top41
  have hin := hp.2.2.2.2.2
  unfold natDecW at h
  rw [rdW_ctl_top] at h
  split at h
  · cases h
  cases hD : decW b m m.top 0 c d with
  | none => rw [hD] at h; cases h
  | some x =>
  obtain ⟨m₁, l⟩ := x
  rw [hD, finK_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hf, hag, htl, hv, hN⟩ := decW_val b c d m.top h41 hdig m 0 c m₁ l
    (Nat.le_of_lt (hsm.tier _)) (UInt64.le_refl _) hcd (by simpa using hin) (by simp [decN, pv])
    (fun h0 => by simp at h0) hD
  have hg := Grows.write m m₁ l hp hf hag (by rw [← PFrame.tsize _ hf]; exact htl)
  have hctl1 : 0 < (m₁.arr64 CTL).size := by rw [hf.ctl]; exact hp.2.1
  have htop' := Mem.top_set64 m₁ (m.top + l) hctl1
  refine ⟨l, rfl, hg, SliceOK.fresh hg htop', ?_, ?_⟩
  · rw [vpool_set64_ne _ _ _ _ (by decide)]; exact hN
  · rw [vpool_set64_ne _ _ _ _ (by decide)]; exact hv

/-! ## con-leche's `readNatAt` is the decimal value -/

section link
open ConLeche.Frontend ConAgua.Scan
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)

theorem decN_one (a : Array UInt8) (i : Nat) : decN a i 1 = (a.getD i 0).toNat - 48 := by
  simp [decN]

theorem uget_getD (i : USize) (h : i < b.usize) :
    (b.uget i (usizeInBounds b i h)).toNat = (b.data.getD i.toNat 0).toNat := by
  have := usizeInBounds' b i h
  simp only [Array.getD, ByteArray.uget]
  rw [dite_eq_left (show i.toNat < b.data.size from this)]
  rfl

/-- `skipDigits` ends a digit run, and `readNat` reads its decimal value. -/
theorem skipDigits_readNat (i : USize) : ∀ acc : Nat,
    i.toNat ≤ (skipDigits b i).toNat ∧
    Digits b.data i.toNat ((skipDigits b i).toNat - i.toNat) ∧
    readNat b i acc = acc * 10 ^ ((skipDigits b i).toNat - i.toNat) +
      decN b.data i.toNat ((skipDigits b i).toNat - i.toNat) := by
  fun_induction skipDigits b i with
  | case1 i h hd ih =>
    intro acc
    have hs := usizeStep b i h
    have hdg : 48 ≤ (b.data.getD i.toNat 0).toNat ∧ (b.data.getD i.toNat 0).toNat ≤ 57 := by
      simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
      rw [← uget_getD b i h]; exact ⟨hd.1, hd.2⟩
    obtain ⟨h1, h2, h3⟩ := ih (acc * 10 + ((b.data.getD i.toNat 0).toNat - 48))
    rw [hs] at h1 h2 h3
    have hr : readNat b i acc = readNat b (i + 1) (acc * 10 + ((b.data.getD i.toNat 0).toNat - 48)) := by
      conv => lhs; unfold readNat
      simp only [h, dite_eq_left, hd, ite_true]
      rw [uget_getD b i h]
    generalize hE : (skipDigits b (i + 1)).toNat = E at h1 h2 h3
    refine ⟨by omega, fun j hj => ?_, ?_⟩
    · rcases j with _ | j
      · simpa using hdg
      · have := h2 j (by omega); rwa [show i.toNat + 1 + j = i.toNat + (j + 1) by omega] at this
    · rw [hr, h3]
      have hk : E - i.toNat = 1 + (E - (i.toNat + 1)) := by omega
      rw [hk, decN_append, decN_one, show i.toNat + 1 = i.toNat + 1 from rfl, Nat.pow_add]
      generalize E - (i.toNat + 1) = K
      generalize (b.data.getD i.toNat 0).toNat - 48 = g
      generalize decN b.data (i.toNat + 1) K = D
      simp only [Nat.pow_one, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
  | case2 i h hd =>
    intro acc
    refine ⟨Nat.le_refl _, fun j hj => by omega, ?_⟩
    conv => lhs; unfold readNat
    simp [hd, decN]
  | case3 i h =>
    intro acc
    refine ⟨Nat.le_refl _, fun j hj => by omega, ?_⟩
    conv => lhs; unfold readNat
    rw [dite_eq_right h]; simp [decN]

theorem digit_u8 (x : UInt8) : 48 ≤ x.toNat → x.toNat ≤ 57 → (x - 48).toUInt64.toNat = x.toNat - 48 := by
  revert x; decide

include h64 hsize in
/-- `readNat64` on a digit run with no overflow reads its decimal value. -/
theorem readNat64_decN (e : USize) (he : e.toNat ≤ b.size) (i : USize) (acc : UInt64)
    (hie : i.toNat ≤ e.toNat) (hd : Digits b.data i.toNat (e.toNat - i.toNat))
    (hb : acc.toNat * 10 ^ (e.toNat - i.toNat) + decN b.data i.toNat (e.toNat - i.toNat) < 2 ^ 64) :
    (readNat64 b i e acc).toNat =
      acc.toNat * 10 ^ (e.toNat - i.toNat) + decN b.data i.toNat (e.toNat - i.toNat) := by
  fun_induction readNat64 b i e acc with
  | case1 i acc h hlt ih =>
    have hs := usizeStep b i h
    have hlt' := USize.lt_iff_toNat_lt.mp hlt
    have hdg := hd 0 (by omega)
    simp only [Nat.add_zero] at hdg
    have hbyte : (b.uget i (usizeInBounds b i h) - 48).toUInt64.toNat =
        (b.data.getD i.toNat 0).toNat - 48 := by
      rw [digit_u8 _ (by rw [uget_getD b i h]; exact hdg.1) (by rw [uget_getD b i h]; exact hdg.2),
        uget_getD b i h]
    have hk : e.toNat - i.toNat = 1 + (e.toNat - (i.toNat + 1)) := by omega
    rw [hk, decN_append, decN_one, Nat.pow_add, Nat.pow_one] at hb ⊢
    have hd' : Digits b.data (i.toNat + 1) (e.toNat - (i.toNat + 1)) := by
      have := digits_shift b.data i.toNat 1 (e.toNat - (i.toNat + 1)) (by rw [← hk]; exact hd)
      exact this
    generalize hK : e.toNat - (i.toNat + 1) = K at hb hd' ⊢
    generalize hg : (b.data.getD i.toNat 0).toNat - 48 = g at hb hbyte ⊢
    generalize hD : decN b.data (i.toNat + 1) K = D at hb ⊢
    have hp := Nat.one_le_pow K 10 (by decide)
    have e1 : (acc.toNat * 10 + g) * 10 ^ K + D = acc.toNat * (10 * 10 ^ K) + (g * 10 ^ K + D) := by
      simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    have hb2 : (acc.toNat * 10 + g) * 10 ^ K + D < 2 ^ 64 := by rw [e1]; exact hb
    have hle : acc.toNat * 10 + g ≤ (acc.toNat * 10 + g) * 10 ^ K := Nat.le_mul_of_pos_right _ hp
    have hacc : (acc * 10 + (b.uget i (usizeInBounds b i h) - 48).toUInt64).toNat = acc.toNat * 10 + g := by
      rw [UInt64.toNat_add, UInt64.toNat_mul, hbyte]
      simp only [UInt64.reduceToNat]
      omega
    have ih' := ih (by rw [hs]; omega) (by rw [hs, hK]; exact hd')
    rw [hs, hK, hD, hacc] at ih'
    rw [ih' hb2, e1]
  | case2 i acc h hlt =>
    have : e.toNat - i.toNat = 0 := by
      have : ¬ i.toNat < e.toNat := fun h' => hlt (USize.lt_iff_toNat_lt.mpr h'); omega
    rw [this]; simp [decN]
  | case3 i acc h =>
    have := usizeGe b i h64 (by omega) h
    have hb' : b.data.size = b.size := rfl
    have : e.toNat - i.toNat = 0 := by omega
    rw [this]; simp [decN]

include h64 hsize in
/-- **A `natVal` the scanner accepted**: its digits `[c, d)` are in the buffer and denote `n`. -/
@[refines_part ConLeche.Frontend.readNatAt "decimal digits into the limb pool"]
theorem natValR_decN (c d : Word) (n : Nat) (h : ConAgua.Front.FieldsLink.NatValR b c d n) :
    c < d ∧ d.toNat ≤ b.size ∧ Digits b.data c.toNat (d.toNat - c.toNat) ∧
      n = decN b.data c.toNat (d.toNat - c.toNat) := by
  obtain ⟨v, e, rfl, rfl, hve, hsk, hrd⟩ := h
  have hlt := USize.lt_iff_toNat_lt.mp hve
  obtain ⟨_, hdg, hrn⟩ := skipDigits_readNat b v 0
  rw [hsk] at hdg hrn
  simp only [Nat.zero_mul, Nat.zero_add] at hrn
  have he : e.toNat ≤ b.size := by
    have h1 := skipDigits_toNat_eq b h64 (by omega) v
    rw [hsk] at h1
    have h2 := L.Scan.Leaves.skipDigitsN_bounds b.data v.toNat (by omega)
    have h3 := L.Scan.Leaves.skipDigitsN_le b.data v.toNat (by omega)
    have : b.data.size = b.size := rfl
    omega
  simp only [USize.toNat_toUInt64]
  refine ⟨(lt_toUInt64_iff _ _).mp hve, he, hdg, ?_⟩
  rw [← hrd, readNatAt]
  split
  · rename_i h18
    have h18' : e.toNat - v.toNat ≤ 18 := by
      rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ (USize.le_of_lt hve)] at h18
      simpa using h18
    have hlt18 := decN_lt b.data v.toNat _ hdg
    have : 10 ^ (e.toNat - v.toNat) ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) h18'
    rw [readNat64_decN b h64 hsize e he v 0 (by omega) hdg (by simp; omega)]
    simp
  · exact hrn

end link

/-! ## The triple -/

end L.Front
