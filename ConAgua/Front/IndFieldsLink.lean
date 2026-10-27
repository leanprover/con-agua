import ConAgua.Front.IndFieldsSpec
import ConAgua.Front.FieldsDeclLink
import ConAgua.Front.IndRel
import ConAgua.Scan.LeafLink
import ConAgua.Scan.Link
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The fields pass of an `inductive` line, linked to con-leche

`indFields_link`: on con-leche's `ok` path (`scanIndDecl b v = .ok (.ind tys cts rcs) e`), a
successful `ind_fields(v)` (its model `indFieldsW`) leaves records in `IFR`/`IFL` related to
`tys`, `cts`, `rcs` by `IndFR` (`IndRel.lean`), and writes nothing but `IFR`/`IFL`.

As in `FieldsDeclLink.lean`, one generic theorem (`iobj_link`) relates `ind_obj`'s loop to a
con-leche record loop of the common shape (`IObjLoop`), given, at each key, that `ind_member`
(`memberW`) keeps a relation `R` between con-leche's loop state and the memory; each record kind
instantiates it, bottom up (rule, recursor, constructor, type, block), with the lists between them
(`ilist_link`, one generic theorem for con-leche's four list loops). The memory side is a growth
relation (`IGrow`: `IFR`/`IFL` tops grow, the words below the old tops are kept except in the
record being read) and the record's slots read through `sv`.
-/

open L.Arena
open ConLeche.Frontend ConAgua.Scan ConAgua.Scan.RecordsLink
open ConAgua.Front.FieldsLink
open L.Front.Fields (rdNatN NONE rdLoopN listN itemsN)
open L.Front (lsCntN)
open L.Scan.Utf8 (byteW)
open L.Scan.Member (nextMemberN)
open L.Scan.Leaves (numEndN skipDigitsN keyEndN)


namespace L.Front.Ind

/-! ## Words of the scratch arrays -/

theorem wd_set64 (m : Mem) (a c : ArrId) (i x : Word) (j : Nat) :
    wd (m.set64 a i x) c j = if c = a ∧ i.toNat = j ∧ j < (m.arr64 a).size then x else wd m c j := by
  by_cases hc : c = a
  · subst hc
    simp only [wd, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases h : i.toNat = j
    · subst h
      by_cases h2 : i.toNat < (m.arr64 c).size
      · simp [h2]
      · simp [h2]
    · simp [h]
  · simp [wd, Mem.arr64_set64_ne _ _ _ _ _ hc, hc]

theorem wd_set64_ne (m : Mem) (a c : ArrId) (i x : Word) (j : Nat) (h : c ≠ a) :
    wd (m.set64 a i x) c j = wd m c j := by
  rw [wd_set64, ite_eq_right (by simp [h])]

theorem wd_set64_same (m : Mem) (a : ArrId) (i x : Word) (h : i.toNat < (m.arr64 a).size) :
    wd (m.set64 a i x) a i.toNat = x := by
  rw [wd_set64, ite_eq_left ⟨rfl, rfl, h⟩]

theorem wd_set64_other (m : Mem) (a : ArrId) (i x : Word) (j : Nat) (h : i.toNat ≠ j) :
    wd (m.set64 a i x) a j = wd m a j := by
  rw [wd_set64, ite_eq_right (by simp [h])]

theorem size_set64' (m : Mem) (a c : ArrId) (i x : Word) :
    ((m.set64 a i x).arr64 c).size = (m.arr64 c).size := by
  by_cases hc : c = a
  · subst hc; simp [Mem.arr64_set64_same]
  · rw [Mem.arr64_set64_ne _ _ _ _ _ hc]

theorem rdW_wd (m : Mem) (a : ArrId) (i : Word) : rdW (m.arr64 a) i = wd m a i.toNat := rfl

/-! ## Numbers: below `10^18` -/

theorem skipDigitsN_digits (b : Array UInt8) (i : Nat) :
    ∀ j, i ≤ j → j < skipDigitsN b i → ∃ h : j < b.size, 48 ≤ b[j] ∧ b[j] ≤ 57 := by
  fun_induction skipDigitsN b i with
  | case1 i h hd ih =>
    intro j hj1 hj2
    by_cases hij : j = i
    · subst hij; exact ⟨h, hd⟩
    · exact ih j (by omega) hj2
  | case2 i h hd => intro j hj1 hj2; omega
  | case3 i h => intro j hj1 hj2; omega

theorem numEndN_digits (b : Array UInt8) (i : Nat) :
    ∀ j, i ≤ j → j < numEndN b i → ∃ h : j < b.size, 48 ≤ b[j] ∧ b[j] ≤ 57 := by
  intro j hj1 hj2
  unfold numEndN at hj2
  dsimp only at hj2
  split at hj2
  · omega
  split at hj2
  · omega
  · exact skipDigitsN_digits b i j hj1 hj2

theorem rdLoopN_lt (b : Array UInt8) (e : Word) (v x : Word) (K : Nat)
    (hd : ∀ j, v.toNat ≤ j → j < e.toNat → ∃ h : j < b.size, 48 ≤ b[j] ∧ b[j] ≤ 57)
    (hx : x.toNat < 10 ^ K) (hk : K + (e.toNat - v.toNat) ≤ 18) :
    (rdLoopN b v e x).toNat < 10 ^ (K + (e.toNat - v.toNat)) := by
  induction hm : e.toNat - v.toNat generalizing v x K with
  | zero =>
    rw [L.Front.Fields.rdLoopN_stop _ _ _ _ (by rw [UInt64.lt_iff_toNat_lt]; omega)]
    simpa using hx
  | succ k ih =>
    have hlt : v < e := by rw [UInt64.lt_iff_toNat_lt]; omega
    rw [L.Front.Fields.rdLoopN_step _ _ _ _ hlt]
    have hv1 : (v + 1).toNat = v.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; have := e.toNat_lt; omega
    obtain ⟨hb, d1, d2⟩ := hd v.toNat (Nat.le_refl _) (by omega)
    have hbw : byteW b v = b[v.toNat].toUInt64 := by simp [byteW, hb]
    have hdig : ((byteW b v - 48) &&& 255).toNat = b[v.toNat].toNat - 48 := by
      rw [hbw]
      have h1 : (48 : UInt8) ≤ b[v.toNat] := d1
      have h2 : b[v.toNat] ≤ 57 := d2
      have h1' : 48 ≤ b[v.toNat].toNat := h1
      have h2' : b[v.toNat].toNat ≤ 57 := h2
      rw [UInt64.toNat_and, UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le]; simp; omega)]
      simp
      rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega
    have hK : 10 ^ K ≤ 10 ^ 17 := Nat.pow_le_pow_right (by decide) (by omega)
    have hx' : (x * 10 + ((byteW b v - 48) &&& 255)).toNat < 10 ^ (K + 1) := by
      have h10 : (x * 10).toNat = x.toNat * 10 := by
        rw [UInt64.toNat_mul]; simp; omega
      rw [UInt64.toNat_add, h10, hdig]
      have : b[v.toNat].toNat - 48 ≤ 9 := by
        have h2 : b[v.toNat] ≤ 57 := d2
        have h2' : b[v.toNat].toNat ≤ 57 := h2
        omega
      rw [Nat.pow_succ]
      have : x.toNat * 10 + (b[v.toNat].toNat - 48) < 2 ^ 64 := by
        have : (10 : Nat) ^ 17 * 10 < 2 ^ 64 := by decide
        omega
      rw [Nat.mod_eq_of_lt this]; omega
    have := ih (v + 1) _ (K + 1) (fun j h1 h2 => hd j (by omega) h2) hx' (by omega) (by omega)
    rwa [show K + 1 + k = K + (k + 1) by omega] at this

/-- A number `read_nat` reads over digits, if it is not `NONE`, has at most 18 digits. -/
theorem rdNatN_lt (b : Array UInt8) (v e : Word) (hv : v.toNat < 2 ^ 63)
    (hd : ∀ j, v.toNat ≤ j → j < e.toNat → ∃ h : j < b.size, 48 ≤ b[j] ∧ b[j] ≤ 57)
    (hne : rdNatN b v e ≠ NONE) : (rdNatN b v e).toNat < 10 ^ 18 := by
  unfold rdNatN at hne ⊢
  split at hne
  · exact absurd rfl hne
  rename_i h18
  rw [ite_eq_right h18]
  have h18' : e.toNat ≤ v.toNat + 18 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h18; simp at h18; omega
  have := rdLoopN_lt b e v 0 0 hd (by simp) (by omega)
  have hp : 10 ^ (0 + (e.toNat - v.toNat)) ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-! ## Growth of the scratch arrays -/

/-- The scratch arrays have fewer than `2^63` words and their tops lie inside them. -/
def Room (m : Mem) : Prop :=
  (m.arr64 IFR).size < 2 ^ 63 ∧ (m.arr64 IFL).size < 2 ^ 63 ∧
    topN m IFR < (m.arr64 IFR).size ∧ topN m IFL < (m.arr64 IFL).size

/-- **Growth** from `m` to `m'`: only `IFR`/`IFL` written, their tops grew, and the words up to
the old tops are kept, except the words `[x0, x1)` of `xa` (the record being read). -/
structure IGrow (m m' : Mem) (xa : ArrId) (x0 x1 : Nat) : Prop where
  fr : MemFrame [IFR, IFL] [] m m'
  top : ∀ a, a = IFR ∨ a = IFL → topN m a ≤ topN m' a
  keep : ∀ a, a = IFR ∨ a = IFL → ∀ i, 1 ≤ i → i ≤ topN m a → ¬ (a = xa ∧ x0 ≤ i ∧ i < x1) →
    wd m' a i = wd m a i

/-- Growth with nothing excepted. -/
abbrev Grow (m m' : Mem) : Prop := IGrow m m' IFR 0 0

theorem IGrow.refl (m : Mem) (xa : ArrId) (x0 x1 : Nat) : IGrow m m xa x0 x1 :=
  ⟨MemFrame.refl _ _ _, fun _ _ => Nat.le_refl _, fun _ _ _ _ _ _ => rfl⟩

theorem IGrow.trans {m₁ m₂ m₃ : Mem} {xa : ArrId} {x0 x1 : Nat} (h₁ : IGrow m₁ m₂ xa x0 x1)
    (h₂ : IGrow m₂ m₃ xa x0 x1) : IGrow m₁ m₃ xa x0 x1 :=
  ⟨h₁.fr.trans h₂.fr, fun a ha => Nat.le_trans (h₁.top a ha) (h₂.top a ha),
    fun a ha i h1 h2 h3 =>
      (h₂.keep a ha i h1 (Nat.le_trans h2 (h₁.top a ha)) h3).trans (h₁.keep a ha i h1 h2 h3)⟩

theorem Grow.ex {m m' : Mem} (h : Grow m m') (xa : ArrId) (x0 x1 : Nat) : IGrow m m' xa x0 x1 :=
  ⟨h.fr, h.top, fun a ha i h1 h2 _ => h.keep a ha i h1 h2 (by omega)⟩

theorem Room.sizes {m m' : Mem} (hf : MemFrame [IFR, IFL] [] m m') :
    (m'.arr64 IFR).size = (m.arr64 IFR).size ∧ (m'.arr64 IFL).size = (m.arr64 IFL).size :=
  ⟨hf.2.2.1 IFR, hf.2.2.1 IFL⟩

/-- A write into `IFR`/`IFL` at a word other than the top. -/
theorem grow_set (m : Mem) (A : ArrId) (hA : A = IFR ∨ A = IFL) (i x : Word) (x0 x1 : Nat)
    (h1 : 1 ≤ i.toNat) (hx0 : x0 ≤ i.toNat) (hx1 : i.toNat < x1) :
    IGrow m (m.set64 A i x) A x0 x1 ∧ (Room m → Room (m.set64 A i x)) ∧
      (∀ c, topN (m.set64 A i x) c = topN m c) := by
  have hCTL : A ≠ CTL := by rcases hA with rfl | rfl <;> decide
  have ht : ∀ c, topN (m.set64 A i x) c = topN m c := by
    intro c; simp only [topN, wd_set64]; rw [ite_eq_right (by omega)]
  have hfr : MemFrame [IFR, IFL] [] m (m.set64 A i x) :=
    (MemFrame.set64 m A hCTL i x).mono (by rcases hA with rfl | rfl <;> simp) (by simp)
  refine ⟨⟨hfr, fun a _ => by rw [ht]; exact Nat.le_refl _, fun a ha j hj1 hj2 hj3 => ?_⟩, fun hR => ?_, ht⟩
  · rw [wd_set64]
    rw [ite_eq_right]
    rintro ⟨rfl, rfl, -⟩
    exact hj3 ⟨rfl, hx0, hx1⟩
  · obtain ⟨r1, r2, r3, r4⟩ := hR
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [ht, size_set64'] <;> assumption

/-- **An allocation** of `n` words of `a` (`IFR` or `IFL`): at the old top `+ 1`, the top moved by
`n`, inside the array; nothing else changes. -/
theorem allocW_facts (m m' : Mem) (a : ArrId) (ha : a = IFR ∨ a = IFL) (n o : Word) (hR : Room m)
    (h : allocW m a n = some (o, m')) :
    o.toNat = topN m a + 1 ∧ topN m' a = topN m a + n.toNat ∧ Room m' ∧ Grow m m' ∧
      (∀ c, c ≠ a → topN m' c = topN m c) ∧ o.toNat + n.toNat ≤ (m.arr64 a).size ∧
      (∀ c, c ≠ a → m'.arr64 c = m.arr64 c) := by
  obtain ⟨r1, r2, r3, r4⟩ := hR
  have hsz : (m.arr64 a).size < 2 ^ 63 := by rcases ha with rfl | rfl <;> assumption
  have htop : topN m a < (m.arr64 a).size := by rcases ha with rfl | rfl <;> assumption
  have hCTL : a ≠ CTL := by rcases ha with rfl | rfl <;> decide
  unfold allocW at h
  by_cases h0 : m.len64 a = 0
  · rw [ite_eq_left h0] at h; cases h
  rw [ite_eq_right h0] at h
  by_cases h1 : m.len64 a < rdW (m.arr64 a) 0 + 1
  · rw [ite_eq_left h1] at h; cases h
  rw [ite_eq_right h1] at h
  by_cases h2 : m.len64 a - (rdW (m.arr64 a) 0 + 1) < n
  · rw [ite_eq_left h2] at h; cases h
  rw [ite_eq_right h2] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hlen : (m.len64 a).toNat = (m.arr64 a).size :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have ht : (rdW (m.arr64 a) 0).toNat = topN m a := rfl
  have ho : (rdW (m.arr64 a) 0 + 1).toNat = topN m a + 1 := by
    rw [UInt64.toNat_add, ht, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
  have hn : n.toNat ≤ (m.arr64 a).size - (topN m a + 1) := by
    have := UInt64.not_lt.mp h2
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp h1), hlen, ho] at this
    exact this
  have hnew : (rdW (m.arr64 a) 0 + 1 - 1 + n).toNat = topN m a + n.toNat := by
    have : rdW (m.arr64 a) 0 + 1 - 1 + n = rdW (m.arr64 a) 0 + n := by
      rw [UInt64.add_sub_cancel]
    rw [this, UInt64.toNat_add, ht, Nat.mod_eq_of_lt (by omega)]
  have hs0 : 0 < (m.arr64 a).size := by omega
  have htop' : ∀ c, topN (m.set64 a 0 (rdW (m.arr64 a) 0 + 1 - 1 + n)) c =
      if c = a then topN m a + n.toNat else topN m c := by
    intro c
    simp only [topN, wd_set64]
    by_cases hc : c = a
    · subst hc; rw [ite_eq_left ⟨rfl, rfl, hs0⟩, ite_eq_left rfl, hnew]; rfl
    · rw [ite_eq_right (by simp [hc]), ite_eq_right hc]
  have hfr : MemFrame [IFR, IFL] [] m (m.set64 a 0 (rdW (m.arr64 a) 0 + 1 - 1 + n)) :=
    (MemFrame.set64 m a hCTL _ _).mono (by rcases ha with rfl | rfl <;> simp) (by simp)
  refine ⟨ho, by rw [htop', ite_eq_left rfl], ?_, ⟨hfr, fun c hc => ?_, fun c hc j hj1 hj2 hj3 => ?_⟩,
    fun c hc => by rw [htop', ite_eq_right hc], by omega,
    fun c hc => Mem.arr64_set64_ne _ _ _ _ _ hc⟩
  · refine ⟨by rw [size_set64']; exact r1, by rw [size_set64']; exact r2, ?_, ?_⟩
    · rw [htop', size_set64']; split
      · rename_i hc; subst hc; omega
      · exact r3
    · rw [htop', size_set64']; split
      · rename_i hc; subst hc; omega
      · exact r4
  · rw [htop']; split
    · rename_i hc'; subst hc'; omega
    · exact Nat.le_refl _
  · rw [wd_set64, ite_eq_right (by rintro ⟨-, h5, -⟩; simp at h5; omega)]

/-- What an allocation leaves alone, without room assumptions. -/
theorem allocW_facts' (m m' : Mem) (a : ArrId) (n o : Word) (h : allocW m a n = some (o, m')) :
    ∀ c, c ≠ a → m'.arr64 c = m.arr64 c := by
  unfold allocW at h
  by_cases h0 : m.len64 a = 0
  · rw [ite_eq_left h0] at h; cases h
  rw [ite_eq_right h0] at h
  by_cases h1 : m.len64 a < rdW (m.arr64 a) 0 + 1
  · rw [ite_eq_left h1] at h; cases h
  rw [ite_eq_right h1] at h
  by_cases h2 : m.len64 a - (rdW (m.arr64 a) 0 + 1) < n
  · rw [ite_eq_left h2] at h; cases h
  rw [ite_eq_right h2] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact fun c hc => Mem.arr64_set64_ne _ _ _ _ _ hc

theorem pushLW_facts (m m' : Mem) (x o : Word) (hR : Room m) (h : pushLW m x = some (o, m')) :
    o.toNat = topN m IFL + 1 ∧ topN m' IFL = topN m IFL + 1 ∧ Room m' ∧ Grow m m' ∧
      wd m' IFL (topN m IFL + 1) = x ∧ m'.arr64 IFR = m.arr64 IFR := by
  unfold pushLW at h
  rcases ha : allocW m IFL 1 with _ | ⟨o₁, m₁⟩ <;> simp only [ha, pushK, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a1, a2, a3, a4, -, a6, a7⟩ := allocW_facts m m₁ IFL (.inr rfl) 1 o₁ hR ha
  have h1 : (1 : Word).toNat = 1 := rfl
  rw [h1] at a2 a6
  have hin : o₁.toNat < (m₁.arr64 IFL).size := by rw [a4.fr.2.2.1 IFL]; omega
  obtain ⟨g1, g2, g3⟩ := grow_set m₁ IFL (.inr rfl) o₁ x (topN m IFL + 1) (topN m IFL + 2)
    (by omega) (by omega) (by omega)
  refine ⟨a1, by rw [g3, a2], g2 a3, ⟨a4.fr.trans g1.fr, fun c hc => Nat.le_trans (a4.top c hc) (g1.top c hc),
    fun c hc j hj1 hj2 hj3 => ?_⟩, by rw [← a1]; exact wd_set64_same _ _ _ _ hin, ?_⟩
  · rw [g1.keep c hc j hj1 (Nat.le_trans hj2 (a4.top c hc)) (fun hh => by obtain ⟨hc', h5, -⟩ := hh; rw [hc'] at hj2; omega)]
    exact a4.keep c hc j hj1 hj2 hj3
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    exact a7 IFR (by decide)

/-! ## `ifl_ids` -/

theorem idsLoopM_facts (b : Array UInt8) : ∀ (m : Mem) (i : Word) (m' : Mem),
    idsLoopM b m i = some m' → Room m →
    topN m' IFL = topN m IFL + (itemsN b i).length ∧ Room m' ∧ Grow m m' ∧
      m'.arr64 IFR = m.arr64 IFR ∧
      (∀ k (hk : k < (itemsN b i).length), wd m' IFL (topN m IFL + 1 + k) = (itemsN b i)[k]) ∧
      (∀ x ∈ itemsN b i, x ≠ NONE) := by
  intro m i
  fun_induction idsLoopM b m i with
  | case1 m i h1 h2 =>
    intro m' h hR; cases h
    rw [L.Front.Fields.itemsN_close _ _ h1 h2]
    exact ⟨rfl, hR, IGrow.refl _ _ _ _, rfl, fun k hk => by simp at hk, by simp⟩
  | case2 m i h1 h2 h3 h4 h5 => intro m' h; cases h
  | case3 m i h1 h2 h3 h4 h5 h6 => intro m' h; cases h
  | case4 m i h1 h2 h3 h4 h5 o m₁ h6 ih =>
    intro m' h hR
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := pushLW_facts m m₁ _ o hR h6
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih m' h p3
    rw [L.Front.Fields.itemsN_digit _ _ h1 h2 h3 h4]
    refine ⟨by rw [i1, p2]; simp; omega, i2, p4.trans i3, i4.trans p6, fun k hk => ?_, ?_⟩
    · cases k with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [i3.keep IFL (.inr rfl) _ (by omega) (by rw [p2]; exact Nat.le_refl _) (by simp), p5]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [← i5 k (by simpa using hk), p2]; congr 1; omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact h5
      · exact i6 x hx
  | case5 m i h1 h2 h3 h4 => intro m' h; cases h
  | case6 m i h1 h2 h3 ih =>
    intro m' h hR
    rw [L.Front.Fields.itemsN_other _ _ h1 h2 h3]
    exact ih m' h hR
  | case7 m i h1 =>
    intro m' h hR; cases h
    rw [L.Front.Fields.itemsN_end _ _ h1]
    exact ⟨rfl, hR, IGrow.refl _ _ _ _, rfl, fun k hk => by simp at hk, by simp⟩

theorem lsCntN_len (b : Array UInt8) : ∀ (i cnt : Word),
    cnt.toNat + (itemsN b i).length < 2 ^ 64 →
    (lsCntN b i cnt).toNat = cnt.toNat + (itemsN b i).length := by
  intro i cnt
  fun_induction lsCntN b i cnt with
  | case1 i cnt h1 h2 => intro _; rw [L.Front.Fields.itemsN_close _ _ h1 h2]; rfl
  | case2 i cnt h1 h2 h3 h4 ih =>
    intro hlt
    rw [L.Front.Fields.itemsN_digit _ _ h1 h2 h3 h4] at hlt ⊢
    simp only [List.length_cons] at hlt ⊢
    have hc : (cnt + 1).toNat = cnt.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    rw [ih (by rw [hc]; omega), hc]; omega
  | case3 i cnt h1 h2 h3 h4 => intro _; rw [L.Front.Fields.itemsN_noprog _ _ h1 h2 h3 h4]; rfl
  | case4 i cnt h1 h2 h3 ih =>
    intro hlt; rw [L.Front.Fields.itemsN_other _ _ h1 h2 h3] at hlt ⊢; exact ih hlt
  | case5 i cnt h1 => intro _; rw [L.Front.Fields.itemsN_end _ _ h1]; rfl

/-- **`ifl_ids(v)`**: the items of the list at `v` appended to `IFL` above its top. -/
theorem idsM_facts (b : Array UInt8) (m m' : Mem) (v : Word) (hR : Room m)
    (h : idsM b m v = some m') :
    topN m' IFL = topN m IFL + (listN b v).length ∧ Room m' ∧ Grow m m' ∧
      m'.arr64 IFR = m.arr64 IFR ∧
      (∀ k (hk : k < (listN b v).length), wd m' IFL (topN m IFL + 1 + k) = (listN b v)[k]) ∧
      (∀ x ∈ listN b v, x ≠ NONE) ∧
      (rdW (m.arr64 IFL) 0 + 1).toNat = topN m IFL + 1 ∧
      (lsCntN b (v + 1) 0).toNat = (listN b v).length := by
  unfold idsM at h
  rcases ha : allocW m IFL 0 with _ | ⟨o, m₁⟩ <;> simp only [ha, idsK0, reduceCtorEq] at h
  obtain ⟨a1, a2, a3, a4, -, -, a7⟩ := allocW_facts m m₁ IFL (.inr rfl) 0 o hR ha
  have a2' : topN m₁ IFL = topN m IFL := by rw [a2]; rfl
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := idsLoopM_facts b m₁ (v + 1) m' h a3
  have hlist : listN b v = itemsN b (v + 1) := rfl
  have hs := i2.2.2.2
  have hs2 := i2.2.1
  refine ⟨by rw [hlist, i1, a2'], i2, a4.trans i3, i4.trans (a7 IFR (by decide)),
    fun k hk => by rw [← a2']; exact i5 k hk, i6, ?_, ?_⟩
  · have ht : (rdW (m.arr64 IFL) 0).toNat = topN m IFL := rfl
    have := hR.2.2.2
    have := hR.2.1
    rw [UInt64.toNat_add, ht, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
  · rw [lsCntN_len b _ _ (by rw [hlist] at *; simp; omega)]; simp [hlist]

/-! ## The generic record loop -/

/-- The shape of a con-leche record loop `F` (state `σ`, record `α`), on its `ok` path, against
`ind_obj`'s loop on the record of kind `kind` at `p`: `R seen st m` relates con-leche's state to
the memory, `Fin d m` the record to it. -/
structure IObjLoop (b : ByteArray) {σ α : Type} (F : USize → Bool → UInt32 → σ → ScanRes α)
    (kind p : Word) (R : UInt32 → σ → Mem → Prop) (Fin : α → Mem → Prop) : Prop where
  stop : ∀ i w seen st d e, ¬ i < b.usize → F i w seen st ≠ .ok d e
  ws : ∀ i w seen st, i < b.usize → isWs (byteAt b i) = true → F i w seen st = F (i + 1) w seen st
  close : ∀ i w seen st m d e, i < b.usize → byteAt b i = 125 → F i w seen st = .ok d e →
    R seen st m → e = i + 1 ∧ Fin d m
  comma : ∀ i w seen st d e, i < b.usize → byteAt b i = 44 → F i w seen st = .ok d e →
    w = false ∧ F (i + 1) true seen st = .ok d e
  quote : ∀ i w seen st d e, i < b.usize → byteAt b i = 34 → F i w seen st = .ok d e →
    w = true ∧ keyEnd b (i + 1) ≠ 0 ∧ valueAt b i (keyEnd b (i + 1)) ≠ i
  key : ∀ i seen st m d e e' m', i < b.usize → byteAt b i = 34 → keyEnd b (i + 1) ≠ 0 →
    valueAt b i (keyEnd b (i + 1)) ≠ i → (valueAt b i (keyEnd b (i + 1))).toNat ≤ b.size →
    F i true seen st = .ok d e → R seen st m →
    memberW b.data m kind p i.toUInt64
      (UInt64.ofNat (keyAt b i (keyEnd b (i + 1) - (i + 1))).ctorIdx)
      (valueAt b i (keyEnd b (i + 1))).toUInt64 = some (e', m') → i.toUInt64 < e' →
    ∃ (eu : USize) (seen' : UInt32) (st' : σ), eu.toUInt64 = e' ∧ F eu false seen' st' = .ok d e ∧
      R seen' st' m'
  other : ∀ i w seen st d e, i < b.usize → isWs (byteAt b i) = false → byteAt b i ≠ 125 →
    byteAt b i ≠ 44 → byteAt b i ≠ 34 → F i w seen st ≠ .ok d e

section generic
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

omit h64 hsize in
theorem objLoopW_congr (m : Mem) (kind p i w j w' : Word)
    (h : nextMemberN b.data i w = nextMemberN b.data j w') :
    objLoopW b.data m kind p i w = objLoopW b.data m kind p j w' := by
  conv => lhs; rw [objLoopW]
  conv => rhs; rw [objLoopW]
  simp only [h]

/-- **`ind_obj`'s loop against a con-leche record loop**: on con-leche's `ok` path, the loop's
end is con-leche's and the record relation holds of the memory after. -/
theorem iobj_link {σ α : Type} (F : USize → Bool → UInt32 → σ → ScanRes α) (kind p : Word)
    (R : UInt32 → σ → Mem → Prop) (Fin : α → Mem → Prop) (H : IObjLoop b F kind p R Fin)
    (i : USize) (w : Bool) (seen : UInt32) (st : σ) (m : Mem) (d : α) (e : USize) (e' : Word)
    (m' : Mem) (h : F i w seen st = .ok d e) (hR : R seen st m)
    (hm : objLoopW b.data m kind p i.toUInt64 (bw w) = some (e', m')) :
    e' = e.toUInt64 ∧ Fin d m' := by
  by_cases hi : i < b.usize
  · have hin := usizeInBounds b i hi
    by_cases hws : isWs (byteAt b i) = true
    · rw [H.ws i w seen st hi hws] at h
      rw [objLoopW_congr b h64 hsize _ _ _ _ _ _ _ (nm_ws b h64 hsize i _ hi hws)] at hm
      exact iobj_link F kind p R Fin H (i + 1) w seen st m d e e' m' h hR hm
    by_cases h125 : byteAt b i = 125
    · obtain ⟨rfl, hF⟩ := H.close i w seen st m d e hi h125 h hR
      rw [objLoopW_close _ _ _ _ _ _ (by rw [nm_close b h64 hsize i _ hi hws h125]),
        nm_close b h64 hsize i _ hi hws h125] at hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
      exact ⟨(succ_toUInt64 h64 i).symm, hF⟩
    by_cases h44 : byteAt b i = 44
    · obtain ⟨rfl, h'⟩ := H.comma i w seen st d e hi h44 h
      simp only [bw, Bool.false_eq_true, ite_false] at hm
      rw [objLoopW_congr b h64 hsize _ _ _ _ _ _ _ (nm_comma b h64 hsize i hi hws h44)] at hm
      exact iobj_link F kind p R Fin H (i + 1) true seen st m d e e' m' h' hR
        (by simpa [bw] using hm)
    by_cases h34 : byteAt b i = 34
    · obtain ⟨rfl, hk, hv⟩ := H.quote i w seen st d e hi h34 h
      have hn := nm_key b h64 hsize i hi h34 hk hv
      have hvle : (valueAt b i (keyEnd b (i + 1))).toNat ≤ b.size := by
        have := L.Scan.Member.nextMemberN_val_le b.data i.toUInt64 1
          (by have : b.data.size = b.size := rfl; omega) (by rw [hn])
        rw [hn] at this; simpa using this
      simp only [bw, ite_true] at hm
      rw [objLoopW_key _ _ _ _ _ _ (by rw [hn]; exact (by decide : (2 : Word) ≠ 0))
        (by rw [hn]; exact (by decide : (2 : Word) ≠ 1))] at hm
      simp only [hn] at hm
      cases hmem : memberW b.data m kind p i.toUInt64
          (UInt64.ofNat (keyAt b i (keyEnd b (i + 1) - (i + 1))).ctorIdx)
          (valueAt b i (keyEnd b (i + 1))).toUInt64 with
      | none => rw [hmem, objK_none] at hm; cases hm
      | some em =>
        obtain ⟨e₁, m₁⟩ := em
        rw [hmem, objK_some] at hm
        split at hm
        · rename_i hlt
          obtain ⟨eu, seen', st', heu, h', hR'⟩ :=
            H.key i seen st m d e e₁ m₁ hi h34 hk hv hvle h hR hmem hlt
          subst heu
          have hiu : i < eu := (lt_toUInt64_iff _ _).mpr hlt
          exact iobj_link F kind p R Fin H eu false seen' st' m₁ d e e' m' h' hR'
            (by simpa [bw] using hm)
        · cases hm
    · exact absurd h (H.other i w seen st d e hi (by simpa using hws) h125 h44 h34)
  · exact absurd h (H.stop i w seen st d e hi)
termination_by b.size - i.toNat
decreasing_by
  all_goals first
    | (have := usizeStep b i hi; omega)
    | (have := USize.lt_iff_toNat_lt.mp hiu; omega)

end generic

/-! ## The generic list loop -/

/-- The shape of a con-leche list loop `G` (items read by `S`, the item `{` at `i`), on its `ok`
path. -/
structure IListLoop (b : ByteArray) {α : Type} (G : USize → List α → Bool → ScanRes (List α))
    (S : USize → ScanRes α) : Prop where
  stop : ∀ i acc w l e, ¬ i < b.usize → G i acc w ≠ .ok l e
  ws : ∀ i acc w, i < b.usize → isWs (byteAt b i) = true → G i acc w = G (i + 1) acc w
  close : ∀ i acc w l e, i < b.usize → byteAt b i = 93 → G i acc w = .ok l e →
    l = acc.reverse ∧ e = i + 1
  comma : ∀ i acc w l e, i < b.usize → byteAt b i = 44 → G i acc w = .ok l e →
    G (i + 1) acc true = .ok l e
  item : ∀ i acc w l e, i < b.usize → byteAt b i = 123 → G i acc w = .ok l e →
    ∃ x e₁, S i = .ok x e₁ ∧ i < e₁ ∧ G e₁ (x :: acc) false = .ok l e
  other : ∀ i acc w l e, i < b.usize → isWs (byteAt b i) = false → byteAt b i ≠ 93 →
    byteAt b i ≠ 44 → byteAt b i ≠ 123 → G i acc w ≠ .ok l e

theorem run_bound (o sz j n T : Nat) (hj : j < n) (h : o + sz * n ≤ T) : o + sz * j + sz ≤ T := by
  have : sz * (j + 1) ≤ sz * n := Nat.mul_le_mul_left sz hj
  rw [Nat.mul_add, Nat.mul_one] at this; omega

theorem len_le_mul (sz n : Nat) (h : 1 ≤ sz) : n ≤ sz * n := Nat.le_mul_of_pos_left _ h

/-- Growth with the excepted words above the old top is growth. -/
theorem IGrow.grow {m m' : Mem} {xa : ArrId} {x0 x1 : Nat} (h : IGrow m m' xa x0 x1)
    (hx : topN m xa < x0) : Grow m m' :=
  ⟨h.fr, h.top, fun a ha i h1 h2 _ => h.keep a ha i h1 h2 (by
    rintro ⟨rfl, h3, -⟩; omega)⟩

/-- A run of records of size `sz` of array `A` at `o` (words, below the top). -/
def RunR {α : Type} (Rec : Nat → α → Mem → Prop) (A : ArrId) (sz : Nat) (m : Mem) (o : Nat)
    (xs : List α) : Prop :=
  1 ≤ o ∧ o + sz * xs.length ≤ topN m A + 1 ∧ ∀ j (h : j < xs.length), Rec (o + sz * j) xs[j] m

section glist
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- **`ind_list`'s loop against a con-leche list loop.** Parameters: the record kind `sub` lives
in `A` with size `sz`; `Rec` is the record relation, stable under growth that leaves it alone
(`stab`); `item` is the record's link (`ind_obj` on a freshly allocated record). -/
theorem ilist_link {α : Type} (G : USize → List α → Bool → ScanRes (List α))
    (S : USize → ScanRes α) (HG : IListLoop b G S) (sub : Word) (A : ArrId)
    (hA : A = IFR ∨ A = IFL) (sz : Nat) (hsz1 : 1 ≤ sz) (hsz : (indSizeN sub).toNat = sz)
    (hfa : ∀ m n, fldAllocW m sub n = allocW m A n)
    (Rec : Nat → α → Mem → Prop)
    (stab : ∀ t x m m' x0 x1, Rec t x m → 1 ≤ t → t + sz ≤ topN m A + 1 → IGrow m m' A x0 x1 →
      t + sz ≤ x0 → Rec t x m')
    (Q : Mem → Mem → Prop) (hQr : ∀ m, Q m m) (hQt : ∀ m₁ m₂ m₃, Q m₁ m₂ → Q m₂ m₃ → Q m₁ m₃)
    (hQa : ∀ m m₁ n q, allocW m A n = some (q, m₁) → Q m m₁)
    (item : ∀ i (m m₁ : Mem) (q : Word) x e (e₂ : Word) m₂, i < b.usize → byteAt b i = 123 →
      S i = .ok x e → Room m → allocW m A (indSizeN sub) = some (q, m₁) →
      objW b.data (flagsW m₁ sub q) i.toUInt64 sub q = some (e₂, m₂) →
      e₂ = e.toUInt64 ∧ Rec q.toNat x m₂ ∧ IGrow m₁ m₂ A q.toNat (q.toNat + sz) ∧ Room m₂ ∧
        topN m₂ A = topN m₁ A ∧ Q m₁ m₂) :
    ∀ (i : USize) (acc : List α) (w : Bool) (m : Mem) (o cnt : Word) (l : List α) (e : USize)
      (r : Word × Word × Word) (m' : Mem),
      G i acc w = .ok l e → Room m → cnt.toNat = acc.length →
      o.toNat + sz * acc.length = topN m A + 1 → RunR Rec A sz m o.toNat acc.reverse →
      listLoopW b.data m sub (indSizeN sub) o cnt i.toUInt64 = some (r, m') →
      r.1 = o ∧ r.2.1.toNat = l.length ∧ r.2.2 = e.toUInt64 ∧ RunR Rec A sz m' o.toNat l ∧
        Grow m m' ∧ Room m' ∧ o.toNat + sz * l.length = topN m' A + 1 ∧ Q m m' := by
  intro i acc w m o cnt l e r m' h hR hc ho hrun hm
  by_cases hi : i < b.usize
  · have hiW := (lt_usize_iff b h64 hsize i).mp hi
    by_cases hws : isWs (byteAt b i) = true
    · rw [HG.ws i acc w hi hws] at h
      have hne : ∀ k : Word, (k = 93 ∨ k = 123) → byteW b.data i.toUInt64 ≠ k := by
        intro k hk h'
        rw [byteW_eq b h64 hsize] at h'
        have := (ws_iff _).mp hws
        rw [h'] at this
        rcases hk with rfl | rfl <;> revert this <;> decide
      rw [listLoopW_other _ _ _ _ _ _ _ hiW (hne 93 (.inl rfl)) (hne 123 (.inr rfl)),
        ← succ_toUInt64 h64] at hm
      exact ilist_link G S HG sub A hA sz hsz1 hsz hfa Rec stab Q hQr hQt hQa item (i + 1) acc w m o cnt l e r m' h hR hc
        ho hrun hm
    by_cases h93 : byteAt b i = 93
    · obtain ⟨rfl, rfl⟩ := HG.close i acc w l e hi h93 h
      rw [listLoopW_close _ _ _ _ _ _ _ hiW (by rw [byteW_eq b h64 hsize, h93]; rfl)] at hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
      refine ⟨rfl, by simp [hc], (succ_toUInt64 h64 i).symm, hrun, IGrow.refl _ _ _ _, hR,
        by simpa using ho, hQr _⟩
    by_cases h44 : byteAt b i = 44
    · have h' := HG.comma i acc w l e hi h44 h
      rw [listLoopW_other _ _ _ _ _ _ _ hiW (by rw [byteW_eq b h64 hsize, h44]; decide)
        (by rw [byteW_eq b h64 hsize, h44]; decide), ← succ_toUInt64 h64] at hm
      exact ilist_link G S HG sub A hA sz hsz1 hsz hfa Rec stab Q hQr hQt hQa item (i + 1) acc true m o cnt l e r m' h'
        hR hc ho hrun hm
    by_cases h123 : byteAt b i = 123
    · obtain ⟨x, e₁, hS, hie, h'⟩ := HG.item i acc w l e hi h123 h
      rw [listLoopW_open _ _ _ _ _ _ _ hiW (by rw [byteW_eq b h64 hsize, h123]; decide)
        (by rw [byteW_eq b h64 hsize, h123]; rfl), hfa] at hm
      rcases hal : allocW m A (indSizeN sub) with _ | ⟨q, m₁⟩ <;> simp only [hal, listK1, reduceCtorEq] at hm
      rcases hob : objW b.data (flagsW m₁ sub q) i.toUInt64 sub q with _ | ⟨e₂, m₂⟩ <;> simp only [hob, listK2, reduceCtorEq] at hm
      obtain ⟨t1, t2, t3, t4, t5, t6⟩ := item i m m₁ q x e₁ e₂ m₂ hi h123 hS hR hal hob
      subst t1
      rw [ite_eq_left ((lt_toUInt64_iff _ _).mp hie)] at hm
      obtain ⟨a1, a2, a3, a4, -, a6, -⟩ := allocW_facts m m₁ A hA _ q hR hal
      rw [hsz] at a2 a6
      have hq : q.toNat = o.toNat + sz * acc.length := by rw [a1, ho]
      have hroom := hR
      obtain ⟨R1, R2, R3, R4⟩ := hroom
      have htopA : topN m A < 2 ^ 63 := by rcases hA with rfl | rfl <;> omega
      have hlen := len_le_mul sz acc.length hsz1
      have hc1 : (cnt + 1).toNat = (x :: acc).length := by
        rw [UInt64.toNat_add, hc]; simp; omega
      have hg : IGrow m m₂ A q.toNat (q.toNat + sz) :=
        (a4.ex A q.toNat (q.toNat + sz)).trans t3
      -- the previous records are below `q`
      have hrun' : RunR Rec A sz m₂ o.toNat (x :: acc).reverse := by
        obtain ⟨r1, r2, r3⟩ := hrun
        simp only [List.length_reverse] at r2
        refine ⟨r1, by simp; rw [t5, a2]; rw [Nat.mul_add]; omega, fun j hj => ?_⟩
        simp only [List.reverse_cons, List.length_append, List.length_reverse, List.length_cons,
          List.length_nil] at hj
        simp only [List.reverse_cons]
        rw [List.getElem_append]
        split
        · rename_i hj'
          simp only [List.length_reverse] at hj'
          have := r3 j (by simpa using hj')
          exact stab _ _ _ _ _ _ this (by omega) (run_bound _ _ _ _ _ hj' r2) hg (by
            rw [hq]; exact run_bound _ _ _ _ _ hj' (Nat.le_refl _))
        · rename_i hj'
          simp only [List.length_reverse, Nat.not_lt] at hj'
          have hj2 : j = acc.length := by omega
          subst hj2
          simp only [List.getElem_singleton]
          rw [← hq]; exact t2
      have ho' : o.toNat + sz * (x :: acc).length = topN m₂ A + 1 := by
        rw [t5, a2]; simp; rw [Nat.mul_add]; omega
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := ilist_link G S HG sub A hA sz hsz1 hsz hfa Rec stab
        Q hQr hQt hQa item e₁ (x :: acc) false m₂ o (cnt + 1) l e r m' h' t4 hc1 ho' hrun' hm
      have hQ1 : Q m m₁ := hQa _ _ _ _ hal
      exact ⟨c1, c2, c3, c4, (hg.grow (by omega)).trans c5, c6, c7,
        hQt _ _ _ hQ1 (hQt _ _ _ t6 c8)⟩
    · exact absurd h (HG.other i acc w l e hi (by simpa using hws) h93 h44 h123)
  · exact absurd h (HG.stop i acc w l e hi)
termination_by i _acc _w _m _o _cnt _l _e _r _m' => b.size - i.toNat
decreasing_by
  all_goals first
    | (have := usizeStep b i hi; have := usizeInBounds b i hi; omega)
    | (have := USize.lt_iff_toNat_lt.mp hie; have := usizeInBounds b i hi; omega)

/-- **`ind_list(v, sub)` against a con-leche list scanner `W`** (`[` at `v`, then the loop `G`). -/
theorem ilistW_link {α : Type} (G : USize → List α → Bool → ScanRes (List α))
    (S : USize → ScanRes α) (HG : IListLoop b G S) (W : USize → ScanRes (List α))
    (hW : ∀ v l e, W v = .ok l e → byteAt b v = 91 ∧ G (v + 1) [] true = .ok l e)
    (sub : Word) (A : ArrId)
    (hA : A = IFR ∨ A = IFL) (sz : Nat) (hsz1 : 1 ≤ sz) (hsz : (indSizeN sub).toNat = sz)
    (hfa : ∀ m n, fldAllocW m sub n = allocW m A n)
    (Rec : Nat → α → Mem → Prop)
    (stab : ∀ t x m m' x0 x1, Rec t x m → 1 ≤ t → t + sz ≤ topN m A + 1 → IGrow m m' A x0 x1 →
      t + sz ≤ x0 → Rec t x m')
    (Q : Mem → Mem → Prop) (hQr : ∀ m, Q m m) (hQt : ∀ m₁ m₂ m₃, Q m₁ m₂ → Q m₂ m₃ → Q m₁ m₃)
    (hQa : ∀ m m₁ n q, allocW m A n = some (q, m₁) → Q m m₁)
    (item : ∀ i (m m₁ : Mem) (q : Word) x e (e₂ : Word) m₂, i < b.usize → byteAt b i = 123 →
      S i = .ok x e → Room m → allocW m A (indSizeN sub) = some (q, m₁) →
      objW b.data (flagsW m₁ sub q) i.toUInt64 sub q = some (e₂, m₂) →
      e₂ = e.toUInt64 ∧ Rec q.toNat x m₂ ∧ IGrow m₁ m₂ A q.toNat (q.toNat + sz) ∧ Room m₂ ∧
        topN m₂ A = topN m₁ A ∧ Q m₁ m₂)
    (v : USize) (m : Mem) (l : List α) (e : USize) (r : Word × Word × Word) (m' : Mem)
    (h : W v = .ok l e) (hR : Room m) (hm : listW b.data m v.toUInt64 sub = some (r, m')) :
    r.2.2 = e.toUInt64 ∧ r.2.1.toNat = l.length ∧ RunR Rec A sz m' r.1.toNat l ∧ Grow m m' ∧
      Room m' ∧ r.1.toNat = topN m A + 1 ∧ r.1.toNat + sz * l.length = topN m' A + 1 ∧ Q m m' := by
  obtain ⟨h91, hG⟩ := hW v l e h
  have hv : v < b.usize := lt_of_byteAt_ne b h64 hsize v (by rw [h91]; decide)
  have hvW := (lt_usize_iff b h64 hsize v).mp hv
  rw [listW_eq, ite_eq_left hvW, ite_eq_right (by rw [byteW_eq b h64 hsize, h91]; decide), hfa] at hm
  cases hal : allocW m A 0 with
  | none => rw [hal, listK0_none] at hm; cases hm
  | some om =>
  obtain ⟨o, m₁⟩ := om
  rw [hal, listK0_some, ← succ_toUInt64 h64] at hm
  obtain ⟨a1, a2, a3, a4, -, -, -⟩ := allocW_facts m m₁ A hA _ o hR hal
  have a2' : topN m₁ A = topN m A := by rw [a2]; rfl
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := ilist_link b h64 hsize G S HG sub A hA sz hsz1 hsz hfa Rec
    stab Q hQr hQt hQa item (v + 1) [] true m₁ o 0 l e r m' hG a3 rfl (by simp; omega)
    ⟨by omega, by simp; omega, fun j hj => by simp at hj⟩ hm
  subst c1
  exact ⟨c3, c2, c4, a4.trans c5, c6, a1, c7, hQt _ _ _ (hQa _ _ _ _ hal) c8⟩

end glist

/-! ## Keys and values -/

theorem skipWsN_ge (a : Array UInt8) (i : Nat) : i ≤ L.Scan.Leaves.skipWsN a i := by
  fun_induction L.Scan.Leaves.skipWsN a i <;> omega

section kv
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- A member's value starts after its key's quote. -/
theorem valueAt_gt (i : USize) (hi : i < b.usize) (hk : keyEnd b (i + 1) ≠ 0)
    (hv : valueAt b i (keyEnd b (i + 1)) ≠ i) : i < valueAt b i (keyEnd b (i + 1)) := by
  have hb64 : b.size < 2 ^ 64 := by omega
  have hbs : b.data.size = b.size := rfl
  have hin := usizeInBounds b i hi
  have hi1 := usizeStep b i hi
  have hke := keyEnd_toNat_eq b h64 hb64 (i + 1)
  have hkn0 : keyEndN b.data (i + 1).toNat ≠ 0 := fun h0 => hk (by
    apply USize.toNat_inj.mp; rw [hke, h0]; rfl)
  have hkb := keyEndN_bounds b.data _ hkn0
  generalize hK : keyEnd b (i + 1) = ke at hv hke ⊢
  unfold valueAt at hv ⊢
  dsimp only at hv ⊢
  by_cases h58 : (byteAt b (skipWs b (ke + 1)) == 58) = true
  · rw [ite_eq_left h58] at hv ⊢
    have hke' : ke < b.usize := by
      rw [USize.lt_iff_toNat_lt, usize_toNat_eq b h64 hb64]; omega
    have hk1 := usizeStep b ke hke'
    have hp := skipWs_toNat_eq b h64 hb64 (ke + 1)
    have hpU : skipWs b (ke + 1) < b.usize :=
      lt_of_byteAt_ne b h64 hsize _ (by simp at h58; rw [h58]; decide)
    have hp1 := usizeStep b _ hpU
    have hq := skipWs_toNat_eq b h64 hb64 (skipWs b (ke + 1) + 1)
    have g1 := skipWsN_ge b.data (ke + 1).toNat
    have g2 := skipWsN_ge b.data (skipWs b (ke + 1) + 1).toNat
    rw [USize.lt_iff_toNat_lt]; omega
  · rw [ite_eq_right h58] at hv; exact absurd rfl hv

end kv

/-! ## `ind_member`'s arms, on con-leche's values -/

section arms
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- A number value: the end, the word, below `10^18`. -/
theorem num_word (i v : USize) (hne : ¬ numEnd b v = v) (hie : i < numEnd b v)
    (hvle : v.toNat ≤ b.size) :
    L.Scan.Values.slotNatN b.data i.toUInt64 v.toUInt64 = (numEnd b v).toUInt64 ∧
    (rdNatN b.data v.toUInt64 (numEnd b v).toUInt64 ≠ NONE →
      NumW (rdNatN b.data v.toUInt64 (numEnd b v).toUInt64) (readNatAt b v (numEnd b v))) := by
  obtain ⟨hsl, hRn⟩ := num_val b h64 hsize i v hne hie hvle
  refine ⟨hsl, fun hx => ⟨hRn hx, ?_⟩⟩
  rw [← hRn hx]
  have hb64 : b.size < 2 ^ 64 := by omega
  have hnt := numEnd_toNat_eq b h64 hb64 v
  apply rdNatN_lt _ _ _ (by rw [USize.toNat_toUInt64]; omega) _ hx
  intro j hj1 hj2
  rw [USize.toNat_toUInt64] at hj1 hj2
  rw [hnt] at hj2
  exact numEndN_digits b.data v.toNat j hj1 hj2

/-- A number key (slot `(1, s, _)`). -/
theorem num_arm (m m' : Mem) (kind q K s sb : Word) (i v : USize) (e' : Word)
    (hk : indSlotN kind K = (1, s, sb)) (hne : ¬ numEnd b v = v) (hie : i < numEnd b v)
    (hvle : v.toNat ≤ b.size)
    (hmem : memberW b.data m kind q i.toUInt64 K v.toUInt64 = some (e', m')) :
    e' = (numEnd b v).toUInt64 ∧
      ∃ x, m' = fldPutW m kind q s x ∧ NumW x (readNatAt b v (numEnd b v)) := by
  rw [memberW_eq, hk] at hmem
  simp only [true_or, ite_true] at hmem
  unfold numW at hmem
  obtain ⟨hsl, hnum⟩ := num_word b h64 hsize i v hne hie hvle
  rw [hsl] at hmem
  split at hmem; cases hmem; rename_i hx
  rw [ite_eq_right (by decide)] at hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmem)
  exact ⟨rfl, _, rfl, hnum hx⟩

/-- An optional number key (slot `(6, s, _)`): the flag `1`, then the number. -/
theorem opt_arm (m m' : Mem) (kind q K s sb : Word) (i v : USize) (e' : Word)
    (hk : indSlotN kind K = (6, s, sb)) (hne : ¬ numEnd b v = v) (hie : i < numEnd b v)
    (hvle : v.toNat ≤ b.size)
    (hmem : memberW b.data m kind q i.toUInt64 K v.toUInt64 = some (e', m')) :
    e' = (numEnd b v).toUInt64 ∧
      ∃ x, m' = fldPutW (fldPutW m kind q s 1) kind q (s + 1) x ∧
        NumW x (readNatAt b v (numEnd b v)) := by
  rw [memberW_eq, hk] at hmem
  simp only [or_true, ite_true] at hmem
  unfold numW at hmem
  obtain ⟨hsl, hnum⟩ := num_word b h64 hsize i v hne hie hvle
  rw [hsl] at hmem
  split at hmem; cases hmem; rename_i hx
  rw [ite_eq_left rfl] at hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmem)
  exact ⟨rfl, _, rfl, hnum hx⟩

/-- A Boolean key (slot `(2, s, _)`). -/
theorem bool_arm (m m' : Mem) (kind q ks K s sb : Word) (v : USize) (x : Bool) (e : USize)
    (e' : Word) (hk : indSlotN kind K = (2, s, sb)) (hx : scanBool b v = .ok x e)
    (hmem : memberW b.data m kind q ks K v.toUInt64 = some (e', m')) :
    e' = e.toUInt64 ∧ m' = fldPutW m kind q s (if x then 1 else 0) := by
  rw [memberW_eq, hk] at hmem
  simp only [show ¬ ((2 : Word) = 1 ∨ (2 : Word) = 6) by decide, true_or, ite_true, ite_false] at hmem
  unfold boolW at hmem
  obtain ⟨hh, hend, hval⟩ := boolV_link b h64 hsize v x e hx
  rw [ite_eq_right hh, ite_eq_left rfl] at hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmem)
  exact ⟨hend, by rw [← hval]; rfl⟩

/-- A Boolean key read past (slot `(8, _, _)`). -/
theorem boolp_arm (m m' : Mem) (kind q ks K s sb : Word) (v : USize) (x : Bool) (e : USize)
    (e' : Word) (hk : indSlotN kind K = (8, s, sb)) (hx : scanBool b v = .ok x e)
    (hmem : memberW b.data m kind q ks K v.toUInt64 = some (e', m')) :
    e' = e.toUInt64 ∧ m' = m := by
  rw [memberW_eq, hk] at hmem
  simp only [show ¬ ((8 : Word) = 1 ∨ (8 : Word) = 6) by decide, or_true, ite_true, ite_false] at hmem
  unfold boolW at hmem
  obtain ⟨hh, hend, -⟩ := boolV_link b h64 hsize v x e hx
  rw [ite_eq_right hh, ite_eq_right (by decide)] at hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmem)
  exact ⟨hend, rfl⟩

/-- A number list's position (slot `(3, s, _)`, `levelParams`). -/
theorem lps_arm (m m' : Mem) (kind q ks K s sb : Word) (v : USize) (xs : List Nat) (e : USize)
    (e' : Word) (hk : indSlotN kind K = (3, s, sb)) (hx : scanNatList b v = .ok xs e)
    (hmem : memberW b.data m kind q ks K v.toUInt64 = some (e', m')) :
    e' = e.toUInt64 ∧ m' = fldPutW m kind q s v.toUInt64 ∧ ItemsR (listN b.data v.toUInt64) xs := by
  rw [memberW_eq, hk] at hmem
  simp only [show ¬ ((3 : Word) = 1 ∨ (3 : Word) = 6) by decide,
    show ¬ ((3 : Word) = 2 ∨ (3 : Word) = 8) by decide, true_or, ite_true, ite_false] at hmem
  unfold nlistW at hmem
  rw [ite_eq_left rfl] at hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmem)
  have hend := scanNatList_link b h64 hsize v
  rw [hx] at hend
  exact ⟨hend.symm, rfl, list_link b h64 hsize v xs e hx⟩

/-- A number list read past (slot `(4, _, _)`, `all`). -/
theorem all_arm (m m' : Mem) (kind q ks K s sb : Word) (v : USize) (xs : List Nat) (e : USize)
    (e' : Word) (hk : indSlotN kind K = (4, s, sb)) (hx : scanNatList b v = .ok xs e)
    (hmem : memberW b.data m kind q ks K v.toUInt64 = some (e', m')) :
    e' = e.toUInt64 ∧ m' = m := by
  rw [memberW_eq, hk] at hmem
  simp only [show ¬ ((4 : Word) = 1 ∨ (4 : Word) = 6) by decide,
    show ¬ ((4 : Word) = 2 ∨ (4 : Word) = 8) by decide, true_or, or_true, ite_true,
    ite_false] at hmem
  unfold nlistW at hmem
  rw [ite_eq_right (by decide), ite_eq_right (by decide)] at hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmem)
  have hend := scanNatList_link b h64 hsize v
  rw [hx] at hend
  exact ⟨hend.symm, rfl⟩

/-- A list of name ids into `IFL` (slot `(5, s, _)`, a type's `ctors`). -/
theorem ids_arm (m m' : Mem) (kind q ks K s sb : Word) (v : USize) (xs : List Nat) (e : USize)
    (e' : Word) (hk : indSlotN kind K = (5, s, sb)) (hx : scanNatList b v = .ok xs e)
    (hmem : memberW b.data m kind q ks K v.toUInt64 = some (e', m')) :
    e' = e.toUInt64 ∧ ∃ m₁, idsM b.data m v.toUInt64 = some m₁ ∧
      m' = fldPutW (fldPutW m₁ kind q s (rdW (m.arr64 IFL) 0 + 1)) kind q (s + 1)
        (lsCntN b.data (v.toUInt64 + 1) 0) ∧ ItemsR (listN b.data v.toUInt64) xs := by
  rw [memberW_eq, hk] at hmem
  simp only [show ¬ ((5 : Word) = 1 ∨ (5 : Word) = 6) by decide,
    show ¬ ((5 : Word) = 2 ∨ (5 : Word) = 8) by decide, or_true, ite_true, ite_false] at hmem
  unfold nlistW at hmem
  rw [ite_eq_right (by decide), ite_eq_left rfl] at hmem
  have hend := scanNatList_link b h64 hsize v
  rw [hx] at hend
  rcases hi : idsM b.data m v.toUInt64 with _ | m₁ <;> simp only [hi, nlK, reduceCtorEq] at hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmem)
  exact ⟨hend.symm, m₁, rfl, rfl, list_link b h64 hsize v xs e hx⟩

omit h64 hsize in
/-- A list of records (slot `(7, s, sub)`). -/
theorem list_arm (m m' : Mem) (kind q K s sub : Word) (i v : USize) (e' : Word)
    (hk : indSlotN kind K = (7, s, sub)) (hiv : i < v)
    (hmem : memberW b.data m kind q i.toUInt64 K v.toUInt64 = some (e', m')) :
    ∃ o c m₁, listW b.data m v.toUInt64 sub = some ((o, c, e'), m₁) ∧
      m' = fldPutW (fldPutW m₁ kind q s o) kind q (s + 1) c := by
  rw [memberW_eq, hk] at hmem
  simp only [show ¬ ((7 : Word) = 1 ∨ (7 : Word) = 6) by decide,
    show ¬ ((7 : Word) = 2 ∨ (7 : Word) = 8) by decide,
    show ¬ ((7 : Word) = 3 ∨ (7 : Word) = 4 ∨ (7 : Word) = 5) by decide, ite_true,
    ite_false] at hmem
  rw [ite_eq_left ((lt_toUInt64_iff _ _).mp hiv)] at hmem
  rcases hl : listW b.data m v.toUInt64 sub with _ | ⟨⟨o, c, e₁⟩, m₁⟩ <;> simp only [hl, memK, reduceCtorEq] at hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmem)
  exact ⟨o, c, m₁, rfl, rfl⟩

end arms

/-! ## A record being read -/

/-- The record of `A` at `q` (size `sz`) being read, from the memory `m₁` it was allocated in. -/
def RecInv (A : ArrId) (sz : Nat) (q : Word) (m₁ m : Mem) : Prop :=
  IGrow m₁ m A q.toNat (q.toNat + sz) ∧ Room m ∧ 1 ≤ q.toNat ∧ q.toNat + sz ≤ topN m₁ A + 1

/-- A write to slot `s` of the record. -/
theorem slot_put (A : ArrId) (hA : A = IFR ∨ A = IFL) (sz : Nat) (hsz : sz ≤ 16) (q s x : Word)
    (m₁ m : Mem) (hI : RecInv A sz q m₁ m) (hs : s.toNat < sz) :
    RecInv A sz q m₁ (m.set64 A (q + s) x) ∧
      wd (m.set64 A (q + s) x) A (q.toNat + s.toNat) = x ∧
      (∀ j, j ≠ q.toNat + s.toNat → wd (m.set64 A (q + s) x) A j = wd m A j) ∧
      (∀ c j, c ≠ A → wd (m.set64 A (q + s) x) c j = wd m c j) ∧
      (∀ c, topN (m.set64 A (q + s) x) c = topN m c) := by
  obtain ⟨g, hR, hq1, hqs⟩ := hI
  have ht := g.top A hA
  obtain ⟨R1, R2, R3, R4⟩ := hR
  have hAs : (m.arr64 A).size < 2 ^ 63 ∧ topN m A < (m.arr64 A).size := by
    rcases hA with rfl | rfl <;> exact ⟨by assumption, by assumption⟩
  have hqs' : (q + s).toNat = q.toNat + s.toNat := by
    rw [UInt64.toNat_add]; apply Nat.mod_eq_of_lt; omega
  obtain ⟨g1, g2, g3⟩ := grow_set m A hA (q + s) x q.toNat (q.toNat + sz) (by omega) (by omega)
    (by omega)
  refine ⟨⟨g.trans g1, g2 ⟨R1, R2, R3, R4⟩, hq1, hqs⟩, ?_, fun j hj => ?_,
    fun c j hc => wd_set64_ne _ _ _ _ _ _ hc, g3⟩
  · rw [← hqs']; exact wd_set64_same _ _ _ _ (by omega)
  · rw [wd_set64_other _ _ _ _ _ (by omega)]

/-- Growth elsewhere (a nested list) while the record is read. -/
theorem RecInv.grow {A : ArrId} {sz : Nat} {q : Word} {m₁ m m' : Mem} (hI : RecInv A sz q m₁ m)
    (hg : Grow m m') (hR : Room m') : RecInv A sz q m₁ m' :=
  ⟨hI.1.trans (hg.ex _ _ _), hR, hI.2.2⟩

/-- A field not seen yet, or seen and related. -/
def SeenR (seen bit : UInt32) (P : Prop) : Prop := P ∨ seen &&& bit = 0

theorem seenR_zero (bit : UInt32) (P : Prop) : SeenR 0 bit P := .inr (by simp)

theorem seenR_or {seen bit a : UInt32} {P Q : Prop} (h : SeenR seen bit P) (ha : a &&& bit = 0)
    (hPQ : P → Q) : SeenR (seen ||| a) bit Q := by
  rcases h with h | h
  · exact .inl (hPQ h)
  · exact .inr (by rw [bit_or_and _ _ _ ha, h])

theorem seenR_close {seen bit M : UInt32} {P : Prop} (h : SeenR seen bit P) (hM : seen &&& M = M)
    (hbM : M &&& bit = bit) (hb : bit ≠ 0) : P := by
  rcases h with h | h
  · exact h
  · exfalso; apply hb
    rw [← hbM, ← hM, UInt32.and_assoc, hbM, h]

theorem IGrow.wd_keep {m m' : Mem} {xa : ArrId} {x0 x1 : Nat} (h : IGrow m m' xa x0 x1)
    (a : ArrId) (ha : a = IFR ∨ a = IFL) (j : Nat) (h1 : 1 ≤ j) (h2 : j ≤ topN m a)
    (h3 : a = xa → j < x0) : wd m' a j = wd m a j :=
  h.keep a ha j h1 h2 (by rintro ⟨h4, h5, -⟩; have := h3 h4; omega)

end L.Front.Ind
