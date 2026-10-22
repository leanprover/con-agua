import ConAgua.Front.IndFieldsSpec
import ConAgua.Front.FieldsDeclLink

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
open L.Scan.Leaves (numEndN skipDigitsN)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

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
      · simp [h2, Array.getElem?_eq_none (Nat.le_of_not_lt h2)]
    · simp [h]
  · simp [wd, Mem.arr64_set64_ne _ _ _ _ _ hc, hc]

theorem wd_set64_ne (m : Mem) (a c : ArrId) (i x : Word) (j : Nat) (h : c ≠ a) :
    wd (m.set64 a i x) c j = wd m c j := by
  rw [wd_set64, if_neg (by simp [h])]

theorem wd_set64_same (m : Mem) (a : ArrId) (i x : Word) (h : i.toNat < (m.arr64 a).size) :
    wd (m.set64 a i x) a i.toNat = x := by
  rw [wd_set64, if_pos ⟨rfl, rfl, h⟩]

theorem wd_set64_other (m : Mem) (a : ArrId) (i x : Word) (j : Nat) (h : i.toNat ≠ j) :
    wd (m.set64 a i x) a j = wd m a j := by
  rw [wd_set64, if_neg (by simp [h])]

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
  rw [if_neg h18]
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

theorem topN_eq (m : Mem) (a : ArrId) : topN m a = (rdW (m.arr64 a) 0).toNat := rfl

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
    intro c; simp only [topN, wd_set64]; rw [if_neg (by omega)]
  have hfr : MemFrame [IFR, IFL] [] m (m.set64 A i x) :=
    (MemFrame.set64 m A hCTL i x).mono (by rcases hA with rfl | rfl <;> simp) (by simp)
  refine ⟨⟨hfr, fun a _ => by rw [ht]; exact Nat.le_refl _, fun a ha j hj1 hj2 hj3 => ?_⟩, fun hR => ?_, ht⟩
  · rw [wd_set64]
    rw [if_neg]
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
  · rw [if_pos h0] at h; cases h
  rw [if_neg h0] at h
  by_cases h1 : m.len64 a < rdW (m.arr64 a) 0 + 1
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : m.len64 a - (rdW (m.arr64 a) 0 + 1) < n
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
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
    · subst hc; rw [if_pos ⟨rfl, rfl, hs0⟩, if_pos rfl, hnew]; rfl
    · rw [if_neg (by simp [hc]), if_neg hc]
  have hfr : MemFrame [IFR, IFL] [] m (m.set64 a 0 (rdW (m.arr64 a) 0 + 1 - 1 + n)) :=
    (MemFrame.set64 m a hCTL _ _).mono (by rcases ha with rfl | rfl <;> simp) (by simp)
  refine ⟨ho, by rw [htop', if_pos rfl], ?_, ⟨hfr, fun c hc => ?_, fun c hc j hj1 hj2 hj3 => ?_⟩,
    fun c hc => by rw [htop', if_neg hc], by omega,
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
  · rw [wd_set64, if_neg (by rintro ⟨-, h5, -⟩; simp at h5; omega)]

theorem pushLW_facts (m m' : Mem) (x o : Word) (hR : Room m) (h : pushLW m x = some (o, m')) :
    o.toNat = topN m IFL + 1 ∧ topN m' IFL = topN m IFL + 1 ∧ Room m' ∧ Grow m m' ∧
      wd m' IFL (topN m IFL + 1) = x ∧ m'.arr64 IFR = m.arr64 IFR := by
  unfold pushLW at h
  cases ha : allocW m IFL 1 with
  | none => rw [ha] at h; cases h
  | some om =>
    obtain ⟨o₁, m₁⟩ := om
    rw [ha, pushK_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
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
  cases ha : allocW m IFL 0 with
  | none => rw [ha, idsK0_none] at h; cases h
  | some om =>
    obtain ⟨o, m₁⟩ := om
    rw [ha, idsK0_some] at h
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
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨(succ_toUInt64 b h64 hsize i).symm, hF⟩
    by_cases h44 : byteAt b i = 44
    · obtain ⟨rfl, h'⟩ := H.comma i w seen st d e hi h44 h
      simp only [bw, Bool.false_eq_true, if_false] at hm
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
      simp only [bw, if_true] at hm
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

end L.Front.Ind
