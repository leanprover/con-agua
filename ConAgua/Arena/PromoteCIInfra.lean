import ConAgua.Arena.PromoteCI

/-!
# Facts about the record pool's reads, writes and copies

`preE m T` (the pool below `T`), the facts of `stP` (a sequence of stores), the reads
`erec_rd1‥5`, `erec_cp` and `erec_wr1‥5` as relations on the pool.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- The record pool below `T`. -/
def preE (m : Mem) (T : Nat) : Array Word := (m.arr64 EREC).extract 0 T

theorem preE_get (m : Mem) (T i : Nat) :
    (preE m T)[i]? = if i < T then (m.arr64 EREC)[i]? else none := by
  simp only [preE, Array.getElem?_extract]
  by_cases h : i < T
  · simp [h]; omega
  · simp [h]; omega

theorem preE_ext {m m' : Mem} {T : Nat} (h : ∀ i < T, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) :
    ArrExt (preE m T) (preE m' T) := by
  intro i v hv
  rw [preE_get] at hv ⊢
  split at hv
  · rename_i hi; rw [if_pos hi, h i hi]; exact hv
  · simp at hv

theorem preE_mono (m : Mem) {T T' : Nat} (h : T ≤ T') : ArrExt (preE m T) (preE m T') := by
  intro i v hv
  rw [preE_get] at hv ⊢
  split at hv
  · rename_i hi; rw [if_pos (by omega)]; exact hv
  · simp at hv

theorem erecP_eq_preE (m : Mem) : erecP m = preE m (erecTop m) := rfl

theorem preE_get_lt {m : Mem} {T i : Nat} {v : Word} (h : (preE m T)[i]? = some v) :
    i < T ∧ (m.arr64 EREC)[i]? = some v := by
  rw [preE_get] at h
  split at h
  · rename_i hi; exact ⟨hi, h⟩
  · simp at h

theorem preE_of_get {m : Mem} {T i : Nat} {v : Word} (hi : i < T) (h : (m.arr64 EREC)[i]? = some v) :
    (preE m T)[i]? = some v := by
  rw [preE_get, if_pos hi]; exact h

/-! ## `stP` -/

theorem arr_set!_get? (a : Array Word) (k i : Nat) (v : Word) :
    (a.set! k v)[i]? = if k = i ∧ k < a.size then some v else a[i]? := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h : k = i
  · subst h; by_cases hk : k < a.size <;> simp [hk]
  · simp [h]

theorem stP_facts (d : Word) : ∀ (ps : List (Word × Word)) (m m' : Mem),
    ps.Pairwise (fun a b => (d + a.1).toNat ≠ (d + b.1).toNat) → stP d m ps = some m' →
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (∀ q ∈ ps, (d + q.1).toNat ≠ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (∀ q ∈ ps, (d + q.1).toNat < (m.arr64 EREC).size) ∧
    (∀ q ∈ ps, (m'.arr64 EREC)[(d + q.1).toNat]? = some q.2) := by
  intro ps
  induction ps with
  | nil =>
    intro m m' _ h
    simp only [stP, Option.some.injEq] at h
    subst h
    exact ⟨rfl, MemFrame.refl _ _ _, fun _ _ => rfl, by simp, by simp⟩
  | cons q ps ih =>
    intro m m' hpw h
    obtain ⟨o, v⟩ := q
    simp only [stP] at h
    split at h
    · cases h
    rename_i hb
    have hb' : (d + o).toNat < (m.arr64 EREC).size := Nat.lt_of_not_le hb
    obtain ⟨hhd, htl⟩ := List.pairwise_cons.mp hpw
    obtain ⟨hs, hf, hu, hbd, hw⟩ := ih _ _ htl h
    have hE : (m.set64 EREC (d + o) v).arr64 EREC = (m.arr64 EREC).set! (d + o).toNat v :=
      Mem.arr64_set64_same _ _ _ _
    have hsz1 : ((m.set64 EREC (d + o) v).arr64 EREC).size = (m.arr64 EREC).size := by
      rw [hE]; simp
    have hfr : MemFrame [EREC] [] m (m.set64 EREC (d + o) v) :=
      MemFrame.set64 m EREC (by decide) _ _
    refine ⟨by rw [hs, hsz1], hfr.trans hf, ?_, ?_, ?_⟩
    · intro i hi
      rw [hu i (fun q hq => hi q (List.mem_cons_of_mem _ hq)), hE, arr_set!_get?]
      have := hi (o, v) (List.mem_cons_self ..)
      simp only at this
      rw [if_neg (by omega)]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hb'
      · have := hbd q hq; rw [hsz1] at this; exact this
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [hu _ (fun q' hq' => (hhd q' hq').symm), hE, arr_set!_get?]
        rw [if_pos (And.intro rfl hb')]
      · exact hw q hq

/-! ## Reads -/

theorem pci_rdW_of_get? (a : Array Word) (i : Word) {w : Word} (h : a[i.toNat]? = some w) :
    rdW a i = w := by
  rw [rdW, h]; rfl

theorem rd1W_of {m : Mem} {s a : Word} (hsz : (m.arr64 EREC).size < 2 ^ 64) (h0 : (m.arr64 EREC)[s.toNat + 0]? = some a) :
    rd1W m s = [a] := by
  have b0 : s.toNat + 0 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp h0).1
  simp only [rd1W]
  rw [if_neg (by omega)]
  rw [pci_rdW_of_get? _ s (by simpa using h0)]

theorem rd2W_of {m : Mem} {s a b : Word} (hsz : (m.arr64 EREC).size < 2 ^ 64) (h0 : (m.arr64 EREC)[s.toNat + 0]? = some a) (h1 : (m.arr64 EREC)[s.toNat + 1]? = some b) :
    rd2W m s = [a, b] := by
  have b0 : s.toNat + 0 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp h0).1
  have b1 : s.toNat + 1 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp h1).1
  have e1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  simp only [rd2W]
  rw [if_neg (by omega)]
  rw [pci_rdW_of_get? _ s (by simpa using h0)]
  rw [pci_rdW_of_get? _ (s + 1) (by rw [e1]; simpa using h1)]

theorem rd4W_of {m : Mem} {s a b c d : Word} (hsz : (m.arr64 EREC).size < 2 ^ 64) (h0 : (m.arr64 EREC)[s.toNat + 0]? = some a) (h1 : (m.arr64 EREC)[s.toNat + 1]? = some b) (h2 : (m.arr64 EREC)[s.toNat + 2]? = some c) (h3 : (m.arr64 EREC)[s.toNat + 3]? = some d) :
    rd4W m s = [a, b, c, d] := by
  have b0 : s.toNat + 0 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp h0).1
  have b1 : s.toNat + 1 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp h1).1
  have b2 : s.toNat + 2 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp h2).1
  have b3 : s.toNat + 3 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp h3).1
  have e1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (s + 2).toNat = s.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : (s + 3).toNat = s.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  simp only [rd4W]
  rw [if_neg (by omega)]
  rw [pci_rdW_of_get? _ s (by simpa using h0)]
  rw [pci_rdW_of_get? _ (s + 1) (by rw [e1]; simpa using h1)]
  rw [pci_rdW_of_get? _ (s + 2) (by rw [e2]; simpa using h2)]
  rw [pci_rdW_of_get? _ (s + 3) (by rw [e3]; simpa using h3)]

theorem rd5W_of {m : Mem} {s a b c d e : Word} (hsz : (m.arr64 EREC).size < 2 ^ 64) (h0 : (m.arr64 EREC)[s.toNat + 0]? = some a) (h1 : (m.arr64 EREC)[s.toNat + 1]? = some b) (h2 : (m.arr64 EREC)[s.toNat + 2]? = some c) (h3 : (m.arr64 EREC)[s.toNat + 3]? = some d) (h4 : (m.arr64 EREC)[s.toNat + 4]? = some e) :
    rd5W m s = [a, b, c, d, e] := by
  have b0 : s.toNat + 0 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp h0).1
  have b1 : s.toNat + 1 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp h1).1
  have b2 : s.toNat + 2 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp h2).1
  have b3 : s.toNat + 3 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp h3).1
  have b4 : s.toNat + 4 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp h4).1
  have e1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (s + 2).toNat = s.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : (s + 3).toNat = s.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have e4 : (s + 4).toNat = s.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  simp only [rd5W]
  rw [if_neg (by omega)]
  rw [pci_rdW_of_get? _ s (by simpa using h0)]
  rw [pci_rdW_of_get? _ (s + 1) (by rw [e1]; simpa using h1)]
  rw [pci_rdW_of_get? _ (s + 2) (by rw [e2]; simpa using h2)]
  rw [pci_rdW_of_get? _ (s + 3) (by rw [e3]; simpa using h3)]
  rw [pci_rdW_of_get? _ (s + 4) (by rw [e4]; simpa using h4)]

theorem rd1_call (p : Prog) (hp : PromoteProg p) {n : Nat} {s : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "erec_rd1" [s] m = some (r, m')) : m' = m ∧ r = rd1W m s ∧ r ≠ [] := by
  obtain ⟨s', rfl, h1, h2, h3⟩ := callW_triple (erecRd1_spec p hp n ⟨m, Locals.init []⟩ s) hc
  subst h1
  exact ⟨rfl, h3, h2⟩

theorem rd2_call (p : Prog) (hp : PromoteProg p) {n : Nat} {s : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "erec_rd2" [s] m = some (r, m')) : m' = m ∧ r = rd2W m s ∧ r ≠ [] := by
  obtain ⟨s', rfl, h1, h2, h3⟩ := callW_triple (erecRd2_spec p hp n ⟨m, Locals.init []⟩ s) hc
  subst h1
  exact ⟨rfl, h3, h2⟩

theorem rd3_call (p : Prog) (hp : PromoteProg p) {n : Nat} {s : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "erec_rd3" [s] m = some (r, m')) : m' = m ∧ r = rd3W m s ∧ r ≠ [] := by
  obtain ⟨s', rfl, h1, h2, h3⟩ := callW_triple (erecRd3_spec p hp n ⟨m, Locals.init []⟩ s) hc
  subst h1
  exact ⟨rfl, h3, h2⟩

theorem rd4_call (p : Prog) (hp : PromoteProg p) {n : Nat} {s : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "erec_rd4" [s] m = some (r, m')) : m' = m ∧ r = rd4W m s ∧ r ≠ [] := by
  obtain ⟨s', rfl, h1, h2, h3⟩ := callW_triple (erecRd4_spec p hp n ⟨m, Locals.init []⟩ s) hc
  subst h1
  exact ⟨rfl, h3, h2⟩

theorem rd5_call (p : Prog) (hp : PromoteProg p) {n : Nat} {s : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "erec_rd5" [s] m = some (r, m')) : m' = m ∧ r = rd5W m s ∧ r ≠ [] := by
  obtain ⟨s', rfl, h1, h2, h3⟩ := callW_triple (erecRd5_spec p hp n ⟨m, Locals.init []⟩ s) hc
  subst h1
  exact ⟨rfl, h3, h2⟩

/-! ## `erec_cp` -/

section cp
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem cp_rel : ∀ (n : Nat) (m : Mem) (d s l : Word) (r : List Word) (m' : Mem),
    s.toNat + l.toNat ≤ d.toNat → d.toNat + l.toNat ≤ (m.arr64 EREC).size →
    (m.arr64 EREC).size < 2 ^ 64 → callW p n "erec_cp" [d, s, l] m = some (r, m') →
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, ¬ (d.toNat ≤ i ∧ i < d.toNat + l.toNat) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (∀ i < l.toNat, (m'.arr64 EREC)[d.toNat + i]? = (m.arr64 EREC)[s.toNat + i]?) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ hc; rw [callW_zero'] at hc; cases hc
  | succ n ih =>
  intro m d s l r m' hsd hdz hsz hc
  obtain ⟨s', hs', -, hW⟩ := callW_triple (erecCp_spec p hp n ⟨m, Locals.init []⟩ d s l) hc
  simp only at hW
  rw [hs'] at hW
  by_cases hl : l = 0
  · simp only [cpW, hl, ↓reduceIte, Option.some.injEq] at hW
    subst hW
    exact ⟨rfl, MemFrame.refl _ _ _, fun _ _ => rfl, by simp [hl]⟩
  have hl0 : 0 < l.toNat := by
    rcases Nat.eq_zero_or_pos l.toNat with h | h
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hl
    · exact h
  simp only [cpW, hl, ↓reduceIte] at hW
  have hsb : s.toNat < (m.arr64 EREC).size := by omega
  have hdb : d.toNat < (m.arr64 EREC).size := by omega
  rw [if_neg (by omega), if_neg (by omega)] at hW
  cases hca : callW p n "erec_cp" [d + 1, s + 1, l - 1] (m.set64 EREC d (rdW (m.arr64 EREC) s)) with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₂⟩ := x
  rw [hca, memK_some] at hW
  have hm : m₂ = m' := Option.some.inj hW
  subst hm
  have hE : (m.set64 EREC d (rdW (m.arr64 EREC) s)).arr64 EREC =
      (m.arr64 EREC).set! d.toNat (rdW (m.arr64 EREC) s) := Mem.arr64_set64_same _ _ _ _
  have hsz1 : ((m.set64 EREC d (rdW (m.arr64 EREC) s)).arr64 EREC).size = (m.arr64 EREC).size := by
    rw [hE]; simp
  have hd1 : (d + 1).toNat = d.toNat + 1 := toNat_add1 d (by omega)
  have hs1 : (s + 1).toNat = s.toNat + 1 := toNat_add1 s (by omega)
  have hl1 : (l - 1).toNat = l.toNat - 1 := toNat_sub1 l hl
  obtain ⟨h1, h2, h3, h4⟩ := ih _ (d + 1) (s + 1) (l - 1) r₂ m₂ (by rw [hs1, hd1, hl1]; omega)
    (by rw [hd1, hl1, hsz1]; omega) (by rw [hsz1]; exact hsz) hca
  have hfr : MemFrame [EREC] [] m (m.set64 EREC d (rdW (m.arr64 EREC) s)) :=
    MemFrame.set64 m EREC (by decide) _ _
  refine ⟨by rw [h1, hsz1], hfr.trans h2, ?_, ?_⟩
  · intro i hi
    by_cases hid : i = d.toNat
    · -- the written cell
      exact absurd ⟨hid ▸ Nat.le_refl _, by omega⟩ hi
    · rw [h3 i (by rw [hd1, hl1]; omega), hE, arr_set!_get?, if_neg (by omega)]
  · intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [h3 (d.toNat + 0) (by rw [hd1]; omega), hE, arr_set!_get?, if_pos ⟨by omega, hdb⟩]
      rw [Nat.add_zero, rdW]
      simp [hsb]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have := h4 j (by rw [hl1]; omega)
      rw [hd1, hs1, hE, arr_set!_get?, if_neg (by omega)] at this
      rw [show d.toNat + (j + 1) = d.toNat + 1 + j by omega, this, show s.toNat + (j + 1) = s.toNat + 1 + j by omega]

end cp

end L.Arena
