import ConAgua.Arena.IndPos2SpecJ

/-! # `IndPos2`, the frame's helpers (lane `indproofs2`, helper `pos2`): records decoded below the
tops (`DecB`) as the words L reads; `NestKey` equality and membership; `nestAcceptGroup`. -/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Decoded below the tops: the reads lie below the top -/

theorem pos2_hslice_get {k : IdxKind} {a : Array Word} :
    ∀ {o n : Nat} {l : List (Idx k)}, hslice? a o n = some l →
    l.length = n ∧ ∀ j, j < n → ∃ w, a[o + j]? = some w ∧ H w ∧ l[j]? = some (decI w)
  | o, 0, l, h => by simp [hslice?] at h; subst h; simp
  | o, n + 1, l, h => by
    simp only [hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    obtain ⟨h1, h2⟩ := pos2_hslice_get hxs
    obtain ⟨w, hw, hwl, rfl⟩ := hd?_some hx
    refine ⟨by simp [h1], fun j hj => ?_⟩
    cases j with
    | zero => exact ⟨w, by simpa using hw, hwl, rfl⟩
    | succ j =>
      obtain ⟨w', h1', h2', h3'⟩ := h2 j (by omega)
      exact ⟨w', by rw [show o + (j + 1) = o + 1 + j by omega]; exact h1', h2', by simpa using h3'⟩

/-- A handle slice decoded in the cut pool lies below the top. -/
theorem pos2_decHL_trunc {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL (truncM m) o l = some xs) : ∀ j < l, o + j < iwTop m := fun j hj => by
  obtain ⟨-, hg⟩ := pos2_hslice_get h
  obtain ⟨w, hw, -⟩ := hg j hj
  exact (truncM_iw_get hw).1

theorem pos2_iwN_trunc {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) :
    i < iwTop m ∧ iwN m i = some v := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  exact ⟨hi, by simp [iwN, nat?, hw']⟩

theorem pos2_iwH_trunc {k : IdxKind} {m : Mem} {i : Nat} {x : Idx k} (h : iwH (truncM m) i = some x) :
    i < iwTop m ∧ iwH m i = some x := by
  obtain ⟨w, hw, hl, rfl⟩ := hd?_some h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  exact ⟨hi, by simp only [iwH, hd?]; rw [hw']; simp [hl]⟩

/-- A key record decoded below the tops: its words and its `ds` slice below the top. -/
theorem pos2_nk_in {m : Mem} {p : Nat} {kk : NestKey} (h : DecB (fun m => decNK m p) m kk) :
    decNK m p = some kk ∧ NKIn m p (· < iwTop m) := by
  refine ⟨h.get (decNK_mono p), ?_⟩
  have h' : decNK (truncM m) p = some kk := h
  simp only [decNK, decAt, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h'
  obtain ⟨c, hc, u, hu, ds, ⟨o, ho, l, hl, hds⟩, -⟩ := h'
  obtain ⟨h0, -⟩ := pos2_iwH_trunc hc
  obtain ⟨h1, -⟩ := pos2_iwH_trunc hu
  obtain ⟨h2, ho'⟩ := pos2_iwN_trunc ho
  obtain ⟨h3, hl'⟩ := pos2_iwN_trunc hl
  refine ⟨fun j hj => ?_, fun o' l' ho2 hl2 j hj => ?_⟩
  · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> simpa using ‹_›
  · rw [ho'] at ho2; rw [hl'] at hl2; cases ho2; cases hl2
    exact pos2_decHL_trunc hds j hj

/-- **A key decoded below the tops, as the words L reads.** -/
theorem pos2_nk_fields {m : Mem} {key : Word} {kk : NestKey} (h : DecB (fun m => decNK m key.toNat) m kk)
    (htop : iwTop m < 2 ^ 64) :
    H (rdW (m.arr64 IW) key) ∧ decI (rdW (m.arr64 IW) key) = kk.cname ∧
    H (rdW (m.arr64 IW) (key + 1)) ∧ decI (rdW (m.arr64 IW) (key + 1)) = kk.lvls ∧
    decHL m (rdW (m.arr64 IW) (key + 2)).toNat (rdW (m.arr64 IW) (key + 3)).toNat = some kk.ds ∧
    (∀ j < (rdW (m.arr64 IW) (key + 3)).toNat, (rdW (m.arr64 IW) (key + 2)).toNat + j < iwTop m) ∧
    key.toNat + 4 ≤ iwTop m := by
  obtain ⟨h1, h2⟩ := pos2_nk_in h
  exact nk_fields h1 h2 htop

/-- A slice of record pointers decoded below the tops: each element is. -/
theorem pos2_decPL_trunc {α : Type} {f : Mem → Nat → Option α} {m : Mem} :
    ∀ {o l : Nat} {xs : List α}, decPL (truncM m) (f (truncM m)) o l = some xs →
    xs.length = l ∧ ∀ j (_hj : j < l), ∃ v, o + j < iwTop m ∧ iwN m (o + j) = some v ∧
      ∃ hx : j < xs.length, f (truncM m) v = some xs[j]
  | o, 0, xs, h => by simp [decPL] at h; subst h; simp
  | o, l + 1, xs, h => by
    obtain ⟨v0, x, xs', rfl, hv0, hx, hxs'⟩ := decPL_cons h
    obtain ⟨h1, h2⟩ := pos2_decPL_trunc hxs'
    refine ⟨by simp [h1], fun j _hj => ?_⟩
    cases j with
    | zero =>
      obtain ⟨hi, hv⟩ := pos2_iwN_trunc hv0
      exact ⟨v0, by simpa using hi, by simpa using hv, by simp, by simpa using hx⟩
    | succ j =>
      obtain ⟨v, h1', h2', hx', h3'⟩ := h2 j (by omega)
      refine ⟨v, by rw [show o + (j + 1) = o + 1 + j by omega]; exact h1',
        by rw [show o + (j + 1) = o + 1 + j by omega]; exact h2', by simp; omega, ?_⟩
      simpa using h3'

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_key_eq`, `nest_keys_contains`: word models -/

/-- The model of `nest_key_eq(k1, k2)` at exec fuel `n + 1` (the memory is unchanged). -/
def nkeW (n : Nat) (m : Mem) (k1 k2 : Word) : Option Word :=
  if rdW (m.arr64 IW) k1 ≠ rdW (m.arr64 IW) k2 then some 0
  else if rdW (m.arr64 IW) (k1 + 1) ≠ rdW (m.arr64 IW) (k2 + 1) then some 0
  else eqW n m (rdW (m.arr64 IW) (k1 + 2)) (rdW (m.arr64 IW) (k1 + 3)) (rdW (m.arr64 IW) (k2 + 2))
    (rdW (m.arr64 IW) (k2 + 3))

/-- `nest_key_eq` at any exec fuel. -/
def nkeWf : Nat → Mem → Word → Word → Option Word
  | 0, _, _, _ => none
  | n + 1, m, k1, k2 => nkeW n m k1 k2

mutual
/-- The model of `nest_keys_contains(off, l, k)`. -/
def nkcW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, o, l, k => if l = 0 then some 0 else nkcK n m o l k (nkeWf n m (rdW (m.arr64 IW) o) k)
def nkcK (n : Nat) (m : Mem) (o l k : Word) : Option Word → Option Word
  | none => none
  | some r => if r ≠ 0 then some 1 else nkcW n m (o + 1) (l - 1) k
end

section arms
variable (n : Nat) (m : Mem) (o l k r : Word)
theorem nkcW_nil (h : l = 0) : nkcW (n + 1) m o l k = some 0 := by simp [nkcW, h]
theorem nkcW_cons (h : ¬ l = 0) : nkcW (n + 1) m o l k = nkcK n m o l k (nkeWf n m (rdW (m.arr64 IW) o) k) := by
  simp [nkcW, h]
theorem nkcK_hit (h : r ≠ 0) : nkcK n m o l k (some r) = some 1 := by rw [nkcK, ite_eq_left h]
theorem nkcK_miss (h : ¬ r ≠ 0) : nkcK n m o l k (some r) = nkcW n m (o + 1) (l - 1) k := by rw [nkcK, ite_eq_right h]
end arms
attribute [ind_grind] nkcW_nil nkcW_cons nkcK_hit nkcK_miss

theorem nestKeyEq_spec (p : Prog) (hq : p.lookup "sl_eq" = some slEq)
    (hp : p.lookup "nest_key_eq" = some nestKeyEqL) (n : Nat) (s₀ : St) (k1 k2 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_key_eq" [k1, k2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ nkeWf n s₀.mem k1 k2 = some (r.headD 0); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestKeyEqL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, slEq_spec p hq n] <;>
      finish (gen := 20) [nkeWf, nkeW, rdW_eq, LocEq]

theorem nestKeysContains_spec (p : Prog) (hq : p.lookup "sl_eq" = some slEq)
    (he : p.lookup "nest_key_eq" = some nestKeyEqL)
    (hp : p.lookup "nest_keys_contains" = some nestKeysContainsL) (n : Nat) :
    ∀ (s₀ : St) (o l k : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_keys_contains" [o, l, k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ nkcW n s₀.mem o l k = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o l k; rw [invoke_eq _ hp]; simp only [callFn, nestKeysContainsL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l k
    simp only [invoke_eq _ hp, callFn, nestKeysContainsL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, nestKeyEq_spec p hq he n, ih] <;>
      finish (gen := 20) [rdW_eq, LocEq]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `NestKey` equality and membership: the relational side -/

theorem pos2_nk_beq (K1 K2 : NestKey) :
    (K1 == K2) = (K1.cname == K2.cname && K1.lvls == K2.lvls && K1.ds == K2.ds) := by
  cases K1; cases K2; simp only [BEq.beq, instBEqNestKey.beq, Bool.and_assoc]

theorem pos2_map_decI_inj {k : IdxKind} : ∀ (ws1 ws2 : List Word), (∀ w ∈ ws1, H w) → (∀ w ∈ ws2, H w) →
    ((ws1.map (decI : Word → Idx k)) = ws2.map decI ↔ ws1 = ws2)
  | [], [], _, _ => by simp
  | [], _ :: _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | w1 :: ws1, w2 :: ws2, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq]
    rw [pos2_map_decI_inj ws1 ws2 (fun w hw => h1 w (by simp [hw])) (fun w hw => h2 w (by simp [hw]))]
    constructor
    · rintro ⟨e, rfl⟩; exact ⟨decI_inj (h1 w1 (by simp)) (h2 w2 (by simp)) e, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

theorem pos2_nk_beq_comm (K1 K2 : NestKey) : (K1 == K2) = (K2 == K1) := by
  rw [pos2_nk_beq, pos2_nk_beq, BEq.comm (a := K1.cname), BEq.comm (a := K1.lvls), BEq.comm (a := K1.ds)]

/-- **`nest_key_eq` is `NestKey` equality**, both keys decoded below the tops. -/
theorem nkeWf_ok {n : Nat} {m : Mem} {k1 k2 r : Word} {K1 K2 : NestKey}
    (h : nkeWf n m k1 k2 = some r) (h1 : DecB (fun m => decNK m k1.toNat) m K1)
    (h2 : DecB (fun m => decNK m k2.toNat) m K2) (htop : iwTop m < 2 ^ 64) :
    r = if K1 == K2 then 1 else 0 := by
  cases n with
  | zero => simp [nkeWf] at h
  | succ n =>
  obtain ⟨a0, a1, a2, a3, a4, a5, -⟩ := pos2_nk_fields h1 htop
  obtain ⟨b0, b1, b2, b3, b4, b5, -⟩ := pos2_nk_fields h2 htop
  simp only [nkeWf, nkeW] at h
  rw [pos2_nk_beq, ← a1, ← b1, ← a3, ← b3, decI_beq' _ _ a0 b0, decI_beq' _ _ a2 b2]
  by_cases e0 : rdW (m.arr64 IW) k1 ≠ rdW (m.arr64 IW) k2
  · rw [ite_eq_left e0] at h; cases h; simp [e0]
  rw [ite_eq_right e0] at h
  simp only [ne_eq, Decidable.not_not] at e0
  by_cases e1 : rdW (m.arr64 IW) (k1 + 1) ≠ rdW (m.arr64 IW) (k2 + 1)
  · rw [ite_eq_left e1] at h; cases h; simp [e1]
  rw [ite_eq_right e1] at h
  simp only [ne_eq, Decidable.not_not] at e1
  have hb1 : (rdW (m.arr64 IW) (k1 + 2)).toNat + (rdW (m.arr64 IW) (k1 + 3)).toNat < 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos (rdW (m.arr64 IW) (k1 + 3)).toNat with hz | hz
    · rw [hz]; exact (rdW (m.arr64 IW) (k1 + 2)).toNat_lt
    · have := a5 _ (by omega : (rdW (m.arr64 IW) (k1 + 3)).toNat - 1 < _); omega
  have hb2 : (rdW (m.arr64 IW) (k2 + 2)).toNat + (rdW (m.arr64 IW) (k2 + 3)).toNat < 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos (rdW (m.arr64 IW) (k2 + 3)).toNat with hz | hz
    · rw [hz]; exact (rdW (m.arr64 IW) (k2 + 2)).toNat_lt
    · have := b5 _ (by omega : (rdW (m.arr64 IW) (k2 + 3)).toNat - 1 < _); omega
  obtain ⟨ws1, hs1, hd1, hw1⟩ := slR_of_decHL m _ _ _ a4 hb1
  obtain ⟨ws2, hs2, hd2, hw2⟩ := slR_of_decHL m _ _ _ b4 hb2
  simp only [UInt64.ofNat_toNat] at hs1 hs2
  simp only [eqW_ok n m _ _ _ _ r ws1 ws2 hs1 hs2 h, hd1, hd2, e0, e1, decide_true, Bool.true_and]
  by_cases e : ws1 = ws2
  · subst e; simp
  · have : ¬ (ws1.map (decI : Word → EIdx)) = ws2.map decI :=
      fun hh => e ((pos2_map_decI_inj ws1 ws2 hw1 hw2).mp hh)
    simp [e, this]

/-- A key slice decoded below the tops. -/
def KsB (m : Mem) (o l : Nat) (ks : List NestKey) : Prop := DecB (fun m => decPL m (decNK m) o l) m ks

theorem KsB.grow {m m' : Mem} {o l : Nat} {ks : List NestKey} (h : KsB m o l ks) (hg : IWGrow m m') :
    KsB m' o l ks := DecB.grow (OMono.decPL decNK_mono o l) hg h

theorem KsB.nil (m : Mem) (o : Nat) : KsB m o 0 [] := by simp [KsB, DecB, decPL]

/-- The head of a nonempty key slice, and its rest. -/
theorem KsB.cons {m : Mem} {o l : Nat} {ks : List NestKey} (h : KsB m o (l + 1) ks) :
    ∃ v K ks', ks = K :: ks' ∧ o < iwTop m ∧ iwN m o = some v ∧ DecB (fun m => decNK m v) m K ∧
      KsB m (o + 1) l ks' := by
  obtain ⟨v, K, ks', rfl, hv, hK, hks⟩ := decPL_cons (show decPL (truncM m) (decNK (truncM m)) o (l + 1) = some ks from h)
  obtain ⟨hi, hv'⟩ := pos2_iwN_trunc hv
  exact ⟨v, K, ks', rfl, hi, hv', hK, hks⟩

/-- **`nest_keys_contains` is `List.contains`**. -/
theorem nkcW_ok (k : Word) (K : NestKey) : ∀ (n : Nat) (m : Mem) (o l r : Word) (ks : List NestKey),
    nkcW n m o l k = some r → KsB m o.toNat l.toNat ks → DecB (fun m => decNK m k.toNat) m K →
    iwTop m < 2 ^ 64 → r = if ks.contains K then 1 else 0 := by
  intro n
  induction n with
  | zero => intro m o l r ks h; simp [nkcW] at h
  | succ n ih =>
    intro m o l r ks h hks hK htop
    by_cases hl0 : l = 0
    · rw [nkcW_nil (h := hl0)] at h; cases h
      subst hl0
      have : ks = [] := by
        have := (show decPL (truncM m) (decNK (truncM m)) o.toNat 0 = some ks from hks)
        simpa [decPL] using this.symm
      subst this; simp
    rw [nkcW_cons (h := hl0)] at h
    obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by
      have : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
    rw [hl'] at hks
    obtain ⟨v, K0, ks', rfl, hoi, hv, hK0, hks'⟩ := hks.cons
    have hrd : (rdW (m.arr64 IW) o).toNat = v := by
      simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at hv
      obtain ⟨w, hw, rfl⟩ := hv; simp [rdW, hw]
    rcases he : nkeWf n m (rdW (m.arr64 IW) o) k with _ | r0 <;> rw [he] at h; · simp [nkcK] at h
    have hr0 := nkeWf_ok he (by rw [hrd]; exact hK0) hK htop
    have hcons : (K0 :: ks').contains K = ((K0 == K) || ks'.contains K) := by
      simp [List.contains_cons, pos2_nk_beq_comm K]
    by_cases hb : r0 ≠ 0
    · rw [nkcK_hit (h := hb)] at h; cases h
      have : (K0 == K) = true := by
        cases hc : (K0 == K) with
        | true => rfl
        | false => rw [hc] at hr0; exact absurd (by simpa using hr0) hb
      simp [hcons, this]
    · rw [nkcK_miss (h := hb)] at h
      have : (K0 == K) = false := by
        cases hc : (K0 == K) with
        | false => rfl
        | true => rw [hc] at hr0; simp at hr0 hb; rw [hb] at hr0; exact absurd hr0 (by decide)
      have ho1 : (o + 1).toNat = o.toNat + 1 := word_add_toNat (by simp; omega)
      have hl1 : (l - 1).toNat = l' := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
      rw [ih m (o + 1) (l - 1) r ks' h (by rw [ho1, hl1]; exact hks') hK htop]
      simp [hcons, this]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Pointer slices decoded below the tops, element by element -/

section pslice
variable {α : Type} {f : Mem → Nat → Option α}

/-- The elements of a pointer slice decoded below the tops. -/
theorem pos2_decB_elems {m : Mem} {o l : Nat} {xs : List α}
    (h : DecB (fun m => decPL m (f m) o l) m xs) :
    xs.length = l ∧ ∀ j (hj : j < xs.length), ∃ v, o + j < iwTop m ∧ iwN m (o + j) = some v ∧
      DecB (fun m => f m v) m xs[j] := by
  obtain ⟨h1, h2⟩ := pos2_decPL_trunc h
  refine ⟨h1, fun j hj => ?_⟩
  obtain ⟨v, a, b, hx, c⟩ := h2 j (by omega)
  exact ⟨v, a, b, c⟩

/-- A pointer slice whose elements are decoded below the tops is. -/
theorem pos2_decB_of_elems {m : Mem} {o : Nat} {xs : List α}
    (h : ∀ j (hj : j < xs.length), ∃ v, o + j < iwTop m ∧ iwN m (o + j) = some v ∧
      DecB (fun m => f m v) m xs[j]) :
    DecB (fun m => decPL m (f m) o xs.length) m xs := by
  show decPL (truncM m) (f (truncM m)) o xs.length = some xs
  refine decPL_of_get _ xs o fun j hj => ?_
  obtain ⟨v, h1, h2, h3⟩ := h j hj
  exact ⟨v, by rw [iwN_truncM h1]; exact h2, h3⟩

/-- **A pointer slice grown by one element** (`sl_snoc`): the old words copied to `q`, `w` after. -/
theorem pos2_decB_snoc (hf : ∀ q, OMono (fun m => f m q)) {m m' : Mem} {o l q : Nat} {xs : List α} {x : α}
    {w : Word} (h : DecB (fun m => decPL m (f m) o l) m xs) (hg : IWGrow m m') (hq : q + l < iwTop m')
    (hw : ∀ i < l, (m'.arr64 IW)[q + i]? = (m.arr64 IW)[o + i]?) (hx : (m'.arr64 IW)[q + l]? = some w)
    (hxd : DecB (fun m => f m w.toNat) m' x) :
    DecB (fun m => decPL m (f m) q (l + 1)) m' (xs ++ [x]) := by
  obtain ⟨hl, he⟩ := pos2_decB_elems h
  have := pos2_decB_of_elems (m := m') (o := q) (xs := xs ++ [x]) (f := f) fun j hj => by
    simp only [List.length_append, List.length_cons, List.length_nil] at hj
    by_cases hjl : j < xs.length
    · obtain ⟨v, h1, h2, h3⟩ := he j hjl
      refine ⟨v, by omega, ?_, by rw [List.getElem_append_left hjl]; exact (DecB.grow (hf v) hg h3)⟩
      simp only [iwN, nat?, iwA] at h2 ⊢; rw [hw j (by omega)]; exact h2
    · have hj' : j = xs.length := by omega
      subst hj'
      refine ⟨w.toNat, by omega, by simp [iwN, nat?, iwA, hl, hx], ?_⟩
      simpa using hxd
  simpa [hl] using this

/-- **Two pointer slices concatenated** (`sl_append`). -/
theorem pos2_decB_append (hf : ∀ q, OMono (fun m => f m q)) {m m' : Mem} {o1 l1 o2 l2 q : Nat}
    {xs ys : List α} (h1 : DecB (fun m => decPL m (f m) o1 l1) m xs)
    (h2 : DecB (fun m => decPL m (f m) o2 l2) m ys) (hg : IWGrow m m') (hq : q + l1 + l2 ≤ iwTop m')
    (hw1 : ∀ i < l1, (m'.arr64 IW)[q + i]? = (m.arr64 IW)[o1 + i]?)
    (hw2 : ∀ i < l2, (m'.arr64 IW)[q + l1 + i]? = (m.arr64 IW)[o2 + i]?) :
    DecB (fun m => decPL m (f m) q (l1 + l2)) m' (xs ++ ys) := by
  obtain ⟨hl1, he1⟩ := pos2_decB_elems h1
  obtain ⟨hl2, he2⟩ := pos2_decB_elems h2
  have := pos2_decB_of_elems (m := m') (o := q) (xs := xs ++ ys) (f := f) fun j hj => by
    simp only [List.length_append] at hj
    by_cases hjl : j < xs.length
    · obtain ⟨v, a, b, c⟩ := he1 j hjl
      refine ⟨v, by omega, ?_, by rw [List.getElem_append_left hjl]; exact (DecB.grow (hf v) hg c)⟩
      simp only [iwN, nat?, iwA] at b ⊢; rw [hw1 j (by omega)]; exact b
    · obtain ⟨v, a, b, c⟩ := he2 (j - xs.length) (by omega)
      refine ⟨v, by omega, ?_, by rw [List.getElem_append_right (by omega)]; exact (DecB.grow (hf v) hg c)⟩
      simp only [iwN, nat?, iwA] at b ⊢
      have := hw2 (j - xs.length) (by omega)
      rw [show q + l1 + (j - xs.length) = q + j by omega] at this
      rw [this]; exact b
  simpa [hl1, hl2] using this

end pslice

/-- A record of four words `[c, us, dO, dL]` (`rec4`) is the key `⟨c, us, ds⟩`, decoded below the
tops when `ds`'s slice is. -/
theorem pos2_key_rec {m' : Mem} {q c us dO dL : Word} {ds : List EIdx} (hc : H c) (hus : H us)
    (hq : q.toNat + 4 ≤ iwTop m')
    (hget : ∀ j < [c, us, dO, dL].length, (m'.arr64 IW)[q.toNat + j]? = [c, us, dO, dL][j]?)
    (hds : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m' ds) :
    DecB (fun m => decNK m q.toNat) m' ⟨decI c, decI us, ds⟩ := by
  have g : ∀ j < 4, ((truncM m').arr64 IW)[q.toNat + j]? = [c, us, dO, dL][j]? := fun j hj => by
    rw [show ((truncM m').arr64 IW) = iwA (truncM m') from rfl, truncM_iw_eq (by omega)]; exact hget j (by simpa using hj)
  show decNK (truncM m') q.toNat = _
  exact decNK_of_words (by simpa using g 0 (by omega)) hc (by simpa using g 1 (by omega)) hus
    (by simpa using g 2 (by omega)) (by simpa using g 3 (by omega)) hds

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_accept_group` refines `nestAcceptGroup` -/

mutual
def nagW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, us, dO, dL, gO, gL, kO, kL =>
    if gL = 0 then some ([kO, kL], m)
    else nagK1 n us dO dL gO gL kO kL (posRecW m [rdW (m.arr64 IW) (rdW (m.arr64 IW) gO), us, dO, dL])
def nagK1 (n : Nat) (us dO dL gO gL kO kL : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (key, m1) => nagK2 n us dO dL gO gL kO kL key m1 (nkcW n m1 kO kL key)
def nagK2 (n : Nat) (us dO dL gO gL kO kL key : Word) (m1 : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some b => if b ≠ 0 then nagW n m1 us dO dL (gO + 1) (gL - 1) kO kL
    else nagK3 n us dO dL gO gL (snocW n m1 kO kL key)
def nagK3 (n : Nat) (us dO dL gO gL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => nagW n m2 us dO dL (gO + 1) (gL - 1) (r.headD 0) (r.tail.headD 0)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (us dO dL gO gL kO kL key b : Word) (r : List Word)
theorem nagW_nil (h : gL = 0) : nagW (n + 1) m us dO dL gO gL kO kL = some ([kO, kL], m) := by simp [nagW, h]
theorem nagW_cons (h : ¬ gL = 0) : nagW (n + 1) m us dO dL gO gL kO kL =
    nagK1 n us dO dL gO gL kO kL (posRecW m [rdW (m.arr64 IW) (rdW (m.arr64 IW) gO), us, dO, dL]) := by
  simp [nagW, h]
theorem nagK1_some : nagK1 n us dO dL gO gL kO kL (some (key, m1)) =
    nagK2 n us dO dL gO gL kO kL key m1 (nkcW n m1 kO kL key) := by rw [nagK1]
theorem nagK2_hit (h : b ≠ 0) : nagK2 n us dO dL gO gL kO kL key m1 (some b) =
    nagW n m1 us dO dL (gO + 1) (gL - 1) kO kL := by rw [nagK2, ite_eq_left h]
theorem nagK2_miss (h : ¬ b ≠ 0) : nagK2 n us dO dL gO gL kO kL key m1 (some b) =
    nagK3 n us dO dL gO gL (snocW n m1 kO kL key) := by rw [nagK2, ite_eq_right h]
theorem nagK3_some : nagK3 n us dO dL gO gL (some (r, m2)) =
    nagW n m2 us dO dL (gO + 1) (gL - 1) (r.headD 0) (r.tail.headD 0) := by rw [nagK3]
end arms
attribute [ind_grind] nagW_nil nagW_cons nagK1_some nagK2_hit nagK2_miss nagK3_some

/-- The lookups of `nest_accept_group`. -/
structure NagLook (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  hc2 : p.lookup "iw_copy" = some iwCopy
  h4 : p.lookup "rec4" = some rec4
  hsn : p.lookup "sl_snoc" = some slSnoc
  hq : p.lookup "sl_eq" = some slEq
  he : p.lookup "nest_key_eq" = some nestKeyEqL
  hkc : p.lookup "nest_keys_contains" = some nestKeysContainsL
  hp : p.lookup "nest_accept_group" = some nestAcceptGroupL

theorem nestAcceptGroup_spec (p : Prog) (L : NagLook p) (n : Nat) :
    ∀ (s₀ : St) (us dO dL gO gL kO kL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_accept_group" [us, dO, dL, gO, gL, kO, kL]
    ⦃fun r s' => LocEq s' s₀ ∧
      nagW n s₀.mem us dO dL gO gL kO kL = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ us dO dL gO gL kO kL
    rw [invoke_eq _ L.hp]; simp only [callFn, nestAcceptGroupL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ us dO dL gO gL kO kL
    simp only [invoke_eq _ L.hp, callFn, nestAcceptGroupL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        posRec4_specW p L.ha L.h4 n, nestKeysContains_spec p L.hq L.he L.hkc n,
        slSnoc_specW p L.ha L.hc2 L.hsn n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, Locals.init_cons_zero]

end L.Ind

namespace L.Ind

open L.Arena

/-- **`nest_accept_group` is `nestAcceptGroup`** over the decoded group and key slice. -/
theorem nagW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (us dO dL : Word) (ds : List EIdx)
    (hus : H us) : ∀ (n : Nat) (m m' : Mem) (a : AState) (gO gL kO kL : Word) (grp : List (NIdx × EIdx))
    (keys : Array NestKey) (r : List Word),
    nagW n m us dO dL gO gL kO kL = some (r, m') → StageR dn vis fe m a →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp →
    KsB m kO.toNat kL.toNat keys.toList → kO.toNat + kL.toNat ≤ iwTop m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      KsB m' (r.headD 0).toNat (r.tail.headD 0).toNat (nestAcceptGroup (decI us) ds grp keys).toList ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  intro n
  induction n with
  | zero => intro m m' a gO gL kO kL grp keys r h; simp [nagW] at h
  | succ n ih =>
    intro m m' a gO gL kO kL grp keys r h hS hds hgl hgb hgrp hks hkb
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    by_cases hg0 : gL = 0
    · rw [nagW_nil (h := hg0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hg0
      have : grp = [] := List.eq_nil_of_length_eq_zero (by simpa using hgl.symm)
      subst this
      exact ⟨hS, IWGrow.refl _, by simpa [nestAcceptGroup] using hks, by simpa using hkb⟩
    rw [nagW_cons (h := hg0)] at h
    obtain ⟨⟨c, t⟩, grp', rfl⟩ : ∃ x grp', grp = x :: grp' := by
      cases grp with
      | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hgl)) hg0
      | cons x grp' => exact ⟨x, grp', rfl⟩
    simp only [List.length_cons] at hgl hgb
    obtain ⟨w, cw, tw, h1, h2, h3, h4, h5, -, -, -⟩ := hgrp 0 (by simp)
    have hrw : rdW (m.arr64 IW) gO = w := by simp only [Nat.add_zero] at h1; simp [rdW, h1]
    have hrc : rdW (m.arr64 IW) w = cw := by simp [rdW, h3]
    rw [hrw, hrc] at h
    simp only [List.getElem_cons_zero] at h5
    rcases hk : posRecW m [cw, us, dO, dL] with _ | ⟨key, m1⟩ <;> rw [hk] at h; · simp [nagK1] at h
    rw [nagK1_some] at h
    obtain ⟨hS1, hg1, hkq, ht1, hget1⟩ := posRecW_stage hk hS (by simp)
    simp only [List.length_cons, List.length_nil] at ht1
    have hds1 := DecB.grow (OMono.decHL _ _) hg1 hds
    have hK : DecB (fun m => decNK m key.toNat) m1 ⟨decI cw, decI us, ds⟩ :=
      pos2_key_rec h4 hus (by omega) hget1 hds1
    have hks1 := hks.grow hg1
    have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
    have hgO1 : (gO + 1).toNat = gO.toNat + 1 := word_add_toNat (by simp; omega)
    have hgL1 : (gL - 1).toNat = grp'.length := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hgrp' : GrpAt m1 (gO + 1).toNat grp' := by
      rw [hgO1]
      have g1 := hgrp.grow (by simpa using hgb) hg1
      intro i hi
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := g1 (i + 1) (by simp; omega)
      exact ⟨a1, a2, a3, by rw [show UInt64.toNat gO + 1 + i = UInt64.toNat gO + (i + 1) by omega]; exact a4, a5, a6, a7, by simpa using a8, a9, a10,
        by simpa using a11⟩
    rcases hc : nkcW n m1 kO kL key with _ | b <;> rw [hc] at h; · simp [nagK2] at h
    have hb := nkcW_ok key _ n m1 kO kL b keys.toList hc hks1 hK htop1
    rw [h5] at hb
    by_cases hbn : b ≠ 0
    · rw [nagK2_hit (h := hbn)] at h
      have hin : keys.toList.contains ⟨c, decI us, ds⟩ = true := by
        cases e : keys.toList.contains ⟨c, decI us, ds⟩ with
        | true => rfl
        | false => rw [e] at hb; exact absurd hb (by simpa using hbn)
      obtain ⟨hS', hg', hk', hb'⟩ := ih m1 m' a (gO + 1) (gL - 1) kO kL grp' keys r h hS1 hds1 hgL1
        (by rw [hgO1]; have := hg1.1; omega) hgrp' hks1 (by have := hg1.1; omega)
      refine ⟨hS', hg1.trans hg', ?_, hb'⟩
      simp only [nestAcceptGroup, ← Array.contains_toList, hin, ite_true]
      exact hk'
    · rw [nagK2_miss (h := hbn)] at h
      have hout : keys.toList.contains ⟨c, decI us, ds⟩ = false := by
        cases e : keys.toList.contains ⟨c, decI us, ds⟩ with
        | false => rfl
        | true => rw [e] at hb; simp at hbn hb; rw [hbn] at hb; exact absurd hb (by decide)
      rcases hsn : snocW n m1 kO kL key with _ | ⟨r2, m2⟩ <;> rw [hsn] at h; · simp [nagK3] at h
      rw [nagK3_some] at h
      obtain ⟨hS2, hg2, hr0, hr1, ht2, hw2, hx2⟩ := snocW_words hsn hS1 (by have := hg1.1; omega)
      have hks2 : KsB m2 (r2.headD 0).toNat (r2.tail.headD 0).toNat (keys.push ⟨c, decI us, ds⟩).toList := by
        rw [hr0, hr1, Array.toList_push]
        exact pos2_decB_snoc decNK_mono hks1 hg2 (by omega) hw2 hx2 (by rw [← h5]; exact DecB.grow (decNK_mono _) hg2 hK)
      obtain ⟨hS', hg', hk', hb'⟩ := ih m2 m' a (gO + 1) (gL - 1) _ _ grp' _ r h hS2
        (DecB.grow (OMono.decHL _ _) hg2 hds1) hgL1
        (by rw [hgO1]; have := hg1.1; have := hg2.1; omega) (hgrp'.grow (by rw [hgO1]; have := hg1.1; omega) hg2) hks2
        (by rw [hr0, hr1]; omega)
      refine ⟨hS', (hg1.trans hg2).trans hg', ?_, hb'⟩
      simp only [nestAcceptGroup, ← Array.contains_toList, hout, Bool.false_eq_true, ite_false]
      exact hk'

end L.Ind

namespace L.Ind

open L.Arena

/-- **`nest_accept_group` refines `nestAcceptGroup`** (a pure twin: the key slice it returns
decodes as the accepted keys). -/
@[refines ConRon.Arena.nestAcceptGroup]
theorem nestAcceptGroup_refines (p : Prog) (L : NagLook p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (us dO dL gO gL kO kL : Word)
    (ds : List EIdx) (grp : List (NIdx × EIdx)) (keys : Array NestKey) (hS : StageR dn vis fe s₀.mem a₀)
    (hus : H us) (hds : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) s₀.mem ds)
    (hgl : gL.toNat = grp.length) (hgb : gO.toNat + grp.length ≤ iwTop s₀.mem)
    (hgrp : GrpAt s₀.mem gO.toNat grp) (hks : KsB s₀.mem kO.toNat kL.toNat keys.toList)
    (hkb : kO.toNat + kL.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_accept_group" [us, dO, dL, gO, gL, kO, kL]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      KsB s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat (nestAcceptGroup (decI us) ds grp keys).toList ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem; ⊤⦄ := by
  refine triple_post (nestAcceptGroup_spec p L n s₀ us dO dL gO gL kO kL) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨h1, h2, h3, h4⟩ := nagW_ok dn vis fe us dO dL ds hus n _ _ a₀ gO gL kO kL grp keys _ hm hS hds hgl hgb
    hgrp hks hkb
  exact ⟨hlc, h1, h2, by simpa using h3, by simpa using h4⟩

end L.Ind
