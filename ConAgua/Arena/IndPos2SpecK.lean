import ConAgua.Arena.IndPos2SpecJ

/-! # `IndPos2`, the frame's helpers (lane `indproofs2`, helper `pos2`): records decoded below the
tops (`DecB`) as the words L reads; `NestKey` equality and membership; `nestAcceptGroup`. -/

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
    rw [hslice?_succ] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
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
    xs.length = l ∧ ∀ j (hj : j < l), ∃ v, o + j < iwTop m ∧ iwN m (o + j) = some v ∧
      ∃ hx : j < xs.length, f (truncM m) v = some xs[j]
  | o, 0, xs, h => by simp [decPL] at h; subst h; simp
  | o, l + 1, xs, h => by
    obtain ⟨v0, x, xs', rfl, hv0, hx, hxs'⟩ := decPL_cons h
    obtain ⟨h1, h2⟩ := pos2_decPL_trunc hxs'
    refine ⟨by simp [h1], fun j hj => ?_⟩
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
theorem nkcK_hit (h : r ≠ 0) : nkcK n m o l k (some r) = some 1 := by rw [nkcK, if_pos h]
theorem nkcK_miss (h : ¬ r ≠ 0) : nkcK n m o l k (some r) = nkcW n m (o + 1) (l - 1) k := by rw [nkcK, if_neg h]
end arms
attribute [ind_grind] nkcW_nil nkcW_cons nkcK_hit nkcK_miss

theorem nestKeyEq_spec (p : Prog) (hq : p.lookup "sl_eq" = some slEq)
    (hp : p.lookup "nest_key_eq" = some nestKeyEqL) (n : Nat) (s₀ : St) (k1 k2 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_key_eq" [k1, k2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ nkeWf n s₀.mem k1 k2 = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nestKeyEqL]
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
    rw [invoke_eq _ hp]
    simp only [callFn, nestKeysContainsL]
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
  · rw [if_pos e0] at h; cases h; simp [e0]
  rw [if_neg e0] at h
  simp only [ne_eq, Decidable.not_not] at e0
  by_cases e1 : rdW (m.arr64 IW) (k1 + 1) ≠ rdW (m.arr64 IW) (k2 + 1)
  · rw [if_pos e1] at h; cases h; simp [e1]
  rw [if_neg e1] at h
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
  rw [eqW_ok n m _ _ _ _ r ws1 ws2 hs1 hs2 h, hd1, hd2]
  simp only [e0, e1, decide_true, Bool.true_and]
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
    cases he : nkeWf n m (rdW (m.arr64 IW) o) k with
    | none => rw [he] at h; simp [nkcK] at h
    | some r0 =>
    rw [he] at h
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
