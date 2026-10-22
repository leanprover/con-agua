import ConAgua.Arena.PromoteRec
import ConAgua.Arena.PromoteERef

/-!
# The record side of the promotion refines the twin's

The three `EREC` list promotions refine `promoteNList`/`promoteLList`/`promoteEList` over a
slice that `hslice?` decodes, the results written above it; `promote_slice` allocates;
`promote_cv` refines `promoteCV` (a record that `decCV` decodes, promoted into one that decodes
to the twin's result), `promote_vg` refines `promoteVG PMemo.empty coreWalkFuel`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## `erec_alloc`, `hslice?` -/

theorem erAlloc_facts {m m' : Mem} {k q : Word} (h : erAllocW m k = some (q, m')) :
    q = etop m ∧ m' = m.set64 CTL 129 (q + k) ∧ (q + k).toNat = q.toNat + k.toNat ∧
      q.toNat + k.toNat ≤ (m.arr64 EREC).size ∧ 129 < (m.arr64 CTL).size := by
  unfold erAllocW at h
  split at h
  · cases h
  rename_i hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [not_or] at hc
  obtain ⟨h1, h2, h3⟩ := hc
  have h1 : 129 < (m.arr64 CTL).size := Nat.lt_of_not_le h1
  have h2 := UInt64.not_lt.mp h2
  have h3 := UInt64.not_lt.mp h3
  rw [len64_eq] at h2 h3
  rw [UInt64.le_iff_toNat_le] at h2
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h2)] at h3
  simp only [UInt64.toNat_ofNat'] at h2 h3
  have hsz : (m.arr64 EREC).size % 2 ^ 64 ≤ (m.arr64 EREC).size := Nat.mod_le _ _
  refine ⟨rfl, rfl, ?_, ?_, h1⟩
  · rw [UInt64.toNat_add]; have := (etop m).toNat_lt; have := k.toNat_lt; omega
  · omega

theorem hslice?_zero (a : Array Word) (o : Nat) {k : IdxKind} :
    (hslice? a o 0 : Option (List (Idx k))) = some [] := rfl

theorem hd?_of {a : Array Word} {i : Nat} {k : IdxKind} {w : Word} (h : a[i]? = some w)
    (hw : w.toNat < 2 ^ 32) : (hd? a i : Option (Idx k)) = some (decI w) := by
  simp [hd?, h, hw]

/-- Every word of a decoded slice is the decoding's handle word, read in place. -/
theorem rdW_of_hd? {a : Array Word} {i : Nat} {k : IdxKind} {x : Idx k} (h : hd? a i = some x)
    (j : Word) (hj : j.toNat = i) : rdW a j = x.word.toUInt64 ∧ j.toNat < a.size := by
  obtain ⟨w, hw, hlt, rfl⟩ := hd?_some h
  rw [← hj] at hw
  refine ⟨by rw [rdW, hw]; simp; exact ((word_decI _ w hlt).mpr rfl).symm, ?_⟩
  rcases Array.getElem?_eq_some_iff.mp hw with ⟨hh, -⟩; exact hh

/-- An `EREC` write keeps the arena relation and the promotion memo. -/
theorem erec_set {m : Mem} {a : AState} {pm : PMemo} (hD : ArenaD m a) (hP : PMemoR m pm)
    (q x : Word) : ArenaD (m.set64 EREC q x) a ∧ PMemoR (m.set64 EREC q x) pm := by
  have hf : MemFrame [EREC] [] m (m.set64 EREC q x) := MemFrame.set64 m EREC (by decide) q x
  exact ⟨⟨ArenaR.frame_ext _ _ (by simp [EREC]) (by simp) m _ hf a hD.1,
    DerR.frameM _ _ m _ hf (by simp [EREC]) a hD.2⟩,
    hP.frame (by simp [EREC]) (by simp) hf⟩

/-! ## The twin's lists -/

theorem promoteNList_nil (pm : PMemo) (fuel : Nat) : promoteNList pm fuel [] = pure (pm, []) := by
  rw [promoteNList]
theorem promoteNList_cons (pm : PMemo) (fuel : Nat) (u : NIdx) (us : List NIdx) :
    promoteNList pm fuel (u :: us) = (do
      let (m, u) ← promoteN pm fuel u
      let (m, us) ← promoteNList m fuel us
      pure (m, u :: us)) := by
  rw [promoteNList]
theorem promoteEList_nil (pm : PMemo) (fuel : Nat) : promoteEList pm fuel [] = pure (pm, []) := by
  rw [promoteEList]
theorem promoteEList_cons (pm : PMemo) (fuel : Nat) (u : EIdx) (us : List EIdx) :
    promoteEList pm fuel (u :: us) = (do
      let (m, u) ← promoteE pm fuel u
      let (m, us) ← promoteEList m fuel us
      pure (m, u :: us)) := by
  rw [promoteEList]

/-- A slice decodes the same in an array that agrees below its end. -/
theorem hslice?_agree {a b : Array Word} {t : Nat} (h : ∀ i < t, b[i]? = a[i]?) {o c : Nat}
    (hc : o + c ≤ t) {k : IdxKind} :
    (hslice? b o c : Option (List (Idx k))) = hslice? a o c := by
  simp only [hslice?]
  exact mapM_congr' _ _ _ fun j hj => by
    simp only [List.mem_range] at hj
    simp only [hd?, h (o + j) (by omega)]

section lists
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`promote_n_list` refines `promoteNList`** over the slice `(o, l)` that `hslice?` decodes, the results
written at `[q, q + l)` above it. -/
theorem nlist_rel : ∀ n : Nat, ∀ (m : Mem) (a : AState) (pm : PMemo) (f o l q : Word)
    (us : List NIdx) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → hslice? (m.arr64 EREC) o.toNat l.toNat = some us →
    o.toNat + l.toNat ≤ q.toNat → q.toNat + l.toNat ≤ (m.arr64 EREC).size →
    (m.arr64 EREC).size < 2 ^ 64 → callW p n "promote_n_list" [f, o, l, q] m = some (r, m') →
    ∃ a' pm' us', (promoteNList pm f.toNat us).run a = .ok ((pm', us'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ hslice? (m'.arr64 EREC) q.toNat l.toNat = some us' ∧
      (∀ i < q.toNat, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
      (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) eCtl m m' := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc; rw [callW_zero'] at hc; cases hc
  | succ n ih =>
  intro m a pm f o l q us r m' hD hP hsl hoq hqs hsz hc
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (promoteNList_spec p hp n ⟨m, Locals.init []⟩ f o l q) hc
  simp only at hW
  by_cases hl : l = 0
  · rw [listW_nil _ _ _ _ _ _ _ _ _ hl] at hW
    cases hW
    subst hl
    have hus : us = [] := by simpa [hslice?] using hsl.symm
    subst hus
    refine ⟨a, pm, [], ?_, hD, hP, rfl, fun _ _ => rfl, rfl, rfl, MemFrame.refl _ _ _⟩
    rw [promoteNList_nil]; rfl
  have hl1 : l.toNat = (l - 1).toNat + 1 := by
    rw [toNat_sub1 l hl]; have := toNat_pred l hl; omega
  rw [hl1, L.Ind.hslice?_succ] at hsl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hsl
  obtain ⟨u, hu, us₀, hus, rfl⟩ := hsl
  obtain ⟨hrd, ho⟩ := rdW_of_hd? hu o rfl
  rw [listW_cons _ _ _ _ _ _ _ _ _ hl (by omega), hrd] at hW
  cases hca : callW p n "promote_n" [f, u.word.toUInt64] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₁⟩ := x
  rw [hca] at hW
  obtain ⟨a₁, pm₁, hrun₁, hD₁, hP₁, hpw₁, hcp₁, hfr₁, -, -, -⟩ :=
    (pn_rel p hp n).1 m a pm f _ r₁ m₁ hD hP (word_lt u) hca
  rw [decI_word] at hrun₁
  have hE₁ : m₁.arr64 EREC = m.arr64 EREC := hfr₁.1 EREC (by decide) (by decide)
  by_cases hq₁ : (m₁.arr64 EREC).size ≤ q.toNat
  · simp [listK, hq₁] at hW
  rw [listK_some (hq := hq₁)] at hW
  cases hcb : callW p n "promote_n_list" [f, o + 1, l - 1, q + 1]
      (m₁.set64 EREC q (r₁.headD 0)) with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₂⟩ := x
  rw [hcb, memK_some] at hW
  cases hW
  obtain ⟨hD₁', hP₁'⟩ := erec_set hD₁ hP₁ q (r₁.headD 0)
  have hE₁' : (m₁.set64 EREC q (r₁.headD 0)).arr64 EREC =
      (m₁.arr64 EREC).set! q.toNat (r₁.headD 0) := Mem.arr64_set64_same _ _ _ _
  have ho1 : (o + 1).toNat = o.toNat + 1 := toNat_add1 o (by omega)
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add1 q (by omega)
  have hag : ∀ i < q.toNat, ((m₁.set64 EREC q (r₁.headD 0)).arr64 EREC)[i]? = (m.arr64 EREC)[i]? := by
    intro i hi
    rw [hE₁', Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hE₁]
    simp [show q.toNat ≠ i by omega]
  have hsl₁ : hslice? ((m₁.set64 EREC q (r₁.headD 0)).arr64 EREC) (o + 1).toNat (l - 1).toNat =
      some us₀ := by
    rw [ho1, ← hus]
    exact hslice?_agree hag (by omega)
  obtain ⟨a₂, pm₂, us₂, hrun₂, hD₂, hP₂, hsl₂, hag₂, hsz₂, hcp₂, hfr₂⟩ :=
    ih _ a₁ pm₁ f (o + 1) (l - 1) (q + 1) us₀ r₂ _ hD₁' hP₁' hsl₁ (by rw [ho1, hq1]; omega)
      (by rw [hq1, size_set64, hE₁]; omega) (by rw [size_set64, hE₁]; exact hsz) hcb
  refine ⟨a₂, pm₂, decI (r₁.headD 0) :: us₂, ?_, hD₂, hP₂, ?_, ?_, ?_, hcp₂.trans hcp₁, ?_⟩
  · rw [promoteNList_cons, run_bind_ok hrun₁]
    simp only
    rw [run_bind_ok hrun₂]; rfl
  · rw [hl1, L.Ind.hslice?_succ, ← hq1, hsl₂]
    have hx : ((s'.mem).arr64 EREC)[q.toNat]? = some (r₁.headD 0) := by
      rw [hag₂ q.toNat (by omega), hE₁', Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds]
      simp [show q.toNat < (m₁.arr64 EREC).size by omega]
    rw [hd?_of hx hpw₁.1]; rfl
  · intro i hi
    rw [hag₂ i (by omega), hag i hi]
  · rw [hsz₂, size_set64, hE₁]
  · exact ((hfr₁.mono (by simp) (by simp)).trans
      ((MemFrame.set64 _ EREC (by decide) _ _).mono (by simp) (by simp))).trans hfr₂

/-- **`promote_l_list` refines `promoteLList`** over the slice `(o, l)` that `hslice?` decodes, the results
written at `[q, q + l)` above it. -/
theorem llist_rel : ∀ n : Nat, ∀ (m : Mem) (a : AState) (pm : PMemo) (f o l q : Word)
    (us : List LIdx) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → hslice? (m.arr64 EREC) o.toNat l.toNat = some us →
    o.toNat + l.toNat ≤ q.toNat → q.toNat + l.toNat ≤ (m.arr64 EREC).size →
    (m.arr64 EREC).size < 2 ^ 64 → callW p n "promote_l_list" [f, o, l, q] m = some (r, m') →
    ∃ a' pm' us', (promoteLList pm f.toNat us).run a = .ok ((pm', us'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ hslice? (m'.arr64 EREC) q.toNat l.toNat = some us' ∧
      (∀ i < q.toNat, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
      (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) eCtl m m' := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc; rw [callW_zero'] at hc; cases hc
  | succ n ih =>
  intro m a pm f o l q us r m' hD hP hsl hoq hqs hsz hc
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (promoteLList_spec p hp n ⟨m, Locals.init []⟩ f o l q) hc
  simp only at hW
  by_cases hl : l = 0
  · rw [listW_nil _ _ _ _ _ _ _ _ _ hl] at hW
    cases hW
    subst hl
    have hus : us = [] := by simpa [hslice?] using hsl.symm
    subst hus
    refine ⟨a, pm, [], ?_, hD, hP, rfl, fun _ _ => rfl, rfl, rfl, MemFrame.refl _ _ _⟩
    rw [promoteLList_nil]; rfl
  have hl1 : l.toNat = (l - 1).toNat + 1 := by
    rw [toNat_sub1 l hl]; have := toNat_pred l hl; omega
  rw [hl1, L.Ind.hslice?_succ] at hsl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hsl
  obtain ⟨u, hu, us₀, hus, rfl⟩ := hsl
  obtain ⟨hrd, ho⟩ := rdW_of_hd? hu o rfl
  rw [listW_cons _ _ _ _ _ _ _ _ _ hl (by omega), hrd] at hW
  cases hca : callW p n "promote_l" [f, u.word.toUInt64] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₁⟩ := x
  rw [hca] at hW
  obtain ⟨a₁, pm₁, hrun₁, hD₁, hP₁, hpw₁, hcp₁, hfr₁, -, -⟩ :=
    (pl_rel p hp n).1 m a pm f _ r₁ m₁ hD hP (word_lt u) hca
  rw [decI_word] at hrun₁
  have hE₁ : m₁.arr64 EREC = m.arr64 EREC := hfr₁.1 EREC (by decide) (by decide)
  by_cases hq₁ : (m₁.arr64 EREC).size ≤ q.toNat
  · simp [listK, hq₁] at hW
  rw [listK_some (hq := hq₁)] at hW
  cases hcb : callW p n "promote_l_list" [f, o + 1, l - 1, q + 1]
      (m₁.set64 EREC q (r₁.headD 0)) with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₂⟩ := x
  rw [hcb, memK_some] at hW
  cases hW
  obtain ⟨hD₁', hP₁'⟩ := erec_set hD₁ hP₁ q (r₁.headD 0)
  have hE₁' : (m₁.set64 EREC q (r₁.headD 0)).arr64 EREC =
      (m₁.arr64 EREC).set! q.toNat (r₁.headD 0) := Mem.arr64_set64_same _ _ _ _
  have ho1 : (o + 1).toNat = o.toNat + 1 := toNat_add1 o (by omega)
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add1 q (by omega)
  have hag : ∀ i < q.toNat, ((m₁.set64 EREC q (r₁.headD 0)).arr64 EREC)[i]? = (m.arr64 EREC)[i]? := by
    intro i hi
    rw [hE₁', Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hE₁]
    simp [show q.toNat ≠ i by omega]
  have hsl₁ : hslice? ((m₁.set64 EREC q (r₁.headD 0)).arr64 EREC) (o + 1).toNat (l - 1).toNat =
      some us₀ := by
    rw [ho1, ← hus]
    exact hslice?_agree hag (by omega)
  obtain ⟨a₂, pm₂, us₂, hrun₂, hD₂, hP₂, hsl₂, hag₂, hsz₂, hcp₂, hfr₂⟩ :=
    ih _ a₁ pm₁ f (o + 1) (l - 1) (q + 1) us₀ r₂ _ hD₁' hP₁' hsl₁ (by rw [ho1, hq1]; omega)
      (by rw [hq1, size_set64, hE₁]; omega) (by rw [size_set64, hE₁]; exact hsz) hcb
  refine ⟨a₂, pm₂, decI (r₁.headD 0) :: us₂, ?_, hD₂, hP₂, ?_, ?_, ?_, hcp₂.trans hcp₁, ?_⟩
  · rw [promoteLList_cons, run_bind_ok hrun₁]
    simp only
    rw [run_bind_ok hrun₂]; rfl
  · rw [hl1, L.Ind.hslice?_succ, ← hq1, hsl₂]
    have hx : ((s'.mem).arr64 EREC)[q.toNat]? = some (r₁.headD 0) := by
      rw [hag₂ q.toNat (by omega), hE₁', Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds]
      simp [show q.toNat < (m₁.arr64 EREC).size by omega]
    rw [hd?_of hx hpw₁.1]; rfl
  · intro i hi
    rw [hag₂ i (by omega), hag i hi]
  · rw [hsz₂, size_set64, hE₁]
  · exact ((hfr₁.mono (by simp) (by simp)).trans
      ((MemFrame.set64 _ EREC (by decide) _ _).mono (by simp) (by simp))).trans hfr₂

/-- **`promote_e_list` refines `promoteEList`** over the slice `(o, l)` that `hslice?` decodes, the results
written at `[q, q + l)` above it. -/
theorem elist_rel : ∀ n : Nat, ∀ (m : Mem) (a : AState) (pm : PMemo) (f o l q : Word)
    (us : List EIdx) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → hslice? (m.arr64 EREC) o.toNat l.toNat = some us →
    o.toNat + l.toNat ≤ q.toNat → q.toNat + l.toNat ≤ (m.arr64 EREC).size →
    (m.arr64 EREC).size < 2 ^ 64 → callW p n "promote_e_list" [f, o, l, q] m = some (r, m') →
    ∃ a' pm' us', (promoteEList pm f.toNat us).run a = .ok ((pm', us'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ hslice? (m'.arr64 EREC) q.toNat l.toNat = some us' ∧
      (∀ i < q.toNat, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
      (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) eCtl m m' := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc; rw [callW_zero'] at hc; cases hc
  | succ n ih =>
  intro m a pm f o l q us r m' hD hP hsl hoq hqs hsz hc
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (promoteEList_spec p hp n ⟨m, Locals.init []⟩ f o l q) hc
  simp only at hW
  by_cases hl : l = 0
  · rw [listW_nil _ _ _ _ _ _ _ _ _ hl] at hW
    cases hW
    subst hl
    have hus : us = [] := by simpa [hslice?] using hsl.symm
    subst hus
    refine ⟨a, pm, [], ?_, hD, hP, rfl, fun _ _ => rfl, rfl, rfl, MemFrame.refl _ _ _⟩
    rw [promoteEList_nil]; rfl
  have hl1 : l.toNat = (l - 1).toNat + 1 := by
    rw [toNat_sub1 l hl]; have := toNat_pred l hl; omega
  rw [hl1, L.Ind.hslice?_succ] at hsl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hsl
  obtain ⟨u, hu, us₀, hus, rfl⟩ := hsl
  obtain ⟨hrd, ho⟩ := rdW_of_hd? hu o rfl
  rw [listW_cons _ _ _ _ _ _ _ _ _ hl (by omega), hrd] at hW
  cases hca : callW p n "promote_e" [f, u.word.toUInt64] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₁⟩ := x
  rw [hca] at hW
  obtain ⟨a₁, pm₁, hrun₁, hD₁, hP₁, hpw₁, hcp₁, hfr₁⟩ :=
    (pe_rel p hp n).1 m a pm f _ r₁ m₁ hD hP (word_lt u) hca
  rw [decE_word] at hrun₁
  have hE₁ : m₁.arr64 EREC = m.arr64 EREC := hfr₁.1 EREC (by decide) (by decide)
  by_cases hq₁ : (m₁.arr64 EREC).size ≤ q.toNat
  · simp [listK, hq₁] at hW
  rw [listK_some (hq := hq₁)] at hW
  cases hcb : callW p n "promote_e_list" [f, o + 1, l - 1, q + 1]
      (m₁.set64 EREC q (r₁.headD 0)) with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₂⟩ := x
  rw [hcb, memK_some] at hW
  cases hW
  obtain ⟨hD₁', hP₁'⟩ := erec_set hD₁ hP₁ q (r₁.headD 0)
  have hE₁' : (m₁.set64 EREC q (r₁.headD 0)).arr64 EREC =
      (m₁.arr64 EREC).set! q.toNat (r₁.headD 0) := Mem.arr64_set64_same _ _ _ _
  have ho1 : (o + 1).toNat = o.toNat + 1 := toNat_add1 o (by omega)
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add1 q (by omega)
  have hag : ∀ i < q.toNat, ((m₁.set64 EREC q (r₁.headD 0)).arr64 EREC)[i]? = (m.arr64 EREC)[i]? := by
    intro i hi
    rw [hE₁', Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hE₁]
    simp [show q.toNat ≠ i by omega]
  have hsl₁ : hslice? ((m₁.set64 EREC q (r₁.headD 0)).arr64 EREC) (o + 1).toNat (l - 1).toNat =
      some us₀ := by
    rw [ho1, ← hus]
    exact hslice?_agree hag (by omega)
  obtain ⟨a₂, pm₂, us₂, hrun₂, hD₂, hP₂, hsl₂, hag₂, hsz₂, hcp₂, hfr₂⟩ :=
    ih _ a₁ pm₁ f (o + 1) (l - 1) (q + 1) us₀ r₂ _ hD₁' hP₁' hsl₁ (by rw [ho1, hq1]; omega)
      (by rw [hq1, size_set64, hE₁]; omega) (by rw [size_set64, hE₁]; exact hsz) hcb
  refine ⟨a₂, pm₂, decI (r₁.headD 0) :: us₂, ?_, hD₂, hP₂, ?_, ?_, ?_, hcp₂.trans hcp₁, ?_⟩
  · rw [promoteEList_cons, run_bind_ok hrun₁]
    simp only
    rw [run_bind_ok hrun₂]; rfl
  · rw [hl1, L.Ind.hslice?_succ, ← hq1, hsl₂]
    have hx : ((s'.mem).arr64 EREC)[q.toNat]? = some (r₁.headD 0) := by
      rw [hag₂ q.toNat (by omega), hE₁', Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds]
      simp [show q.toNat < (m₁.arr64 EREC).size by omega]
    rw [hd?_of hx hpw₁.1]; rfl
  · intro i hi
    rw [hag₂ i (by omega), hag i hi]
  · rw [hsz₂, size_set64, hE₁]
  · exact ((hfr₁.mono (by simp) (by simp)).trans
      ((MemFrame.set64 _ EREC (by decide) _ _).mono (by simp) (by simp))).trans hfr₂

end lists

end L.Arena
