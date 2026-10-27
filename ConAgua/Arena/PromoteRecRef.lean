import ConAgua.Arena.PromoteRec
import ConAgua.Arena.PromoteERef
import ConAgua.Arena.IndLibSpec
import Std.Tactic.BVDecide.Normalize.Prop

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

/-- **The statement of a list promotion** `gl` refining the twin's `TL` over the slice `(o, l)`
that `hslice?` decodes, the results written at `[q, q + l)` above it. -/
def PListRel (p : Prog) (gl : FnName) {k : IdxKind}
    (TL : PMemo → Nat → List (Idx k) → AM (PMemo × List (Idx k))) : Prop :=
    ∀ n : Nat, ∀ (m : Mem) (a : AState) (pm : PMemo) (f o l q : Word)
    (us : List (Idx k)) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → hslice? (m.arr64 EREC) o.toNat l.toNat = some us →
    (o.toNat + l.toNat ≤ q.toNat ∨ l = 0) → q.toNat + l.toNat ≤ (m.arr64 EREC).size →
    (m.arr64 EREC).size < 2 ^ 64 → callW p n gl [f, o, l, q] m = some (r, m') →
    ∃ a' pm' us', (TL pm f.toNat us).run a = .ok ((pm', us'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ hslice? (m'.arr64 EREC) q.toNat l.toNat = some us' ∧
      (∀ i < q.toNat, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
      (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) eCtl m m' ∧ TierKeep m m'

section lists
variable (p : Prog) (hp : PromoteProg p)
include hp

omit hp in
/-- **A `promote_X_list` refines its twin's list promotion** over the slice `(o, l)` that `hslice?`
decodes, the results written at `[q, q + l)` above it: from the element's relation `hrel`. -/
theorem list_gen {k : IdxKind} (g gl : FnName) (T : PMemo → Nat → Idx k → AM (PMemo × Idx k))
    (TL : PMemo → Nat → List (Idx k) → AM (PMemo × List (Idx k)))
    (hnil : ∀ pm fuel, TL pm fuel [] = pure (pm, []))
    (hcons : ∀ pm fuel u us, TL pm fuel (u :: us) = (do
      let (m, u) ← T pm fuel u
      let (m, us) ← TL m fuel us
      pure (m, u :: us)))
    (hspec : ∀ n s₀ f o l q, ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) gl [f, o, l, q]
      ⦃fun _ s' => LocEq s' s₀ ∧ listW p n gl g s₀.mem f o l q = some s'.mem; ⊤⦄)
    (hrel : ∀ n m a pm f (u : Idx k) r m', ArenaD m a → PMemoR m pm →
      callW p n g [f, u.word.toUInt64] m = some (r, m') →
      ∃ a' pm', (T pm f.toNat u).run a = .ok ((pm', decI (r.headD 0)), a') ∧ ArenaD m' a' ∧
        PMemoR m' pm' ∧ PW (r.headD 0) ∧ cp a' = cp a ∧ MemFrame eArrs eCtl m m' ∧ TierKeep m m') :
    PListRel p gl TL := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc; rw [callW_zero'] at hc; cases hc
  | succ n ih =>
  intro m a pm f o l q us r m' hD hP hsl hoq hqs hsz hc
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (hspec n ⟨m, Locals.init []⟩ f o l q) hc
  simp only at hW
  by_cases hl : l = 0
  · rw [listW_nil _ _ _ _ _ _ _ _ _ hl] at hW
    cases hW
    subst hl
    have hus : us = [] := by simpa [hslice?] using hsl.symm
    subst hus
    refine ⟨a, pm, [], ?_, hD, hP, rfl, fun _ _ => rfl, rfl, rfl, MemFrame.refl _ _ _, TierKeep.refl _⟩
    rw [hnil]; rfl
  have hoq : o.toNat + l.toNat ≤ q.toNat := hoq.resolve_right hl
  have hl1 : l.toNat = (l - 1).toNat + 1 := by
    rw [toNat_sub1 l hl]; have := toNat_pred l hl; omega
  rw [hl1, L.Ind.hslice?_succ] at hsl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hsl
  obtain ⟨u, hu, us₀, hus, rfl⟩ := hsl
  obtain ⟨hrd, ho⟩ := rdW_of_hd? hu o rfl
  rw [listW_cons _ _ _ _ _ _ _ _ _ hl (by omega), hrd] at hW
  cases hca : callW p n g [f, u.word.toUInt64] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₁⟩ := x
  rw [hca] at hW
  obtain ⟨a₁, pm₁, hrun₁, hD₁, hP₁, hpw₁, hcp₁, hfr₁, htk₁⟩ := hrel n m a pm f u r₁ m₁ hD hP hca
  have hE₁ : m₁.arr64 EREC = m.arr64 EREC := hfr₁.1 EREC (by decide) (by decide)
  by_cases hq₁ : (m₁.arr64 EREC).size ≤ q.toNat
  · simp [listK, hq₁] at hW
  rw [listK_some (hq := hq₁)] at hW
  cases hcb : callW p n gl [f, o + 1, l - 1, q + 1]
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
  obtain ⟨a₂, pm₂, us₂, hrun₂, hD₂, hP₂, hsl₂, hag₂, hsz₂, hcp₂, hfr₂, htk₂⟩ :=
    ih _ a₁ pm₁ f (o + 1) (l - 1) (q + 1) us₀ r₂ _ hD₁' hP₁' hsl₁ (.inl (by rw [ho1, hq1]; omega))
      (by rw [hq1, size_set64, hE₁]; omega) (by rw [size_set64, hE₁]; exact hsz) hcb
  refine ⟨a₂, pm₂, decI (r₁.headD 0) :: us₂, ?_, hD₂, hP₂, ?_, ?_, ?_, hcp₂.trans hcp₁, ?_,
    htk₁.trans ((TierKeep.of_frame (MemFrame.set64 _ EREC (by decide) _ _) (by simp)).trans htk₂)⟩
  · rw [hcons, run_bind_ok hrun₁]
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
  · exact ((hfr₁.mono (fun _ h => List.mem_cons_of_mem _ h) (by simp)).trans
      ((MemFrame.set64 _ EREC (by decide) _ _).mono (by simp) (by simp))).trans hfr₂


/-- **`promote_n_list` refines `promoteNList`** over the slice `(o, l)` that `hslice?` decodes, the results
written at `[q, q + l)` above it. -/
theorem nlist_rel : ∀ n : Nat, ∀ (m : Mem) (a : AState) (pm : PMemo) (f o l q : Word)
    (us : List NIdx) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → hslice? (m.arr64 EREC) o.toNat l.toNat = some us →
    (o.toNat + l.toNat ≤ q.toNat ∨ l = 0) → q.toNat + l.toNat ≤ (m.arr64 EREC).size →
    (m.arr64 EREC).size < 2 ^ 64 → callW p n "promote_n_list" [f, o, l, q] m = some (r, m') →
    ∃ a' pm' us', (promoteNList pm f.toNat us).run a = .ok ((pm', us'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ hslice? (m'.arr64 EREC) q.toNat l.toNat = some us' ∧
      (∀ i < q.toNat, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
      (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) eCtl m m' ∧ TierKeep m m' :=
  list_gen p "promote_n" "promote_n_list" promoteN promoteNList promoteNList_nil promoteNList_cons (promoteNList_spec p hp) fun n m a pm f u r m' hD hP hc => by
    obtain ⟨a', pm', h1, h2, h3, h4, h5, h6, -, -, -⟩ := (pn_rel p hp n).1 m a pm f _ r m' hD hP (word_lt u) hc
    rw [decI_word] at h1
    exact ⟨a', pm', h1, h2, h3, h4, h5, h6.mono (by simp) (by simp), TierKeep.of_frame h6 (by decide)⟩

/-- **`promote_l_list` refines `promoteLList`** over the slice `(o, l)` that `hslice?` decodes, the results
written at `[q, q + l)` above it. -/
theorem llist_rel : ∀ n : Nat, ∀ (m : Mem) (a : AState) (pm : PMemo) (f o l q : Word)
    (us : List LIdx) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → hslice? (m.arr64 EREC) o.toNat l.toNat = some us →
    (o.toNat + l.toNat ≤ q.toNat ∨ l = 0) → q.toNat + l.toNat ≤ (m.arr64 EREC).size →
    (m.arr64 EREC).size < 2 ^ 64 → callW p n "promote_l_list" [f, o, l, q] m = some (r, m') →
    ∃ a' pm' us', (promoteLList pm f.toNat us).run a = .ok ((pm', us'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ hslice? (m'.arr64 EREC) q.toNat l.toNat = some us' ∧
      (∀ i < q.toNat, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
      (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) eCtl m m' ∧ TierKeep m m' :=
  list_gen p "promote_l" "promote_l_list" promoteL promoteLList promoteLList_nil promoteLList_cons (promoteLList_spec p hp) fun n m a pm f u r m' hD hP hc => by
    obtain ⟨a', pm', h1, h2, h3, h4, h5, h6, -, -⟩ := (pl_rel p hp n).1 m a pm f _ r m' hD hP (word_lt u) hc
    rw [decI_word] at h1
    exact ⟨a', pm', h1, h2, h3, h4, h5, h6.mono (by simp) (by simp), TierKeep.of_frame h6 (by decide)⟩

/-- **`promote_e_list` refines `promoteEList`** over the slice `(o, l)` that `hslice?` decodes, the results
written at `[q, q + l)` above it. -/
theorem elist_rel : ∀ n : Nat, ∀ (m : Mem) (a : AState) (pm : PMemo) (f o l q : Word)
    (us : List EIdx) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → hslice? (m.arr64 EREC) o.toNat l.toNat = some us →
    (o.toNat + l.toNat ≤ q.toNat ∨ l = 0) → q.toNat + l.toNat ≤ (m.arr64 EREC).size →
    (m.arr64 EREC).size < 2 ^ 64 → callW p n "promote_e_list" [f, o, l, q] m = some (r, m') →
    ∃ a' pm' us', (promoteEList pm f.toNat us).run a = .ok ((pm', us'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ hslice? (m'.arr64 EREC) q.toNat l.toNat = some us' ∧
      (∀ i < q.toNat, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
      (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) eCtl m m' ∧ TierKeep m m' :=
  list_gen p "promote_e" "promote_e_list" promoteE promoteEList promoteEList_nil promoteEList_cons (promoteEList_spec p hp) fun n m a pm f u r m' hD hP hc => by
    obtain ⟨a', pm', h1, h2, h3, h4, h5, h6, h7⟩ := (pe_rel p hp n).1 m a pm f _ r m' hD hP (word_lt u) hc
    rw [decE_word] at h1
    exact ⟨a', pm', h1, h2, h3, h4, h5, h6.mono (by simp) (by simp), h7⟩

end lists

section slices
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`promote_slice(k, f, o, l)`**: a fresh slice at the old top, the kind's list promotion
(`gl`, its relation `hlist`) of the decoded slice `(o, l)`. -/
theorem slice_gen {k : IdxKind} (kw : Word) (gl : FnName)
    (TL : PMemo → Nat → List (Idx k) → AM (PMemo × List (Idx k)))
    (hk : ∀ n f o l r m₁, sliceK p n kw f o l (some (r, m₁)) =
      offK (r.headD 0) (callW p n gl [f, o, l, r.headD 0] m₁))
    (hlist : PListRel p gl TL)
    (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f o l : Word)
    (us : List (Idx k)) (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsl : hslice? (m.arr64 EREC) o.toNat l.toNat = some us)
    (hot : o.toNat + l.toNat ≤ erecTop m ∨ l = 0)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "promote_slice" [kw, f, o, l] m = some (r, m')) :
    r.headD 0 = etop m ∧ erecTop m' = erecTop m + l.toNat ∧ erecTop m' ≤ (m'.arr64 EREC).size ∧
    ∃ a' pm' us', (TL pm f.toNat us).run a = .ok ((pm', us'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ hslice? (m'.arr64 EREC) (erecTop m) l.toNat = some us' ∧
      (∀ i < erecTop m, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
      (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (promoteSlice_spec p hp n ⟨m, Locals.init []⟩ kw f o l) hc
  simp only [sliceW] at hW
  cases n with
  | zero => rw [callW_zero'] at hW; cases hW
  | succ n =>
  cases hca : callW p (n + 1) "erec_alloc" [l] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨q, m₁⟩ := x
  rw [hca, hk] at hW
  obtain ⟨s₁, hs₁, -, hW₁⟩ := callW_triple (erecAlloc_spec p (hp.get "erec_alloc") n ⟨m, Locals.init []⟩ l) hca
  rw [hs₁] at hW₁
  dsimp only at hW₁
  obtain ⟨hq, rfl, hql, hroom, hctl⟩ := erAlloc_facts hW₁
  cases hcb : callW p (n + 1) gl [f, o, l, q.headD 0] (m.set64 CTL 129 (q.headD 0 + l)) with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₂⟩ := x
  rw [hcb, offK_some] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  have hf₁ : MemFrame [] [129] m (m.set64 CTL 129 (q.headD 0 + l)) := MemFrame.setCtl m 129 _
  have hE₁ : (m.set64 CTL 129 (q.headD 0 + l)).arr64 EREC = m.arr64 EREC :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hD₁ : ArenaD (m.set64 CTL 129 (q.headD 0 + l)) a :=
    ⟨ArenaR.frame_ext _ _ (by simp) (by simp) m _ hf₁ a hD.1, DerR.frameM _ _ m _ hf₁ (by simp) a hD.2⟩
  have hP₁ := hP.frame (by simp) (by simp) hf₁
  have hqv : (q.headD 0).toNat = erecTop m := by rw [hq]; rfl
  obtain ⟨a₂, pm₂, us₂, hrun, hD₂, hP₂, hsl₂, hag, hsz₂, hcp, hfr, htk⟩ :=
    hlist (n + 1) _ a pm f o l (q.headD 0) us r₂ m₂ hD₁ hP₁ (by rw [hE₁]; exact hsl)
      (by rw [hqv]; exact hot) (by rw [hqv, hE₁]; omega) (by rw [hE₁]; exact hsz) hcb
  have h129 : rdW (m₂.arr64 CTL) 129 = q.headD 0 + l := by
    rw [hfr.2.1 129 (by simp)]; rw [rdW_set64]; simp [hctl]
  rw [← hm]
  refine ⟨by rw [← hr, hq], ?_, ?_, a₂, pm₂, us₂, hrun, hD₂, hP₂, by rw [← hqv]; exact hsl₂,
    fun i hi => by rw [hag i (by omega), hE₁], by rw [hsz₂, hE₁], hcp, ?_,
    (TierKeep.of_frame hf₁ (by simp)).trans htk⟩
  · simp only [erecTop, h129, hql, hqv]
  · simp only [erecTop, h129, hql, hsz₂, hE₁]; rw [hqv]; omega
  · exact (hf₁.mono (by simp) (by simp)).trans (hfr.mono (by simp) (by simp))


/-- **`promote_slice(0, f, o, l)`**: a fresh slice at the old top, `promoteNList` of the decoded
slice `(o, l)`. -/
theorem sliceN_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f o l : Word)
    (us : List NIdx) (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsl : hslice? (m.arr64 EREC) o.toNat l.toNat = some us)
    (hot : o.toNat + l.toNat ≤ erecTop m ∨ l = 0)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "promote_slice" [0, f, o, l] m = some (r, m')) :
    r.headD 0 = etop m ∧ erecTop m' = erecTop m + l.toNat ∧ erecTop m' ≤ (m'.arr64 EREC).size ∧
    ∃ a' pm' us', (promoteNList pm f.toNat us).run a = .ok ((pm', us'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ hslice? (m'.arr64 EREC) (erecTop m) l.toNat = some us' ∧
      (∀ i < erecTop m, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
      (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' :=
  slice_gen p hp 0 "promote_n_list" promoteNList (fun _ _ _ _ _ _ => by simp [sliceK]) (nlist_rel p hp) n m a pm f o l us r m'
    hD hP hsl hot hsz hc

/-- **`promote_slice(1, f, o, l)`**: a fresh slice at the old top, `promoteLList` of the decoded
slice `(o, l)`. -/
theorem sliceL_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f o l : Word)
    (us : List LIdx) (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsl : hslice? (m.arr64 EREC) o.toNat l.toNat = some us)
    (hot : o.toNat + l.toNat ≤ erecTop m ∨ l = 0)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "promote_slice" [1, f, o, l] m = some (r, m')) :
    r.headD 0 = etop m ∧ erecTop m' = erecTop m + l.toNat ∧ erecTop m' ≤ (m'.arr64 EREC).size ∧
    ∃ a' pm' us', (promoteLList pm f.toNat us).run a = .ok ((pm', us'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ hslice? (m'.arr64 EREC) (erecTop m) l.toNat = some us' ∧
      (∀ i < erecTop m, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
      (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' :=
  slice_gen p hp 1 "promote_l_list" promoteLList (fun _ _ _ _ _ _ => by simp [sliceK]) (llist_rel p hp) n m a pm f o l us r m'
    hD hP hsl hot hsz hc

/-- **`promote_slice(2, f, o, l)`**: a fresh slice at the old top, `promoteEList` of the decoded
slice `(o, l)`. -/
theorem sliceE_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f o l : Word)
    (us : List EIdx) (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsl : hslice? (m.arr64 EREC) o.toNat l.toNat = some us)
    (hot : o.toNat + l.toNat ≤ erecTop m ∨ l = 0)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "promote_slice" [2, f, o, l] m = some (r, m')) :
    r.headD 0 = etop m ∧ erecTop m' = erecTop m + l.toNat ∧ erecTop m' ≤ (m'.arr64 EREC).size ∧
    ∃ a' pm' us', (promoteEList pm f.toNat us).run a = .ok ((pm', us'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ hslice? (m'.arr64 EREC) (erecTop m) l.toNat = some us' ∧
      (∀ i < erecTop m, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
      (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' :=
  slice_gen p hp 2 "promote_e_list" promoteEList (fun _ _ _ _ _ _ => by simp [sliceK]) (elist_rel p hp) n m a pm f o l us r m'
    hD hP hsl hot hsz hc

end slices

/-! ## The record pool below its top -/

theorem erecP_getElem (m : Mem) (i : Nat) (hi : i < erecTop m) (hs : erecTop m ≤ (m.arr64 EREC).size) :
    (erecP m)[i]? = (m.arr64 EREC)[i]? := by
  simp only [erecP, Array.getElem?_extract]
  rw [ite_eq_left (by simp; omega)]; simp

theorem erecP_size_le (m : Mem) : (erecP m).size ≤ erecTop m := by
  simp only [erecP, Array.size_extract]; omega

/-- A slice that decodes below the top reads the raw pool. -/
theorem hslice?_erecP {m : Mem} {o l : Nat} {k : IdxKind} (hs : erecTop m ≤ (m.arr64 EREC).size)
    (hb : o + l ≤ erecTop m) :
    (hslice? (erecP m) o l : Option (List (Idx k))) = hslice? (m.arr64 EREC) o l :=
  (hslice?_agree (fun i hi => (erecP_getElem m i hi hs).symm) hb).symm

/-- A decoded slice of the pool below its top lies below the top. -/
theorem hslice?_bound {a : Array Word} {o l : Nat} {k : IdxKind} {xs : List (Idx k)}
    (h : hslice? a o l = some xs) : l = 0 ∨ o + l ≤ a.size := by
  induction l generalizing o xs with
  | zero => exact .inl rfl
  | succ l ih =>
    right
    rw [L.Ind.hslice?_succ] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs', hxs, rfl⟩ := h
    obtain ⟨w, hw, -⟩ := hd?_some hx
    rcases Array.getElem?_eq_some_iff.mp hw with ⟨hh, -⟩
    rcases ih hxs with h0 | h0
    · subst h0; omega
    · omega

/-- **A promoted constant value's four words** (`promote_cv`'s results) denote `cv` in the pool. -/
def CVWords (m : Mem) (r : List Word) (cv : IConstantVal) : Prop :=
  r = [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0] ∧
  PW (r.headD 0) ∧ decI (r.headD 0) = cv.name ∧
  hslice? (erecP m) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some cv.levelParams ∧
  PW (r.tail.tail.tail.headD 0) ∧ decE (r.tail.tail.tail.headD 0) = cv.type

section cv
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`promote_cv` refines `promoteCV`.** -/
theorem cv_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f s : Word) (cv : IConstantVal)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hcv : decCV (erecP m) s.toNat = some cv) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "promote_cv" [f, s] m = some (r, m')) :
    ∃ a' pm' cv', (promoteCV pm f.toNat cv).run a = .ok ((pm', cv'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ CVWords m' r cv' ∧ ErecGrow m m' ∧ erecTop m' ≤ (m'.arr64 EREC).size ∧
      cp a' = cp a ∧ MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (promoteCV_spec p hp n ⟨m, Locals.init []⟩ f s) hc
  simp only at hW
  simp only [decCV, hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hcv
  obtain ⟨nm, hnm, lps, ⟨o, ho, l, hl, hsl⟩, ty, hty, rfl⟩ := hcv
  have raw : ∀ {i : Nat} {v : Word}, (erecP m)[i]? = some v → (m.arr64 EREC)[i]? = some v :=
    fun h => erecP_get h
  obtain ⟨w0, hw0, hw0l, rfl⟩ := hd?_some hnm
  obtain ⟨w3, hw3, hw3l, rfl⟩ := hd?_some hty
  simp only [nat?, Option.map_eq_some_iff] at ho hl
  obtain ⟨wo, hwo, rfl⟩ := ho
  obtain ⟨wl, hwl, rfl⟩ := hl
  have hlt : s.toNat + 3 < (m.arr64 EREC).size := by
    rcases Array.getElem?_eq_some_iff.mp (raw hw3) with ⟨hh, -⟩; exact hh
  have hs1 : (s + 1).toNat = s.toNat + 1 := toNat_add1 s (by omega)
  have hs2 : (s + 2).toNat = s.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have hs3 : (s + 3).toNat = s.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have hrd : cvRdW m s = [w0, wo, wl, w3] := by
    have e0 : rdW (m.arr64 EREC) s = w0 := by rw [rdW, raw hw0]; rfl
    have e1 : rdW (m.arr64 EREC) (s + 1) = wo := by rw [rdW, hs1, raw hwo]; rfl
    have e2 : rdW (m.arr64 EREC) (s + 2) = wl := by rw [rdW, hs2, raw hwl]; rfl
    have e3 : rdW (m.arr64 EREC) (s + 3) = w3 := by rw [rdW, hs3, raw hw3]; rfl
    simp only [cvRdW, hs1, hs2, hs3, e0, e1, e2, e3]
    rw [ite_eq_right (by omega)]
  rw [cvW_eq (h := by rw [hrd]; simp), hrd] at hW
  simp only [List.headD_cons, List.tail_cons] at hW
  cases hca : callW p n "promote_n" [f, w0] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₁⟩ := x
  rw [hca, cvK_some] at hW
  obtain ⟨a₁, pm₁, hrun₁, hD₁, hP₁, hpw₁, hcp₁, hfr₁, -, -, -⟩ :=
    (pn_rel p hp n).1 m a pm f w0 r₁ m₁ hD hP hw0l hca
  have hE₁ : m₁.arr64 EREC = m.arr64 EREC := hfr₁.1 EREC (by decide) (by decide)
  have ht₁ : erecTop m₁ = erecTop m := by simp only [erecTop]; rw [hfr₁.2.1 129 (by decide)]
  cases hcb : callW p n "promote_slice" [0, f, wo, wl] m₁ with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₂⟩ := x
  rw [hcb, cvK₂_some] at hW
  have hslr : hslice? (m₁.arr64 EREC) wo.toNat wl.toNat = some lps := by
    rw [hE₁]; exact (erecP_ext m).hslice? hsl
  have hot : wo.toNat + wl.toNat ≤ erecTop m₁ ∨ wl = 0 := by
    rcases hslice?_bound hsl with h0 | h0
    · right; exact UInt64.toNat_inj.mp (by simpa using h0)
    · left; have := erecP_size_le m; omega
  obtain ⟨hq, ht₂, hts₂, a₂, pm₂, lps', hrun₂, hD₂, hP₂, hsl₂, hag₂, hsz₂, hcp₂, hfr₂, htk₂⟩ :=
    sliceN_rel p hp n m₁ a₁ pm₁ f wo wl lps r₂ m₂ hD₁ hP₁ hslr hot (by rw [hE₁]; exact hsz) hcb
  cases hcc : callW p n "promote_e" [f, w3] m₂ with
  | none => rw [hcc] at hW; cases hW
  | some x =>
  obtain ⟨r₃, m₃⟩ := x
  rw [hcc, cvK₃_some] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨a₃, pm₃, hrun₃, hD₃, hP₃, hpw₃, hcp₃, hfr₃, htk₃⟩ :=
    (pe_rel p hp n).1 m₂ a₂ pm₂ f w3 r₃ m₃ hD₂ hP₂ hw3l hcc
  have hE₃ : m₃.arr64 EREC = m₂.arr64 EREC := hfr₃.1 EREC (by decide) (by decide)
  have ht₃ : erecTop m₃ = erecTop m₂ := by simp only [erecTop]; rw [hfr₃.2.1 129 (by decide)]
  have hqv : (r₂.headD 0).toNat = erecTop m := by rw [hq, ← ht₁]; rfl
  rw [← hm, ← hr]
  refine ⟨a₃, pm₃, ⟨decI (r₁.headD 0), lps', decE (r₃.headD 0)⟩, ?_, hD₃, hP₃, ?_, ?_, ?_,
    hcp₃.trans (hcp₂.trans hcp₁), ?_, (TierKeep.of_frame hfr₁ (by decide)).trans (htk₂.trans htk₃)⟩
  · simp only [promoteCV]
    rw [run_bind_ok hrun₁]
    simp only
    rw [run_bind_ok hrun₂]
    simp only
    have hrun₃' : (promoteE pm₂ f.toNat (decI w3)).run a₂ = .ok ((pm₃, decE (r₃.headD 0)), a₃) :=
      hrun₃
    rw [run_bind_ok hrun₃']; rfl
  · refine ⟨rfl, hpw₁, rfl, ?_, hpw₃, rfl⟩
    simp only [List.headD_cons, List.tail_cons]
    rw [hslice?_erecP (by rw [ht₃, hE₃]; exact hts₂) (by rw [ht₃, ht₂, hqv, ht₁]; exact Nat.le_refl _)]
    rw [hE₃, hqv, ← ht₁]; exact hsl₂
  · refine ⟨by rw [ht₃, ht₂, ht₁]; omega, fun i hi => ?_, by rw [hE₃, hsz₂, hE₁]⟩
    rw [hE₃, hag₂ i (by rw [ht₁]; exact hi), hE₁]
  · rw [ht₃, hE₃]; exact hts₂
  · exact ((hfr₁.mono (by simp) (by simp)).trans hfr₂).trans (hfr₃.mono (fun _ h => List.mem_cons_of_mem _ h) (by simp))

end cv

/-! ## `promote_clear`, `promote_vg` -/

/-- **The four clears give the empty memo.** -/
theorem clear_rel {m m' : Mem} {pm : PMemo} (hP : PMemoR m pm) (h : clearW m = some m') :
    PMemoR m' PMemo.empty ∧ MemFrame [] [140, 141, 142, 143, 144, 145, 146, 147] m m' := by
  unfold clearW at h
  by_cases h1 : rdW (m.arr64 CTL) pnSch.cs + 2 = 0
  · simp [pmClrK, h1] at h
  rw [pmClrK_some _ _ h1] at h
  by_cases h2 : rdW ((mclearG pnSch m).arr64 CTL) plSch.cs + 2 = 0
  · simp [pmClrK, h2] at h
  rw [pmClrK_some _ _ h2] at h
  by_cases h3 : rdW ((mclearG plSch (mclearG pnSch m)).arr64 CTL) plsSch.cs + 2 = 0
  · simp [pmClrK, h3] at h
  rw [pmClrK_some _ _ h3] at h
  by_cases h4 : rdW ((mclearG plsSch (mclearG plSch (mclearG pnSch m))).arr64 CTL) peSch.cs + 2 = 0
  · simp [pmClrK, h4] at h
  rw [pmClrK_some _ _ h4] at h
  cases h
  have f1 := mclearG_frame pnSch m
  have f2 := mclearG_frame plSch (mclearG pnSch m)
  have f3 := mclearG_frame plsSch (mclearG plSch (mclearG pnSch m))
  have f4 := mclearG_frame peSch (mclearG plsSch (mclearG plSch (mclearG pnSch m)))
  have fr : ∀ {k : IdxKind} (S T : MemoSch) (K : MemoKey (Idx k))
      (VR : Mem → Word → Idx k → Prop) (hT : T.WF) (hS1 : S.arr ≠ T.arr)
      (hS2 : T.cs ∉ [S.cs, S.cs + 1]) (m₁ : Mem) (mp : Std.HashMap (Idx k) (Idx k)),
      VR = VP k → MemoRV T K VR m₁ mp → MemoRV T K VR (mclearG S m₁) mp :=
    fun S T K VR hT _ hS2 m₁ mp hV h => by
      subst hV
      exact memoRV_frame T hT K _ [] _ (by simp) hS2 m₁ _ (mclearG_frame S m₁) (fun _ _ h => h) mp h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact fr _ _ _ _ pnSch_wf (by decide) (by decide) _ _ rfl
      (fr _ _ _ _ pnSch_wf (by decide) (by decide) _ _ rfl
        (fr _ _ _ _ pnSch_wf (by decide) (by decide) _ _ rfl
          (memoRV_clear pnSch pnSch_wf _ _ m _ hP.n h1)))
  · exact fr _ _ _ _ plSch_wf (by decide) (by decide) _ _ rfl
      (fr _ _ _ _ plSch_wf (by decide) (by decide) _ _ rfl
        (memoRV_clear plSch plSch_wf _ _ _ _
          (fr _ _ _ _ plSch_wf (by decide) (by decide) _ _ rfl hP.l) h2))
  · exact fr _ _ _ _ plsSch_wf (by decide) (by decide) _ _ rfl
      (memoRV_clear plsSch plsSch_wf _ _ _ _
        (fr _ _ _ _ plsSch_wf (by decide) (by decide) _ _ rfl
          (fr _ _ _ _ plsSch_wf (by decide) (by decide) _ _ rfl hP.ls)) h3)
  · exact memoRV_clear peSch peSch_wf _ _ _ _
      (fr _ _ _ _ peSch_wf (by decide) (by decide) _ _ rfl
        (fr _ _ _ _ peSch_wf (by decide) (by decide) _ _ rfl
          (fr _ _ _ _ peSch_wf (by decide) (by decide) _ _ rfl hP.e))) h4
  · exact (((f1.mono (by simp) (by simp)).trans (f2.mono (by simp) (by simp))).trans
      (f3.mono (by simp) (by simp))).trans (f4.mono (by simp) (by simp))

theorem vgStore_facts {m m' : Mem} {d k nm q l t x : Word}
    (h : vgStore m d k nm q l t x = some m') (hd : d.toNat + 5 < 2 ^ 64) :
    d.toNat + 5 < (m.arr64 EREC).size ∧
    (m'.arr64 EREC)[d.toNat]? = some k ∧ (m'.arr64 EREC)[d.toNat + 1]? = some nm ∧
    (m'.arr64 EREC)[d.toNat + 2]? = some q ∧ (m'.arr64 EREC)[d.toNat + 3]? = some l ∧
    (m'.arr64 EREC)[d.toNat + 4]? = some t ∧ (m'.arr64 EREC)[d.toNat + 5]? = some x ∧
    (∀ i < d.toNat, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' := by
  unfold vgStore at h
  split at h
  · cases h
  rename_i hc
  cases h
  have e1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (d + 2).toNat = d.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : (d + 3).toNat = d.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have e4 : (d + 4).toNat = d.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have e5 : (d + 5).toNat = d.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
  have hlt : d.toNat + 5 < (m.arr64 EREC).size := by
    simp only [not_or, Nat.not_le] at hc; have := hc.2.2.2.2.2; rw [e5] at this; exact this
  have fr : ∀ (m₁ : Mem) (i v : Word), MemFrame [EREC] [] m₁ (m₁.set64 EREC i v) :=
    fun m₁ i v => MemFrame.set64 m₁ EREC (by decide) i v
  have b0 : d.toNat < (m.arr64 EREC).size := by omega
  have b1 : d.toNat + 1 < (m.arr64 EREC).size := by omega
  have b2 : d.toNat + 2 < (m.arr64 EREC).size := by omega
  have b3 : d.toNat + 3 < (m.arr64 EREC).size := by omega
  have b4 : d.toNat + 4 < (m.arr64 EREC).size := by omega
  refine ⟨hlt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try intros)
  all_goals (try simp only [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, e1, e2, e3, e4, e5])
  all_goals (try simp [b0, b1, b2, b3, b4, hlt])
  all_goals (try omega)
  · rename_i i hi
    simp [show d.toNat + 5 ≠ i by omega, show d.toNat + 4 ≠ i by omega,
      show d.toNat + 3 ≠ i by omega, show d.toNat + 2 ≠ i by omega,
      show d.toNat + 1 ≠ i by omega, show d.toNat ≠ i by omega]
  · exact (((((fr _ _ _).trans (fr _ _ _)).trans (fr _ _ _)).trans (fr _ _ _)).trans
      (fr _ _ _)).trans (fr _ _ _)

/-- The arrays a value-group promotion writes. -/
theorem vg_arrs : ∀ b ∈ EREC :: eArrs, (b < 50 ∨ (54 < b ∧ b < 64)) ∨ b = 136 ∨ (146 ≤ b ∧ b ≤ 149) ∨
    (256 ≤ b ∧ b < 306) ∨ (310 < b ∧ b < 320) := by
  simp only [eArrs, lsArrs, lArrs, List.cons_append, List.nil_append, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, EREC, POOL, POOL1, PT0, NAREC, NASLOT, NSREC,
    NSSLOT, NNREC, NNSLOT, PNM, ZREC, ZSLOT, SREC, SSLOT, MREC, MSLOT, IREC, ISLOT, PREC, PSLOT,
    PLM, LSREC, LSSLOT, PLSM, REC, SLOT, AREC, ASLOT, SOREC, SOSLOT, CREC, CSLOT, LEREC, LESLOT,
    BREC, BSLOT, FVREC, FVSLOT, LAREC, LASLOT, FAREC, FASLOT, PJREC, PJSLOT, ADER, LADER, FADER,
    LEDER, PJDER, PEM, SHP, MHP, IHP, LSHP, SOLP, CLP, FVLP]
  simp
/-- The `CTL` words a value-group promotion writes. -/
theorem vg_ctl : ∀ x ∈ (129 :: 140 :: 142 :: 144 :: 146 :: eCtl : List L.Word),
      x.toNat < 64 ∨ x.toNat = 129 ∨ (140 ≤ x.toNat ∧ x.toNat ≤ 147) := by
  simp only [eCtl, lsCtl, lCtl, List.cons_append, List.nil_append, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_true]
  simp

section vg
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`promote_vg` refines `promoteVG PMemo.empty coreWalkFuel`**: the promoted value group is a
fresh record that decodes to the twin's result. -/
theorem vg_rel (n : Nat) (m : Mem) (a : AState) (pm₀ : PMemo) (g vis : Word) (vg : ValueGroup)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm₀)
    (hvg : decVG (erecP m) g.toNat = some vg) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "promote_vg" [g, vis] m = some (r, m')) :
    ∃ a' pm' vg', (promoteVG PMemo.empty coreWalkFuel vg).run a = .ok ((pm', vg'), a') ∧
      ArenaD m' a' ∧ PMemoR m' pm' ∧ decVG (erecP m') (r.headD 0).toNat = some vg' ∧
      ErecGrow m m' ∧ erecTop m' ≤ (m'.arr64 EREC).size ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) (129 :: 140 :: 142 :: 144 :: 146 :: eCtl) m m' ∧ TierKeep m m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (promoteVG_specW p hp n ⟨m, Locals.init []⟩ g vis) hc
  simp only [vgW] at hW
  cases n with
  | zero => rw [callW_zero'] at hW; cases hW
  | succ n =>
  -- the clears
  cases hca : callW p (n + 1) "promote_clear" [] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₁⟩ := x
  rw [hca] at hW
  obtain ⟨s₁, hs₁, -, hW₁⟩ := callW_triple (promoteClear_spec p hp n ⟨m, Locals.init []⟩) hca
  rw [hs₁] at hW₁
  obtain ⟨hP₁, hf₁⟩ := clear_rel hP hW₁
  have hD₁ : ArenaD m₁ a :=
    ⟨ArenaR.frame_ext _ _ (by simp) (by simp) m _ hf₁ a hD.1, DerR.frameM _ _ m _ hf₁ (by simp) a hD.2⟩
  have hE₁ : m₁.arr64 EREC = m.arr64 EREC := hf₁.1 EREC (by simp) (by decide)
  have ht₁ : erecTop m₁ = erecTop m := by simp only [erecTop]; rw [hf₁.2.1 129 (by simp)]
  have hP₁r : erecP m₁ = erecP m := by simp only [erecP, hE₁, ht₁]
  -- the record's words
  simp only [decVG, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hvg
  obtain ⟨kn, hkn, kd, hkd, cv, hcv, jv, hjv, rfl⟩ := hvg
  simp only [nat?, Option.map_eq_some_iff] at hkn
  obtain ⟨kw, hkw, rfl⟩ := hkn
  obtain ⟨jw, hjw, hjl, rfl⟩ := hd?_some hjv
  have hg5 : g.toNat + 5 < (m.arr64 EREC).size := by
    rcases Array.getElem?_eq_some_iff.mp (erecP_get hjw) with ⟨hh, -⟩; exact hh
  have hg5' : (g + 5).toNat = g.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
  have hg1 : (g + 1).toNat = g.toNat + 1 := toNat_add1 g (by omega)
  have hrd : vgRdW m₁ g = [kw, jw] := by
    simp only [vgRdW, hE₁, hg5']
    rw [ite_eq_right (by omega)]
    simp only [rdW, hg5', erecP_get hkw, erecP_get hjw]; rfl
  rw [vgK₀_some (h := by rw [hrd]; simp), hrd] at hW
  simp only [List.headD_cons, List.tail_cons] at hW
  -- the constant value
  cases hcb : callW p (n + 1) "promote_cv" [L.Ind.CWF, g + 1] m₁ with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨c, m₂⟩ := x
  rw [hcb, vgK_some] at hW
  obtain ⟨a₂, pm₂, cv', hrun₂, hD₂, hP₂, hcw, hgr₂, hts₂, hcp₂, hfr₂, htk₂⟩ :=
    cv_rel p hp (n + 1) m₁ a _ _ _ cv c m₂ hD₁ hP₁ (by rw [hP₁r, hg1]; exact hcv)
      (by rw [hE₁]; exact hsz) hcb
  -- the value
  cases hcc : callW p (n + 1) "promote_e" [L.Ind.CWF, jw] m₂ with
  | none => rw [hcc] at hW; cases hW
  | some x =>
  obtain ⟨xr, m₃⟩ := x
  rw [hcc, vgK₂_some] at hW
  obtain ⟨a₃, pm₃, hrun₃, hD₃, hP₃, hpw₃, hcp₃, hfr₃, htk₃⟩ :=
    (pe_rel p hp (n + 1)).1 m₂ a₂ pm₂ _ jw xr m₃ hD₂ hP₂ hjl hcc
  have hE₃ : m₃.arr64 EREC = m₂.arr64 EREC := hfr₃.1 EREC (by decide) (by decide)
  have ht₃ : erecTop m₃ = erecTop m₂ := by simp only [erecTop]; rw [hfr₃.2.1 129 (by decide)]
  -- the allocation
  cases hcd : callW p (n + 1) "erec_alloc" [6] m₃ with
  | none => rw [hcd] at hW; cases hW
  | some x =>
  obtain ⟨dr, m₄⟩ := x
  rw [hcd, vgK₃_some] at hW
  obtain ⟨s₄, hs₄, -, hW₄⟩ := callW_triple (erecAlloc_spec p (hp.get "erec_alloc") n ⟨m₃, Locals.init []⟩ 6) hcd
  rw [hs₄, show ({ mem := m₃, loc := Locals.init [] } : St).mem = m₃ from rfl] at hW₄
  obtain ⟨hdq, rfl, hd6, hroom, hctl⟩ := erAlloc_facts hW₄
  -- the record's words
  cases hce : callW p (n + 1) "vg_wr" [dr.headD 0, kw, c.headD 0, c.tail.headD 0,
      c.tail.tail.headD 0, c.tail.tail.tail.headD 0, xr.headD 0]
      (m₃.set64 CTL 129 (dr.headD 0 + 6)) with
  | none => rw [hce] at hW; cases hW
  | some x =>
  obtain ⟨r₅, m₅⟩ := x
  rw [hce, offK_some] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨s₅, hs₅, -, hW₅⟩ := callW_triple (vgWr_spec p hp (n + 1)
    ⟨m₃.set64 CTL 129 (dr.headD 0 + 6), Locals.init []⟩ _ _ _ _ _ _ _) hce
  rw [hs₅, show ({ mem := m₃.set64 CTL 129 (dr.headD 0 + 6), loc := Locals.init [] } : St).mem =
    m₃.set64 CTL 129 (dr.headD 0 + 6) from rfl] at hW₅
  have hdv : (dr.headD 0).toNat = erecTop m₃ := by rw [hdq]; rfl
  have hsz₃ : (m₃.arr64 EREC).size = (m.arr64 EREC).size := by rw [hE₃, hgr₂.2.2, hE₁]
  have h6 : (6 : Word).toNat = 6 := rfl
  rw [h6] at hd6 hroom
  obtain ⟨hlt, w0, w1, w2, w3, w4, w5, hag, hsz₅, hf₅⟩ := vgStore_facts hW₅ (by omega)
  have hE₄ : (m₃.set64 CTL 129 (dr.headD 0 + 6)).arr64 EREC = m₃.arr64 EREC :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have ht₄ : erecTop (m₃.set64 CTL 129 (dr.headD 0 + 6)) = erecTop m₃ + 6 := by
    simp only [erecTop]
    rw [rdW_set64, ite_eq_left ⟨rfl, rfl, by simpa using hctl⟩, hd6, hdv]; rfl
  have ht₅ : erecTop m₅ = erecTop m₃ + 6 := by
    simp only [erecTop] at ht₄ ⊢; rw [hf₅.2.1 129 (by simp)]; exact ht₄
  have hts₅ : erecTop m₅ ≤ (m₅.arr64 EREC).size := by rw [ht₅, hsz₅, hE₄]; omega
  have rd : ∀ i, i < 6 → (erecP m₅)[(dr.headD 0).toNat + i]? =
      (m₅.arr64 EREC)[(dr.headD 0).toNat + i]? := fun i hi =>
    erecP_getElem m₅ _ (by rw [ht₅]; omega) hts₅
  have hg₂₅ : ErecGrow m₂ m₅ := by
    refine ⟨by rw [ht₅, ← ht₃]; omega, fun i hi => ?_, by rw [hsz₅, hE₄, hE₃]⟩
    rw [hag i (by rw [hdv, ht₃]; exact hi), hE₄, hE₃]
  obtain ⟨hc4, hpw0, hn0, hsl, hpw3, ht3⟩ := hcw
  rw [← hm, ← hr]
  refine ⟨a₃, pm₃, ⟨kd, cv', decE (xr.headD 0)⟩, ?_, ?_, ?_, ?_, ?_, hts₅, hcp₃.trans hcp₂, ?_,
    (TierKeep.of_frame hf₁ (by simp)).trans (htk₂.trans (htk₃.trans
      ((TierKeep.of_frame (MemFrame.setCtl m₃ 129 _) (by simp)).trans (TierKeep.of_frame hf₅ (by simp)))))⟩
  · rw [← L.Ind.CWF_eq]
    simp only [promoteVG]
    rw [run_bind_ok hrun₂]
    simp only
    have hrun₃' : (promoteE pm₂ L.Ind.CWF.toNat (decI jw)).run a₂ =
        .ok ((pm₃, decE (xr.headD 0)), a₃) := hrun₃
    rw [run_bind_ok hrun₃']; rfl
  · have hf : MemFrame [EREC] [129] m₃ m₅ :=
      ((MemFrame.setCtl m₃ 129 _).mono (by simp) (by simp)).trans (hf₅.mono (by simp) (by simp))
    exact ⟨ArenaR.frame_ext _ _ (by simp [EREC]) (by simp) _ _ hf _ hD₃.1,
      DerR.frameM _ _ _ _ hf (by simp [EREC]) _ hD₃.2⟩
  · exact (hP₃.frame (by simp) (by simp) (MemFrame.setCtl m₃ 129 _)).frame (by simp [EREC]) (by simp)
      hf₅
  · have r0 := rd 0 (by decide); rw [Nat.add_zero, w0] at r0
    have r1 := rd 1 (by decide); rw [w1] at r1
    have r2 := rd 2 (by decide); rw [w2] at r2
    have r3 := rd 3 (by decide); rw [w3] at r3
    have r4 := rd 4 (by decide); rw [w4] at r4
    have r5 := rd 5 (by decide); rw [w5] at r5
    have hsl₅ := (hg₂₅.ext).hslice? hsl
    simp only [decVG, decCV, hlist?, nat?, hd?, r0, r1, r2, r3, r4, r5, Option.map_some,
      Option.bind_eq_bind, Option.bind_some, hkd, hpw0.1, hpw3.1, hpw₃.1, ↓reduceIte, show (dr.headD 0).toNat + 1 + 1 = (dr.headD 0).toNat + 2 from rfl,
      show (dr.headD 0).toNat + 1 + 3 = (dr.headD 0).toNat + 4 from rfl,
      show (dr.headD 0).toNat + 2 + 1 = (dr.headD 0).toNat + 3 from rfl, Option.pure_def]
    rw [hsl₅]
    simp only [Option.bind_some, hn0]
    rw [show (decI (c.tail.tail.tail.headD 0) : EIdx) = cv'.type from ht3]
    rfl
  · have := hgr₂.1
    refine ⟨by rw [ht₅, ht₃]; rw [ht₁] at this; omega, fun i hi => ?_, by rw [hsz₅, hE₄, hsz₃]⟩
    rw [hag i (by rw [hdv, ht₃]; omega), hE₄, hE₃, hgr₂.2.1 i (by rw [ht₁]; exact hi), hE₁]
  · exact ((((hf₁.mono (by simp) (by simp)).trans (hfr₂.mono (by simp) (by simp))).trans (hfr₃.mono (fun _ h => List.mem_cons_of_mem _ h)
      (by simp))).trans ((MemFrame.setCtl m₃ 129 _).mono (by simp) (by simp))).trans
      (hf₅.mono (by simp) (by simp))

end vg

end L.Arena
