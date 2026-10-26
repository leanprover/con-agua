import ConAgua.Front.IndApplyRefine2

/-!
# The apply step of an `inductive` line against the twin, III: `listed`, `Nodup`, `ctorIx`

`vi_listed` against the twin's `listed ← tys.mapM fun t => t.ctors.mapM st.name` (its flattening
is the slice the model pushed, `listedW_twin`); `ifl_nodup` against `List.Nodup` of the decoded
handles (`nodupW_twin`); `ifl_find_last` against the twin's `ctorIx` fold (`findLastW_twin`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend


namespace L.Front.Ind

/-! ## Slices -/

theorem islice_append {k : IdxKind} (m : Mem) (o p q : Nat) :
    islice (k := k) m o (p + q) = islice m o p ++ islice m (o + p) q := by
  simp only [islice, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp [Nat.add_assoc]

theorem islice_ext {k : IdxKind} {m m' : Mem} (hE : IExt m m') (o l : Nat) (h1 : 1 ≤ o)
    (h2 : o + l ≤ topN m IFL + 1) : islice (k := k) m' o l = islice m o l := by
  simp only [islice]
  apply List.map_congr_left
  intro c hc
  simp only [List.mem_range] at hc
  rw [hE.keep _ (by omega) (by omega)]

/-! ## `vi_listed` -/

section listed
variable {b : ByteArray} {m₀ : Mem} {st : StateD} (hD : StateDR m₀ st) (a : AState)
  (tys : List ConLeche.Frontend.IndTypeRec) (to tn : Word)
  (hF : ∀ k (hk : k < tys.length), TyF b m₀ (to.toNat + 11 * k) tys[k])
  (hlen : tn.toNat = tys.length) (hbnd : to.toNat + 11 * tys.length < 2 ^ 63)
include hD hF hlen hbnd

theorem listedGoW_twin : ∀ (n : Nat) (m m' : Mem) (j : Word), listedGoW n m to tn j = some m' →
    IExt m₀ m → TopOK m → j ≤ tn →
    ∃ L : List (List NIdx), ((tys.drop j.toNat).mapM fun t : ConLeche.Frontend.IndTypeRec => t.ctors.mapM st.name).run a = .ok (L, a) ∧
      IExt m m' ∧ TopOK m' ∧ topN m' IFL = topN m IFL + L.flatten.length ∧
      L.flatten = islice m' (topN m IFL + 1) L.flatten.length ∧
      (∀ c, c < L.flatten.length → (wd m' IFL (topN m IFL + 1 + c)).toNat < 2 ^ 32) ∧
      L.map List.length = (tys.drop j.toNat).map fun t : ConLeche.Frontend.IndTypeRec => t.ctors.length := by
  intro n
  induction n with
  | zero => intro m m' j h; simp [listedGoW] at h
  | succ n ih =>
    intro m m' j h hE hT hj
    simp only [listedGoW] at h
    split at h
    · rename_i htj
      cases h
      have : j.toNat = tys.length := by
        have := UInt64.le_iff_toNat_le.mp hj; have := UInt64.le_iff_toNat_le.mp htj; omega
      refine ⟨[], by rw [this, List.drop_length]; rfl, IExt.refl _, hT, by simp, by simp [islice],
        by simp, by rw [this, List.drop_length]; rfl⟩
    rename_i htj
    have hjt : j < tn := UInt64.not_le.mp htj
    have hjn := UInt64.lt_iff_toNat_lt.mp hjt
    have hk : j.toNat < tys.length := by omega
    obtain ⟨-, hc4, hnums, -, -, -⟩ := hF j.toNat hk
    have hi3 : (to + 11 * j + 3).toNat = to.toNat + 11 * j.toNat + 3 :=
      widx _ _ _ _ (by simp; omega)
    have hi4 : (to + 11 * j + 4).toNat = to.toNat + 11 * j.toNat + 4 :=
      widx _ _ _ _ (by simp; omega)
    rcases hg : idsGoW n m (rdW (m.arr64 IFR) (to + 11 * j + 3)) (rdW (m.arr64 IFR) (to + 11 * j + 4)) 0 with _ | m₁ <;> simp only [hg, mK, reduceCtorEq] at h
    rw [wd_eq, wd_eq, hi3, hi4, hE.wdR, hE.wdR] at hg
    have hnums' := hnums.ext hE
    obtain ⟨n1, n2, n3⟩ := hnums'
    obtain ⟨i1, i2, i3, i4⟩ := idsGoW_facts n m m₁ _ _ 0 hg hT (UInt64.le_iff_toNat_le.mpr (Nat.zero_le _))
      (by rw [hc4]; exact n2)
    simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero, hc4] at i3 i4
    have hj1 := wsucc j tn hjt
    obtain ⟨L, lr, le, lt, ltop, lfl, lb, llen⟩ := ih m₁ m' (j + 1) h (hE.trans i1) i2
      (UInt64.le_iff_toNat_le.mpr (by rw [hj1]; exact hjn))
    have hl0 : (tys[j.toNat].ctors.mapM st.name).run a =
        .ok (islice m₁ (topN m IFL + 1) tys[j.toNat].ctors.length, a) := by
      refine mapM_run_idx _ a _ _ (islice_length _ _ _) (fun c hc => ?_)
      have := i4 c (Nat.zero_le _) hc
      rw [islice_get]
      have hn := n3 c hc
      rw [← hn.1]
      exact (lkW_name hD a (by rw [← lkW_congr (hE.tbl NID (.inl rfl))]; exact this)).1
    refine ⟨islice m₁ (topN m IFL + 1) tys[j.toNat].ctors.length :: L, ?_, i1.trans le, lt, ?_, ?_, ?_, ?_⟩
    · rw [hj1] at lr
      rw [List.drop_eq_getElem_cons hk, List.mapM_cons, run_bind _ _ a _ hl0, run_bind _ _ a _ lr]
      rfl
    · rw [ltop, i3]; simp [islice_length]; omega
    · simp only [List.flatten_cons, List.length_append, islice_length]
      rw [islice_append, islice_ext le (topN m IFL + 1) tys[j.toNat].ctors.length (by omega)
        (by rw [i3]; omega)]
      congr 1
      rw [lfl, i3, show topN m IFL + tys[j.toNat].ctors.length + 1 =
        topN m IFL + 1 + tys[j.toNat].ctors.length by omega, islice_length]
    · intro c hc
      simp only [List.flatten_cons, List.length_append, islice_length] at hc
      by_cases hc' : c < tys[j.toNat].ctors.length
      · rw [le.keep _ (by omega) (by rw [i3]; omega)]
        have := i4 c (Nat.zero_le _) hc'
        have hw := (lkW_name hD a (by rw [← lkW_congr (hE.tbl NID (.inl rfl))]; exact this)).2
        exact hw
      · have := lb (c - tys[j.toNat].ctors.length) (by omega)
        rw [i3] at this
        rw [show topN m IFL + 1 + c = topN m IFL + tys[j.toNat].ctors.length + 1 +
          (c - tys[j.toNat].ctors.length) by omega]
        exact this
    · rw [List.drop_eq_getElem_cons hk, List.map_cons, List.map_cons, islice_length, llen, hj1]

include hD hF hlen hbnd in
/-- **`vi_listed` is the twin's `listed`**: its flattening is the slice `(fo, x)` the model pushed. -/
theorem listedW_twin {n : Nat} {m m' : Mem} {fo x : Word} (h : listedW n m to tn = some ((fo, x), m'))
    (hE : IExt m₀ m) (hT : TopOK m) :
    ∃ L : List (List NIdx), (tys.mapM fun t : ConLeche.Frontend.IndTypeRec => t.ctors.mapM st.name).run a = .ok (L, a) ∧
      IExt m m' ∧ TopOK m' ∧ fo.toNat = topN m IFL + 1 ∧ x.toNat = L.flatten.length ∧
      topN m' IFL = topN m IFL + L.flatten.length ∧ L.flatten = islice m' fo.toNat L.flatten.length ∧
      (∀ c, c < L.flatten.length → (wd m' IFL (fo.toNat + c)).toNat < 2 ^ 32) ∧
      L.map List.length = tys.map fun t : ConLeche.Frontend.IndTypeRec => t.ctors.length := by
  cases n with
  | zero => simp [listedW] at h
  | succ n =>
  simp only [listedW] at h
  rcases ha : allocW m IFL 0 with _ | ⟨lo, m₁⟩ <;> simp only [ha, allocK, reduceCtorEq] at h
  rcases hg : listedGoW n m₁ to tn 0 with _ | m₂ <;> simp only [hg, listedK, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  obtain ⟨a1, a2, a3, a4⟩ := allocW_ok hT ha
  simp only [show (0 : Word).toNat = 0 from rfl, Nat.add_zero] at a4
  obtain ⟨L, l1, l2, l3, l4, l5, l6, l7⟩ := listedGoW_twin hD a tys to tn hF hlen hbnd n m₁ _ 0 hg
    (hE.trans a1) a2 (UInt64.le_iff_toNat_le.mpr (Nat.zero_le _))
  simp only [show (0 : Word).toNat = 0 from rfl, List.drop_zero] at l1 l7
  have hlt := l3.1
  have htop := l3.2
  rw [a4] at l5 l6
  refine ⟨L, l1, a1.trans l2, l3, a3, ?_, by rw [l4, a4], by rw [a3]; exact l5,
    by rw [a3]; exact l6, l7⟩
  have e0 : rdW (m₂.arr64 IFL) 0 = wd m₂ IFL 0 := rfl
  have hw : (rdW (m₂.arr64 IFL) 0).toNat = topN m IFL + L.flatten.length := by
    rw [e0]; show topN m₂ IFL = _; rw [l4, a4]
  have hlo : lo.toNat ≤ (rdW (m₂.arr64 IFL) 0 + 1).toNat := by
    rw [widx2 _ _ (by simp; omega)]; simp; omega
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hlo),
    widx2 _ _ (by simp; omega), hw, a3]
  simp only [UInt64.toNat_one]; omega

end listed

/-! ## `ifl_contains`, `ifl_nodup` -/

theorem containsW_facts : ∀ (n : Nat) (m : Mem) (o l x j r : Word), containsW n m o l x j = some r →
    o.toNat + l.toNat < 2 ^ 64 →
    (r ≠ 0 → ∃ k, j.toNat ≤ k ∧ k < l.toNat ∧ wd m IFL (o.toNat + k) = x) ∧
    (r = 0 → ∀ k, j.toNat ≤ k → k < l.toNat → wd m IFL (o.toNat + k) ≠ x) := by
  intro n
  induction n with
  | zero => intro m o l x j r h; simp [containsW] at h
  | succ n ih =>
    intro m o l x j r h hb
    simp only [containsW] at h
    split at h
    · rename_i hlj
      cases h
      have := UInt64.le_iff_toNat_le.mp hlj
      exact ⟨fun h => absurd rfl h, fun _ k h1 h2 => by omega⟩
    rename_i hlj
    have hjl := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hlj)
    have hoj : (o + j).toNat = o.toNat + j.toNat := widx2 _ _ (by omega)
    split at h
    · rename_i hx
      cases h
      rw [wd_eq, hoj] at hx
      exact ⟨fun _ => ⟨j.toNat, Nat.le_refl _, hjl, hx⟩, fun h => absurd h (by decide)⟩
    · rename_i hx
      rw [wd_eq, hoj] at hx
      have hj1 := wsucc j l (UInt64.not_le.mp hlj)
      obtain ⟨i1, i2⟩ := ih m o l x (j + 1) r h hb
      rw [hj1] at i1 i2
      refine ⟨fun hr => ?_, fun hr k h1 h2 => ?_⟩
      · obtain ⟨k, k1, k2, k3⟩ := i1 hr; exact ⟨k, by omega, k2, k3⟩
      · by_cases hk : k = j.toNat
        · subst hk; exact hx
        · exact i2 hr k (by omega) h2

theorem nodupW_facts : ∀ (n : Nat) (m : Mem) (o l j u : Word), nodupW n m o l j = some u →
    o.toNat + l.toNat < 2 ^ 64 → u ≠ 0 →
    ∀ i i', j.toNat ≤ i → i < i' → i' < l.toNat → wd m IFL (o.toNat + i) ≠ wd m IFL (o.toNat + i') := by
  intro n
  induction n with
  | zero => intro m o l j u h; simp [nodupW] at h
  | succ n ih =>
    intro m o l j u h hb hu
    simp only [nodupW] at h
    split at h
    · rename_i hlj
      have := UInt64.le_iff_toNat_le.mp hlj
      intro i i' h1 h2 h3; omega
    rename_i hlj
    have hjl := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hlj)
    have hj1 := wsucc j l (UInt64.not_le.mp hlj)
    have hoj : (o + j).toNat = o.toNat + j.toNat := widx2 _ _ (by omega)
    rcases hc : containsW n m o l (rdW (m.arr64 IFL) (o + j)) (j + 1) with _ | c <;> simp only [hc, nodupK, reduceCtorEq] at h
    split at h
    · cases h; exact absurd rfl hu
    rename_i hc0
    have hc0' : c = 0 := by simpa using hc0
    obtain ⟨-, c2⟩ := containsW_facts n m o l _ _ c hc hb
    have ih' := ih m o l (j + 1) u h hb hu
    rw [hj1] at ih' c2
    intro i i' h1 h2 h3
    by_cases hi : i = j.toNat
    · subst hi
      have := c2 hc0' i' (by omega) h3
      rw [wd_eq, hoj] at this
      exact fun e => this e.symm
    · exact ih' i i' (by omega) h2 h3

theorem decI_inj' {k : IdxKind} (x y : Word) (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32)
    (h : (decI x : Idx k) = decI y) : x = y := by
  simp only [decI] at h
  have h' := congrArg (fun z : Idx k => z.word) h
  simp only [Idx.ofWord] at h'
  have := congrArg UInt32.toNat h'
  simp [UInt64.toNat_toUInt32] at this
  apply UInt64.toNat_inj.mp
  omega

/-- The decoded handles of a slice whose words are distinct and below `2^32` have no duplicate. -/
theorem islice_nodup {m : Mem} {o l : Nat} (hw : ∀ c, c < l → (wd m IFL (o + c)).toNat < 2 ^ 32)
    (hd : ∀ i i', i < i' → i' < l → wd m IFL (o + i) ≠ wd m IFL (o + i')) :
    (islice (k := .name) m o l).Nodup := by
  rw [List.nodup_iff_eq_of_getElem_eq]
  intro i i' hi hi' e
  simp only [islice_length] at hi hi'
  rw [islice_get, islice_get] at e
  have e' := decI_inj' _ _ (hw i hi) (hw i' hi') e
  apply Classical.byContradiction
  intro hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact hd i i' h hi' e'
  · exact hd i' i h hi e'.symm

/-! ## `ifl_find_last` and the twin's `ctorIx` -/

theorem findLastW_facts : ∀ (n : Nat) (m : Mem) (o x j f k : Word), findLastW n m o x j = some (f, k) →
    o.toNat + j.toNat < 2 ^ 64 →
    (f ≠ 0 → k.toNat < j.toNat ∧ wd m IFL (o.toNat + k.toNat) = x ∧
      ∀ k', k.toNat < k' → k' < j.toNat → wd m IFL (o.toNat + k') ≠ x) := by
  intro n
  induction n with
  | zero => intro m o x j f k h; simp [findLastW] at h
  | succ n ih =>
    intro m o x j f k h hb
    simp only [findLastW] at h
    split at h
    · cases h; intro hf; exact absurd rfl hf
    rename_i hj0
    have hj0' : j.toNat ≠ 0 := fun e => hj0 (UInt64.toNat_inj.mp (by simpa using e))
    have hj1 : (j - 1).toNat = j.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
    have hoj : (o + j - 1).toNat = o.toNat + (j.toNat - 1) := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [widx2 _ _ hb]; simp; omega)),
        widx2 _ _ hb]; simp; omega
    split at h
    · rename_i hx
      cases h
      intro _
      rw [wd_eq, hoj] at hx
      exact ⟨by rw [hj1]; omega, by rw [hj1]; exact hx, fun k' h1 h2 => by rw [hj1] at h1; omega⟩
    · rename_i hx
      rw [wd_eq, hoj] at hx
      intro hf
      obtain ⟨i1, i2, i3⟩ := ih m o x (j - 1) f k h (by rw [hj1]; omega) hf
      rw [hj1] at i1 i3
      refine ⟨by omega, i2, fun k' h1 h2 => ?_⟩
      by_cases hk : k' = j.toNat - 1
      · subst hk; exact hx
      · exact i3 k' h1 (by omega)

/-- The twin's `ctorIx` fold: a name's entry is the index of its last occurrence. -/
theorem ctorIx_last (l : List NIdx) : ∀ (M : Std.HashMap NIdx Nat) (c : Nat) (n : NIdx) (k : Nat)
    (hk : k < l.length), l[k] = n → (∀ k', k < k' → (hk' : k' < l.length) → l[k'] ≠ n) →
    ((l.foldl (fun (mi : Std.HashMap NIdx Nat × Nat) x => (mi.1.insert x mi.2, mi.2 + 1)) (M, c)).1)[n]? =
      some (c + k) := by
  induction l with
  | nil => intro M c n k hk; simp at hk
  | cons x xs ih =>
    intro M c n k hk h1 h2
    simp only [List.foldl_cons]
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at h1
      subst h1
      rw [ctorIx_absent xs _ _ _ (fun k' hk' => h2 (k' + 1) (by omega) (by simp; omega))]
      simp [Std.HashMap.getElem?_insert]
    | succ k =>
      rw [ih _ _ _ k (by simp at hk; omega) (by simpa using h1)
        (fun k' hk' hk'' => h2 (k' + 1) (by omega) (by simp; omega))]
      congr 1; omega
where
  ctorIx_absent (l : List NIdx) : ∀ (M : Std.HashMap NIdx Nat) (c : Nat) (n : NIdx),
      (∀ k (hk : k < l.length), l[k] ≠ n) →
      ((l.foldl (fun (mi : Std.HashMap NIdx Nat × Nat) x => (mi.1.insert x mi.2, mi.2 + 1)) (M, c)).1)[n]? =
        M[n]? := by
    induction l with
    | nil => intro M c n _; rfl
    | cons x xs ih =>
      intro M c n h
      simp only [List.foldl_cons]
      rw [ih _ _ _ (fun k hk => by have := h (k + 1) (by simp; omega); simpa using this)]
      have hx : x ≠ n := by have := h 0 (by simp); simpa using this
      simp [Std.HashMap.getElem?_insert, hx]

end L.Front.Ind
