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

set_option linter.unusedSimpArgs false

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

theorem flatten_length_map {α : Type} (L : List (List α)) :
    L.flatten.length = (L.map List.length).sum := by
  induction L with
  | nil => rfl
  | cons l L ih => simp [ih]

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
    cases hg : idsGoW n m (rdW (m.arr64 IFR) (to + 11 * j + 3)) (rdW (m.arr64 IFR) (to + 11 * j + 4)) 0 with
    | none => rw [hg, memK_none] at h; cases h
    | some m₁ =>
    rw [hg, memK_some] at h
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
      exact (lkW_name hD a (by rw [← lkW_congr (hE.other NID (by decide) (by decide) (by decide))]; exact this)).1
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
        have hw := (lkW_name hD a (by rw [← lkW_congr (hE.other NID (by decide) (by decide) (by decide))]; exact this)).2
        exact hw
      · have := lb (c - tys[j.toNat].ctors.length) (by omega)
        rw [i3] at this
        rw [show topN m IFL + 1 + c = topN m IFL + tys[j.toNat].ctors.length + 1 +
          (c - tys[j.toNat].ctors.length) by omega]
        exact this
    · rw [List.drop_eq_getElem_cons hk, List.map_cons, List.map_cons, islice_length, llen, hj1]

end listed

end L.Front.Ind
