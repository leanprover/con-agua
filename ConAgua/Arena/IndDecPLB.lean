module

public import ConAgua.Arena.IndDecStab

@[expose] public section

/-!
# IndDecPLB: slices decoded with their bound

A member's constructor slice `(o, l)` decoded below the tops says nothing about `o` when `l = 0`;
the positivity walk (`CssAt`) wants `o + l ≤ iwTop` for every member. `decPLB` carries the bound in
the decoding (below the tops the pool's size is its top), so it survives `sl_cons` and growth.
`decMSB` is a member shape whose constructor slice is decoded with its bound: the group headers of
`block_groups` (`decGH`) carry it, `block_shape_members_of` copies it into the member records, and
`ShapeSl` keeps it for the shape's members (`block_shape_member_ctors`).
-/

noncomputable section

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- A pointer slice whose end lies within the pool. -/
def decPLB {α : Type} (m : Mem) (f : Nat → Option α) (o l : Nat) : Option (List α) :=
  if o + l ≤ (m.arr64 IW).size then decPL m f o l else none

/-- A member's constructors with their slice's bound. -/
def decCNSB (m : Mem) (q : Nat) : Option (List (IConstantVal × Nat)) :=
  decAt m (fun o l => decPLB m (decCN m) o l) q

/-- A member shape whose constructor slice (words `2`, `3`) is decoded with its bound. -/
def decMSB (m : Mem) (p : Nat) : Option MemberShape := do
  let x ← decMS m p
  let _ ← decCNSB m (p + 2)
  pure x

/-- Below the tops, the pool's size is at most its top. -/
theorem iwA_truncM_size_le (m : Mem) : ((truncM m).arr64 IW).size ≤ iwTop m := by
  apply Nat.le_of_not_lt
  intro h
  have := truncM_iw_get? m (iwTop m)
  rw [ite_eq_right (Nat.lt_irrefl _)] at this
  simp only [iwA, aread_apply, Array.getElem?_eq_getElem h] at this
  cases this

/-- A `[off, len]` member record decoded with its bound: the bound. -/
theorem decCNSB_bound {m : Mem} {q : Nat} {cs : List (IConstantVal × Nat)}
    (h : DecB (fun m => decCNSB m q) m cs) :
    ∃ o l, iwN (truncM m) q = some o ∧ iwN (truncM m) (q + 1) = some l ∧ o + l ≤ iwTop m ∧
      decPL (truncM m) (decCN (truncM m)) o l = some cs := by
  have h' : decCNSB (truncM m) q = some cs := h
  simp only [decCNSB, decAt, Option.bind_eq_bind, Option.bind_eq_some_iff] at h'
  obtain ⟨o, ho, l, hl, hd⟩ := h'
  simp only [decPLB] at hd
  split at hd
  · rename_i hb
    exact ⟨o, l, ho, hl, Nat.le_trans hb (iwA_truncM_size_le m), hd⟩
  · cases hd

theorem iwA_size_mono {m m' : Mem} (he : PoolExt m m') : (m.arr64 IW).size ≤ (m'.arr64 IW).size := by
  rcases Nat.eq_zero_or_pos (m.arr64 IW).size with h0 | h0
  · omega
  · have h1 : iwA m ((m.arr64 IW).size - 1) = some ((m.arr64 IW)[(m.arr64 IW).size - 1]'(by omega)) :=
      Array.getElem?_eq_getElem _
    have h2 := he.1 _ _ h1
    simp only [iwA, aread_apply] at h2
    have := (Array.getElem?_eq_some_iff.mp h2).1
    omega

theorem decPLB_omono {α : Type} {f : Mem → Nat → Option α} (hf : ∀ q, OMono (fun m => f m q)) (o l : Nat) :
    OMono (fun m => decPLB m (f m) o l) := by
  refine ⟨fun m m' x he h => ?_⟩
  simp only [decPLB] at h ⊢
  split at h
  · rename_i hb
    rw [ite_eq_left (Nat.le_trans hb (iwA_size_mono he))]
    exact (OMono.decPL hf o l).mono m m' x he h
  · cases h

theorem decCNSB_mono (q : Nat) : OMono (fun m => decCNSB m q) :=
  OMono.decAt (fun o l => decPLB_omono decCN_mono o l) q

theorem decMSB_mono (p : Nat) : OMono (fun m => decMSB m p) :=
  OMono.bind (decMS_mono p) fun _ => OMono.bind (decCNSB_mono (p + 2)) fun _ => OMono.const _

/-- … and at least every bound below the top, when the top lies within the pool. -/
theorem le_iwA_truncM_size {m : Mem} {k : Nat} (hk : k ≤ iwTop m) (hT : iwTop m ≤ (m.arr64 IW).size) :
    k ≤ ((truncM m).arr64 IW).size := by
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · omega
  · have e := truncM_iw_get? m (k - 1)
    rw [ite_eq_left (by omega)] at e
    simp only [iwA, aread_apply, Array.getElem?_eq_getElem (show k - 1 < (m.arr64 IW).size by omega)] at e
    have := (Array.getElem?_eq_some_iff.mp e).1
    omega

/-- A pointer slice decoded by `f` is decoded by any `g` that extends `f`. -/
theorem decPL_weak {α : Type} {m : Mem} {f g : Nat → Option α}
    (hfg : ∀ v x, f v = some x → g v = some x) {o l : Nat} {xs : List α}
    (e : decPL m f o l = some xs) : decPL m g o l = some xs := by
  unfold decPL at e ⊢
  generalize List.range l = L at e ⊢
  induction L generalizing xs with
  | nil => simpa using e
  | cons j js ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at e ⊢
    obtain ⟨y, hy, ys, hys, rfl⟩ := e
    obtain ⟨v, hv, hy⟩ := hy
    exact ⟨y, ⟨v, hv, hfg _ _ hy⟩, ys, ih hys, rfl⟩

theorem decMSB_decMS {m : Mem} {p : Nat} {x : MemberShape} (h : decMSB m p = some x) :
    decMS m p = some x := by
  simp only [decMSB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨y, hy, -, -, rfl⟩ := h
  exact hy

/-- The members decoded with their bounds, decoded. -/
theorem decPL_decMSB {m : Mem} {o l : Nat} {xs : List MemberShape}
    (e : decPL m (decMSB m) o l = some xs) : decPL m (decMS m) o l = some xs :=
  decPL_weak (fun _ _ h => decMSB_decMS h) e

/-- `decMSB`'s parts: the member, and its constructor slice with the bound. -/
theorem decMSB_some {m : Mem} {p : Nat} {x : MemberShape} (h : decMSB m p = some x) :
    decMS m p = some x ∧ decCNSB m (p + 2) = some x.ctors := by
  simp only [decMSB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨y, hy, cs, hcs, rfl⟩ := h
  refine ⟨hy, ?_⟩
  rw [decMS] at hy
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hy
  obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, f, hf, rfl⟩ := hy
  simp only [decCNSB, decAt, Option.bind_eq_bind, Option.bind_eq_some_iff, decPLB] at hcs ⊢
  obtain ⟨o, ho, l, hl, hd'⟩ := hcs
  simp only [decAt, Option.bind_eq_bind, Option.bind_eq_some_iff] at hf
  obtain ⟨o', ho', l', hl', hd''⟩ := hf
  rw [Nat.add_assoc] at hl
  rw [ho] at ho'; cases ho'
  rw [show p + 2 + 1 = p + (2 + 1) by omega, hl] at hl'; cases hl'
  refine ⟨o, ho, l, by rw [Nat.add_assoc]; exact hl, ?_⟩
  split at hd'
  · rw [ite_eq_left (by assumption)]; exact hd''
  · cases hd'

/-- A member and its constructor slice's bound make a `decMSB`. -/
theorem decMSB_of {m : Mem} {p o l : Nat} {x : MemberShape} (h : decMS m p = some x)
    (ho : iwN m (p + 2) = some o) (hl : iwN m (p + 3) = some l) (hb : o + l ≤ (m.arr64 IW).size) :
    decMSB m p = some x := by
  have hy := h
  rw [decMS] at hy
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hy
  obtain ⟨a, ha, b, hb', c, hc, d, hd, e, he, f, hf, rfl⟩ := hy
  simp only [decAt, Option.bind_eq_bind, Option.bind_eq_some_iff] at hf
  obtain ⟨o', ho', l', hl', hd''⟩ := hf
  rw [ho] at ho'; cases ho'
  rw [show p + 2 + 1 = p + 3 by omega, hl] at hl'; cases hl'
  simp only [decMSB, h, decCNSB, decAt, ho, show p + 2 + 1 = p + 3 by omega, hl, decPLB,
    ite_true, hb, hd'', bind, Option.bind_some, pure]

/-- **A shape record's members (words `0`, `1`) decoded with their bounds** (`ShapeSl`'s third
clause). -/
abbrev MsB (m : Mem) (q : Word) : Prop :=
  ∃ ms, DecB (fun m => decAt m (decPL m (decMSB m)) q.toNat) m ms

theorem MsB.grow {m m' : Mem} {q : Word} (h : MsB m q) (hg : IWGrow m m') : MsB m' q :=
  let ⟨ms, h⟩ := h
  ⟨ms, h.grow (OMono.decAt (fun o l => OMono.decPL decMSB_mono o l) _) hg⟩

/-- … carried to a copy of the record's words `0`, `1`. -/
theorem MsB.copy {m m' : Mem} {p q : Word} (h : MsB m p) (hg : IWGrow m m') (hq : q.toNat + 1 < iwTop m')
    (e0 : (m'.arr64 IW)[q.toNat]? = (m'.arr64 IW)[p.toNat]?)
    (e1 : (m'.arr64 IW)[q.toNat + 1]? = (m'.arr64 IW)[p.toNat + 1]?) : MsB m' q := by
  obtain ⟨ms, h⟩ := h
  have hp : decAt (truncM m') (decPL (truncM m') (decMSB (truncM m'))) p.toNat = some ms :=
    h.grow (OMono.decAt (fun o l => OMono.decPL decMSB_mono o l) _) hg
  refine ⟨ms, ?_⟩
  show decAt (truncM m') (decPL (truncM m') (decMSB (truncM m'))) q.toNat = some ms
  simp only [decAt, bind, Option.bind_eq_some_iff] at hp ⊢
  obtain ⟨o, ho, l, hl, hd⟩ := hp
  have tr : ∀ {i j v}, j < iwTop m' → (m'.arr64 IW)[j]? = (m'.arr64 IW)[i]? →
      iwN (truncM m') i = some v → iwN (truncM m') j = some v := by
    intro i j v hj e hv
    simp only [iwN, nat?, Option.map_eq_some_iff] at hv ⊢
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨-, hw'⟩ := truncM_iw_get hw
    refine ⟨w, ?_, rfl⟩
    rw [truncM_iw_get?, ite_eq_left hj]
    simp only [iwA, aread_apply] at hw' ⊢
    rw [e, hw']
  exact ⟨o, tr (by omega) e0 ho, l, tr hq e1 hl, hd⟩

end L.Ind

end
