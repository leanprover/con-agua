import ConAgua.Arena.IndLibSpec

/-!
# Decoders stay decoded as the pools grow: one lemma for every decoder (lane `indproofs2`)

Every decoder of the stage (`IndIface.lean`: `decHL`, `decPL`, `decBS`, `decRS`, `decTM`, …) reads
the two pools `IW`, `EREC` through `a[i]?` only, inside `Option` binds and `mapM`s. Two facts make
one stability lemma serve all of them, replacing the per-decoder "stays decoded as the pool grows"
lemmas (`decHL_grow`, `decBL_grow`, `decNL_grow`, `decCVp_grow`, `decCK_grow`, …) and the `hstab`
hypotheses of lane `indproofs`:

* **Monotone** (`OMono f`): a successful decoding reads only words that exist, so it decodes the
  same in any memory whose pools extend the old ones (`PoolExt`). Proved per decoder by the
  combinators below (`OMono.bind`, `OMono.mapM`, the readers), one line each.
* **Below the tops** (`DecB f m x`): the decoding succeeds in `truncM m`, the memory with both pools
  cut at their tops. Every memory the pools grow into (`IWGrow`) extends `truncM m`, so
  `DecB.stab` gives exactly lane `indproofs`' `hstab` (`∀ m', IWGrow m m' → f m' = some x`), and
  `DecB.grow` keeps `DecB` itself. A `DecB` fact comes from the reads' bounds (`iwN_truncM`,
  `decHL_decB`, `decRL_decB`) and from `DecB` of the parts (a record whose words are below the top).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-! ## Monotone decoders -/

/-- `m'`'s pools extend `m`'s. -/
def PoolExt (m m' : Mem) : Prop := ArrExt (iwA m) (iwA m') ∧ ArrExt (erA m) (erA m')

theorem PoolExt.refl (m : Mem) : PoolExt m m := ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem PoolExt.trans {m₁ m₂ m₃ : Mem} (h₁ : PoolExt m₁ m₂) (h₂ : PoolExt m₂ m₃) : PoolExt m₁ m₃ :=
  ⟨fun i v h => h₂.1 i v (h₁.1 i v h), fun i v h => h₂.2 i v (h₁.2 i v h)⟩

/-- **A monotone memory reader**: a successful read stays the same in any extension of the
pools. -/
structure OMono {α : Type} (f : Mem → Option α) : Prop where
  mono : ∀ m m' x, PoolExt m m' → f m = some x → f m' = some x

section mono
variable {α β : Type}

theorem OMono.const (o : Option α) : OMono (fun _ => o) := ⟨fun _ _ _ _ h => h⟩

theorem OMono.bind {f : Mem → Option α} {g : Mem → α → Option β} (hf : OMono f)
    (hg : ∀ a, OMono (fun m => g m a)) : OMono (fun m => f m >>= g m) := by
  refine ⟨fun m m' x he h => ?_⟩
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨a, ha, hx⟩ := h
  exact ⟨a, hf.mono m m' a he ha, (hg a).mono m m' x he hx⟩

theorem OMono.map {f : Mem → Option α} (g : α → β) (hf : OMono f) :
    OMono (fun m => (f m).map g) := by
  refine ⟨fun m m' x he h => ?_⟩
  simp only [Option.map_eq_some_iff] at h ⊢
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, hf.mono m m' a he ha, rfl⟩

theorem OMono.mapM {f : Mem → Nat → Option α} (hf : ∀ j, OMono (fun m => f m j)) :
    ∀ l : List Nat, OMono (fun m => l.mapM (f m))
  | [] => ⟨fun _ _ _ _ h => by simpa using h⟩
  | j :: js => by
    refine ⟨fun m m' x he h => ?_⟩
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    exact ⟨y, (hf j).mono m m' y he hy, ys, (OMono.mapM hf js).mono m m' ys he hys, rfl⟩

theorem OMono.iwGet (i : Nat) : OMono (fun m => (iwA m)[i]?) := ⟨fun _ _ _ he h => he.1 _ _ h⟩
theorem OMono.iwN (i : Nat) : OMono (fun m => iwN m i) := ⟨fun _ _ _ he h => he.1.nat? h⟩
theorem OMono.iwB (i : Nat) : OMono (fun m => iwB m i) := ⟨fun _ _ _ he h => he.1.bool? h⟩
theorem OMono.iwH {k : IdxKind} (i : Nat) : OMono (fun m => (iwH m i : Option (Idx k))) :=
  ⟨fun _ _ _ he h => he.1.hd? h⟩
theorem OMono.decHL {k : IdxKind} (o l : Nat) : OMono (fun m => (decHL m o l : Option (List (Idx k)))) :=
  ⟨fun _ _ _ he h => he.1.hslice? h⟩
theorem OMono.decCVp (q : Nat) : OMono (fun m => decCVp m q) := ⟨fun _ _ _ he h => he.2.decCV h⟩

theorem OMono.decNL (o l : Nat) : OMono (fun m => decNL m o l) :=
  OMono.mapM (fun j => OMono.iwN (o + j)) _

theorem OMono.decPL {f : Mem → Nat → Option α} (hf : ∀ q, OMono (fun m => f m q)) (o l : Nat) :
    OMono (fun m => decPL m (f m) o l) :=
  OMono.mapM (fun j => OMono.bind (OMono.iwN (o + j)) hf) _

theorem OMono.decAt {g : Mem → Nat → Nat → Option (List α)} (hg : ∀ o l, OMono (fun m => g m o l))
    (i : Nat) : OMono (fun m => decAt m (g m) i) :=
  OMono.bind (OMono.iwN i) fun o => OMono.bind (OMono.iwN (i + 1)) fun l => hg o l

end mono

/-! ### Every decoder of `IndIface.lean` is monotone

Each proof unfolds the decoder and applies the combinators (`OMono.bind`, `decAt`, `decPL`,
the readers); the do-blocks' tails are constant `some`s. -/

section decoders
theorem decCN_mono (p : Nat) : OMono (fun m => decCN m p) := by
  unfold decCN
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply OMono.bind
    | intro _
    )

theorem decMS_mono (p : Nat) : OMono (fun m => decMS m p) := by
  unfold decMS
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply OMono.bind
    | intro _
    )

theorem decRS_mono (p : Nat) : OMono (fun m => decRS m p) := by
  unfold decRS
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply decMS_mono
    | apply OMono.bind
    | intro _
    )

theorem decBS_mono (p : Nat) : OMono (fun m => decBS m p) := by
  unfold decBS
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply decMS_mono
    | apply decRS_mono
    | apply OMono.bind
    | intro _
    )

theorem decCtx_mono (p : Nat) : OMono (fun m => decCtx m p) := by
  unfold decCtx
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply decMS_mono
    | apply decRS_mono
    | apply decBS_mono
    | apply OMono.bind
    | intro _
    )

theorem decNK_mono (p : Nat) : OMono (fun m => decNK m p) := by
  unfold decNK
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply decMS_mono
    | apply decRS_mono
    | apply decBS_mono
    | apply decCtx_mono
    | apply OMono.bind
    | intro _
    )

theorem decCK_mono (p : Nat) : OMono (fun m => decCK m p) := by
  unfold decCK
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply decMS_mono
    | apply decRS_mono
    | apply decBS_mono
    | apply decCtx_mono
    | apply decNK_mono
    | apply OMono.bind
    | intro _
    )

theorem decNH_mono (p : Nat) : OMono (fun m => decNH m p) := by
  unfold decNH
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply decMS_mono
    | apply decRS_mono
    | apply decBS_mono
    | apply decCtx_mono
    | apply decNK_mono
    | apply decCK_mono
    | apply OMono.bind
    | intro _
    )

theorem decNCN_mono (p : Nat) : OMono (fun m => decNCN m p) := by
  unfold decNCN
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply decMS_mono
    | apply decRS_mono
    | apply decBS_mono
    | apply decCtx_mono
    | apply decNK_mono
    | apply decCK_mono
    | apply decNH_mono
    | apply OMono.bind
    | intro _
    )

theorem decNS_mono (p : Nat) : OMono (fun m => decNS m p) := by
  unfold decNS
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply decMS_mono
    | apply decRS_mono
    | apply decBS_mono
    | apply decCtx_mono
    | apply decNK_mono
    | apply decCK_mono
    | apply decNH_mono
    | apply decNCN_mono
    | apply OMono.bind
    | intro _
    )

theorem decNN_mono (p : Nat) : OMono (fun m => decNN m p) := by
  unfold decNN
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply decMS_mono
    | apply decRS_mono
    | apply decBS_mono
    | apply decCtx_mono
    | apply decNK_mono
    | apply decCK_mono
    | apply decNH_mono
    | apply decNCN_mono
    | apply decNS_mono
    | apply OMono.bind
    | intro _
    )

theorem decCS_mono (p : Nat) : OMono (fun m => decCS m p) := by
  unfold decCS
  refine OMono.bind (OMono.iwN p) fun t => ?_
  rcases t with _ | _ | t <;> simp only <;>
  (repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply decMS_mono
    | apply decRS_mono
    | apply decBS_mono
    | apply decCtx_mono
    | apply decNK_mono
    | apply decCK_mono
    | apply decNH_mono
    | apply decNCN_mono
    | apply decNS_mono
    | apply decNN_mono
    | apply OMono.bind
    | intro _
    ))

theorem decCR_mono (p : Nat) : OMono (fun m => decCR m p) := by
  unfold decCR
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply decMS_mono
    | apply decRS_mono
    | apply decBS_mono
    | apply decCtx_mono
    | apply decNK_mono
    | apply decCK_mono
    | apply decNH_mono
    | apply decNCN_mono
    | apply decNS_mono
    | apply decNN_mono
    | apply decCS_mono
    | apply OMono.bind
    | intro _
    )

theorem decTM_mono (p : Nat) : OMono (fun m => decTM m p) := by
  unfold decTM
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply decMS_mono
    | apply decRS_mono
    | apply decBS_mono
    | apply decCtx_mono
    | apply decNK_mono
    | apply decCK_mono
    | apply decNH_mono
    | apply decNCN_mono
    | apply decNS_mono
    | apply decNN_mono
    | apply decCS_mono
    | apply decCR_mono
    | apply OMono.bind
    | intro _
    )

theorem decCF_mono (p : Nat) : OMono (fun m => decCF m p) := by
  unfold decCF
  refine OMono.bind (OMono.iwN p) fun t => ?_
  rcases t with _ | _ | t <;> simp only <;>
  (repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply decMS_mono
    | apply decRS_mono
    | apply decBS_mono
    | apply decCtx_mono
    | apply decNK_mono
    | apply decCK_mono
    | apply decNH_mono
    | apply decNCN_mono
    | apply decNS_mono
    | apply decNN_mono
    | apply decCS_mono
    | apply decCR_mono
    | apply decTM_mono
    | apply OMono.bind
    | intro _
    ))

theorem decCC_mono (p : Nat) : OMono (fun m => decCC m p) := by
  unfold decCC
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply decMS_mono
    | apply decRS_mono
    | apply decBS_mono
    | apply decCtx_mono
    | apply decNK_mono
    | apply decCK_mono
    | apply decNH_mono
    | apply decNCN_mono
    | apply decNS_mono
    | apply decNN_mono
    | apply decCS_mono
    | apply decCR_mono
    | apply decTM_mono
    | apply decCF_mono
    | apply OMono.bind
    | intro _
    )

theorem decCG_mono (p : Nat) : OMono (fun m => decCG m p) := by
  unfold decCG
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwB
    | apply OMono.iwH
    | apply OMono.decHL
    | apply OMono.decNL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply OMono.decPL
    | apply decCN_mono
    | apply decMS_mono
    | apply decRS_mono
    | apply decBS_mono
    | apply decCtx_mono
    | apply decNK_mono
    | apply decCK_mono
    | apply decNH_mono
    | apply decNCN_mono
    | apply decNS_mono
    | apply decNN_mono
    | apply decCS_mono
    | apply decCR_mono
    | apply decTM_mono
    | apply decCF_mono
    | apply decCC_mono
    | apply OMono.bind
    | intro _
    )

theorem decKL_mono (o l : Nat) : OMono (fun m => decKL m o l) :=
  OMono.mapM (fun j => OMono.bind (OMono.iwGet (o + j)) fun w => OMono.const (decNFK w)) _

end decoders

/-! ## Below the tops -/

/-- The memory with both pools cut at their tops. -/
def truncM (m : Mem) : Mem :=
  ⟨m.bytes, (m.words.set! IW ((m.arr64 IW).extract 0 (iwTop m))).set! EREC
      ((m.arr64 EREC).extract 0 (erTop m)), m.glob⟩

/-- A word of the cut `IW`: the pool's word below the top. -/
theorem truncM_iw_get? (m : Mem) (i : Nat) :
    (iwA (truncM m))[i]? = if i < iwTop m then (iwA m)[i]? else none := by
  simp only [iwA, truncM, Mem.arr64, Array.getD_eq_getD_getElem?]
  by_cases h : IW < m.words.size
  · simp [Array.set!_eq_setIfInBounds, h, Array.getElem?_extract, IW, EREC]
    split <;> split <;> simp_all <;> omega
  · have h' : m.words[IW]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt h)
    simp [Array.set!_eq_setIfInBounds, h, IW, EREC]

theorem truncM_er_get? (m : Mem) (i : Nat) :
    (erA (truncM m))[i]? = if i < erTop m then (erA m)[i]? else none := by
  simp only [erA, truncM, Mem.arr64, Array.getD_eq_getD_getElem?]
  by_cases h : EREC < m.words.size
  · simp [Array.set!_eq_setIfInBounds, h, Array.getElem?_extract]
    split <;> simp_all <;> omega
  · have h' : m.words[EREC]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt h)
    simp [Array.set!_eq_setIfInBounds, h]

/-- A word of the cut pool is a word below the top. -/
theorem truncM_iw_get {m : Mem} {i : Nat} {v : Word} (h : (iwA (truncM m))[i]? = some v) :
    i < iwTop m ∧ (iwA m)[i]? = some v := by
  rw [truncM_iw_get?] at h; split at h
  · exact ⟨by assumption, h⟩
  · cases h

theorem truncM_er_get {m : Mem} {i : Nat} {v : Word} (h : (erA (truncM m))[i]? = some v) :
    i < erTop m ∧ (erA m)[i]? = some v := by
  rw [truncM_er_get?] at h; split at h
  · exact ⟨by assumption, h⟩
  · cases h

/-- **Below the top, the cut pool reads as the pool.** -/
theorem truncM_iw_eq {m : Mem} {i : Nat} (hi : i < iwTop m) :
    (iwA (truncM m))[i]? = (iwA m)[i]? := by rw [truncM_iw_get?, ite_eq_left hi]

theorem truncM_er_eq {m : Mem} {i : Nat} (hi : i < erTop m) :
    (erA (truncM m))[i]? = (erA m)[i]? := by rw [truncM_er_get?, ite_eq_left hi]

/-- Every memory the pools grow into extends the cut pools. -/
theorem IWGrow.truncExt {m m' : Mem} (hg : IWGrow m m') : PoolExt (truncM m) m' := by
  refine ⟨fun i v h => ?_, fun i v h => ?_⟩
  · obtain ⟨hi, hv⟩ := truncM_iw_get h
    simp only [iwA] at hv ⊢; rw [hg.2.2.1 i hi]; exact hv
  · obtain ⟨hi, hv⟩ := truncM_er_get h
    simp only [erA] at hv ⊢; rw [hg.2.2.2 i hi]; exact hv

/-- **Decoded below the tops**: the decoding succeeds in the cut pools. -/
def DecB {α : Type} (f : Mem → Option α) (m : Mem) (x : α) : Prop := f (truncM m) = some x

section decB
variable {α : Type} {f : Mem → Option α} {m m' : Mem} {x : α}

/-- **The generic stability lemma**: a decoding below the tops holds in every memory the pools
grow into (lane `indproofs`' `hstab`). -/
theorem DecB.stab (hf : OMono f) (h : DecB f m x) : ∀ m', IWGrow m m' → f m' = some x :=
  fun _m' hg => hf.mono _ _ _ hg.truncExt h

theorem DecB.get (hf : OMono f) (h : DecB f m x) : f m = some x := h.stab hf m (IWGrow.refl m)

/-- It stays below the tops as they grow. -/
theorem DecB.grow (hf : OMono f) (hg : IWGrow m m') (h : DecB f m x) : DecB f m' x := by
  refine hf.mono _ _ _ ⟨fun i v hv => ?_, fun i v hv => ?_⟩ h
  · obtain ⟨hi, hv'⟩ := truncM_iw_get hv
    rw [truncM_iw_eq (Nat.lt_of_lt_of_le hi hg.1)]
    simp only [iwA] at hv' ⊢; rw [hg.2.2.1 i hi]; exact hv'
  · obtain ⟨hi, hv'⟩ := truncM_er_get hv
    rw [truncM_er_eq (Nat.lt_of_lt_of_le hi hg.2.1)]
    simp only [erA] at hv' ⊢; rw [hg.2.2.2 i hi]; exact hv'

end decB

theorem mapM_congr_range {α : Type} {f g : Nat → Option α} :
    ∀ (l : List Nat), (∀ j ∈ l, f j = g j) → l.mapM f = l.mapM g
  | [], _ => rfl
  | j :: js, h => by
    simp only [List.mapM_cons, h j (by simp), mapM_congr_range js (fun x hx => h x (by simp [hx]))]

/-- A read of `IW` below the top is the same in the cut pools. -/
theorem iwN_truncM {m : Mem} {i : Nat} (hi : i < iwTop m) :
    iwN (truncM m) i = iwN m i := by simp only [iwN, nat?, truncM_iw_eq hi]

theorem iwH_truncM {k : IdxKind} {m : Mem} {i : Nat} (hi : i < iwTop m) :
    (iwH (truncM m) i : Option (Idx k)) = iwH m i := by simp only [iwH, hd?, truncM_iw_eq hi]

/-- A handle slice below the top reads the same in the cut pools. -/
theorem decHL_truncM {k : IdxKind} {m : Mem} {o l : Nat} (hb : o + l ≤ iwTop m) :
    (decHL (truncM m) o l : Option (List (Idx k))) = decHL m o l := by
  unfold decHL hslice?
  refine mapM_congr_range _ fun j hj => ?_
  have : j < l := List.mem_range.mp hj
  exact iwH_truncM (k := k) (by omega)

/-- A handle slice below the top is decoded below the tops. -/
theorem decHL_decB {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL m o l = some xs) (hb : o + l ≤ iwTop m) :
    DecB (fun m => (decHL m o l : Option (List (Idx k)))) m xs := by
  show decHL (truncM m) o l = some xs; rw [decHL_truncM hb]; exact h

/-- A number slice below the top is decoded below the tops. -/
theorem decNL_decB {m : Mem} {o l : Nat} {xs : List Nat}
    (h : decNL m o l = some xs) (hb : o + l ≤ iwTop m) :
    DecB (fun m => decNL m o l) m xs := by
  show decNL (truncM m) o l = some xs
  unfold decNL at *
  rw [← h]
  refine mapM_congr_range _ fun j hj => ?_
  have : j < l := List.mem_range.mp hj
  exact iwN_truncM (by omega)

/-- **The stage's slice post `decRL` gives a slice decoded below the tops.** -/
theorem decRL_decB {k : IdxKind} {m : Mem} {i : Nat} {r : List Word} {xs : List (Idx k)}
    (h : decRL (fun m => decHL m) i m r xs) :
    DecB (fun m => (decHL m (r.getD i 0).toNat (r.getD (i + 1) 0).toNat : Option (List (Idx k)))) m xs :=
  decHL_decB h.1 h.2

/-! ## The old per-decoder lemmas as instances

`decHL_grow` (lane `indproofs`, `IndInstallSpec.lean`) is the generic lemma at `decHL`. -/

theorem decHL_grow' {k : IdxKind} {m m' : Mem} (hg : IWGrow m m') {o l : Nat}
    {xs : List (Idx k)} (hb : o + l ≤ iwTop m) (h : decHL m o l = some xs) :
    decHL m' o l = some xs :=
  (decHL_decB h hb).stab (OMono.decHL o l) m' hg

end L.Ind
