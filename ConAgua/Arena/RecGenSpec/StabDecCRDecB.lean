import ConAgua.Arena.RecGenSpec.DecNLAt
import ConAgua.Arena.RecGenSpec.StabDecCKExt

/-!
# StabDecCRDecB

`word_lt_of_stab`, `iwN_lt_of_stab`, `ptr_lt_of_stab`, `iwN_huge`, `decPL_truncM_of`, `decNL_truncM_of` and the lemmas only they use.
-/

open ConRon.Arena
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Perturbation tools -/

/-- **A word that every growth keeps is below the top.** -/
theorem word_lt_of_stab {m : Mem} {i : Nat} {w : Word} (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hw : (m.arr64 IW)[i]? = some w) (hdet : ∀ m', IWGrow m m' → (m'.arr64 IW)[i]? = some w) :
    i < iwTop m := by
  have hil := (Array.getElem?_eq_some_iff.mp hw).1
  rcases Nat.lt_or_ge i (iwTop m) with h | h
  · exact h
  obtain ⟨hg, hset, -⟩ := perturb h hil hsz (w + 1)
  have e := hdet _ hg
  rw [hset] at e
  exact absurd (congrArg UInt64.toNat (Option.some.inj e)) (word_succ_ne w)

/-- **A number that every growth reads the same is below the top.** -/
theorem iwN_lt_of_stab {m : Mem} {i v : Nat} (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hv : iwN m i = some v) (hdet : ∀ m', IWGrow m m' → iwN m' i = some v) : i < iwTop m := by
  obtain ⟨w, hw, hwv⟩ := iwN_set_word hv
  refine word_lt_of_stab hsz hw fun m' hg => ?_
  have h' := hdet m' hg
  simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at h'
  obtain ⟨w', hw', e⟩ := h'
  rw [hw']; congr 1; apply UInt64.toNat_inj.mp; rw [e, hwv]

/-- **A word whose perturbation to `2^64 - 1` breaks a stable decoding is below the top.** -/
theorem ptr_lt_of_stab {α : Type} {f : Mem → Option α} {m : Mem} {x : α} {i : Nat}
    (h : StabD f m x) (hsz : (m.arr64 IW).size < 2 ^ 64) (hil : i < (m.arr64 IW).size)
    (hfail : iwTop m ≤ i → ∀ m', ((m'.arr64 IW)[i]? = some (UInt64.ofNat (2 ^ 64 - 1))) →
      (∀ j, j ≠ i → (m'.arr64 IW)[j]? = (m.arr64 IW)[j]?) → (m'.arr64 IW).size = (m.arr64 IW).size →
      f m' ≠ some x) :
    i < iwTop m := by
  rcases Nat.lt_or_ge i (iwTop m) with hlt | hge
  · exact hlt
  obtain ⟨hg, hset, hoth⟩ := perturb hge hil hsz (UInt64.ofNat (2 ^ 64 - 1))
  exact absurd (h _ hg) (hfail hge _ hset hoth ((set64IW_frame m _ _).2.2.1 IW))

/-- A read at index `2^64 - 1` (or any index past the array) fails. -/
theorem iwN_huge {m : Mem} (hsz : (m.arr64 IW).size < 2 ^ 64) : iwN m (2 ^ 64 - 1) = none := by
  simp only [iwN, nat?, iwA, Option.map_eq_none_iff]
  exact Array.getElem?_eq_none (by omega)

/-- A pointer slice read in the cut pools: the slots below the top, each pointer's decoding the
same. -/
theorem decPL_truncM_of {α : Type} {m : Mem} {f f' : Nat → Option α} {o l : Nat}
    (hb : ∀ j < l, o + j < iwTop m) (hf : ∀ j < l, ∀ q, iwN m (o + j) = some q → f' q = f q) :
    decPL (truncM m) f' o l = decPL m f o l := by
  unfold decPL
  refine mapM_congr_range _ fun j hj => ?_
  have hj' : j < l := List.mem_range.mp hj
  rw [iwN_truncM (hb j hj')]
  cases hq : iwN m (o + j) with
  | none => rfl
  | some q => simp only [Option.bind_eq_bind, Option.bind_some]; exact hf j hj' q hq

/-- A number slice read in the cut pools. -/
theorem decNL_truncM_of {m : Mem} {o l : Nat} (hb : ∀ j < l, o + j < iwTop m) :
    decNL (truncM m) o l = decNL m o l := by
  unfold decNL
  exact mapM_congr_range _ fun j hj => iwN_truncM (hb j (List.mem_range.mp hj))

theorem decCK_truncM {m : Mem} {k : Nat} (hk : CKExt m k) : decCK (truncM m) k = decCK m k := by
  obtain ⟨h1, h2⟩ := hk
  simp only [decCK]
  rw [iwH_truncM (by omega), iwH_truncM (by omega)]
  have hat : decAt (truncM m) (decHL (k := IdxKind.expr) (truncM m)) (k + 2) =
      decAt m (decHL (k := IdxKind.expr) m) (k + 2) := by
    simp only [decAt]
    rw [iwN_truncM (by omega), iwN_truncM (by omega)]
    rcases ho : iwN m (k + 2) with _ | o
    · simp
    rcases hl : iwN m (k + 2 + 1) with _ | l
    · simp
    show decHL (truncM m) o l = decHL m o l
    rcases h2 o l ho (by simpa using hl) with hb | rfl
    · exact decHL_truncM hb
    · simp [decHL, hslice?]
  rw [hat]

/-! ## `decNN` -/

theorem decNN_eq {m : Mem} {q : Nat} {x : Nat × Nat} (h : decNN m q = some x) :
    iwN m q = some x.1 ∧ iwN m (q + 1) = some x.2 := by
  simp only [decNN, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact ⟨ha, hb⟩

/-- **A stable `decNN` reads below the top.** -/
theorem stab_decNN {m : Mem} {q : Nat} {x : Nat × Nat} (h : StabD (fun m => decNN m q) m x)
    (hsz : (m.arr64 IW).size < 2 ^ 64) : q + 1 < iwTop m := by
  obtain ⟨-, h1⟩ := decNN_eq h.get
  exact iwN_lt_of_stab hsz h1 fun m' hg => (decNN_eq (h m' hg)).2

theorem decNN_truncM {m : Mem} {q : Nat} (hq : q + 1 < iwTop m) : decNN (truncM m) q = decNN m q := by
  simp only [decNN, iwN_truncM (show q < iwTop m by omega), iwN_truncM hq]

/-! ## `decCS` -/

theorem decCS_minor_eq {m : Mem} {sp c : Nat} {cc : NIdx} {ihs : List (Nat × Nat)}
    (h : decCS m sp = some (.minor c cc ihs)) :
    iwN m sp = some 1 ∧ iwN m (sp + 1) = some c ∧ iwH m (sp + 2) = some cc ∧
      decAt m (decPL m (decNN m)) (sp + 3) = some ihs := by
  simp only [decCS, bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, h⟩ := h
  rcases t with _ | _ | t
  · exfalso
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, e⟩ := h
    cases e
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨c', hc, cc', hcc, ihs', hihs, e⟩ := h
    simp only [ClassSlot.minor.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact ⟨ht, hc, hcc, hihs⟩
  · simp at h

/-- **A stable class slot reads the same in the cut pools.** -/
theorem stab_decCS_decB {m : Mem} {sp : Nat} {s : ClassSlot} (h : StabD (fun m => decCS m sp) m s)
    (hsz : (m.arr64 IW).size < 2 ^ 64) : decCS (truncM m) sp = some s := by
  obtain ⟨hsp2, hck⟩ := stab_decCS_ext h hsz
  have h0 := h.get
  rcases decCS_some_cases h0 with ⟨ht, kp, k, hkp, hk, rfl⟩ | ⟨ht, c, hc, cc, ihs, rfl⟩
  · simp [decCS, iwN_truncM (show sp < iwTop m by omega), ht,
      iwN_truncM (show sp + 1 < iwTop m by omega), hkp, decCK_truncM (hck kp ht hkp), hk]
  -- a minor slot
  obtain ⟨-, -, hcc, hihs⟩ := decCS_minor_eq h0
  obtain ⟨o3, l3, ho3, hl3, hdpl⟩ := decAt_some hihs
  have hs4 : sp + 4 < iwTop m := by
    refine iwN_lt_of_stab hsz hl3 fun m' hg => ?_
    obtain ⟨-, -, -, h3⟩ := decCS_minor_eq (h m' hg)
    obtain ⟨o', l', ho', hl', hd'⟩ := decAt_some h3
    rw [show sp + 3 + 1 = sp + 4 by omega] at hl'
    rw [hl', ← decPL_length m' hd', decPL_length m hdpl]
  rw [show sp + 3 + 1 = sp + 4 by omega] at hl3
  -- the pointers, then their pairs
  have hgr : ∀ m', IWGrow m m' → decPL m' (decNN m') o3 l3 = some ihs := by
    intro m' hg
    obtain ⟨-, -, -, h3⟩ := decCS_minor_eq (h m' hg)
    obtain ⟨o', l', ho', hl', hd'⟩ := decAt_some h3
    rw [iwN_grow hg (by omega), ho3] at ho'
    rw [show sp + 3 + 1 = sp + 4 by omega, iwN_grow hg hs4, hl3] at hl'
    cases ho'; cases hl'; exact hd'
  have hptr : ∀ j < l3, o3 + j < iwTop m := by
    intro j hj
    obtain ⟨q, hq, -⟩ := decPL_getH m hdpl j hj
    refine ptr_lt_of_stab h hsz (iwN_lt hq) fun hge m' hset hoth hsz' => fun e => ?_
    obtain ⟨-, -, -, h3⟩ := decCS_minor_eq e
    obtain ⟨o', l', ho', hl', hd'⟩ := decAt_some h3
    have e3 : iwN m' (sp + 3) = iwN m (sp + 3) := by
      simp only [iwN, nat?, iwA]; rw [hoth _ (by omega)]
    have e4 : iwN m' (sp + 3 + 1) = iwN m (sp + 4) := by
      simp only [iwN, nat?, iwA]; rw [hoth _ (by omega)]
    rw [e3, ho3] at ho'; rw [e4, hl3] at hl'
    cases ho'; cases hl'
    obtain ⟨q', hq', hf⟩ := decPL_getH m' hd' j hj
    have : q' = 2 ^ 64 - 1 := by
      simp only [iwN, nat?, iwA, hset, Option.map_some, Option.some.injEq] at hq'
      rw [← hq']; rfl
    subst this
    simp only [decNN, bind, Option.bind_eq_some_iff] at hf
    obtain ⟨a, ha, -⟩ := hf
    rw [← hsz'] at hsz
    rw [iwN_huge hsz] at ha; cases ha
  have hpair : ∀ j < l3, ∀ q, iwN m (o3 + j) = some q → q + 1 < iwTop m := by
    intro j hj q hq
    obtain ⟨q0, hq0, hf0⟩ := decPL_getH m hdpl j hj
    rw [hq] at hq0; cases hq0
    have hjl : j < ihs.length := by rw [decPL_length m hdpl]; exact hj
    refine stab_decNN (x := ihs[j]'hjl) (fun m' hg => ?_) hsz
    obtain ⟨q', hq', hf'⟩ := decPL_getH m' (hgr m' hg) j hj
    rw [iwN_grow hg (hptr j hj), hq] at hq'
    cases hq'; exact hf'
  have hcc' : (iwH (truncM m) (sp + 2) : Option NIdx) = iwH m (sp + 2) := iwH_truncM (by omega)
  have hdpl' : decPL (truncM m) (decNN (truncM m)) o3 l3 = some ihs := by
    rw [decPL_truncM_of hptr (fun j hj q hq => decNN_truncM (hpair j hj q hq)), hdpl]
  simp only [decCS, iwN_truncM (show sp < iwTop m by omega), ht,
    iwN_truncM (show sp + 1 < iwTop m by omega), hc, hcc', hcc, decAt,
    iwN_truncM (show sp + 3 < iwTop m by omega), ho3, show sp + 3 + 1 = sp + 4 by omega,
    iwN_truncM hs4, hl3]
  simp [hdpl']

/-! ## `decCR` -/

theorem decCR_eq {m : Mem} {p : Nat} {rd : ClassRead} (h : decCR m p = some rd) :
    decAt m (decPL m (decCS m)) p = some rd.slots ∧ decAt m (decNL m) (p + 2) = some rd.recCls := by
  simp only [decCR, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact ⟨ha, hb⟩

/-- **A stably decoding class reading is decoded below the tops.** -/
theorem stab_decCR_decB {m : Mem} {p : Nat} {rd : ClassRead} (h : StabD (fun m => decCR m p) m rd)
    (hsz : (m.arr64 IW).size < 2 ^ 64) : DecB (fun m => decCR m p) m rd := by
  obtain ⟨h1, h2⟩ := decCR_eq h.get
  obtain ⟨so, sl, hso, hsl, hsd⟩ := decAt_some h1
  obtain ⟨o2, l2, ho2, hl2, hnd⟩ := decAt_some h2
  -- the lengths are determined
  have hp1 : p + 1 < iwTop m := by
    refine iwN_lt_of_stab hsz hsl fun m' hg => ?_
    obtain ⟨g1, -⟩ := decCR_eq (h m' hg)
    obtain ⟨o', l', -, hl', hd'⟩ := decAt_some g1
    rw [hl', ← decPL_length m' hd', decPL_length m hsd]
  have hp3 : p + 2 + 1 < iwTop m := by
    refine iwN_lt_of_stab hsz hl2 fun m' hg => ?_
    obtain ⟨-, g2⟩ := decCR_eq (h m' hg)
    obtain ⟨o', l', -, hl', hd'⟩ := decAt_some g2
    rw [hl', ← decNL_length m' hd', decNL_length m hnd]
  -- every growth reads the same slices
  have hgr : ∀ m', IWGrow m m' → decPL m' (decCS m') so sl = some rd.slots ∧
      decNL m' o2 l2 = some rd.recCls := by
    intro m' hg
    obtain ⟨g1, g2⟩ := decCR_eq (h m' hg)
    obtain ⟨o', l', ho', hl', hd'⟩ := decAt_some g1
    obtain ⟨o'', l'', ho'', hl'', hd''⟩ := decAt_some g2
    rw [iwN_grow hg (by omega), hso] at ho'
    rw [iwN_grow hg hp1, hsl] at hl'
    rw [iwN_grow hg (by omega), ho2] at ho''
    rw [iwN_grow hg hp3, hl2] at hl''
    cases ho'; cases hl'; cases ho''; cases hl''
    exact ⟨hd', hd''⟩
  -- the class numbers
  have hrc : ∀ j < l2, o2 + j < iwTop m := by
    intro j hj
    exact iwN_lt_of_stab hsz (decNL_at hnd j hj) fun m' hg => by
      rw [decNL_at (hgr m' hg).2 j hj]
  -- the slot pointers
  have hptr : ∀ j < sl, so + j < iwTop m := by
    intro j hj
    obtain ⟨q, hq, -⟩ := decPL_getH m hsd j hj
    refine ptr_lt_of_stab h hsz (iwN_lt hq) fun hge m' hset hoth hsz' => fun e => ?_
    obtain ⟨g1, -⟩ := decCR_eq e
    obtain ⟨o', l', ho', hl', hd'⟩ := decAt_some g1
    have e0 : iwN m' p = iwN m p := by simp only [iwN, nat?, iwA]; rw [hoth _ (by omega)]
    have e1 : iwN m' (p + 1) = iwN m (p + 1) := by simp only [iwN, nat?, iwA]; rw [hoth _ (by omega)]
    rw [e0, hso] at ho'; rw [e1, hsl] at hl'
    cases ho'; cases hl'
    obtain ⟨q', hq', hf⟩ := decPL_getH m' hd' j hj
    have : q' = 2 ^ 64 - 1 := by
      simp only [iwN, nat?, iwA, hset, Option.map_some, Option.some.injEq] at hq'
      rw [← hq']; rfl
    subst this
    rw [← hsz'] at hsz
    simp only [decCS, iwN_huge hsz, bind, Option.bind] at hf
    cases hf
  -- each slot reads the same in the cut pools
  have hslot : ∀ j < sl, ∀ q, iwN m (so + j) = some q → decCS (truncM m) q = decCS m q := by
    intro j hj q hq
    have hjl : j < rd.slots.length := by rw [decPL_length m hsd]; exact hj
    obtain ⟨q0, hq0, hf0⟩ := decPL_getH m hsd j hj
    rw [hq] at hq0; cases hq0
    rw [hf0]
    refine stab_decCS_decB (s := rd.slots[j]'hjl) (fun m' hg => ?_) hsz
    obtain ⟨q', hq', hf'⟩ := decPL_getH m' (hgr m' hg).1 j hj
    rw [iwN_grow hg (hptr j hj), hq] at hq'
    cases hq'; exact hf'
  show decCR (truncM m) p = some rd
  have hs' : decPL (truncM m) (decCS (truncM m)) so sl = some rd.slots := by
    rw [decPL_truncM_of hptr hslot, hsd]
  have hn' : decNL (truncM m) o2 l2 = some rd.recCls := by rw [decNL_truncM_of hrc, hnd]
  simp only [decCR, decAt, iwN_truncM (show p < iwTop m by omega), hso, iwN_truncM hp1, hsl,
    iwN_truncM (show p + 2 < iwTop m by omega), ho2, iwN_truncM hp3, hl2]
  simp [hs', hn']

end L.Ind
