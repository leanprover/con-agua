import ConAgua.Arena.RecGenSpec.ClassMinorSlot
import ConAgua.Arena.RecGenSpec.Rec3IwSlice
import ConAgua.Arena.RecGenSpec.RgW
import ConAgua.Census.Attr

/-!
# Classes: `ConRon.Arena.ClassRead.classes`

The refinement theorems `classReadClasses_refines_decB` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A slice read in the cut record pool lies below the top (or is empty). -/
theorem rec3ErSlice {m : Mem} {o l : Nat} {xs : List NIdx} (h : hslice? (erA (truncM m)) o l = some xs) :
    o + l ≤ erTop m ∨ l = 0 := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · exact .inr h0
  obtain ⟨w, hw⟩ := rec3SliceLast h h0
  have := (truncM_er_get hw).1
  exact .inl (by omega)

/-- **A constant record decoded below the tops is `CVExt`.** -/
theorem rec3CVExt_of_trunc {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp (truncM m) q = some cv) :
    CVExt m q ∧ decCVp m q = some cv := by
  have h' : decCV (erA (truncM m)) q = some cv := h
  obtain ⟨w, hw3, -, -⟩ := decCV_typeW h'
  have h3 := (truncM_er_get hw3).1
  obtain ⟨w1, w2, h1, h2, hs⟩ := decCV_slice h'
  refine ⟨⟨by omega, fun o l ho hl => ?_⟩, (OMono.decCVp q).mono _ _ _ (IWGrow.refl m).truncExt h⟩
  rw [truncM_er_eq (by omega)] at h1 h2
  simp only [nat?, h1, h2, Option.map_some, Option.some.injEq] at ho hl
  subst ho hl
  exact rec3ErSlice hs

/-- **`RecsOK` from the recursor shapes decoded below the tops.** -/
theorem rec3RecsOK_of_decB {m : Mem} {ro rl : Nat} {recs : List RecShape}
    (h : DecB (fun m => decPL m (decRS m) ro rl) m recs) (hb : ro + rl ≤ iwTop m) :
    RecsOK m ro rl (recs.map (·.cvR)) := by
  have hlen := decPL_length _ h
  refine ⟨hb, by simp [hlen], fun j hj => ?_⟩
  obtain ⟨p0, hp0, hRS⟩ := decPL_getH (truncM m) h j hj
  obtain ⟨q, hq, hcv, hrP, -, -⟩ := rec2DecRS_parts hRS
  obtain ⟨hcx, hcvm⟩ := rec3CVExt_of_trunc hcv
  exact ⟨p0, q, _, (rec2IwN_trunc hp0).2, by have := (rec2IwN_trunc hrP).1; omega, (rec2IwN_trunc hq).2,
    hcvm, hcx, by simp [List.getElem?_eq_getElem (show j < recs.length by omega)]⟩

/-- A class key record decoded below the tops is `CKExt`. -/
theorem rec3CKExt_of_trunc {m : Mem} {k : Nat} {key : ClassKey} (h : decCK (truncM m) k = some key) :
    CKExt m k := by
  simp only [decCK, bind, Option.bind_eq_some_iff, pure] at h
  obtain ⟨_, _, _, _, ds, hds, -⟩ := h
  obtain ⟨o, l, ho, hl, hdl⟩ := decAt_some hds
  have hlt := (rec2IwN_trunc hl).1
  refine ⟨by omega, fun o' l' ho' hl' => ?_⟩
  rw [(rec2IwN_trunc ho).2] at ho'
  rw [show k + 2 + 1 = k + 3 by omega, (rec2IwN_trunc hl).2] at hl'
  rw [show k + 2 + 1 = k + 3 by omega] at hl
  cases ho'; cases hl'
  exact rec3IwSlice hdl

/-- **`SlotsExt` from the slots decoded below the tops.** -/
theorem rec3SlotsExt_of_decB {m : Mem} {so sl : Nat} {slots : List ClassSlot}
    (h : DecB (fun m => decPL m (decCS m) so sl) m slots) (hb : so + sl ≤ iwTop m) :
    SlotsExt m so sl := by
  refine ⟨hb, fun j hj sp hsp => ?_⟩
  obtain ⟨sp', hsp', hcs⟩ := decPL_getH (truncM m) h j (by have := decPL_length _ h; omega)
  rw [(rec2IwN_trunc hsp').2] at hsp
  cases hsp
  have htag := decCS_tag hcs
  generalize hs : slots[j]'_ = s at hcs htag
  cases s with
  | motive key =>
    obtain ⟨kp, hkp, hck⟩ := decCS_motive_key hcs
    refine ⟨by have := (rec2IwN_trunc hkp).1; omega, fun kp' h0 h1 => ?_⟩
    rw [(rec2IwN_trunc hkp).2] at h1
    cases h1
    exact rec3CKExt_of_trunc hck
  | minor c C ihs =>
    obtain ⟨-, h1, -⟩ := decCS_minor hcs
    refine ⟨by have := (rec2IwN_trunc h1).1; omega, fun kp' h0 _ => ?_⟩
    rw [(rec2IwN_trunc htag).2] at h0
    simp [ClassSlot.isMinor] at h0

/-! ## The refinements with the hypotheses discharged -/

/-- **`class_read_classes` refines `ClassRead.classes`** from the slots decoded below the tops
(`SlotsExt` derived). -/
@[refines ConRon.Arena.ClassRead.classes]
theorem classReadClasses_refines_decB (p : Prog) (hc : p.lookup "iw_copy" = some iwCopy)
    (ha : p.lookup "iw_alloc" = some iwAlloc) (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "class_read_classes" = some classReadClasses) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (so sl : Word) (slots : List ClassSlot)
    (hS : StageR dn vis fe s₀.mem a₀)
    (hslots : DecB (fun m => decPL m (decCS m) so.toNat sl.toNat) s₀.mem slots)
    (hb : so.toNat + sl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_classes" [so, sl]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      CcRes s'.mem r (ConRon.Arena.ClassRead.classes slots); ⊤⦄ :=
  classReadClasses_refines p hc ha hsc hp n s₀ a₀ dn vis fe so sl slots hS
    (hslots.get (OMono.decPL (fun q => decCS_mono q) _ _)) (rec3SlotsExt_of_decB hslots hb)

end L.Ind

end
