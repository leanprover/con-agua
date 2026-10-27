import ConAgua.Front.FrontPreOK2
import ConAgua.Front.FrontRun

/-!
# The frontend's records, word by word, III: one line, the driver's steps (lane `pipeline`)

`frontLineW_grow`: `front_line`'s model, on the arms of `frontLineW_refines`, is `DGrow`
(`FrontPreOK1.lean`, `FrontPreOK2.lean`); `lineKW_grow` the same for the driver's step model,
`initKW_dk` for `front_init`'s.
-/

open L.Arena
open L.Scan.Member L.Scan.Values L.Scan.Records L.Scan.Line L.Front.Fields
open ConLeche.Frontend hiding StateD RecordVerdict applyLine
open ConAgua.Scan ConAgua.Scan.RecordsLink ConAgua.Scan.LineLink
open ConAgua.Front.FieldsLink
open ConRon.Arena ConRon.Arena.Frontend

namespace L.Front

section grow
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- **`apply_any`'s model is `DGrow`.** -/
theorem applyAnyW_grow (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (m m' : Mem) (hm : m.arr8 IN = b.data) (a₀ : AState)
    (st : StateD) (hR : ArenaD m a₀) (hD : StateDR m st) (hok : ConRon.Bridge.StateOK a₀)
    (j : USize) (r : LineRec) (e : USize)
    (hloop : scanLineLoop b j true 0 0 .absent = .ok r e)
    (h : applyAnyW p b.data m j.toUInt64 = some m') : DGrow m m' := by
  unfold applyAnyW at h
  split at h
  · exact (lineRecW_dk _ _ _ _ _ _ _ _ h).grow
  split at h
  · exact (applyExprW_dk _ _ _ _ _ _ _ _ h).grow
  · unfold applyDLineW at h
    split at h; cases h; rename_i _ _ hpl
    have hX : (declLineN b.data j.toUInt64).pl ≠ 0 → DRecR b r (declLineN b.data j.toUInt64) :=
      declLine_link b h64 hsize j true 0 0 .absent DFld.none r e hloop trivial
    replace hX := hX hpl
    generalize declLineN b.data j.toUInt64 = f at hX h
    split at h
    · rename_i h25
      rcases r with _ | _ | _ | d | _ | _ <;> simp only [DRecR] at hX
      cases d with
      | ind tys cts rcs =>
        obtain ⟨-, v, hv, e', hscan⟩ := hX
        obtain ⟨x, hx, hxm⟩ := runF_some h
        have hW := M.of_run (P := fun s => s = ⟨m, Locals.init []⟩) rfl hx
          (L.Front.Ind.applyInd_spec p hFI hAI hII hXI b.data hsize x.1 _ hm f.name)
        rw [hxm, hv] at hW
        exact L.Front.Ind.applyIndW_grow h64 hsize hR hD hok hscan hW.2
      | ax _ _ => exact absurd (hX.1.symm.trans h25) (by decide)
      | defn _ _ _ _ => exact absurd (hX.1.symm.trans h25) (by decide)
      | thm _ _ => exact absurd (hX.1.symm.trans h25) (by decide)
      | opaq _ _ _ => exact absurd (hX.1.symm.trans h25) (by decide)
      | quot _ _ => exact absurd (hX.1.symm.trans h25) (by decide)
    · exact applyDeclW_grow _ _ _ st hD _ _ _ _ _ _ _ _ h

/-- **`front_line`'s model is `DGrow`.** -/
theorem frontLineW_grow (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (m m' : Mem) (hm : m.arr8 IN = b.data) (i : USize)
    (a₀ : AState) (st : StateD) (hR : ArenaD m a₀) (hD : StateDR m st)
    (hsok : ConRon.Bridge.StateOK a₀) (r : List Word)
    (h : frontLineW p b.data m i.toUInt64 = some (r, m')) : DGrow m m' := by
  have hL := lineFwd_link b h64 hsize i
  have hs := ConAgua.Scan.skipWs_toUInt64_eq b h64 (by omega) i
  unfold frontLineW at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact (DK.refl m).grow
  rename_i hok
  obtain ⟨r₀, q, hsc⟩ : ∃ r q, scanLineFwd b i = .ok r q := by
    revert hL hok
    cases scanLineFwd b i with
    | ok r q => intro _ _; exact ⟨r, q, rfl⟩
    | err e => intro hL hok; rw [← hL] at hok; exact absurd rfl hok
  rw [USize.toNat_toUInt64, ← hs] at h
  have hsc' := hsc
  unfold scanLineFwd at hsc'
  dsimp only at hsc'
  generalize hsw : skipWs b i = s at hsc' h
  split at h
  · -- a record
    rename_i hrec
    obtain ⟨hslt, hs123⟩ := hrec
    have hsU : s < b.usize := (lt_usize_iff b h64 hsize s).mpr hslt
    have hb123 : byteAt b s = 123 := by
      rw [byteW_eq b h64 hsize] at hs123; exact (u8_toUInt64_eq _ 123 (by decide)).mp hs123
    simp only [hb123, show ((123 : UInt8) == 10) = false by decide, Bool.false_eq_true, ite_false,
      show (b.usize ≤ s) = False from propext ⟨fun h' => absurd hsU (USize.not_lt.mpr h'), False.elim⟩,
      show ((123 : UInt8) != 123) = false by decide] at hsc'
    split at hsc'
    · cases hsc'
    rename_i r' j hloop
    obtain ⟨m₁, hW, hm₁⟩ := Option.map_eq_some_iff.mp h
    rw [← succ_toUInt64 h64] at hW
    simp only [okRes, Prod.mk.injEq] at hm₁
    obtain ⟨-, rfl⟩ := hm₁
    exact applyAnyW_grow b h64 hsize p hFI hAI hII hXI m m₁ hm a₀ st hR hD hsok _ r' j hloop hW
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact (DK.refl m).grow

theorem lineKW_grow (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (m m' : Mem) (hm : m.arr8 IN = b.data) (i : USize)
    (a₀ : AState) (st : StateD) (hR : ArenaD m a₀) (hD : StateDR m st)
    (hsok : ConRon.Bridge.StateOK a₀) (ok nx : Word)
    (h : lineKW p b.data m i.toUInt64 = some (ok, nx, m')) : DGrow m m' := by
  unfold lineKW at h
  split at h; cases h; rename_i r m₁ hW
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact frontLineW_grow b h64 hsize p hFI hAI hII hXI m m₁ hm i a₀ st hR hD hsok r hW
  · cases h

end grow

/-- **`front_init` leaves `DECL`, `DLP` alone.** -/
theorem initKW_dk (m m' : Mem) (h : initKW m = some m') : DK m m' := by
  unfold initKW at h
  split at h; cases h; rename_i m₂ hW
  split at h
  · cases h
    simp only [frontInitW] at hW
    cases h1 : putK NID 0 (nainternW m) with
    | none => rw [h1] at hW; simp [initK] at hW
    | some m₁ =>
      rw [h1, initK_some] at hW
      refine (DK.putK (.inl rfl) (fun w m₃ hI => ?_) h1).trans
        (DK.putK (.inr (.inl rfl)) (fun w m₃ hI => ?_) hW)
      · exact DK.ofFrame (consInternM_frame nanonCS_wf hI)
      · exact DK.ofFrame (consInternM_frame zeroCS_wf hI)
  · cases h

end L.Front
