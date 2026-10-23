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

/-- **`front_line`'s model is `DGrow`.** -/
theorem frontLineW_grow (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (m m' : Mem) (hm : m.arr8 IN = b.data) (i : USize)
    (a₀ : AState) (st : StateD) (hR : ArenaD m a₀) (hD : StateDR m st)
    (hsok : ConRon.Bridge.StateOK a₀) (r : List Word)
    (h : frontLineW p b.data m i.toUInt64 = some (r, m')) : DGrow m m' := by
  sorry

theorem lineKW_grow (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (m m' : Mem) (hm : m.arr8 IN = b.data) (i : USize)
    (a₀ : AState) (st : StateD) (hR : ArenaD m a₀) (hD : StateDR m st)
    (hsok : ConRon.Bridge.StateOK a₀) (ok nx : Word)
    (h : lineKW p b.data m i.toUInt64 = some (ok, nx, m')) : DGrow m m' := by
  unfold lineKW at h
  split at h
  · cases h
  rename_i r m₁ hW
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact frontLineW_grow b h64 hsize p hFI hAI hII hXI m m₁ hm i a₀ st hR hD hsok r hW
  · cases h

end grow

/-- **`front_init` leaves `DECL`, `DLP` alone.** -/
theorem initKW_dk (m m' : Mem) (h : initKW m = some m') : DK m m' := by
  sorry

end L.Front
