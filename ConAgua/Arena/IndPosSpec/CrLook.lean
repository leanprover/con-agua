import ConAgua.Arena.IndPosSpec.DpGoW
import ConAgua.Arena.IndPosSpec.NoGoStep
import ConAgua.Arena.IndPosSpec.RxMapW

/-!
# CrLook

`dpMR_mfr`, `allocW_mfr`, `posRecW_mfr`, `instW_mfr`, `RxFr`, `CrLook`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem dpMR_mfr {S0 : List ArrId} {T0 : List Word} {m m' : Mem} (hf : MFr S0 T0 m m') (hS : DPM ∉ S0)
    (hT : (206 : Word) ∉ T0) {mp : Std.HashMap EIdx Nat} (h : dpMR m mp) : dpMR m' mp := by
  obtain ⟨A, C, f, hA, hC⟩ := hf.memo DPM 206 (by decide) (by decide) hS hT
  exact memoRG_frame dpSch dpSch_wf bmKey (fun w : Word => w.toNat) A C hA hC m m' f mp h

theorem allocW_mfr {m m' : Mem} {k q : Word} (h : allocW m k = some (q, m')) : MFr [] [] m m' := by
  simp only [allocW] at h
  split at h; · simp at h
  split at h; · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact MFr.of_iw (allocMem_frame m k)

theorem posRecW_mfr {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m')) :
    MFr [] [] m m' := by
  simp only [posRecW] at h
  split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  exact (allocW_mfr ‹_›).trans (MFr.of_iw (wrIW_frame _ _ _))

theorem instW_mfr (n : Nat) : ∀ (m m' : Mem) (ao al e : Word) (r : List Word), instW n m ao al e = some (r, m') →
    MFr [] [] m m' := by
  induction n with
  | zero => intro m m' ao al e r h; simp [instW] at h
  | succ n ih =>
    intro m m' ao al e r h
    simp only [instW, instK1, instK2.eq_def, instK3.eq_def] at h
    mfr_auto h [MFr.ofI1F, ih _ _ _ _ _ _]

/-! ### The banked walk `replace_fvars` writes only its own memo -/

/-- The banked walk's write set among the memos. -/
abbrev RxFr (m m' : Mem) : Prop := MFr [RFM] [208, 209, 218, 219] m m'

end L.Ind

namespace L.Ind

open L.Arena

/-- The lookups of `nest_crest`. -/
structure CrLook (p : Prog) : Prop where
  rx : RxLook p
  ng : p.lookup "nest_phs_go" = some nestPhsGo
  np : p.lookup "nest_phs" = some nestPhs
  ip : p.lookup "inst_pis_with" = some instPisWith
  raf : p.lookup "ra_find" = some (memoFindG raSch)
  rap : p.lookup "ra_put" = some (memoPutG raSch)
  rgo : p.lookup "replace_apps_go" = some replaceAppsGo
  rnd : p.lookup "replace_apps_node" = some replaceAppsNode
  rcl : p.lookup "ra_clear" = some (memoClearG raSch)
  ra : p.lookup "replace_apps" = some replaceApps
  cc : p.lookup "nest_canon_crest" = some nestCanonCrest
  cr : p.lookup "nest_crest" = some nestCrest

end L.Ind

end
