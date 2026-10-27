import ConAgua.Arena.IndPosSpec.CrLook
import ConAgua.Arena.IndPosSpec.EnvFindWHit
import ConAgua.Arena.IndPosSpec.PiBWStage
import ConAgua.Arena.IndSumSpec5
import ConAgua.Arena.RecCheckSpec

/-!
# BvbWMfr

`hbMR_mfr`, `PosMR`, `posmemo_erCopyW_iw`, `erToIwW_mfr`, `MFr.ofFvbF`, `envFindW_mfr` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem hbMR_mfr {S0 : List ArrId} {T0 : List Word} {m m' : Mem} (hf : MFr S0 T0 m m') (hS : HBM ∉ S0)
    (hT : (214 : Word) ∉ T0) {mp : Std.HashMap (EIdx × Nat) Bool} (h : hbMR m mp) : hbMR m' mp := by
  obtain ⟨A, C, f, hA, hC⟩ := hf.memo HBM 214 (by decide) (by decide) hS hT
  exact memoRV_frame hbSch hbSch_wf lfKey hbVR A C hA hC m m' f (fun _ _ h => h) mp h

/-- **The walk memos of the positivity check, well formed in `m`.** -/
structure PosMR (m : Mem) : Prop where
  no : ∃ mp, noMR m mp
  dp : ∃ mp, dpMR m mp
  rp : ∃ mp, rpMR m mp
  hb : ∃ mp, hbMR m mp
  rf : ∃ M G g, RfInv m M G g

theorem posmemo_erCopyW_iw : ∀ (n : Nat) (m m' : Mem) (d s l : Word), erCopyW n m d s l = some m' →
    MemFrame [IW] [200] m m'
  | 0, _, _, _, _, _, h => by simp [erCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [erCopyW_nil n m d s l hl] at h; cases h; exact MemFrame.refl _ _ _
    · rw [erCopyW_step n m d s l hl] at h
      exact (set64IW_frame _ _ _).trans (posmemo_erCopyW_iw n _ _ _ _ _ h)

theorem erToIwW_mfr {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : erToIwW n m o l = some (r, m')) :
    MFr [] [] m m' := by
  unfold erToIwW at h
  split at h; · simp at h
  rename_i q m1 hal
  split at h; · simp at h
  rename_i m2 hc
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact (allocW_mfr hal).trans (MFr.of_iw (posmemo_erCopyW_iw _ _ _ _ _ _ hc))

/-! ## Frames of the models, by `mfr_auto` (`IndPosSpec/NoGoStep`) -/

/-- Across `fvar_b` (its write set, the `fvarRange` memo). -/
theorem MFr.ofFvbF {m m' : Mem} {args r : List Word} (h : fvbF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (fvbF_frame h)
    (fun b hb => .inl (by simp only [frA, List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb; decide))
    (fun x hx => .inl (by simp only [frC, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide))
theorem envFindW_mfr {m m' : Mem} {w vis : Word} {r : List Word} (h : envFindW m w vis = some (r, m')) :
    MFr [] [] m m' := by rw [envFindW_mem h]; exact MFr.refl _ _ _

theorem dcGoW_mfr : ∀ (n : Nat) (m m' : Mem) (hi off l : Word) (r : List Word),
    dcGoW n m hi off l = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, h => by simp [dcGoW] at h
  | n + 1, m, m', hi, off, l, r, h => by
    unfold dcGoW dcK at h
    mfr_auto h [MFr.ofFvbF, dcGoW_mfr n _ _ _ _ _ _]

theorem dcWf_mfr {n : Nat} {m m' : Mem} {ctx off l : Word} {r : List Word} (h : dcWf n m ctx off l = some (r, m')) :
    MFr [] [] m m' := by
  cases n with
  | zero => simp [dcWf] at h
  | succ n => exact dcGoW_mfr _ _ _ _ _ _ _ h

theorem bvbW_mfr {n : Nat} {m m' : Mem} {h f x : Word} (hb : bvbW n m h f = some (x, m')) : MFr [] [] m m' := by
  have hfr : BbFrame m m' := by
    match n, hb with
    | n + 1, hb =>
      by_cases hs : derBW m h = 32767
      · rw [bvbW_sat (n := n) (m := m) (h := h) (f := f) hs] at hb
        match n, hb with
        | k + 1, hb => rw [bbN_succ] at hb; exact bbMemoW_frame k m m' h f x hb
      · rw [bvbW_pk (n := n) (m := m) (h := h) (f := f) hs] at hb
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
        exact MemFrame.refl _ _ _
  exact MFr.of_frame hfr (by simp [BMEMO]) (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> decide)

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `cv_lps` under the stage relation, an empty slice at any offset -/

theorem posmemo_cvLpsW_mfr {n : Nat} {m m' : Mem} {q : Word} {r : List Word} (h : cvLpsW n m q = some (r, m')) :
    MFr [] [] m m' := erToIwW_mfr h

end L.Ind

end

end
