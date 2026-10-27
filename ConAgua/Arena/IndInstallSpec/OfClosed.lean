import ConAgua.Arena.IndInstallSpec.Icvg
import ConAgua.Arena.RecCheckSpec.RcLook

/-!
# OfClosed

`maMR_mfr`, `ShapeCV.grow`, `taFreeA`, `taFreeC`, `taMR.ofClosed`, `blockTaCallees`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The `mentions_any` memo across a writer outside the stage memos. -/
theorem maMR_mfr {m m' : Mem} {mp : Std.HashMap EIdx Bool} (h : MFr [] [] m m') (hm : maMR m mp) :
    maMR m' mp := by
  obtain ⟨A, C, f, hA, hC⟩ := h.memo maSch.arr maSch.cs (by decide) (by decide) (by simp) (by simp)
  exact memoRG_frame maSch maSch_wf bmKey _ A C hA hC m m' f mp hm

theorem ShapeCV.grow {m m' : Mem} {q : Word} (h : ShapeCV m q) (hg : IWGrow m m')
    (hq9 : q.toNat + 9 ≤ iwTop m)
    (hsrc : ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → o + l ≤ iwTop m)
    (hptr : ∀ o l j v, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → j < l →
      iwN m (o + j) = some v → v + 1 < iwTop m) : ShapeCV m' q := by
  intro o l ho hl j hj c hc d hd
  rw [iwN_grow hg (by omega)] at ho
  rw [iwN_grow hg (by omega)] at hl
  have hb := hsrc o l ho hl
  rw [iwN_grow hg (by omega)] at hc
  have hcv := hptr o l j c ho hl hj hc
  rw [iwN_grow hg (by omega)] at hd
  exact CVExt_grow hg (h o l ho hl j hj c hc d hd)

/-! ## What the recursor stage needs of the pass -/

/-- Every word array below 320 (both tiers) but `target_abs`' memo's. -/
def taFreeA : List ArrId := (List.range 388).filter (· ≠ TAM)
/-- Every `CTL` word below 256 but that memo's two control words. -/
def taFreeC : List Word := ((List.range 256).filter (fun c => c ≠ 212 ∧ c ≠ 213)).map Nat.toUInt64

/-- A callee of a program whose text writes outside `target_abs`' memo keeps it. -/
theorem taMR.ofClosed {p : Prog} {fs : List FnName} (hcl : closedA p taFreeA taFreeC fs = true)
    {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word} {m' : Mem}
    (h : callW p n f vs m = some (r, m')) (hM : ∃ mp, taMR m mp) : ∃ mp, taMR m' mp := by
  obtain ⟨mp, hm⟩ := hM
  refine ⟨mp, taMR_mfr (S := [201, 202, 203, 204, 205, 207, 208])
    (T := [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 214, 215, 216, 217, 218, 219])
    ⟨taFreeA, taFreeC, (run_memFrame hcl hf (run_of_callW h)).1, fun b hb => ?_, fun x hx => ?_⟩
    (by decide) (by decide) hm⟩
  · simp only [taFreeA, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb
    have key : ∀ x < 388, x ≠ 206 → x < 201 ∨ 208 < x ∨ x ∈ [201, 202, 203, 204, 205, 207, 208] := by
      decide +kernel
    exact key b hb.1 (by simpa [TAM] using hb.2)
  · simp only [taFreeC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
    obtain ⟨c, ⟨hc, h2⟩, rfl⟩ := hx
    have : (Nat.toUInt64 c).toNat = c := by simp; omega
    rw [this]
    have key : ∀ x < 256, ¬ (x = 212 ∨ x = 213) → x < 202 ∨ 219 < x ∨
        x.toUInt64 ∈ ([202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 214, 215, 216, 217, 218, 219] : List Word) := by
      decide +kernel
    exact key c hc (by omega)

/-- The callees of `check_block` before the tail that keep `target_abs`' memo by their text. -/
def blockTaCallees : List FnName := ["block_raw_rec", "check_block_pass"]

end L.Ind
