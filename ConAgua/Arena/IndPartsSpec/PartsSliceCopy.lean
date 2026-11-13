module

public import ConAgua.Arena.IndCopy2
import ConAgua.Arena.IndPartsSpec.MemberNames
import ConAgua.Arena.IndGrindAttr
public import ConAgua.Arena.IndDecStab
import ConAgua.Arena.Env
import ConAgua.Arena.ErecRd

@[expose] public section

/-!
# PartsSliceCopy

`erCopyW_zero`, `partsHslice_last`, `partsErToIw_zero`, `partsSliceCopy`, `partsLpsCopy` and the lemmas only they use.
-/


/-!
# Refinements of `IndParts`, part 13 (lane `indproofs2`, helper `parts`): `blockShape?`'s pins

The reserved-name and level-parameter pins (`block_shape_pins_formers`/`_recs`/`_ctors`/`_ok`,
pure in the twin: one `Bool`), and the eliminator (`block_shape_large`). Shared pieces: a constant's
level parameters copied by `er_to_iw` (`partsLpsCopy`), `reserved_contains` against the twin's
`reservedBasisNames` (`partsResCont`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## A constant's level parameters, copied -/

theorem erCopyW_zero (n : Nat) (m : Mem) (d o o' : Word) : erCopyW n m d o 0 = erCopyW n m d o' 0 := by
  cases n <;> rfl

theorem partsHslice_last {k : IdxKind} {a : Array Word} : ∀ (l o : Nat) (xs : List (Idx k)),
    hslice? (aread a) o (l + 1) = some xs → ∃ w, a[o + l]? = some w
  | 0, o, xs, h => by
    rw [hslice?_succ] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, -⟩ := h
    obtain ⟨w, hw, -, -⟩ := hd?_some hx
    exact ⟨w, by simpa using hw⟩
  | l + 1, o, xs, h => by
    rw [hslice?_succ] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, -, ys, hys, -⟩ := h
    obtain ⟨w, hw⟩ := partsHslice_last l (o + 1) ys hys
    exact ⟨w, by rw [show o + (l + 1) = o + 1 + l by omega]; exact hw⟩

theorem partsErToIw_zero (n : Nat) (m : Mem) (o : Word) : erToIwW n m o 0 = erToIwW n m 0 0 := by
  simp only [erToIwW]
  rcases allocW m 0 with _ | ⟨q, m1⟩
  · rfl
  · simp only; rw [erCopyW_zero _ _ _ o 0]

/-- **`er_to_iw` of an `EREC` handle slice decoded below the tops.** -/
theorem partsSliceCopy {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {o l : Word} {r : List Word} {xs : List NIdx} (h : erToIwW n m o l = some (r, m'))
    (hS : StageR vis fe m a) (hs : hslice? (erA (truncM m)) o.toNat l.toNat = some xs) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  rw [truncM_erA] at hs
  have hsz := hS.iw.iwSize
  have hroom := erToIwW_room h hsz
  obtain ⟨rfl, hd, hg, hf, -, ht⟩ := erToIwW_dec (k := .name) h hsz hS.iw.ctl hs
  refine ⟨⟨CheckR.frame_iw hf hS.check, IWOK.of_iw hf hS.iw ?_⟩, hg, by simpa using hd, by simpa using ht⟩
  rw [← ht, hf.size IW]; exact hroom

/-- `er_to_iw` of a constant's level-parameter slice (decoded below the tops), as a handle slice. -/
theorem partsLpsCopy {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {q : Nat} {cv : IConstantVal} {r : List Word}
    (h : erToIwW n m (erRd m (UInt64.ofNat q + CV.lpsOff)) (erRd m (UInt64.ofNat q + CV.lpsLen)) =
      some (r, m'))
    (hS : StageR vis fe m a) (hcv : DecB (fun m => decCVp m q) m cv) (hq : q < 2 ^ 64) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some cv.levelParams ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  have hcv' : decCV (erA (truncM m)) q = some cv := hcv
  obtain ⟨-, hlv, -⟩ := decCV_eq_some.mp hcv'
  obtain ⟨o', l', ho, hl, hsl⟩ := hlist?_words hlv
  have hqw : (UInt64.ofNat q).toNat = q := UInt64.toNat_ofNat_of_lt' hq
  have ho' := ho; have hl' := hl
  rw [truncM_erA] at ho' hl'
  have e1 : erRd m (UInt64.ofNat q + CV.lpsOff) = o' := L.Arena.erRd_of _ _ (by
    rw [off_add_toNat rfl (by have := erecP_lt64 ho'; omega), hqw]; exact ho')
  have e2 : erRd m (UInt64.ofNat q + CV.lpsLen) = l' := L.Arena.erRd_of _ _ (by
    rw [off_add_toNat CV.lpsLen_toNat (by have := erecP_lt64 hl'; omega), hqw, ← Nat.add_assoc]
    exact hl')
  rw [e1, e2] at h
  exact partsSliceCopy h hS hsl


end L.Ind

end
