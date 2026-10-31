module

public import ConAgua.Arena.RecClassSpec.PiBWRoom
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr

@[expose] public section

/-!
# CtorX

`sumAddNoOv`, the decoders `check_sum_ctors`' refinement reads (`sortsDec`,
`sumRec2`, `sumDecCN_of`, `sumSortsDec_of`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A word sum that does not wrap. -/
theorem sumAddNoOv {a b : Word} (h : ¬ a + b < a) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
  have := b.toNat_lt; have := a.toNat_lt
  rw [UInt64.toNat_add]; omega

/-! ## The relation to the twin -/

/-- The sorts headers' decoder: a pointer to `[off, len]` of a level-handle slice. -/
abbrev sortsDec (m : Mem) (q : Nat) : Option (List LIdx) := decLH m (fun o l => decHL m o l) q

theorem sortsDec_mono (q : Nat) : OMono (fun m => sortsDec m q) :=
  OMono.decAt (fun o l => OMono.decHL o l) q

/-- **A `rec2` record under the stage relation**, its two words read below the new top. -/
theorem sumRec2 {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a0 : AState} {x y : Word} {r : List Word} (h : recW m 2 [x, y] = some (r, m'))
    (hS : StageR dn vis fe m a0) :
    StageR dn vis fe m' a0 ∧ IWGrow m m' ∧ iwN (truncM m') (r.headD 0).toNat = some x.toNat ∧
      iwN (truncM m') ((r.headD 0).toNat + 1) = some y.toNat := by
  obtain ⟨hS', hg, hr, hget, htop⟩ := recW_stage h hS rfl
  subst hr
  have hT : (rdW (m.arr64 CTL) 200).toNat = iwTop m := rfl
  refine ⟨hS', hg, ?_, ?_⟩
  · rw [List.headD_cons, iwN_truncM (by simp at htop; omega)]
    simp only [iwN, nat?, iwA]; rw [show (rdW (m.arr64 CTL) 200).toNat = (rdW (m.arr64 CTL) 200).toNat + 0 from rfl,
      hget 0 (by simp)]; rfl
  · rw [List.headD_cons, iwN_truncM (by simp at htop; omega)]
    simp only [iwN, nat?, iwA]; rw [hget 1 (by simp)]; rfl

/-- The `[cv, nF]` record of a constructor, decoded below the top. -/
theorem sumDecCN_of {m : Mem} {q cvw nF : Nat} {cv : IConstantVal}
    (h0 : iwN (truncM m) q = some cvw) (h1 : iwN (truncM m) (q + 1) = some nF)
    (hcv : DecB (fun m => decCVp m cvw) m cv) : DecB (fun m => decCN m q) m (cv, nF) := by
  show decCN (truncM m) q = some (cv, nF)
  simp only [decCN, h0, h1, Option.bind_eq_bind, Option.bind_some]
  rw [show decCVp (truncM m) cvw = some cv from hcv]; rfl

/-- A sorts header, decoded below the top. -/
theorem sumSortsDec_of {m : Mem} {q o l : Nat} {xs : List LIdx}
    (h0 : iwN (truncM m) q = some o) (h1 : iwN (truncM m) (q + 1) = some l)
    (hd : decHL m o l = some xs) (hb : o + l ≤ iwTop m) : DecB (fun m => sortsDec m q) m xs := by
  show decLH (truncM m) (fun o l => decHL (truncM m) o l) q = some xs
  simp only [decLH, decAt, h0, h1, Option.bind_eq_bind, Option.bind_some]
  rw [decHL_truncM hb]; exact hd

end L.Ind

end
