import ConAgua.Arena.RecClassSpec.MjProg

/-!
# GtProg

`rec2CG_get`, `GtProg`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Pieces -/

theorem rec2CG_get {m : Mem} {g : Nat} {G : ClassGen} (h : decCG m g = some G) :
    iwN m g = some G.nP ∧ decAt m (decPL m (decCS m)) (g + 7) = some G.slots := by
  simp only [decCG, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨nP, hnP, ps, hps, cls, hcls, ft, hft, sl, hsl, cts, hcts, el, hel, pre, hpre, rfl⟩ := h
  exact ⟨hnP, hsl⟩

/-! ## `class_gen_rec_ty_tail`, `class_gen_rec_ty` -/

/-- The lookups `class_gen_rec_ty` needs. -/
structure GtProg (p : Prog) : Prop extends MtProg p where
  fvf : p.lookup "fvar_find" = some fvarFind
  fvp : p.lookup "fvar_push" = some fvarPush
  ifv : p.lookup "intern_fvar" = some internFVar
  sv : p.lookup "class_gen_slot_var" = some classGenSlotVar
  ms : p.lookup "class_read_motive_slot" = some classReadMotiveSlot
  mv : p.lookup "class_gen_mot_var" = some classGenMotVar
  snoc : p.lookup "sl_snoc" = some slSnoc
  rtt : p.lookup "class_gen_rec_ty_tail" = some classGenRecTyTail
  rt : p.lookup "class_gen_rec_ty" = some classGenRecTy

end L.Ind

end
