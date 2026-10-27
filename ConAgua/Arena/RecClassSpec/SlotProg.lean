import ConAgua.Arena.IndRealAbs

/-!
# SlotProg

`SlotProg`, `nameCopyW_afr`, `memberNamesW_afr`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Models -/

/-- The lookups `class_read_slot` needs. -/
structure SlotProg (p : Prog) : Prop where
  fh : p.lookup "fvar_head" = some fvarHead
  ad : AdF p
  v : p.lookup "e_view" = some eView
  f : p.lookup "sl_find" = some slFind
  cm : p.lookup "class_of_motive_var" = some classOfMotiveVar
  c : p.lookup "iw_copy" = some iwCopy
  a : p.lookup "iw_alloc" = some iwAlloc
  sc : p.lookup "sl_cons" = some slCons
  r2 : p.lookup "rec2" = some rec2
  r4 : p.lookup "rec4" = some rec4
  r5 : p.lookup "rec5" = some rec5
  i1 : p.lookup "class_read_minor_ih1" = some classReadMinorIh1
  is : p.lookup "class_read_minor_ihs" = some classReadMinorIhs
  fin : p.lookup "class_read_minor_finish" = some classReadMinorFinish
  pb : p.lookup "pi_binders" = some piBinders
  min : p.lookup "class_read_minor" = some classReadMinor
  tl : p.lookup "class_read_minor_tail" = some classReadMinorTail
  mc : p.lookup "member_names_copy" = some memberNamesCopy
  mn : p.lookup "block_shape_member_names" = some blockShapeMemberNames
  ct : p.lookup "sl_contains" = some slContains
  x : p.lookup "env_ix" = some envIxL
  g : p.lookup "env_row_get" = some envRowGetL
  ef : p.lookup "env_find" = some envFindL
  npc : p.lookup "class_n_pc_of" = some classNPcOf
  smot : p.lookup "class_read_slot_motive" = some classReadSlotMotive
  slot : p.lookup "class_read_slot" = some classReadSlot

theorem nameCopyW_afr : ∀ (n : Nat) (m m' : Mem) (d s l : Word), nameCopyW n m d s l = some m' →
    AFr m m'
  | 0, _, _, _, _, _, h => by simp [nameCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [nameCopyW_nil n m d s l hl] at h; cases h; exact AFr.refl _
    · rw [nameCopyW_step n m d s l hl] at h
      exact (set64IW_afr _ _ _).trans (nameCopyW_afr n _ _ _ _ _ h)

/-- `memberNamesW` keeps `AbsOK`. -/
theorem memberNamesW_afr {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : memberNamesW n m p = some (r, m')) : AFr m m' := by
  unfold memberNamesW at h
  afr_auto h [allocW_afr, nameCopyW_afr _ _ _ _ _ _]

end L.Ind

end
