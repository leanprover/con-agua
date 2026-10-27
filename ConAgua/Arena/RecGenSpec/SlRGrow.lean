import ConAgua.Arena.IndInstallSpec9

/-!
# SlRGrow

`ocK2`, `NoProg`, `slR_grow`, `clsDecI_inj`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `target_major_of_outside_occ` -/

def ocK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

/-- The lookups of `nest_occ`. -/
structure NoProg (p : Prog) : Prop where
  hv : p.lookup "e_view" = some eView
  hc : p.lookup "sl_contains" = some slContains
  hf : p.lookup "no_find" = some (memoFindG noSch)
  hput : p.lookup "no_put" = some (memoPutG noSch)
  hgo : p.lookup "nest_occ_go" = some nestOccGo
  hnode : p.lookup "nest_occ_node" = some nestOccNode
  hcl : p.lookup "no_clear" = some (memoClearG noSch)
  hp : p.lookup "nest_occ" = some nestOcc

theorem slR_grow {m m' : Mem} (hg : IWGrow m m') (hT : iwTop m < 2 ^ 64) :
    ∀ {o l : Word} {ws : List Word}, SlR m o l ws → (∀ i < l.toNat, o.toNat + i < iwTop m) → SlR m' o l ws := by
  intro o l ws h
  induction h with
  | nil => intro _; exact SlR.nil
  | @cons o l ws hl _ ih =>
    intro hb
    have hl1 : 1 ≤ l.toNat := by
      rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl
      · omega
    have ho : o.toNat < iwTop m := by have := hb 0 hl1; simpa using this
    have e : rdW (m.arr64 IW) o = rdW (m'.arr64 IW) o := by simp only [rdW]; rw [hg.2.2.1 _ ho]
    rw [e]
    refine SlR.cons hl (ih fun i hi => ?_)
    have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hlm : (l - 1).toNat = l.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hl1))]; simp
    rw [ho1]; rw [hlm] at hi; have := hb (i + 1) (by omega); omega

theorem clsDecI_inj {κ : IdxKind} {x y : Word} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) :
    ((decI x : Idx κ) = decI y) ↔ x = y :=
  ⟨fun e => (decI_eq_iff x hx _).mp e ▸ decI_word_self y hy, fun e => e ▸ rfl⟩

end L.Ind
