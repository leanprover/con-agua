import ConAgua.Arena.IndPos
import ConAgua.Arena.StageInst1
import ConAgua.Arena.IndGrindAttr

/-!
# MkLook

`LowFr`, `mkAppW_low`, `mkLamW_low`, `mkForallW_low`, `mkLetW_low`, `mkProjW_low` and the lemmas only they use.
-/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Low frames: writers of the store tiers (arrays and `CTL` words below 64) -/

def LowFr (m m' : Mem) : Prop :=
  ∃ (A : List ArrId) (C : List Word), MemFrame A C m m' ∧ (∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320)) ∧ (∀ x ∈ C, x.toNat < 64)

theorem mkAppW_low {m m' : Mem} {f x r : Word} (hI : mkAppW m f x = some (r, m')) : LowFr m m' := by
  have hf : MemFrame (ADER :: (tier1 ADER) :: appCS.wset) [appCS.ca, appCS.ca + 1] m m' := by
    unfold mkAppW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame appCS_wf hx) hI
  exact ⟨_, _, hf, by simp [tier1, tierOff, ConsSch.wset, appCS, ADER, AREC, ASLOT], by simp [appCS]⟩

theorem mkLamW_low {m m' : Mem} {t b r : Word} (hI : mkLamW m t b = some (r, m')) : LowFr m m' := by
  have hf : MemFrame (LADER :: (tier1 LADER) :: lamCS.wset) [lamCS.ca, lamCS.ca + 1] m m' := by
    unfold mkLamW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame lamCS_wf hx) hI
  exact ⟨_, _, hf, by simp [tier1, tierOff, ConsSch.wset, lamCS, LADER, LAREC, LASLOT], by simp [lamCS]⟩

theorem mkForallW_low {m m' : Mem} {t b r : Word} (hI : mkForallW m t b = some (r, m')) : LowFr m m' := by
  have hf : MemFrame (FADER :: (tier1 FADER) :: forallCS.wset) [forallCS.ca, forallCS.ca + 1] m m' := by
    unfold mkForallW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame forallCS_wf hx) hI
  exact ⟨_, _, hf, by simp [tier1, tierOff, ConsSch.wset, forallCS, FADER, FAREC, FASLOT], by simp [forallCS]⟩

theorem mkLetW_low {m m' : Mem} {t v b r : Word} (hI : mkLetW m t v b = some (r, m')) : LowFr m m' := by
  have hf : MemFrame (LEDER :: (tier1 LEDER) :: letCS.wset) [letCS.ca, letCS.ca + 1] m m' := by
    unfold mkLetW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame letCS_wf hx) hI
  exact ⟨_, _, hf, by simp [tier1, tierOff, ConsSch.wset, letCS, LEDER, LEREC, LESLOT], by simp [letCS]⟩

theorem mkProjW_low {m m' : Mem} {n i e r : Word} (hI : mkProjW m n i e = some (r, m')) : LowFr m m' := by
  have hf : MemFrame (PJDER :: (tier1 PJDER) :: projCS.wset) [projCS.ca, projCS.ca + 1] m m' := by
    unfold mkProjW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame projCS_wf hx) hI
  exact ⟨_, _, hf, by simp [tier1, tierOff, ConsSch.wset, projCS, PJDER, PJREC, PJSLOT], by simp [projCS]⟩

/-! ## `replace_apps_go` / `replace_apps_node` -/

structure MkLook (p : Prog) : Prop where
  hd : p.lookup "der_b" = some derB
  appF : p.lookup "app_find" = some appFind
  appP : p.lookup "app_push" = some appPush
  appI : p.lookup "intern_app" = some internApp
  appM : p.lookup "mk_app" = some mkApp
  lamF : p.lookup "lam_find" = some lamFind
  lamP : p.lookup "lam_push" = some lamPush
  lamI : p.lookup "intern_lam" = some internLamL
  lamM : p.lookup "mk_lam" = some mkLam
  forF : p.lookup "forall_find" = some forallFind
  forP : p.lookup "forall_push" = some forallPush
  forI : p.lookup "intern_forall" = some internForallL
  forM : p.lookup "mk_forall" = some mkForall
  ltF : p.lookup "letE_find" = some letFind
  ltP : p.lookup "letE_push" = some letPush
  ltI : p.lookup "intern_letE" = some internLet
  ltM : p.lookup "mk_let" = some mkLet
  prjF : p.lookup "proj_find" = some projFind
  prjP : p.lookup "proj_push" = some projPush
  prjI : p.lookup "intern_proj" = some internProj
  prjM : p.lookup "mk_proj" = some mkProj

structure AhLook (p : Prog) : Prop where
  hi1 : I1Prog p
  hv : p.lookup "e_view" = some eView
  hph : p.lookup "ph_app" = some phApp
  hf : p.lookup "sl_find" = some slFind
  hpw : p.lookup "pin_word" = some pinWordL
  hsf : p.lookup "sort_find" = some sortFind
  hsp : p.lookup "sort_push" = some sortPush
  his : p.lookup "intern_sort" = some internSort
  hff : p.lookup "fvar_find" = some fvarFind
  hfp : p.lookup "fvar_push" = some fvarPush
  hif : p.lookup "intern_fvar" = some internFVar
  hcs : p.lookup "nest_canon_sub" = some nestCanonSub
  hp : p.lookup "app_hole" = some appHole

def rpMkW (m : Mem) (g a2 x2 c2 y : Word) (x : Word) : Option (Word × Mem) :=
  if g = 4 then mkAppW m a2 x2
  else if g = 5 then mkLamW m a2 x2
  else if g = 6 then mkForallW m a2 x2
  else if g = 7 then mkLetW m a2 x2 c2
  else mkProjW m x y a2

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (no nl us b nn f f1 h g x y z a2 x2 c2 r : Word) (v fr rr : List Word)
theorem rpMkW_let : rpMkW m 7 a2 x2 c2 y x = mkLetW m a2 x2 c2 := by simp [rpMkW]
theorem rpMkW_proj : rpMkW m 9 a2 x2 c2 y x = mkProjW m x y a2 := by simp [rpMkW]
end arms
attribute [ind_grind] rpMkW_let rpMkW_proj

theorem raSch_wf : raSch.WF := ⟨by decide, by decide⟩

abbrev rpMR (m : Mem) (mp : Std.HashMap EIdx EIdx) : Prop :=
  MemoRG raSch bmKey (fun w : Word => decE w) m mp

end L.Ind

end
