module

public import ConAgua.Arena.IndPosSpec.CtxFields
public import ConAgua.Arena.IndPosSpec.GrpAt
public import ConAgua.Arena.IndPosSpec.MatesW
public import ConAgua.Arena.IndPartsSpec.RecTW
import ConAgua.Arena.IndPartsSpec.BlockCounts
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.Env
import all ConAgua.Arena.IndPos2

@[expose] public section

/-!
# FgW2

`nestBlockOf_specW`, `nboW`, `FmLook`, `nestFrameMates_specW` (`nfmW`) and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_block_of`, `nest_frame_mates` -/

/-- **`nest_block_of(vis, c)` is its model `nboW`** (generated). -/
l_model nestBlockOf_specW (p : Prog)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hf : p.lookup "env_find" = some envFindL)
    (hp : p.lookup "nest_block_of" = some nestBlockOfL)
  fns [hp ↦ nboW]
  specs [callW_spec p n "env_find"]
  grind [ind_grind] finish [rdW_eq] gen 20

/-- The lookups of `nest_frame_mates`. -/
structure FmLook (p : Prog) : Prop where
  hc : p.lookup "sl_contains" = some slContains
  ha : p.lookup "iw_alloc" = some iwAlloc
  hcp : p.lookup "iw_copy" = some iwCopy
  hsn : p.lookup "sl_snoc" = some slSnoc
  hgo : p.lookup "nest_frame_mates_go" = some nestFrameMatesGoL
  hg : p.lookup "env_row_get" = some envRowGetL
  hf : p.lookup "env_find" = some envFindL
  hbo : p.lookup "nest_block_of" = some nestBlockOfL
  hp : p.lookup "nest_frame_mates" = some nestFrameMatesL

/-- **`nest_frame_mates(vis, c)` is its model `nfmW`** (generated). -/
l_model nestFrameMates_specW (p : Prog) (hL : FmLook p)
  fns [hL.hp ↦ nfmW list]
  specs [nestBlockOf_specW p hL.hg hL.hf hL.hbo n, nestFrameMatesGo_spec p hL.hc hL.ha hL.hcp hL.hsn hL.hgo n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

/-! ## `sl_new1` -/

/-- The model of `sl_new1(x)`. -/
def new1W (m : Mem) (x : Word) : Option (List Word × Mem) :=
  match allocW m 1 with
  | none => none
  | some (q, _) => some ([q, 1], (allocMem m 1).set64 IW (rdW (m.arr64 CTL) 200) x)

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_frame_grp`: the stack grown by the group's holes, and the group's names -/

/-- **`nest_frame_grp` is its model `fgW`** (generated). -/
l_model nestFrameGrp_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc2 : p.lookup "iw_copy" = some iwCopy) (h3 : p.lookup "rec3" = some rec3)
    (h4 : p.lookup "rec4" = some rec4) (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hv : p.lookup "e_view" = some eView) (hs : p.lookup "sl_cons" = some slCons)
    (hpb : p.lookup "pi_binders" = some piBinders)
    (hp : p.lookup "nest_frame_grp" = some nestFrameGrpL)
  fns [hp ↦ fgW list]
  specs [posRec4_specW p ha h4 n, L.Ind.rec3_specW_iw p ha h3 n, piBinders_spec p ha hc2 hv hs hpb n,
    slSnoc_specW p ha hc2 hsn n]
  grind [arena_grind, ind_grind]
  finish [rdW_eq, Locals.init_cons_zero, CWF, List.getD_cons_zero, List.getD_cons_succ] gen 20 instances 5000

/-- The generated result step `fgW.k_nest_frame_grp` is the identity on `fgW`'s results. -/
theorem fgW_kId (n : Nat) (m : Mem) (hi us dO dL gO gL pO pL nO nL : Word) :
    fgW.k_nest_frame_grp (fgW n m hi us dO dL gO gL pO pL nO nL) = fgW n m hi us dO dL gO gL pO pL nO nL := by
  rcases n with _ | n
  · simp [fgW.eq_1, fgW.k_nest_frame_grp]
  rw [fgW.eq_2]; split
  · simp [fgW.k_nest_frame_grp]
  generalize posRecW _ _ = x; rcases x with _ | ⟨k, m1⟩
  · simp [fgW.k_nest_frame_grp, fgW.k_rec4]
  simp only [fgW.k_rec4]
  generalize piBW _ _ _ _ = x; rcases x with _ | ⟨rs, m2⟩
  · simp [fgW.k_nest_frame_grp, fgW.k_pi_binders]
  simp only [fgW.k_pi_binders]
  generalize posRecW _ _ = x; rcases x with _ | ⟨h, m3⟩
  · simp [fgW.k_nest_frame_grp, fgW.k_rec3]
  simp only [fgW.k_rec3]
  generalize snocW _ _ _ _ _ = y; rcases y with _ | ⟨r, m4⟩
  · simp [fgW.k_nest_frame_grp, fgW.k_sl_snoc]
  simp only [fgW.k_sl_snoc]
  generalize snocW _ _ _ _ _ = y; rcases y with _ | ⟨r, m5⟩
  · simp [fgW.k_nest_frame_grp, fgW.k_sl_snoc_2]
  simp only [fgW.k_sl_snoc_2]
  generalize fgW _ _ _ _ _ _ _ _ _ _ _ _ = z; rcases z with _ | ⟨r', m6⟩ <;> simp [fgW.k_nest_frame_grp]

section arms
variable (n : Nat) (m m1 : Mem) (hi us dO dL gO gL pO pL nO nL c key : Word) (r : List Word)
theorem fgW_nil (h : gL = 0) : fgW (n + 1) m hi us dO dL gO gL pO pL nO nL = some ([pO, pL, nO, nL], m) :=
  fgW.arm1 _ _ _ _ _ _ _ _ _ _ _ _ h
theorem fgW_cons (h : ¬ gL = 0) : fgW (n + 1) m hi us dO dL gO gL pO pL nO nL =
    fgW.k_rec4 n hi us dO dL gO gL pO pL nO nL (rdW (m.arr64 IW) (rdW (m.arr64 IW) gO))
      (posRecW m [rdW (m.arr64 IW) (rdW (m.arr64 IW) gO), us, dO, dL]) := fgW.arm2 _ _ _ _ _ _ _ _ _ _ _ _ h
theorem fgK1_some : fgW.k_rec4 n hi us dO dL gO gL pO pL nO nL c (some (key, m1)) =
    fgW.k_pi_binders n hi us dO dL gO gL pO pL nO nL c key
      (piBW n m1 CWF (rdW (m1.arr64 IW) (rdW (m1.arr64 IW) gO + 1))) := by rw [fgW.k_rec4.arm1]
theorem fgKb_some : fgW.k_pi_binders n hi us dO dL gO gL pO pL nO nL c key (some (r, m1)) =
    fgW.k_rec3 n hi us dO dL gO gL pO pL nO nL c (posRecW m1 [key, hi, r.getD 1 0]) := by
  rw [fgW.k_pi_binders.arm1]; rcases r with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
theorem fgK2_some : fgW.k_rec3 n hi us dO dL gO gL pO pL nO nL c (some (key, m1)) =
    fgW.k_sl_snoc n hi us dO dL gO gL nO nL c (snocW n m1 pO pL key) := by rw [fgW.k_rec3.arm1]
theorem fgK3_some : fgW.k_sl_snoc n hi us dO dL gO gL nO nL c (some (r, m1)) =
    fgW.k_sl_snoc_2 n hi us dO dL gO gL (r.headD 0) (r.tail.headD 0) (snocW n m1 nO nL c) := by
  rw [fgW.k_sl_snoc.arm1]
theorem fgK4_some : fgW.k_sl_snoc_2 n hi us dO dL gO gL pO pL (some (r, m1)) =
    fgW n m1 hi us dO dL (gO + 1) (gL - 1) pO pL (r.headD 0) (r.tail.headD 0) := by
  rw [fgW.k_sl_snoc_2.arm1, fgW_kId]
end arms
attribute [ind_grind] fgW_nil fgW_cons fgK1_some fgKb_some fgK2_some fgK3_some fgK4_some

end L.Ind

namespace L.Ind

open L.Arena

/-- A group's tail, from the next pointer on. -/
theorem GrpAt.tail {m : Mem} {o : Nat} {x : NIdx × EIdx} {grp : List (NIdx × EIdx)} (h : GrpAt m o (x :: grp)) :
    GrpAt m (o + 1) grp := fun i hi => by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h (i + 1) (by simp; omega)
  exact ⟨a1, a2, a3, by rw [show o + 1 + i = o + (i + 1) by omega]; exact a4, a5, a6, a7, by simpa using a8, a9,
    a10, by simpa using a11⟩

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_frame_holes`: the group's holes, interned in order -/

/-- **`nest_frame_holes` is its model `fhW`** (generated). -/
l_model nestFrameHoles_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc2 : p.lookup "iw_copy" = some iwCopy) (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar)
    (hp : p.lookup "nest_frame_holes" = some nestFrameHolesL)
  fns [hp ↦ fhW list]
  specs [internFVar_spec p hff hfp hif n, slSnoc_specW p ha hc2 hsn n]
  grind [arena_grind, ind_grind] finish [rdW_eq, Locals.init_cons_zero] gen 20 instances 5000

/-- The generated result step `fhW.k_nest_frame_holes` (the two result words) is the identity on
`fhW`'s own results. -/
theorem fhW_kId (n : Nat) (m : Mem) (hi gO gL aO aL : Word) :
    fhW.k_nest_frame_holes (fhW n m hi gO gL aO aL) = fhW n m hi gO gL aO aL := by
  rcases n with _ | n
  · simp [fhW.eq_1, fhW.k_nest_frame_holes]
  rw [fhW.eq_2]; split
  · simp [fhW.k_nest_frame_holes]
  split
  · simp [fhW.k_nest_frame_holes]
  generalize fvinternW _ _ _ = x; rcases x with _ | ⟨v, m1⟩
  · simp [fhW.k_nest_frame_holes, fhW.k_intern_fvar]
  simp only [fhW.k_intern_fvar]; split
  · simp [fhW.k_nest_frame_holes]
  generalize snocW _ _ _ _ _ = y; rcases y with _ | ⟨r, m2⟩
  · simp [fhW.k_nest_frame_holes, fhW.k_sl_snoc]
  simp only [fhW.k_sl_snoc]
  generalize fhW _ _ _ _ _ _ _ = z; rcases z with _ | ⟨r', m3⟩ <;> simp [fhW.k_nest_frame_holes]

section arms
variable (n : Nat) (m m1 : Mem) (hi gO gL aO aL v : Word) (r : List Word)
theorem fhW_nil (h : gL = 0) : fhW (n + 1) m hi gO gL aO aL = some ([aO, aL], m) := fhW.arm1 _ _ _ _ _ _ _ h
theorem fhW_cons (h : ¬ gL = 0) (h1 : ¬ hi + 1 = 0) : fhW (n + 1) m hi gO gL aO aL =
    fhW.k_intern_fvar n hi gO gL aO aL (fvinternW m hi (rdW (m.arr64 IW) (rdW (m.arr64 IW) gO + 1))) :=
  fhW.arm2 _ _ _ _ _ _ _ h h1
theorem fhK1_ok (h : ¬ 4294967296 ≤ v) : fhW.k_intern_fvar n hi gO gL aO aL (some (v, m1)) =
    fhW.k_sl_snoc n hi gO gL (snocW n m1 aO aL v) := fhW.k_intern_fvar.arm1 _ _ _ _ _ _ _ _ h
theorem fhK2_some : fhW.k_sl_snoc n hi gO gL (some (r, m1)) =
    fhW n m1 (hi + 1) (gO + 1) (gL - 1) (r.headD 0) (r.tail.headD 0) := by
  rw [fhW.k_sl_snoc.arm1, fhW_kId]
end arms
attribute [ind_grind] fhW_nil fhW_cons fhK1_ok fhK2_some

end L.Ind

namespace L.Ind

open L.Arena

/-- The twin's holes of a group from `hi` on, one by one. -/
def pos2FhT (hi : Nat) : List (NIdx × EIdx) → AM (List EIdx)
  | [] => pure []
  | x :: g => do
    let v ← internFVarE hi x.2
    let vs ← pos2FhT (hi + 1) g
    pure (v :: vs)

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_cont_new_active`: the group's keys -/

/-- **`nest_cont_new_active` is its model `caW`** (generated). -/
l_model nestContNewActive_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc2 : p.lookup "iw_copy" = some iwCopy) (h4 : p.lookup "rec4" = some rec4)
    (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hp : p.lookup "nest_cont_new_active" = some nestContNewActiveL)
  fns [hp ↦ caW list]
  specs [posRec4_specW p ha h4 n, slSnoc_specW p ha hc2 hsn n]
  grind [arena_grind, ind_grind] finish [rdW_eq, Locals.init_cons_zero] gen 20 instances 5000

/-- The generated result step `caW.k_nest_cont_new_active` is the identity on `caW`'s results. -/
theorem caW_kId (n : Nat) (m : Mem) (us dO dL gO gL aO aL : Word) :
    caW.k_nest_cont_new_active (caW n m us dO dL gO gL aO aL) = caW n m us dO dL gO gL aO aL := by
  rcases n with _ | n
  · simp [caW.eq_1, caW.k_nest_cont_new_active]
  rw [caW.eq_2]; split
  · simp [caW.k_nest_cont_new_active]
  generalize posRecW _ _ = x; rcases x with _ | ⟨k, m1⟩
  · simp [caW.k_nest_cont_new_active, caW.k_rec4]
  simp only [caW.k_rec4]
  generalize snocW _ _ _ _ _ = y; rcases y with _ | ⟨r, m2⟩
  · simp [caW.k_nest_cont_new_active, caW.k_sl_snoc]
  simp only [caW.k_sl_snoc]
  generalize caW _ _ _ _ _ _ _ _ _ = z; rcases z with _ | ⟨r', m3⟩ <;> simp [caW.k_nest_cont_new_active]

section arms
variable (n : Nat) (m m1 : Mem) (us dO dL gO gL aO aL key : Word) (r : List Word)
theorem caW_nil (h : gL = 0) : caW (n + 1) m us dO dL gO gL aO aL = some ([aO, aL], m) :=
  caW.arm1 _ _ _ _ _ _ _ _ _ h
theorem caW_cons (h : ¬ gL = 0) : caW (n + 1) m us dO dL gO gL aO aL =
    caW.k_rec4 n us dO dL gO gL aO aL (posRecW m [rdW (m.arr64 IW) (rdW (m.arr64 IW) gO), us, dO, dL]) :=
  caW.arm2 _ _ _ _ _ _ _ _ _ h
theorem caK1_some : caW.k_rec4 n us dO dL gO gL aO aL (some (key, m1)) =
    caW.k_sl_snoc n us dO dL gO gL (snocW n m1 aO aL key) := caW.k_rec4.arm1 _ _ _ _ _ _ _ _ _ _
theorem caK2_some : caW.k_sl_snoc n us dO dL gO gL (some (r, m1)) =
    caW n m1 us dO dL (gO + 1) (gL - 1) (r.headD 0) (r.tail.headD 0) := by
  rw [caW.k_sl_snoc.arm1, caW_kId]
end arms
attribute [ind_grind] caW_nil caW_cons caK1_some caK2_some

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_cont_params_closed`: the parameters have no local variables -/

l_model nestContParamsClosed_spec (p : Prog) (hb : BvbProg p) (hf : HfF p)
    (hp : p.lookup "nest_cont_params_closed" = some nestContParamsClosedL)
  fns [hp ↦ cpW list]
  specs [bvarBL_spec p hb n, fvbF_spec p hf n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `pin_at` (a copy of lane `decls3`'s model, `DeclBasisSpec.lean`, which this chain does not
import) -/

def pos2PinW (m : Mem) (i : Word) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else if 52 ≤ i then none
  else if i = 51 then some ([rdW (m.arr64 PINS) 71], m) else some ([rdW (m.arr64 PINS) (1 + i)], m)

end L.Ind

end
