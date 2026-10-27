import ConAgua.Arena.IndPosSpec.CtxFields
import ConAgua.Arena.IndPosSpec.GrpAt
import ConAgua.Arena.IndSumSpec7

/-!
# FgW2

`nestBlockOf_specW`, `nboW`, `nfmK`, `nfmW`, `nfmK_some`, `FmLook` and the lemmas only they use.
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
l_model nestBlockOf_specW (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hf : p.lookup "env_find" = some envFindL)
    (hp : p.lookup "nest_block_of" = some nestBlockOfL)
  fns [hp ↦ nboW]
  specs [envFind_specW p hx hg hf n]
  grind [ind_grind] finish [rdW_eq] gen 20

def nfmK (n : Nat) (c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => matesK3 (matesW n m1 c (r.headD 0) (r.tail.headD 0) 0 0)

/-- The model of `nest_frame_mates(vis, c)`. -/
def nfmW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, c => nfmK n c (nboW m vis c)

theorem nfmK_some (n : Nat) (c : Word) (r : List Word) (m1 : Mem) :
    nfmK n c (some (r, m1)) = matesK3 (matesW n m1 c (r.headD 0) (r.tail.headD 0) 0 0) := rfl
attribute [ind_grind] nfmK_some

/-- The lookups of `nest_frame_mates`. -/
structure FmLook (p : Prog) : Prop where
  hc : p.lookup "sl_contains" = some slContains
  ha : p.lookup "iw_alloc" = some iwAlloc
  hcp : p.lookup "iw_copy" = some iwCopy
  hsn : p.lookup "sl_snoc" = some slSnoc
  hgo : p.lookup "nest_frame_mates_go" = some nestFrameMatesGoL
  hx : p.lookup "env_ix" = some envIxL
  hg : p.lookup "env_row_get" = some envRowGetL
  hf : p.lookup "env_find" = some envFindL
  hbo : p.lookup "nest_block_of" = some nestBlockOfL
  hp : p.lookup "nest_frame_mates" = some nestFrameMatesL

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

mutual
def fgW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, hi, us, dO, dL, gO, gL, pO, pL, nO, nL =>
    if gL = 0 then some ([pO, pL, nO, nL], m)
    else fgK1 n hi us dO dL gO gL pO pL nO nL (rdW (m.arr64 IW) (rdW (m.arr64 IW) gO))
      (posRecW m [rdW (m.arr64 IW) (rdW (m.arr64 IW) gO), us, dO, dL])
def fgK1 (n : Nat) (hi us dO dL gO gL pO pL nO nL c : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (key, m1) => fgK2 n hi us dO dL gO gL pO pL nO nL c (posRecW m1 [key, hi])
def fgK2 (n : Nat) (hi us dO dL gO gL pO pL nO nL c : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hole, m2) => fgK3 n hi us dO dL gO gL nO nL c (snocW n m2 pO pL hole)
def fgK3 (n : Nat) (hi us dO dL gO gL nO nL c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => fgK4 n hi us dO dL gO gL (r.headD 0) (r.tail.headD 0) (snocW n m3 nO nL c)
def fgK4 (n : Nat) (hi us dO dL gO gL pO pL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m4) => fgW n m4 hi us dO dL (gO + 1) (gL - 1) pO pL (r.headD 0) (r.tail.headD 0)
end

section arms
variable (n : Nat) (m m1 : Mem) (hi us dO dL gO gL pO pL nO nL c key : Word) (r : List Word)
theorem fgW_nil (h : gL = 0) : fgW (n + 1) m hi us dO dL gO gL pO pL nO nL = some ([pO, pL, nO, nL], m) := by
  simp [fgW, h]
theorem fgW_cons (h : ¬ gL = 0) : fgW (n + 1) m hi us dO dL gO gL pO pL nO nL =
    fgK1 n hi us dO dL gO gL pO pL nO nL (rdW (m.arr64 IW) (rdW (m.arr64 IW) gO))
      (posRecW m [rdW (m.arr64 IW) (rdW (m.arr64 IW) gO), us, dO, dL]) := by simp [fgW, h]
theorem fgK1_some : fgK1 n hi us dO dL gO gL pO pL nO nL c (some (key, m1)) =
    fgK2 n hi us dO dL gO gL pO pL nO nL c (posRecW m1 [key, hi]) := by rw [fgK1]
theorem fgK2_some : fgK2 n hi us dO dL gO gL pO pL nO nL c (some (key, m1)) =
    fgK3 n hi us dO dL gO gL nO nL c (snocW n m1 pO pL key) := by rw [fgK2]
theorem fgK3_some : fgK3 n hi us dO dL gO gL nO nL c (some (r, m1)) =
    fgK4 n hi us dO dL gO gL (r.headD 0) (r.tail.headD 0) (snocW n m1 nO nL c) := by rw [fgK3]
theorem fgK4_some : fgK4 n hi us dO dL gO gL pO pL (some (r, m1)) =
    fgW n m1 hi us dO dL (gO + 1) (gL - 1) pO pL (r.headD 0) (r.tail.headD 0) := by rw [fgK4]
end arms
attribute [ind_grind] fgW_nil fgW_cons fgK1_some fgK2_some fgK3_some fgK4_some

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

mutual
def fhW : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, hi, gO, gL, aO, aL =>
    if gL = 0 then some ([aO, aL], m)
    else if hi + 1 = 0 then none
    else fhK1 n hi gO gL aO aL (fvinternW m hi (rdW (m.arr64 IW) (rdW (m.arr64 IW) gO + 1)))
def fhK1 (n : Nat) (hi gO gL aO aL : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (v, m1) => if 4294967296 ≤ v then none else fhK2 n hi gO gL (snocW n m1 aO aL v)
def fhK2 (n : Nat) (hi gO gL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => fhW n m2 (hi + 1) (gO + 1) (gL - 1) (r.headD 0) (r.tail.headD 0)
end

section arms
variable (n : Nat) (m m1 : Mem) (hi gO gL aO aL v : Word) (r : List Word)
theorem fhW_nil (h : gL = 0) : fhW (n + 1) m hi gO gL aO aL = some ([aO, aL], m) := by simp [fhW, h]
theorem fhW_cons (h : ¬ gL = 0) (h1 : ¬ hi + 1 = 0) : fhW (n + 1) m hi gO gL aO aL =
    fhK1 n hi gO gL aO aL (fvinternW m hi (rdW (m.arr64 IW) (rdW (m.arr64 IW) gO + 1))) := by simp [fhW, h, h1]
theorem fhK1_ok (h : ¬ 4294967296 ≤ v) : fhK1 n hi gO gL aO aL (some (v, m1)) =
    fhK2 n hi gO gL (snocW n m1 aO aL v) := by simp [fhK1, h]
theorem fhK2_some : fhK2 n hi gO gL (some (r, m1)) =
    fhW n m1 (hi + 1) (gO + 1) (gL - 1) (r.headD 0) (r.tail.headD 0) := by rw [fhK2]
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

mutual
def caW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, us, dO, dL, gO, gL, aO, aL =>
    if gL = 0 then some ([aO, aL], m)
    else caK1 n us dO dL gO gL aO aL (posRecW m [rdW (m.arr64 IW) (rdW (m.arr64 IW) gO), us, dO, dL])
def caK1 (n : Nat) (us dO dL gO gL aO aL : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (key, m1) => caK2 n us dO dL gO gL (snocW n m1 aO aL key)
def caK2 (n : Nat) (us dO dL gO gL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => caW n m2 us dO dL (gO + 1) (gL - 1) (r.headD 0) (r.tail.headD 0)
end

section arms
variable (n : Nat) (m m1 : Mem) (us dO dL gO gL aO aL key : Word) (r : List Word)
theorem caW_nil (h : gL = 0) : caW (n + 1) m us dO dL gO gL aO aL = some ([aO, aL], m) := by simp [caW, h]
theorem caW_cons (h : ¬ gL = 0) : caW (n + 1) m us dO dL gO gL aO aL =
    caK1 n us dO dL gO gL aO aL (posRecW m [rdW (m.arr64 IW) (rdW (m.arr64 IW) gO), us, dO, dL]) := by
  simp [caW, h]
theorem caK1_some : caK1 n us dO dL gO gL aO aL (some (key, m1)) = caK2 n us dO dL gO gL (snocW n m1 aO aL key) := by
  rw [caK1]
theorem caK2_some : caK2 n us dO dL gO gL (some (r, m1)) =
    caW n m1 us dO dL (gO + 1) (gL - 1) (r.headD 0) (r.tail.headD 0) := by rw [caK2]
end arms
attribute [ind_grind] caW_nil caW_cons caK1_some caK2_some

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_cont_params_closed`: the parameters have no local variables -/

mutual
def cpW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, hp, dO, dL =>
    if dL = 0 then some ([1], m) else cpK1 n hp dO dL (bvbW n m (rdW (m.arr64 IW) dO) CWF)
def cpK1 (n : Nat) (hp dO dL : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (bb, m1) =>
    if bb ≠ 0 then some ([0], m1) else cpK2 n hp dO dL (fvbF m1 [CWF, rdW (m1.arr64 IW) dO])
def cpK2 (n : Nat) (hp dO dL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => if hp < r.headD 0 then some ([0], m2) else cpW n m2 hp (dO + 1) (dL - 1)
end

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `pin_at` (a copy of lane `decls3`'s model, `DeclBasisSpec.lean`, which this chain does not
import) -/

def pos2PinW (m : Mem) (i : Word) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else if 51 ≤ i then none else some ([rdW (m.arr64 PINS) (1 + i)], m)

/-! ## `nest_cont_checks`: hole-free indices, not `Quot`, parameters without local variables -/

def p2ccK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => if r.headD 0 = 0 then none else some ([0], m2)
def p2ccK1 (k : Nat) (hp nn dO dL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 ≠ 0 then none
    else match pos2PinW m1 47 with
      | none => none
      | some (q, m2) => if nn = q.headD 0 then none else p2ccK2 (cpW k m2 hp dO dL)
end L.Ind

end
