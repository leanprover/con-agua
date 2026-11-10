module

public import ConAgua.Arena.IndPartsSpec.IndPartsProg2
public import ConAgua.Arena.IndGrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndParts

@[expose] public section

/-!
# BmoW

`bsnW`, `bsnW_nil`, `bsnW_cons`, `bsnK_some` and the lemmas only they use; the generated `bctW` and `bmoW`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The models -/

/-- **The model of `block_shape_names_of`.** -/
def bsnW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, cto, ctl =>
    if ctl = 0 then some ([0, 0], m)
    else bsnK n cto (bsnW n m (cto + 1) (ctl - 1))
where
  /-- After the recursive call. -/
  bsnK (n : Nat) (cto : Word) : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (r, m1) => bgoK3 (consW n m1 (erRd m1 (rdW (m1.arr64 IW) cto)) (r.headD 0)
        (r.tail.headD 0))

section arms
variable (n : Nat) (m m1 : Mem) (cto ctl cso csl io go ro rl c : Word) (r : List Word)
theorem bsnW_nil (h : ctl = 0) : bsnW (n + 1) m cto ctl = some ([0, 0], m) := by simp [bsnW, h]
theorem bsnW_cons (h : ctl ≠ 0) : bsnW (n + 1) m cto ctl = bsnW.bsnK n cto (bsnW n m (cto + 1) (ctl - 1)) := by
  simp [bsnW, h]
theorem bsnK_some : bsnW.bsnK n cto (some (r, m1)) = bgoK3 (consW n m1
    (erRd m1 (rdW (m1.arr64 IW) cto)) (r.headD 0) (r.tail.headD 0)) := rfl
end arms
attribute [ind_grind] bsnW_nil bsnW_cons bsnK_some

/-- **`block_shape_ctors_of` is its model `bctW`** (generated). -/
l_model bct_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hcons : p.lookup "sl_cons" = some slCons)
    (h2 : p.lookup "rec2" = some rec2) (hp : p.lookup "block_shape_ctors_of" = some blockShapeCtorsOf)
  fns [hp ↦ bctW list]
  specs [posRec2_specW p ha h2 n, slCons_specW p ha hc hcons n]
  grind [arena_grind, ind_grind] finish [rdW_eq]

/-- **`block_shape_members_of` is its model `bmoW`** (generated). -/
l_model bmo_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hcons : p.lookup "sl_cons" = some slCons)
    (h5 : p.lookup "rec5" = some rec5) (hp : p.lookup "block_shape_members_of" = some blockShapeMembersOf)
  fns [hp ↦ bmoW list]
  specs [posRec5_specW p ha h5 n, slCons_specW p ha hc hcons n]
  grind [arena_grind, ind_grind] finish [rdW_eq]

end L.Ind

end
