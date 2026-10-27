import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.IndGrindAttr

/-!
# BmoW

`bsnW`, `bctW`, `bmoW`, `bsnW_nil`, `bsnW_cons`, `bsnK_some` and the lemmas only they use.
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
    | some (r, m1) => bgoK3 (consW n m1 (rdW (m1.arr64 EREC) (rdW (m1.arr64 IW) cto)) (r.headD 0)
        (r.tail.headD 0))

/-- **The model of `block_shape_ctors_of`.** -/
def bctW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, cso, csl =>
    if csl = 0 then some ([0, 0], m)
    else bctK n (rdW (m.arr64 IW) cso) (bctW n m (cso + 1) (csl - 1))
where
  /-- After the recursive call: the `[cv, nF]` record, consed on. -/
  bctK (n : Nat) (c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (r, m1) =>
      match posRecW m1 [rdW (m1.arr64 IW) c, rdW (m1.arr64 IW) (c + 2)] with
      | none => none
      | some (e, m2) => bgoK3 (consW n m2 e (r.headD 0) (r.tail.headD 0))

/-- **The model of `block_shape_members_of`.** -/
def bmoW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, cto, ctl, io, go =>
    if ctl = 0 then some ([0, 0], m)
    else bmoK n cto io go (bmoW n m (cto + 1) (ctl - 1) (io + 1) (go + 1))
where
  /-- After the recursive call: the member record, consed on. -/
  bmoK (n : Nat) (cto io go : Word) : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (r, m1) =>
      match posRecW m1 [rdW (m1.arr64 IW) cto, rdW (m1.arr64 IW) io,
          rdW (m1.arr64 IW) (rdW (m1.arr64 IW) go), rdW (m1.arr64 IW) (rdW (m1.arr64 IW) go + 1)] with
      | none => none
      | some (e, m2) => bgoK3 (consW n m2 e (r.headD 0) (r.tail.headD 0))

section arms
variable (n : Nat) (m m1 : Mem) (cto ctl cso csl io go ro rl c : Word) (r : List Word)
theorem bsnW_nil (h : ctl = 0) : bsnW (n + 1) m cto ctl = some ([0, 0], m) := by simp [bsnW, h]
theorem bsnW_cons (h : ctl ≠ 0) : bsnW (n + 1) m cto ctl = bsnW.bsnK n cto (bsnW n m (cto + 1) (ctl - 1)) := by
  simp [bsnW, h]
theorem bsnK_some : bsnW.bsnK n cto (some (r, m1)) = bgoK3 (consW n m1
    (rdW (m1.arr64 EREC) (rdW (m1.arr64 IW) cto)) (r.headD 0) (r.tail.headD 0)) := rfl
theorem bctW_nil (h : csl = 0) : bctW (n + 1) m cso csl = some ([0, 0], m) := by simp [bctW, h]
theorem bctW_cons (h : csl ≠ 0) : bctW (n + 1) m cso csl =
    bctW.bctK n (rdW (m.arr64 IW) cso) (bctW n m (cso + 1) (csl - 1)) := by simp [bctW, h]
theorem bctK_some : bctW.bctK n c (some (r, m1)) =
    (match posRecW m1 [rdW (m1.arr64 IW) c, rdW (m1.arr64 IW) (c + 2)] with
      | none => none
      | some (e, m2) => bgoK3 (consW n m2 e (r.headD 0) (r.tail.headD 0))) := rfl
theorem bmoW_nil (h : ctl = 0) : bmoW (n + 1) m cto ctl io go = some ([0, 0], m) := by simp [bmoW, h]
theorem bmoW_cons (h : ctl ≠ 0) : bmoW (n + 1) m cto ctl io go =
    bmoW.bmoK n cto io go (bmoW n m (cto + 1) (ctl - 1) (io + 1) (go + 1)) := by simp [bmoW, h]
theorem bmoK_some : bmoW.bmoK n cto io go (some (r, m1)) =
    (match posRecW m1 [rdW (m1.arr64 IW) cto, rdW (m1.arr64 IW) io,
          rdW (m1.arr64 IW) (rdW (m1.arr64 IW) go), rdW (m1.arr64 IW) (rdW (m1.arr64 IW) go + 1)] with
      | none => none
      | some (e, m2) => bgoK3 (consW n m2 e (r.headD 0) (r.tail.headD 0))) := rfl
end arms
attribute [ind_grind] bsnW_nil bsnW_cons bsnK_some bctW_nil bctW_cons bctK_some bmoW_nil bmoW_cons
  bmoK_some

end L.Ind

end
