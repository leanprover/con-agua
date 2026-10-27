import ConAgua.Arena.DeclHeader
import ConAgua.Arena.IndPartsSpec.EqW

/-!
# BpcW

`pinK4`, `bpfW`, `bpfK1`, `bpfK2`, `bpfK3`, `bprW` and the lemmas only they use.
-/

set_option linter.unusedSectionVars false

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

/-! ## The pins: models -/

/-- After the recursive call: its answer. -/
def pinK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0], m2)

mutual
/-- **The model of `block_shape_pins_formers`.** -/
def bpfW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, cto, ctl, lo, ll =>
    if ctl = 0 then some ([1], m)
    else bpfK1 n cto ctl lo ll (rdW (m.arr64 IW) cto) m
      (resContW n m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cto)))
/-- After `reserved_contains`. -/
def bpfK1 (n : Nat) (cto ctl lo ll cv : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some b =>
    if b ≠ 0 then some ([0], m)
    else bpfK2 n cto ctl lo ll (erToIwW n m (rdW (m.arr64 EREC) (cv + 1)) (rdW (m.arr64 EREC) (cv + 2)))
/-- After `er_to_iw`. -/
def bpfK2 (n : Nat) (cto ctl lo ll : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rp, m1) => bpfK3 n cto ctl lo ll m1 (eqW n m1 (rp.headD 0) (rp.tail.headD 0) lo ll)
/-- After `sl_eq`. -/
def bpfK3 (n : Nat) (cto ctl lo ll : Word) (m1 : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some e => if e = 0 then some ([0], m1) else pinK4 (bpfW n m1 (cto + 1) (ctl - 1) lo ll)
end

/-- **The model of `block_shape_pins_recs`.** -/
def bprW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, ro, rl =>
    if rl = 0 then some ([1], m)
    else match resContW n m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro))) with
      | none => none
      | some b => if b ≠ 0 then some ([0], m) else pinK4 (bprW n m (ro + 1) (rl - 1))

section arms
variable (n : Nat) (m : Mem) (ro rl : Word)
theorem bprW_nil (h : rl = 0) : bprW (n + 1) m ro rl = some ([1], m) := by simp [bprW, h]
theorem bprW_cons (h : rl ≠ 0) : bprW (n + 1) m ro rl =
    (match resContW n m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro))) with
      | none => none
      | some b => if b ≠ 0 then some ([0], m) else pinK4 (bprW n m (ro + 1) (rl - 1))) := by
  simp only [bprW]; rw [ite_eq_right h]
end arms
attribute [ind_grind] bprW_nil bprW_cons

mutual
/-- **The model of `block_shape_pins_ctors`.** -/
def bpcW : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, nP, cso, csl, lo, ll =>
    if csl = 0 then some ([1], m)
    else if rdW (m.arr64 IW) (rdW (m.arr64 IW) cso + 1) ≠ nP then some ([0], m)
    else bpcK1 n nP cso csl lo ll (rdW (m.arr64 IW) (rdW (m.arr64 IW) cso)) m
      (resContW n m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) cso))))
/-- After `reserved_contains`. -/
def bpcK1 (n : Nat) (nP cso csl lo ll cv : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some b =>
    if b ≠ 0 then some ([0], m)
    else bpcK2 n nP cso csl lo ll (erToIwW n m (rdW (m.arr64 EREC) (cv + 1)) (rdW (m.arr64 EREC) (cv + 2)))
/-- After `er_to_iw`. -/
def bpcK2 (n : Nat) (nP cso csl lo ll : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rp, m1) => bpcK3 n nP cso csl lo ll m1 (eqW n m1 (rp.headD 0) (rp.tail.headD 0) lo ll)
/-- After `sl_eq`. -/
def bpcK3 (n : Nat) (nP cso csl lo ll : Word) (m1 : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some e => if e = 0 then some ([0], m1) else pinK4 (bpcW n m1 nP (cso + 1) (csl - 1) lo ll)
end

/-! ## `block_shape_pins_ok` -/

/-- **The model of `block_shape_pins_ok`** (at exec fuel `n + 1`). -/
def bpoW (n : Nat) (m : Mem) (nP cto ctl lo ll ro rl cso csl : Word) : Option (List Word × Mem) :=
  match bpfW n m cto ctl lo ll with
  | none => none
  | some (ra, m1) =>
    if ra.headD 0 = 0 then some ([0], m1)
    else match bprW n m1 ro rl with
      | none => none
      | some (rb, m2) =>
        if rb.headD 0 = 0 then some ([0], m2)
        else match bpcW n m2 nP cso csl lo ll with
          | none => none
          | some (rc, m3) => some ([rc.headD 0], m3)

end L.Ind

end
