import ConAgua.Arena.IndPartsSpec.BlockRecNameSetOk
import ConAgua.Arena.IndPartsSpec.BmgW
import ConAgua.Arena.IndPartsSpec.BmoW
import ConAgua.Arena.IndPartsSpec.BpcW
import ConAgua.Arena.IndPartsSpec.BsoK2
import ConAgua.Arena.IndSumSpec.ColW
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# Bsp

`bslW`, `brh_spec`, `brhW`, `brs_spec`, `brsW`, `packMem` and the lemmas only they use.
-/

section


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

/-- **The model of `block_shape_large`.** -/
def bslW (n : Nat) (m : Mem) (cvR0 lo ll : Word) : Option (List Word × Mem) :=
  if rdW (m.arr64 EREC) (cvR0 + 2) = 0 then some ([0, 0], m)
  else match erToIwW n m (rdW (m.arr64 EREC) (cvR0 + 1) + 1) (rdW (m.arr64 EREC) (cvR0 + 2) - 1) with
    | none => none
    | some (rp, m1) =>
      match eqW n m1 (rp.headD 0) (rp.tail.headD 0) lo ll with
      | none => none
      | some e =>
        if e = 0 then some ([0, 0], m1)
        else match containsW n m1 lo ll (rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (cvR0 + 1))) with
          | none => none
          | some hs => if hs ≠ 0 then some ([0, 0], m1)
            else some ([1, rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (cvR0 + 1))], m1)

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`block_shape_rhss_of` is its model `brhW`** (generated). -/
l_model brh_spec (p : Prog) (hP : IndPartsProg4 p)
    (hp : p.lookup "block_shape_rhss_of" = some blockShapeRhssOf)
  fns [hp ↦ brhW]
  specs [slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [ind_grind] finish [rdW_eq] gen 20

/-! ## `block_shape_recs_of` -/

/-- **`block_shape_recs_of` is its model `brsW`** (generated). -/
l_model brs_spec (p : Prog) (hP : IndPartsProg4 p) (h6 : p.lookup "rec6" = some rec6)
    (hr : p.lookup "block_shape_rhss_of" = some blockShapeRhssOf)
    (hp : p.lookup "block_shape_recs_of" = some blockShapeRecsOf)
  fns [hp ↦ brsW]
  specs [recTargetOf_spec p hP.view hP.find hP.target hP.strip hP.ad n, brh_spec p hP hr n,
    rec6_specW p hP.alloc h6 n, slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [ind_grind] finish [rdW_eq] gen 20

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `block_shape_pack` -/

/-- The memory after `block_shape_pack`. -/
def packMem (m : Mem) (a b c d e f g h i : Word) : Mem :=
  let q := rdW (m.arr64 CTL) 200
  (((((((((allocMem m 9).set64 IW q a).set64 IW (q + 1) b).set64 IW (q + 2) c).set64 IW (q + 3) d).set64
    IW (q + 4) e).set64 IW (q + 5) f).set64 IW (q + 6) g).set64 IW (q + 7) h).set64 IW (q + 8) i

theorem packMem_eq (m : Mem) (a b c d e f g h i : Word) :
    packMem m a b c d e f g h i = wrIW (allocMem m 9) (rdW (m.arr64 CTL) 200) [a, b, c, d, e, f, g, h, i] := by
  simp [packMem, wrIW, UInt64.add_assoc]

theorem partsPack_eq (m : Mem) (a b c d e f g h i : Word) :
    (match allocW m 9 with | none => none | some (q, _) => some (q, packMem m a b c d e f g h i)) =
      posRecW m [a, b, c, d, e, f, g, h, i] := by
  rw [posRecW_eq m _ 9 rfl, packMem_eq]; cases allocW m 9 <;> rfl

theorem bsp_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "block_shape_pack" = some blockShapePack) (n : Nat) (s₀ : St)
    (mo ml ro rl nP elim s large isProp : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_shape_pack" [mo, ml, ro, rl, nP, elim, s, large, isProp]
    ⦃fun r s' => LocEq s' s₀ ∧
      posRecW s₀.mem [mo, ml, ro, rl, nP, elim, s, large, isProp] = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [← partsPack_eq, invoke_eq _ hp]
  simp only [callFn, blockShapePack]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish (gen := 20) [packMem, allocMem, allocW]

/-! ## `block_shape_build`: the model -/

/-- **`block_shape_seal` is its model `bsealW`** (generated). -/
l_model bseal_spec (p : Prog) (hna : NaF p) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hpk : p.lookup "block_shape_pack" = some blockShapePack)
    (hp : p.lookup "block_shape_seal" = some blockShapeSeal)
  fns [hp ↦ bsealW list]
  specs [naF_spec p hna n, bsp_spec p ha hpk n]
  grind [ind_grind] simp []

/-- After `block_shape_large`. -/
def bbK13' (mo ml ro2 rl2 nPd s ip : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bgoK3 (bsealW m mo ml ro2 rl2 nPd s ip (r.headD 0) (r.tail.headD 0))

/-- After `block_shape_recs_of`. -/
def bbK12 (n : Nat) (nPd _cto _ctl _cso _csl _rso _rsl _cvT0 cvR0 : Word) (lo ll s ip mo ml : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbK13' mo ml (r.headD 0) (r.tail.headD 0) nPd s ip (bslW n m cvR0 lo ll)

/-- After `block_shape_members_of`. -/
def bbK11 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (no nl lo ll s ip : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbK12 n nPd cto ctl cso csl rso rsl cvT0 cvR0 lo ll s ip (r.headD 0) (r.tail.headD 0) (brsW (n + 1) m no nl rso rsl)

/-- After `block_groups`. -/
def bbK10 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (no nl io lo ll s ip : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbK11 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl lo ll s ip (bmoW (n + 1) m cto ctl io (r.headD 0))

/-- After `param_levels`. -/
def bbK9 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (no nl io lo ll s ip cof cl2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbK10 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip (bgW n m no nl (r.headD 0) nPd ctl cof cl2)

/-- After `block_shape_ctors_of`. -/
def bbK8 (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (no nl io lo ll s ip : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbK9 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip (r.headD 0) (r.tail.headD 0) (plW (n + 1) m lo ll)

section arms
variable (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 cvR0 : Word) (m : Mem) (r : List Word)
  (no nl io lo ll s ip mo ml : Word) (q : Word)
theorem bbK11_some : bbK11 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl lo ll s ip (some (r, m)) =
    bbK12 n nPd cto ctl cso csl rso rsl cvT0 cvR0 lo ll s ip (r.headD 0) (r.tail.headD 0)
      (brsW (n + 1) m no nl rso rsl) := rfl
theorem bbK8_some : bbK8 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip (some (r, m)) =
    bbK9 n nPd cto ctl cso csl rso rsl cvT0 cvR0 no nl io lo ll s ip (r.headD 0) (r.tail.headD 0)
      (plW (n + 1) m lo ll) := rfl
end arms
attribute [ind_grind] bbK11_some bbK8_some

/-- **The model of `block_shape_fin`** (at exec fuel `n + 2`). -/
def bfW (n : Nat) (m : Mem) (nPd cto ctl cso csl rso rsl no nl io lo ll s ip : Word) :
    Option (List Word × Mem) :=
  bbK8 n nPd cto ctl cso csl rso rsl 0 (rdW (m.arr64 IW) (rdW (m.arr64 IW) rso)) no nl io lo ll s ip
    (bctW (n + 1) m cso csl)

/-- After `lvl_eq_c`. -/
def btK3 (_c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl no nl io lo ll s : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bgoK3 (bfW n m nPd cto ctl cso csl rso rsl no nl io lo ll s (if r.headD 0 = 2 then 1 else 0))

/-- After `pin_word(53)`. -/
def btK2 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl no nl io lo ll s : Word) (m : Mem) :
    Option Word → Option (List Word × Mem)
  | none => none
  | some z => btK3 c n nPd cto ctl cso csl rso rsl no nl io lo ll s (c (n + 2) "lvl_eq_c" [s, z] m)

/-- After `block_shape_result_sort`. -/
def btK1 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl no nl io lo ll : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => btK2 c n nPd cto ctl cso csl rso rsl no nl io lo ll (r.headD 0) m (pinWordV m 53)

/-- **The model of `block_shape_tail`** (at exec fuel `n + 3`). -/
def btW (c : CallM) (n : Nat) (m : Mem) (nPd cto ctl cso csl rso rsl no nl io il lo ll : Word) :
    Option (List Word × Mem) :=
  btK1 c n nPd cto ctl cso csl rso rsl no nl io lo ll
    (bsoW m nPd io il (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cto + 3)))

/-- After `block_shape_pins_ok`. -/
def bbH4 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl no nl io il lo ll : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0, 0], m)
    else bgoK3 (btW c n m nPd cto ctl cso csl rso rsl no nl io il lo ll)

/-- After `er_to_iw`. -/
def bbH3 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl no nl io il : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbH4 c n nPd cto ctl cso csl rso rsl no nl io il (r.headD 0) (r.tail.headD 0)
      (bpoW (n + 2) m nPd cto ctl (r.headD 0) (r.tail.headD 0) rso rsl cso csl)

/-- After `block_member_counts`. -/
def bbH2 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 no nl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0, 0], m)
    else bbH3 c n nPd cto ctl cso csl rso rsl no nl (r.tail.headD 0) (r.tail.tail.headD 0)
      (erToIwW (n + 3) m (rdW (m.arr64 EREC) (cvT0 + 1)) (rdW (m.arr64 EREC) (cvT0 + 2)))

/-- After `block_shape_names_of`. -/
def bbH1 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbH2 c n nPd cto ctl cso csl rso rsl cvT0 (r.headD 0) (r.tail.headD 0)
      (bmcW (n + 2) m nPd ctl csl (r.headD 0) (r.tail.headD 0) rso rsl cto ctl)

section arms
variable (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 : Word) (m : Mem) (r : List Word)
  (no nl io il lo ll s z : Word)
theorem btK2_some : btK2 c n nPd cto ctl cso csl rso rsl no nl io lo ll s m (some z) =
    btK3 c n nPd cto ctl cso csl rso rsl no nl io lo ll s (c (n + 2) "lvl_eq_c" [s, z] m) := rfl
theorem bbH4_fail (h : r.headD 0 = 0) : bbH4 c n nPd cto ctl cso csl rso rsl no nl io il lo ll (some (r, m)) =
    some ([0, 0], m) := by simp only [bbH4]; exact ite_eq_left h
theorem bbH4_ok (h : ¬ r.headD 0 = 0) : bbH4 c n nPd cto ctl cso csl rso rsl no nl io il lo ll (some (r, m)) =
    bgoK3 (btW c n m nPd cto ctl cso csl rso rsl no nl io il lo ll) := by simp only [bbH4]; exact ite_eq_right h
theorem bbH3_some : bbH3 c n nPd cto ctl cso csl rso rsl no nl io il (some (r, m)) =
    bbH4 c n nPd cto ctl cso csl rso rsl no nl io il (r.headD 0) (r.tail.headD 0)
      (bpoW (n + 2) m nPd cto ctl (r.headD 0) (r.tail.headD 0) rso rsl cso csl) := rfl
theorem bbH1_some : bbH1 c n nPd cto ctl cso csl rso rsl cvT0 (some (r, m)) =
    bbH2 c n nPd cto ctl cso csl rso rsl cvT0 (r.headD 0) (r.tail.headD 0)
      (bmcW (n + 2) m nPd ctl csl (r.headD 0) (r.tail.headD 0) rso rsl cto ctl) := rfl
end arms
attribute [ind_grind] btK2_some bbH4_fail bbH4_ok bbH3_some bbH1_some

end L.Ind

end

end
