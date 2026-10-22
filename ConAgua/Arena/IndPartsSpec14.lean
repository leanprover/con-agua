import ConAgua.Arena.IndPartsSpec13

/-!
# Refinements of `IndParts`, part 14 (lane `indproofs2`, helper `parts`): `blockShape?`

The result sort (`block_shape_result_sort`, through `strip_pis`; `nP + nIdx` wrapping is a capacity
abort), the record (`block_shape_pack`), `block_shape_build` composing every piece, `block_shape`,
`block_parts`.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `block_shape_result_sort` -/

/-- After `e_view`: the sort's level, else `zeroLevel`. -/
def bsoK2 (m1 : Mem) (v : List Word) : Option (List Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 2 then some ([v.getD 1 0], m1)
  else match pinWordV m1 53 with
    | none => none
    | some z => some ([z], m1)

/-- After `strip_pis`. -/
def bsoK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then (match pinWordV m1 53 with
      | none => none
      | some z => some ([z], m1))
    else bsoK2 m1 (eViewW m1 (r1.tail.tail.tail.headD 0))

/-- **The model of `block_shape_result_sort`.** -/
def bsoW (m : Mem) (nP io il ty : Word) : Option (List Word × Mem) :=
  if nP + getDW m io il 0 0 < nP then none
  else bsoK1 (stubM "strip_pis" m [nP + getDW m io il 0 0, ty])

theorem bso_spec (p : Prog) (hv : p.lookup "e_view" = some eView) (hpw : p.lookup "pin_word" = some pinWordL)
    (hg : p.lookup "sl_getd" = some slGetD)
    (hp : p.lookup "block_shape_result_sort" = some blockShapeResultSort) (n : Nat) (s₀ : St)
    (nP io il ty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_shape_result_sort" [nP, io, il, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ bsoW s₀.mem nP io il ty = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeResultSort]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, slGetD_specW p hg n,
      stubM_spec p "strip_pis" n, eViewSpec4 p hv n, pinWord_specV p hpw n] <;>
    finish (gen := 20) [bsoW, bsoK1, bsoK2]

end L.Ind
