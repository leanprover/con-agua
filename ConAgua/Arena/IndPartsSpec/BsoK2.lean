import ConAgua.Arena.IndPosSpec.MatesW
import ConAgua.Arena.StripTeleSpec

/-!
# BsoK2

`bsoK2`, `bsoK1`, `bsoW`, `bsoTwin`.
-/

noncomputable section

set_option experimental.vcgen true

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
  else bsoK1 (stripF 6 m [nP + getDW m io il 0 0, ty])

/-- The twin's result sort (`blockShape?`'s first `let s`). -/
def bsoTwin (nP : Nat) (nIdxs : List Nat) (ty : EIdx) : AM LIdx := do
  match ← stripPis (nP + nIdxs.headD 0) ty with
  | some q => do
    match ← view q.2 with
    | .sort s => pure s
    | _ => zeroLevel
  | none => zeroLevel

end L.Ind

end
