module

public import ConAgua.Arena.IndPosSpec.NestOccGo
public import ConAgua.Arena.IndPartsSpec.EqW

@[expose] public section

/-!
# EeK2

`noF`.
-/

noncomputable section

/-!
# `RecCheck`: `targetK53`, the L side (lane `indproofs3`, helper `rec`)

K.53′ at one recorded field: `strip_pis` (stub), the telescope check (`target_k53_tele`: both sides
erased by `erase_each`, compared by `sl_eq`), the head check (`target_k53_heads`: `get_app_fn_f`,
`get_app_args_f` stubs, `e_view`), the argument check (`target_k53_args`: erased indices, the
leaf's class `intern_const` + `mk_app_n_f` (stub) + `nest_occ`, then `target_class_match`).
L: `erase_each` is the twin's `mapM` as a self-recursion consing each result (`sl_cons`, D18); a
handle guard after `intern_const` (`mk_app_n_f`'s contract takes a handle).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

def noF : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, lo, hi, e => noConstW n m no nl lo hi e

end L.Ind

end
end
