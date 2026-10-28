import ConAgua.Arena.RecCheckSpec.TcmF

/-!
# K53Look

`K53Look`, the lookups of `target_k53`.
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

/-- The lookups of `target_k53`. -/
structure K53Look (p : Prog) : Prop where
  tmn : TmnLook p
  hv : p.lookup "e_view" = some eView
  ad : AdF p
  sc : p.lookup "sl_contains" = some slContains
  nf : p.lookup "no_find" = some (memoFindG noSch)
  np : p.lookup "no_put" = some (memoPutG noSch)
  ngo : p.lookup "nest_occ_go" = some nestOccGo
  nnode : p.lookup "nest_occ_node" = some nestOccNode
  ncl : p.lookup "no_clear" = some (memoClearG noSch)
  no : p.lookup "nest_occ" = some nestOcc
  cf : p.lookup "const_find" = some constFind
  cp : p.lookup "const_push" = some constPush
  ic : p.lookup "intern_const" = some internConst
  eq : p.lookup "sl_eq" = some slEq
  ee : p.lookup "erase_each" = some eraseEach
  tte : p.lookup "target_k53_tele" = some targetK53Tele
  tkh : p.lookup "target_k53_heads" = some targetK53Heads
  tka : p.lookup "target_k53_args" = some targetK53Args
  tk : p.lookup "target_k53" = some targetK53
  strip : StripProg p

end L.Ind

end
end
