module

import ConAgua.Arena.Verdict
public import ConAgua.Arena.WhnfIotaRec
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import ConAgua.Checker.NoVerdictFns
public import ConAgua.L.ErrSpec
import all ConAgua.Arena.WhnfIotaRec

@[expose] public section

/-!
# The generated models of `WhnfIotaRecRefine.lean`

Generated `unified` models only (and `iota_rec_vck`'s index length word `ixLen` they fold), apart
from their refinements (`WhnfIotaRecRefine.lean`): they need the code and their callees' runs, not the
refinements before it, so they build beside that chain.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **`iota_rec_cmp`'s model, both outcomes** (generated; `defeq_list` through its run: the record
pool's frame, `callW_iotaRecCmp_erec`, needs it). -/
l_model irCmpE_spec (p : Prog) (hf : p.lookup "iota_rec_cmp" = some iotaRecCmpL)
  fns [hf ↦ irCmpE list]
  specs [callW_spec p n "erec_push", callW_spec p n "rec_fire_args", callW_spec p n "stack_cover"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- The index slice's length word of `iota_rec_vck`. -/
def ixLen (mI rP : Word) : Word := (mI - rP) * Cmp.ule.evalW rP mI

/-- **`iota_rec_vck`'s model, both outcomes** (generated; `iota_rec_cmp`, `iota_certs_full` and
`iota_index_ok` through their runs, `lvls_eq_c` and `const_ty_at` lifted). -/
l_model vckE_spec (p : Prog) (hp : p.lookup "iota_rec_vck" = some iotaRecVckL)
  fns [hp ↦ vckE list]
  specs [callW_spec p n "lvls_eq_c", callW_spec p n "const_ty_at"]
  grind [arena_grind] fold [ixLen] extra [ld64_rdW_specE, ld64_rdW_specT] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
