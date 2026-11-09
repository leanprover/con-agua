module

public import ConAgua.Arena.IndT.Tail
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.IndStream

@[expose] public section

/-!
# `check_block_tail_stream` and `stream_k_check`: the unified models (lane `ronsync2`, stage 3)

`check_block_tail_stream(p, fe2b, out.off, out.len)` (`IndInstall.lean`) is `tailStreamT`
(`IndT/Tail`): `stream_k_check` and `stream_recs_check` through their calls, `block_rec_infos_tf`,
`cons_block_recs_temp`, the flushes and `gen_rec_check_pop_all` (outside the verdict closure) lifted.
The refinements (`streamKCheck`, `streamRecsCheck` and its callees in `Arena/IndStream`) are still
to write (handoff in `_tmp/ronsync2/area-ind.md`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of the stream half's models. -/
structure TsLook (p : Prog) : Prop where
  ts : p.lookup "check_block_tail_stream" = some checkBlockTailStream
  skc : p.lookup "stream_k_check" = some streamKCheckL

set_option experimental.vcgen true in
/-- **`stream_k_check`'s unified model**: `rec_k_expected` lifted. -/
l_model skcE_spec (p : Prog) (hP : TsLook p)
  fns [hP.skc ↦ skcE]
  specs [callW_spec p n "rec_k_expected"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **`check_block_tail_stream`'s unified model**: the K flags and the stream's recursors through
their calls, the rest lifted. -/
l_model ctsE_spec (p : Prog) (hP : TsLook p)
  fns [hP.ts ↦ ctsE]
  specs [callW_spec p n "block_rec_infos_tf", callW_spec p n "cons_block_recs_temp",
    callW_spec p n "flush_caches", callW_spec p n "gen_rec_check_pop_all"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


end L.Ind

end
