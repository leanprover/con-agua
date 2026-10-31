module

public import ConAgua.Arena.RecGen
public import ConAgua.Arena.Verdict
public import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.L.ModelGen

@[expose] public section

/-!
# The unified model of `gen_rec_check_prep`

Generated alone: the function has thirteen callees and the record's fourteen writes. The callees
outside the verdict closure are lifted; the five checks (`target_rec_pins`, `class_stream_recs`,
`classes_nfs`, `classes_ctors`, `class_rec_tys_ok`) are read through their runs (the ok half reads
the calls' walk memos and array sizes).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

noncomputable section

namespace L.Ind

open L.Arena

l_model grpE_spec (p : Prog) (hf : p.lookup "gen_rec_check_prep" = some genRecCheckPrep)
  fns [hf ↦ grpE]
  specs [callW_spec p n "block_large_elim_allowed", callW_spec p n "class_gen_prefix_binders",
    callW_spec p n "gen_rec_check_any_no_member", callW_spec p n "gen_rec_check_former_tys",
    callW_spec p n "gen_rec_check_former_tys_c", callW_spec p n "gen_rec_check_minor_ok",
    callW_spec p n "iw_alloc", callW_spec p n "struct_elim_level"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 20000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Ind

end
