module

public import ConAgua.Verdict.PosE1M
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Checker.NoVerdictTree

@[expose] public section

/-!
# Error models of `nest_cont_new`, `nest_frame`, `nest_grow_group`, `nest_group_ctors` (lane
`verdicts-b`, helper `ia2`, fork `kn2a`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

noncomputable section

l_model nggE_spec (p : Prog) (hn : NitLook p) (h2 : p.lookup "rec2" = some rec2) (h4 : p.lookup "rec4" = some rec4)
    (hsn : p.lookup "sl_snoc" = some slSnoc) (hf : p.lookup "nest_grow_group" = some nestGrowGroupL)
  fns [hf ↦ nggE list]
  specs [posRec4_specW p hn.ty.ha h4 n, nitE_spec p hn n, posRec2_specW p hn.ty.ha h2 n,
    slSnoc_specW p hn.ty.ha hn.hc2 hsn n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model ngcE_spec (p : Prog) (hl : NtLook p) (hc : p.lookup "iw_copy" = some iwCopy)
    (hap : p.lookup "sl_append" = some slAppend) (hp : p.lookup "nest_group_ctors" = some nestGroupCtorsL)
  fns [hp ↦ ngcE list]
  specs [nt_spec' p hl n, slAppend_specW p hl.ha hc hap n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end

l_model nnewE_spec (p : Prog) (hf : p.lookup "nest_cont_new" = some nestContNewL)
  fns [hf ↦ nnewE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified

l_model nfrE_spec (p : Prog) (hf : p.lookup "nest_frame" = some nestFrameL)
  fns [hf ↦ nfrE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified

end L.Ind
