module

public import ConAgua.Verdict.IndBTmf
public import ConAgua.Verdict.IndBPins
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.L.ModelGen

@[expose] public section
/-!
# `class_majors`: the model for both outcomes

`clmE` (`l_model … unified`): `intern_const`, `mk_app_n_f` and `sl_cons` lifted (their `Option`
models), `target_major_of` through `tmfE`, `target_major_pins` through `tmpE`, the recursion through
the model. Its refinement is `clm_ref` (`IndT/RecGen19`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model clmE_spec (p : Prog) (P : ClmProg p)
  fns [P.cm ↦ clmE]
  specs [tmfE_spec p P.tmf n, tmpE_spec p P.tmp n, internConst_spec p P.tmp.cf P.tmp.cp P.tmp.ic n,
    mknF_spec p P.tmp.ad n, slCons_specW p P.keys.rx.ha P.keys.copy P.keys.cons n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Ind

end
