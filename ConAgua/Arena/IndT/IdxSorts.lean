module

import ConRon.Bridge.Inductives.SumInstall
import ConAgua.Arena.IndT.Sum3
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndT.Install1
import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndRealAbsSim
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RecClassSpec.PiBWRoom
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.IndInstallSpec.GrcProg
public import ConAgua.Arena.KnotEntry
public import ConAgua.Verdict.VCtx
public import ConRon.Bridge.Checker.Hyp
import all ConAgua.Arena.IndInstall

@[expose] public section

/-!
# `check_block_idx_sorts`: one model and one refinement for both outcomes

`iisE` (`check_block_idx_sorts_one`) and `iisrE` (`check_block_idx_sorts`), `l_model … unified`:
`open_pis_at_fvars_f`, `rec2` and `sl_cons` (outside the verdict closure) through their `Option`
models, `check_struct_field_sorts_i` through its run (`callE`; `RefE.bindRun` with its spec and
`fsorts_ref`), the member check
through its unified model. `iis_ref` and `iisr_ref` refine `idxOneAM` and `checkBlockIdxSorts`
for both outcomes; `checkBlockIdxSorts_refinesC` is the ok half.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_block_idx_sorts`' unified model**: `open_pis_at_fvars_f` through its `Option` model,
`check_struct_field_sorts_i` through its run (`callE`), the recursion. -/
l_model iisE_spec (p : Prog) (hP : IdxProg p) (hOpf : OpfF p)
  fns [hP.idx ↦ iisE]
  specs [opfF_spec p hOpf n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Ind

end
