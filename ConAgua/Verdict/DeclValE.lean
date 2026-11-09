module

import ConAgua.Arena.DeclCvgT
public import ConAgua.Arena.CrOKFrame
import ConAgua.Arena.IndRealMemoCrT
public import ConAgua.Arena.IndRealApdT
public import ConAgua.Arena.DeclValSpec
import ConAgua.Arena.DeclValT
import ConAgua.Arena.DeclStepSpec
public import ConAgua.Verdict.LefRef
public import ConAgua.Verdict.VCtx
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclValRef
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPartsSpec.MemberNames
import ConAgua.Arena.IndRealLvlT
import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.LvlGrow
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Core.Walks.Cached
public import ConAgua.Arena.KnotEntry
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.DeclStep

@[expose] public section

/-!
# The model of `check_thm_val` (lane `verdicts-b`)

The unified model of `check_thm_val` (`checkThmVal_specE`); its refinement for both outcomes is
`checkThmVal_ref` (`DeclValsE.lean`). (`install_value_guards`, `check_value_group` and their
claims are gone with the old twin's fold.)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

noncomputable section

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-! ## `check_thm_val(vis, c)` -/

/-- **The model of `check_thm_val`, both outcomes**: `pin_word`, `env_push` (outside the verdict
closure) through their `Option` models; the core stubs and `lvl_eq_fueled`
through their runs. -/
l_model checkThmVal_specE (p : Prog) (hV : ValProg p)
  fns [hV.tv ↦ checkThmValE]
  specs [pinWord_specW p hV.cvg.pin n, callW_spec p n "env_push"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
