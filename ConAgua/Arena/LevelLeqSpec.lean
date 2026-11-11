module

meta import ConAgua.L.Semantics
public import ConAgua.Arena.LevelLeq
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.LevelLeq

@[expose] public section

/-!
# The specs of the comparison: `lv_leq`, `lv_rest`, `lv_imax`, `lv_imax_l`, `lv_imax_r`, `lv_cases`,
`lv_cases_at`

Generated (`l_model … nodefs`; the models are `LevelLeq.lean`'s `defs` run of the same command):
one step per function and the induction on the L fuel (`leqSpecs`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **The seven functions are their models**, at every fuel. -/
l_model leqSpecs (p : Prog) (hp : LevelProg p)
  fns [hp.leq ↦ leqW, hp.rest ↦ restW, hp.imax ↦ imaxRW, hp.imaxL ↦ imaxLW, hp.imaxR ↦ imaxRrW,
    hp.cases ↦ casesW, hp.casesAt ↦ caW]
  specs [lvNode_spec p hp.node n, lvEq_spec p hp.node hp.eq n, lhMk_spec p hp.alloc n,
    lvDist1_spec p hp.alloc hp.dist1 n, lvDist2_spec p hp.node hp.alloc hp.comb hp.simp hp.dist2 n,
    lvSubsimp_spec p hp.node hp.alloc hp.comb hp.simp hp.subst hp.subsimp n]
  grind [level_grind] fold [lvG, lvA, lvB] gen 20 noguard ["lv_node"] nodefs

end L.Arena
