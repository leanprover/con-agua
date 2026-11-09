module

public import ConAgua.Arena.IndT.StreamRecsTop
public import ConAgua.Arena.IndT.SumSteps
import ConAgua.Arena.DefEqMidPeel
import ConAgua.Arena.IndPartsSpec.RecTW
import ConAgua.Arena.IndPosSpec.RootHoles
import ConAgua.Arena.LiftRefine
import ConAgua.Arena.RecCheckSpec.ArfW
import ConAgua.Arena.IndSumSpec.TsrW
import ConAgua.Arena.IndRealMemo
import ConAgua.Arena.StageInst1
import ConAgua.L.ModelGen
import ConRon.Bridge.Inductives.StreamRecs
import all ConAgua.Arena.IndStream

@[expose] public section

/-!
# `stream_nested_ok` under `StageC` (lane `ronsync2`, stage 3)

`stream_nested_ok(ty, mI, rP, kind, lvls, pins)` (`IndStream.lean`) and its helpers
`stream_nested_dom`, `stream_nested_pins`, `stream_nested_bvars`: their models (`snoW`, `sndW`,
`snpW`, `snbW`, callees through their runs `callW`), the callees' steps under the stage relation
(`StageR`, `AbsOK`, the `IW` growth), the helpers' sims against con-ron's `streamNestedDom` and
its two `mapM`s, and `snoSim_of : SnoProg p → SnoSim p dn`, the obligation `sr1_ref` takes (the
twin's step from con-ron's `streamNestedOk_run`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

/-- The lookups `stream_nested_ok` needs. -/
structure SnoProg (p : Prog) : Prop where
  ok : p.lookup "stream_nested_ok" = some streamNestedOkL
  dom : p.lookup "stream_nested_dom" = some streamNestedDomL
  pins : p.lookup "stream_nested_pins" = some streamNestedPins
  bvars : p.lookup "stream_nested_bvars" = some streamNestedBvars
  ev : p.lookup "e_view" = some eView
  ln : p.lookup "ls_node" = some lsNode
  pc : p.lookup "pool_copy" = some poolCopy
  vl : p.lookup "view_ls" = some viewLsL
  app : p.lookup "sl_append" = some slAppend
  le : p.lookup "lift_entry" = some liftEntry
  lift : LiftProg p
  sum : SumProg p

l_model snpW_spec (p : Prog) (h : SnoProg p)
  fns [h.pins ↦ snpW]
  specs [callW_spec p n "lift_entry", callW_spec p n "sl_cons"]
  grind [arena_grind] extra [ld64_rd_spec]

l_model snbW_spec (p : Prog) (h : SnoProg p)
  fns [h.bvars ↦ snbW]
  specs [callW_spec p n "intern_bvar", callW_spec p n "sl_cons"]
  grind [arena_grind]

l_model sndW_spec (p : Prog) (h : SnoProg p)
  fns [h.dom ↦ sndW]
  specs [callW_spec p n "get_app_fn_f", callW_spec p n "e_view", callW_spec p n "view_ls",
    callW_spec p n "sl_eq", callW_spec p n "get_app_args_f", callW_spec p n "stream_nested_pins",
    callW_spec p n "stream_nested_bvars", callW_spec p n "sl_append"]
  grind [arena_grind] extra [evalE_tagE]

l_model snoW_spec (p : Prog) (h : SnoProg p)
  fns [h.ok ↦ snoW]
  specs [callW_spec p n "strip_pis", callW_spec p n "e_view", callW_spec p n "stream_nested_dom"]
  grind [arena_grind] extra [evalE_tagE]

end L.Ind

end
