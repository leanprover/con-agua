module

public import ConAgua.Arena.RecGenSpec.DecCNWords
public import ConAgua.Verdict.IndBRec1
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree

@[expose] public section

/-!
# The generated models of `class_ctor_of`, `class_ctors_of`, `classes_ctors`

The unified models `cxoE`, `cosE`, `ccsE` apart from their refinements (`RecGen27.lean`): they need
the code (`CxoProg`, `CosProg`, `CcsProg`) and `class_minor_slot`'s model, not the refinements
before `RecGen27`, so they build beside that chain instead of on it.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

noncomputable section

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

/-- **`class_ctor_of`'s unified model**: the callees outside the verdict closure lifted,
`class_minor_slot` by its unified model, `class_fields_of` and `class_fields_agree` through their
runs (the ok half reads the calls' array sizes, `callW_keepW`). -/
l_model cxoE_spec (p : Prog) (P : CxoProg p)
  fns [P.cxo ↦ cxoE]
  specs [callW_spec p n "target_major_at", callW_spec p n "class_ctor_of_nfs",
    classMinorSlotE_spec p P.cms n, callW_spec p n "open_pis_at_fvars_f", callW_spec p n "target_ctor_at",
    callW_spec p n "inst_pis_with", callW_spec p n "rec6"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`class_ctors_of`' unified model**: `iw_alloc` lifted, `class_ctor_of` through its run (the
loop's ok half reads the call's array sizes, `callW_keepW`). -/
l_model cosE_spec (p : Prog) (P : CosProg p)
  fns [P.cos ↦ cosE] specs [callW_spec p n "iw_alloc"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`classes_ctors`' unified model**: `iw_alloc` and `rec2` lifted, `class_ctors_of` through its
run (`callW_keepW`). -/
l_model ccsE_spec (p : Prog) (P : CcsProg p)
  fns [P.ccs ↦ ccsE] specs [callW_spec p n "iw_alloc", callW_spec p n "rec2"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Ind
