import ConAgua.Arena.IndPos2SpecN

/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the L side — every
function of the block refines its word model, by one induction on the exec fuel. -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of the `nestPos` block (and its leaves). -/
structure NbLook (p : Prog) : Prop where
  ct : CtLook p
  nit : NitLook p
  nag : NagLook p
  dc : DcLook p
  fm : FmLook p
  nt : NtLook p
  pf : PfLook p
  usl : UslLook p
  h3 : p.lookup "rec3" = some rec3
  h6 : p.lookup "rec6" = some rec6
  hap : p.lookup "sl_append" = some slAppend
  hn1 : p.lookup "sl_new1" = some slNew1
  hfg : p.lookup "nest_frame_grp" = some nestFrameGrpL
  hgc : p.lookup "nest_group_ctors" = some nestGroupCtorsL
  hfh : p.lookup "nest_frame_holes" = some nestFrameHolesL
  hgg : p.lookup "nest_grow_group" = some nestGrowGroupL
  hca : p.lookup "nest_cont_new_active" = some nestContNewActiveL
  hcf : p.lookup "nest_cont_new_finish" = some nestContNewFinishL
  hpc : p.lookup "nest_cont_params_closed" = some nestContParamsClosedL
  hcc : p.lookup "nest_cont_checks" = some nestContChecksL
  hpa : p.lookup "pin_at" = some pinAtL
  hws : p.lookup "nest_walk_stack" = some nestWalkStackL
  hrh : p.lookup "nest_res_head" = some nestResHeadL
  hro : p.lookup "nest_ctors_res_ok" = some nestCtorsResOkL
  hu4 : p.lookup "nest_ctors_u4" = some nestCtorsU4L
  hnf : p.lookup "nest_ctor_nf" = some nestCtorNfL
  hcl : p.lookup "close_telescope" = some closeTelescope
  hdf : p.lookup "dp_find" = some (memoFindG dpSch)
  hdp : p.lookup "dp_put" = some (memoPutG dpSch)
  hdg : p.lookup "depth_go" = some depthGo
  hdn : p.lookup "depth_node" = some depthNode
  hdc : p.lookup "dp_clear" = some (memoClearG dpSch)
  hdd : p.lookup "depth" = some depth
  hwf : p.lookup "whnf_walk_fuel" = some whnfWalkFuel
  pfields : p.lookup "nest_fields" = some nestFieldsL
  pwalk : p.lookup "nest_ctors_walk" = some nestCtorsWalkL
  pone : p.lookup "nest_ctors_one" = some nestCtorsOneL
  pctors : p.lookup "nest_ctors" = some nestCtorsL
  pframe : p.lookup "nest_frame" = some nestFrameL
  pnew : p.lookup "nest_cont_new" = some nestContNewL
  pkey : p.lookup "nest_cont_key" = some nestContKeyL
  pcont : p.lookup "nest_cont" = some nestContL
  papp : p.lookup "nest_pos_app" = some nestPosAppL
  pbind : p.lookup "nest_pos_bind" = some nestPosBindL
  ppos : p.lookup "nest_pos" = some nestPosL

section spec
variable (p : Prog)

/-- The specs of the block at exec fuel `n`. -/
def NbSpec (n : Nat) : Prop :=
  (∀ (s₀ : St) (vis ctx fu po pl dep kb e ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_pos" [vis, ctx, fu, po, pl, dep, kb, e, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbPosW n s₀.mem vis ctx fu po pl dep kb e ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl dep kb w ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_pos_bind" [vis, ctx, fu, po, pl, dep, kb, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbBindW n s₀.mem vis ctx fu po pl dep kb w ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl kb hi w ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_pos_app" [vis, ctx, fu, po, pl, kb, hi, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbAppW n s₀.mem vis ctx fu po pl kb hi w ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl kb nn us aO aL ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_cont" [vis, ctx, fu, po, pl, kb, nn, us, aO, aL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbContW n s₀.mem vis ctx fu po pl kb nn us aO aL ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_cont_key" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbKeyW n s₀.mem vis ctx fu po pl kb nn us dO dL nPc cty ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_cont_new" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbNewW n s₀.mem vis ctx fu po pl kb nn us dO dL nPc cty ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_frame" [vis, ctx, fu, po, pl, hi, us, dO, dL, nPc, gO, gL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbFrameW n s₀.mem vis ctx fu po pl hi us dO dL nPc gO gL ns =
      some ([r.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_ctors" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cO, cL, ns,
      oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧ nbCtorsW n s₀.mem vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_ctors_one" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cv, nF, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbOneW n s₀.mem vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx root fu po pl hi nF crest ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_ctors_walk" [vis, ctx, root, fu, po, pl, hi, nF, crest, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbWalkW n s₀.mem vis ctx root fu po pl hi nF crest ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
        r.tail.tail.tail.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl base nF j cur ns kO kL dO dL : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_fields" [vis, ctx, fu, po, pl, base, nF, j, cur, ns, kO, kL, dO, dL]
    ⦃fun r s' => LocEq s' s₀ ∧ nbFieldsW n s₀.mem vis ctx fu po pl base nF j cur ns kO kL dO dL =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
        r.tail.tail.tail.tail.headD 0, r.tail.tail.tail.tail.tail.headD 0], s'.mem); ⊤⦄)

variable {p} (L : NbLook p) (n : Nat) (ih : NbSpec p n)
include L ih

theorem nbFields_step (s₀ : St) (vis ctx fu po pl base nF j cur ns kO kL dO dL : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_fields" [vis, ctx, fu, po, pl, base, nF, j, cur, ns, kO,
      kL, dO, dL]
    ⦃fun r s' => LocEq s' s₀ ∧ nbFieldsW (n + 1) s₀.mem vis ctx fu po pl base nF j cur ns kO kL dO dL =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
        r.tail.tail.tail.tail.headD 0, r.tail.tail.tail.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, -, -, -, -, -, -, -, -, -, hFields⟩ := ih
  have R := L.ct.cr.rx
  rw [invoke_eq _ L.pfields]
  simp only [callFn, nestFieldsL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p R.hl.hv n, hPos, internFVar_spec p R.hl.hff R.hl.hfp R.hl.hif n,
      stubM_spec p "instantiate1_fast" n, slSnoc_specW p R.ha L.nit.hc2 L.nag.hsn n, hFields] <;>
    simp_all [nbFieldsW_succ, nbFieldsK1_some, nbFieldsK2_some, nbFieldsK3_some, nbFieldsK4_some,
      nbFieldsK5_some, LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW_eq]

end spec

end L.Ind
