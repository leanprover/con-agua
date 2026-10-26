import ConAgua.Arena.IndPos2SpecN
set_option linter.unusedSectionVars false

/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the L side — every
function of the block refines its word model, by one induction on the exec fuel. -/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of the `nestPos` block (and its leaves). -/
structure NbLook (p : Prog) : Prop where
  hi1 : I1Prog p
  ab : AbF p
  na : NaF p
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



theorem posRec3_eq (m : Mem) (a b c : Word) :
    (match allocW m 3 with | none => none | some (q, _) => some (q, rec3Mem m a b c)) =
      posRecW m [a, b, c] := by
  rw [posRecW_eq m [a, b, c] 3 rfl]
  cases allocW m 3 with
  | none => rfl
  | some pr =>
    simp only [rec3Mem, wrIW]
    rw [show rdW (m.arr64 CTL) 200 + 1 + 1 = rdW (m.arr64 CTL) 200 + 2 by
      rw [UInt64.add_assoc]; rfl]

theorem posRec3_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (h3 : p.lookup "rec3" = some rec3)
    (n : Nat) (s₀ : St) (a b c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec3" [a, b, c]
    ⦃fun r s' => LocEq s' s₀ ∧ posRecW s₀.mem [a, b, c] = some (r.headD 0, s'.mem); ⊤⦄ := by
  simp only [← posRec3_eq, invoke_eq _ h3, callFn, rec3]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [rec3Mem, allocMem, allocW]

theorem pos2_getElem_getD (a : Array Word) (i : Nat) (h : i < a.size) : a[i] = a[i]?.getD 0 := by
  simp [h]

/-! ## Leaf callees at any exec fuel -/

theorem whnfWalkFuel_spec' (p : Prog) (L : NbLook p) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "whnf_walk_fuel" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ wfWf n s₀.mem e = some ([r.headD 0], s'.mem); ⊤⦄ := by
  match n with
  | 0 => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | 1 =>
    rw [invoke_eq _ L.hwf]; simp only [callFn, whnfWalkFuel]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, invoke_exec0 p] <;> grind
  | n + 2 =>
    refine triple_post (whnfWalkFuel_spec p L.ct.cr.rx.hl.hv L.hdf L.hdp L.hdg L.hdn L.hdc L.hdd L.hwf n s₀ e) ?_
    rintro r s' ⟨h1, h2⟩
    exact ⟨h1, by simp [wfWf, h2]⟩

theorem nestCtorNf_spec' (p : Prog) (L : NbLook p) (k : Nat) (s₀ : St) (ctx po pl us dO dL cv closed : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_ctor_nf" [ctx, po, pl, us, dO, dL, cv, closed]
    ⦃fun r s' => LocEq s' s₀ ∧ ncnWf k s₀.mem ctx po pl us dO dL cv closed = some ([r.headD 0], s'.mem); ⊤⦄ := by
  match k with
  | 0 => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | k + 1 =>
    refine triple_post (nestCtorNf_spec p L.ct.cr.rx L.hnf k s₀ ctx po pl us dO dL cv closed) ?_
    rintro r s' ⟨h1, h2⟩
    exact ⟨h1, by simp [ncnWf, h2]⟩

theorem nestWalkStack_spec' (p : Prog) (L : NbLook p) (n : Nat) (s₀ : St) (ctx off l po pl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_walk_stack" [ctx, off, l, po, pl]
    ⦃fun r s' => LocEq s' s₀ ∧ nwsWf n s₀.mem ctx off l po pl = some (r, s'.mem); ⊤⦄ := by
  match n with
  | 0 => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | n + 1 => exact nestWalkStack_spec p L.dc L.hws n s₀ ctx off l po pl

section spec
variable (p : Prog)

/-- The specs of the block at exec fuel `n`. -/
def NbSpec (cR : CallM) (n : Nat) : Prop :=
  (∀ (s₀ : St) (vis ctx fu po pl dep kb e ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_pos" [vis, ctx, fu, po, pl, dep, kb, e, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbPosW cR n s₀.mem vis ctx fu po pl dep kb e ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl dep kb w ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_pos_bind" [vis, ctx, fu, po, pl, dep, kb, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbBindW cR n s₀.mem vis ctx fu po pl dep kb w ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl kb hi w ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_pos_app" [vis, ctx, fu, po, pl, kb, hi, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbAppW cR n s₀.mem vis ctx fu po pl kb hi w ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl kb nn us aO aL ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_cont" [vis, ctx, fu, po, pl, kb, nn, us, aO, aL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbContW cR n s₀.mem vis ctx fu po pl kb nn us aO aL ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_cont_key" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbKeyW cR n s₀.mem vis ctx fu po pl kb nn us dO dL nPc cty ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_cont_new" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbNewW cR n s₀.mem vis ctx fu po pl kb nn us dO dL nPc cty ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_frame" [vis, ctx, fu, po, pl, hi, us, dO, dL, nPc, gO, gL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbFrameW cR n s₀.mem vis ctx fu po pl hi us dO dL nPc gO gL ns =
      some ([r.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_ctors" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cO, cL, ns,
      oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧ nbCtorsW cR n s₀.mem vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_ctors_one" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cv, nF, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbOneW cR n s₀.mem vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx root fu po pl hi nF crest ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_ctors_walk" [vis, ctx, root, fu, po, pl, hi, nF, crest, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbWalkW cR n s₀.mem vis ctx root fu po pl hi nF crest ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
        r.tail.tail.tail.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl base nF j cur ns kO kL dO dL : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_fields" [vis, ctx, fu, po, pl, base, nF, j, cur, ns, kO, kL, dO, dL]
    ⦃fun r s' => LocEq s' s₀ ∧ nbFieldsW cR n s₀.mem vis ctx fu po pl base nF j cur ns kO kL dO dL =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
        r.tail.tail.tail.tail.headD 0, r.tail.tail.tail.tail.tail.headD 0], s'.mem); ⊤⦄)

variable {p} (L : NbLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (ih : NbSpec p cR n)
include L hcR ih

theorem nbFields_step (s₀ : St) (vis ctx fu po pl base nF j cur ns kO kL dO dL : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_fields" [vis, ctx, fu, po, pl, base, nF, j, cur, ns, kO,
      kL, dO, dL]
    ⦃fun r s' => LocEq s' s₀ ∧ nbFieldsW cR (n + 1) s₀.mem vis ctx fu po pl base nF j cur ns kO kL dO dL =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
        r.tail.tail.tail.tail.headD 0, r.tail.tail.tail.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, -, -, -, -, -, -, -, -, -, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pfields, callFn, nestFieldsL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p R.hl.hv n, hPos, internFVar_spec p R.hl.hff R.hl.hfp R.hl.hif n,
      i1F_spec p L.hi1 n, slSnoc_specW p R.ha L.nit.hc2 L.nag.hsn n, hFields] <;>
    simp_all [nbFieldsW_succ, nbFieldsK1_some, nbFieldsK2_some, nbFieldsK3_some, nbFieldsK4_some,
      nbFieldsK5_some, LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ]


theorem nbWalk_step (s₀ : St) (vis ctx root fu po pl hi nF crest ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_ctors_walk" [vis, ctx, root, fu, po, pl, hi, nF, crest, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbWalkW cR (n + 1) s₀.mem vis ctx root fu po pl hi nF crest ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
        r.tail.tail.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pwalk, callFn, nestCtorsWalkL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      whnfWalkFuel_spec' p L n, hFields,
      closeTelescope_spec p R.hk.hd R.hk.forF R.hk.forP R.hk.forI R.hk.forM L.hcl L.ab n] <;>
    simp_all [nbWalkW_succ, nbWalkK1_some, nbWalkK2_some, nbWalkK3_some,
      LocEq, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ]

theorem nbOne_step (s₀ : St) (vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_ctors_one" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cv, nF, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbOneW cR (n + 1) s₀.mem vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pone, callFn, nestCtorsOneL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      nestCtorsCrest_spec p L.ct cR hcR n, hWalk, nestCtorsU4_spec p L.usl L.hu4 n,
      nestCtorsResOk_spec p L.nit.no L.nit.hoa L.hrh L.nt.ad L.hro n, nestCtorNf_spec' p L n,
      slSnoc_specW p R.ha L.nit.hc2 L.nag.hsn n, rec6_specW p R.ha L.h6 n] <;>
    simp_all [nbOneW_succ, nbOneK1_some, nbOneK2_some, nbOneK3_some, nbOneK4_some, nbOneK5_some,
      nbOneK6_some, nbOneK7_some,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

theorem nbCtors_step (s₀ : St) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_ctors" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cO, cL, ns, oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧ nbCtorsW cR (n + 1) s₀.mem vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pctors, callFn, nestCtorsL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      hOne, posRec3_specW p R.ha L.h3 n, slSnoc_specW p R.ha L.nit.hc2 L.nag.hsn n, hCtors] <;>
    simp_all [nbCtorsW_succ, nbCtorsK1_some, nbCtorsK2_some, nbCtorsK3_some,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

theorem nbFrame_step (s₀ : St) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_frame" [vis, ctx, fu, po, pl, hi, us, dO, dL, nPc, gO, gL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbFrameW cR (n + 1) s₀.mem vis ctx fu po pl hi us dO dL nPc gO gL ns = some ([r.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pframe, callFn, nestFrameL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      naF_spec p L.na n, internConst_spec p R.cf R.cp R.ci n,
      mknF_spec p L.nt.ad n, hcR n "infer_type_core",
      nestFrameGrp_spec p R.ha L.nit.hc2 R.h2 R.h4 L.nag.hsn L.hfg n,
      nestGroupCtors_spec p L.nt L.nit.hc2 L.hap L.hgc n,
      nestFrameHoles_spec p R.ha L.nit.hc2 L.nag.hsn R.hl.hff R.hl.hfp R.hl.hif L.hfh n, hCtors] <;>
    simp_all [nbFrameW_succ, nbFrameK1_some, nbFrameK2_some, nbFrameK3_some, nbFrameK4_some,
      nbFrameK5_some, nbFrameK6_some, nbFrameK7_some, nbFrameK8_some,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

theorem nbNew_step (s₀ : St) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_cont_new" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbNewW cR (n + 1) s₀.mem vis ctx fu po pl kb nn us dO dL nPc cty ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pnew, callFn, nestContNewL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      nestWalkStack_spec' p L n, nestFrameMates_specW p L.fm n, nestCtxHiAt_specE p R.hi n,
      posRec2_specW p R.ha R.h2 n, slNew1_specW p R.ha L.hn1 n,
      nestGrowGroup_spec p L.nit R.h2 R.h4 L.nag.hsn L.hgg cR hcR n,
      nestContNewActive_spec p R.ha L.nit.hc2 R.h4 L.nag.hsn L.hca n,
      slAppend_specW p R.ha L.nit.hc2 L.hap n, rec6_specW p R.ha L.h6 n, hFrame,
      nestContNewFinish_spec p L.nag L.dc L.h6 L.hcf n] <;>
    simp_all [nbNewW_succ, nbNewK1_some, nbNewK2_some, nbNewK3_some, nbNewK4_some, nbNewK5_some,
      nbNewK6_some, nbNewK7_some, nbNewK8_some, nbNewK9_some, nbAppK6_some,
      LocEq, BinOp.eval, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

theorem nbKey_step (s₀ : St) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_cont_key" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbKeyW cR (n + 1) s₀.mem vis ctx fu po pl kb nn us dO dL nPc cty ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pkey, callFn, nestContKeyL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      posRec4_specW p R.ha R.h4 n, nestKeysContains_spec p L.nag.hq L.nag.he L.nag.hkc n,
      dc_spec' p L.dc.hf L.dc.hh L.dc.hg L.dc.hp n, hNew] <;>
    simp_all [nbKeyW_succ, nbKeyK1_some, nbKeyK2_some, nbAppK6_some, nestedW, Cmp.evalW,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

theorem nbCont_step (s₀ : St) (vis ctx fu po pl kb nn us aO aL ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_cont" [vis, ctx, fu, po, pl, kb, nn, us, aO, aL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbContW cR (n + 1) s₀.mem vis ctx fu po pl kb nn us aO aL ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pcont, callFn, nestContL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      nt_spec' p L.nt n, nestCtxHiAt_specE p R.hi n,
      nestContChecks_spec p L.nit.no L.nit.hoa L.hpa L.usl.hbp L.dc.hf L.hpc L.hcc n, posRec4_specW p R.ha R.h4 n,
      nestInstType_spec' p L.nit cR hcR n, hKey] <;>
    simp_all [nbContW_succ, nbContK1_some, nbContK2_some, nbContK3_some, nbContK4_some, nbAppK6_some,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ]

theorem nbApp_step (s₀ : St) (vis ctx fu po pl kb hi w ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_pos_app" [vis, ctx, fu, po, pl, kb, hi, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbAppW cR (n + 1) s₀.mem vis ctx fu po pl kb hi w ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.papp, callFn, nestPosAppL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      gaaF_spec p L.nt.ad n, gafF_spec p L.nt.ad n, eView_spec p R.hl.hv n,
      nestPosFvar_spec p L.pf n, slContains_spec p L.nit.no.hc n, hCont] <;>
    simp_all [nbAppW_succ, nbAppK1_some, nbAppK2_some, nbAppK4_some, nbAppK5_some, nbAppK6_some,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

theorem nbBind_step (s₀ : St) (vis ctx fu po pl dep kb w ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_pos_bind" [vis, ctx, fu, po, pl, dep, kb, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbBindW cR (n + 1) s₀.mem vis ctx fu po pl dep kb w ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pbind, callFn, nestPosBindL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      nestCtxHiAt_specE p R.hi n, eView_spec p R.hl.hv n, nestOcc_spec' p L.nit.no n,
      internFVar_spec p R.hl.hff R.hl.hfp R.hl.hif n, i1F_spec p L.hi1 n, hPos,
      abF_spec p L.ab n, mkForall_spec p R.hk.hd R.hk.forF R.hk.forP R.hk.forI R.hk.forM n] <;>
    simp_all [nbBindW_succ, nbBindK1_some, nbBindK2_some, nbBindK3_some, nbBindK4_some, nbBindK5_some,
      nbBindK6_some,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

theorem nbPos_step (s₀ : St) (vis ctx fu po pl dep kb e ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_pos" [vis, ctx, fu, po, pl, dep, kb, e, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbPosW cR (n + 1) s₀.mem vis ctx fu po pl dep kb e ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.ppos, callFn, nestPosL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      nestCtxHiAt_specE p R.hi n, hcR n "whnf_top", nestOcc_spec' p L.nit.no n, hBind, hApp] <;>
    simp_all [nbPosW_succ, nbPosK1_some, nbPosK2_some, nbPosK3_some, nbPosK4_some, nbPosK5_some,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

end spec

end L.Ind

namespace L.Ind

open L.Arena

theorem nbSpec_zero (p : Prog) (cR : CallM) : NbSpec p cR 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    exact triple_post (invoke_exec0 p _ _ _) (fun _ _ h => h.elim)

/-- **The block refines its word models**, at every exec fuel. -/
theorem nbSpec_all {p : Prog} (L : NbLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) : NbSpec p cR n := by
  induction n with
  | zero => exact nbSpec_zero p cR
  | succ n ih =>
    exact ⟨nbPos_step L cR hcR n ih, nbBind_step L cR hcR n ih, nbApp_step L cR hcR n ih, nbCont_step L cR hcR n ih, nbKey_step L cR hcR n ih,
      nbNew_step L cR hcR n ih, nbFrame_step L cR hcR n ih, nbCtors_step L cR hcR n ih, nbOne_step L cR hcR n ih, nbWalk_step L cR hcR n ih,
      nbFields_step L cR hcR n ih⟩

end L.Ind
