module

public import ConAgua.Arena.BasisBlockC
public import ConAgua.Arena.IndDeclConstsRef
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.IlpRd
import ConRon.Bridge.Checker.Basis
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# `check_basis_block` refines `checkBasisBlock` (lane `ronsync2`, stage 3)

`check_basis_block(vis, kind, bo, bl)` (`DeclArms.lean`): the pinned block read
(`rom_basis_decls`, `RomRefs`), the block copied to `IW` (`er_to_iw`), compared with the pin
(`pin_list_ok`, its contract `PinListOkRef`), each pin at the names its record declares
(`basis_at_block`, `BasisRefs`) installed (`install_basis_decls`, `ibds_ref`). The memos by the
call closure's write set (`cbbFns`, the stream index's `dcA`/`dcC` with `dc0Leaves`: `DcMem`,
`I1Memo`), the twin's `CheckOK` by con-ron's `RStep`s. `cbbRef_of` is `CbbRef`.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The call closure of `check_basis_block`** in the checker's program, without
`dc0Leaves` (`inst_lp_core`, `erec_alloc`) and what only they reach. -/
def cbbFns : List FnName :=
  ["check_basis_block", "install_basis_decls", "install_basis_decl", "env_push", "env_row_set",
   "env_find", "base_row_get", "env_row_get", "basis_at_block", "at_block_go", "sl_cons", "iw_copy",
   "iw_alloc", "ci_at_lps", "erec_put", "rules_at_lps_go", "fire_levels_at", "spn_to_er", "sle_go",
   "lv_sub_int", "lv_intern", "intern_imax", "imax_push", "imax_find", "intern_max", "max_push",
   "max_find", "intern_succ", "succ_push", "succ_find", "intern_param", "param_push", "param_find",
   "intern_zero", "zero_push", "zero_find", "lv_node", "lp_substl", "lh_mk", "lp_lookup",
   "keys_push", "ek_copy", "ls_node", "inst_lp", "param_levels", "intern_ls_iw", "intern_ls",
   "ls_push", "ls_find", "ls_match", "limbs_eq", "lit_hash", "iw_pool", "pool_room",
   "param_levels_go", "sl_get", "er_to_iw", "er_copy", "er_copy_er", "cv_at_lps", "rom_basis_decls",
   "rci_block", "rci_block_to", "rci_ci", "rci_rules_to", "rci_rule", "rom_expr_c", "rom_ex_two_c",
   "memo_push", "rset_put", "rset_find", "mk_let", "intern_letE", "letE_push", "letE_find", "der_b",
   "mk_forall", "intern_forall", "forall_push", "forall_find", "mk_lam", "intern_lam", "lam_push",
   "lam_find", "mk_app", "intern_app", "app_push", "app_find", "rom_ex_one_c", "mk_proj",
   "intern_proj", "proj_push", "proj_find", "rom_u64_c", "rom_name_c", "intern_nnum", "nnum_push",
   "nnum_find", "intern_nstr", "nstr_push", "nstr_find", "nstr_match", "rom_put_c", "intern_nanon",
   "nanon_push", "nanon_find", "intern_fvar", "fvar_push", "fvar_find", "rom_ex_leaf_c",
   "intern_const", "const_push", "const_find", "rom_levels_c", "stk_pool", "rom_lvls_go_c",
   "stk_push", "rom_level_c", "rom_lit", "intern_lit", "lit_push", "lit_find", "lit_match",
   "intern_sort", "sort_push", "sort_find", "intern_bvar", "bvar_push", "bvar_find", "rom_ex_ref_c",
   "memo_get", "rom_exprs_to_c", "rci_lvls_to", "rci_caps", "rci_name_sl", "rci_names_to", "rci_cv",
   "rci_fresh", "rset_clear", "rci_slot", "pin_list_ok", "block_links_ok", "block_links_ok_go",
   "block_link_ok_at", "rules_link_ok", "pin_link_ok", "pin_link_go", "canon_name_map", "sl_getd",
   "sl_find", "cv_lps", "const_named", "er_sl_eq", "pin_copies_ok", "pin_copy_ok", "pin_agrees",
   "ci_eq", "ci_eq_rest", "b_eq", "rules_eq", "rule_eq_but_rhs", "rule_eq_b", "er_sl_at",
   "rule_eq_a", "caps_eq", "caps_eq_c", "caps_eq_b", "caps_eq_a", "hint_eq", "cv_eq", "sl_nodup",
   "sl_contains"]

/-- **`cbbFns` stores into `dcA`/`dcC` only** (`Checker/BasisBlockClosed.lean`). -/
def CbbClosed (p : Prog) : Prop := closedAL p dcA dcC cbbFns dc0Leaves = true

/-- **A call of `cbbFns` keeps the stream index's memory invariants**, the `instantiate1Lift`
memo too (`dc_keep`'s and `dc0_keepI1`'s leaf arms). -/
theorem cbb_keep {p : Prog} (hP : DcLeafProg p) (hcl : CbbClosed p) {f : FnName} (hf : f ∈ cbbFns)
    {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word} (h : callW p n f vs m = some (r, m'))
    (hM : DcMem m) (hI : I1Memo m) : DcMem m' ∧ DcIdx m m' ∧ I1Memo m' := by
  refine callW_keepL (P := fun x => DcMem x ∧ DcIdx m x ∧ I1Memo x) hcl
    (fun _ _ hfr hx => ⟨hx.1.frameDc hfr, hx.2.1.frameDc hfr, hx.2.2.frameDc hfr⟩) ?_ hf h
    ⟨hM, DcIdx.refl m, hI⟩
  intro g hg n vs m₁ r m₂ hc hx
  simp only [dc0Leaves, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨dcMem_ma hP.ma hc hx.1, hx.2.1.frame (maLeaf_frame hP.ma hc)
      (fun b hb h' => by simp at h'; subst h'; revert hb; decide)
      (by decide) (by decide) (by decide) (by decide),
      I1Memo.frame hx.2.2 (maLeaf_frame hP.ma hc) (by decide) (by decide)⟩
  · exact ⟨dcMem_ilp hP.ilpf hc hx.1, hx.2.1.frame (instLPCore_frame hP.ilpf hc)
      (fun b hb h' => ilpfA_idx b h' hb) (by decide) (by decide) (by decide) ilpfA_pins,
      I1Memo.frame hx.2.2 (instLPCore_frame hP.ilpf hc) (by decide) (by decide)⟩
  · refine ⟨dcMem_alloc hP.alloc hc hx.1, dcIdx_alloc hP.alloc hc hx.2.1, ?_⟩
    rw [erecAlloc_mem hP.alloc hc]
    rcases erAllocMem_frame m₁ (vs.getD 0 0) with hfr | hfr
    · exact I1Memo.frame hx.2.2 hfr (by simp) (by decide)
    · exact I1Memo.frame hx.2.2 hfr (by simp) (by decide)

theorem mapM_range_congr {β : Type} {f g : Nat → Option β} :
    ∀ (l : Nat), (∀ j < l, f j = g j) → (List.range l).mapM f = (List.range l).mapM g
  | 0, _ => rfl
  | l + 1, h => by
    simp only [List.range_succ, List.mapM_append, List.mapM_cons, List.mapM_nil,
      mapM_range_congr l (fun j hj => h j (by omega)), h l (by omega)]

/-- **`er_to_iw` copies a block's record pointers**: the fresh `IW` slice decodes (`basisDec`) as
the `EREC` slice (`BlockAt`), any pointer (also above `2 ^ 32`, past `erToIwW_dec`'s handles). -/
theorem erToIwW_blk {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} {block : List IConstantInfo}
    (h : erToIwW n m o l = some (r, m')) (hS : StageR vis fe m a) (hB : BlockAt o l block m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ r.tail.headD 0 = l ∧
      DecB (basisDec dn (r.headD 0).toNat l.toNat) m' block ∧ MemFrame [IW] [200] m m' := by
  have hsz := hS.iw.iwSize
  have hc := hS.iw.ctl
  have hol : o.toNat + l.toNat ≤ 2 ^ 64 :=
    Nat.le_of_lt hB.2
  have hf0 := erToIwW_iwFr h
  simp only [erToIwW] at h
  cases hal : allocW m l with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  rcases hcp : erCopyW (n - 1) m1 q o l with _ | m2 <;>
    simp only [hcp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq hm1
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hIW := allocMem_IW m l
  have hR : ∀ a, erRd (allocMem m l) a = erRd m a := fun a => by
    simp only [allocMem, erRd]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by rw [tierA_EREC]; split <;> decide)]
  obtain ⟨hA, hS2, hG⟩ := erCopyW_get (n - 1) _ _ _ _ _ hcp hol
    (by rw [hIW]; exact hroom) (by rw [hIW]; exact hsz)
  rw [hIW] at hS2 hG
  have htop : rdW (m2.arr64 CTL) 200 = q + l := by
    rw [hA CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + l).toNat = q.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hg : IWGrow m m2 := by
    refine iwGrow_of_frame hf0 (N := l) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hG, ite_eq_right (by omega)]
  have hT2 : iwTop m2 = q.toNat + l.toNat := by simp only [iwTop, htop, hsum]
  have hroom2 : iwTop m2 ≤ (m2.arr64 IW).size := by rw [hT2, hS2]; omega
  refine ⟨⟨CheckR.frame_iw hf0 hS.check, hS.iw.of_iw hf0 hroom2⟩, hg, rfl, ?_, hf0⟩
  show basisDec dn q.toNat l.toNat (truncM m2) = some block
  rw [← hB.1]
  simp only [basisDec, decPL, L.Front.decCIsR]
  apply mapM_range_congr
  intro j hj
  have hb := hB.1
  obtain ⟨v, hv, hci⟩ : ∃ v, nat? (erecP m) (o.toNat + j) = some v ∧
      ∃ ci, decCI (erecP m) v = some ci := by
    have := mapM_opt_get _ (List.range l.toNat) block hb j (by simpa using hj)
    simp only [List.getElem_range, Option.bind_eq_bind, Option.bind_eq_some_iff] at this
    obtain ⟨v, hv, hc⟩ := this
    exact ⟨v, hv, _, hc⟩
  obtain ⟨w, hw, rfl⟩ : ∃ w, erecP m (o.toNat + j) = some w ∧ w.toNat = v := by
    simp only [nat?, Option.map_eq_some_iff] at hv; exact hv
  have e : (UInt64.ofNat (o.toNat + j)).toNat = o.toNat + j := by simp; omega
  have hw' : erecP m (UInt64.ofNat (o.toNat + j)).toNat = some w := by rw [e]; exact hw
  have hiw : iwA (truncM m2) (q.toNat + j) = some w := by
    rw [truncM_iw_eq (by omega)]
    simp only [iwA, aread_apply, hG]
    rw [ite_eq_left (by omega), hR, show q.toNat + j - q.toNat = j by omega, (erRd_of_erecP hw').1]
  obtain ⟨ci, hci⟩ := hci
  have hci2 : decCI (erA (truncM m2)) w.toNat = some ci :=
    ArrExt.decCI (by rw [truncM_erA]; exact hg.ext) hci
  simp only [iwN, nat?, hiw, Option.map_some]
  simp [hci, hci2, hw]

/-- **`check_basis_block`'s comparison's contract**: `pin_list_ok(io, il, po, pl)` on two `IW`
slices of constant records (the block's copy, the pin) refines `pinListOk block pins` (con-ron's
`pinListOk_run`: an `RStep`). Its proof belongs with `BasisL.lean`'s entry points (`basisRefs_of`). -/
def PinListOkRef (p : Prog) : Prop := ∀ (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (io il po pl : Word) (block pins : List IConstantInfo),
  L.Rom.RomRef p "pin_list_ok" [io, il, po, pl]
    (fun m a => StageT dn vis fe m a ∧ ConRon.Bridge.StateOK a ∧ ConRon.Bridge.ReadOK a ∧
      DecB (basisDec dn io.toNat il.toNat) m block ∧ DecB (basisDec dn po.toNat pl.toNat) m pins ∧
      (∃ B, Frontend.denoteCIList a.store block = some B) ∧
      (∃ P, Frontend.denoteCIList a.store pins = some P))
    (ConRon.Arena.pinListOk block pins) (KeepPostT dn vis fe (fun _ r b => (r.headD 0 ≠ 0 ↔ b = true)))

/-- The program facts `cbb_ref` takes. -/
structure CbbProg (p : Prog) : Prop where
  cbb : p.lookup "check_basis_block" = some checkBasisBlockL
  basis : BasisProg p
  rom : L.Rom.RomRefs p
  bref : BasisRefs p
  pl : PinListOkRef p
  ia : p.lookup "iw_alloc" = some iwAlloc
  ec : p.lookup "er_copy" = some erCopy
  eti : p.lookup "er_to_iw" = some erToIw
  leaf : DcLeafProg p
  closed : CbbClosed p

set_option experimental.vcgen true in
/-- **The model of `check_basis_block(vis, kind, bo, bl)`, both outcomes**: its callees (outside
the verdict closure) through their runs, `install_basis_decls` by its unified model. -/
l_model cbbE_spec (p : Prog) (hP : CbbProg p)
  fns [hP.cbb ↦ cbbE]
  specs [callW_spec p n "rom_basis_decls", callW_spec p n "er_to_iw", callW_spec p n "pin_list_ok",
    callW_spec p n "basis_at_block", installBasisDecls_specE p hP.basis n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem cbbF_rbd : "rom_basis_decls" ∈ cbbFns := List.elem_iff.mp (by decide)
theorem cbbF_eti : "er_to_iw" ∈ cbbFns := List.elem_iff.mp (by decide)
theorem cbbF_plo : "pin_list_ok" ∈ cbbFns := List.elem_iff.mp (by decide)
theorem cbbF_cbb : "check_basis_block" ∈ cbbFns := List.elem_iff.mp (by decide)

/-- **A call of `cbbFns` keeps `DcSt`**, given the twin's side after it. -/
theorem DcSt.stepB {p : Prog} (hP : CbbProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {env : ConLeche.Env} {f : FnName} (hf : f ∈ cbbFns) {n : Nat}
    {vs : List Word} {m m' : Mem} {a a' : AState} {r : List Word}
    (h : DcSt dn vis fe env m a) (hc : callW p n f vs m = some (r, m'))
    (hS : StageR vis fe m' a') (hok : ConRon.Bridge.CheckOK false env fe a')
    (hx : Ext a.store a'.store) : DcSt dn vis fe env m' a' := by
  obtain ⟨hM, hX, hI⟩ := cbb_keep hP.leaf hP.closed hf hc h.mem h.i1
  refine ⟨hS, hok, hM, hI, ⟨by rw [hX.sz]; exact h.tmem.erec, by rw [hX.sz]; exact h.tmem.spn,
    by rw [hX.sz]; exact h.tmem.bstk, hM.core,
    fun k x hk => ConRon.Bridge.denoteN_ext (h.tmem.dnN k x hk) hx⟩, ?_⟩
  simp only [pinW, hX.pins]; exact h.pin

/-- **`check_basis_block(vis, kind, bo, bl)` refines `checkBasisBlock`, both outcomes**, under the
stream index's `DcSt` (the stage with con-ron's `CheckOK`, the memos): the pin read
(`rom_basis_decls`, con-ron's `BasisKind.decls_run`), the block's copy (`erToIwW_blk`), the
comparison (`PinListOkRef`, `pinListOk_run`) and its decline, the pins at the block's names
(`BasisRefs.atBlock`, `BasisKind.atBlock_run`), the install (`ibds_ref`). -/
theorem cbb_ref {p : Prog} (hP : CbbProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {env : ConLeche.Env} (n : Nat) {m : Mem} {a : AState} {k bo bl : Word}
    {block : List IConstantInfo} {blockP : List ConLeche.ConstantInfo} (hk : k.toNat < 4)
    (hD : DcSt dn vis fe env m a) (hBA : BlockAt bo bl block m)
    (hbP : Frontend.denoteCIList a.store block = some blockP) :
    RefE True (cbbE p n m vis k bo bl) (checkBasisBlock fe (basisOfW k.toNat) block) a
      (fun v fe' a' => StageR v.1 fe' v.2 a' ∧ IWGrow m v.2) := by
  cases n with
  | zero => rw [cbbE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n =>
  rw [cbbE.arm1]
  simp only [ConRon.Arena.checkBasisBlock]
  -- `rom_basis_decls`
  refine RefE.onlySim (fun _ => cbbE.k_rom_basis_decls.none ..) (fun _ _ h => h) fun r1 m1 c1 => ?_
  rw [cbbE.k_rom_basis_decls.arm1]
  obtain ⟨pins, a1, hrun1, hS1, hg1, hpd1⟩ := hP.rom.basis dn vis fe k hk n m a r1 m1 hD.stage c1
  refine RefE.bind_right hrun1 ?_
  obtain ⟨hi1, hP1⟩ := ConRon.Bridge.BasisKind.decls_run hD.chk.state hrun1
  have hr1 := ConRon.Bridge.RStep.of_istep hi1 hD.chk.readOK
  have hD1 := hD.stepB hP cbbF_rbd c1 hS1 (hr1.checkOK hD.chk) hr1.ext
  -- `er_to_iw`
  refine RefE.onlySim (fun _ => cbbE.k_er_to_iw.none ..) (fun _ _ h => h) fun r2 m2 c2 => ?_
  rw [cbbE.k_er_to_iw.arm1]
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (erToIw_specW p hP.ia hP.ec hP.eti n _ bo bl) c2
  simp only at hs2 hW2
  subst hs2
  have hBA1 := blockAt_grow hBA hg1
  obtain ⟨hS2, hg2, hl2, hdec2, -⟩ := erToIwW_blk (dn := dn) hW2 hD1.stage hBA1
  have hD2 := hD1.stepB hP cbbF_eti c2 hS2 hD1.chk (Ext.refl _)
  -- `pin_list_ok`
  refine RefE.onlySim (fun _ => cbbE.k_pin_list_ok.none ..) (fun _ _ h => h) fun r3 m3 c3 => ?_
  have hbP1 := ConRon.Bridge.denoteCIList_mono hr1.ext _ _ hbP
  obtain ⟨b3, a3, hrun3, hT3, hg3, hb3⟩ := hP.pl dn vis fe _ _ _ _ block pins n s2.mem a1 r3 m3
    ⟨hD2.stageT, hD2.chk.state, hD2.chk.readOK, by rw [hl2]; exact hdec2,
      hpd1.1.grow (basisDec_mono dn _ _) hg2, ⟨_, hbP1⟩, ⟨_, hP1⟩⟩ c3
  refine RefE.bind_right hrun3 ?_
  obtain ⟨hr3, -⟩ := ConRon.Bridge.pinListOk_run hD2.chk.state hD2.chk.readOK hbP1 hP1 hrun3
  have hD3 := hD2.stepB hP cbbF_plo c3 hT3.stage (hr3.checkOK hD2.chk) hr3.ext
  by_cases h0 : r3.headD 0 = 0
  · rw [cbbE.k_pin_list_ok.abort1 _ _ _ _ _ _ _ _ h0]
    have hb : b3 = false := by cases b3 <;> simp_all
    subst hb
    exact fun _ => ErrClaim.bind_left (ErrClaim.fail_abort _ _ (by decide))
  rw [cbbE.k_pin_list_ok.arm1 _ _ _ _ _ _ _ _ h0]
  have hb : b3 = true := by simp_all
  subst hb
  simp only [ite_true]
  -- `basis_at_block`
  refine RefE.onlySim (fun _ => cbbE.k_basis_at_block.none ..) (fun _ _ h => h) fun r4 m4 c4 => ?_
  rw [cbbE.k_basis_at_block.arm1]
  obtain ⟨L, a4, hrun4, ⟨hT4, hg4, hL4⟩, -⟩ := hP.bref.atBlock dn vis fe k bo bl block hk n m3 a3 r4 m4
    ⟨hD3.stageT, hD3.chk.state, hD3.chk.readOK, blockAt_grow hBA1 (hg2.trans hg3), _,
      ConRon.Bridge.denoteCIList_mono hr3.ext _ _ hbP1⟩ c4
  refine RefE.bind_right hrun4 ?_
  exact (ibds_ref hP.basis dn n hT4.stage hL4.1).mono fun _ _ _ hR =>
    ⟨hR.stage, hg1.trans (hg2.trans (hg3.trans (hg4.trans hR.grow)))⟩

/-- An unconditional refinement under any `G`. -/
theorem RefE.ofTrue {α β : Type} {G : Prop} {x : Except Err α} {T : AM β} {a : AState}
    {R : α → β → AState → Prop} (h : RefE True x T a R) : RefE G x T a R := by
  cases x with
  | error e => exact fun _ => h trivial
  | ok v => exact h

/-- **`check_basis_block`'s contract** (`CbbRef`) from the program facts: `cbb_ref` on the call's
run (`RefE.ofCallE`), the memos after it by the write set (`cbb_keep`). -/
theorem cbbRef_of {p : Prog} (hP : CbbProg p) (dn : NIdx → Option ConLeche.Name) : CbbRef p dn := by
  intro n vis k o l fe env m a block blockP hk hC hBA hbP hIM hA
  have hD : DcSt dn vis fe env m a := ⟨hC.stage, hC.check,
    ⟨hC.mem.memos, hIM.stage, hIM.cr, hA.ab, hA.il, hA.wk⟩, hIM.i1, hC.mem, hC.flag⟩
  have h := RefE.ofCallE (s₀ := ⟨m, Locals.init []⟩) (cbbE_spec p hP n _ vis k o l) id
    (RefE.ofTrue (cbb_ref hP n hk hD hBA hbP))
  rcases c : callE p n "check_basis_block" [vis, k, o, l] m with e | ⟨r, m'⟩
  · rw [c] at h; exact h
  rw [c] at h
  obtain ⟨y, a', hrun, s', hs', -, hR, hg⟩ := h
  obtain ⟨hM', -, hI'⟩ := cbb_keep hP.leaf hP.closed cbbF_cbb (callW_of_callE c) hD.mem hD.i1
  simp only at hs'
  subst hs'
  exact ⟨y, a', hrun, ⟨hR, hM'.core, hg, ⟨hM'.stage, hI', hM'.cr⟩⟩⟩

end L.Ind
