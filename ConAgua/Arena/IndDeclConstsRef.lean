module

public import ConAgua.Arena.IndDeclConstsTable
public import ConAgua.Arena.IndDeclConstsFrame
public import ConAgua.Arena.IndDeclConstsTwin
public import ConAgua.Arena.IndRealPartsC2
public import ConAgua.Arena.DeclBasisRef
public import ConAgua.Arena.DeclAndPinIndCopy2
public import ConAgua.Arena.IndPosSpec.GgW2
import ConAgua.Arena.IndPosSpec.NestContParamsClosed
public import ConAgua.Arena.IndArmBridge2
public import ConAgua.Arena.IndDeclConstsSpec
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Inductives.Install
import ConLeche.Verify.Inductives.BlockShapeInv
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all ConAgua.Arena.IndDeclConsts
public import ConAgua.Arena.IndPartsSpec.IndPartsProg5
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndPartsSpec.RulePrefixAt

import ConAgua.L.ModelGen
import ConAgua.Arena.IndT.BlockCS
import ConAgua.Arena.ExceptOpt

@[expose] public section

/-!
# What a declaration installs: the refinements (lane `ronsync2`, stage 3)

`decl_constants(i)` refines con-ron's `declConstants d` and `decl_tables(i)` its `declTables d`
(`Arena/Install.lean`), at the statements of `IndDeclConstsSpec.lean`. Each L function has a
model (`dconW`, `daW`, `diW`, `dtW`: calls as `callW`, continuations in the `bkW` style); the
proofs follow the twin's arms: `erec_ci` (`erecCiW_ok`), `quot_at` (`BasisRefs`),
`ind_block_to_erec` (`indBlockToErec_ok`), `read_block` (`readBlock_refinesC`), `block_constants` (`bkW_ok`), `block_tables` (`btsW_ok`). The frame
facts come from the write set (`IndDeclConstsFrame.lean`: `dc_keep`, `dc0_keepI1`), `CheckOK`
across the twin's run from `IndDeclConstsTwin.lean`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena
open L.Front (DECL DLP dw)

/-! ## The models -/

/-- The quotient slot of a record's kind word. -/
def qSlot (w : Word) : Word := if w = 1 then 0 else if w = 2 then 1 else if w = 3 then 2 else 3

/-! ## The specs -/

/-- **The model of `decl_constants_axiom(q)`**. -/
l_model da_spec (p : Prog) (hp : p.lookup "decl_constants_axiom" = some declConstantsAxiom)
  fns [hp ↦ daW list]
  specs [callW_spec p n "pin_at", callW_spec p n "quot_at", callW_spec p n "sl_new1"]
  grind [arena_grind]

/-- **The model of `decl_constants_ind(bo, bl, nP)`**. -/
l_model di_spec (p : Prog) (hp : p.lookup "decl_constants_ind" = some declConstantsInd)
  fns [hp ↦ diW list]
  specs [callW_spec p n "read_block", callW_spec p n "block_constants"]
  grind [arena_grind]

/-- **The model of `decl_constants(i)`**, by the record's kind. -/
l_model dcon_spec (p : Prog) (hp : p.lookup "decl_constants" = some declConstants)
  fns [hp ↦ dconW list]
  specs [callW_spec p n "erec_ci", callW_spec p n "sl_new1", callW_spec p n "decl_constants_axiom",
    callW_spec p n "quot_at", callW_spec p n "ind_block_to_erec", callW_spec p n "decl_constants_ind"]
  grind [arena_grind]

/-- `decl_constants`' quotient arm by its slot `qSlot`. -/
theorem dconW.k_erec_ci_3_some (p : Prog) (n : Nat) (i : Word) (r : List Word) (m : Mem) :
    dconW.k_erec_ci_3 p n i (some (r, m)) =
      dconW.j1 p n (r.headD 0) (qSlot (rdW (m.arr64 DECL) (7 + 8 * i))) m := by
  rw [dconW.k_erec_ci_3.eq_2]; unfold qSlot
  generalize rdW (m.arr64 DECL) (7 + 8 * i) = w
  by_cases h1 : w = 1 <;> by_cases h2 : w = 2 <;> by_cases h3 : w = 3 <;> simp [h1, h2, h3]

/-- **The model of `decl_tables(i)`**. -/
l_model dt_spec (p : Prog) (hp : p.lookup "decl_tables" = some declTables)
  fns [hp ↦ dtW list]
  specs [callW_spec p n "ind_block_to_erec", callW_spec p n "read_block",
    callW_spec p n "block_tables"]
  grind [arena_grind]

/-! ## The state the arms thread -/

/-- **What the arms keep from call to call**: the stage relation, con-ron's `CheckOK` at `env`, the
write set's memory invariant (`DcMem`), the `instantiate1Lift` memo, the twin's memory half and the
pin flag. -/
structure DcSt (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) : Prop where
  stage : StageR vis fe m a
  chk : ConRon.Bridge.CheckOK false env fe a
  mem : DcMem m
  i1 : I1Memo m
  tmem : TwinMem dn m a
  pin : pinW m 0 ≠ 0

section dcst
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

theorem DcSt.stageC {m : Mem} {a : AState} (h : DcSt dn vis fe env m a) : StageC dn vis fe env m a :=
  ⟨h.stage, h.chk, h.tmem, h.pin⟩

theorem DcSt.stageT {m : Mem} {a : AState} (h : DcSt dn vis fe env m a) : StageT dn vis fe m a :=
  h.stageC.stageT

theorem DcSt.abs {m : Mem} {a : AState} (h : DcSt dn vis fe env m a) : AbsOK m :=
  ⟨h.mem.ab, h.i1, h.mem.cr, h.mem.il, h.mem.wk, h.mem.core.hb⟩

theorem DcIdx.trans {m₀ m₁ m₂ : Mem} (h₁ : DcIdx m₀ m₁) (h₂ : DcIdx m₁ m₂) : DcIdx m₀ m₂ :=
  ⟨fun b hb => (h₂.arr b hb).trans (h₁.arr b hb), h₂.c128.trans h₁.c128, h₂.c1.trans h₁.c1,
    fun h0 => (h₂.c130 (h₁.c1.trans h0)).trans (h₁.c130 h0), h₂.pins.trans h₁.pins,
    fun b => (h₂.sz b).trans (h₁.sz b)⟩

/-- **A call of the write set** keeps `DcSt`, given the twin's side after it. -/
theorem DcSt.step {p : Prog} (hP : DcLeafProg p) {f : FnName} (hf : f ∈ dcFns) {n : Nat}
    {vs : List Word} {m m' : Mem} {a a' : AState} {r : List Word}
    (h : DcSt dn vis fe env m a) (hc : callW p n f vs m = some (r, m'))
    (hS : StageR vis fe m' a') (hok : ConRon.Bridge.CheckOK false env fe a')
    (hx : Ext a.store a'.store) (hI : I1Memo m') : DcSt dn vis fe env m' a' ∧ DcIdx m m' := by
  obtain ⟨hM, hX⟩ := dc_keep hP hf hc h.mem
  refine ⟨⟨hS, hok, hM, hI, ⟨by rw [hX.sz]; exact h.tmem.erec, by rw [hX.sz]; exact h.tmem.spn,
    by rw [hX.sz]; exact h.tmem.bstk, hM.core,
    fun k x hk => ConRon.Bridge.denoteN_ext (h.tmem.dnN k x hk) hx⟩, ?_⟩, hX⟩
  simp only [pinW, hX.pins]; exact h.pin

/-- The same for a call of `dc0Fns` (the `instantiate1Lift` memo by the write set). -/
theorem DcSt.step0 {p : Prog} (hP : DcLeafProg p) {f : FnName} (hf : f ∈ dcFns) (hf0 : f ∈ dc0Fns)
    {n : Nat} {vs : List Word} {m m' : Mem} {a a' : AState} {r : List Word}
    (h : DcSt dn vis fe env m a) (hc : callW p n f vs m = some (r, m'))
    (hS : StageR vis fe m' a') (hok : ConRon.Bridge.CheckOK false env fe a')
    (hx : Ext a.store a'.store) : DcSt dn vis fe env m' a' ∧ DcIdx m m' :=
  h.step hP hf hc hS hok hx (dc0_keepI1 hP hf0 hc h.i1)

/-- `DcSt` from the pre-condition. -/
theorem DeclConstsPre.dcSt {i : Word} {d : IDeclaration} {m : Mem} {a : AState}
    (h : DeclConstsPre dn vis fe i d m a) : ∃ env, DcSt dn vis fe env m a := by
  obtain ⟨env, hc⟩ := h.tw.chk
  exact ⟨env, h.stage, hc, ⟨h.tw.twin.memos, h.memos.stage, h.memos.cr, h.tw.abs.ab, h.tw.abs.il,
    h.tw.abs.wk⟩, h.memos.i1, h.tw.twin.mem, h.tw.pin⟩

/-- The scratch flag `CTL[1]` is off while the twin's scratch tier is closed. -/
theorem flag0_of {m : Mem} {a : AState} (h : CheckR m a vis fe) (hoff : a.store.scratchOn = false) :
    rdW (m.arr64 CTL) 1 = 0 := by
  have hf := h.arena.base.app.flag
  rw [hoff] at hf
  simpa using hf

/-- **The frame half of both posts**, from `DcSt` after the run. -/
theorem dc_post {m m' : Mem} {a' : AState} (h : DcSt dn vis fe env m' a') (hX : DcIdx m m')
    (hoff : rdW (m.arr64 CTL) 1 = 0) : IndMemos m' ∧ IdxKeep m m' ∧ DeclTwin dn fe m' a' :=
  ⟨⟨h.mem.stage, h.i1, h.mem.cr⟩, ⟨hX.arr, hX.c128, hX.c130 hoff, fun _ => h.mem.core⟩,
    ⟨TwinOK.of_check h.chk h.tmem, h.pin, h.abs, ⟨env, h.chk⟩⟩⟩

end dcst

/-! ## The program -/

/-- **The lookups and program facts both refinements take**: the tables' and constants' (and
their callees'), the quotient pins' refinements (`BasisRefs`), the write set's leaves
(`DcLeafProg`), `ind_block_to_erec`'s, `read_block`'s (`IndPartsProg5`, `CoreStageClosed`,
`LvlCacheProg`), `erec_ci`'s (`RecProg`). -/
structure DeclConstsProg (p : Prog) : Prop extends TablesProg p where
  basis : BasisRefs p
  leaf : DcLeafProg p
  ibe : IbeProg p
  parts : IndPartsProg5 p
  hcl : CoreStageClosed p
  hL : LvlCacheProg p
  rcp : RecProg p
  pinAt : p.lookup "pin_at" = some pinAtL
  slNew1 : p.lookup "sl_new1" = some slNew1
  decl_constants : p.lookup "decl_constants" = some declConstants
  decl_constants_axiom : p.lookup "decl_constants_axiom" = some declConstantsAxiom
  decl_constants_ind : p.lookup "decl_constants_ind" = some declConstantsInd
  decl_tables : p.lookup "decl_tables" = some declTables

/-! The callees in the write set. -/
theorem dcF_ibe : "ind_block_to_erec" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_rb : "read_block" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_bk : "block_constants" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_eci : "erec_ci" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_qa : "quot_at" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_new1 : "sl_new1" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_pin : "pin_at" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_dca : "decl_constants_axiom" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_dci : "decl_constants_ind" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dc0F_ibe : "ind_block_to_erec" ∈ dc0Fns := List.elem_iff.mp (by decide)
theorem dc0F_rb : "read_block" ∈ dc0Fns := List.elem_iff.mp (by decide)
theorem dc0F_bk : "block_constants" ∈ dc0Fns := List.elem_iff.mp (by decide)
theorem dc0F_eci : "erec_ci" ∈ dc0Fns := List.elem_iff.mp (by decide)
theorem dc0F_qa : "quot_at" ∈ dc0Fns := List.elem_iff.mp (by decide)
theorem dc0F_new1 : "sl_new1" ∈ dc0Fns := List.elem_iff.mp (by decide)
theorem dc0F_pin : "pin_at" ∈ dc0Fns := List.elem_iff.mp (by decide)
theorem dc0F_dca : "decl_constants_axiom" ∈ dc0Fns := List.elem_iff.mp (by decide)
theorem dc0F_dci : "decl_constants_ind" ∈ dc0Fns := List.elem_iff.mp (by decide)

theorem decTblL_nil (m : Mem) : decTblL m [0, 0] [] := by simp [decTblL, decRL, decPL]
theorem decCIL_nil (m : Mem) : decCIL m [0, 0] [] := by simp [decCIL, decRL, decPL]

/-! ## `decl_tables` -/

theorem dtW_ok {p : Prog} (hP : DeclConstsProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {env : ConLeche.Env} {i : Word} {d : IDeclaration} {n : Nat} {m m' : Mem}
    {a : AState} {r : List Word}
    (hpre : DeclConstsPre dn vis fe i d m a) (h0 : DcSt dn vis fe env m a)
    (h : dtW p n m i = some (r, m')) :
    ∃ ts a', (ConRon.Arena.declTables d).run a = .ok (ts, a') ∧
      KeepPost vis fe decTblL m m' a' r ts ∧ DcSt dn vis fe env m' a' ∧ DcIdx m m' := by
  obtain ⟨ds, hD, hi, hdi⟩ := hpre.decls
  have hi8 : 8 * i.toNat + 9 < 2 ^ 64 := by have := hD.room; have := hD.dsize; omega
  have ek : rdW (m.arr64 DECL) (1 + 8 * i) = dw (m.arr64 DECL) i.toNat 0 :=
    rdW_dw _ hi8 (by decide) (by decide)
  rcases n with _ | n
  · simp [dtW] at h
  rw [dtW.eq_2, ek] at h
  have hdecl := hpre.decl
  rcases (Classical.em (∃ b nP, d = .indDecl b nP)).symm with hd | hd
  · have hk : dw (m.arr64 DECL) i.toNat 0 ≠ 6 := by
      cases d with
      | indDecl b nP => exact absurd ⟨b, nP, rfl⟩ hd
      | _ => simp only [L.Front.DeclAtF, L.Front.DeclAt] at hdecl; rw [hdecl.1]; decide
    rw [ite_eq_left hk] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨[], a, ?_, ⟨hpre.stage, IWGrow.refl m, decTblL_nil _⟩, h0, DcIdx.refl m⟩
    cases d with
    | indDecl b nP => exact absurd ⟨b, nP, rfl⟩ hd
    | _ => rfl
  obtain ⟨b, nP, rfl⟩ := hd
  obtain ⟨hk6, hnP, -⟩ := hdecl
  rw [ite_eq_right (not_not_intro hk6)] at h
  obtain ⟨bP, hbP⟩ : ∃ bP, Frontend.denoteCIList a.store b = some bP := by
    obtain ⟨dd, hd⟩ := hpre.den
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨bP, hb, -⟩ := hd
    exact ⟨bP, hb⟩
  -- `ind_block_to_erec`
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [dtW.k_ind_block_to_erec.none])
  rw [dtW.k_ind_block_to_erec.arm1] at h
  obtain ⟨hS1, hg1, -, -, -, hb1, hbt1⟩ := indBlockToErec_ok hP.ibe h1 hpre.stage hpre.decl
    (hpre.front b nP rfl) hpre.dsize hpre.psize
  obtain ⟨h01, hX1⟩ := h0.step0 hP.leaf dcF_ibe dc0F_ibe h1 hS1 h0.chk (Ext.refl _)
  -- `read_block`
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [dtW.k_read_block.none])
  have eD : m1.arr64 DECL = m.arr64 DECL := hX1.arr _ (.inl rfl)
  have ew : rdW (m1.arr64 DECL) (5 + 8 * i) = dw (m.arr64 DECL) i.toNat 4 := by
    rw [eD]; exact rdW_dw _ hi8 (by decide) (by decide)
  rw [ew] at h3
  have hblk : DecB (fun m => decEBlk dn m (r1.headD 0).toNat (r1.tail.headD 0).toNat) m1 b :=
    decB_decEBlk_of_decCIs hb1
  obtain ⟨s3, hs3, -, hok3, hR3, hS3, hg3⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (readBlock_refinesC p hP.hcl hP.hL hP.parts n ⟨m1, Locals.init []⟩ a _ _ _ b h01.stageC
      h01.abs hbP hblk) (callW_mono h3 (Nat.le_add_right n 5))
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hnP] at hrun3 hR3 hS3
  generalize AM.res (ConRon.Arena.readBlock nP b) a = x3 at hrun3 hR3
  generalize AM.st (ConRon.Arena.readBlock nP b) a = a3 at hrun3 hS3
  obtain ⟨hps3, -, hq3⟩ := ConRon.Bridge.Inductives.readBlock_installS h01.chk hbP hrun3
  obtain ⟨h03, hX3⟩ := h01.step0 hP.leaf dcF_rb dc0F_rb h3 hS3
    (checkOK_of_pstep h01.chk hps3) hps3.ext
  cases x3 with
  | error ce =>
    obtain ⟨hc3, -⟩ := hR3
    rw [dtW.k_read_block.arm1 (hc1 := hc3.1)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨[], a3, ?_, ⟨hS3, hg1.trans hg3, decTblL_nil _⟩, h03, hX1.trans hX3⟩
    simp only [ConRon.Arena.declTables, StateT.run_bind, hrun3]
    rfl
  | ok bs =>
  obtain ⟨e3, hq, -⟩ := hR3
  rw [dtW.k_read_block.arm2 (hc1 := e3)] at h
  generalize r3.tail.headD 0 = pp at hq h
  -- the members' slice
  have hqt : decBS (truncM s3.mem) pp.toNat = some bs := hq
  obtain ⟨hmem, -⟩ := decBS_some hqt
  obtain ⟨o, l, ho, hl, hdm, hob⟩ := partsAt decMS_mono hmem
  obtain ⟨hoW, -⟩ := iwRd (o := pp) (w := 0) (by simpa using ho)
  obtain ⟨hlW, -⟩ := iwRd (o := pp) (w := 1) (by simpa using hl)
  have eo : rdW (s3.mem.arr64 IW) pp = o := by
    have := UInt64.toNat_inj.mp hoW; simpa using this
  have el : rdW (s3.mem.arr64 IW) (pp + 1) = l := UInt64.toNat_inj.mp hlW
  rw [eo, el] at h
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [dtW.k_block_tables.none])
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (bts_spec hP.toTablesProg n _ pp o l) h4
  -- the parameter count
  simp only [ConRon.Bridge.Inductives.ROp] at hq3
  obtain ⟨pP, hpP, hdP⟩ := hq3
  have hbnP : bs.nP = nP := ((ConRon.Bridge.Inductives.dShape_inv hdP).2.2.1).trans
    (ConLeche.readBlock_inv (except_toOption_eq_some.mp hpP)).1
  have hnPb : 1 + bs.nP < 2 ^ 64 := by rw [hbnP]; have := hpre.nPb b nP rfl; omega
  obtain ⟨ts, a4, hrun4, hB4, hS4, hg4, hA4⟩ := btsW_ok hP.toTablesProg pp bs vis fe hnPb n
    s3.mem s4.mem a3 o l bs.members r4 hS3 h03.abs hq ⟨hdm, hob⟩ hW4
  obtain ⟨hms, -⟩ := ConRon.Bridge.Inductives.dShape_inv hdP
  obtain ⟨hps4, -, -⟩ := ConRon.Bridge.Inductives.blockTables_run bs.members pP.members
    h03.chk.state hdP hms hrun4
  obtain ⟨h04, hX4⟩ := h03.step hP.leaf L.Ind.dcF_bts h4 hS4 (checkOK_of_pstep h03.chk hps4)
    hps4.ext hA4.i1
  cases ts with
  | none =>
    have hz : r4.headD 0 = 0 := hB4
    rw [dtW.k_block_tables.arm1 p r4 _ hz] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨[], a4, ?_, ⟨hS4, hg1.trans (hg3.trans hg4), decTblL_nil _⟩, h04,
      hX1.trans (hX3.trans hX4)⟩
    simp only [ConRon.Arena.declTables, StateT.run_bind, hrun3, except_ok_bind, hrun4]
    rfl
  | some ts =>
    obtain ⟨h1', hd4, hb4⟩ := hB4
    rw [dtW.k_block_tables.arm2 p r4 _ (by rw [h1']; decide)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨ts, a4, ?_, ⟨hS4, hg1.trans (hg3.trans hg4), ?_⟩, h04,
      hX1.trans (hX3.trans hX4)⟩
    · simp only [ConRon.Arena.declTables, StateT.run_bind, hrun3, except_ok_bind, hrun4]
      rfl
    · exact ⟨by simpa using hd4, by simpa using hb4⟩

/-! ## The constant-slice helpers -/

theorem decCIL_pair {m : Mem} {r : List Word} {x : List IConstantInfo} (h : decCIL m r x) :
    decCIL m [r.headD 0, r.tail.headD 0] x := by
  rcases r with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simpa [decCIL, decRL] using h

/-- **A constant record `x` as a one-element slice** (`sl_new1`). -/
theorem new1W_ci {vis : Word} {fe : IFEnv} {a : AState} {m m' : Mem} {x : Word} {r : List Word}
    {ci : IConstantInfo} (h : new1W m x = some (r, m')) (hS : StageR vis fe m a)
    (hx : decCI (erecP m) x.toNat = some ci) :
    decCIL m' r [ci] ∧ StageR vis fe m' a ∧ IWGrow m m' := by
  obtain ⟨hpr, hr⟩ := new1W_rec h
  obtain ⟨hS', hg, htop, hget⟩ := partsFreshGet hpr hS (by simp)
  obtain ⟨-, h0⟩ := truncM_iw_get (hget 0 (by simp))
  refine ⟨?_, hS', hg⟩
  rw [hr]
  refine ⟨?_, by simp at htop ⊢; omega⟩
  have := decPL_of_get (m := m') (decCI (erecP m')) [ci] (r.headD 0).toNat (fun j hj => by
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    exact ⟨x.toNat, by simp only [iwN, nat?]; rw [h0]; rfl, hg.ext.decCI hx⟩)
  simpa using this

/-- A constant record decoded below the tops (`decRCI`), in the grown pool. -/
theorem decRCI_get {dn : NIdx → Option ConLeche.Name} {m : Mem} {r : List Word} {ci : IConstantInfo}
    (h : decRCI dn m r ci) : decCI (erecP m) (r.headD 0).toNat = some ci := by
  have h' : decCI (erA (truncM m)) (r.headD 0).toNat = some ci := h
  rwa [truncM_erA] at h'

/-- The quotient slot word of a record's kind word. -/
theorem qSlot_eq (w : Word) : qSlot w = UInt64.ofNat (L.Front.quotW w).slot := by
  unfold qSlot L.Front.quotW
  by_cases h1 : w = 1
  · simp [h1]; rfl
  by_cases h2 : w = 2
  · simp [h2]; rfl
  by_cases h3 : w = 3
  · simp [h3]; rfl
  simp [h1, h2, h3]; rfl

/-! ## `decl_constants_ind` -/

theorem diW_ok {p : Prog} (hP : DeclConstsProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {env : ConLeche.Env} {b : List IConstantInfo} {bP : List ConLeche.ConstantInfo}
    {nP : Nat} {bo bl w : Word} {n : Nat} {m m' : Mem} {a : AState} {r : List Word}
    (h0 : DcSt dn vis fe env m a) (hblk : BlockAt bo bl b m)
    (hbP : Frontend.denoteCIList a.store b = some bP) (hw : w.toNat = nP)
    (h : diW p n m bo bl w = some (r, m')) :
    ∃ cis a', (ConRon.Arena.declConstants (.indDecl b nP)).run a = .ok (cis, a') ∧
      KeepPost vis fe decCIL m m' a' r cis ∧ DcSt dn vis fe env m' a' ∧ DcIdx m m' := by
  rcases n with _ | n
  · simp [diW] at h
  rw [diW.arm1] at h
  -- `read_block`
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [diW.k_read_block.none])
  have hblk' : DecB (fun m => decEBlk dn m bo.toNat bl.toNat) m b :=
    decB_decEBlk_of_decCIs hblk.1
  obtain ⟨s3, hs3, -, hok3, hR3, hS3, hg3⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (readBlock_refinesC p hP.hcl hP.hL hP.parts n ⟨m, Locals.init []⟩ a _ _ _ b h0.stageC
      h0.abs hbP hblk') (callW_mono h3 (Nat.le_add_right n 5))
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hw] at hrun3 hR3 hS3
  generalize AM.res (ConRon.Arena.readBlock nP b) a = x3 at hrun3 hR3
  generalize AM.st (ConRon.Arena.readBlock nP b) a = a3 at hrun3 hS3
  obtain ⟨hps3, -, hq3⟩ := ConRon.Bridge.Inductives.readBlock_installS h0.chk hbP hrun3
  obtain ⟨h03, hX3⟩ := h0.step0 hP.leaf dcF_rb dc0F_rb h3 hS3
    (checkOK_of_pstep h0.chk hps3) hps3.ext
  cases x3 with
  | error ce =>
    obtain ⟨hc3, -⟩ := hR3
    rw [diW.k_read_block.arm1 (hc1 := hc3.1)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨[], a3, ?_, ⟨hS3, hg3, decCIL_nil _⟩, h03, hX3⟩
    simp only [ConRon.Arena.declConstants, StateT.run_bind, hrun3]
    rfl
  | ok bs =>
  obtain ⟨e3, hq, hsl⟩ := hR3
  rw [diW.k_read_block.arm2 (hc1 := e3)] at h
  generalize r3.tail.headD 0 = pp at hq hsl h
  -- `block_constants`
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [diW.k_block_constants.none])
  rw [diW.k_block_constants.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (bk_spec p hP.bk n _ pp) h4
  obtain ⟨mp, hmp⟩ := h03.mem.stage.ma
  obtain ⟨cis, a4, hrun4, hd4, hb4, hS4, hg4⟩ := bkW_ok hP.toBlockProg hS3 hq hsl.1 hmp hW4
  simp only [ConRon.Bridge.Inductives.ROp] at hq3
  obtain ⟨pP, -, hdP⟩ := hq3
  obtain ⟨hps4, -, -⟩ := ConRon.Bridge.Inductives.blockConstants_run h03.chk.state h03.chk.pins
    hdP hrun4
  obtain ⟨h04, hX4⟩ := h03.step0 hP.leaf dcF_bk dc0F_bk h4 hS4 (checkOK_of_pstep h03.chk hps4)
    hps4.ext
  refine ⟨cis, a4, ?_, ⟨hS4, hg3.trans hg4, ⟨by simpa using hd4, by simpa using hb4⟩⟩,
    h04, hX3.trans hX4⟩
  simp only [ConRon.Arena.declConstants, StateT.run_bind, hrun3, except_ok_bind, hrun4]

/-! ## `decl_constants_axiom` -/

theorem daW_ok {p : Prog} (hP : DeclConstsProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {env : ConLeche.Env} {q : Word} {cv : IConstantVal} {c : ConLeche.ConstantVal}
    {n : Nat} {m m' : Mem} {a : AState} {r : List Word}
    (h0 : DcSt dn vis fe env m a) (hnd : L.Rom.NamesDn dn a L.Rom.quotNames)
    (hci : decCI (erecP m) q.toNat = some (.axiomInfo cv))
    (hcv : decCV (erecP m) (q.toNat + 1) = some cv) (hcvd : Frontend.denoteCV a.store cv = some c)
    (h : daW p n m q = some (r, m')) :
    ∃ cis a', (ConRon.Arena.declConstantsAxiom cv).run a = .ok (cis, a') ∧
      KeepPost vis fe decCIL m m' a' r cis ∧ DcSt dn vis fe env m' a' ∧ DcIdx m m' := by
  rcases n with _ | n
  · simp [daW] at h
  rw [daW.arm1] at h
  obtain ⟨wn, hwn, hwnl, hname⟩ := decCV_name hcv
  have hqb : q.toNat + 1 < 2 ^ 64 := L.Arena.erecP_lt64 hwn
  have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have ex : ∀ {m₁ : Mem}, erecP m₁ (q.toNat + 1) = some wn → erRd m₁ (q + 1) = wn :=
    fun h => (erRd_of_erecP (by rw [hq1]; exact h)).1
  -- `Quot.sound`'s pin
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [daW.k_pin_at.none])
  rw [daW.k_pin_at.eq_2] at h
  simp only [erRd_foldN] at h
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pinAt_specW p hP.pinAt n _ 4) h1
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok hW1 h0.stage.check.pins
  rw [hm1, hr1] at h
  simp only [List.headD_cons] at h
  simp only [ex hwn] at h
  have hpq : ConRon.Arena.pinQuotSound.run a = .ok (decI (pinW m (1 + (4 : Word).toNat)), a) := by
    simpa [ConRon.Arena.pinQuotSound, show ConRon.Arena.PIN_QUOT_SOUND = (4 : Word).toNat from rfl]
      using hrun1
  have hb1 := decI_beq (k := .name) wn _ hwnl hl1
  by_cases e1 : wn = pinW m (1 + (4 : Word).toNat)
  · simp only [e1, ↓reduceIte] at h
    obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [daW.k_quot_at.none])
    rw [daW.k_quot_at.arm1] at h
    obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [daW.k_sl_new1.none])
    rw [daW.k_sl_new1.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨ci, a2, hrun2, hT2, hg2, hd2⟩ := hP.basis.quotAt dn vis fe .sound (q + 1) cv n m a r2 m2
      ⟨h0.stageT, h0.chk.state, h0.chk.readOK, hnd, by rw [hq1]; exact hcv, c, hcvd⟩ h2
    have hS2 := hT2.stage
    obtain ⟨hr2, -⟩ := ConRon.Bridge.quotAt_run h0.chk.state h0.chk.readOK hcvd hrun2
    obtain ⟨h02, hX2⟩ := h0.step0 hP.leaf dcF_qa dc0F_qa h2 hS2 (hr2.checkOK h0.chk) hr2.ext
    obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (slNew1_specW p hP.alloc hP.slNew1 n _ _) h3
    obtain ⟨hdl, hS3, hg3⟩ := new1W_ci hW3 hS2 (decRCI_get hd2)
    obtain ⟨h03, hX3⟩ := h02.step0 hP.leaf dcF_new1 dc0F_new1 h3 hS3 h02.chk (Ext.refl _)
    refine ⟨[ci], a2, ?_, ⟨hS3, hg2.trans hg3, decCIL_pair hdl⟩, h03, hX2.trans hX3⟩
    simp only [ConRon.Arena.declConstantsAxiom, StateT.run_bind, hpq, except_ok_bind, hname,
      e1, hrun2, beq_self_eq_true, ↓reduceIte]
    rfl
  simp only [e1, ↓reduceIte] at h
  -- `sorryAx`'s pin
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [daW.k_pin_at_2.none])
  rw [daW.k_pin_at_2.eq_2] at h
  simp only [erRd_foldN] at h
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pinAt_specW p hP.pinAt n _ 13) h4
  obtain ⟨hm4, hr4, hl4, hrun4⟩ := pinAtW_ok hW4 h0.stage.check.pins
  rw [hm4, hr4] at h
  simp only [List.headD_cons] at h
  simp only [ex hwn] at h
  have hps : ConRon.Arena.pinSorryAx.run a = .ok (decI (pinW m (1 + (13 : Word).toNat)), a) := by
    simpa [ConRon.Arena.pinSorryAx, show ConRon.Arena.PIN_SORRY_AX = (13 : Word).toNat from rfl]
      using hrun4
  have hb4 := decI_beq (k := .name) wn _ hwnl hl4
  have hrunA : ∀ {x : List IConstantInfo}, (ConRon.Arena.declConstantsAxiom cv).run a =
      (if wn = pinW m (1 + (13 : Word).toNat) then .ok ([], a) else .ok ([.axiomInfo cv], a) :
        Except _ (List IConstantInfo × AState)) := by
    intro _
    simp only [ConRon.Arena.declConstantsAxiom, StateT.run_bind, hpq, except_ok_bind, hname, hb1,
      e1, decide_false, Bool.false_eq_true, ite_false, hps, hb4]
    by_cases e : wn = pinW m (1 + (13 : Word).toNat) <;>
      simp only [e, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;> rfl
  by_cases e4 : wn = pinW m (1 + (13 : Word).toNat)
  · simp only [e4, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨[], a, ?_, ⟨h0.stage, IWGrow.refl _, decCIL_nil _⟩, h0, DcIdx.refl _⟩
    rw [hrunA (x := []), ite_eq_left e4]
  simp only [e4, ↓reduceIte] at h
  obtain ⟨⟨r5, m5⟩, h5, h⟩ := of_K h (by simp [daW.k_sl_new1.none])
  rw [daW.k_sl_new1.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s5, rfl, -, hW5⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slNew1_specW p hP.alloc hP.slNew1 n _ _) h5
  obtain ⟨hdl, hS5, hg5⟩ := new1W_ci hW5 h0.stage hci
  obtain ⟨h05, hX5⟩ := h0.step0 hP.leaf dcF_new1 dc0F_new1 h5 hS5 h0.chk (Ext.refl _)
  refine ⟨[.axiomInfo cv], a, ?_, ⟨hS5, hg5, decCIL_pair hdl⟩, h05, hX5⟩
  rw [hrunA (x := []), ite_eq_right e4]

/-! ## `decl_constants` -/

/-- `erec_ci(i, ck)` then `sl_new1`: the one record `installStepGo` pushes. -/
theorem eciNew1 {p : Prog} (hP : DeclConstsProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {env : ConLeche.Env} {i ck : Word} {ds : Array IDeclaration} {ci : IConstantInfo}
    {n : Nat} {m m' : Mem} {a : AState} {r : List Word}
    (h0 : DcSt dn vis fe env m a) (hD : L.Front.DeclsF (m.arr64 DECL) (m.arr64 DLP) ds)
    (hi : i.toNat < ds.size) (hci : stepCI ck.toNat ds[i.toNat] = some ci)
    (h : dconW.k_erec_ci p n (callW p n "erec_ci" [i, ck] m) = some (r, m')) :
    KeepPost vis fe decCIL m m' a r [ci] ∧ DcSt dn vis fe env m' a ∧ DcIdx m m' := by
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [dconW.k_erec_ci.none])
  rw [dconW.k_erec_ci.arm1] at h
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [dconW.k_sl_new1.none])
  rw [dconW.k_sl_new1.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (erecCi_specW p hP.rcp n _ i ck) h1
  obtain ⟨hS1, hg1, hci1, -⟩ := erecCiW_ok hW1 h0.stage hD hi hci
  obtain ⟨h01, hX1⟩ := h0.step0 hP.leaf dcF_eci dc0F_eci h1 hS1 h0.chk (Ext.refl _)
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (slNew1_specW p hP.alloc hP.slNew1 n _ _) h2
  obtain ⟨hdl, hS2, hg2⟩ := new1W_ci hW2 hS1 hci1
  obtain ⟨h02, hX2⟩ := h01.step0 hP.leaf dcF_new1 dc0F_new1 h2 hS2 h01.chk (Ext.refl _)
  exact ⟨⟨hS2, hg1.trans hg2, decCIL_pair hdl⟩, h02, hX1.trans hX2⟩

theorem dconW_ok {p : Prog} (hP : DeclConstsProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {env : ConLeche.Env} {i : Word} {d : IDeclaration} {n : Nat} {m m' : Mem}
    {a : AState} {r : List Word}
    (hpre : DeclConstsPre dn vis fe i d m a) (h0 : DcSt dn vis fe env m a)
    (h : dconW p n m i = some (r, m')) :
    ∃ cis a', (ConRon.Arena.declConstants d).run a = .ok (cis, a') ∧
      KeepPost vis fe decCIL m m' a' r cis ∧ DcSt dn vis fe env m' a' ∧ DcIdx m m' := by
  obtain ⟨ds, hD, hi, hdi⟩ := hpre.decls
  have hi8 : 8 * i.toNat + 9 < 2 ^ 64 := by have := hD.room; have := hD.dsize; omega
  have ek : rdW (m.arr64 DECL) (1 + 8 * i) = dw (m.arr64 DECL) i.toNat 0 :=
    rdW_dw _ hi8 (by decide) (by decide)
  rcases n with _ | n
  · simp [dconW] at h
  rw [dconW.eq_2] at h
  rw [ek] at h
  have hdecl := hpre.decl
  obtain ⟨dd, hdd⟩ := hpre.den
  cases d with
  | defnDecl cv v hint =>
    obtain ⟨hk, -⟩ := hdecl
    simp (config := { decide := true }) only [hk, ↓reduceIte] at h
    exact ⟨_, a, rfl, eciNew1 hP h0 hD hi (by rw [hdi]; rfl) h⟩
  | thmDecl cv v =>
    obtain ⟨hk, -⟩ := hdecl
    simp (config := { decide := true }) only [hk, ↓reduceIte] at h
    exact ⟨_, a, rfl, eciNew1 hP h0 hD hi (by rw [hdi]; rfl) h⟩
  | opaqueDecl cv v =>
    obtain ⟨hk, -⟩ := hdecl
    simp (config := { decide := true }) only [hk, ↓reduceIte] at h
    exact ⟨_, a, rfl, eciNew1 hP h0 hD hi (by rw [hdi]; rfl) h⟩
  | axiomDecl cv =>
    obtain ⟨hk, hcvA⟩ := hdecl
    simp (config := { decide := true }) only [hk, ↓reduceIte] at h
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hdd
    obtain ⟨c, hc, -⟩ := hdd
    obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [dconW.k_erec_ci_2.none])
    rw [dconW.k_erec_ci_2.arm1] at h
    obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [dconW.k_sl_new1.none])
    rw [dconW.k_sl_new1.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (erecCi_specW p hP.rcp n _ i 0) h1
    obtain ⟨hS1, hg1, hci1, hcv1, -⟩ := erecCiW_okA hW1 h0.stage hD hi hcvA
    obtain ⟨h01, hX1⟩ := h0.step0 hP.leaf dcF_eci dc0F_eci h1 hS1 h0.chk (Ext.refl _)
    obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
      (da_spec p hP.decl_constants_axiom n _ _) h2
    obtain ⟨cis, a2, hrun2, hK, h02, hX2⟩ := daW_ok hP h01 hpre.quotDn hci1 hcv1 hc hW2
    exact ⟨cis, a2, hrun2, ⟨hK.1, hg1.trans hK.2.1, decCIL_pair hK.2.2⟩, h02, hX1.trans hX2⟩
  | quotDecl k cv =>
    obtain ⟨hk, hcvA, hqk⟩ := hdecl
    simp (config := { decide := true }) only [hk, ↓reduceIte] at h
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hdd
    obtain ⟨c, hc, -⟩ := hdd
    obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [dconW.k_erec_ci_3.none])
    rw [dconW.k_erec_ci_3_some, dconW.j1.arm1] at h
    obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (erecCi_specW p hP.rcp n _ i 0) h1
    obtain ⟨hS1, hg1, -, hcv1, -⟩ := erecCiW_okA hW1 h0.stage hD hi hcvA
    obtain ⟨h01, hX1⟩ := h0.step0 hP.leaf dcF_eci dc0F_eci h1 hS1 h0.chk (Ext.refl _)
    have eD1 : s1.mem.arr64 DECL = m.arr64 DECL := hX1.arr _ (.inl rfl)
    have ek6 : rdW (m.arr64 DECL) (7 + 8 * i) = dw (m.arr64 DECL) i.toNat 6 :=
      rdW_dw _ hi8 (by decide) (by decide)
    rw [eD1, ek6, qSlot_eq, hqk] at h
    generalize r1.headD 0 = q at hcv1 h
    obtain ⟨wn, hwn, -, -⟩ := decCV_name hcv1
    have hqb : q.toNat + 1 < 2 ^ 64 := L.Arena.erecP_lt64 hwn
    have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [dconW.k_erec_ci.none])
    rw [dconW.k_erec_ci.arm1] at h
    obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [dconW.k_sl_new1.none])
    rw [dconW.k_sl_new1.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨ci, a2, hrun2, hT2, hg2, hd2⟩ := hP.basis.quotAt dn vis fe k (q + 1) cv n s1.mem a r2 m2
      ⟨h01.stageT, h01.chk.state, h01.chk.readOK, hpre.quotDn, by rw [hq1]; exact hcv1, c, hc⟩ h2
    have hS2 := hT2.stage
    obtain ⟨hr2, -⟩ := ConRon.Bridge.quotAt_run h01.chk.state h01.chk.readOK hc hrun2
    obtain ⟨h02, hX2⟩ := h01.step0 hP.leaf dcF_qa dc0F_qa h2 hS2 (hr2.checkOK h01.chk) hr2.ext
    obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (slNew1_specW p hP.alloc hP.slNew1 n _ _) h3
    obtain ⟨hdl, hS3, hg3⟩ := new1W_ci hW3 hS2 (decRCI_get hd2)
    obtain ⟨h03, hX3⟩ := h02.step0 hP.leaf dcF_new1 dc0F_new1 h3 hS3 h02.chk (Ext.refl _)
    refine ⟨[ci], a2, ?_, ⟨hS3, hg1.trans (hg2.trans hg3), decCIL_pair hdl⟩, h03,
      hX1.trans (hX2.trans hX3)⟩
    simp only [ConRon.Arena.declConstants, StateT.run_bind, hrun2, except_ok_bind]
    rfl
  | indDecl b nP =>
    obtain ⟨hk6, hnP, -⟩ := hdecl
    simp (config := { decide := true }) only [hk6, ↓reduceIte] at h
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hdd
    obtain ⟨bP, hbP, -⟩ := hdd
    obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [dconW.k_ind_block_to_erec.none])
    rw [dconW.k_ind_block_to_erec.arm1] at h
    obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [dconW.k_sl_new1.none])
    rw [dconW.k_sl_new1.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hS1, hg1, -, -, -, hb1, hbt1⟩ := indBlockToErec_ok hP.ibe h1 hpre.stage hpre.decl
      (hpre.front b nP rfl) hpre.dsize hpre.psize
    obtain ⟨h01, hX1⟩ := h0.step0 hP.leaf dcF_ibe dc0F_ibe h1 hS1 h0.chk (Ext.refl _)
    have eD1 : m1.arr64 DECL = m.arr64 DECL := hX1.arr _ (.inl rfl)
    have ek4 : rdW (m.arr64 DECL) (5 + 8 * i) = dw (m.arr64 DECL) i.toNat 4 :=
      rdW_dw _ hi8 (by decide) (by decide)
    rw [eD1, ek4] at h2
    obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (di_spec p hP.decl_constants_ind n _ _ _ _) h2
    obtain ⟨cis, a2, hrun2, hK, h02, hX2⟩ := diW_ok hP h01 ⟨hb1, hbt1⟩ hbP hnP hW2
    exact ⟨cis, a2, hrun2, ⟨hK.1, hg1.trans hK.2.1, decCIL_pair hK.2.2⟩, h02, hX1.trans hX2⟩

/-! ## The refinements -/

/-- **`decl_constants(i)` refines `declConstants d`**: the constants record `i` installs, in
push order, an `IW` slice of `EREC` constant records. -/
@[refines ConRon.Arena.declConstants]
theorem declConstants_refines {p : Prog} (hp : DeclConstsProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv)
    (i : Word) (d : IDeclaration) :
    RefAM p "decl_constants" [i] (DeclConstsPre dn vis fe i d) (ConRon.Arena.declConstants d)
      (fun m m' a r x => KeepPost vis fe decCIL m m' a r x ∧ IndMemos m' ∧ IdxKeep m m' ∧
        DeclTwin dn fe m' a) := by
  intro n s₀ a₀ hpre
  obtain ⟨env, h0⟩ := hpre.dcSt
  refine triple_post (callW_spec p n "decl_constants" [i] s₀) ?_
  rintro r s' ⟨hloc, hc⟩
  obtain ⟨s'', hs'', -, hW⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (dcon_spec p hp.decl_constants n _ i) hc
  rw [hs''] at hW
  obtain ⟨cis, a', hrun, hK, h1, hX⟩ := dconW_ok hp hpre h0 hW
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hloc, hok, ?_⟩
  rw [hst, hres]
  exact ⟨hK, dc_post h1 hX (flag0_of hpre.stage.check hpre.off)⟩

/-- **`decl_tables(i)` refines `declTables d`**: the projection tables record `i` installs, an
`IW` slice of `EREC` table records. -/
@[refines ConRon.Arena.declTables]
theorem declTables_refines {p : Prog} (hp : DeclConstsProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv)
    (i : Word) (d : IDeclaration) :
    RefAM p "decl_tables" [i] (DeclConstsPre dn vis fe i d) (ConRon.Arena.declTables d)
      (fun m m' a r x => KeepPost vis fe decTblL m m' a r x ∧ IndMemos m' ∧ IdxKeep m m' ∧
        DeclTwin dn fe m' a) := by
  intro n s₀ a₀ hpre
  obtain ⟨env, h0⟩ := hpre.dcSt
  refine triple_post (callW_spec p n "decl_tables" [i] s₀) ?_
  rintro r s' ⟨hloc, hc⟩
  obtain ⟨s'', hs'', -, hW⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (dt_spec p hp.decl_tables n _ i) hc
  rw [hs''] at hW
  obtain ⟨ts, a', hrun, hK, h1, hX⟩ := dtW_ok hp hpre h0 hW
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hloc, hok, ?_⟩
  rw [hst, hres]
  exact ⟨hK, dc_post h1 hX (flag0_of hpre.stage.check hpre.off)⟩

end L.Ind

end
