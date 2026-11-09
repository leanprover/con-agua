module

public import ConAgua.Arena.IndDeclConstsTable
public import ConAgua.Arena.IndDeclConstsFrame
public import ConAgua.Arena.IndDeclConstsTwin
public import ConAgua.Arena.IndRealPartsC2
public import ConAgua.Arena.DeclBasisRef
public import ConAgua.Arena.DeclAndPinIndCopy2
public import ConAgua.Arena.DeclRec
public import ConAgua.Arena.DeclBasisSpec
public import ConAgua.Arena.IndPosSpec.GgW2
import ConAgua.Arena.IndPosSpec.NestContParamsClosed
public import ConAgua.Arena.IndArmBridge2
public import ConAgua.Arena.IndInstallSpec.PartsAt
import ConAgua.Arena.IndPartsSpec.BlockSplitRecs
public import ConAgua.Arena.IndDeclConstsSpec
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Inductives.Install
import ConLeche.Verify.Inductives.BlockShapeInv
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all ConAgua.Arena.IndDeclConsts

@[expose] public section

/-!
# What a declaration installs: the refinements (lane `ronsync2`, stage 3)

`decl_constants(i)` refines con-ron's `declConstants d` and `decl_tables(i)` its `declTables d`
(`Arena/Install.lean`), at the statements of `IndDeclConstsSpec.lean`. Each L function has a
model (`dconW`, `daW`, `diW`, `dtW`: calls as `callW`, continuations in the `bkW` style); the
proofs follow the twin's arms: `erec_ci` (`erecCiW_ok`), `quot_at`/`basis_name_hit`/
`basis_at_block` (`BasisRefs`), `ind_block_to_erec` (`indBlockToErec_ok`), `block_shape`
(`blockShape_refinesC`), `block_constants` (`bkW_ok`), `block_tables` (`btsW_ok`). The frame
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

/-- After `sl_new1`/`basis_at_block`/…: the pair. -/
abbrev dcPair : Option (List Word × Mem) → Option (List Word × Mem) := bfgK4

/-- After a record: `sl_new1` of it. -/
def dcNew1 (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bfgK4 (callW p n "sl_new1" [r.headD 0] m)

/-- `decl_constants_axiom`, after the second pin (`sorryAx`). -/
def daK2 (p : Prog) (n : Nat) (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if erRd m (q + 1) = r.headD 0 then some ([0, 0], m)
      else bfgK4 (callW p n "sl_new1" [q] m)

/-- `decl_constants_axiom`, after the first pin (`Quot.sound`). -/
def daK1 (p : Prog) (n : Nat) (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if erRd m (q + 1) = r.headD 0 then dcNew1 p n (callW p n "quot_at" [4, q + 1] m)
      else daK2 p n q (callW p n "pin_at" [13] m)

/-- **The model of `decl_constants_axiom(q)`**. -/
def daW (p : Prog) : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, q => daK1 p n q (callW p n "pin_at" [4] m)

/-- `decl_constants_ind`, after `block_shape`. -/
def diK2 (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then some ([0, 0], m)
      else bfgK4 (callW p n "block_constants" [r.tail.headD 0] m)

/-- `decl_constants_ind`, after `basis_name_hit`. -/
def diK1 (p : Prog) (n : Nat) (bo bl nP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then diK2 p n (callW p n "block_shape" [nP, bo, bl] m)
      else bfgK4 (callW p n "basis_at_block" [r.tail.headD 0, bo, bl] m)

/-- **The model of `decl_constants_ind(bo, bl, nP)`**. -/
def diW (p : Prog) : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, bo, bl, nP => diK1 p n bo bl nP (callW p n "basis_name_hit" [bo, bl] m)

/-- The quotient slot of a record's kind word. -/
def qSlot (w : Word) : Word := if w = 1 then 0 else if w = 2 then 1 else if w = 3 then 2 else 3

/-- `decl_constants`, a quotient record after `erec_ci`. -/
def dcKq (p : Prog) (n : Nat) (i : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => dcNew1 p n (callW p n "quot_at" [qSlot (rdW (m.arr64 DECL) (7 + 8 * i)), r.headD 0 + 1] m)

/-- `decl_constants`, an axiom after `erec_ci`. -/
def dcKa (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bfgK4 (callW p n "decl_constants_axiom" [r.headD 0] m)

/-- `decl_constants`, an inductive block after `ind_block_to_erec`. -/
def dcKi (p : Prog) (n : Nat) (i : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bfgK4 (callW p n "decl_constants_ind"
      [r.headD 0, r.tail.headD 0, rdW (m.arr64 DECL) (5 + 8 * i)] m)

/-- **The model of `decl_constants(i)`**, by the record's kind. -/
def dconW (p : Prog) : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, i =>
    let k := rdW (m.arr64 DECL) (1 + 8 * i)
    if k = 2 then dcNew1 p n (callW p n "erec_ci" [i, 1] m)
    else if k = 3 then dcNew1 p n (callW p n "erec_ci" [i, 2] m)
    else if k = 4 then dcNew1 p n (callW p n "erec_ci" [i, 0] m)
    else if k = 1 then dcKa p n (callW p n "erec_ci" [i, 0] m)
    else if k = 5 then dcKq p n i (callW p n "erec_ci" [i, 0] m)
    else if k = 6 then dcKi p n i (callW p n "ind_block_to_erec" [i] m)
    else none

/-- `decl_tables`, after `block_shape`. -/
def dtK3 (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then some ([0, 0], m)
      else bfgK4 (callW p n "block_tables" [r.tail.headD 0, rdW (m.arr64 IW) (r.tail.headD 0),
        rdW (m.arr64 IW) (r.tail.headD 0 + 1)] m)

/-- `decl_tables`, after `basis_name_hit`. -/
def dtK2 (p : Prog) (n : Nat) (i bo bl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0
      then dtK3 p n (callW p n "block_shape" [rdW (m.arr64 DECL) (5 + 8 * i), bo, bl] m)
      else some ([0, 0], m)

/-- `decl_tables`, after `ind_block_to_erec`. -/
def dtK1 (p : Prog) (n : Nat) (i : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => dtK2 p n i (r.headD 0) (r.tail.headD 0)
      (callW p n "basis_name_hit" [r.headD 0, r.tail.headD 0] m)

/-- **The model of `decl_tables(i)`**. -/
def dtW (p : Prog) : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, i => if rdW (m.arr64 DECL) (1 + 8 * i) = 6
      then dtK1 p n i (callW p n "ind_block_to_erec" [i] m) else some ([0, 0], m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (q i bo bl nP : Word) (r : List Word)
theorem dcNew1_some : dcNew1 p n (some (r, m)) = bfgK4 (callW p n "sl_new1" [r.headD 0] m) := rfl
theorem daK2_some : daK2 p n q (some (r, m)) = if erRd m (q + 1) = r.headD 0 then some ([0, 0], m)
    else bfgK4 (callW p n "sl_new1" [q] m) := rfl
theorem daK1_some : daK1 p n q (some (r, m)) =
    if erRd m (q + 1) = r.headD 0 then dcNew1 p n (callW p n "quot_at" [4, q + 1] m)
    else daK2 p n q (callW p n "pin_at" [13] m) := rfl
theorem daW_succ : daW p (n + 1) m q = daK1 p n q (callW p n "pin_at" [4] m) := rfl
theorem diK2_some : diK2 p n (some (r, m)) = if r.headD 0 = 0 then some ([0, 0], m)
    else bfgK4 (callW p n "block_constants" [r.tail.headD 0] m) := rfl
theorem diK1_some : diK1 p n bo bl nP (some (r, m)) =
    if r.headD 0 = 0 then diK2 p n (callW p n "block_shape" [nP, bo, bl] m)
    else bfgK4 (callW p n "basis_at_block" [r.tail.headD 0, bo, bl] m) := rfl
theorem diW_succ : diW p (n + 1) m bo bl nP = diK1 p n bo bl nP (callW p n "basis_name_hit" [bo, bl] m) := rfl
theorem dcKq_some : dcKq p n i (some (r, m)) =
    dcNew1 p n (callW p n "quot_at" [qSlot (rdW (m.arr64 DECL) (7 + 8 * i)), r.headD 0 + 1] m) := rfl
theorem dcKa_some : dcKa p n (some (r, m)) = bfgK4 (callW p n "decl_constants_axiom" [r.headD 0] m) := rfl
theorem dcKi_some : dcKi p n i (some (r, m)) = bfgK4 (callW p n "decl_constants_ind"
      [r.headD 0, r.tail.headD 0, rdW (m.arr64 DECL) (5 + 8 * i)] m) := rfl
theorem dtK3_some : dtK3 p n (some (r, m)) = if r.headD 0 = 0 then some ([0, 0], m)
      else bfgK4 (callW p n "block_tables" [r.tail.headD 0, rdW (m.arr64 IW) (r.tail.headD 0),
        rdW (m.arr64 IW) (r.tail.headD 0 + 1)] m) := rfl
theorem dtK2_some : dtK2 p n i bo bl (some (r, m)) = if r.headD 0 = 0
      then dtK3 p n (callW p n "block_shape" [rdW (m.arr64 DECL) (5 + 8 * i), bo, bl] m)
      else some ([0, 0], m) := rfl
theorem dtK1_some : dtK1 p n i (some (r, m)) = dtK2 p n i (r.headD 0) (r.tail.headD 0)
      (callW p n "basis_name_hit" [r.headD 0, r.tail.headD 0] m) := rfl
theorem dtW_succ : dtW p (n + 1) m i = if rdW (m.arr64 DECL) (1 + 8 * i) = 6
      then dtK1 p n i (callW p n "ind_block_to_erec" [i] m) else some ([0, 0], m) := rfl
end arms
attribute [ind_grind] dcNew1_some daK2_some daK1_some daW_succ diK2_some diK1_some diW_succ dcKq_some
  dcKa_some dcKi_some dtK3_some dtK2_some dtK1_some dtW_succ

/-! ## The specs -/

theorem da_spec (p : Prog) (hp : p.lookup "decl_constants_axiom" = some declConstantsAxiom) (n : Nat)
    (s₀ : St) (q : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "decl_constants_axiom" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ daW p n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, declConstantsAxiom]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "pin_at", callW_spec p n "quot_at", callW_spec p n "sl_new1"] <;>
      finish (gen := 20) [erRd, rdW_eq]

theorem di_spec (p : Prog) (hp : p.lookup "decl_constants_ind" = some declConstantsInd) (n : Nat)
    (s₀ : St) (bo bl nP : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "decl_constants_ind" [bo, bl, nP]
    ⦃fun r s' => LocEq s' s₀ ∧ diW p n s₀.mem bo bl nP = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, declConstantsInd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "basis_name_hit", callW_spec p n "basis_at_block",
        callW_spec p n "block_shape", callW_spec p n "block_constants"] <;>
      finish (gen := 20) [rdW_eq]

theorem dcon_spec (p : Prog) (hp : p.lookup "decl_constants" = some declConstants) (n : Nat)
    (s₀ : St) (i : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "decl_constants" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ dconW p n s₀.mem i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, declConstants]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "erec_ci", callW_spec p n "sl_new1", callW_spec p n "decl_constants_axiom",
        callW_spec p n "quot_at", callW_spec p n "ind_block_to_erec",
        callW_spec p n "decl_constants_ind"] <;>
      finish (gen := 20) [dconW, qSlot, rdW_eq]

theorem dt_spec (p : Prog) (hp : p.lookup "decl_tables" = some declTables) (n : Nat)
    (s₀ : St) (i : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "decl_tables" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ dtW p n s₀.mem i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, declTables]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "ind_block_to_erec", callW_spec p n "basis_name_hit",
        callW_spec p n "block_shape", callW_spec p n "block_tables"] <;>
      finish (gen := 20) [rdW_eq]


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

theorem DcSt.abs {m : Mem} {a : AState} (h : DcSt dn vis fe env m a) : AbsOK m :=
  ⟨h.mem.ab, h.i1, h.mem.cr, h.mem.il, h.mem.wk⟩

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
their callees'), the pinned basis blocks' refinements (`BasisRefs`), the write set's leaves
(`DcLeafProg`), `ind_block_to_erec`'s, `block_shape`'s (`IndPartsProg5`, `CoreStageClosed`,
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
theorem dcF_bnh : "basis_name_hit" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_bsh : "block_shape" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_bts : "block_tables" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_bk : "block_constants" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_bab : "basis_at_block" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_eci : "erec_ci" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_qa : "quot_at" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_new1 : "sl_new1" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_pin : "pin_at" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_dca : "decl_constants_axiom" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dcF_dci : "decl_constants_ind" ∈ dcFns := List.elem_iff.mp (by decide)
theorem dc0F_ibe : "ind_block_to_erec" ∈ dc0Fns := List.elem_iff.mp (by decide)
theorem dc0F_bnh : "basis_name_hit" ∈ dc0Fns := List.elem_iff.mp (by decide)
theorem dc0F_bsh : "block_shape" ∈ dc0Fns := List.elem_iff.mp (by decide)
theorem dc0F_bk : "block_constants" ∈ dc0Fns := List.elem_iff.mp (by decide)
theorem dc0F_bab : "basis_at_block" ∈ dc0Fns := List.elem_iff.mp (by decide)
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
  rw [dtW_succ, ek] at h
  have hdecl := hpre.decl
  rcases (Classical.em (∃ b nP, d = .indDecl b nP)).symm with hd | hd
  · have hk : dw (m.arr64 DECL) i.toNat 0 ≠ 6 := by
      cases d with
      | indDecl b nP => exact absurd ⟨b, nP, rfl⟩ hd
      | _ => simp only [L.Front.DeclAtF, L.Front.DeclAt] at hdecl; rw [hdecl.1]; decide
    rw [ite_eq_right hk] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨[], a, ?_, ⟨hpre.stage, IWGrow.refl m, decTblL_nil _⟩, h0, DcIdx.refl m⟩
    cases d with
    | indDecl b nP => exact absurd ⟨b, nP, rfl⟩ hd
    | _ => rfl
  obtain ⟨b, nP, rfl⟩ := hd
  obtain ⟨hk6, hnP, -⟩ := hdecl
  rw [ite_eq_left hk6] at h
  obtain ⟨bP, hbP⟩ : ∃ bP, Frontend.denoteCIList a.store b = some bP := by
    obtain ⟨dd, hd⟩ := hpre.den
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨bP, hb, -⟩ := hd
    exact ⟨bP, hb⟩
  -- `ind_block_to_erec`
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [dtK1])
  rw [dtK1_some] at h
  obtain ⟨hS1, hg1, -, -, -, hb1, hbt1⟩ := indBlockToErec_ok hP.ibe h1 hpre.stage hpre.decl
    (hpre.front b nP rfl) hpre.dsize hpre.psize
  obtain ⟨h01, hX1⟩ := h0.step0 hP.leaf dcF_ibe dc0F_ibe h1 hS1 h0.chk (Ext.refl _)
  -- `basis_name_hit`
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [dtK2])
  rw [dtK2_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2⟩ := hP.basis.nameHit vis fe _ _ b n m1 a r2 m2
    ⟨hS1, hpre.ok, hb1, hbt1⟩ h2
  obtain ⟨hst2, hxt2, hp2, hc2, -, -, -⟩ := ConRon.Bridge.basisNameHit_run hpre.ok hbP hrun2
  have hchk2 := h01.chk.mono hst2 hxt2 hc2 hp2
  obtain ⟨h02, hX2⟩ := h01.step0 hP.leaf dcF_bnh dc0F_bnh h2 hS2 hchk2 hxt2
  have hbP2 := ConRon.Bridge.denoteCIList_mono hxt2 _ _ hbP
  cases x2 with
  | some kind =>
    obtain ⟨e1, -⟩ := hx2
    rw [e1, ite_eq_right (by decide)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨[], a2, ?_, ⟨hS2, hg1.trans hg2, decTblL_nil _⟩, h02, hX1.trans hX2⟩
    simp only [ConRon.Arena.declTables, StateT.run_bind, hrun2, except_ok_bind]
    rfl
  | none =>
  have e0 : r2.headD 0 = 0 := hx2
  rw [e0, ite_eq_left rfl] at h
  -- `block_shape`
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [dtK3])
  rw [dtK3_some] at h
  have eD : m2.arr64 DECL = m.arr64 DECL := (hX1.trans hX2).arr _ (.inl rfl)
  have ew : rdW (m2.arr64 DECL) (5 + 8 * i) = dw (m.arr64 DECL) i.toNat 4 := by
    rw [eD]; exact rdW_dw _ hi8 (by decide) (by decide)
  rw [ew] at h3
  have hblk : DecB (fun m => decEBlk dn m (r1.headD 0).toNat (r1.tail.headD 0).toNat) m2 b :=
    (decB_decEBlk_of_decCIs hb1).grow (decEBlk_mono dn _ _) hg2
  obtain ⟨s3, hs3, -, hok3, hR3, hS3, hg3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (blockShape_refinesC p hP.hcl hP.hL hP.parts n ⟨m2, Locals.init []⟩ a2 _ _ _ b h02.stageC
      h02.abs hbP2 hblk) (callW_mono h3 (Nat.le_add_right n 5))
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hnP] at hrun3 hR3 hS3
  generalize AM.res (ConRon.Arena.blockShape? nP b) a2 = x3 at hrun3 hR3
  generalize AM.st (ConRon.Arena.blockShape? nP b) a2 = a3 at hrun3 hS3
  obtain ⟨hps3, -, hq3⟩ := ConRon.Bridge.Inductives.blockShape?_installS h02.chk hbP2 hrun3
  obtain ⟨h03, hX3⟩ := h02.step0 hP.leaf dcF_bsh dc0F_bsh h3 hS3
    (checkOK_of_pstep h02.chk hps3) hps3.ext
  cases x3 with
  | none =>
    have e3 : r3.headD 0 = 0 := hR3
    rw [e3, ite_eq_left rfl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨[], a3, ?_, ⟨hS3, hg1.trans (hg2.trans hg3), decTblL_nil _⟩, h03,
      hX1.trans (hX2.trans hX3)⟩
    simp only [ConRon.Arena.declTables, StateT.run_bind, hrun2, except_ok_bind, hrun3]
    rfl
  | some bs =>
  obtain ⟨e3, hq, -⟩ := hR3
  rw [e3, ite_eq_right (by decide)] at h
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
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [bfgK4])
  rw [bfgK4_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (bts_spec hP.toTablesProg n _ pp o l) h4
  -- the parameter count
  simp only [ConRon.Bridge.Inductives.ROp] at hq3
  obtain ⟨pP, hpP, hdP⟩ := hq3
  have hbnP : bs.nP = nP := ((ConRon.Bridge.Inductives.dShape_inv hdP).2.2.1).trans
    (ConLeche.blockShape?_inv hpP).1
  have hnPb : 1 + bs.nP < 2 ^ 64 := by rw [hbnP]; have := hpre.nPb b nP rfl; omega
  obtain ⟨ts, a4, hrun4, hd4, hb4, hS4, hg4, hA4⟩ := btsW_ok hP.toTablesProg pp bs vis fe hnPb n
    s3.mem s4.mem a3 o l bs.members r4 hS3 h03.abs hq ⟨hdm, hob⟩ hW4
  obtain ⟨hms, -⟩ := ConRon.Bridge.Inductives.dShape_inv hdP
  obtain ⟨hps4, -, -, -⟩ := ConRon.Bridge.Inductives.blockTables_run bs.members pP.members
    h03.chk.state hdP hms hrun4
  obtain ⟨h04, hX4⟩ := h03.step hP.leaf dcF_bts h4 hS4 (checkOK_of_pstep h03.chk hps4)
    hps4.ext hA4.i1
  refine ⟨ts, a4, ?_, ⟨hS4, hg1.trans (hg2.trans (hg3.trans hg4)), ?_⟩, h04,
    hX1.trans (hX2.trans (hX3.trans hX4))⟩
  · simp only [ConRon.Arena.declTables, StateT.run_bind, hrun2, except_ok_bind, hrun3, hrun4]
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

theorem BlockAt.grow {o l : Word} {b : List IConstantInfo} {m m' : Mem} (h : BlockAt o l b m)
    (hg : IWGrow m m') : BlockAt o l b m' := by
  have hb := (decB_decEBlk_of_decCIs (dn := fun _ => none) h.1).grow (decEBlk_mono _ _ _) hg
  exact ⟨hb.get (decEBlk_mono _ _ _), Nat.le_trans h.2 hg.er⟩

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
  rw [diW_succ] at h
  -- `basis_name_hit`
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [diK1])
  rw [diK1_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2⟩ := hP.basis.nameHit vis fe bo bl b n m a r2 m2
    ⟨h0.stage, h0.chk.state, hblk⟩ h2
  obtain ⟨hst2, hxt2, hp2, hc2, -, -, -⟩ := ConRon.Bridge.basisNameHit_run h0.chk.state hbP hrun2
  have hchk2 := h0.chk.mono hst2 hxt2 hc2 hp2
  obtain ⟨h02, hX2⟩ := h0.step0 hP.leaf dcF_bnh dc0F_bnh h2 hS2 hchk2 hxt2
  have hbP2 := ConRon.Bridge.denoteCIList_mono hxt2 _ _ hbP
  have hblk2 := hblk.grow hg2
  cases x2 with
  | some kind =>
    obtain ⟨e1, hk4, hkind⟩ := hx2
    rw [e1, ite_eq_right (by decide)] at h
    obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [bfgK4])
    rw [bfgK4_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨cis, a3, hrun3, ⟨⟨hS3, hg3, hd3, -⟩, hb3⟩⟩ := hP.basis.atBlock dn vis fe _ bo bl b hk4
      n m2 a2 r3 m3 ⟨hS2, hst2, hblk2⟩ h3
    rw [hkind] at hrun3
    obtain ⟨hr3, -⟩ := ConRon.Bridge.BasisKind.atBlock_run hst2 hchk2.readOK hbP2 hrun3
    obtain ⟨h03, hX3⟩ := h02.step0 hP.leaf dcF_bab dc0F_bab h3 hS3 (hr3.checkOK hchk2) hr3.ext
    refine ⟨cis, a3, ?_, ⟨hS3, hg2.trans hg3, ?_⟩, h03, hX2.trans hX3⟩
    · simp only [ConRon.Arena.declConstants, StateT.run_bind, hrun2, except_ok_bind, hrun3]
    · have hg := hd3.get (basisDec_mono dn _ _)
      exact ⟨by simpa [basisDec, erA] using hg, by simpa using hb3⟩
  | none =>
  have e0 : r2.headD 0 = 0 := hx2
  rw [e0, ite_eq_left rfl] at h
  -- `block_shape`
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [diK2])
  rw [diK2_some] at h
  have hblk' : DecB (fun m => decEBlk dn m bo.toNat bl.toNat) m2 b :=
    decB_decEBlk_of_decCIs hblk2.1
  obtain ⟨s3, hs3, -, hok3, hR3, hS3, hg3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (blockShape_refinesC p hP.hcl hP.hL hP.parts n ⟨m2, Locals.init []⟩ a2 _ _ _ b h02.stageC
      h02.abs hbP2 hblk') (callW_mono h3 (Nat.le_add_right n 5))
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hw] at hrun3 hR3 hS3
  generalize AM.res (ConRon.Arena.blockShape? nP b) a2 = x3 at hrun3 hR3
  generalize AM.st (ConRon.Arena.blockShape? nP b) a2 = a3 at hrun3 hS3
  obtain ⟨hps3, -, hq3⟩ := ConRon.Bridge.Inductives.blockShape?_installS h02.chk hbP2 hrun3
  obtain ⟨h03, hX3⟩ := h02.step0 hP.leaf dcF_bsh dc0F_bsh h3 hS3
    (checkOK_of_pstep h02.chk hps3) hps3.ext
  cases x3 with
  | none =>
    have e3 : r3.headD 0 = 0 := hR3
    rw [e3, ite_eq_left rfl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨[], a3, ?_, ⟨hS3, hg2.trans hg3, decCIL_nil _⟩, h03, hX2.trans hX3⟩
    simp only [ConRon.Arena.declConstants, StateT.run_bind, hrun2, except_ok_bind, hrun3]
    rfl
  | some bs =>
  obtain ⟨e3, hq, hsl⟩ := hR3
  rw [e3, ite_eq_right (by decide)] at h
  generalize r3.tail.headD 0 = pp at hq hsl h
  -- `block_constants`
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [bfgK4])
  rw [bfgK4_some] at h
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
  refine ⟨cis, a4, ?_, ⟨hS4, hg2.trans (hg3.trans hg4), ⟨by simpa using hd4, by simpa using hb4⟩⟩,
    h04, hX2.trans (hX3.trans hX4)⟩
  simp only [ConRon.Arena.declConstants, StateT.run_bind, hrun2, except_ok_bind, hrun3, hrun4]

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
  sorry

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
