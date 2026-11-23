module

public import ConAgua.Arena.IndexLoops
public import ConAgua.Arena.IndDeclConstsRef
public import ConRon.Bridge.Checker.Index
public import ConAgua.Arena.DeclPins
public import ConAgua.Arena.IndexFreeze
import ConRon.Bridge.Checker.Install
import ConAgua.Arena.IndRealAbsT
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.CheckerL

@[expose] public section

/-!
# The stream index: `idx_add`, `build_index`

`idx_add(k)` is `IStreamIndex.add` of record `k` (the work pool emptied, `FIRSTS[k]` the next
counter, the record's constants and tables read off it and inserted); `build_index(cnt)` is
`buildIndexGo` over the records `0‥cnt - 1`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

/-- **`idx_add` is its model `idxAddW`** (generated). -/
l_model idxAdd_specW (p : Prog) (hp : p.lookup "idx_add" = some idxAddL)
  fns [hp ↦ idxAddW list]
  specs [callW_spec p n "iw_reset", callW_spec p n "decl_constants", callW_spec p n "idx_consts",
    callW_spec p n "decl_tables", callW_spec p n "idx_tables"]
  grind [arena_grind] bind ntBW

/-- **`build_index` is its model `buildIndexW`** (generated). -/
l_model buildIndex_specW (p : Prog) (hp : p.lookup "build_index" = some buildIndexL)
  fns [hp ↦ buildIndexW list]
  specs [callW_spec p n "str_lit_names", callW_spec p n "idx_add", callW_spec p n "index_freeze"]
  grind [arena_grind] bind ntBW

/-! ## The relations -/

/-- The literal names of the driver's environment at the pins `P` (`driverFE`, the twin's
`mkIFEnvLits`): `build_index` writes them into `CTL[162‥171]` first (`str_lit_names`). -/
def drvLits (P : Pins) : List NIdx := (ConRon.Bridge.driverFE P).base.lits

/-- The environment the stream index's builder runs at: the index's base layer, below `c` and
record position `r`, no own constants, the literal flags off and the pins' literal names
(`drvLits`, as the driver's environment). -/
def bEnv (b : IFBase) (P : Pins) (c r : Nat) : IFEnv :=
  ⟨⟨[], []⟩, {}, { b with below := c, belowRec := r, lits := drvLits P }, {}, false, false⟩

/-- **`IndexR` across a memory that keeps the index rows (arrays `129‥134`), `FIRSTS` and
`CTL[128]`**, and whose record pool extends the old one. -/
theorem IndexR.grow {m m' : Mem} {I : IStreamIndex} (h : IndexR m I)
    (hA : ∀ b : TieredArray, b.hi = false → ((129 ≤ b.arr ∧ b.arr ≤ 134) ∨ b.arr = 137) →
      m'.arr64 b = m.arr64 b)
    (h128 : rdW (m'.arr64 CTL) 128 = rdW (m.arr64 CTL) 128) (hx : ArrExt (erecP m) (erecP m')) :
    IndexR m' I := by
  have hb : ∀ w, baseRow m' w = baseRow m w := fun w => by
    simp only [baseRow, hA (eixArr (rowTag w) : TieredArray)
      (by unfold eixArr; split <;> (try split) <;> decide)
      (by unfold eixArr; split <;> (try split) <;> decide)]
  have hbt : ∀ w, baseTbl m' w = baseTbl m w := fun w => by
    simp only [baseTbl, hA (tixArr (rowTag w) : TieredArray)
      (by unfold tixArr; split <;> (try split) <;> decide)
      (by unfold tixArr; split <;> (try split) <;> decide)]
  have hF : m'.arr64 FIRSTS = m.arr64 FIRSTS := hA _ (by decide) (by decide)
  refine ⟨fun n => ?_, fun n => ?_, fun i hi => by rw [hF]; exact h.firsts i hi,
    by rw [hF]; exact h.firstsSize, by rw [h128]; exact h.next, fun x hx => by rw [hb]; exact h.rows x hx⟩
  · have := h.base n; rw [hb, this]; split
    · rfl
    · cases e : I.base.idx[n]? with
      | none => rw [e] at this; simp_all
      | some y =>
        rw [e] at this
        simp only [Option.map_some, ite_eq_right_of_eq_false _ _ (eq_false ‹_›), Option.some.injEq,
          Prod.mk.injEq] at this
        rw [← this.2, hx.decCI this.2.symm]
  · have := h.btbl n; rw [hbt, this]; split
    · rfl
    · cases e : I.base.tbls[n]? with
      | none => rw [e] at this; simp_all
      | some y =>
        rw [e] at this
        simp only [Option.map_some, ite_eq_right_of_eq_false _ _ (eq_false ‹_›), Option.some.injEq,
          Prod.mk.injEq] at this
        rw [← this.2, hx.decTbl this.2.symm]

/-- `fe` with the base layer `b` (its bounds and literal names kept). -/
def _root_.ConRon.Arena.IFEnv.rebase (fe : IFEnv) (b : IFBase) : IFEnv :=
  ⟨fe.env, fe.idx, { b with below := fe.base.below, belowRec := fe.base.belowRec, lits := fe.base.lits },
    fe.tbls, fe.natLit, fe.strLit⟩

/-- The pins' literal names (`pinLits`, as `str_lit_names` reads them) are the driver's
(`drvLits`) at a filled pin table. -/
theorem pinLits_drv {m : Mem} {P : Pins} (hF : PinsFull m P) : pinLits m = drvLits P := by
  unfold pinLits drvLits
  simp only [ConRon.Bridge.driverFE, IFEnv.ofParts, PIN_NAT, PIN_NAT_ZERO, PIN_NAT_SUCC, PIN_STRING,
    PIN_STRING_OF_LIST, PIN_LIST, PIN_LIST_NIL, PIN_LIST_CONS, PIN_CHAR, PIN_CHAR_OF_NAT]
  apply List.map_congr_left
  intro i hi
  have hi' : i < 51 := by simp at hi; omega
  have hs : i < P.names.size := by rw [hF.names_size]; omega
  simp only [Array.getD, hs, dite_true]
  exact (hF.names i hi').symm

theorem bEnv_rebase (b b' : IFBase) (P : Pins) (c r : Nat) : (bEnv b P c r).rebase b' = bEnv b' P c r := rfl

/-! ## The twin-side invariants at an environment that sees nothing

The builder runs at `bEnv I.base P 0 0`: no constant and no table is visible, as at the driver's
empty environment (`DriverOK`'s `driverFE`). The twin-side invariants (`TwinOK`,
`CheckOK`) read the environment through `find?` and `findTable?` alone. -/

theorem bEnv_find_zero (b : IFBase) (P : Pins) (n : NIdx) : (bEnv b P 0 0).find? n = none := by
  simp only [bEnv, IFEnv.find?, IFEnv.lookup, IFBase.find?]
  simp only [Std.HashMap.isEmpty_empty, ite_true]
  split <;> simp

theorem bEnv_findTable_zero (b : IFBase) (P : Pins) (n : NIdx) : (bEnv b P 0 0).findTable? n = none := by
  simp [IFEnv.findTable?, bEnv_find_zero]

theorem bEnv_litsStored (b : IFBase) (P : Pins) (i stop : Nat) (hi : i < stop) :
    (bEnv b P 0 0).litsStored i stop = false := by
  rw [IFEnv.litsStored.eq_1, ite_eq_right_of_eq_false _ _ (by simp; omega)]
  split
  · rw [bEnv_find_zero]
  · rfl

/-- The builder's environment's flags are its lookups' (none: it sees nothing). -/
theorem bEnv_flags (b : IFBase) (P : Pins) : ConRon.Bridge.FlagsOK (bEnv b P 0 0) :=
  ⟨by rw [IFEnv.natLitStoredBy, bEnv_litsStored _ _ _ _ (by decide)]; rfl,
   by rw [IFEnv.strLitStoredBy, IFEnv.natLitStoredBy, bEnv_litsStored _ _ _ _ (by decide)]; rfl⟩

theorem emptyEnv_find (P : Pins) (n : NIdx) : (ConRon.Bridge.driverFE P).find? n = none := by
  simp [ConRon.Bridge.driverFE, IFEnv.ofParts, IFEnv.find?, IFEnv.lookup, IFBase.find?]

theorem emptyEnv_findTable (P : Pins) (n : NIdx) : (ConRon.Bridge.driverFE P).findTable? n = none := by
  simp [IFEnv.findTable?, emptyEnv_find]

theorem _root_.L.Arena.StoreDen.congrFe {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState}
    {fe fe' : IFEnv} (hf : ∀ n, fe'.find? n = fe.find? n) (ht : ∀ n, fe'.findTable? n = fe.findTable? n)
    (h : StoreDen dn m a fe) : StoreDen dn m a fe' :=
  { h with
    constLps := fun c ci e => h.constLps c ci ((hf c).symm.trans e)
    proj := fun c t e => h.proj c t ((ht c).symm.trans e)
    recRules := fun c cv mI rP isK rules e => h.recRules c cv mI rP isK rules ((hf c).symm.trans e)
    recLevels := fun c cv mI rP isK rules e => h.recLevels c cv mI rP isK rules ((hf c).symm.trans e) }

theorem _root_.L.Arena.TwinOK.congrFe {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState}
    {fe fe' : IFEnv} (hf : ∀ n, fe'.find? n = fe.find? n) (ht : ∀ n, fe'.findTable? n = fe.findTable? n)
    (h : TwinOK dn m a fe) : TwinOK dn m a fe' :=
  { h with den := h.den.congrFe hf ht }

theorem checkOK_congrFe {eager : Bool} {env : ConLeche.Env} {a : AState} {fe fe' : IFEnv}
    (hf : ∀ n, fe'.find? n = fe.find? n) (ht : ∀ n, fe'.findTable? n = fe.findTable? n)
    (hfl : ConRon.Bridge.FlagsOK fe') (hl : fe'.base.lits = fe.base.lits)
    (h : ConRon.Bridge.CheckOK eager env fe a) : ConRon.Bridge.CheckOK eager env fe' a :=
  { h with
    ienv := { hit := fun n ci e => h.ienv.hit n ci ((hf n).symm.trans e)
              cover := fun nm c e => let ⟨n, ci, h1, h2, h3⟩ := h.ienv.cover nm c e; ⟨n, ci, h1, (hf n).trans h2, h3⟩
              tblHit := fun n t e => h.ienv.tblHit n t ((ht n).symm.trans e)
              tblCover := fun nm pt e => let ⟨n, t, h1, h2, h3⟩ := h.ienv.tblCover nm pt e; ⟨n, t, h1, (ht n).trans h2, h3⟩
              flags := hfl
              lits := by unfold ConRon.Bridge.LitsOK; rw [hl]; exact h.ienv.lits } }

/-- `TwinOK` from one base layer's empty view to another's. -/
theorem _root_.L.Arena.TwinOK.bEnv0 {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState}
    {b : IFBase} {P : Pins} (b' : IFBase) (h : TwinOK dn m a (bEnv b P 0 0)) : TwinOK dn m a (bEnv b' P 0 0) :=
  h.congrFe (fun n => by rw [bEnv_find_zero, bEnv_find_zero])
    (fun n => by rw [bEnv_findTable_zero, bEnv_findTable_zero])

/-- **`DeclTwin` in the builder**: the twin-side invariants at the empty view, from `TwinOK`, the
pin flag, the inductive memos and the driver's invariant. -/
theorem declTwin_of {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {b : IFBase}
    {P : Pins} (hT : TwinOK dn m a (bEnv b P 0 0)) (hp : pinW m 0 ≠ 0) (hM : IndMemos m)
    (hd : ConRon.Bridge.DriverOK a) (hP : a.pins = P) : L.Ind.DeclTwin dn (bEnv b P 0 0) m a :=
  ⟨hT, hp, hT.absOK hM.i1 hM.cr hp, ⟨_, checkOK_congrFe
    (fun n => by rw [bEnv_find_zero, emptyEnv_find])
    (fun n => by rw [bEnv_findTable_zero, emptyEnv_findTable]) (bEnv_flags _ _) (by rw [hP]; rfl) hd⟩⟩

/-- The stream index's row arrays. -/
def IdxA : List TieredArray := EixA ++ TixA

theorem idxA_range : ∀ b ∈ IdxA, b.hi = false ∧ 129 ≤ b.arr ∧ b.arr ≤ 134 := by decide

/-- **`EnvR` at a new base layer**: a memory changed only in the index rows and `CTL[128]`, whose
index rows are `I`'s, is in `EnvR` at the environment with `I`'s base layer (the own layer and the
bounds unchanged). -/
theorem EnvR.rebase {m m' : Mem} {vis : Word} {fe : IFEnv} {I : IStreamIndex} {A : List TieredArray}
    {C : List Word} (h : EnvR m vis fe) (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b ∈ IdxA)
    (hC : ∀ x ∈ C, x = 128) (hI : IndexR m' I) :
    EnvR m' vis (fe.rebase I.base) := by
  have hc : ∀ x : Word, x ≠ 128 → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x :=
    fun x hx => hf.ctl x (fun hm => hx (hC x hm))
  have ha : ∀ b : TieredArray, b ∉ IdxA → b ≠ CTL → m'.arr64 b = m.arr64 b := fun b hb hb2 =>
    hf.arr b (fun hm => hb (hA b hm)) hb2
  have hs : stampW m' = stampW m := hc 133 (by decide)
  have hP : erecP m' = erecP m :=
    erecP_congr' (ha _ (by decide) (by decide)) (ha _ (by decide) (by decide)) (hc 129 (by decide)) (hc 130 (by decide))
  have o1 : ∀ g t, tierA (oixArr g) t ∉ IdxA ∧ tierA (oixArr g) t ≠ CTL := fun g t => by
    unfold tierA oixArr; generalize (t &&& 1 != 0) = b
    cases b <;> split <;> (try split) <;> decide
  have o2 : ∀ g t, tierA (otxArr g) t ∉ IdxA ∧ tierA (otxArr g) t ≠ CTL := fun g t => by
    unfold tierA otxArr; generalize (t &&& 1 != 0) = b
    cases b <;> split <;> (try split) <;> decide
  have hor : ∀ w, ownRow m' w = ownRow m w := fun w => by
    simp only [ownRow, ha _ (o1 _ _).1 (o1 _ _).2]
  have hraw : ∀ w, ownRaw m' w = ownRaw m w := fun w => by simp only [ownRaw, hor, hs]
  have hot : ∀ w, ownTbl m' w = ownTbl m w := fun w => by simp only [ownTbl, ha _ (o2 _ _).1 (o2 _ _).2, hs]
  refine ⟨fun n => ?_, fun n hn => ?_, fun n hn => ?_, fun n n' hn hq => ?_, fun n => ?_,
    fun n hn => ?_, ?_, ?_, fun n => hI.base n, fun n => hI.btbl n, by rw [hs]; exact h.stamp, fun w hw => by
      rw [hor, hs, ha _ (o2 _ _).1 (o2 _ _).2]; exact h.ownBelow w hw, ?_, ?_, ?_⟩
  · show fe.idx[n]? = _; rw [h.own n]; simp only [ownFind, hraw, hP]
  · rw [hraw] at hn ⊢; rw [hP]; exact h.own_dec n hn
  · rw [hraw] at hn ⊢; exact h.fresh n hn
  · rw [hraw, hraw] at hq; rw [hraw] at hn; exact h.uniq n n' hn hq
  · show fe.tbls[n]? = _; rw [h.otbl n, hot, hP]
  · rw [hot] at hn ⊢; rw [hP]; exact h.otbl_dec n hn
  · rw [hc 134 (by decide)]; exact h.below
  · rw [hc 135 (by decide)]; exact h.belowRec
  · rw [hc 160 (by decide)]; exact h.natLit
  · rw [hc 161 (by decide)]; exact h.strLit
  · rw [litWords_congr (fun i hi => hc _ (by
      intro e; have := congrArg UInt64.toNat e; simp at this; omega))]; exact h.lits

/-- **`EnvR` across the literal names' writes** (`str_lit_names`: `CTL[162‥171]`): the
environment with the names `L` the new words. -/
theorem EnvR.relits {m m' : Mem} {vis : Word} {fe : IFEnv} {L : List NIdx}
    (h : EnvR m vis fe) (hf : MemFrame [] litCtl m m') (hl : L.map (·.word.toUInt64) = litWords m') :
    EnvR m' vis { fe with base := { fe.base with lits := L } } := by
  have he : ∀ b ∈ envArrs, m'.arr64 b = m.arr64 b := fun b hb =>
    hf.arr b (by simp) (fun e => by subst e; revert hb; decide)
  have hc : ∀ x : Word, x.toNat < 162 → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x := fun x hx' =>
    hf.ctl x (fun hx => by simp only [litCtl, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with h | h | h | h | h | h | h | h | h | h <;> subst h <;> exact absurd hx' (by decide))
  have hP : erecP m' = erecP m := by
    funext i
    simp only [erecP, erTop, erecTop1, he EREC (by decide), he (tier1 EREC) (by decide),
      hc 129 (by decide), hc 130 (by decide)]
    rfl
  have hs : stampW m' = stampW m := hc 133 (by decide)
  have hor : ∀ w, ownRow m' w = ownRow m w := fun w => by
    simp only [ownRow, he _ (tierA_oix_mem _ _)]
  have hraw : ∀ w, ownRaw m' w = ownRaw m w := fun w => by simp only [ownRaw, hor, hs]
  have hfind : ∀ w, ownFind m' vis w = ownFind m vis w := fun w => by
    simp only [ownFind, hraw, hP]
  have hot : ∀ w, ownTbl m' w = ownTbl m w := fun w => by
    simp only [ownTbl, he _ (tierA_otx_mem _ _), hs]
  have hb : ∀ w, baseRow m' w = baseRow m w := fun w => by
    simp only [baseRow, he _ (eix_mem _)]
  have hbt : ∀ w, baseTbl m' w = baseTbl m w := fun w => by
    simp only [baseTbl, he _ (tix_mem _)]
  exact ⟨fun n => by rw [hfind]; exact h.own n, fun n => by rw [hraw, hP]; exact h.own_dec n,
    fun n => by rw [hraw]; exact h.fresh n, fun n n' => by rw [hraw, hraw]; exact h.uniq n n',
    fun n => by rw [hot, hP]; exact h.otbl n, fun n => by rw [hot, hP]; exact h.otbl_dec n,
    by rw [hc 134 (by decide)]; exact h.below,
    by rw [hc 135 (by decide)]; exact h.belowRec,
    fun n => by rw [hb, hP]; exact h.base n, fun n => by rw [hbt, hP]; exact h.btbl n,
    by rw [hs]; exact h.stamp, fun w hw => by
      rw [hor, hs, he _ (tierA_otx_mem _ _)]; exact h.ownBelow w hw,
    by rw [hc 160 (by decide)]; exact h.natLit, by rw [hc 161 (by decide)]; exact h.strLit, hl⟩

/-- **`StageR` across the literal names' writes**, at the environment the new memory relates. -/
theorem _root_.L.Ind.StageR.of_lits {vis vis' : Word} {fe fe' : IFEnv} {a : AState} {m m' : Mem}
    (hS : StageR vis fe m a) (hf : MemFrame [] litCtl m m') (hE : EnvR m' vis' fe') :
    StageR vis' fe' m' a ∧ IWGrow m m' := by
  have hA3 : (IW : TieredArray) ∉ ([] : List TieredArray) ∧ (EREC : TieredArray) ∉ ([] : List TieredArray) ∧
      tier1 EREC ∉ ([] : List TieredArray) := by simp
  have hC3 : (129 : Word) ∉ litCtl ∧ (130 : Word) ∉ litCtl ∧ (200 : Word) ∉ litCtl := by decide
  refine ⟨⟨⟨⟨ArenaR.frame (fun b hb => by simp at hb) (fun x hx => not_mem_arenaCtl x (by
      simp only [litCtl, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide)) hf hS.check.arena.base,
      DerR.frameM _ _ m _ hf (fun b hb => by simp at hb) a hS.check.arena.der⟩,
    hS.check.core.frame (fun b hb => by simp at hb) (fun x hx => by simp only [litCtl, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide) hf,
    hS.check.pins.frame (fun b hb => by simp at hb) hf, hE,
    hS.check.mode.frame hf (by decide) (by decide)⟩, IWOK.of_keep hf hA3 hC3 hS.iw⟩,
    IWGrow.of_keep hf hA3 hC3⟩

/-- **`CheckR` at a new base layer** (`EnvR.rebase`): the arena, the core, the pins and the mode
read none of the index rows or `CTL[128]`. -/
theorem CheckR.rebase {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} {I : IStreamIndex}
    {A : List TieredArray} {C : List Word} (h : CheckR m a vis fe) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b ∈ IdxA) (hC : ∀ x ∈ C, x = 128) (hI : IndexR m' I) :
    CheckR m' a vis (fe.rebase I.base) := by
  have hI' : ∀ b ∈ A, b.hi = false ∧ 129 ≤ b.arr ∧ b.arr ≤ 134 := fun b hb =>
    idxA_range b (hA b hb)
  refine ⟨⟨?_, ?_⟩, h.core.frame (fun b hb => .inr (by have := hI' b hb; omega))
      (fun x hx => .inr (by rw [hC x hx]; decide)) hf,
    h.pins.frame (fun b hb => .inr (by have := hI' b hb; omega)) hf,
    h.env.rebase hf hA hC hI,
    h.mode.frame hf (fun h => by have := hC _ h; simp at this) (fun h => by have := hC _ h; simp at this)⟩
  · exact ArenaR.frame_ext A C (fun b hb => by have := hI' b hb; exact ⟨this.1, by omega⟩)
      (fun x hx => by rw [hC x hx]; decide) m m' hf a h.arena.base
  · exact DerR.frameM A C m m' hf (fun b hb => by have := hI' b hb; omega) a h.arena.der

/-! ## `idx_add` -/

/-- The lookups the stream index's builder takes. -/
structure IdxProg (p : Prog) : Prop extends L.Ind.DeclConstsProg p where
  idx_add : p.lookup "idx_add" = some idxAddL
  build_index : p.lookup "build_index" = some buildIndexL
  idx_consts : p.lookup "idx_consts" = some idxConstsL
  idx_tables : p.lookup "idx_tables" = some idxTablesL
  base_row_get : p.lookup "base_row_get" = some baseRowGetL
  base_row_set : p.lookup "base_row_set" = some baseRowSetL
  tbl_base_get : p.lookup "tbl_base_get" = some tblBaseGetL
  tbl_base_set : p.lookup "tbl_base_set" = some tblBaseSetL
  iw_reset : p.lookup "iw_reset" = some L.Ind.iwReset
  fz : FreezeProg p

/-- **What the builder keeps from record to record**, at the index `I` built so far: the stage
relation at the index's base layer's empty view (no constant visible, no own constants), the twin's
invariants beyond it and the filled pin table, the index rows, the
front's records `ds`, the twin's driver invariant with the scratch tier closed, every record
persistent and denoting, `Quot`'s names under `dn`, the inductive memos. -/
structure BuildR (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration) (m : Mem)
    (a : AState) (I : IStreamIndex) : Prop where
  stage : StageR 0 (bEnv I.base a.pins 0 0) m a
  /-- The twin's invariants beyond the stage relation (at the empty view). -/
  twin : TwinOK dn m a (bEnv I.base a.pins 0 0)
  /-- The pin table is filled. -/
  pin : pinW m 0 ≠ 0
  idx : IndexR m I
  decls : L.Front.DeclsF (m.arr64 L.Front.DECL) (m.arr64 L.Front.DLP) ds
  front : ∀ i (h : i < ds.size) b nP, ds[i] = .indDecl b nP → FrontBlock b
  drv : ConRon.Bridge.DriverOK a
  off : a.store.scratchOn = false
  recs : ∀ x ∈ ds.toList, ConRon.Bridge.PersDecl x ∧ ∃ d, Frontend.denoteDecl a.store x = some d
  quotDn : L.Rom.NamesDn dn a L.Rom.quotNames
  memos : IndMemos m
  fsize : (m.arr64 FIRSTS).size < 2 ^ 64
  /-- The next counter is below `2^32` (`idx_consts`' capacity). -/
  nextLt : I.next < 2 ^ 32

theorem getD_headD (l : List Word) : l.getD 0 0 = l.headD 0 ∧ l.getD 1 0 = l.tail.headD 0 := by
  rcases l with _ | ⟨x, _ | ⟨y, _⟩⟩ <;> simp

/-- The twin's step's result. -/
def addRes (I : IStreamIndex) (L : List IConstantInfo) (Q : List IProjTable) : IStreamIndex :=
  ⟨{ I.base with idx := (insertConsts I.base.idx I.next L).1, tbls := insertTables I.base.tbls I.firsts.size Q }, I.firsts.push I.next, (insertConsts I.base.idx I.next L).2,
    none, none⟩

/-- The twin's step through its two reads. -/
theorem add_run {I : IStreamIndex} {d : IDeclaration} {a a₁ a₂ : AState} {L : List IConstantInfo}
    {Q : List IProjTable} (h1 : (declConstants d).run a = .ok (L, a₁))
    (h2 : (declTables d).run a₁ = .ok (Q, a₂)) :
    (I.add d).run a = .ok (addRes I L Q, a₂) := by
  have h1' : declConstants d a = .ok (L, a₁) := h1
  have h2' : declTables d a₁ = .ok (Q, a₂) := h2
  show IStreamIndex.add I d a = _
  simp only [IStreamIndex.add, Bind.bind, StateT.bind, Except.bind, h1', h2']
  rfl

/-- `iw_reset`'s memory keeps the stage relation (only the work pool's top moves, to `0`). -/
theorem _root_.L.Ind.StageR.reset {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} (hS : StageR vis fe m a) :
    StageR vis fe (m.set64 CTL 200 0) a := by
  refine ⟨CheckR.frame_hi (A := []) (C := [200]) (by simp) (by simp) (MemFrame.setCtl m 200 0)
    hS.check, ?_⟩
  exact IWOK.of_iw ((MemFrame.setCtl m 200 0).mono (by simp) (by simp)) hS.iw
    (by simp [iwTop, rdW_set64, hS.iw.ctl])

theorem RecGrow.refl (m : Mem) : RecGrow m m := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem RecGrow.trans {m₁ m₂ m₃ : Mem} (h₁ : RecGrow m₁ m₂) (h₂ : RecGrow m₂ m₃) : RecGrow m₁ m₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun i hi => (h₂.2 i (Nat.lt_of_lt_of_le hi h₁.1)).trans (h₁.2 i hi)⟩

/-- A frame outside `EREC` and `CTL[129]` keeps the record pool. -/
theorem RecGrow.of_frame {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (EREC : TieredArray) ∉ A) (hC : (129 : Word) ∉ C) : RecGrow m m' :=
  ⟨by simp only [erTop, hf.ctl 129 hC]; exact Nat.le_refl _,
    fun _ _ => by rw [hf.arr _ hA (by decide)]⟩

/-- **What the index build keeps** beside `BuildR`: the record pool's prefix, the tier-1 pool's
top `CTL[130]`, the core's walk memos. -/
structure BKeep (m m' : Mem) : Prop where
  grow : RecGrow m m'
  ctl130 : rdW (m'.arr64 CTL) 130 = rdW (m.arr64 CTL) 130
  memos : CoreMemos m → CoreMemos m'

theorem BKeep.refl (m : Mem) : BKeep m m := ⟨RecGrow.refl m, rfl, id⟩

theorem BKeep.trans {m₁ m₂ m₃ : Mem} (h₁ : BKeep m₁ m₂) (h₂ : BKeep m₂ m₃) : BKeep m₁ m₃ :=
  ⟨h₁.grow.trans h₂.grow, h₂.ctl130.trans h₁.ctl130, h₂.memos ∘ h₁.memos⟩

/-- A frame outside the record pool, `CTL[129]`, `CTL[130]` and the core's memos keeps them. -/
theorem BKeep.of_frame {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (EREC : TieredArray) ∉ A ∧ (ILMEMO : TieredArray) ∉ A ∧ (ABMEMO : TieredArray) ∉ A ∧
      (WSM : TieredArray) ∉ A ∧ (FLM : TieredArray) ∉ A ∧ (LSM : TieredArray) ∉ A ∧
      (LPMEMO : TieredArray) ∉ A ∧ (LPLMEMO : TieredArray) ∉ A ∧ (LPLSMEMO : TieredArray) ∉ A)
    (hC : (129 : Word) ∉ C ∧ (130 : Word) ∉ C ∧ (50 : Word) ∉ C ∧ (48 : Word) ∉ C ∧
      (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C ∧ (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧
      (58 : Word) ∉ C) (hHB : (L.Ind.HBM : TieredArray) ∉ A := by decide)
    (hHBc : (214 : Word) ∉ C := by first | decide | simp) : BKeep m m' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hA
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hC
  exact ⟨RecGrow.of_frame hf a1 c1, hf.ctl 130 c2, fun h =>
    CoreMemos.frame hf ⟨a2, a3⟩ ⟨c3, c4⟩ h ⟨a4, a5, a6⟩ ⟨c5, c6, c7⟩ ⟨a7, a8, a9⟩ ⟨c8, c9, c10⟩ hHB hHBc⟩

/-- `decl_constants`/`decl_tables`' post keeps them. -/
theorem BKeep.of_idx {m m' : Mem} (hg : IWGrow m m') (hK : L.Ind.IdxKeep m m') : BKeep m m' :=
  ⟨L.Arena.IWGrow.recGrow hg, hK.ctl130, hK.memos⟩

section idx
variable {p : Prog} (hP : IdxProg p)
include hP

/-- **`idx_add(k)` refines `IStreamIndex.add` of record `k`**: from the builder's relation at an
index of `k` records, a returning run is the twin's step, and the relation holds after it at the
index with record `k` added. -/
theorem idxAdd_ref {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} 
    {k : Word} {d : IDeclaration} {n : Nat} {m m' : Mem} {a : AState} {I : IStreamIndex}
    {res : List Word} (hR : BuildR dn ds m a I) (hk : I.firsts.size = k.toNat)
    (hd : ds[k.toNat]? = some d) (hc : callW p n "idx_add" [k] m = some (res, m')) :
    ∃ I' a', (I.add d).run a = .ok (I', a') ∧ BuildR dn ds m' a' I' ∧
      I'.firsts.size = k.toNat + 1 ∧ BKeep m m' := by
  rcases n with _ | n
  · rw [callW_zero] at hc; cases hc
  have hw := callW_model (M := fun mm => idxAddW p (n + 1) mm k)
    (fun s₀ => idxAdd_specW p hP.idx_add (n + 1) s₀ k) hc
  simp only [idxAddW] at hw
  have hlt : k.toNat < ds.size := by
    rcases Nat.lt_or_ge k.toNat ds.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hd; cases hd
  have hdk : ds[k.toNat] = d := by rw [Array.getElem?_eq_getElem hlt] at hd; exact Option.some.inj hd
  -- `iw_reset`
  cases h1 : callW p n "iw_reset" [] m with
  | none => rw [h1] at hw; simp [ntBW] at hw
  | some q1 =>
  obtain ⟨ρ1, m1⟩ := q1
  rw [h1, bW_some] at hw
  obtain ⟨s1, hs1, -, e1⟩ := triple_of_callW (iwReset_specW p hP.iw_reset n ⟨m, Locals.init []⟩) h1
  simp only [iwResetW, Option.some.injEq, Prod.mk.injEq] at e1
  obtain ⟨-, e1⟩ := e1
  rw [hs1] at e1; subst e1
  have hI1 : IndexR (m.set64 CTL 200 0) I :=
    hR.idx.grow (fun b _ h2 => Mem.arr64_set64_ne _ _ _ _ _ (by rintro rfl; revert h2; decide))
      (rdW_set_ctl m 200 0 128 (by decide)) (by rw [erecP_reset]; exact fun _ _ h => h)
  -- the first counter
  split at hw
  · cases hw
  rename_i hF
  have eF : (m.set64 CTL 200 0).arr64 FIRSTS = m.arr64 FIRSTS := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hF' : k.toNat < (m.arr64 FIRSTS).size := by
    simp only [Mem.len64, eF, UInt64.le_iff_toNat_le] at hF
    have := hR.fsize
    have e : (UInt64.ofNat (m.arr64 FIRSTS).size).toNat = (m.arr64 FIRSTS).size := by simp; omega
    omega
  -- the memory after the first counter's write
  have hS1 : StageR 0 (bEnv I.base a.pins 0 0) (m.set64 CTL 200 0) a := hR.stage.reset
  generalize hm2 : (m.set64 CTL 200 0).set64 FIRSTS k (rdW ((m.set64 CTL 200 0).arr64 CTL) 128) = m2 at hw
  have hf12 : MemFrame [FIRSTS] [] (m.set64 CTL 200 0) m2 := hm2 ▸ MemFrame.set64 _ FIRSTS (by decide) k _
  have hS2 : StageR 0 (bEnv I.base a.pins 0 0) m2 a :=
    ⟨CheckR.frame_hi (fun b hb => by simp at hb; subst hb; decide) (by simp) hf12 hS1.check,
      IWOK.frame hf12 (by decide) (by decide) (by decide) (by decide) hS1.iw⟩
  have hI2 : IndexR m2 { I with firsts := I.firsts.push I.next } := by
    have := hI1.pushFirst (by rw [eF, hk]; exact hF') (by rw [hk]; exact UInt64.toNat_lt k)
    rw [hk, UInt64.ofNat_toNat] at this; rw [← hm2]; exact this
  have hM2 : IndMemos m2 :=
    (hR.memos.frame (MemFrame.setCtl m 200 0) (by simp) (fun x hx => by simp at hx; subst hx; decide)).frame
      hf12 (fun b hb => by simp at hb; subst hb; decide) (by simp)
  have eA2 : ∀ b : TieredArray, b ≠ CTL → b ≠ FIRSTS → m2.arr64 b = m.arr64 b := fun b h1 h2 => by
    rw [hf12.arr b (by simpa using h2) h1, Mem.arr64_set64_ne _ _ _ _ _ h1]
  have eD2 := eA2 L.Front.DECL (by decide) (by decide)
  have eP2 := eA2 L.Front.DLP (by decide) (by decide)
  have hdm : d ∈ ds.toList := by rw [← hdk]; simp
  obtain ⟨hpd, dd, hden⟩ := hR.recs d hdm
  -- `decl_constants`
  cases h2 : callW p n "decl_constants" [k] m2 with
  | none => rw [h2] at hw; simp [ntBW] at hw
  | some q2 =>
  obtain ⟨ρ2, m3⟩ := q2
  rw [h2, bW_some] at hw
  have hT2 : TwinOK dn m2 a (bEnv I.base a.pins 0 0) :=
    (hR.twin.frame (MemFrame.setCtl m 200 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).frame hf12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp2 : pinW m2 0 ≠ 0 := by
    rw [pinW_frame hf12 (by decide), pinW_frame (MemFrame.setCtl m 200 0) (by decide)]; exact hR.pin
  have hpre2 : L.Ind.DeclConstsPre dn 0 (bEnv I.base a.pins 0 0) k d m2 a :=
    ⟨hS2, by rw [eD2, eP2, ← hdk]; exact hR.decls.recs _ hlt,
      fun b nP e => hR.front _ hlt b nP (hdk.trans e), hR.drv.state, hR.quotDn, hM2,
      by rw [eD2]; exact hR.decls.dsize, by rw [eP2]; exact hR.decls.psize, hR.off,
      declTwin_of hT2 hp2 hM2 hR.drv rfl,
      fun b nP e => by have := hR.decls.npb _ hlt b nP (hdk.trans e); omega, ⟨dd, hden⟩, ⟨ds, by rw [eD2, eP2]; exact hR.decls, hlt, hdk⟩⟩
  obtain ⟨s3, hs3, -, hok3, ⟨hS3, hg3, hL3⟩, hM3, hK3, hT3⟩ := triple_of_callW
    (L.Ind.declConstants_refines hP.toDeclConstsProg dn 0 (bEnv I.base a.pins 0 0) k d n
      ⟨m2, Locals.init []⟩ a hpre2) h2
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  obtain ⟨hdrv3, hx3, hpin3, hoff3, -, -⟩ := ConRon.Bridge.constsSpec hR.drv hR.off hpd hden hrun3
  have hI3 : IndexR s3.mem { I with firsts := I.firsts.push I.next } :=
    hI2.grow (fun b _ h => hK3.arr b (h.elim (fun h => .inr (.inr (.inr h)))
      (fun h => .inr (.inr (.inl h))))) hK3.ctl128 hg3.ext
  obtain ⟨hDL, -⟩ := hL3
  rw [(getD_headD ρ2).1, (getD_headD ρ2).2] at hDL
  -- `idx_consts`
  cases h4 : callW p n "idx_consts" [ρ2.headD 0, ρ2.tail.headD 0] s3.mem with
  | none => rw [h4] at hw; simp [ntBW] at hw
  | some q4 =>
  obtain ⟨ρ4, m4⟩ := q4
  rw [h4, bW_some] at hw
  obtain ⟨s4, hs4, -, -, hI4, hf4, hnx4⟩ := triple_of_callW
    (idxConsts_spec p hP.idx_consts hP.base_row_get hP.base_row_set n ⟨s3.mem, Locals.init []⟩
      _ _ hI3 hDL (by have := hS3.iw.ctl; simp only at this ⊢; omega) hS3.iw.iwSize hR.nextLt) h4
  subst hs4
  have hS4 : StageR 0 (bEnv (insC { I with firsts := I.firsts.push I.next } (AM.res (declConstants d) a)).base a.pins 0 0) s4.mem
      (AM.st (declConstants d) a) :=
    ⟨hS3.check.rebase hf4 (fun b hb => List.mem_append_left _ hb) (by simp) hI4,
      IWOK.frame hf4 (by decide) (by decide) (by decide) (by decide) hS3.iw⟩
  have hM4 : IndMemos s4.mem := hM3.frame hf4
    (fun b hb => by simp [EixA] at hb; rcases hb with rfl | rfl | rfl <;> decide)
    (fun x hx => by simp at hx; subst hx; decide)
  have eA4 : ∀ b : TieredArray, b ∉ EixA → b ≠ CTL → s4.mem.arr64 b = s3.mem.arr64 b :=
    fun b h1 h2 => hf4.arr b h1 h2
  have eD4 : s4.mem.arr64 L.Front.DECL = m.arr64 L.Front.DECL := by
    rw [eA4 _ (by decide) (by decide), hK3.arr _ (.inl rfl), eD2]
  have eP4 : s4.mem.arr64 L.Front.DLP = m.arr64 L.Front.DLP := by
    rw [eA4 _ (by decide) (by decide), hK3.arr _ (.inr (.inl rfl)), eP2]
  have hden3 := ConRon.Bridge.denoteDecl_pext (ConRon.Bridge.PExt.of_ext hx3) hpd hden
  -- `decl_tables`
  cases h5 : callW p n "decl_tables" [k] s4.mem with
  | none => rw [h5] at hw; simp [ntBW] at hw
  | some q5 =>
  obtain ⟨ρ5, m5⟩ := q5
  rw [h5, bW_some] at hw
  have hpre5 : L.Ind.DeclConstsPre dn 0 (bEnv (insC { I with firsts := I.firsts.push I.next } (AM.res (declConstants d) a)).base a.pins 0 0)
      k d s4.mem (AM.st (declConstants d) a) :=
    ⟨hS4, by rw [eD4, eP4, ← hdk]; exact hR.decls.recs _ hlt,
      fun b nP e => hR.front _ hlt b nP (hdk.trans e), hdrv3.state, hR.quotDn.ext hx3, hM4,
      by rw [eD4]; exact hR.decls.dsize, by rw [eP4]; exact hR.decls.psize, hoff3,
      declTwin_of ((hT3.twin.frame hf4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).bEnv0 _)
        (by rw [pinW_frame hf4 (by decide)]; exact hT3.pin) hM4 hdrv3 hpin3,
      fun b nP e => by have := hR.decls.npb _ hlt b nP (hdk.trans e); omega, ⟨dd, hden3⟩, ⟨ds, by rw [eD4, eP4]; exact hR.decls, hlt, hdk⟩⟩
  obtain ⟨s5, hs5, -, hok5, ⟨hS5, hg5, hL5⟩, hM5, hK5, hT5⟩ := triple_of_callW
    (L.Ind.declTables_refines hP.toDeclConstsProg dn 0 _ k d n ⟨s4.mem, Locals.init []⟩ _ hpre5) h5
  subst hs5
  have hrun5 := AM.run_of_ok _ _ hok5
  obtain ⟨hdrv5, hx5, hpin5, hoff5, -, -⟩ := ConRon.Bridge.tablesSpec hdrv3 hoff3 hpd hden3 hrun5
  have hI5 : IndexR s5.mem (insC { I with firsts := I.firsts.push I.next } (AM.res (declConstants d) a)) :=
    hI4.grow (fun b _ h => hK5.arr b (h.elim (fun h => .inr (.inr (.inr h)))
      (fun h => .inr (.inr (.inl h))))) hK5.ctl128 hg5.ext
  obtain ⟨hTL, -⟩ := hL5
  rw [(getD_headD ρ5).1, (getD_headD ρ5).2] at hTL
  -- `idx_tables`
  cases h6 : callW p n "idx_tables" [ρ5.headD 0, ρ5.tail.headD 0, k] s5.mem with
  | none => rw [h6] at hw; simp [ntBW] at hw
  | some q6 =>
  obtain ⟨ρ6, m6⟩ := q6
  rw [h6, bW_some] at hw
  obtain ⟨s6, hs6, -, -, hI6, hf6⟩ := triple_of_callW
    (idxTables_spec p hP.idx_tables hP.tbl_base_get hP.tbl_base_set n ⟨s5.mem, Locals.init []⟩
      _ _ k hI5 hTL hS5.iw.iwSize (by have := hR.fsize; omega)) h6
  subst hs6
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨-, rfl⟩ := hw
  rw [← hk] at hI6
  replace hI6 : IndexR s6.mem
      (addRes I (AM.res (declConstants d) a) (AM.res (declTables d) (AM.st (declConstants d) a))) :=
    ⟨hI6.base, hI6.btbl, hI6.firsts, hI6.firstsSize, hI6.next, hI6.rows⟩
  have eA6 : ∀ b : TieredArray, b ∉ TixA → b ≠ CTL → s6.mem.arr64 b = s5.mem.arr64 b :=
    fun b h1 h2 => hf6.arr b h1 h2
  have eD6 : s6.mem.arr64 L.Front.DECL = m.arr64 L.Front.DECL := by
    rw [eA6 _ (by decide) (by decide), hK5.arr _ (.inl rfl), eD4]
  have eP6 : s6.mem.arr64 L.Front.DLP = m.arr64 L.Front.DLP := by
    rw [eA6 _ (by decide) (by decide), hK5.arr _ (.inr (.inl rfl)), eP4]
  have eF6 : (s6.mem.arr64 FIRSTS).size = (m.arr64 FIRSTS).size := by
    rw [eA6 _ (by decide) (by decide), hK5.arr _ (.inr (.inr (.inl rfl))),
      eA4 _ (by decide) (by decide), hK3.arr _ (.inr (.inr (.inl rfl))), hf12.size, eF]
  have g1 : BKeep m m2 :=
    (BKeep.of_frame (MemFrame.setCtl m 200 0) (by decide) (by decide)).trans
      (BKeep.of_frame hf12 (by decide) (by decide))
  have hG : BKeep m s6.mem := ((((g1.trans (BKeep.of_idx hg3 hK3)).trans
    (BKeep.of_frame hf4 (by decide) (by decide))).trans
    (BKeep.of_idx hg5 hK5)).trans (BKeep.of_frame hf6 (by decide) (by decide)))
  refine ⟨_, _, add_run hrun3 hrun5, ?_, by simp [addRes, hk], hG⟩
  refine ⟨by rw [hpin5, hpin3]; exact ⟨hS5.check.rebase hf6 (fun b hb => List.mem_append_right _ hb)
      (by simp) hI6, IWOK.frame hf6 (by decide) (by decide) (by decide) (by decide) hS5.iw⟩,
    by rw [hpin5, hpin3]; exact (hT5.twin.frame hf6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).bEnv0 _, by rw [pinW_frame hf6 (by decide)]; exact hT5.pin,
    hI6, by rw [eD6, eP6]; exact hR.decls, hR.front, hdrv5, hoff5, fun x hx => ?_,
    (hR.quotDn.ext hx3).ext hx5, hM5.frame hf6
      (fun b hb => by simp [TixA] at hb; rcases hb with rfl | rfl | rfl <;> decide) (by simp), by rw [eF6]; exact hR.fsize,
    by simpa [addRes, insC] using hnx4⟩
  obtain ⟨hpx, dx, hdx⟩ := hR.recs x hx
  exact ⟨hpx, dx, ConRon.Bridge.denoteDecl_pext (ConRon.Bridge.PExt.of_ext (hx3.trans hx5)) hpx hdx⟩

/-- **`idx_add(k)` refines `IStreamIndex.add` of record `k`** (`idxAdd_ref` as a triple). -/
@[refines ConRon.Arena.IStreamIndex.add]
theorem idxAdd_refines {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} 
    (k : Word) (d : IDeclaration) (n : Nat) (s₀ : St) (a : AState) (I : IStreamIndex)
    (hR : BuildR dn ds s₀.mem a I) (hk : I.firsts.size = k.toNat)
    (hd : ds[k.toNat]? = some d) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "idx_add" [k]
    ⦃fun _ s' => LocEq s' s₀ ∧ ∃ I' a', (I.add d).run a = .ok (I', a') ∧
      BuildR dn ds s'.mem a' I' ∧ I'.firsts.size = k.toNat + 1; ⊤⦄ :=
  triple_post (callW_spec p n "idx_add" [k] s₀) fun _ _ ⟨hl, hc⟩ => ⟨hl,
    let ⟨I', a', h1, h2, h3, _⟩ := idxAdd_ref hP hR hk hd hc; ⟨I', a', h1, h2, h3⟩⟩

/-- `build_index`'s loop from record `k`: `buildIndexGo` over the records from `k` on. -/
theorem buildIndexLoop_ref {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} 
    {cnt : Word} (hcnt : cnt.toNat = ds.size) :
    ∀ (n : Nat) (m m' : Mem) (k : Word) (a : AState) (I : IStreamIndex),
      BuildR dn ds m a I → I.firsts.size = k.toNat → k.toNat ≤ ds.size →
      buildIndexW.loop1 p n m cnt k = some m' →
      ∃ I' a', buildIndexGo I k.toNat (ds.toList.drop k.toNat) a = buildIndexGo I' ds.size [] a' ∧
        BuildR dn ds m' a' I' ∧ I'.firsts.size = ds.size ∧ BKeep m m' := by
  intro n
  induction n with
  | zero => intro m m' k a I _ _ _ h; rw [buildIndexW.loop1.eq_1] at h; cases h
  | succ n ih =>
    intro m m' k a I hR hk hle h
    by_cases g : k < cnt
    · rw [buildIndexW.loop1.arm1 _ _ _ _ _ g] at h
      have hlt : k.toNat < ds.size := by rw [← hcnt]; exact g
      cases h1 : callW p n "idx_add" [k] m with
      | none => rw [h1] at h; simp [ntBW] at h
      | some q =>
      obtain ⟨ρ, m₁⟩ := q
      rw [h1, bW_some] at h
      have hd : ds[k.toNat]? = some ds[k.toNat] := Array.getElem?_eq_getElem hlt
      obtain ⟨I₁, a₁, hrun, hR₁, hk₁, hg₁⟩ := idxAdd_ref hP hR hk hd h1
      have e1 : (k + 1).toNat = k.toNat + 1 := by
        rw [UInt64.toNat_add]; have := UInt64.toNat_lt cnt; simp; omega
      obtain ⟨I', a', hgo, hR', hk', hg'⟩ := ih m₁ m' (k + 1) a₁ I₁ hR₁ (by rw [e1]; exact hk₁)
        (by rw [e1]; omega) h
      refine ⟨I', a', ?_, hR', hk', hg₁.trans hg'⟩
      rw [e1] at hgo
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      have hrun' : I.add ds[k.toNat] a = .ok (I₁, a₁) := hrun
      simp only [Array.getElem_toList]
      show (match I.add ds[k.toNat] a with
        | .ok (I', s') => buildIndexGo I' (k.toNat + 1) (ds.toList.drop (k.toNat + 1)) s'
        | .error e => .ok (.error (e, k.toNat), a)) = _
      rw [hrun']; exact hgo
    · rw [buildIndexW.loop1.arm2 _ _ _ _ _ g] at h
      cases h
      have hge : ds.size ≤ k.toNat := by rw [← hcnt]; exact Nat.le_of_not_lt g
      have e : k.toNat = ds.size := by omega
      refine ⟨I, a, ?_, hR, by rw [hk, e], BKeep.refl _⟩
      rw [e, List.drop_of_length_le (by simp)]

/-- **`build_index(cnt)` refines `buildIndex`** over the front's records (`cnt` of them): the
literal names written first (`str_lit_names`, the twin's builder environment `mkIFEnvLits`; the
builder's relation `hR` holds once they are), the records added (`buildIndexLoop_ref`), the
index frozen (`index_freeze`): the twin's frozen index is built, the relation holds at it, and
`FrozenR` (its literal names and thresholds in `CTL[162‥173]`). -/
@[refines ConRon.Arena.buildIndexGo ConRon.Arena.buildIndex ConRon.Arena.IStreamIndex.freeze]
theorem buildIndex_refines {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
    (cnt : Word) (hcnt : cnt.toNat = ds.size) (n : Nat) (s₀ : St) (a : AState)
    (hF : PinsFull s₀.mem a.pins) (hc : 173 < (s₀.mem.arr64 CTL).size)
    (hR : ∀ m', MemFrame [] litCtl s₀.mem m' → (pinLits s₀.mem).map (·.word.toUInt64) = litWords m' →
      BuildR dn ds m' a {}) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "build_index" [cnt]
    ⦃fun _ s' => LocEq s' s₀ ∧ ∃ I a', buildIndex ds a = .ok (.ok I, a') ∧
      BuildR dn ds s'.mem a' I ∧ FrozenR s'.mem I ∧ I.firsts.size = ds.size ∧
      BKeep s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (callW_spec p n "build_index" [cnt] s₀) fun _ s' ⟨hl, hc'⟩ => ⟨hl, ?_⟩
  rcases n with _ | n
  · rw [callW_zero] at hc'; cases hc'
  have hw := callW_model (M := fun mm => buildIndexW p (n + 1) mm cnt)
    (fun s₀ => buildIndex_specW p hP.build_index (n + 1) s₀ cnt) hc'
  simp only [buildIndexW] at hw
  -- the literal names
  cases h0 : callW p n "str_lit_names" [] s₀.mem with
  | none => rw [h0] at hw; simp [ntBW] at hw
  | some q0 =>
  obtain ⟨ρ0, m0⟩ := q0
  rw [h0, bW_some] at hw
  obtain ⟨s0, hs0, -, hl0, hf0⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (strLitNames_refines hP.fz n _ hF hc) h0
  subst hs0
  have hR0 := hR s0.mem hf0 hl0
  -- the records
  cases h : buildIndexW.loop1 p (n + 1) s0.mem cnt 0 with
  | none => rw [h] at hw; simp [buildIndexW.k_loop1] at hw
  | some m₁ =>
  rw [h, buildIndexW.k_loop1.arm1] at hw
  obtain ⟨I₁, a₁, hgo, hR₁, hsz₁, hg₁⟩ :=
    buildIndexLoop_ref hP hcnt (n + 1) s0.mem _ 0 a {} hR0 rfl (Nat.zero_le _) h
  -- the freeze
  cases h2 : callW p n "index_freeze" [] m₁ with
  | none => rw [h2] at hw; simp [ntBW] at hw
  | some q2 =>
  obtain ⟨ρ2, m2⟩ := q2
  rw [h2, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨-, rfl⟩ := hw
  have hF₁ : PinsFull m₁ a₁.pins := hR₁.stage.check.pins.full hR₁.pin
  have hl₁ : (pinLits m₁).map (·.word.toUInt64) = litWords m₁ := by
    rw [pinLits_drv hF₁]; exact hR₁.stage.check.env.lits
  have hc₁ : 173 < (m₁.arr64 CTL).size := by have := hR₁.stage.iw.ctl; omega
  obtain ⟨s2, hs2, -, hfz, hFz, hIz, hf2⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (indexFreeze_refines hP.fz n _ hR₁.idx hF₁ hc₁ hl₁ (a := a₁)) h2
  rw [← hs2]
  refine ⟨frozenAt I₁ (pinLits m₁), a₁, ?_, ?_, hFz, by simp [frozenAt, hsz₁],
    ((BKeep.of_frame hf0 (by decide) (by decide)).trans hg₁).trans
      (BKeep.of_frame hf2 (by decide) (by decide))⟩
  · have e : buildIndex ds a = buildIndexGo I₁ ds.size [] a₁ := by rw [← hgo]; rfl
    rw [e]
    show (match I₁.freeze a₁ with
      | .ok (F, s') => Except.ok (Except.ok F, s')
      | .error e => .ok (.error (e, ds.size), a₁)) = _
    rw [show I₁.freeze a₁ = _ from hfz]
  · refine ⟨⟨CheckR.frame_hi (A := []) (C := [172, 173]) (by simp)
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide) hf2 hR₁.stage.check,
      IWOK.frame hf2 (by decide) (by decide) (by decide) (by decide) hR₁.stage.iw⟩,
      (hR₁.twin.frame hf2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).bEnv0 _,
      by rw [pinW_frame hf2 (by decide)]; exact hR₁.pin, hIz,
      by rw [hf2.arr _ (by simp) (by decide), hf2.arr _ (by simp) (by decide)]; exact hR₁.decls,
      hR₁.front, hR₁.drv, hR₁.off, hR₁.recs, hR₁.quotDn,
      hR₁.memos.frame hf2 (fun b hb => by simp at hb)
        (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide),
      by rw [hf2.arr _ (by simp) (by decide)]; exact hR₁.fsize, by simpa [frozenAt] using hR₁.nextLt⟩

end idx

end L.Arena
