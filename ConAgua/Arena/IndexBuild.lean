module

public import ConAgua.Arena.IndexLoops
public import ConAgua.Arena.IndDeclConstsSpec
public import ConAgua.Arena.DeclCvg
public import ConAgua.Arena.DeclNatBase
public import ConRon.Bridge.Checker.Index
import ConRon.Bridge.Checker.Install
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
  specs [callW_spec p n "idx_add"]
  grind [arena_grind] bind ntBW

/-! ## The relations -/

/-- The environment the stream index's builder runs at: the index's base layer, below `c` and
record position `r` (the job's view, `IStreamIndex.view`, has this shape), no own constants. -/
def bEnv (b : IFBase) (c r : Nat) : IFEnv :=
  ⟨⟨[], []⟩, {}, { b with below := c, belowRec := r }, {}⟩

theorem view_eq_bEnv (I : IStreamIndex) (k : Nat) :
    I.view k = bEnv I.base (I.firsts.getD k I.next) k := rfl

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
    by rw [hF]; exact h.firstsSize, by rw [h128]; exact h.next⟩
  · have := h.base n; rw [hb, this]; split
    · rfl
    · cases e : I.base.idx[n]? with
      | none => rw [e] at this; simp_all
      | some y =>
        rw [e] at this
        simp only [Option.map_some, ite_cond_eq_false _ _ (eq_false ‹_›), Option.some.injEq,
          Prod.mk.injEq] at this
        rw [← this.2, hx.decCI this.2.symm]
  · have := h.btbl n; rw [hbt, this]; split
    · rfl
    · cases e : I.base.tbls[n]? with
      | none => rw [e] at this; simp_all
      | some y =>
        rw [e] at this
        simp only [Option.map_some, ite_cond_eq_false _ _ (eq_false ‹_›), Option.some.injEq,
          Prod.mk.injEq] at this
        rw [← this.2, hx.decTbl this.2.symm]

/-- `fe` with the base layer `b` (its bounds kept). -/
def _root_.ConRon.Arena.IFEnv.rebase (fe : IFEnv) (b : IFBase) : IFEnv :=
  ⟨fe.env, fe.idx, { b with below := fe.base.below, belowRec := fe.base.belowRec }, fe.tbls⟩

theorem bEnv_rebase (b b' : IFBase) (c r : Nat) : (bEnv b c r).rebase b' = bEnv b' c r := rfl

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
    fun n hn => ?_, ?_, ?_, fun n => hI.base n, fun n => hI.btbl n, by rw [hs]; exact h.stamp⟩
  · show fe.idx[n]? = _; rw [h.own n]; simp only [ownFind, hraw, hP]
  · rw [hraw] at hn ⊢; rw [hP]; exact h.own_dec n hn
  · rw [hraw] at hn ⊢; exact h.fresh n hn
  · rw [hraw, hraw] at hq; rw [hraw] at hn; exact h.uniq n n' hn hq
  · show fe.tbls[n]? = _; rw [h.otbl n, hot, hP]
  · rw [hot] at hn ⊢; rw [hP]; exact h.otbl_dec n hn
  · rw [hc 134 (by decide)]; exact h.below
  · rw [hc 135 (by decide)]; exact h.belowRec

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

/-- **What the builder keeps from record to record**, at the index `I` built so far: the stage
relation at the index's base layer (bounds `c`, `r`, no own constants), the index rows, the
front's records `ds`, the twin's driver invariant with the scratch tier closed, every record
persistent and denoting, `Quot`'s names under `dn`, the inductive memos. -/
structure BuildR (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration) (c r : Nat) (m : Mem)
    (a : AState) (I : IStreamIndex) : Prop where
  stage : StageR 0 (bEnv I.base c r) m a
  idx : IndexR m I
  decls : L.Front.DeclsF (m.arr64 L.Front.DECL) (m.arr64 L.Front.DLP) ds
  front : ∀ i (h : i < ds.size) b nP, ds[i] = .indDecl b nP → FrontBlock b
  drv : ConRon.Bridge.DriverOK a
  off : a.store.scratchOn = false
  recs : ∀ x ∈ ds.toList, ConRon.Bridge.PersDecl x ∧ ∃ d, Frontend.denoteDecl a.store x = some d
  quotDn : L.Rom.NamesDn dn a L.Rom.quotNames
  memos : IndMemos m
  fsize : (m.arr64 FIRSTS).size < 2 ^ 64

theorem getD_headD (l : List Word) : l.getD 0 0 = l.headD 0 ∧ l.getD 1 0 = l.tail.headD 0 := by
  rcases l with _ | ⟨x, _ | ⟨y, _⟩⟩ <;> simp

/-- The twin's step's result. -/
def addRes (I : IStreamIndex) (L : List IConstantInfo) (Q : List IProjTable) : IStreamIndex :=
  ⟨{ I.base with idx := (insertConsts I.base.idx I.next L).1, tbls := insertTables I.base.tbls I.firsts.size Q }, I.firsts.push I.next, (insertConsts I.base.idx I.next L).2⟩

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
  have h := (IWOK_iff m).mp hS.iw
  have hne : ∀ b : TieredArray, b ≠ CTL → (m.set64 CTL 200 0).arr64 b = m.arr64 b :=
    fun b hb => Mem.arr64_set64_ne _ _ _ _ _ hb
  rw [IWOK_iff]
  simp only [iwTop, erTop, erecTop1, rdW_set_ctl m 200 0 129 (by decide),
    rdW_set_ctl m 200 0 130 (by decide), hne IW (by decide), hne EREC (by decide),
    hne (tier1 EREC) (by decide), Mem.size_arr64_set64]
  refine ⟨by rw [rdW_set64, if_pos ⟨rfl, rfl, by simpa using h.2.2.2.2.1⟩]; simp, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem erecP_reset' (m : Mem) : erecP (m.set64 CTL 200 0) = erecP m :=
  erecP_congr' (Mem.arr64_set64_ne _ _ _ _ _ (by decide)) (Mem.arr64_set64_ne _ _ _ _ _ (by decide))
    (rdW_set_ctl m 200 0 129 (by decide)) (rdW_set_ctl m 200 0 130 (by decide))

section idx
variable {p : Prog} (hP : IdxProg p)
include hP

/-- **`idx_add(k)` refines `IStreamIndex.add` of record `k`**: from the builder's relation at an
index of `k` records, a returning run is the twin's step, and the relation holds after it at the
index with record `k` added. -/
theorem idxAdd_ref {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration} {c r : Nat}
    {k : Word} {d : IDeclaration} {n : Nat} {m m' : Mem} {a : AState} {I : IStreamIndex}
    {res : List Word} (hR : BuildR dn ds c r m a I) (hk : I.firsts.size = k.toNat)
    (hd : ds[k.toNat]? = some d) (hc : callW p n "idx_add" [k] m = some (res, m')) :
    ∃ I' a', (I.add d).run a = .ok (I', a') ∧ BuildR dn ds c r m' a' I' ∧
      I'.firsts.size = k.toNat + 1 := by
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
      (rdW_set_ctl m 200 0 128 (by decide)) (by rw [erecP_reset']; exact fun _ _ h => h)
  -- the first counter
  split at hw
  · cases hw
  rename_i hF
  have eF : (m.set64 CTL 200 0).arr64 FIRSTS = m.arr64 FIRSTS := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hF' : k.toNat < (m.arr64 FIRSTS).size := by
    simp only [Mem.len64, eF, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat] at hF
    have := hR.fsize
    have e : (UInt64.ofNat (m.arr64 FIRSTS).size).toNat = (m.arr64 FIRSTS).size := by simp; omega
    omega
  -- the memory after the first counter's write
  have hS1 : StageR 0 (bEnv I.base c r) (m.set64 CTL 200 0) a := hR.stage.reset
  generalize hm2 : (m.set64 CTL 200 0).set64 FIRSTS k (rdW ((m.set64 CTL 200 0).arr64 CTL) 128) = m2 at hw
  have hf12 : MemFrame [FIRSTS] [] (m.set64 CTL 200 0) m2 := hm2 ▸ MemFrame.set64 _ FIRSTS (by decide) k _
  have hS2 : StageR 0 (bEnv I.base c r) m2 a :=
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
  have hpre2 : L.Ind.DeclConstsPre dn 0 (bEnv I.base c r) k d m2 a :=
    ⟨hS2, by rw [eD2, eP2, ← hdk]; exact hR.decls.recs _ hlt,
      fun b nP e => hR.front _ hlt b nP (hdk.trans e), hR.drv.state, hR.quotDn, hM2,
      by rw [eD2]; exact hR.decls.dsize, by rw [eP2]; exact hR.decls.psize⟩
  obtain ⟨s3, hs3, -, hok3, ⟨hS3, hg3, hL3⟩, hM3, hK3⟩ := triple_of_callW
    (L.Ind.declConstants_refines hP.toDeclConstsProg dn 0 (bEnv I.base c r) k d n
      ⟨m2, Locals.init []⟩ a hpre2) h2
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  obtain ⟨hdrv3, hx3, -, hoff3, -, -⟩ := ConRon.Bridge.constsSpec hR.drv hR.off hpd hden hrun3
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
  obtain ⟨s4, hs4, -, -, hI4, hf4⟩ := triple_of_callW
    (idxConsts_spec p hP.idx_consts hP.base_row_get hP.base_row_set n ⟨s3.mem, Locals.init []⟩
      _ _ hI3 hDL (by have := hS3.iw.ctl; simp only at this ⊢; omega) hS3.iw.iwSize) h4
  subst hs4
  sorry

end idx

end L.Arena
