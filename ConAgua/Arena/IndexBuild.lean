module

public import ConAgua.Arena.IndexLoops
public import ConAgua.Arena.IndDeclConstsSpec
public import ConAgua.Arena.DeclCvg
public import ConAgua.Arena.DeclNatBase
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

open L.Ind (IW iwN decPL ntBW)

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

end L.Arena
