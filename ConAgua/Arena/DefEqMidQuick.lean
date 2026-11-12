module

public import ConAgua.Arena.DefEqMidLams
public import ConAgua.Arena.CoreDen
public import ConAgua.Arena.DefEqLeaves2
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.ModelGen
public import ConAgua.Arena.CoreLevels
import all ConAgua.Arena.CoreLevels
import all ConAgua.Arena.DefEq
import ConAgua.L.WordOff
import ConAgua.Arena.IndPosSpec.UnW
import ConAgua.Arena.InferBodyDisp

@[expose] public section

/-!
# The easy cases: `quick_defeq` (lane `defeq`)

`quickDefEq`'s dispatch on the two tags (`quick_defeq`) and its four arms, each its own function
(`DefEq.lean`): `quick_sort` (the level comparison, `lvl_eq_c`), `lit_eq` (`DefEqLeaves2.lean`),
`quick_forall` (`defeq_binders`), `quick_lam` (`defeq_lams`). The arms read their pairs through
`e_view`. `quickDefeq_refines` closes `QuickDefeqSpec` (`DefEqMid.lean`, `delta_quick`'s
hypothesis).

**Store hypotheses** (`StoreDenotes`): a stored sort's level and a stored constant's level list
read back (`denoteL`/`denoteLs`); `lvl_eq_c`'s refinement (`CoreLevels.lean`) takes the readbacks
as hypotheses. A property of the store relation, not proved here.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **Stored levels read back.** -/
structure StoreDenotes : Prop where
  sort : ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word), CoreS dn m a vis fe M eb → ∀ (h : EIdx) (u : LIdx),
    a.store.view h = some (.sort u) → ∃ l, denoteL a.store.ls u = some l
  constLs : ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word), CoreS dn m a vis fe M eb → ∀ (h : EIdx) (c : NIdx) (us : LsIdx),
    a.store.view h = some (.const c us) → ∃ ls, denoteLs a.store.lss us = some ls

theorem StoreDenotes.of_den (h : CoreDen) : StoreDenotes :=
  ⟨fun dn m a vis fe M eb hS => (h dn m a vis fe M eb hS).sort,
    fun dn m a vis fe M eb hS => (h dn m a vis fe M eb hS).constLs⟩

/-- The lookups of this file. -/
structure QuickProg (p : Prog) : Prop where
  lams : LamsProg p
  lv : LvlCacheProg p
  qd : p.lookup "quick_defeq" = some quickDefeqL
  qs : p.lookup "quick_sort" = some quickSortL
  qf : p.lookup "quick_forall" = some quickForallL
  ql : p.lookup "quick_lam" = some quickLamL
  le : p.lookup "lit_eq" = some litEqL
  lq : p.lookup "limbs_eq" = some limbsEq

/-! ## `e_view` runs -/

/-- **A run of `e_view`**: the memory kept, the twin's view, the words denoting it, the tag word. -/
theorem eView_callW_view {p : Prog} (hp : p.lookup "e_view" = some L.Ind.eView) {n : Nat}
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h : Word} {r : List Word}
    (hc : callW p n "e_view" [h] m = some (r, m')) :
    m' = m ∧ ∃ v, a.store.view (decE h) = some v ∧ L.Ind.ViewR r v ∧ r.headD 0 = tagW h := by
  obtain ⟨s', hm, rfl, hne, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (L.Ind.eView_spec p hp n ⟨m, Locals.init []⟩ h) hc
  obtain ⟨v, hv, hvr⟩ := L.Ind.eViewW_ok m a hR h (hr ▸ hne)
  refine ⟨hm.symm, v, hv, hr ▸ hvr, ?_⟩
  rw [hr]; exact L.Arena.eViewW_head m h (hr ▸ hne)

theorem viewR_sort {r : List Word} {v : ENodeView} (hr : L.Ind.ViewR r v) (h2 : r.headD 0 = 2) :
    v = .sort (decI (r.tail.headD 0)) ∧ HW (r.tail.headD 0) := by
  cases v <;> simp only [L.Ind.ViewR, h2] at hr
  all_goals first
    | (exfalso; obtain ⟨h0, -⟩ := hr; revert h0; decide)
    | (exfalso; revert hr; decide)
    | (obtain ⟨-, h1, h3⟩ := hr; rw [L.getD_one] at h1 h3; exact ⟨by rw [h3], h1⟩)

theorem viewR_forall {r : List Word} {v : ENodeView} (hr : L.Ind.ViewR r v) (h6 : r.headD 0 = 6) :
    v = .forallE (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0)) ∧ HW (r.tail.headD 0) ∧
      HW (r.tail.tail.headD 0) := by
  cases v <;> simp only [L.Ind.ViewR, h6] at hr
  all_goals first
    | (exfalso; obtain ⟨h0, -⟩ := hr; revert h0; decide)
    | (exfalso; revert hr; decide)
    | (obtain ⟨-, h1, h3, h4, h5⟩ := hr; rw [L.getD_one] at h1 h3; rw [L.getD_two] at h4 h5
       exact ⟨by rw [h3, h5], h1, h4⟩)

theorem viewR_lam {r : List Word} {v : ENodeView} (hr : L.Ind.ViewR r v) (h5 : r.headD 0 = 5) :
    v = .lam (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0)) ∧ HW (r.tail.headD 0) ∧
      HW (r.tail.tail.headD 0) := by
  cases v <;> simp only [L.Ind.ViewR, h5] at hr
  all_goals first
    | (exfalso; obtain ⟨h0, -⟩ := hr; revert h0; decide)
    | (exfalso; revert hr; decide)
    | (obtain ⟨-, h1, h3, h4, h6⟩ := hr; rw [L.getD_one] at h1 h3; rw [L.getD_two] at h4 h6
       exact ⟨by rw [h3, h6], h1, h4⟩)

section qp
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (depth : Nat) (a b : EIdx) (s : AState)

end qp

/-- `lvl_eq_c` does not return at fuel `1` (its first statement is a call). -/
theorem lvlEqC_one (p : Prog) (hp : LvlCacheProg p) (u v : Word) (m m' : Mem) (r : List Word) :
    callW p 1 "lvl_eq_c" [u, v] m ≠ some (r, m') := by
  intro hc
  have h : ⦃fun s => s = (⟨m, Locals.init []⟩ : St)⦄ invoke p (exec p 1) "lvl_eq_c" [u, v]
      ⦃fun _ _ => False; ⊤⦄ := by
    rw [invoke_eq _ hp.c]
    simp only [callFn, lvlEqCL]
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, L.Ind.invoke_exec0 p "lq_find",
      L.Ind.invoke_exec0 p "lvl_eq_rec"] <;>
      grind
  obtain ⟨_, _, hf⟩ := triple_of_callW h hc
  exact hf

/-! ## `quick_sort` -/

/-- **`quick_sort`'s model, both outcomes** (generated; `e_view` and `lvl_eq_c` lifted). -/
l_model qsE_spec (p : Prog) (hf : p.lookup "quick_sort" = some quickSortL)
  fns [hf ↦ qsE list]
  specs [callW_spec p n "e_view", callW_spec p n "lvl_eq_c"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem decO_ne_zero {w : Word} (h : w ≠ 0) : decO w = some ((w - 1) != 0) := by
  unfold decO
  by_cases h1 : w = 1
  · subst h1; rfl
  · simp only [h, h1, ↓reduceIte, Option.some.injEq]
    have : w - 1 ≠ 0 := fun h' => h1 (by
      have := congrArg (· + 1) h'; simpa using this)
    simp [this]

/-! ## `quick_forall`, `quick_lam` -/

theorem peelFuel_lt : peelFuel < 2 ^ 62 := by unfold peelFuel; decide

/-- **`quick_forall`'s model, both outcomes** (generated; `e_view` lifted, `defeq_binders` by its
unified model). -/
l_model qfE_spec (p : Prog) (hf : p.lookup "quick_forall" = some quickForallL)
    (hb : p.lookup "defeq_binders" = some defeqBindersL)
  fns [hf ↦ qfE list]
  specs [callW_spec p n "e_view", dbE_spec p hb n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`quick_lam`'s model, both outcomes** (generated; `e_view` lifted, `defeq_lams` by its unified
model). -/
l_model qlE_spec (p : Prog) (hf : p.lookup "quick_lam" = some quickLamL)
    (hl : p.lookup "defeq_lams" = some defeqLamsL)
  fns [hf ↦ qlE list]
  specs [callW_spec p n "e_view", defeqLams_specE p hl n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## `quick_defeq`: the dispatch -/

/-- **`quick_defeq`'s model, both outcomes** (generated; `lit_eq` lifted, the other arms by their
unified models). -/
l_model qdE_spec (p : Prog) (hf : p.lookup "quick_defeq" = some quickDefeqL)
    (hs : p.lookup "quick_sort" = some quickSortL) (hfa : p.lookup "quick_forall" = some quickForallL)
    (hla : p.lookup "quick_lam" = some quickLamL)
    (hb : p.lookup "defeq_binders" = some defeqBindersL) (hl : p.lookup "defeq_lams" = some defeqLamsL)
  fns [hf ↦ qdE list]
  specs [callW_spec p n "lit_eq", qsE_spec p hs n, qfE_spec p hfa hb n, qlE_spec p hla hl n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem coreRef_redec {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec₁ dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r r' : List Word} {ok₁ ok : List Word → Prop}
    (h : CoreRef T a₀ dec₁ dn m₀ vis fe M eb r m ok₁) (hd : dec₁ r = dec r') (hok : ok r') :
    CoreRef T a₀ dec dn m₀ vis fe M eb r' m ok :=
  ⟨h.run, h.after, h.res.trans hd, hok⟩

theorem tag_bne (x y : Word) (hx : HW x) (hy : HW y) :
    ((decE x).tag != (decE y).tag) = decide (tagW x ≠ tagW y) := by
  rw [decE_tag x hx, decE_tag y hy]
  have h1 : (tagW x).toNat < 2 ^ 32 := by have := tagW_lt x hx; omega
  have h2 : (tagW y).toNat < 2 ^ 32 := by have := tagW_lt y hy; omega
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · intro h e; exact h (by rw [e])
  · intro h e; apply h; apply UInt64.toNat_inj.mp
    have := congrArg UInt32.toNat e
    simp only [UInt64.toNat_toUInt32] at this
    omega

/-- `lit_eq`'s model passed its view checks. -/
theorem litEqW_views {m : Mem} {a b w : Word} (h : litEqW m a b = some w) :
    viewOK m a LIT ∧ viewOK m b LIT := by
  unfold litEqW at h
  by_cases as : tierW a ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [as] at h
  by_cases ac : tcnt m LIT (tierW a) ≤ idxW a
  · simp [as, ac] at h
  by_cases bs : tierW b ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [ac, bs] at h
  by_cases bc : tcnt m LIT (tierW b) ≤ idxW b
  · simp [as, ac, bs, bc] at h
  exact ⟨⟨as, by simpa using ac⟩, ⟨bs, by simpa using bc⟩⟩

/-- An arm's answer `r`, re-listed as `(1, r)`. -/
theorem qd_arm {p : Prog} {n : Nat} {G : Prop} {x : Except Err (List Word × Mem)}
    {T : AM (Option Bool)} {a₀ : AState} {dn : NIdx → Option ConLeche.Name} {m₀ : Mem} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hG : KnotNvG p n → G)
    (h : RefE G x T a₀ (CorePost (fun r => some (decBool r)) dn m₀ vis fe M eb ResH)) :
    RefE (KnotNvG p n) (qdE.k_quick_sort p x) T a₀ (CorePost decOB dn m₀ vis fe M eb ResW) := by
  rcases x with e | ⟨r, m₁⟩
  · exact fun g => h (hG g)
  obtain ⟨y, a', hrun, hP⟩ := h
  exact RefE.ret hrun ⟨hP.after, by rw [hP.res]; rfl, ⟨hw1, hP.valid⟩⟩

/-- **`quick_defeq` refines `quickDefEq`, both outcomes**: the errors are the arms'. -/
theorem qd_ref (p : Prog) (hp : QuickProg p) (hil : InstListOK p) (hi : Inst1OK p)
    (hsd : StoreDenotes) (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d x y : Word)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hx : HW x) (hy : HW y)
    (hd : d.toNat < 2 ^ 63) :
    RefE (KnotNvG p n) (qdE p (n + 1) s₀.mem mode vis d x y)
      (quickDefEq (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE x) (decE y)) a₀
      (CorePost decOB dn s₀.mem vis fe M eb ResW) := by
  sorry

/-- **`quick_defeq` refines `quickDefEq`** at the knot: closes `QuickDefeqSpec` one level up
(`qd_ref`'s ok half). -/
@[refines ConRon.Arena.quickDefEq]
theorem quickDefeq_refines (p : Prog) (hp : QuickProg p) (hil : InstListOK p) (hi : Inst1OK p)
    (hsd : StoreDenotes) (n : Nat) (hk : KnotUpTo p n) : QuickDefeqSpec p (n + 1) :=
  fun F s₀ a₀ dn vis fe M eb mode d x y hF hn hs hx hy hd =>
    RefE.coreSpec (qdE_spec p hp.qd hp.qs hp.qf hp.ql hp.lams.peel.binders hp.lams.lams (n + 1) s₀ mode
      vis d x y)
      (qd_ref p hp hil hi hsd n hk F s₀ a₀ dn vis fe M eb mode d x y (by omega) (by omega) hs hx hy hd)

end L.Arena
