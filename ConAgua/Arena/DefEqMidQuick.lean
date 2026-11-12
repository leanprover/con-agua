module

public import ConAgua.Arena.DefEqMidPeel
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
  peel : PeelProg p
  mid : DefEqMidProg p
  lv : LvlCacheProg p
  qd : p.lookup "quick_defeq" = some quickDefeqL
  qs : p.lookup "quick_sort" = some quickSortL
  qb : p.lookup "quick_binders" = some quickBindersL
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

/-- The twin's arm match of `quickDefEq` (after the tag tests). -/
def quickPairT (mode : ConLeche.CheckMode) (r : CoreFnsA) (depth : Nat) (a b : EIdx) :
    AM (Option Bool) := do
  match ← view a, ← view b with
  | .sort u, .sort v => do
    let ok ← liftFueled "level comparison" (← lvlEq? u v)
    pure (some ok)
  | .lit l₁, .lit l₂ => pure (some (l₁ == l₂))
  | .forallE ty₁ body₁, .forallE ty₂ body₂ => do
    let ok ← defeqBinders mode r false bindersFuel depth #[] ty₁ body₁ ty₂ body₂
    pure (some ok)
  | .lam ty₁ body₁, .lam ty₂ body₂ => do
    let ok ← defeqBinders mode r true bindersFuel depth #[] ty₁ body₁ ty₂ body₂
    pure (some ok)
  | _, _ => pure none

theorem quickDefEq_eq (mode : ConLeche.CheckMode) (r : CoreFnsA) (depth : Nat) (a b : EIdx) :
    quickDefEq mode r depth a b =
      if a == b then pure (some true)
      else if a.tag != b.tag then pure none
      else if a.tag == ETag.sort || a.tag == ETag.lit || a.tag == ETag.forallE ||
          a.tag == ETag.lam then quickPairT mode r depth a b
      else pure none := by rfl

section qp
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (depth : Nat) (a b : EIdx) (s : AState)

theorem quickPairT_sort (u v : LIdx) (ha : s.store.view a = some (.sort u))
    (hb : s.store.view b = some (.sort v)) :
    (quickPairT mode r depth a b).run s = (do
      let o ← lvlEq? u v
      let ok ← liftFueled "level comparison" o
      pure (some ok) : AM (Option Bool)).run s := by
  simp only [quickPairT, StateT.run_bind, view_run _ _ _ ha, view_run _ _ _ hb, except_ok_bind]

theorem quickPairT_lit (l₁ l₂ : ConLeche.Literal) (ha : s.store.view a = some (.lit l₁))
    (hb : s.store.view b = some (.lit l₂)) :
    (quickPairT mode r depth a b).run s = .ok (some (l₁ == l₂), s) := by
  simp only [quickPairT, StateT.run_bind, view_run _ _ _ ha, view_run _ _ _ hb, except_ok_bind]; rfl

theorem quickPairT_forall (t₁ c₁ t₂ c₂ : EIdx) (ha : s.store.view a = some (.forallE t₁ c₁))
    (hb : s.store.view b = some (.forallE t₂ c₂)) :
    (quickPairT mode r depth a b).run s = (do
      let ok ← defeqBinders mode r false bindersFuel depth #[] t₁ c₁ t₂ c₂
      pure (some ok) : AM (Option Bool)).run s := by
  simp only [quickPairT, StateT.run_bind, view_run _ _ _ ha, view_run _ _ _ hb, except_ok_bind]

theorem quickPairT_lam (t₁ c₁ t₂ c₂ : EIdx) (ha : s.store.view a = some (.lam t₁ c₁))
    (hb : s.store.view b = some (.lam t₂ c₂)) :
    (quickPairT mode r depth a b).run s = (do
      let ok ← defeqBinders mode r true bindersFuel depth #[] t₁ c₁ t₂ c₂
      pure (some ok) : AM (Option Bool)).run s := by
  simp only [quickPairT, StateT.run_bind, view_run _ _ _ ha, view_run _ _ _ hb, except_ok_bind]

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

/-- **`quick_sort` refines `quickDefEq`'s sort arm, both outcomes**: its one error is its own
decline, `lvl_eq_c`'s `0` (out of level fuel), as the twin's `liftFueled "level comparison"`. -/
theorem qs_ref (p : Prog) (hp : QuickProg p) (hsd : StoreDenotes) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb : Word) (mode : ConLeche.CheckMode) (r : CoreFnsA) (depth : Nat) (a b : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe M eb) (h2a : tagW a = 2) (h2b : tagW b = 2) :
    RefE True (qsE p (n + 1) s₀.mem a b) (quickPairT mode r depth (decE a) (decE b)) a₀
      (CorePost (fun r => some (decBool r)) dn s₀.mem vis fe M eb ResH) := by
  simp only [qsE]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ c1 => eView_callW_view (a := a₀) hp.peel.eview
    hS.arena.base c1) fun ra m₁ ⟨e₁, va, hva, hvra, hta⟩ => ?_
  subst e₁; dsimp only [qsE.k_e_view]
  obtain ⟨rfl, hwa⟩ := viewR_sort hvra (hta.trans h2a)
  refine RefE.onlySim (fun _ => rfl) (fun _ _ c2 => eView_callW_view (a := a₀) hp.peel.eview
    hS.arena.base c2) fun rb m₂ ⟨e₂, vb, hvb, hvrb, htb⟩ => ?_
  subst e₂; dsimp only [qsE.k_e_view_2]
  obtain ⟨rfl, hwb⟩ := viewR_sort hvrb (htb.trans h2b)
  refine RefE.of_run_eq (quickPairT_sort mode r depth _ _ a₀ _ _ hva hvb) ?_
  obtain ⟨lu, hdu⟩ := hsd.sort dn s₀.mem a₀ vis fe M eb hS _ _ hva
  obtain ⟨lv, hdv⟩ := hsd.sort dn s₀.mem a₀ vis fe M eb hS _ _ hvb
  cases n with
  | zero => rw [callW_zero, liftE_none, qsE.k_lvl_eq_c.none]; exact RefE.of_cls0 (by simp)
  | succ n₁ =>
  cases n₁ with
  | zero =>
    exact RefE.onlySim (Q := fun _ _ => False) (fun _ => qsE.k_lvl_eq_c.none ..)
      (fun _ _ c3 => lvlEqC_one p hp.lv _ _ _ _ _ c3) fun _ _ h => h.elim
  | succ n₂ =>
  refine RefE.bind_callW (fun _ => rfl) (lvlEqC_refines p hp.lv n₂ s₀ a₀ dn vis fe M eb hS _ _ hwa hwb lu lv
    hdu hdv) fun rz m₃ _ e₃ => RefE.after_core (w := id) e₃ fun M₃ hS₃ _ => ?_
  dsimp only [qsE.k_lvl_eq_c]
  by_cases hz : rz.headD 0 = 0
  · -- the decline: `lvl_eq_c` ran out of fuel, the twin's `liftFueled` fails
    rw [ite_eq_left hz, show decO (rz.headD 0) = none by unfold decO; rw [ite_eq_left hz]]
    exact fun _ => ErrClaim.bind_left (ErrClaim.fail _ _ rfl)
  rw [ite_eq_right hz, decO_ne_zero hz]
  have h3 := e₃.resOk
  unfold ResH HW at h3
  have hres : HW (rz.headD 0 - 1) := by
    unfold HW
    generalize rz.headD 0 = z at h3 hz ⊢
    have hz' : z.toNat ≠ 0 := fun h' => hz (UInt64.toNat_inj.mp (by simpa using h'))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_one]; omega)),
      UInt64.toNat_one]
    omega
  exact RefE.ret rfl (CorePost.ret hS₃ rfl hres)

/-! ## `quick_binders` -/

/-- **`quick_binders`' model, both outcomes** (generated; `e_view` lifted, `defeq_binders` by its
unified model). -/
l_model qbE_spec (p : Prog) (hf : p.lookup "quick_binders" = some quickBindersL) (hp : PeelProg p)
  fns [hf ↦ qbE list]
  specs [callW_spec p n "e_view", dbE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`quick_binders` refines `quickDefEq`'s `∀` (`lam = 0`) and `λ` (`lam = 1`) arms, both
outcomes**: the errors are `defeq_binders`'. -/
theorem qb_ref (p : Prog) (hp : QuickProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode lam d a b : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (hlam : (lam = 0 ∧ tagW a = 6 ∧ tagW b = 6) ∨ (lam = 1 ∧ tagW a = 5 ∧ tagW b = 5))
    (hd : d.toNat < 2 ^ 63) :
    RefE (KnotNvG p n) (qbE p (n + 1) s₀.mem mode vis lam d a b)
      (quickPairT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE a) (decE b)) a₀
      (CorePost (fun r => some (decBool r)) dn s₀.mem vis fe M eb ResH) := by
  sorry

/-! ## `quick_defeq`: the dispatch -/

/-- **`quick_defeq`'s model, both outcomes** (generated; `lit_eq` lifted, the other arms by their
unified models). -/
l_model qdE_spec (p : Prog) (hf : p.lookup "quick_defeq" = some quickDefeqL)
    (hs : p.lookup "quick_sort" = some quickSortL) (hqb : p.lookup "quick_binders" = some quickBindersL)
    (hpp : PeelProg p)
  fns [hf ↦ qdE list]
  specs [callW_spec p n "lit_eq", qsE_spec p hs n, qbE_spec p hqb hpp n]
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
  have hS := hs.rel
  rw [quickDefEq_eq]
  simp only [qdE]
  by_cases he : x = y
  · have hb : (decE x == decE y) = true := by rw [decE_beq_eq _ _ hx hy]; simp [he]
    rw [ite_eq_left he]
    simp only [hb, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS rfl ⟨hw1, hw1⟩)
  rw [ite_eq_right he]
  have hb : (decE x == decE y) = false := by rw [decE_beq_eq _ _ hx hy]; simp [he]
  simp only [hb, Bool.false_eq_true, ↓reduceIte, tag_bne x y hx hy, decide_eq_true_eq]
  by_cases hg : tagW x ≠ tagW y
  · rw [ite_eq_left hg, ite_eq_left hg]
    exact RefE.ret rfl (CorePost.ret hS rfl ⟨hw0, hw0⟩)
  have hg' : tagW x = tagW y := Classical.byContradiction hg
  rw [ite_eq_right hg, ite_eq_right hg]
  simp only [tag_beq_w x hx 2 (by decide) ETag.sort rfl 2 rfl,
    tag_beq_w x hx 8 (by decide) ETag.lit rfl 8 rfl, tag_beq_w x hx 6 (by decide) ETag.forallE rfl 6 rfl,
    tag_beq_w x hx 5 (by decide) ETag.lam rfl 5 rfl, Bool.or_eq_true, decide_eq_true_eq]
  by_cases h2 : tagW x = 2
  · rw [ite_eq_left h2]
    simp only [h2, true_or, ↓reduceIte]
    cases n with
    | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
    | succ k =>
    exact qd_arm (fun _ => trivial)
      (qs_ref p hp hsd k s₀ a₀ dn vis fe M eb _ _ _ x y hS h2 (hg' ▸ h2))
  rw [ite_eq_right h2]
  by_cases h8 : tagW x = 8
  · rw [ite_eq_left h8]
    simp only [h8, true_or, or_true, ↓reduceIte]
    rcases c : callW p n "lit_eq" [x, y] s₀.mem with _ | ⟨r, m₁⟩
    · rw [liftE_none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]
    obtain ⟨k, rfl⟩ := callW_succ c
    obtain ⟨t, ht, htm, -, hlw⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (litEq_spec p hp.le hp.lq k ⟨s₀.mem, Locals.init []⟩ x y) c
    obtain ⟨vx, vy⟩ := litEqW_views hlw
    obtain ⟨l₁, hl₁⟩ := view_lit s₀.mem a₀ hS.arena.base x hx vx h8
    obtain ⟨l₂, hl₂⟩ := view_lit s₀.mem a₀ hS.arena.base y hy vy (hg' ▸ h8)
    obtain ⟨t', ht', -, -, hdec, hrh⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (litEq_refines p hp.le hp.lq k ⟨s₀.mem, Locals.init []⟩ a₀ hS.arena.base x y hx hy h8 (hg' ▸ h8)
        l₁ l₂ hl₁ hl₂) c
    have hm₁ : m₁ = s₀.mem := by rw [← ht, htm]
    rw [hm₁]
    exact RefE.ret (quickPairT_lit _ _ _ _ _ a₀ _ _ hl₁ hl₂)
      (CorePost.ret hS (by rw [decOB, ite_eq_right (show ([1, r.headD 0] : List Word).headD 0 ≠ 0 by simp)]; simp only [List.tail_cons, List.headD_cons]; rw [← hdec]; rfl) ⟨hw1, hrh⟩)
  rw [ite_eq_right h8]
  by_cases h6 : tagW x = 6
  · rw [ite_eq_left h6]
    simp only [h6, true_or, or_true, ↓reduceIte]
    cases n with
    | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
    | succ k =>
    exact qd_arm (fun g => g.mono (by omega))
      (qb_ref p hp hil k (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe M
        eb mode 0 d x y hs (.inl ⟨rfl, h6, hg' ▸ h6⟩) hd)
  rw [ite_eq_right h6]
  by_cases h5 : tagW x = 5
  · rw [ite_eq_left h5]
    simp only [h5, or_true, ↓reduceIte]
    cases n with
    | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
    | succ k =>
    exact qd_arm (fun g => g.mono (by omega))
      (qb_ref p hp hil k (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe M
        eb mode 1 d x y hs (.inr ⟨rfl, h5, hg' ▸ h5⟩) hd)
  rw [ite_eq_right h5]
  simp only [h2, h8, h6, h5, or_self, ↓reduceIte]
  exact RefE.ret rfl (CorePost.ret hS rfl ⟨hw0, hw0⟩)

/-- **`quick_defeq` refines `quickDefEq`** at the knot: closes `QuickDefeqSpec` one level up
(`qd_ref`'s ok half). -/
@[refines ConRon.Arena.quickDefEq]
theorem quickDefeq_refines (p : Prog) (hp : QuickProg p) (hil : InstListOK p) (hi : Inst1OK p)
    (hsd : StoreDenotes) (n : Nat) (hk : KnotUpTo p n) : QuickDefeqSpec p (n + 1) :=
  fun F s₀ a₀ dn vis fe M eb mode d x y hF hn hs hx hy hd =>
    RefE.coreSpec (qdE_spec p hp.qd hp.qs hp.qb hp.peel (n + 1) s₀ mode
      vis d x y)
      (qd_ref p hp hil hi hsd n hk F s₀ a₀ dn vis fe M eb mode d x y (by omega) (by omega) hs hx hy hd)

end L.Arena
