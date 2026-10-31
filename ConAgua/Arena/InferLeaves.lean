import ConAgua.Arena.KnotSlot
import ConAgua.Arena.IndView
import ConAgua.Arena.IndMaster
import ConAgua.Arena.Infer
import ConAgua.Arena.WhnfIota
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.WhnfCoreApp
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.RefECore
import ConAgua.Arena.KnotE
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.WordOff

/-!
# The leaf inference functions of `Infer.lean` (lane `defeq`)

Each function has one model and one refinement for both outcomes (`RefE` with `CorePost`) where
it is unified; its ok half (`RefE.coreSpec`) is the `CoreSpec` the knot reads.

* `ensure_sort` refines `ensureSort` from the knot's `whnf` slot (`es_ref`; `ensureSort_refines`,
  `EnsureSortSpecE`), which discharges the stage entry `ensure_sort_core` (`esc_ref`); the other
  stage entry `infer_type_core` is the `infer` slot's (`itc_ref`).
* `defeq_arg` refines `defeqArg` from the `defeq`/`defeq_e` slots (`da_ref`; `defeq_e` is
  `de_ref`, `KnotSlot.lean`) and `is_eager_reduce`'s spec (`IsEagerReduceH`, a hypothesis: its
  refinement is lane `defeq`'s other helper's).
* `infer_lit` refines the `.lit` clauses `inferLitT` (`il_ref`), `infer_const` the `.const` clause
  `inferConstT` (`inferConst_ref`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- What the leaf specs need of a program. -/
structure InferLeafProg (p : Prog) : Prop where
  ensureSort : p.lookup "ensure_sort" = some ensureSortL
  defeqArg : p.lookup "defeq_arg" = some defeqArgL
  lamResult : p.lookup "infer_lam_result" = some inferLamResultL
  derb : p.lookup "der_b" = some derB
  faf : p.lookup "forall_find" = some forallFind
  fap : p.lookup "forall_push" = some forallPush
  fai : p.lookup "intern_forall" = some internForallL
  mkfa : p.lookup "mk_forall" = some mkForall
  inferLit : p.lookup "infer_lit" = some inferLitL
  pinAt : p.lookup "pin_at" = some pinAtL
  inferConst : p.lookup "infer_const" = some inferConstL
  envix : p.lookup "env_ix" = some envIxL
  envrow : p.lookup "env_row_get" = some envRowGetL
  envfind : p.lookup "env_find" = some envFindL
  lsNode : p.lookup "ls_node" = some lsNode

/-! ## `ensure_sort` -/

/-- **`ensure_sort`'s unified model**: the `whnf` slot through its run. -/
l_model esE_spec (p : Prog) (hf : p.lookup "ensure_sort" = some ensureSortL)
  fns [hf ↦ esE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] unified

theorem tag_sort_beq (h : Word) (hh : HW h) (hg : tagW h = 2) : ((decE h).tag == ETag.sort) = true := by
  rw [decE_tag_sort_beq h hh, hg]; rfl

theorem tag_sort_ne (h : Word) (hh : HW h) (hg : tagW h ≠ 2) :
    ((decE h).tag == ETag.sort) = false := by
  rw [decE_tag_sort_beq h hh]; simpa using hg

section esr
variable (p : Prog)

/-- **`ensure_sort` refines `ensureSort`, both outcomes**: `whnf`'s errors are its slot's, a
non-sort rejects. -/
theorem es_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d e : Word)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (he : HW e) :
    RefE (KnotUpToE p n) (esE p (n + 1) s₀.mem mode vis d e)
      (ensureSort (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) a₀
      (CorePost decLv dn s₀.mem vis fe M eb ResH) := by
  simp only [esE]
  refine RefE.bind_callE (fun _ => rfl)
    ((hk n (Nat.le_refl _)).whnf F s₀ a₀ dn vis fe M eb mode d e hF hn hs he)
    (fun hG => (hG n (Nat.le_refl _)).whnf F s₀ a₀ dn vis fe M eb mode d e hF hn hs he)
    fun r₁ m₁ _ ⟨_, ⟨M₁, hS₁, hK₁, hSt₁⟩, _, hrw⟩ => ?_
  dsimp only [esE.k_whnf]
  refine RefE.guardIf (by rfl) (tag_sort_ne _ hrw)
    (fun hb g => Bool.noConfusion ((tag_sort_beq _ hrw g).symm.trans hb)) fun g1 _ => ?_
  have hg : tagW (r₁.headD 0) = 2 := by simpa using g1
  refine RefE.abort0 (by rfl) fun g2 => ?_
  refine RefE.abort0 (by rfl) fun g3 => ?_
  obtain ⟨hv, hu⟩ := L.Ind.view_sort_f m₁ _ hS₁.arena.base (r₁.headD 0) hrw ⟨g2, UInt64.not_le.mp g3⟩ hg
  exact RefE.bind_right (view_run _ _ _ hv) (RefE.ret rfl ⟨⟨M₁, hS₁, hK₁, hSt₁⟩, rfl, hu⟩)

/-- **`ensure_sort` refines `ensureSort`** at the knot (`es_ref`'s ok half). -/
@[refines ConRon.Arena.ensureSort]
theorem ensureSort_refines (hp : InferLeafProg p) (n : Nat) (hk : KnotUpTo p n) :
    EnsureSortSpec p (n + 1) :=
  fun F s₀ a₀ dn vis fe M eb mode d e hF hn hs he =>
    RefE.coreSpec (esE_spec p hp.ensureSort (n + 1) s₀ mode vis d e)
      (es_ref p n hk F s₀ a₀ dn vis fe M eb mode d e (by omega) (by omega) hs he)

end esr

/-- `ensure_sort`'s error claim (`es_ref`'s error half, at every L fuel). -/
def EnsureSortSpecE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
    HW e →
    CoreSpecE p n "ensure_sort" [mode, vis, d, e]
      (ensureSort (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) s₀ a₀

/-- `ensure_sort`'s error claim at every L fuel up to `n` (`es_ref`'s error half). -/
theorem ensureSortSpecE_of_knot (p : Prog) (hp : InferLeafProg p) :
    ∀ n, KnotUpTo p n → KnotUpToE p n → EnsureSortSpecE p n
  | 0, _, _ => fun _ s₀ a₀ _ _ _ _ _ _ _ _ _ _ _ _ => CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hkE => fun F s₀ a₀ dn vis fe M eb mode d e hF hn hs he =>
    RefE.coreSpecE (esE_spec p hp.ensureSort (n + 1) s₀ mode vis d e) trivial (hkE.mono (by omega))
      (es_ref p n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d e (by omega) (by omega) hs he)

/-! ## The stage entries `infer_type_core`, `ensure_sort_core` (the verified mode) -/

/-- **`infer_type_core`'s model, both outcomes**: the `infer` slot through its run. -/
l_model itcE_spec (p : Prog) (hf : p.lookup "infer_type_core" = some inferTypeCoreL)
  fns [hf ↦ itcE list] grind [arena_grind] unified

/-- **`ensure_sort_core`'s model, both outcomes**: `ensure_sort` through its run. -/
l_model escE_spec (p : Prog) (hf : p.lookup "ensure_sort_core" = some ensureSortCoreL)
  fns [hf ↦ escE list] grind [arena_grind] unified

section entry
variable (p : Prog) (hp : KnotEntryProg p)

/-- **`infer_type_core(vis, dep, e)` refines `inferTypeCore .verified fe F dep e`, both
outcomes**: the `infer` slot's. -/
theorem itc_ref (n : Nat) (hi : InferSlot p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (dep e : Word)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hS : CoreS dn s₀.mem a₀ vis fe M 0) (he : HW e) :
    RefE (InferSlotE p n) (itcE p (n + 1) s₀.mem vis dep e)
      (inferTypeCore .verified fe F dep.toNat (decE e)) a₀ (CorePost decH dn s₀.mem vis fe M 0 ResH) := by
  simp only [itcE]
  rcases h : callE p n "infer" [0, vis, dep, e] s₀.mem with e1 | ⟨r, m₁⟩
  · exact fun hG => CoreSpecE.of_callE (hG F s₀ a₀ dn vis fe M 0 0 dep e hF hn (slotPre_zero hS) he) h
  obtain ⟨hrun, hR⟩ := (CoreSpec.of_callW (hi F s₀ a₀ dn vis fe M 0 0 dep e hF hn (slotPre_zero hS) he)
    (callW_of_callE h)).post
  exact RefE.ret hrun ⟨hR.after, by simpa [decH] using hR.res, by simpa [ResH] using hR.valid⟩

include hp in
/-- **`infer_type_core` refines `inferTypeCore`** at the verified mode and every fuel `F ≥ n`
(`checkFuel` among them), from the `infer` slot at L-fuel `n` (`itc_ref`'s ok half). -/
@[refines_part ConRon.Arena.inferTypeCore "from InferSlot"]
theorem inferTypeCore_refines (n : Nat) (hi : InferSlot p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (dep e : Word)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hS : CoreS dn s₀.mem a₀ vis fe M 0) (he : HW e) :
    CoreSpec p (n + 1) "infer_type_core" [vis, dep, e]
      (inferTypeCore .verified fe F dep.toNat (decE e)) decH s₀ a₀ dn vis fe M 0 :=
  RefE.coreSpec (itcE_spec p hp.inferTypeCore (n + 1) s₀ vis dep e)
    (itc_ref p n hi F s₀ a₀ dn vis fe M dep e hF hn hS he)

/-- **`ensure_sort_core(vis, dep, t)` refines `ensureSortCore .verified fe F dep t`, both
outcomes**: `ensure_sort`'s. -/
theorem esc_ref (n : Nat) (hs : EnsureSortSpec p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (dep t : Word)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hS : CoreS dn s₀.mem a₀ vis fe M 0) (ht : HW t) :
    RefE (EnsureSortSpecE p n) (escE p (n + 1) s₀.mem vis dep t)
      (ensureSortCore .verified fe F dep.toNat (decE t)) a₀ (CorePost decLv dn s₀.mem vis fe M 0 ResH) := by
  simp only [escE]
  rcases h : callE p n "ensure_sort" [0, vis, dep, t] s₀.mem with e1 | ⟨r, m₁⟩
  · exact fun hG => CoreSpecE.of_callE (hG F s₀ a₀ dn vis fe M 0 0 dep t hF hn (slotPre_zero hS) ht) h
  obtain ⟨hrun, hR⟩ := (CoreSpec.of_callW (hs F s₀ a₀ dn vis fe M 0 0 dep t hF hn (slotPre_zero hS) ht)
    (callW_of_callE h)).post
  exact RefE.ret hrun ⟨hR.after, by simpa [decLv] using hR.res, by simpa [ResH] using hR.valid⟩

end entry

/-- **`ensure_sort_core` refines `ensureSortCore`** at the verified mode and every fuel `F > n`,
from the knot at every L-fuel up to `n` (`esc_ref`'s ok half). -/
@[refines_part ConRon.Arena.ensureSortCore "from KnotUpTo"]
theorem ensureSortCore_refines (p : Prog) (hp : InferLeafProg p) (he : KnotEntryProg p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (dep t : Word) (hF : n + 1 ≤ F) (hn : n + 1 ≤ 2 ^ 62)
    (hS : CoreS dn s₀.mem a₀ vis fe M 0) (ht : HW t) :
    CoreSpec p (n + 2) "ensure_sort_core" [vis, dep, t]
      (ensureSortCore .verified fe F dep.toNat (decE t)) decLv s₀ a₀ dn vis fe M 0 :=
  RefE.coreSpec (escE_spec p he.ensureSortCore (n + 2) s₀ vis dep t)
    (esc_ref p (n + 1) (ensureSort_refines p hp n hk) F s₀ a₀ dn vis fe M dep t hF hn hS ht)

/-! ## Sequencing two core runs -/

/-- **A core run, then a core run from its state**: when the whole twin run is the second run
from the first one's state, the refinement composes. -/
theorem coreRef_then {α β : Type} [Inhabited α] [Inhabited β] {T₁ : AM α} {T₂ T : AM β}
    {a₀ : AState} {dec₁ : List Word → α} {dec : List Word → β} {dn : NIdx → Option ConLeche.Name}
    {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r₁ r : List Word}
    {ok₁ ok : List Word → Prop}
    (h₁ : CoreRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb →
      CoreRef T₂ (AM.st T₁ a₀) dec dn m₁ vis fe M' eb r m ok)
    (hT : T.run a₀ = T₂.run (AM.st T₁ a₀)) : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨M', hS, hK, hSt⟩ := h₁.after
  obtain ⟨hok2, hA2, hres2, hrw2⟩ := h₂ M' hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (hT.trans (AM.run_of_ok _ _ hok2))
  exact ⟨hok, hst ▸ CoreAfter.comp hK hSt hA2, hres.trans hres2, hrw2⟩

/-! ## `defeq_arg` -/

/-- `is_eager_reduce(h)` refines `isEagerReduce` (its refinement is the other helper's, on
branch `defeq-leaves`: a hypothesis here). -/
def IsEagerReduceH (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb h : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW h →
    CoreSpec p n "is_eager_reduce" [h] (isEagerReduce (decE h)) decBool s₀ a₀ dn vis fe M eb

/-- **`defeq_arg`'s unified model**: `is_eager_reduce` lifted, the `defeq` and `defeq_e` slots
through their runs. -/
l_model daE_spec (p : Prog) (hf : p.lookup "defeq_arg" = some defeqArgL)
  fns [hf ↦ daE list]
  specs [callW_spec p n "is_eager_reduce"]
  grind [arena_grind] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What the inference functions' error arms assume: the knot's error half at the callees' fuel
and the verdict closure. -/
structure InferG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  nv : closedNV p L.Checker.nvFns = true

theorem InferG.mono {p : Prog} {n n' : Nat} (h : InferG p n) (hn : n' ≤ n) : InferG p n' :=
  ⟨h.knot.mono hn, h.nv⟩

/-- **Every spec holds at L fuel `0`** (the run fails). -/
theorem CoreSpec.zeroLet {α : Type} [Inhabited α] (p : Prog) (f : FnName) (args : List Word)
    (T : AM α) (dec : List Word → α) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word) (ok : List Word → Prop) :
    CoreSpec p 0 f args T dec s₀ a₀ dn vis fe M eb ok := by
  apply L.M.triple_of_run
  intro s r s' _ hrun
  rw [invoke_run_loc] at hrun
  obtain ⟨e, he⟩ : ∃ e, (invoke p (exec p 0) f args).run ⟨s.mem, Locals.init []⟩ = .error e := by
    simp only [invoke, lookupFn]
    cases p.lookup f with
    | none | some fd => exact ⟨_, rfl⟩
  rw [he] at hrun; cases hrun

/-- `defeq_e`'s error claim at every L fuel up to `n` (`de_ref`'s error half). -/
theorem defeqE_anyE (p : Prog) (hkp : KnotProg p) :
    ∀ n, KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d x y : Word),
    n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW x → HW y →
    CoreSpecE p n "defeq_e" [mode, vis, d, x, y]
      ((coreKnot (decMode mode) fe id F).defeqE d.toNat (decE x) (decE y)) s₀ a₀
  | 0, _, _, _, s₀, a₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hkE, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, x, y, hF, hn, hs, hx, hy =>
    RefE.coreSpecE (deE_spec p hkp.defeqE (n + 1) s₀ mode vis d x y) trivial
      (hkE n (by omega)).defeq
      (de_ref p n (hk n (by omega)).defeq F s₀ a₀ dn vis fe M eb mode d x y hF hn hs hx hy)

/-- **`defeq_arg` refines `defeqArg`, both outcomes**, at the knot: the `defeq` and `defeq_e`
slots' errors; `is_eager_reduce` (outside the verdict closure) claims nothing. -/
theorem da_ref (p : Prog) (hkp : KnotProg p) (n : Nat) (he : IsEagerReduceH p) (hk : KnotUpTo p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a ta ty : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hta : HW ta)
    (hty : HW ty) :
    RefE (InferG p n) (daE p (n + 1) s₀.mem mode vis d a ta ty)
      (defeqArg (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE ta) (decE ty)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  simp only [daE, defeqArg]
  refine RefE.bind_callW (fun _ => rfl) (he n s₀ a₀ dn vis fe M eb a hs.rel ha)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M' hS' _ => ?_
  dsimp only [daE.k_is_eager_reduce]
  have hs' : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M' eb mode := ⟨hS', hs.mode4, hs.eb_mode⟩
  by_cases h0 : r₁.headD 0 ≠ 0
  · rw [ite_eq_left h0, show decBool r₁ = true by simpa [decBool] using h0, ite_eq_left rfl,
      ← bind_pure ((coreKnot (decMode mode) fe id F).defeqE _ _ _)]
    have hde : DefeqESlot p n := by
      cases n with
      | zero => intro F s₀ a₀ dn vis fe M eb mode d x y _ _ _ _ _
                exact CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
      | succ j => exact defeqE_refines p hkp j (hk j (by omega)).defeq
    exact RefE.bind_callE (fun _ => rfl) (hde F _ _ dn vis fe M' eb mode d ta ty hF hn hs' hta hty)
      (fun (hG : InferG p n) => defeqE_anyE p hkp n hk hG.knot F _ _ dn vis fe M' eb mode d ta ty hF hn
        hs' hta hty) fun r₂ m₂ _ h₂ => RefE.ret rfl ⟨h₂.after, rfl, h₂.resOk⟩
  rw [ite_eq_right h0, show decBool r₁ = false by simpa [decBool] using h0, ite_eq_right (by decide),
    ← bind_pure ((coreKnot (decMode mode) fe id F).defeq _ _ _)]
  exact RefE.bind_callE (fun _ => rfl)
    ((hk n (Nat.le_refl _)).defeq F _ _ dn vis fe M' eb mode d ta ty hF hn hs' hta hty)
    (fun (hG : InferG p n) => (hG.knot n (Nat.le_refl _)).defeq F _ _ dn vis fe M' eb mode d ta ty hF hn
      hs' hta hty) fun r₂ m₂ _ h₂ => RefE.ret rfl ⟨h₂.after, rfl, h₂.resOk⟩

/-- **`defeq_arg` refines `defeqArg`** at the knot (`da_ref`'s ok half). -/
@[refines ConRon.Arena.defeqArg]
theorem defeqArg_refines (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (n : Nat)
    (he : IsEagerReduceH p) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a ta ty : Word)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hta : HW ta)
    (hty : HW ty) :
    CoreSpec p (n + 1) "defeq_arg" [mode, vis, d, a, ta, ty]
      (defeqArg (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE ta) (decE ty)) decBool
      s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (daE_spec p hp.defeqArg (n + 1) s₀ mode vis d a ta ty)
    (da_ref p hkp n he hk F s₀ a₀ dn vis fe M eb mode d a ta ty hF hn hs ha hta hty)

/-- `defeq_arg`'s error claim at every L fuel up to `n` (`da_ref`'s error half). -/
theorem defeqArg_anyE (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (he : IsEagerReduceH p) :
    ∀ n, KnotUpTo p n → InferG p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a ta ty : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW a →
    HW ta → HW ty →
    CoreSpecE p n "defeq_arg" [mode, vis, d, a, ta, ty]
      (defeqArg (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE ta) (decE ty)) s₀ a₀
  | 0, _, _, _, s₀, a₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hG, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, ta, ty, hF, hn, hs, ha, hta, hty =>
    RefE.coreSpecE (daE_spec p hp.defeqArg (n + 1) s₀ mode vis d a ta ty) hG.nv (hG.mono (by omega))
      (da_ref p hkp n he (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a ta ty (by omega)
        (by omega) hs ha hta hty)

/-! ## `mk_forall` under `CoreS` -/

theorem EStore.lss_internBind' (st : EStore) (tag : UInt32) (ty b : EIdx) :
    (st.internBind tag ty b).1.lss = st.lss := by
  unfold EStore.internBind
  dsimp only
  repeat' split
  all_goals rfl

theorem keeps_cpl_internForall (ty b : EIdx) : Keeps cpl (internE (.forallE ty b)) := by
  simp only [internE]; unfold Keeps; intro a r a' h
  simp only [internForallEE, StateT.run_bind, StateT.run_get, pure_bind] at h
  repeat' split at h
  all_goals simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
    ConRon.Arena.fail, throwThe, MonadExceptOf.throw] at h
  all_goals first
    | (cases h; rfl)
    | (cases h; simp only [cpl, EStore.internForallE, EStore.lss_internBind'])
    | (simp [throwThe, Functor.map, Except.map] at h)

theorem fainternW_hw (m : Mem) (a : AState) (hR : ForallR m a) (t b : Word) (w : Word) (m' : Mem)
    (hI : fainternW m t b = some (w, m')) : w.toNat < 2 ^ 32 := by
  exact consInternM_lt forallCS_wf hR hI

theorem mkForallW_hw (m : Mem) (a : AState) (hA : ArenaD m a) (t b r : Word) (m' : Mem)
    (hI : mkForallW m t b = some (r, m')) : r.toNat < 2 ^ 32 := by
  unfold mkForallW at hI
  split at hI
  · cases hI
  rcases hI₁ : fainternW m t b with _ | ⟨r₁, m₁⟩ <;> simp only [hI₁, mkK, reduceCtorEq] at hI
  split at hI
  · cases hI
  simp only [Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  exact fainternW_hw m a hA.base.forallE t b _ m₁ hI₁

theorem mkForallW_frame {m m' : Mem} {t b r : Word} (hI : mkForallW m t b = some (r, m')) :
    MemFrame [FADER, FAREC, FASLOT, tier1 FADER, tier1 FAREC, tier1 FASLOT] [30, 31] m m' := by
  unfold mkForallW at hI; split at hI; · cases hI
  exact (L.Ind.mkK_frame (by decide) (fun r₁ m₁ hx => by
    exact consInternM_frame forallCS_wf hx) hI).mono
    (by simp [ConsSch.wset, forallCS, FADER, FAREC, FASLOT]) (by simp [forallCS])

/-- **`mk_forall` refines `internE (.forallE …)` under `CoreS`.** -/
theorem mkForall_core {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (t b : Word)
    (rs : List Word) (hI : mkForallW m t b = some (rs.headD 0, m')) :
    CoreRef (internE (.forallE (decE t) (decE b))) a decH dn m vis fe M eb rs m' := by
  obtain ⟨hok, hD, hres⟩ := mkForall_ok m a hS.arena t b _ m' hI
  have hf := mkForallW_frame hI
  have hrun := AM.run_of_ok _ _ hok
  have hS' : CoreS dn m' _ vis fe M eb := hS.arena_frame hD (Keeps.run (keeps_cpl_internForall _ _) hrun) hf
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by decide)
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.arr SPN (by simp [tier1, FADER, FAREC, FASLOT, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.ctl 136 (by simp)
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _,
      StackKept.of_frame hf⟩,
    by rw [hres]; rfl, mkForallW_hw m a hS.arena t b _ m' hI⟩

/-! ## `infer_lam_result` -/

/-- The model of `infer_lam_result` past `abstract1`'s run. -/
def lamResK (p : Prog) (n : Nat) (ty : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m₁) => call1W p n "mk_forall" [ty, r.headD 0] m₁

theorem lamResK_some (p : Prog) (n : Nat) (ty : Word) (r : List Word) (m₁ : Mem) :
    lamResK p n ty (some (r, m₁)) = call1W p n "mk_forall" [ty, r.headD 0] m₁ := rfl

section lr
variable (p : Prog) (hp : InferLeafProg p)

include hp in
theorem inferLamResult_spec (n : Nat) (s₀ : St) (ty bt d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_lam_result" [ty, bt, d]
    ⦃fun r s' => LocEq s' s₀ ∧
      lamResK p n ty (callW p n "abs_entry" [bt, d, 0] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.lamResult]
  simp only [callFn, inferLamResultL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "abs_entry",
      callW_spec p n "mk_forall"] <;>
    finish [lamResK_some, call1W_some]

theorem inferLamResult_run (ty bt ab : EIdx) (d : Nat) (a a₁ : AState)
    (h : (abstract1Fast coreWalkFuel bt d 0).run a = .ok (ab, a₁)) :
    (inferLamResult ty bt d).run a = (internE (.forallE ty ab)).run a₁ := by
  simp only [inferLamResult, StateT.run_bind, h, except_ok_bind, internE]

include hp in
/-- **`infer_lam_result` refines `inferLamResult`**, from `abstract1`'s spec (`Abstract1OK`). -/
@[refines ConRon.Arena.inferLamResult]
theorem inferLamResult_refines (n : Nat) (ha : Abstract1OK p) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb ty bt d : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe M eb) (hbt : HW bt) :
    CoreSpec p (n + 1) "infer_lam_result" [ty, bt, d]
      (inferLamResult (decE ty) (decE bt) d.toNat) decH s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferLamResult_spec p hp n s₀ ty bt d)
  subst hs0
  refine ⟨hloc, ?_⟩
  cases hc : callW p n "abs_entry" [bt, d, 0] s.mem with
  | none => rw [hc] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc, lamResK_some] at hW
  have h₁ := CoreSpec.of_callW (ha n s a₀ dn vis fe M eb bt d 0 hS hbt) hc
  have hrun₁ := AM.run_of_ok _ _ h₁.run
  rw [h₁.res] at hrun₁
  have hT := inferLamResult_run (decE ty) (decE bt) _ d.toNat a₀ _ hrun₁
  cases hc2 : callW p n "mk_forall" [ty, r₁.headD 0] m₁ with
  | none => simp only [call1W, hc2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [call1W_some _ _ _ _ _ _ _ hc2] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, rfl⟩ := hW
  obtain ⟨s₂, hs₂, -, hmk⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (mkForall_spec p hp.derb hp.faf hp.fap hp.fai hp.mkfa n _ ty (r₁.headD 0)) hc2
  rw [hs₂, hr] at hmk
  exact coreRef_then h₁ (fun M' hS' => mkForall_core hS' ty (r₁.headD 0) r hmk) hT

end lr

/-! ## `infer_lit`: the `.lit` clauses -/

/-- **The `.lit` clauses of `inferBody`** (and `inferBodyIO`), copied: the twin fragment
`infer_lit` refines. -/
def inferLitT (fe : IFEnv) (l : ConLeche.Literal) : AM EIdx :=
  match l with
  | .natVal _ => do
      if ← natLitSupported fe then do
        let nn ← pinNat
        constE nn
      else fail (.invalid "Nat literal without the Nat basis declarations")
  | .strVal _ => do
      if ← strLitSupported fe then do
        let sn ← pinString
        constE sn
      else fail (.notImplemented
        "string literals before the String support declarations")

/-- `inferBody`'s `.lit` arm is `inferLitT`. -/
@[refines_part ConRon.Arena.inferBody "lit"]
theorem inferBody_lit (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)
    (l : ConLeche.Literal) (hv : a.store.view e = some (.lit l)) :
    (inferBody r fe d e).run a = (inferLitT fe l).run a := by
  simp only [inferBody, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  cases l <;> rfl

/-- `inferBodyIO`'s `.lit` arm is `inferLitT`. -/
@[refines_part ConRon.Arena.inferBodyIO "lit"]
theorem inferBodyIO_lit (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)
    (l : ConLeche.Literal) (hv : a.store.view e = some (.lit l)) :
    (inferBodyIO r fe d e).run a = (inferLitT fe l).run a := by
  simp only [inferBodyIO, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  cases l <;> rfl

/-- The callees of `infer_lit` with no proof yet (lane `whnf`'s `sorry`s and stubs): their specs. -/
structure InferLitCallees (p : Prog) : Prop where
  natLitSup : ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb : Word), CoreS dn s₀.mem a₀ vis fe M eb →
    CoreSpec p n "nat_lit_supported" [vis] (natLitSupported fe) decBool s₀ a₀ dn vis fe M eb
  strLitSup : StrLitSupportedOK p
  constE : ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb nm : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW nm →
    CoreSpec p n "const_e" [nm] (constE (decI nm)) decH s₀ a₀ dn vis fe M eb

/-- **`infer_lit`'s unified model**: the support tests, the pin and `const_e` (outside the verdict
closure) lifted. -/
l_model ilE_spec (p : Prog) (hf : p.lookup "infer_lit" = some inferLitL)
  fns [hf ↦ ilE list]
  specs [callW_spec p n "nat_lit_supported", callW_spec p n "str_lit_supported",
    callW_spec p n "pin_at", callW_spec p n "const_e"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] finish [tierW, idxW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem view_lit_f (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h LIT) (hg : tagW h = 8) :
    ∃ k : LitNode, a.store.view (decE h) = some (.lit k.l) ∧ RecRel m (tierW h) (idxW h) k := by
  obtain ⟨k, hk, hu⟩ := node_of m a h litCS RecRel (·.lits) _ hR.lit.2 hv.2
  exact ⟨k, by rw [view_tier m a hR h hh hv.1, get_lit _ h hh hg, Tbl.node?, hk]; rfl, hu⟩

/-- One `.lit` clause after its passed support test (from `m₁`, `a₁`): the pin `k` and its
constant, both outcomes (`pin_at` and `const_e` lifted). -/
theorem il_arm (p : Prog) (hp : InferLeafProg p) (hc : InferLitCallees p) (n : Nat) (k : Nat)
    (hk : k < 51) {m₁ : Mem} {a₁ : AState} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m₁ a₁ vis fe M eb) :
    RefE (closedNV p L.Checker.nvFns = true) (ilE.k_pin_at p n (liftE (callW p n "pin_at" [k.toUInt64] m₁)))
      (pinAt k >>= constE) a₁ (CorePost decH dn m₁ vis fe M eb ResH) := by
  refine RefE.bindLift (fun _ => rfl) fun r₂ m₂ c2 => ?_
  obtain ⟨s₂, hs₂, hm₂, -, hlt, hpin⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (pinAt_refines p hp.pinAt n _ a₁ ⟨fun _ => hS.pins⟩ k.toUInt64) c2
  have hm : m₂ = m₁ := hs₂.symm.trans hm₂
  subst hm
  rw [show k.toUInt64.toNat = k by simp; omega] at hpin
  refine ⟨_, _, hpin, ?_⟩
  dsimp only [ilE.k_pin_at]
  rw [← bind_pure (constE _)]
  exact RefE.bind_callW (fun _ => rfl) (hc.constE n ⟨m₂, Locals.init []⟩ _ dn vis fe M eb (r₂.headD 0) hS hlt)
    fun r₃ m₃ _ h₃ => RefE.ret rfl ⟨h₃.after, rfl, h₃.resOk⟩

/-- **`infer_lit(vis, e)` refines the `.lit` clauses** (`inferLitT`) at the literal the handle
views, both outcomes: a `Nat` literal without its basis rejects, a `String` literal without its
support declines; the support tests, the pin and `const_e` (`InferLitCallees`) claim nothing. -/
theorem il_ref (p : Prog) (hp : InferLeafProg p) (hc : InferLitCallees p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb e : Word) (l : ConLeche.Literal) (hS : CoreS dn s₀.mem a₀ vis fe M eb)
    (he : HW e) (hg : tagW e = 8) (hv : a₀.store.view (decE e) = some (.lit l)) :
    RefE (closedNV p L.Checker.nvFns = true) (ilE p (n + 1) s₀.mem vis e) (inferLitT fe l) a₀
      (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  simp only [ilE]
  refine RefE.abort0 (by rfl) fun h1 => ?_
  refine RefE.abort0 (by rfl) fun h2 => ?_
  obtain ⟨k, hk, hrel⟩ := view_lit_f s₀.mem a₀ hS.arena.base e he ⟨h1, UInt64.not_le.mp h2⟩ hg
  rw [hv] at hk
  have hl : l = k.l := by simpa using hk
  subst hl
  obtain ⟨l⟩ := k
  by_cases h3 : tfld s₀.mem LIT (tierW e) (idxW e) 0 = 0
  · rw [ite_eq_left h3]
    cases l with
    | strVal str => simp [RecRel, StrRec, h3] at hrel
    | natVal N =>
    simp only [inferLitT]
    refine RefE.bind_callW (fun _ => rfl) (hc.natLitSup n s₀ a₀ dn vis fe M eb hS)
      fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
    dsimp only [ilE.k_nat_lit_supported]
    refine RefE.guardIf (by rfl) (fun h0 => by simp only [decBool, h0]; rfl)
      (fun hb => by simpa [decBool] using hb)
      fun _ _ => ?_
    exact il_arm p hp hc n 1 (by decide) hS₁
  · rw [ite_eq_right h3]
    cases l with
    | natVal N => simp [RecRel, NatRec, h3] at hrel
    | strVal str =>
    simp only [inferLitT]
    refine RefE.bind_callW (fun _ => rfl) (hc.strLitSup n s₀ a₀ dn vis fe M eb hS)
      fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
    dsimp only [ilE.k_str_lit_supported]
    refine RefE.guardIf (by rfl) (fun h0 => by simp only [decBool, h0]; rfl)
      (fun hb => by simpa [decBool] using hb)
      fun _ _ => ?_
    exact il_arm p hp hc n 5 (by decide) hS₁

/-- **`infer_lit(vis, e)` refines the `.lit` clauses** (`il_ref`'s ok half). -/
@[refines_part ConRon.Arena.inferBody "lit (inferLitT)"]
theorem inferLit_refines (p : Prog) (hp : InferLeafProg p) (hc : InferLitCallees p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb e : Word) (l : ConLeche.Literal) (hS : CoreS dn s₀.mem a₀ vis fe M eb)
    (he : HW e) (hg : tagW e = 8) (hv : a₀.store.view (decE e) = some (.lit l)) :
    CoreSpec p (n + 1) "infer_lit" [vis, e] (inferLitT fe l) decH s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (ilE_spec p hp.inferLit (n + 1) s₀ vis e)
    (il_ref p hp hc n s₀ a₀ dn vis fe M eb e l hS he hg hv)

/-! ## `infer_const`: the `.const` clause -/

/-- **The `.const` clause of `inferBody`**, copied: the twin fragment `infer_const` refines.
(`inferBodyIO`'s clause reads the length with `viewLsLen` instead: another fragment.) -/
def inferConstT (fe : IFEnv) (n : NIdx) (us : LsIdx) : AM EIdx :=
  match fe.find? n with
  | none => do
    let err ← unknownConstError n
    fail err
  | some ci => do
    let cv := ci.toConstantVal
    let usl ← viewLs us
    if usl.length != cv.levelParams.length then do
      fail (.invalid "incorrect number of universe levels")
    else constTyAt cv us

/-- `inferBody`'s `.const` arm is `inferConstT`. -/
@[refines_part ConRon.Arena.inferBody "const"]
theorem inferBody_const (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState) (n : NIdx)
    (us : LsIdx) (hv : a.store.view e = some (.const n us)) :
    (inferBody r fe d e).run a = (inferConstT fe n us).run a := by
  simp only [inferBody, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  rfl

/-- A decoded constant record has its `ConstantVal` at `q + 1`. -/
theorem decCI_cvA {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {ci : IConstantInfo} (h : decCI a dn q.toNat = some ci) (hab : ArrExt a b) :
    decCV b (q.toNat + 1) = some ci.toConstantVal := by
  cases hq : a[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | k
  all_goals (rw [hk] at h; simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h)
  all_goals first
    | (simp at h; done)
    | ((first
        | obtain ⟨cv, hcv, rfl⟩ := h
        | obtain ⟨cv, hcv, _, -, rfl⟩ := h
        | obtain ⟨cv, hcv, _, -, _, -, rfl⟩ := h
        | obtain ⟨cv, hcv, _, -, _, -, _, -, rfl⟩ := h
        | obtain ⟨cv, hcv, _, -, _, -, _, -, _, -, rfl⟩ := h
        | obtain ⟨cv, hcv, _, -, _, -, _, -, _, -, _, -, rfl⟩ := h
        | obtain ⟨cv, hcv, _, -, _, -, _, -, _, -, _, -, _, -, rfl⟩ := h)
       exact hab.decCV hcv)

theorem mapM_len {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (xs : List β), l.mapM f = some xs → xs.length = l.length
  | [], xs, h => by simp at h; subst h; rfl
  | a :: l, xs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, -, ys, hys, rfl⟩ := h
    simp [mapM_len f l ys hys]

theorem hslice?_length {k : IdxKind} {b : Array Word} {o c : Nat} {xs : List (Idx k)}
    (h : hslice? b o c = some xs) : xs.length = c := by
  unfold hslice? at h; simpa using mapM_len _ _ _ h

/-- The words of a decoded `ConstantVal` at `q + 1`: name, level-parameter slice, type. -/
theorem infer_decCV_words {b : Array Word} {q : Word} {cv : IConstantVal}
    (h : decCV b (q.toNat + 1) = some cv) (hsz : b.size < 2 ^ 63) :
    HW (rdW b (q + 1)) ∧ cv.name = decI (rdW b (q + 1)) ∧ HW (rdW b (q + 4)) ∧
      cv.type = decI (rdW b (q + 4)) ∧
      hslice? b (rdW b (q + 2)).toNat (rdW b (q + 3)).toNat = some cv.levelParams := by
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨nm, hn, ls, hl, ty, ht, rfl⟩ := h
  obtain ⟨w1, hw1, hl1, rfl⟩ := hd?_eq hn
  obtain ⟨w4, hw4, hl4, rfl⟩ := hd?_eq ht
  have hlt : q.toNat + 1 + 3 < b.size := by
    rcases Nat.lt_or_ge (q.toNat + 1 + 3) b.size with h' | h'
    · exact h'
    · simp [Array.getElem?_eq_none h'] at hw4
  have hq : q.toNat < 2 ^ 63 := by omega
  have r1 : rdW b (q + 1) = w1 := by simp (disch := omega) only [rdW, off_toNat, hw1]; rfl
  have r4 : rdW b (q + 4) = w4 := by
    simp (disch := omega) only [rdW, off_toNat]; rw [show q.toNat + 4 = q.toNat + 1 + 3 by omega, hw4]; rfl
  simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hl
  obtain ⟨o, ⟨wo, hwo, rfl⟩, c, ⟨wc, hwc, rfl⟩, hs⟩ := hl
  have r2 : rdW b (q + 2) = wo := by
    simp (disch := omega) only [rdW, off_toNat]; rw [show q.toNat + 2 = q.toNat + 1 + 1 by omega, hwo]; rfl
  have r3 : rdW b (q + 3) = wc := by
    simp (disch := omega) only [rdW, off_toNat]; rw [show q.toNat + 3 = q.toNat + 1 + 1 + 1 by omega, hwc]; rfl
  rw [r1, r2, r3, r4]
  exact ⟨hl1, rfl, hl4, rfl, hs⟩

theorem viewLs_run (h : LsIdx) (a : AState) (ids : List LIdx) (hv : a.store.lss.view h = some ids) :
    (viewLs h).run a = .ok (ids, a) := by
  simp [viewLs, hv, StateT.run_bind, StateT.run_get]; rfl

theorem coreRef_congr {α : Type} [Inhabited α] {T T' : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} (h : T.run a₀ = T'.run a₀)
    (h' : CoreRef T' a₀ dec dn m₀ vis fe M eb r m ok) : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨h1, h2, h3, h4⟩ := h'
  refine ⟨?_, ?_, ?_, h4⟩ <;> unfold AM.ok AM.st AM.res at * <;> rw [h] <;> assumption

/-- **`infer_const`'s unified model**: every callee (outside the verdict closure) lifted. -/
l_model inferConstE_spec (p : Prog) (hf : p.lookup "infer_const" = some inferConstL)
    (hls : p.lookup "ls_node" = some lsNode)
  fns [hf ↦ inferConstE list]
  specs [callW_spec p n "env_find", lsNode_spec p hls n, callW_spec p n "const_ty_at", callW_spec p n "pin_at"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] finish [tierW, idxW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`infer_const(vis, n, us)` refines the `.const` clause** (`inferConstT`), both outcomes: an
unknown name rejects, `sorryAx` declines (`unknownConstError`), a level count mismatch rejects;
the callees claim nothing (`nvFns`). `const_ty_at`'s ok half from its spec (`ConstTyAtOK`). -/
theorem inferConst_ref (p : Prog) (hp : InferLeafProg p) (hct : ConstTyAtOK p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb nm us : Word) (hS : CoreS dn s₀.mem a₀ vis fe M eb) (hnm : HW nm)
    (hus : HW us) :
    RefE (closedNV p L.Checker.nvFns = true) (inferConstE p (n + 1) s₀.mem vis nm us)
      (inferConstT fe (decI nm) (decI us)) a₀ (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  simp only [inferConstE]
  refine RefE.onlySim (fun _ => rfl) (fun r₁ m₁ c1 => And.intro (triple_of_callW
      (envFind_refines p hp.envix hp.envrow hp.envfind n ⟨s₀.mem, Locals.init []⟩ vis nm hS.env hnm) c1)
      (triple_of_callW (envFind_found p hp.envix hp.envrow hp.envfind n ⟨s₀.mem, Locals.init []⟩ vis nm hnm) c1))
    fun r₁ m₁ ⟨⟨t₁, ht₁, hm₁, _, hfind⟩, ⟨_, _, _, _, hfound⟩⟩ => ?_
  rw [ht₁] at hm₁
  subst hm₁
  dsimp only [inferConstE.k_env_find]
  by_cases h0 : r₁.headD 0 = 0
  · -- `unknownConstError`
    rw [ite_eq_left h0]
    have hnone : fe.find? (decI nm) = none := by rw [hfind]; simp only [decFound, h0, ite_true]
    refine RefE.onlySim (fun _ => rfl) (fun r₂ m₂ c2 => triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (pinAt_refines p hp.pinAt n ⟨s₀.mem, Locals.init []⟩ a₀ ⟨fun _ => hS.pins⟩ 13) c2)
      fun r₂ m₂ ⟨t₂, ht₂, hm₂, _, hlt, hpin⟩ => ?_
    have hue : (unknownConstError (decI nm)).run a₀ = .ok (if nm = r₂.headD 0 then
        CheckError.notImplemented "use of the sorryAx axiom" else .invalid "unknown constant", a₀) := by
      have hb := decI_beq (k := .name) nm (r₂.headD 0) hnm hlt
      simp only [unknownConstError, pinSorryAx, show PIN_SORRY_AX = (13 : Word).toNat from rfl,
        StateT.run_bind, hpin, except_ok_bind, hb]
      by_cases he : nm = r₂.headD 0
      · simp only [he, ↓reduceIte]; rfl
      · simp only [he, ↓reduceIte]; rfl
    rw [show inferConstT fe (decI nm) (decI us) = (unknownConstError (decI nm) >>= fun err => fail err) by
      simp only [inferConstT, hnone]]
    refine RefE.bind_right hue ?_
    dsimp only [inferConstE.k_pin_at]
    by_cases he : nm = r₂.headD 0
    · rw [ite_eq_left he, ite_eq_left he]; exact fun _ => ErrClaim.fail _ _ rfl
    · rw [ite_eq_right he, ite_eq_right he]; exact fun _ => ErrClaim.fail _ _ rfl
  -- found: the level count
  rw [ite_eq_right h0]
  obtain ⟨htag, hrow, hq⟩ := hfound h0
  obtain ⟨ci, hci⟩ := hS.env.found_some nm hnm htag hrow
  have hfind' : fe.find? (decI nm) = some ci := by
    rw [hfind]; simp only [decFound, h0, ↓reduceIte, hq]; exact hci
  rw [← hq] at hci
  have hcv := decCI_cvA hci (erecP_ext _)
  generalize hcvr : ci.toConstantVal = cv at hcv
  refine RefE.abort0 (by rfl) fun hne => ?_
  obtain ⟨hw1, hname, hw4, hty, hsl⟩ := infer_decCV_words hcv hS.erec
  obtain ⟨ids, hv, hlen1, hlen2⟩ := lsNodeW_view hS.arena.base hus hne
  rw [show inferConstT fe (decI nm) (decI us) = (viewLs (decI us) >>= fun usl =>
      if (usl.length != cv.levelParams.length) = true then fail (.invalid "incorrect number of universe levels")
      else constTyAt cv (decI us)) by simp only [inferConstT, hfind', hcvr]]
  refine RefE.bind_right (viewLs_run _ _ _ hv) ?_
  refine RefE.guardThen (by rfl)
    (fun hl => by
      rw [hslice?_length hsl, ← hlen2, ← hlen1]
      simp only [bne_iff_ne, ne_eq]
      intro h; exact hl (UInt64.toNat_inj.mp h))
    (fun hb hl => by rw [hslice?_length hsl, ← hl, hlen1, hlen2] at hb; simp at hb) fun _ _ => ?_
  have hcv' : cv = ⟨decI (rdW (s₀.mem.arr64 EREC) (r₁.tail.headD 0 + 1)), cv.levelParams,
      decE (rdW (s₀.mem.arr64 EREC) (r₁.tail.headD 0 + 4))⟩ := by
    rw [← hname, decE_eq, ← hty]
  rw [hcv', ← bind_pure (constTyAt _ _)]
  refine RefE.bind_callW (fun _ => rfl)
    (hct n s₀ a₀ dn vis fe M eb _ _ _ _ us cv.levelParams hS hw1 hw4 hus hsl)
    fun r₃ m₃ _ h₃ => ?_
  exact RefE.ret rfl ⟨h₃.after, rfl, h₃.resOk⟩

/-- **`infer_const` refines the `.const` clause** (`inferConst_ref`'s ok half). -/
@[refines_part ConRon.Arena.inferBody "const (inferConstT)"]
theorem inferConst_refines (p : Prog) (hp : InferLeafProg p) (hct : ConstTyAtOK p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb nm us : Word) (hS : CoreS dn s₀.mem a₀ vis fe M eb) (hnm : HW nm)
    (hus : HW us) :
    CoreSpec p (n + 1) "infer_const" [vis, nm, us] (inferConstT fe (decI nm) (decI us)) decH s₀ a₀
      dn vis fe M eb :=
  RefE.coreSpec (inferConstE_spec p hp.inferConst hp.lsNode (n + 1) s₀ vis nm us)
    (inferConst_ref p hp hct n s₀ a₀ dn vis fe M eb nm us hS hnm hus)

end L.Arena
