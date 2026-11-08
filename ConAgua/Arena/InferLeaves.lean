module

public import ConAgua.Arena.KnotSlot
import ConAgua.Arena.IndView
import ConAgua.Arena.IndMaster
public import ConAgua.Arena.Infer
public import ConAgua.Arena.WhnfIota
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
public import ConAgua.Arena.WhnfCoreApp
import ConAgua.Arena.WhnfCoreRefine
public import ConAgua.Arena.RefECore
public import ConAgua.Arena.KnotE
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.WordOff
import ConAgua.Arena.DerRel
import ConAgua.Arena.RefWalk
import all ConAgua.Arena.Infer
import all ConAgua.Arena.Knot
import all ConAgua.Arena.LevelEquiv

@[expose] public section

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
      (ensureSort (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE e)) a₀
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

end esr

/-- `ensure_sort`'s error claim (`es_ref`'s error half, at every L fuel). -/
def EnsureSortSpecE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
    HW e →
    CoreSpecE p n "ensure_sort" [mode, vis, d, e]
      (ensureSort (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE e)) s₀ a₀

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
      ((coreKnot (decMode mode) (decEager mode) fe id F).defeqE d.toNat (decE x) (decE y)) s₀ a₀
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
      (defeqArg (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE a) (decE ta) (decE ty)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  simp only [daE, defeqArg]
  refine RefE.bind_callW (fun _ => rfl) (he n s₀ a₀ dn vis fe M eb a hs.rel ha)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M' hS' _ => ?_
  dsimp only [daE.k_is_eager_reduce]
  have hs' : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M' eb mode := ⟨hS', hs.mode4, hs.eb_mode⟩
  by_cases h0 : r₁.headD 0 ≠ 0
  · rw [ite_eq_left h0, show decBool r₁ = true by simpa [decBool] using h0, ite_eq_left rfl,
      ← bind_pure ((coreKnot (decMode mode) (decEager mode) fe id F).defeqE _ _ _)]
    have hde : DefeqESlot p n := by
      cases n with
      | zero => intro F s₀ a₀ dn vis fe M eb mode d x y _ _ _ _ _
                exact CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
      | succ j => exact defeqE_refines p hkp j (hk j (by omega)).defeq
    exact RefE.bind_callE (fun _ => rfl) (hde F _ _ dn vis fe M' eb mode d ta ty hF hn hs' hta hty)
      (fun (hG : InferG p n) => defeqE_anyE p hkp n hk hG.knot F _ _ dn vis fe M' eb mode d ta ty hF hn
        hs' hta hty) fun r₂ m₂ _ h₂ => RefE.ret rfl ⟨h₂.after, rfl, h₂.resOk⟩
  rw [ite_eq_right h0, show decBool r₁ = false by simpa [decBool] using h0, ite_eq_right (by decide),
    ← bind_pure ((coreKnot (decMode mode) (decEager mode) fe id F).defeq _ _ _)]
  exact RefE.bind_callE (fun _ => rfl)
    ((hk n (Nat.le_refl _)).defeq F _ _ dn vis fe M' eb mode d ta ty hF hn hs' hta hty)
    (fun (hG : InferG p n) => (hG.knot n (Nat.le_refl _)).defeq F _ _ dn vis fe M' eb mode d ta ty hF hn
      hs' hta hty) fun r₂ m₂ _ h₂ => RefE.ret rfl ⟨h₂.after, rfl, h₂.resOk⟩

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
include hp in
theorem inferLamResult_run (ty bt ab : EIdx) (d : Nat) (a a₁ : AState)
    (h : (abstract1Fast coreWalkFuel bt d 0).run a = .ok (ab, a₁)) :
    (inferLamResult ty bt d).run a = (internE (.forallE ty ab)).run a₁ := by
  simp only [inferLamResult, StateT.run_bind, h, except_ok_bind, internE]

include hp in
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
      if ← strLitStored fe then do
        let sn ← pinString
        constE sn
      else fail (.notImplemented
        "string literals before the String support declarations")

/-- `inferBody`'s `.lit` arm is `inferLitT`. -/
@[refines_part ConRon.Arena.inferBody "lit"]
theorem inferBody_lit (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)
    (l : ConLeche.Literal) (hv : a.store.view e = some (.lit l)) :
    (inferBody r fe d e).run a = (inferLitT fe l).run a := by
  sorry

/-- `inferBodyIO`'s `.lit` arm is `inferLitT`. -/
@[refines_part ConRon.Arena.inferBodyIO "lit"]
theorem inferBodyIO_lit (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)
    (l : ConLeche.Literal) (hv : a.store.view e = some (.lit l)) :
    (inferBodyIO r fe d e).run a = (inferLitT fe l).run a := by
  sorry

/-- The callees of `infer_lit` with no proof yet (lane `whnf`'s `sorry`s and stubs): their specs. -/
structure InferLitCallees (p : Prog) : Prop where
  natLitSup : ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb : Word), CoreS dn s₀.mem a₀ vis fe M eb →
    CoreSpec p n "nat_lit_supported" [vis] (natLitSupported fe) decBool s₀ a₀ dn vis fe M eb
  strLitSup : StrLitStoredOK p
  constE : ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb nm : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW nm →
    CoreSpec p n "const_e" [nm] (constE (decI nm)) decH s₀ a₀ dn vis fe M eb

/-- **`infer_lit`'s unified model**: the support tests, the pin and `const_e` (outside the verdict
closure) lifted. -/
l_model ilE_spec (p : Prog) (hf : p.lookup "infer_lit" = some inferLitL)
  fns [hf ↦ ilE list]
  specs [callW_spec p n "nat_lit_supported", callW_spec p n "str_lit_stored",
    callW_spec p n "pin_at", callW_spec p n "const_e"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] finish [tierW, idxW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem view_lit_f (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h LIT) (hg : tagW h = 8) :
    ∃ k : LitNode, a.store.view (decE h) = some (.lit k.l) ∧ RecRel m (tierW h) (idxW h) k := by
  obtain ⟨k, hk, hu⟩ := node_of m a h litCS RecRel (·.lits) _ hR.lit.2 hv.2
  exact ⟨k, by rw [view_tier m a hR h hh hv.1, get_lit _ h hh hg, Tbl.node?, hk]; rfl, hu⟩

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
    {ci : IConstantInfo} (h : decCI (aread a) q.toNat = some ci) (hab : ArrExt (aread a) (aread b)) :
    decCV (aread b) (q.toNat + 1) = some ci.toConstantVal := by
  sorry

theorem mapM_len {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (xs : List β), l.mapM f = some xs → xs.length = l.length
  | [], xs, h => by simp at h; subst h; rfl
  | a :: l, xs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, -, ys, hys, rfl⟩ := h
    simp [mapM_len f l ys hys]

theorem hslice?_length {k : IdxKind} {b : Array Word} {o c : Nat} {xs : List (Idx k)}
    (h : hslice? (aread b) o c = some xs) : xs.length = c := by
  unfold hslice? at h; simpa using mapM_len _ _ _ h

/-- The words of a decoded `ConstantVal` at `q + 1`: name, level-parameter slice, type. -/
theorem infer_decCV_words {b : Array Word} {q : Word} {cv : IConstantVal}
    (h : decCV (aread b) (q.toNat + 1) = some cv) (hsz : b.size < 2 ^ 63) :
    HW (rdW b (q + 1)) ∧ cv.name = decI (rdW b (q + 1)) ∧ HW (rdW b (q + 4)) ∧
      cv.type = decI (rdW b (q + 4)) ∧
      hslice? (aread b) (rdW b (q + 2)).toNat (rdW b (q + 3)).toNat = some cv.levelParams := by
  sorry

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

end L.Arena
