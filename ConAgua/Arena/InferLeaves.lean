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

/-!
# The leaf inference functions of `Infer.lean` (lane `defeq`)

The callW pattern (`WhnfCoreRefine.lean`): a word model of each function with its callees
through their runs, the L spec by `vcgen` + `finish`, the refinement from the callees' specs.

* `ensure_sort` refines `ensureSort` from the knot's `whnf` slot (`ensureSort_refines`), which
  discharges `EnsureSortSpec` (`ensureSortCore_refines`).
* `defeq_arg` refines `defeqArg` from the `defeq`/`defeq_e` slots and `is_eager_reduce`'s spec
  (`IsEagerReduceH`, a hypothesis: its refinement is lane `defeq`'s other helper's).
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

/-- The model of `ensure_sort` past `whnf`'s run `res`: the sort record's word. -/
def ensureSortK (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m₁) =>
    if r.headD 0 >>> 28 ≠ 2 then none
    else if tierW (r.headD 0) ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0 then none
    else if tcnt m₁ SORT (tierW (r.headD 0)) ≤ idxW (r.headD 0) then none
    else some (tfld m₁ SORT (tierW (r.headD 0)) (idxW (r.headD 0)) 0, m₁)

theorem ensureSortK_ok (m₁ : Mem) (r : List Word) (h1 : r.headD 0 >>> 28 = 2)
    (h2 : ¬ (tierW (r.headD 0) ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0))
    (h3 : idxW (r.headD 0) < tcnt m₁ SORT (tierW (r.headD 0))) :
    ensureSortK (some (r, m₁)) =
      some (tfld m₁ SORT (tierW (r.headD 0)) (idxW (r.headD 0)) 0, m₁) := by
  have h3' : ¬ tcnt m₁ SORT (tierW (r.headD 0)) ≤ idxW (r.headD 0) := by
    simpa using h3
  simp only [ensureSortK, h1, h2, h3', ne_eq, not_true_eq_false, ↓reduceIte]

section es
variable (p : Prog) (hp : InferLeafProg p)

include hp in
theorem ensureSort_spec (n : Nat) (s₀ : St) (mode vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ensure_sort" [mode, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ ensureSortK (callW p n "whnf" [mode, vis, d, e] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.ensureSort]
  simp only [callFn, ensureSortL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "whnf",
      evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
    finish [ensureSortK_ok, tierW, idxW]

end es

theorem tag_sort_beq (h : Word) (hh : HW h) (hg : h >>> 28 = 2) : ((decE h).tag == ETag.sort) = true := by
  rw [decE_tag h hh, hg]; decide

theorem ensureSort_run (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e x : EIdx) (u : LIdx) (a a₁ : AState)
    (hw : (r.whnf d e).run a = .ok (x, a₁)) (ht : (x.tag == ETag.sort) = true)
    (hv : a₁.store.view x = some (.sort u)) :
    (ensureSort r fe d e).run a = .ok (u, a₁) := by
  simp only [ensureSort, StateT.run_bind, hw, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv]
  rfl

section esr
variable (p : Prog) (hp : InferLeafProg p)

include hp in
/-- **`ensure_sort` refines `ensureSort`** at the knot, from the knot's `whnf` slot. -/
@[refines ConRon.Arena.ensureSort]
theorem ensureSort_refines (n : Nat) (hk : KnotUpTo p n) : EnsureSortSpec p (n + 1) := by
  intro F s₀ a₀ dn vis fe M eb mode d e hF hn hs he
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (ensureSort_spec p hp n s₀ mode vis d e)
  subst hs0
  refine ⟨hloc, ?_⟩
  cases hc : callW p n "whnf" [mode, vis, d, e] s.mem with
  | none => rw [hc] at hW; simp [ensureSortK] at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW
    ((hk n (Nat.le_refl _)).whnf F s a₀ dn vis fe M eb mode d e (by omega) (by omega) hs he) hc
  rw [hc] at hW; simp only [ensureSortK] at hW
  obtain ⟨h1, hW⟩ := of_ite_none hW
  obtain ⟨h2, hW⟩ := of_ite_none hW
  obtain ⟨h3, hW⟩ := of_ite_none hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  have hg : r₁.headD 0 >>> 28 = 2 := by simpa using h1
  obtain ⟨hv, hu⟩ := L.Ind.view_sort_f m₁ _ hS₁.arena.1 (r₁.headD 0) hrw
    ⟨h2, by simpa using h3⟩ hg
  have hrun := ensureSort_run _ fe d.toNat (decE e) _ _ a₀ _ (by rw [AM.run_of_ok _ _ hok, hres]; rfl)
    (tag_sort_beq _ hrw hg) hv
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok', ?_, by rw [hres', decLv, ← hr], by unfold ResH; rw [← hr]; exact hu⟩
  rw [hst', ← hm]; exact ⟨M', hS₁, hK₁, hSt₁⟩

end esr

/-- **`ensure_sort_core` refines `ensureSortCore`** at the verified mode and every fuel `F > n`,
from the knot at every L-fuel up to `n`. -/
@[refines_part ConRon.Arena.ensureSortCore "from KnotUpTo"]
theorem ensureSortCore_refines (p : Prog) (hp : InferLeafProg p) (he : KnotEntryProg p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (dep t : Word) (hF : n + 1 ≤ F) (hn : n + 1 ≤ 2 ^ 62)
    (hS : CoreS dn s₀.mem a₀ vis fe M 0) (ht : HW t) :
    CoreSpec p (n + 2) "ensure_sort_core" [vis, dep, t]
      (ensureSortCore .verified fe F dep.toNat (decE t)) decLv s₀ a₀ dn vis fe M 0 :=
  ensureSortCore_of_spec p he (n + 1) (ensureSort_refines p hp n hk) F s₀ a₀ dn vis fe M dep t hF hn
    hS ht

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
  obtain ⟨M', hS, hK, hSt⟩ := h₁.2.1
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

/-- The model of `defeq_arg` past `is_eager_reduce`'s run `res`. -/
def defeqArgK (p : Prog) (n : Nat) (mode vis d ta ty : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m₁) =>
    if r.headD 0 ≠ 0 then call1W p n "defeq_e" [mode, vis, d, ta, ty] m₁
    else call1W p n "defeq" [mode, vis, d, ta, ty] m₁

theorem defeqArgK_e (p : Prog) (n : Nat) (mode vis d ta ty : Word) (r : List Word) (m₁ : Mem)
    (h : r.headD 0 ≠ 0) :
    defeqArgK p n mode vis d ta ty (some (r, m₁)) = call1W p n "defeq_e" [mode, vis, d, ta, ty] m₁ := by
  simp only [defeqArgK, h, ne_eq, not_false_eq_true, ↓reduceIte]

theorem defeqArgK_p (p : Prog) (n : Nat) (mode vis d ta ty : Word) (r : List Word) (m₁ : Mem)
    (h : r.headD 0 = 0) :
    defeqArgK p n mode vis d ta ty (some (r, m₁)) = call1W p n "defeq" [mode, vis, d, ta, ty] m₁ := by
  simp only [defeqArgK, h, ne_eq, not_true_eq_false, ↓reduceIte]

section da
variable (p : Prog) (hp : InferLeafProg p)

include hp in
theorem defeqArg_spec (n : Nat) (s₀ : St) (mode vis d a ta ty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq_arg" [mode, vis, d, a, ta, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ defeqArgK p n mode vis d ta ty
      (callW p n "is_eager_reduce" [a] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.defeqArg]
  simp only [callFn, defeqArgL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "is_eager_reduce",
      callW_spec p n "defeq_e", callW_spec p n "defeq"] <;>
    finish [defeqArgK_e, defeqArgK_p, call1W_some]

end da

theorem defeqArg_run (r : CoreFnsA) (d : Nat) (a ta ty : EIdx) (a₀ a₁ : AState) (b : Bool)
    (h : (isEagerReduce a).run a₀ = .ok (b, a₁)) :
    (defeqArg r d a ta ty).run a₀ = (if b then r.defeqE d ta ty else r.defeq d ta ty).run a₁ := by
  cases b <;> simp [defeqArg, StateT.run_bind, h, except_ok_bind]

section dar
variable (p : Prog) (hp : InferLeafProg p)

include hp in
/-- **`defeq_arg` refines `defeqArg`** at the knot, from the `defeq` and `defeq_e` slots and
`is_eager_reduce`'s spec. -/
@[refines ConRon.Arena.defeqArg]
theorem defeqArg_refines (n : Nat) (he : IsEagerReduceH p) (hd : DefeqSlot p n)
    (hde : DefeqESlot p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a ta ty : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hta : HW ta)
    (hty : HW ty) :
    CoreSpec p (n + 1) "defeq_arg" [mode, vis, d, a, ta, ty]
      (defeqArg (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE ta) (decE ty)) decBool
      s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (defeqArg_spec p hp n s₀ mode vis d a ta ty)
  subst hs0
  refine ⟨hloc, ?_⟩
  cases hc : callW p n "is_eager_reduce" [a] s.mem with
  | none => rw [hc] at hW; simp [defeqArgK] at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc] at hW
  have h₁ := CoreSpec.of_callW (he n s a₀ dn vis fe M eb a hs.rel ha) hc
  have hrun₁ := AM.run_of_ok _ _ h₁.1
  rw [h₁.2.2.1] at hrun₁
  have hT := defeqArg_run (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE ta) (decE ty)
    a₀ _ _ hrun₁
  by_cases h0 : r₁.headD 0 ≠ 0
  · rw [defeqArgK_e p n mode vis d ta ty r₁ m₁ h0] at hW
    have hb : decBool r₁ = true := by simp only [decBool, bne_iff_ne]; exact h0
    rw [hb] at hT
    exact coreRef_then h₁ (fun M' hS' => CoreSpec.of_call1W
      (s₀ := ⟨m₁, Locals.init []⟩)
      (hde F _ _ dn vis fe M' eb mode d ta ty hF hn ⟨hS', hs.mode4, hs.eb_mode⟩ hta hty)
      (fun r r' h => by simp only [decBool, h]) hW) hT
  · rw [defeqArgK_p p n mode vis d ta ty r₁ m₁ (by simpa using h0)] at hW
    have hb : decBool r₁ = false := by simp only [decBool, bne_eq_false_iff_eq]; simpa using h0
    rw [hb] at hT
    exact coreRef_then h₁ (fun M' hS' => CoreSpec.of_call1W
      (s₀ := ⟨m₁, Locals.init []⟩)
      (hd F _ _ dn vis fe M' eb mode d ta ty hF hn ⟨hS', hs.mode4, hs.eb_mode⟩ hta hty)
      (fun r r' h => by simp only [decBool, h]) hW) hT

end dar

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
  exact fainternW_hw m a hA.1.forallE t b _ m₁ hI₁

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
    (by simp [tier1, tierOff, FADER, FAREC, FASLOT])
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [tier1, tierOff, FADER, FAREC, FASLOT, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "abs_entry",
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
  have hrun₁ := AM.run_of_ok _ _ h₁.1
  rw [h₁.2.2.1] at hrun₁
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

/-- The pin read and `const_e` after a support test's run `res`. -/
def pinArmK (p : Prog) (n : Nat) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m₂) => call1W p n "const_e" [r.headD 0] m₂

/-- A support test's run `res`, then the pin `k` and its constant. -/
def litArmK (p : Prog) (n : Nat) (k : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m₁) => if r.headD 0 = 0 then none else pinArmK p n (callW p n "pin_at" [k] m₁)

/-- **The model of `infer_lit`.** -/
def inferLitK (p : Prog) (n : Nat) (m : Mem) (vis e : Word) : Option (Word × Mem) :=
  if tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m LIT (tierW e) ≤ idxW e then none
  else if tfld m LIT (tierW e) (idxW e) 0 = 0 then
    litArmK p n 1 (callW p n "nat_lit_supported" [vis] m)
  else litArmK p n 5 (callW p n "str_lit_supported" [vis] m)

section litK
variable (p : Prog) (n : Nat) (m m₁ : Mem) (vis e k : Word) (r : List Word)

theorem pinArmK_some : pinArmK p n (some (r, m₁)) = call1W p n "const_e" [r.headD 0] m₁ := rfl

theorem litArmK_ok (h : r.headD 0 ≠ 0) :
    litArmK p n k (some (r, m₁)) = pinArmK p n (callW p n "pin_at" [k] m₁) := by
  simp only [litArmK, h, ↓reduceIte]

theorem inferLitK_nat (h1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (h2 : idxW e < tcnt m LIT (tierW e))
    (h3 : tfld m LIT (tierW e) (idxW e) 0 = 0) :
    inferLitK p n m vis e = litArmK p n 1 (callW p n "nat_lit_supported" [vis] m) := by
  have h2' : ¬ tcnt m LIT (tierW e) ≤ idxW e := by simpa using h2
  simp only [inferLitK, h1, h2', h3, ↓reduceIte]

theorem inferLitK_str (h1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (h2 : idxW e < tcnt m LIT (tierW e))
    (h3 : tfld m LIT (tierW e) (idxW e) 0 ≠ 0) :
    inferLitK p n m vis e = litArmK p n 5 (callW p n "str_lit_supported" [vis] m) := by
  have h2' : ¬ tcnt m LIT (tierW e) ≤ idxW e := by simpa using h2
  simp only [inferLitK, h1, h2', h3, ↓reduceIte]

end litK

section il
variable (p : Prog) (hp : InferLeafProg p)

include hp in
theorem inferLit_spec (n : Nat) (s₀ : St) (vis e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_lit" [vis, e]
    ⦃fun r s' => LocEq s' s₀ ∧ inferLitK p n s₀.mem vis e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.inferLit]
  simp only [callFn, inferLitL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_lit_supported", callW_spec p n "str_lit_supported",
      callW_spec p n "pin_at", callW_spec p n "const_e", evalE_tld, tld, evalE_cnt, tcntM,
        evalE_tierE, evalE_idxE] <;>
    finish [inferLitK_nat, inferLitK_str, litArmK_ok, pinArmK_some, call1W_some, tierW, idxW, tfld]

end il

theorem view_lit_f (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h LIT) (hg : h >>> 28 = 8) :
    ∃ k : LitNode, a.store.view (decE h) = some (.lit k.l) ∧ RecRel m (tierW h) (idxW h) k := by
  obtain ⟨k, hk, hu⟩ := node_of m a h litCS RecRel (·.lits) _ hR.lit.2 hv.2
  exact ⟨k, by rw [view_tier m a hR h hh hv.1, get_lit _ h hh hg, Tbl.node?, hk]; rfl, hu⟩

theorem inferLitT_nat_run (fe : IFEnv) (N : Nat) (a a₁ : AState) (nn : NIdx)
    (h1 : (natLitSupported fe).run a = .ok (true, a₁)) (h2 : pinNat.run a₁ = .ok (nn, a₁)) :
    (inferLitT fe (.natVal N)).run a = (constE nn).run a₁ := by
  simp only [inferLitT, StateT.run_bind, h1, except_ok_bind, ↓reduceIte, h2]

theorem inferLitT_str_run (fe : IFEnv) (s : String) (a a₁ : AState) (sn : NIdx)
    (h1 : (strLitSupported fe).run a = .ok (true, a₁)) (h2 : pinString.run a₁ = .ok (sn, a₁)) :
    (inferLitT fe (.strVal s)).run a = (constE sn).run a₁ := by
  simp only [inferLitT, StateT.run_bind, h1, except_ok_bind, ↓reduceIte, h2]

/-- One `.lit` clause after its support test: the test's run, the pin, `const_e`. -/
theorem litArm_ref (p : Prog) (hp : InferLeafProg p) (hc : InferLitCallees p) (n : Nat) (k : Nat)
    (hk : k < 51) {T₁ : AM Bool} {T : AM EIdx} {s : St} {a₀ : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {r r₁ : List Word} {m₁ m' : Mem}
    (h₁ : CoreRef T₁ a₀ decBool dn s.mem vis fe M eb r₁ m₁)
    (_h0 : r₁.headD 0 ≠ 0)
    (hW : pinArmK p n (callW p n "pin_at" [k.toUInt64] m₁) = some (r.headD 0, m'))
    (hT : ∀ nn, (pinAt k).run (AM.st T₁ a₀) = .ok (nn, AM.st T₁ a₀) →
      T.run a₀ = (constE nn).run (AM.st T₁ a₀)) :
    CoreRef T a₀ decH dn s.mem vis fe M eb r m' := by
  cases hc2 : callW p n "pin_at" [k.toUInt64] m₁ with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2, pinArmK_some] at hW
  obtain ⟨M', hS', -, -⟩ := h₁.2.1
  obtain ⟨s₂, hs₂, hm₂, -, hlt, hpin⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (pinAt_refines p hp.pinAt n _ (AM.st T₁ a₀) ⟨fun _ => hS'.pins⟩ k.toUInt64) hc2
  have hm : m₂ = m₁ := hs₂.symm.trans hm₂
  subst hm
  have hkk : k.toUInt64.toNat = k := by simp; omega
  rw [hkk] at hpin
  exact coreRef_then h₁ (fun M'' hS'' => CoreSpec.of_call1W (s₀ := ⟨m₂, Locals.init []⟩)
    (hc.constE n _ _ dn vis fe M'' eb (r₂.headD 0) hS'' hlt) (fun r r' h => by simp only [decH, h])
    hW) (hT _ hpin)

/-- **`infer_lit(vis, e)` refines the `.lit` clauses** (`inferLitT`) at the literal the handle
views, from the support tests' and `const_e`'s specs (`InferLitCallees`). -/
@[refines_part ConRon.Arena.inferBody "lit (inferLitT)"]
theorem inferLit_refines (p : Prog) (hp : InferLeafProg p) (hc : InferLitCallees p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb e : Word) (l : ConLeche.Literal) (hS : CoreS dn s₀.mem a₀ vis fe M eb)
    (he : HW e) (hg : e >>> 28 = 8) (hv : a₀.store.view (decE e) = some (.lit l)) :
    CoreSpec p (n + 1) "infer_lit" [vis, e] (inferLitT fe l) decH s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (inferLit_spec p hp n s₀ vis e)
  subst hs0
  refine ⟨hloc, ?_⟩
  unfold inferLitK at hW
  obtain ⟨h1, hW⟩ := of_ite_none hW
  obtain ⟨h2, hW⟩ := of_ite_none hW
  obtain ⟨k, hk, hrel⟩ := view_lit_f s.mem a₀ hS.arena.1 e he ⟨h1, by simpa using h2⟩ hg
  rw [hv] at hk
  have hl : l = k.l := by simpa using hk
  subst hl
  obtain ⟨l⟩ := k
  by_cases h3 : tfld s.mem LIT (tierW e) (idxW e) 0 = 0
  · rw [ite_eq_left h3] at hW
    cases l with
    | strVal str => simp [RecRel, StrRec, h3] at hrel
    | natVal N =>
    cases hc1 : callW p n "nat_lit_supported" [vis] s.mem with
    | none => rw [hc1] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hc1] at hW
    by_cases h0 : r₁.headD 0 = 0
    · simp only [litArmK, h0, ↓reduceIte] at hW; cases hW
    rw [litArmK_ok (h := h0)] at hW
    have h₁ := CoreSpec.of_callW (hc.natLitSup n s a₀ dn vis fe M eb hS) hc1
    have hrun₁ := AM.run_of_ok _ _ h₁.1
    rw [h₁.2.2.1, show decBool r₁ = true by simp only [decBool, bne_iff_ne]; exact h0] at hrun₁
    exact litArm_ref p hp hc n 1 (by decide) h₁ h0 hW
      (fun nn hpin => inferLitT_nat_run fe N a₀ _ nn hrun₁ hpin)
  · rw [ite_eq_right h3] at hW
    cases l with
    | natVal N => simp [RecRel, NatRec, h3] at hrel
    | strVal str =>
    cases hc1 : callW p n "str_lit_supported" [vis] s.mem with
    | none => rw [hc1] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hc1] at hW
    by_cases h0 : r₁.headD 0 = 0
    · simp only [litArmK, h0, ↓reduceIte] at hW; cases hW
    rw [litArmK_ok (h := h0)] at hW
    have h₁ := CoreSpec.of_callW (hc.strLitSup n s a₀ dn vis fe M eb hS) hc1
    have hrun₁ := AM.run_of_ok _ _ h₁.1
    rw [h₁.2.2.1, show decBool r₁ = true by simp only [decBool, bne_iff_ne]; exact h0] at hrun₁
    exact litArm_ref p hp hc n 5 (by decide) h₁ h0 hW
      (fun nn hpin => inferLitT_str_run fe str a₀ _ nn hrun₁ hpin)

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

theorem infer_toNat_add_small (q : Word) (k : Nat) (hk : k < 8) (hq : q.toNat < 2 ^ 63) :
    (q + k.toUInt64).toNat = q.toNat + k := by
  rw [UInt64.toNat_add]; simp; omega

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
  have e1 : (q + 1).toNat = q.toNat + 1 := infer_toNat_add_small q 1 (by decide) hq
  have e2 : (q + 2).toNat = q.toNat + 2 := infer_toNat_add_small q 2 (by decide) hq
  have e3 : (q + 3).toNat = q.toNat + 3 := infer_toNat_add_small q 3 (by decide) hq
  have e4 : (q + 4).toNat = q.toNat + 4 := infer_toNat_add_small q 4 (by decide) hq
  have r1 : rdW b (q + 1) = w1 := by simp [rdW, e1, hw1]
  have r4 : rdW b (q + 4) = w4 := by
    simp only [rdW, e4]; rw [show q.toNat + 4 = q.toNat + 1 + 3 by omega, hw4]; rfl
  simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hl
  obtain ⟨o, ⟨wo, hwo, rfl⟩, c, ⟨wc, hwc, rfl⟩, hs⟩ := hl
  have r2 : rdW b (q + 2) = wo := by
    simp only [rdW, e2]; rw [show q.toNat + 2 = q.toNat + 1 + 1 by omega, hwo]; rfl
  have r3 : rdW b (q + 3) = wc := by
    simp only [rdW, e3]; rw [show q.toNat + 3 = q.toNat + 1 + 1 + 1 by omega, hwc]; rfl
  rw [r1, r2, r3, r4]
  exact ⟨hl1, rfl, hl4, rfl, hs⟩

theorem viewLs_run (h : LsIdx) (a : AState) (ids : List LIdx) (hv : a.store.lss.view h = some ids) :
    (viewLs h).run a = .ok (ids, a) := by
  simp [viewLs, hv, StateT.run_bind, StateT.run_get]; rfl

theorem inferConstT_run (fe : IFEnv) (n : NIdx) (us : LsIdx) (a : AState) (ci : IConstantInfo)
    (cv : IConstantVal) (ids : List LIdx) (hf : fe.find? n = some ci)
    (hcv : ci.toConstantVal = cv)
    (hv : (viewLs us).run a = .ok (ids, a)) (hlen : ids.length = cv.levelParams.length) :
    (inferConstT fe n us).run a = (constTyAt cv us).run a := by
  subst hcv
  simp only [inferConstT, hf, StateT.run_bind, except_ok_bind, hv, hlen, bne_self_eq_false]
  rfl

theorem coreRef_congr {α : Type} [Inhabited α] {T T' : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} (h : T.run a₀ = T'.run a₀)
    (h' : CoreRef T' a₀ dec dn m₀ vis fe M eb r m ok) : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  unfold CoreRef AM.ok AM.st AM.res at *; rw [h]; exact h'

/-- The model of `infer_const` past `env_find`'s run. -/
def constArmK (p : Prog) (n : Nat) (us : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m₁) =>
    if r.headD 0 = 0 then none
    else if lsNodeW m₁ us = [] then none
    else if (lsNodeW m₁ us).tail.headD 0 ≠ rdW (m₁.arr64 EREC) (r.tail.headD 0 + 3) then none
    else call1W p n "const_ty_at" [rdW (m₁.arr64 EREC) (r.tail.headD 0 + 1),
      rdW (m₁.arr64 EREC) (r.tail.headD 0 + 2), rdW (m₁.arr64 EREC) (r.tail.headD 0 + 3),
      rdW (m₁.arr64 EREC) (r.tail.headD 0 + 4), us] m₁

theorem constArmK_ok (p : Prog) (n : Nat) (us : Word) (r : List Word) (m₁ : Mem)
    (h0 : r.headD 0 ≠ 0)
    (hne : lsNodeW m₁ us ≠ [])
    (hl : (lsNodeW m₁ us).tail.headD 0 = rdW (m₁.arr64 EREC) (r.tail.headD 0 + 3)) :
    constArmK p n us (some (r, m₁)) = call1W p n "const_ty_at" [rdW (m₁.arr64 EREC) (r.tail.headD 0 + 1),
      rdW (m₁.arr64 EREC) (r.tail.headD 0 + 2), rdW (m₁.arr64 EREC) (r.tail.headD 0 + 3),
      rdW (m₁.arr64 EREC) (r.tail.headD 0 + 4), us] m₁ := by
  simp only [constArmK, h0, hne, hl, ne_eq, not_true_eq_false, ↓reduceIte]

section ic
variable (p : Prog) (hp : InferLeafProg p)

include hp in
theorem inferConst_spec (n : Nat) (s₀ : St) (vis nm us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_const" [vis, nm, us]
    ⦃fun r s' => LocEq s' s₀ ∧
      constArmK p n us (callW p n "env_find" [nm, vis] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.inferConst]
  simp only [callFn, inferConstL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "env_find",
      lsNode_spec p hp.lsNode n, callW_spec p n "const_ty_at", callW_spec p n "pin_at"] <;>
    finish [constArmK_ok, call1W_some]

end ic

/-- **`infer_const(vis, n, us)` refines the `.const` clause** (`inferConstT`), from `const_ty_at`'s
spec (`ConstTyAtOK`, lane `whnf`'s, a `sorry` there: a hypothesis here). -/
@[refines_part ConRon.Arena.inferBody "const (inferConstT)"]
theorem inferConst_refines (p : Prog) (hp : InferLeafProg p) (hct : ConstTyAtOK p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb nm us : Word) (hS : CoreS dn s₀.mem a₀ vis fe M eb) (hnm : HW nm)
    (hus : HW us) :
    CoreSpec p (n + 1) "infer_const" [vis, nm, us] (inferConstT fe (decI nm) (decI us)) decH s₀ a₀
      dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (inferConst_spec p hp n s₀ vis nm us)
  subst hs0
  refine ⟨hloc, ?_⟩
  cases hc : callW p n "env_find" [nm, vis] s.mem with
  | none => rw [hc] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc] at hW
  obtain ⟨t₁, ht₁, hm₁, -, hfind⟩ := triple_of_callW
    (envFind_refines p hp.envix hp.envrow hp.envfind n s vis nm hS.env hnm) hc
  obtain ⟨-, -, -, -, hfound⟩ := triple_of_callW
    (envFind_found p hp.envix hp.envrow hp.envfind n s vis nm hnm) hc
  rw [ht₁] at hm₁
  subst hm₁
  dsimp only [constArmK] at hW
  obtain ⟨h0, hW⟩ := of_ite_none hW
  obtain ⟨htag, hrow, hq⟩ := hfound h0
  obtain ⟨ci, hci⟩ := hS.env.found_some nm hnm htag hrow
  have hfind' : fe.find? (decI nm) = some ci := by
    rw [hfind]; simp only [decFound, h0, ↓reduceIte, hq]; exact hci
  rw [← hq] at hci
  have hcv := decCI_cvA hci (erecP_ext _)
  generalize hcvr : ci.toConstantVal = cv at hcv
  obtain ⟨hne, hW⟩ := of_ite_none hW
  obtain ⟨hl, hW⟩ := of_ite_none hW
  have hl' : (lsNodeW s.mem us).tail.headD 0 = rdW (s.mem.arr64 EREC) (r₁.tail.headD 0 + 3) := by
    simpa using hl
  obtain ⟨hw1, hname, hw4, hty, hsl⟩ := infer_decCV_words hcv hS.erec
  obtain ⟨ids, hv, hlen1, hlen2⟩ := lsNodeW_view hS.arena.1 hus hne
  have hlen : ids.length = cv.levelParams.length := by
    rw [hslice?_length hsl, ← hl', hlen1, hlen2]
  have hT := inferConstT_run fe (decI nm) (decI us) a₀ ci cv ids hfind' hcvr
    (viewLs_run _ _ _ hv) hlen
  have hcv' : cv = ⟨decI (rdW (s.mem.arr64 EREC) (r₁.tail.headD 0 + 1)), cv.levelParams,
      decE (rdW (s.mem.arr64 EREC) (r₁.tail.headD 0 + 4))⟩ := by
    rw [← hname, decE_eq, ← hty]
  rw [hcv'] at hT
  exact coreRef_congr hT (CoreSpec.of_call1W (s₀ := ⟨s.mem, Locals.init []⟩)
    (hct n _ a₀ dn vis fe M eb _ _ _ _ us cv.levelParams hS hw1 hw4 hus hsl)
    (fun r r' h => by simp only [decH, h]) hW)

end L.Arena
