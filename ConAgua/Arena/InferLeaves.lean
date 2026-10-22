import ConAgua.Arena.KnotSlot
import ConAgua.Arena.IndView
import ConAgua.Arena.IndMaster
import ConAgua.Arena.WhnfCoreApp

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

/-! ## `ensure_sort` -/

/-- The model of `ensure_sort` past `whnf`'s run `res`: the sort record's word. -/
def ensureSortK (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m₁) =>
    if r.headD 0 >>> 28 ≠ 2 then none
    else if tierW (r.headD 0) ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0 then none
    else if rdW (m₁.arr64 CTL) (16 + tierW (r.headD 0)) ≤ idxW (r.headD 0) then none
    else some (rdW (m₁.arr64 SOREC) (idxW (r.headD 0) * 2 + tierW (r.headD 0)), m₁)

theorem ensureSortK_ok (m₁ : Mem) (r : List Word) (h1 : r.headD 0 >>> 28 = 2)
    (h2 : ¬ (tierW (r.headD 0) ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0))
    (h3 : idxW (r.headD 0) < rdW (m₁.arr64 CTL) (16 + tierW (r.headD 0))) :
    ensureSortK (some (r, m₁)) =
      some (rdW (m₁.arr64 SOREC) (idxW (r.headD 0) * 2 + tierW (r.headD 0)), m₁) := by
  have h3' : ¬ rdW (m₁.arr64 CTL) (16 + tierW (r.headD 0)) ≤ idxW (r.headD 0) := by
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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "whnf"] <;>
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
  by_cases h1 : r₁.headD 0 >>> 28 ≠ 2
  · rw [if_pos h1] at hW; cases hW
  rw [if_neg h1] at hW
  by_cases h2 : tierW (r₁.headD 0) ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0
  · rw [if_pos h2] at hW; cases hW
  rw [if_neg h2] at hW
  by_cases h3 : rdW (m₁.arr64 CTL) (16 + tierW (r₁.headD 0)) ≤ idxW (r₁.headD 0)
  · rw [if_pos h3] at hW; cases hW
  rw [if_neg h3] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
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
  rw [fainternW_eq] at hI
  exact internM_hw forallSch FaRecRel fahash forallSch_wf m _ _ _ hR (faMt m t b) _ _ _ _
    (probe_homeG forallSch m 0 _ _ (faprobeW_arm m t b 0) _)
    (probe_homeG forallSch m 1 _ _ (faprobeW_arm m t b 1) _) _ (fapushOK_room m) _ _ w m' hI

theorem mkForallW_hw (m : Mem) (a : AState) (hA : ArenaD m a) (t b r : Word) (m' : Mem)
    (hI : mkForallW m t b = some (r, m')) : r.toNat < 2 ^ 32 := by
  unfold mkForallW at hI
  split at hI
  · cases hI
  cases hI₁ : fainternW m t b with
  | none => simp [hI₁, mkK] at hI
  | some p =>
  obtain ⟨r₁, m₁⟩ := p
  simp only [hI₁, mkK_some] at hI
  split at hI
  · cases hI
  simp only [Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  exact fainternW_hw m a hA.1.forallE t b _ m₁ hI₁

theorem mkForallW_frame {m m' : Mem} {t b r : Word} (hI : mkForallW m t b = some (r, m')) :
    MemFrame [FADER, FAREC, FASLOT] [30, 31] m m' := by
  unfold mkForallW at hI; split at hI; · cases hI
  exact L.Ind.mkK_frame (by decide) (fun r₁ m₁ hx => by
    rw [fainternW_eq] at hx; exact internM_frame _ forallSch_wf _ _ _ _ _ _ _ _ hx) hI

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
      rcases hb with rfl | rfl | rfl <;> decide)
    (by simp [FADER, FAREC, FASLOT, PINS])
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [FADER, FAREC, FASLOT, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _,
      ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩⟩,
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
      lamResK p n ty (callW p n "abstract1" [bt, d, 0] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.lamResult]
  simp only [callFn, inferLamResultL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "abstract1",
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
  cases hc : callW p n "abstract1" [bt, d, 0] s.mem with
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

end L.Arena
