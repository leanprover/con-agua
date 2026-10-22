import ConAgua.Arena.KnotSlot
import ConAgua.Arena.IndView

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

end L.Arena
