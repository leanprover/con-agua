import ConAgua.Arena.DeclReduceSpec
import ConAgua.Arena.DeclCanonEq

/-!
# `matchesPin`, `reduceStoredOk`, `reduceElemOk` (lane `decls3`)

The comparisons with the pins: `matches_pin` is `cv_eq` (helper `decls3-canon`'s word-level
comparison, `cvEqB_ok`), and the two environment shapes of the reduce operations read the
environment (`env_find`: `envFindW_miss`/`envFindW_hit`) and compare with a ROM value. Through the
ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Ind

theorem matchesPin_eq (cv pin : IConstantVal) : cv.matchesPin pin = pure (decide (cv = pin)) := by
  cases cv; cases pin
  simp only [IConstantVal.matchesPin, IConstantVal.mk.injEq]
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]

/-! ## `matches_pin(q, pin)` -/

/-- **The model of `matches_pin`**: `cv_eq`'s word-level comparison; the memory unchanged. -/
def mpW (m : Mem) (q pin : Word) : Option (List Word × Mem) :=
  some ([if cvEqB (m.arr64 EREC) q pin then 1 else 0], m)

theorem mp_specW (p : Prog) (hC : CanonProg p) (hp : p.lookup "matches_pin" = some matchesPinL)
    (n : Nat) (s₀ : St) (q pin : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "matches_pin" [q, pin]
    ⦃fun r s' => LocEq s' s₀ ∧ mpW s₀.mem q pin = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, matchesPinL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, cvEq_spec' p hC n] <;>
      finish [mpW]

theorem mpW_ok {m m' : Mem} {a : AState} {q pin : Word} {r : List Word} {cv cv' : IConstantVal}
    (h : mpW m q pin = some (r, m')) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (h1 : decCV (erA m) q.toNat = some cv) (h2 : decCV (erA m) pin.toNat = some cv') :
    m' = m ∧ (cv.matchesPin cv').run a = .ok (decide (cv = cv'), a) ∧
      decW0B m' r (decide (cv = cv')) := by
  simp only [mpW, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [cvEqB_ok hsz h1 h2, matchesPin_eq]
  refine ⟨rfl, rfl, ?_⟩
  by_cases e : cv = cv' <;> simp [e, decW0B]

/-- **`matches_pin(q, pin)` refines `IConstantVal.matchesPin`** (sorry-free). -/
@[refines ConRon.Arena.IConstantVal.matchesPin]
theorem matchesPin_refines (p : Prog) (hC : CanonProg p)
    (hp : p.lookup "matches_pin" = some matchesPinL) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (q pin : Word) (cv cv' : IConstantVal) :
    RefAM p "matches_pin" [q, pin]
      (fun m a => StageR dn vis fe m a ∧ decCV (erA m) q.toNat = some cv ∧
        decCV (erA m) pin.toNat = some cv')
      (cv.matchesPin cv') (KeepPost dn vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, h1, h2⟩
  refine triple_post (mp_specW p hC hp n s₀ q pin) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hmem, hrun, hd⟩ := mpW_ok (a := a₀) hm hS.2.2.2.2.1 h1 h2
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres, hmem]
  exact ⟨hS, IWGrow.refl _, by rw [← hmem]; exact hd⟩

end L.Arena
