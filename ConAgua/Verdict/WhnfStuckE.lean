import ConAgua.Verdict.WhnfModels7E
import ConAgua.Verdict.WhnfPirrE
import ConAgua.Arena.DefEqStuck

/-!
# The `whnf` family's stuck-side helpers: `prop_irrel` (lane `verdicts-b`, helper `k2`)

`prop_irrel` has no verdict site of its own: its claims are `proof_irrel`'s (`proofIrrelE_of`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace L.Arena

theorem whnfStuckE_nv : ∀ f ∈ ["not_proof_fast", "is_proof_fast"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-- Error model of `prop_irrel`, by hand (the ok model `piK1`). -/
def piHE (p : Prog) (n : Nat) (m : Mem) (mode vis d a b : Word) : Except Err (List Word × Mem) :=
  match callE p n "not_proof_fast" [vis, a] m with
  | .error e => .error e
  | .ok (r₁, m₁) =>
  match callE p n "not_proof_fast" [vis, b] m₁ with
  | .error e => .error e
  | .ok (r₂, m₂) =>
  if r₁.headD 0 ≠ 0 ∨ r₂.headD 0 ≠ 0 then .ok ([0], m₂) else
  match callE p n "is_proof_fast" [vis, a] m₂ with
  | .error e => .error e
  | .ok (r₃, m₃) =>
  match callE p n "is_proof_fast" [vis, b] m₃ with
  | .error e => .error e
  | .ok (r₄, m₄) =>
  if r₃.headD 0 ≠ 0 ∧ r₄.headD 0 ≠ 0 then .ok ([1], m₄) else
  match callE p n "proof_irrel" [mode, vis, d, a, b] m₄ with
  | .error e => .error e
  | .ok (r₅, m₅) => .ok ([r₅.headD 0], m₅)

set_option experimental.vcgen true in
set_option maxRecDepth 8000 in
theorem piHE_spec (p : Prog) (hp : p.lookup "prop_irrel" = some propIrrelL) (n : Nat) (s₀ : St)
    (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "prop_irrel" [mode, vis, d, a, b]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 → piHE p n s₀.mem mode vis d a b = .error ε⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, propIrrelL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callE_spec p n "not_proof_fast",
    callE_spec p n "is_proof_fast", callE_spec p n "proof_irrel"] <;>
  simp_all [piHE, Cmp.eval, Cmp.evalW, BinOp.eval, LocEq, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ,
    Sig.retVal, Sig.retOr]

section pi
variable (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (hnv : closedNV p L.Checker.nvFns = true)
  (hPI : ProofIrrelE p)
include hq hc hnv hPI

/-- **`prop_irrel`'s verdicts** are `proof_irrel`'s. -/
theorem propIrrel_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpecE p (n + 1) "prop_irrel" [mode, vis, d, a, b]
      (propIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (piHE_spec p hq.propIrrel n ⟨s₀.mem, Locals.init []⟩ mode vis d a b) hc0
    (Err.code_ne_of_cls hk0)
  simp only [piHE] at hW
  rw [propIrrel_eq]
  cases c1 : callE p n "not_proof_fast" [vis, a] s₀.mem with
  | error e1 =>
    rw [c1] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfStuckE_nv "not_proof_fast" (by simp)) c1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [c1] at hW
  simp only at hW
  obtain ⟨hok1, ⟨M₁, hS₁, -, -⟩, hres1, -⟩ :=
    CoreSpec.of_callW (hc.defeq.notProofFast n s₀ a₀ dn vis fe M eb a hs.rel ha) (callW_of_callE c1)
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  cases c2 : callE p n "not_proof_fast" [vis, b] m₁ with
  | error e2 =>
    rw [c2] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfStuckE_nv "not_proof_fast" (by simp)) c2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [c2] at hW
  simp only at hW
  obtain ⟨hok2, ⟨M₂, hS₂, -, -⟩, hres2, -⟩ := CoreSpec.of_callW
    (hc.defeq.notProofFast n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb b hS₁ hb) (callW_of_callE c2)
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun2
  by_cases h12 : r₁.headD 0 ≠ 0 ∨ r₂.headD 0 ≠ 0
  · rw [if_pos h12] at hW; cases hW
  rw [if_neg h12] at hW
  simp only [not_or, ne_eq, Decidable.not_not] at h12
  have hx : (decBool r₁ || decBool r₂) = false := by
    simp [decBool_eq_false h12.1, decBool_eq_false h12.2]
  cases c3 : callE p n "is_proof_fast" [vis, a] m₂ with
  | error e3 =>
    rw [c3] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfStuckE_nv "is_proof_fast" (by simp)) c3
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [c3] at hW
  simp only at hW
  obtain ⟨hok3, ⟨M₃, hS₃, -, -⟩, hres3, -⟩ := CoreSpec.of_callW
    (hc.defeq.isProofFast n ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb a hS₂ ha) (callW_of_callE c3)
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  cases c4 : callE p n "is_proof_fast" [vis, b] m₃ with
  | error e4 =>
    rw [c4] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfStuckE_nv "is_proof_fast" (by simp)) c4
  | ok q =>
  obtain ⟨r₄, m₄⟩ := q
  rw [c4] at hW
  simp only at hW
  obtain ⟨hok4, ⟨M₄, hS₄, -, -⟩, hres4, -⟩ := CoreSpec.of_callW
    (hc.defeq.isProofFast n ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb b hS₃ hb) (callW_of_callE c4)
  have hrun4 := AM.run_of_ok _ _ hok4
  rw [hres4] at hrun4
  by_cases h34 : r₃.headD 0 ≠ 0 ∧ r₄.headD 0 ≠ 0
  · rw [if_pos h34] at hW; cases hW
  rw [if_neg h34] at hW
  have hy : (decBool r₃ && decBool r₄) = false := by
    by_cases h3 : r₃.headD 0 = 0
    · simp [decBool_eq_false h3]
    · have h4 : r₄.headD 0 = 0 := Classical.byContradiction fun h4 => h34 ⟨h3, h4⟩
      simp [decBool_eq_false h4]
  have hW' := err_of_k (k := fun (x : Except Err (List Word × Mem)) => match x with
      | .error e => (.error e : Except Err (List Word × Mem))
      | .ok (r₅, m₅) => .ok ([r₅.headD 0], m₅)) (by intro q e; simp) (fun _ => rfl) hW
  cases n with
  | zero => exact ErrClaim.of_callE_zero hW'
  | succ N =>
  refine ErrClaim.of_run_err (fun ce h' => ?_) (CoreSpecE.of_callE (hPI N (hk.mono (Nat.le_succ N))
    (hkE.mono (Nat.le_succ N)) F (by omega) (by omega) ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode d a b hS₄
    hs.mode4 hs.eb_mode ha hb) hW')
  simp only [StateT.run_bind, hrun1, except_ok_bind, hrun2, hx, Bool.false_eq_true, ↓reduceIte, hrun3,
    hrun4, hy]
  exact h'

end pi

end L.Arena
