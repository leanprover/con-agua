import ConAgua.Verdict.WhnfModels7E
import ConAgua.Verdict.WhnfPirrE
import ConAgua.Arena.DefEqStuck
import ConAgua.Arena.DefEqStuckEta

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

/-! ## `eta_cert`, `eta_cert_body`, `eta_cert_ty` -/

theorem whnfEtaE_nv : ∀ f ∈ ["inst1", "intern_fvar", "mk_app", "io_neutral"], f ∈ L.Checker.nvFns := by
  decide +kernel

section etaErr
variable (r : CoreFnsA) (depth : Nat)

theorem etaTy_err_infer (lhs cod₂ fv : EIdx) (a : AState) (ce : CheckError)
    (h : (r.infer (depth + 1) lhs).run a = .error ce) : (etaTyT r depth lhs cod₂ fv).run a = .error ce := by
  simp only [etaTyT, StateT.run_bind, h]; rfl

theorem etaTy_err_defeq (lhs cod₂ fv t₁ t₂ : EIdx) (a a₁ a₂ : AState)
    (h1 : (r.infer (depth + 1) lhs).run a = .ok (t₁, a₁))
    (h2 : (instantiate1Fast coreWalkFuel cod₂ fv 0).run a₁ = .ok (t₂, a₂)) (ce : CheckError)
    (h3 : (r.defeq (depth + 1) t₁ t₂).run a₂ = .error ce) :
    (etaTyT r depth lhs cod₂ fv).run a = .error ce := by
  simp only [etaTyT, StateT.run_bind, h1, except_ok_bind, h2, h3]

theorem etaBody_err_defeq (mode : ConLeche.CheckMode) (ty₁ body₁ b cod₂ fv lhs rhs : EIdx)
    (a a₁ a₂ a₃ : AState) (h1 : (internE (.fvar depth ty₁)).run a = .ok (fv, a₁))
    (h2 : (instantiate1Fast coreWalkFuel body₁ fv 0).run a₁ = .ok (lhs, a₂))
    (h3 : (internE (.app b fv)).run a₂ = .ok (rhs, a₃)) (ce : CheckError)
    (h4 : (r.defeq (depth + 1) lhs rhs).run a₃ = .error ce) :
    (etaBodyT mode r depth ty₁ body₁ b cod₂).run a = .error ce := by
  simp only [etaBodyT, StateT.run_bind, h1, except_ok_bind, h2, h3, h4]; rfl

theorem etaBody_err_ty (mode : ConLeche.CheckMode) (ty₁ body₁ b cod₂ fv lhs rhs : EIdx)
    (a a₁ a₂ a₃ a₄ : AState) (hv : mode.verifiedChecks = true)
    (h1 : (internE (.fvar depth ty₁)).run a = .ok (fv, a₁))
    (h2 : (instantiate1Fast coreWalkFuel body₁ fv 0).run a₁ = .ok (lhs, a₂))
    (h3 : (internE (.app b fv)).run a₂ = .ok (rhs, a₃))
    (h4 : (r.defeq (depth + 1) lhs rhs).run a₃ = .ok (true, a₄)) (ce : CheckError)
    (h5 : (etaTyT r depth lhs cod₂ fv).run a₄ = .error ce) :
    (etaBodyT mode r depth ty₁ body₁ b cod₂).run a = .error ce := by
  simp only [etaBodyT, StateT.run_bind, h1, except_ok_bind, h2, h3, h4, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, hv, h5]

end etaErr

section eta
variable (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (hnv : closedNV p L.Checker.nvFns = true)
include hq hc hnv

/-- **`eta_cert_ty`'s verdicts** are the `infer` and `defeq` slots'. -/
theorem etaCertTy_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d lhs cod2 fv : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hd : ¬ d + 1 = 0) (hl : HW lhs)
    (hcod : HW cod2) (hfv : HW fv) :
    CoreSpecE p (n + 1) "eta_cert_ty" [mode, vis, d, lhs, cod2, fv]
      (etaTyT (coreKnot (decMode mode) fe id F) d.toNat (decE lhs) (decE cod2) (decE fv)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (ectE_spec p hq.etaCertTy (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d lhs cod2 fv) hc0 (Err.code_ne_of_cls hk0)
  simp only [ectE] at hW
  have hd1 := toNat_succ_of_ne hd
  cases c1 : callE p n "infer" [mode, vis, d + 1, lhs] s₀.mem with
  | error e1 =>
    rw [c1, ectE.k_infer.none] at hW; cases hW
    have h := CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).infer F s₀ a₀ dn vis fe M eb mode (d + 1) lhs
      hF hn hs hl) c1
    rw [hd1] at h
    exact ErrClaim.of_run_err (fun ce h' => etaTy_err_infer (cod₂ := _) (fv := _) (a := a₀) (ce := ce) (h := h')) h
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [c1] at hW
  simp only [ectE.k_infer] at hW
  have h₁ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).infer F s₀ a₀ dn vis fe M eb mode (d + 1) lhs
    hF hn hs hl) (callW_of_callE c1)
  rw [hd1] at h₁
  obtain ⟨hok1, ⟨M₁, hS₁, -, -⟩, hres1, hr1⟩ := h₁
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  cases c2 : callE p n "inst1" [cod2, fv, 0] m₁ with
  | error e2 =>
    rw [c2, ectE.k_inst1.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfEtaE_nv "inst1" (by simp)) c2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [c2] at hW
  simp only [ectE.k_inst1] at hW
  obtain ⟨hok2, ⟨M₂, hS₂, -, -⟩, hres2, hr2⟩ := CoreSpec.of_callW
    (hc.inst1 n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb cod2 fv 0 hS₁ hcod hfv) (callW_of_callE c2)
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun2
  have hW' := err_of_k (by intro q e; simp [ectE.k_defeq]) (fun _ => rfl) hW
  have h := CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).defeq F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb
    mode (d + 1) (r₁.headD 0) (r₂.headD 0) hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ hr1 hr2) hW'
  rw [hd1] at h
  exact ErrClaim.of_run_err (fun ce h' => etaTy_err_defeq (a := a₀) (h1 := hrun1) (h2 := hrun2) (ce := ce) (h3 := h')) h

/-- **`eta_cert_body`'s verdicts** are the `defeq` slot's and `eta_cert_ty`'s. -/
theorem etaCertBody_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d ty1 body1 b cod2 : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty1) (hbody : HW body1)
    (_hb : HW b) (hcod : HW cod2) :
    CoreSpecE p (n + 1) "eta_cert_body" [mode, vis, d, ty1, body1, b, cod2]
      (etaBodyT (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE ty1) (decE body1)
        (decE b) (decE cod2)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (ecbE_spec p hq.etaCertBody (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d ty1 body1 b cod2) hc0 (Err.code_ne_of_cls hk0)
  simp only [ecbE] at hW
  by_cases hd : d + 1 = 0
  · rw [if_pos hd] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg hd] at hW
  have hd1 := toNat_succ_of_ne hd
  cases c1 : callE p n "intern_fvar" [d, ty1] s₀.mem with
  | error e1 =>
    rw [c1, ecbE.k_intern_fvar.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfEtaE_nv "intern_fvar" (by simp)) c1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [c1] at hW
  simp only [ecbE.k_intern_fvar] at hW
  obtain ⟨s₁, hs₁, -, hfv⟩ := triple_of_callE
    (internFVar_spec p hq.body.fvf hq.body.fvp hq.body.fvi n ⟨s₀.mem, Locals.init []⟩ d ty1) c1
  rw [hs₁] at hfv
  obtain ⟨hok1, ⟨M₁, hS₁, -, -⟩, hres1, hr1⟩ := internFVar_core hs.rel d ty1 hty r₁ hfv
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  cases c2 : callE p n "inst1" [body1, r₁.headD 0, 0] m₁ with
  | error e2 =>
    rw [c2, ecbE.k_inst1.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfEtaE_nv "inst1" (by simp)) c2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [c2] at hW
  simp only [ecbE.k_inst1] at hW
  obtain ⟨hok2, ⟨M₂, hS₂, -, -⟩, hres2, hr2⟩ := CoreSpec.of_callW
    (hc.inst1 n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb body1 (r₁.headD 0) 0 hS₁ hbody hr1)
    (callW_of_callE c2)
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun2
  cases c3 : callE p n "mk_app" [b, r₁.headD 0] m₂ with
  | error e3 =>
    rw [c3, ecbE.k_mk_app.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfEtaE_nv "mk_app" (by simp)) c3
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [c3] at hW
  simp only [ecbE.k_mk_app] at hW
  obtain ⟨hok3, ⟨M₃, hS₃, -, -⟩, hres3, hr3⟩ := mkApp_core hq.leaf.core.spine hS₂ b (r₁.headD 0) r₃
    (callW_of_callE c3)
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  cases c4 : callE p n "defeq" [mode, vis, d + 1, r₂.headD 0, r₃.headD 0] m₃ with
  | error e4 =>
    rw [c4, ecbE.k_defeq.none] at hW; cases hW
    have h := CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).defeq F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb
      mode (d + 1) (r₂.headD 0) (r₃.headD 0) hF hn ⟨hS₃, hs.mode4, hs.eb_mode⟩ hr2 hr3) c4
    rw [hd1] at h
    exact ErrClaim.of_run_err (fun ce h' => etaBody_err_defeq (mode := _) (cod₂ := _) (a := a₀) (h1 := hrun1) (h2 := hrun2)
      (h3 := hrun3) (ce := ce) (h4 := h')) h
  | ok q =>
  obtain ⟨r₄, m₄⟩ := q
  rw [c4] at hW
  simp only [ecbE.k_defeq] at hW
  have h₄ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).defeq F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb
    mode (d + 1) (r₂.headD 0) (r₃.headD 0) hF hn ⟨hS₃, hs.mode4, hs.eb_mode⟩ hr2 hr3)
    (callW_of_callE c4)
  rw [hd1] at h₄
  obtain ⟨hok4, ⟨M₄, hS₄, -, -⟩, hres4, -⟩ := h₄
  have hrun4 := AM.run_of_ok _ _ hok4
  rw [hres4] at hrun4
  by_cases h0 : r₄.headD 0 = 0
  · rw [if_pos h0] at hW; cases hW
  rw [if_neg h0] at hW
  rw [decBool_true_of h0] at hrun4
  by_cases hm : mode &&& 1 = 0
  · rw [if_pos hm] at hW
    have hv : (decMode mode).verifiedChecks = true := by rw [decMode_vc mode hs.mode4]; simpa using hm
    have hW' := err_of_k (by intro q e; simp [ecbE.k_eta_cert_ty]) (fun _ => rfl) hW
    cases n with
    | zero => exact ErrClaim.of_callE_zero hW'
    | succ N =>
    exact ErrClaim.of_run_err (fun ce h' => etaBody_err_ty (a := a₀) (hv := hv) (h1 := hrun1) (h2 := hrun2)
        (h3 := hrun3) (h4 := hrun4) (ce := ce) (h5 := h'))
      (CoreSpecE.of_callE (etaCertTy_refinesE p hq hc hnv N (hk.mono (Nat.le_succ N))
        (hkE.mono (Nat.le_succ N)) F ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode d (r₂.headD 0) cod2 (r₁.headD 0) (by omega)
        (by omega) ⟨hS₄, hs.mode4, hs.eb_mode⟩ hd hr2 hcod hr1) hW')
  · rw [if_neg hm] at hW; cases hW

end eta

end L.Arena
