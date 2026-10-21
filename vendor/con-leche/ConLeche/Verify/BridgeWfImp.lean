module

public import ConLeche.Verify.BridgeDecl
import ConLeche.Verify.Inductives.NestedRead
import ConLeche.Verify.Extend.Inversions

public section

/-!
# Scoping facts for the cache bridge

The cached tier's bridge (`ConLeche/Verify/Cached/BridgeCS1.lean`
through `BridgeCSDecl.lean`) carries the arguments' well-scopedness to
every operation call.  At each call site it comes from

* the checker's own input validation (`looseBVarsBounded`/`hasFvar`
  guards precede every inference of raw input — at depth 0
  fvar-freedom *is* well-scopedness),
* the scoping-preservation lemmas for the operations' outputs
  (`inferTypeCore_WScoped`), and
* scoping of the iota-theorem check's opened telescopes
  (`openPisAtFvars_WScoped`, `instPisAt_WScoped`, `instLamsAt_WScoped`
  — the defeq comparisons run at the opened depth, over variables of
  that frame).

This module holds the pieces of that which are not lemmas about the
operations themselves.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

open Expr

/-! ## Small syntactic toolkit -/

theorem wscopedB_of_not_hasFvar {e : Expr} (h : e.hasFvar = false)
    {d : Nat} : e.wscopedB d = true :=
  (WScoped.of_not_hasFvar h).to_wscopedB

/-! ## Opened telescopes -/

/-- `openPisAtFvars` puts the variable it creates for binder `j` at
index `i + j` — the positional companion of `openPisAtFvars_WScoped`,
needed wherever a check runs at each binder's *own* frame. -/
theorem openPisAtFvars_index :
    ∀ (n : Nat) (e : Expr) (i : Nat) {fvs : List Expr} {body : Expr},
      openPisAtFvars n e i = some (fvs, body) →
      ∀ (j : Nat) (x : Expr), fvs[j]? = some x →
        ∃ ty, x = Expr.fvar (i + j) ty := by
  intro n
  induction n with
  | zero =>
    intro e i fvs body h j x hx
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at hx
    exact nomatch hx
  | succ n ih =>
    intro e i fvs body h j x hx
    cases e with
    | forallE dom bodyE =>
      simp only [openPisAtFvars] at h
      revert h
      cases hrec : openPisAtFvars n
          (bodyE.instantiate1 (.fvar i dom)) (i + 1) with
      | none => intro h; exact nomatch h
      | some p =>
        obtain ⟨fvs', bodyR⟩ := p
        intro h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          exact ⟨dom, by rw [← hx, Nat.add_zero]⟩
        | succ j =>
          simp only [List.getElem?_cons_succ] at hx
          obtain ⟨ty', hx'⟩ := ih _ (i + 1) hrec j x hx
          exact ⟨ty', by rw [hx']; congr 1; omega⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | lam _ _ | letE _ _ _ | lit _ | proj _ _ _ =>
      exact nomatch h

/-- Opening a `∀`-telescope at fresh free variables produces variables
and a body scoped at the extended frame. -/
theorem openPisAtFvars_WScoped :
    ∀ (n : Nat) (e : Expr) (i : Nat) {fvs : List Expr} {body : Expr},
      openPisAtFvars n e i = some (fvs, body) → WScoped i e →
      (∀ x ∈ fvs, WScoped (i + n) x) ∧ WScoped (i + n) body := by
  intro n
  induction n with
  | zero =>
    intro e i fvs body h hw
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), hw⟩
  | succ n ih =>
    intro e i fvs body h hw
    cases e with
    | forallE dom bodyE =>
      simp only [openPisAtFvars] at h
      revert h
      cases hrec : openPisAtFvars n
          (bodyE.instantiate1 (.fvar i dom)) (i + 1) with
      | none => intro h; exact nomatch h
      | some p =>
        obtain ⟨fvs', bodyR⟩ := p
        intro h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [WScoped] at hw
        obtain ⟨hdom, hbody⟩ := hw
        have hinst : WScoped (i + 1)
            (bodyE.instantiate1 (.fvar i dom)) :=
          WScoped.instantiate1 hdom 0 hbody
        obtain ⟨hfvs', hbody'⟩ := ih _ _ hrec hinst
        have harith : i + 1 + n = i + (n + 1) := by omega
        rw [harith] at hfvs' hbody'
        refine ⟨?_, hbody'⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp only [WScoped]
          exact ⟨by omega, hdom⟩
        · exact hfvs' x hx
    | bvar k => exact nomatch h
    | fvar a c => exact nomatch h
    | sort u => exact nomatch h
    | const c us => exact nomatch h
    | app f a => exact nomatch h
    | lam b c => exact nomatch h
    | letE b c d => exact nomatch h
    | lit l => exact nomatch h
    | proj s k e => exact nomatch h

/-! ## Scoping of the structural-Nat certification equations -/

/-- The recurrence equations' sides are well-scoped at depth 2 (their
free variables are `fvar 0`/`fvar 1` with closed annotations). -/
theorem natOpEquations_wscopedB {c : Name} (hc : c ∈ natOpNames) :
    ∀ eq ∈ natOpEquations 0 c,
      eq.1.wscopedB 2 = true ∧ eq.2.wscopedB 2 = true := by
  simp only [natOpNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (intro eq heq
     simp +decide [natOpEquations] at heq
     first
       | (rcases heq with rfl | rfl | rfl | rfl) <;>
           simp +decide [Expr.wscopedB]
       | (rcases heq with rfl | rfl | rfl) <;>
           simp +decide [Expr.wscopedB]
       | (rcases heq with rfl | rfl) <;>
           simp +decide [Expr.wscopedB])

/-- Substituting a closed value for a constant preserves scoping. -/
theorem wscopedB_substConst0 {n : Name} {r : Expr}
    (hr : r.hasFvar = false) :
    ∀ (e : Expr) {d : Nat}, e.wscopedB d = true →
      (Expr.substConst0 n r e).wscopedB d = true
  | .const c us, d, he => by
    simp only [Expr.substConst0]
    split
    · exact wscopedB_of_not_hasFvar hr
    · exact he
  | .app f a, d, he => by
    simp only [Expr.substConst0, Expr.wscopedB, Bool.and_eq_true] at he ⊢
    exact ⟨wscopedB_substConst0 hr f he.1, wscopedB_substConst0 hr a he.2⟩
  | .bvar _, _, he | .fvar _ _, _, he | .sort _, _, he | .lit _, _, he
  | .lam _ _, _, he | .forallE _ _, _, he
  | .letE _ _ _, _, he | .proj _ _ _, _, he => he

/-! ## The div/mod pin gate -/

/-- The pinned open certificate statements are well-scoped at the
certificate frame: hypotheses at their own binder index (they ride as
the `fvar 2`/`fvar 3` annotations), the equation at the full frame. -/
theorem divModCertStmts_wscopedB {c : Name} (hc : c ∈ natDivModNames) :
    ∀ st ∈ divModCertStmts c,
      (∀ hyp ∈ st.1, hyp.wscopedB 2 = true) ∧ st.2.wscopedB 4 = true := by
  simp only [natDivModNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

/-- The applied certificate proof is well-scoped at the frame. -/
theorem divModCertApplied_wscopedB {proofS : Expr} {hyps : List Expr}
    (hp : proofS.hasFvar = false)
    (hh : ∀ hyp ∈ hyps, hyp.wscopedB 2 = true) :
    (divModCertApplied proofS hyps).wscopedB 4 = true := by
  have hpw : proofS.wscopedB 4 = true := wscopedB_of_not_hasFvar hp
  unfold divModCertApplied
  match hyps, hh with
  | [], hh => simp [Expr.wscopedB, hpw]
  | [h1], hh =>
    have h1w := hh h1 (by simp)
    simp [Expr.wscopedB, hpw, h1w]
  | [h1, h2], hh =>
    have h1w := hh h1 (by simp)
    have h2w3 : h2.wscopedB 3 = true :=
      (WScoped.mono (by omega) (WScoped.of_wscopedB
        (hh h2 (by simp)))).to_wscopedB
    simp [Expr.wscopedB, hpw, h1w, h2w3]
  | _ :: _ :: _ :: _, hh => simp [Expr.wscopedB, hpw]

/-! ## A checked constant's type slot -/

/-- Close a goal whose hypothesis is a pure run that begins with a
`throw`: such a run never succeeds. -/
macro "throwM_elim" h:ident : tactic =>
  `(tactic| simp only [throw, throwThe, MonadExceptOf.throw, Bind.bind,
      Except.bind, reduceCtorEq] at $h:ident)

/-- The type-slot `ConstWF` facts of a successfully checked constant:
level parameters, constant resolution, closedness and fvar-freedom are
all checked outright (the stored type is the declared one). -/
theorem checkConstantVal_typeWF {env : Env} {cv : ConstantVal}
    {F : Nat} (h : checkConstantVal (fueledOps mode F) env cv = .ok ()) :
    cv.type.hasFvar = false ∧
    cv.type.allLevelParamsDefined cv.levelParams = true ∧
    cv.type.constsResolve env = true ∧
    cv.type.looseBVarsBounded 0 = true := by
  obtain ⟨-, -, -, -, hlb, hif, -, -, htp, htr, -, -⟩ := checkConstantVal_inv h
  exact ⟨hif, htp, htr, hlb⟩

end ConLeche
