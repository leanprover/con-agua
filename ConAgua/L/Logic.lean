module

public import ConAgua.L.Semantics
public import ConAgua.L.GrindAttr
public import Std.WP
public import Std.Tactic.Do

@[expose] public section

/-!
# L: proof support

The program logic is `Std.WP` on `M = StateT St (Except Err)`; `vcgen` steps through `step`,
`evalE`, `evalC`, … on concrete syntax. This file has

* the `lang_grind` vocabulary: one equation per helper function and constructor, so that a
  verification condition about `BinOp.eval .add x y` or `(s.setLoc 0 v).loc 1` is plain
  arithmetic for `grind`;
* `step_while`, which unfolds one iteration of a loop that is named by a constant (a loop spec is
  stated about the constant, so that the recursive call `k w` matches the induction hypothesis).
-/

namespace L

open Std.WP
open scoped Lean.Order

attribute [lang_grind] BinOp.eval Cmp.eval Cmp.evalW Sig.retOr Sig.retVal
attribute [lang_grind cases] Sig

@[lang_grind =] theorem St.setLoc_loc (s : St) (x y : Var) (v : Word) :
    (s.setLoc x v).loc y = if y = x then v else s.loc y := rfl

@[lang_grind =] theorem St.setLoc_mem (s : St) (x : Var) (v : Word) :
    (s.setLoc x v).mem = s.mem := rfl

@[lang_grind =] theorem St.setLocs_nil (s : St) (vs : List Word) : s.setLocs [] vs = s := rfl

@[lang_grind =] theorem St.setLocs_cons (s : St) (x : Var) (xs : List Var) (vs : List Word) :
    s.setLocs (x :: xs) vs = (s.setLoc x (vs.headD 0)).setLocs xs vs.tail := rfl

attribute [lang_grind =] List.headD_cons List.headD_nil List.tail_cons List.tail_nil List.cons.injEq

@[lang_grind =] theorem Locals.init_nil (x : Var) : Locals.init [] x = 0 := by
  simp [Locals.init]

@[lang_grind =] theorem Locals.init_cons_zero (v : Word) (vs : List Word) :
    Locals.init (v :: vs) 0 = v := rfl

@[lang_grind =] theorem Locals.init_cons_succ (v : Word) (vs : List Word) (x : Var) :
    Locals.init (v :: vs) (x + 1) = Locals.init vs x := rfl

attribute [lang_grind] Mem.len8 Mem.len64

/-- A local of a state that is equal to a record literal. `grind` does not project `loc` out of
an equation `t = { mem := m, loc := l }` by itself, because `t.loc x` is an over-applied
projection (docs/gaps/grind-state-eq-projection.lean); a callee spec's frame condition `s' = s₀`
then hides the caller's untouched locals. The multi-pattern fires for every read `t.loc x` and
every record literal in the goal; the equation itself is left to congruence closure. -/
theorem St.loc_of_eq_mk {t : St} {m : Mem} {l : Locals} (h : t = St.mk m l) (x : Var) :
    t.loc x = l x := by
  subst h; rfl

grind_pattern [lang_grind] St.loc_of_eq_mk => t.loc x, St.mk m l

/-- Restoring the caller's locals after a call that left the memory alone gives back the
caller's state. -/
@[lang_grind =] theorem St.restore_eq (s s' : St) (h : s'.mem = s.mem) :
    ({ s' with loc := s.loc } : St) = s := by
  cases s; cases s'; simp_all

theorem invoke_eq {p : Prog} {k : Stmt → M Sig} {f : FnName} {fd : FunDecl} (vs : List Word)
    (h : p.lookup f = some fd) : invoke p k f vs = callFn k fd vs := by
  simp [invoke, lookupFn, h]

/-- A spec of a named block at fuel `n + 1` is a spec of its first step at fuel `n`: this is how
a loop spec (stated about `exec`, so that it is its own induction hypothesis) is used inside the
enclosing body. -/
theorem Triple.step_exec {p : Prog} {n : Nat} {s : Stmt} {P : St → Prop} {Q : Sig → St → Prop}
    (h : ⦃P⦄ exec p (n + 1) s ⦃Q; ⊤⦄) : ⦃P⦄ step p (exec p n) s ⦃Q; ⊤⦄ := h

/-- From a partial-correctness triple to a run (after con-ron's `AM.of_run`). -/
theorem M.of_run {α : Type} {prog : M α} {s s' : St} {a : α} {P : St → Prop}
    {Q : α → St → Prop} (hp : P s) (h : prog.run s = .ok (a, s'))
    (hwp : ⦃fun s => P s⦄ prog ⦃fun r s'' => Q r s''; ⊤⦄) : Q a s' := by
  have hs := hwp.le_wp s hp
  rw [Std.WP.StateT.wp_apply_eq, h] at hs
  exact hs

/-- From a statement about every successful run to a partial-correctness triple. -/
theorem M.triple_of_run {α : Type} {prog : M α} {P : St → Prop} {Q : α → St → Prop}
    (h : ∀ (s : St) (a : α) (s' : St), P s → prog.run s = .ok (a, s') → Q a s') :
    ⦃fun s => P s⦄ prog ⦃fun r s'' => Q r s''; ⊤⦄ := by
  refine ⟨fun s hp => ?_⟩
  rw [Std.WP.StateT.wp_apply_eq]
  cases hr : prog.run s with
  | error e => change (⊤ : Err → Prop) e; simp
  | ok p => exact h s p.1 p.2 hp hr

/-- One iteration of a loop named by a constant `w`. -/
theorem step_while {p : Prog} {k : Stmt → M Sig} {w : Stmt} {c : Cond} {s : Stmt}
    (h : w = .while c s) :
    step p k w = (do
      if (← evalC c) then
        match ← step p k s with
        | .normal => k w
        | .brk => return .normal
        | .ret v => return .ret v
      else return .normal) := by
  subst h; rfl

end L
