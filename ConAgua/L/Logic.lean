module

public import ConAgua.L.Semantics
public import Std.Do.Triple.SpecLemmas
public import Std.WP.Monad.Instances
public import Std.WP.Triple.Basic
import ConAgua.L.GrindAttr

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

/-- A word store leaves the byte arrays alone. -/
@[lang_grind =] theorem Mem.arr8_set64_apply (m : Mem) (a : ArrId) (i v : Word) (x : ArrId) :
    (m.set64 a i v).arr8 x = m.arr8 x := rfl

/-- A byte store leaves the word arrays alone. -/
@[lang_grind =] theorem Mem.arr64_set8_apply (m : Mem) (a : ArrId) (i v : Word) (x : ArrId) :
    (m.set8 a i v).arr64 x = m.arr64 x := rfl

/-! ### Global variables

A global read after a write is the written word or the old one; writes to arrays and globals do
not touch each other. With these, `vcgen` + `finish` treat globals as they treat locals. -/

/-- Stated over the numbers: `grind` decides `h.id = g.id` for literal globals. -/
@[lang_grind =] theorem Mem.setG_glob (m : Mem) (g h : GVar) (v : Word) :
    (m.setG g v).glob h = if h.id = g.id then v else m.glob h := by
  simp only [Mem.setG]
  by_cases e : h = g
  · subst e; simp
  · rw [ite_eq_right e, ite_eq_right (fun e' => e (by cases h; cases g; simp_all))]

@[lang_grind =] theorem Mem.setG_arr8 (m : Mem) (g : GVar) (v : Word) (a : ArrId) :
    (m.setG g v).arr8 a = m.arr8 a := rfl

@[lang_grind =] theorem Mem.setG_arr64 (m : Mem) (g : GVar) (v : Word) (a : ArrId) :
    (m.setG g v).arr64 a = m.arr64 a := rfl

@[lang_grind =] theorem Mem.setG_bytes (m : Mem) (g : GVar) (v : Word) :
    (m.setG g v).bytes = m.bytes := rfl

@[lang_grind =] theorem Mem.setG_words (m : Mem) (g : GVar) (v : Word) :
    (m.setG g v).words = m.words := rfl

@[lang_grind =] theorem Mem.set64_glob (m : Mem) (a : ArrId) (i v : Word) (g : GVar) :
    (m.set64 a i v).glob g = m.glob g := rfl

@[lang_grind =] theorem Mem.set8_glob (m : Mem) (a : ArrId) (i v : Word) (g : GVar) :
    (m.set8 a i v).glob g = m.glob g := rfl

@[lang_grind =] theorem St.setG_mem (s : St) (g : GVar) (v : Word) :
    (s.setG g v).mem = s.mem.setG g v := rfl

@[lang_grind =] theorem St.setG_loc (s : St) (g : GVar) (v : Word) (x : Var) :
    (s.setG g v).loc x = s.loc x := rfl

/-- Byte reads are compared as words (`c != LITS.c8[k]`); the model compares bytes. -/
theorem UInt8.toUInt64_eq_iff (a b : UInt8) : (a.toUInt64 = b.toUInt64) = (a = b) := by
  apply propext; constructor
  · intro h; apply UInt8.toNat_inj.mp; have := congrArg UInt64.toNat h; simpa using this
  · intro h; rw [h]

attribute [lang_grind =] UInt8.toUInt64_eq_iff

/-- A local of a state that is equal to a record literal. `grind` does not project `loc` out of
an equation `t = { mem := m, loc := l }` by itself, because `t.loc x` is an over-applied
projection (docs/gaps/grind-state-eq-projection.lean); a callee spec's frame condition `s' = s₀`
then hides the caller's untouched locals. The multi-pattern fires for every read `t.loc x` and
every record literal in the goal; the equation itself is left to congruence closure. -/
theorem St.loc_of_eq_mk {t : St} {m : Mem} {l : Locals} (h : t = St.mk m l) (x : Var) :
    t.loc x = l x := by
  subst h; rfl

grind_pattern [lang_grind] St.loc_of_eq_mk => t.loc x, St.mk m l

/-- The locals of `s` are those of `t`: the frame condition of a callee that may change memory
(post `LocEq s' s₀ ∧ …`). A plain `s'.loc = s₀.loc` does not reach the caller's reads
`s'.loc x`: `grind` would have to apply the function equation, and the term `s₀.loc x` does not
exist yet. The pattern `LocEq s t, s.loc x` creates it. -/
def LocEq (s t : St) : Prop := s.loc = t.loc

theorem LocEq.loc {s t : St} (h : LocEq s t) (x : Var) : s.loc x = t.loc x := by rw [h]

grind_pattern [lang_grind] LocEq.loc => LocEq s t, s.loc x

/-- `callFn` restores the caller's locals: the callee's post `LocEq s' s₀` holds. -/
theorem LocEq.restore (s : St) (m : Mem) : LocEq (St.mk m s.loc) s := rfl

grind_pattern [lang_grind] LocEq.restore => St.mk m s.loc

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
