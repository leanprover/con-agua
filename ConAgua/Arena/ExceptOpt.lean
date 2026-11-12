module

public import ConAgua.Arena.GrindAttr

@[expose] public section

/-!
# A reader's `Except` as an `Option`

con-ron's inductive reader (`readBlock`, `blockCounts`, `blockMemberCounts`) answers an `Except
CheckError _`, whose every error is `.invalid` with a message; L's reader returns a flag (and the
value), drops the message, and its caller fails with the invalid class. The relation is upstream's
own (`ConRon.Bridge.Inductives.readBlock_spec`): the two answers agree as `Option`s
(`Except.toOption`), the same value or both an error. These are the equations a proof uses; they
are in `arena_grind`.
-/

namespace L.Arena

@[simp, grind =] theorem except_toOption_ok {ε α : Type} (a : α) :
    (Except.ok a : Except ε α).toOption = some a := rfl

@[simp, grind =] theorem except_toOption_error {ε α : Type} (e : ε) :
    (Except.error e : Except ε α).toOption = none := rfl

theorem except_toOption_eq_some {ε α : Type} {x : Except ε α} {a : α} :
    x.toOption = some a ↔ x = .ok a := by
  cases x <;> simp [Except.toOption]

theorem except_toOption_eq_none {ε α : Type} {x : Except ε α} :
    x.toOption = none ↔ ∃ e, x = .error e := by
  cases x <;> simp [Except.toOption]

attribute [arena_grind =] except_toOption_ok except_toOption_error

end L.Arena
