import ConAgua.Arena.IndStubs

/-!
# PureRun

`Rec3At`, `StmtAt`, `StmtL`, `decStmtL`, `pure_run_eq`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section nat
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-! ### Statements -/

/-- A three-word record at `p`. -/
def Rec3At (m : Mem) (p a b c : Word) : Prop :=
  p.toNat + 3 ≤ iwTop m ∧ (iwA m)[p.toNat]? = some a ∧ (iwA m)[p.toNat + 1]? = some b ∧
    (iwA m)[p.toNat + 2]? = some c

/-- **A statement record** `[hyps.off, hyps.len, eq]` at `p`. -/
def StmtAt (m : Mem) (p : Word) (st : List EIdx × EIdx) : Prop :=
  ∃ ho hl e : Word, Rec3At m p ho hl e ∧ ho.toNat + hl.toNat ≤ iwTop m ∧
    decHL m ho.toNat hl.toNat = some st.1 ∧ H e ∧ st.2 = decE e

/-- **A statement list**: the slice `(o, l)` of pointers to statement records. -/
def StmtL (m : Mem) (o l : Nat) (ss : List (List EIdx × EIdx)) : Prop :=
  o + l ≤ iwTop m ∧ l = ss.length ∧ ∀ (j : Nat) (hj : j < ss.length), ∃ p : Word,
    (iwA m)[o + j]? = some p ∧ StmtAt m p ss[j]

def decStmtL (m : Mem) (r : List Word) (ss : List (List EIdx × EIdx)) : Prop :=
  StmtL m (r.getD 0 0).toNat (r.getD 1 0).toNat ss

/-! ### Records of statements -/

theorem pure_run_eq {α : Type} {x y : α} {a a' : AState} (h : (pure x : AM α).run a = .ok (y, a')) :
    y = x ∧ a' = a := by
  simp only [StateT.run_pure] at h
  have := Except.ok.inj h
  exact ⟨(Prod.mk.inj this).1.symm, (Prod.mk.inj this).2.symm⟩

end nat

end L.Ind
