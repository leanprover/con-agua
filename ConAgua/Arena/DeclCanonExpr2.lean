module

public import ConAgua.Arena.DeclCanonExpr
import ConAgua.Arena.DeclCvg

@[expose] public section

/-!
# The canonical expression comparison, relational lemma (lane `decls3`, helper `decls3-canon`)
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem cnGetD1' (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, z⟩⟩ <;> rfl
theorem getD2' (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, _ | ⟨z, w⟩⟩⟩ <;> rfl
theorem getD3' (r : List Word) : r.getD 3 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, v⟩⟩⟩⟩ <;> rfl

theorem andThen_ok' {A B : AM Bool} {a : AState} {r r1 : Word} {b1 : Bool} {Q : Prop}
    (hA : A.run a = .ok (b1, a)) (hr1 : r1 = if b1 then 1 else 0)
    (hB : r1 ≠ 0 → ∃ b2, B.run a = .ok (b2, a) ∧ r = (if b2 then 1 else 0) ∧ Q)
    (h0 : r1 = 0 → r = 0 ∧ Q) :
    ∃ b, (do let x ← A; if x = true then B else pure false : AM Bool).run a = .ok (b, a) ∧
      r = (if b then 1 else 0) ∧ Q := by
  cases b1
  · obtain ⟨hr, hQ⟩ := h0 (by simpa using hr1)
    refine ⟨false, ?_, by simp [hr], hQ⟩
    simp [StateT.run_bind, hA, exc_ok_bind']; rfl
  · obtain ⟨b2, hb2, hr, hQ⟩ := hB (by simp [hr1])
    refine ⟨b2, ?_, hr, hQ⟩
    simp [StateT.run_bind, hA, exc_ok_bind', hb2]

/-- Literals are hash-consed: two handles viewing the same literal are the same handle. -/
def LitInj (a : AState) : Prop :=
  ∀ (x y : EIdx) (l : ConLeche.Literal), a.store.view x = some (.lit l) →
    a.store.view y = some (.lit l) → x = y

theorem ceW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (po pl qo ql co cl fuel x y r : Word) (ps qs cs : List NIdx),
    ceW n m po pl qo ql co cl fuel x y = some (r, m') → StageR vis fe m a →
    CtxR m po pl qo ql co cl ps qs cs → LitInj a → PoolSmall m → x.toNat < 2 ^ 32 →
    y.toNat < 2 ^ 32 →
    ∃ b, (ConRon.Arena.canonExprEq ps qs cs fuel.toNat (decE x) (decE y)).run a = .ok (b, a) ∧
      r = (if b then 1 else 0) ∧ StageR vis fe m' a ∧ IWGrow m m' ∧ PoolSmall m' := by
  sorry

/-- The post of a comparison that leaves the twin state alone but may grow the pool, with the
literal hash-consing carried along. -/
def CPostL {α : Type} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (dec : Mem → List Word → α → Prop) (m m' : Mem) (a : AState) (r : List Word) (x : α) : Prop :=
  CPost dn vis fe dec m m' a r x ∧ LitInj a

/-- **`canon_expr_eq` refines `canonExprEq`** (literals compared by handle, `LitInj`). -/
@[refines ConRon.Arena.canonExprEq]
theorem canonExprEq_refines (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (po pl qo ql co cl fuel x y : Word) (ps qs cs : List NIdx) :
    RefAM p "canon_expr_eq" [po, pl, qo, ql, co, cl, fuel, x, y]
      (fun m a => StageR vis fe m a ∧ CtxR m po pl qo ql co cl ps qs cs ∧ LitInj a ∧
        PoolSmall m ∧ x.toNat < 2 ^ 32 ∧ y.toNat < 2 ^ 32)
      (ConRon.Arena.canonExprEq ps qs cs fuel.toNat (decE x) (decE y))
      (CPostL dn vis fe decW0B) := by
  sorry

end L.Ind
