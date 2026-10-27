module

public import ConAgua.L.Logic
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# Conditions and expressions as pure values

`evalE`/`evalC` read the state and never write it; when they do not throw, their value is
`Expr.pval`/`Cond.pval` of the state (reads past the end are `0` there; those runs throw). With
`evalC_spec` in place of unfolding `evalC`, `vcgen` gives one path per `if`, not one per
short-circuit exit of an `&&`/`||` chain: `if c₁ && … && c₉ then S else T` otherwise puts `T`'s
verification condition on all ten exits, and a chain of such `if`s multiplies (DESIGN.md, "Slow
declarations").

Recipe (`ConAgua/Scan/Key.lean`, `keyAtG2_spec`):
`vcgen [exec, step, evalC_spec, evalE_spec, evalArgs, setLoc]`, then
`all_goals simp only [Cond.pval, Expr.pval, rd8 …, Locals.init, St.loc, List.getD_cons_zero,
List.getD_cons_succ, Cmp.eval, BinOp.eval, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
beq_iff_eq] at *` and `grind`. (`grind` alone unfolds `Cond.pval` one E-matching generation per
level and runs out on long chains.)
-/

set_option experimental.vcgen true
open Std.WP
open scoped Lean.Order
namespace L

/-- Byte `i` of byte array `a`, zero-extended, `0` out of bounds (what `ld8` reads when it does
not throw). -/
def rd8 (m : Mem) (a : ArrId) (i : Word) : Word := ((m.arr8 a).getD i.toNat 0).toUInt64
/-- Word `i` of word array `a`, `0` out of bounds. -/
def rd64 (m : Mem) (a : ArrId) (i : Word) : Word := (m.arr64 a).getD i.toNat 0
/-- Byte `i` of a constant byte string, `0` out of bounds. -/
def rdc (d : List UInt8) (i : Word) : Word := (d.getD i.toNat 0).toUInt64

/-- An expression's value in `s`, reads out of bounds as `0`. -/
def Expr.pval (s : St) : Expr → Word
  | .const w => w
  | .var x => s.loc x
  | .bin op a b => op.eval (Expr.pval s a) (Expr.pval s b)
  | .ld8 a i => rd8 s.mem a (Expr.pval s i)
  | .ld64 a i => rd64 s.mem a (Expr.pval s i)
  | .len8 a => s.mem.len8 a
  | .len64 a => s.mem.len64 a
  | .cmpw c a b => c.evalW (Expr.pval s a) (Expr.pval s b)
  | .ldc d i => rdc d (Expr.pval s i)
  | .glob g => s.mem.glob g
  | .ld64t a t i => rd64 s.mem (tierA a (Expr.pval s t)) (Expr.pval s i)
  | .len64t a t => s.mem.len64 (tierA a (Expr.pval s t))
  | .ld8x8 b i => le64 (s.mem.src8 b) (Expr.pval s i).toNat

/-- A condition's value in `s` (short-circuit makes no difference: nothing is written). -/
def Cond.pval (s : St) : Cond → Bool
  | .cmp c a b => c.eval (Expr.pval s a) (Expr.pval s b)
  | .and p q => Cond.pval s p && Cond.pval s q
  | .or p q => Cond.pval s p || Cond.pval s q
  | .not p => !Cond.pval s p

theorem evalE_spec (e : Expr) (s₀ : St) :
    ⦃fun s => s = s₀⦄ evalE e ⦃fun v s' => s' = s₀ ∧ v = Expr.pval s₀ e; ⊤⦄ := by
  induction e with
  | const w => vcgen [evalE] <;> grind [Expr.pval]
  | var x => vcgen [evalE] <;> grind [Expr.pval]
  | bin op a b iha ihb => vcgen [evalE, iha, ihb] <;> grind [Expr.pval]
  | ld8 a i ih => vcgen [evalE, ld8, ih] <;> simp_all [Expr.pval, rd8, Array.getD]
  | ld64 a i ih => vcgen [evalE, ld64, ih] <;> simp_all [Expr.pval, rd64, Array.getD]
  | len8 a => vcgen [evalE] <;> grind [Expr.pval]
  | len64 a => vcgen [evalE] <;> grind [Expr.pval]
  | cmpw c a b iha ihb => vcgen [evalE, iha, ihb] <;> grind [Expr.pval]
  | ldc d i ih => vcgen [evalE, ldc, ih] <;> simp_all [Expr.pval, rdc, List.getD]
  | glob g => vcgen [evalE] <;> grind [Expr.pval]
  | ld64t a t i iht ihi => vcgen [evalE, ld64, iht, ihi] <;> simp_all [Expr.pval, rd64, Array.getD]
  | len64t a t ih => vcgen [evalE, ih] <;> grind [Expr.pval]
  | ld8x8 b i ih => vcgen [evalE, ld8x8, ih] <;> simp_all [Expr.pval]

theorem evalC_spec (c : Cond) (s₀ : St) :
    ⦃fun s => s = s₀⦄ evalC c ⦃fun b s' => s' = s₀ ∧ b = Cond.pval s₀ c; ⊤⦄ := by
  induction c with
  | cmp c a b => vcgen [evalC, evalE_spec a s₀, evalE_spec b s₀] <;> grind [Cond.pval]
  | and p q ihp ihq => vcgen [evalC, ihp, ihq] <;> grind [Cond.pval]
  | or p q ihp ihq => vcgen [evalC, ihp, ihq] <;> grind [Cond.pval]
  | not p ih => vcgen [evalC, ih] <;> grind [Cond.pval]

end L
