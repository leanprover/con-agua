import ConAgua.Arena.WhnfCoreStep
open L L.Arena ConRon.Arena
open Std.WP
open scoped Lean.Order
set_option experimental.vcgen true
namespace L.Arena

def tB : FunDecl := lfn (mode, vis, d, v, h, so, sn) locals (hd, ho, hn, st, r) {
  (hd, ho, hn) := call head_and_args(v);
  (st, r) := call whnf_app(mode, vis, d, v, hd, ho, hn, 0, so, sn, 0);
  return (st, r)
}

def tBW (p : Prog) (n : Nat) (m : Mem) (mode vis d v h so sn : Word) : Option (Word × Word × Mem) :=
  match callW p n "head_and_args" [v] m with
  | none => none
  | some (r₃, m₃) =>
  match callW p n "whnf_app" [mode, vis, d, v, r₃.headD 0, r₃.tail.headD 0, r₃.tail.tail.headD 0, 0, so, sn, 0] m₃ with
  | none => none
  | some (r₄, m₄) => some (r₄.headD 0, r₄.tail.headD 0, m₄)

theorem tBW_some (p : Prog) (n : Nat) (m m₃ m₄ : Mem) (mode vis d v h so sn : Word) (r₃ r₄ : List Word)
    (h₃ : callW p n "head_and_args" [v] m = some (r₃, m₃))
    (h₄ : callW p n "whnf_app" [mode, vis, d, v, r₃.headD 0, r₃.tail.headD 0, r₃.tail.tail.headD 0, 0, so, sn, 0] m₃ = some (r₄, m₄)) :
    tBW p n m mode vis d v h so sn = some (r₄.headD 0, r₄.tail.headD 0, m₄) := by
  simp only [tBW, h₃, h₄]

theorem tB_spec (p : Prog) (hp : p.lookup "tB" = some tB) (n : Nat) (s₀ : St) (mode vis d v h so sn : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "tB" [mode, vis, d, v, h, so, sn]
    ⦃fun r s' => LocEq s' s₀ ∧
      tBW p n s₀.mem mode vis d v h so sn = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, tB]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "whnf_app", callW_spec p n "head_and_args"] <;>
    finish [tBW_some]
end L.Arena
