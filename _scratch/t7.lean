import ConAgua.Arena.WhnfCoreStep
open L L.Arena ConRon.Arena
open Std.WP
open scoped Lean.Order
set_option experimental.vcgen true
namespace L.Arena

def tA : FunDecl := lfn (mode, vis, d, v, h, so, sn) locals (st, r) {
  (st, r) := call whnf_app(mode, vis, d, v, h, so, sn, u64(v == h), so, sn, 0);
  return (st, r)
}

def tAW (p : Prog) (n : Nat) (m : Mem) (mode vis d v h so sn : Word) : Option (Word × Word × Mem) :=
  match callW p n "whnf_app" [mode, vis, d, v, h, so, sn, Cmp.evalW .eq v h, so, sn, 0] m with
  | none => none
  | some (r₄, m₄) => some (r₄.headD 0, r₄.tail.headD 0, m₄)

theorem tAW_some (p : Prog) (n : Nat) (m m₄ : Mem) (mode vis d v h so sn : Word) (r₄ : List Word)
    (h₄ : callW p n "whnf_app" [mode, vis, d, v, h, so, sn, Cmp.evalW .eq v h, so, sn, 0] m = some (r₄, m₄)) :
    tAW p n m mode vis d v h so sn = some (r₄.headD 0, r₄.tail.headD 0, m₄) := by
  simp only [tAW, h₄]

theorem tA_spec (p : Prog) (hp : p.lookup "tA" = some tA) (n : Nat) (s₀ : St) (mode vis d v h so sn : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "tA" [mode, vis, d, v, h, so, sn]
    ⦃fun r s' => LocEq s' s₀ ∧
      tAW p n s₀.mem mode vis d v h so sn = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, tA]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "whnf_app"] <;>
    finish [tAW_some]
end L.Arena
