module

public import ConAgua.Compiler.SimCall

@[expose] public section

/-!
# Tail calls

`x⃗ := f(a⃗); return x⃗`, compiled by `tailCode`: the arguments into their registers, fuel, the
frame popped, a jump to `f`. `f` then returns to this function's caller: its simulation
(`FunSim`) does not depend on the caller's frame, so it is used with the return address above
this function's frame, and its results are this function's (`Conts.tail`).
-/

namespace L.Compiler

open L

section
variable [Host] {G : Layout} (hG : G.Ok) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
  (p : Prog)
include hG hTab

theorem sim_tail (t : NTree) (n : Nat) (hFun : FunSim p G t n)
    (hProg : ∀ f fd, p.lookup f = some fd → ∃ kf, Code (compileFn G.tab t f fd) kf) (s u : Stmt) :
    SimSTail p G (stepRun p (exec p n)) (· ≤ n) s u := by
  sorry

end

end L.Compiler
