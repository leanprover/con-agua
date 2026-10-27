import ConAgua.Arena.IndPosSpec.Nb
import ConAgua.Arena.IndPosSpec.RsLook
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# P2rtW

`p2rtW`, `p2rtK1`, `p2rtK2`, `p2rtK3`, `p2sfW`, `p2sfK`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Models -/

mutual
/-- `nest_root`. -/
def p2rtW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, ctx, hO, hL, cO, cL, ns, oO, oL =>
    if cL = 0 then some ([oO, oL, ns], m)
    else p2rtK1 cR n vis ctx hO hL cO cL oO oL
      (nbCtorsW cR n m vis ctx 1 0 0 0 (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 10)) (rdW (m.arr64 IW) (ctx + 7))
        (rdW (m.arr64 IW) (ctx + 8)) (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) hO hL
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO)) (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1)) ns 0 0)
def p2rtK1 (cR : CallM) (n : Nat) (vis ctx hO hL cO cL oO oL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => p2rtK2 cR n vis ctx hO hL cO cL oO oL (r.tail.tail.headD 0) (posRecW m1 [r.headD 0, r.tail.headD 0])
def p2rtK2 (cR : CallM) (n : Nat) (vis ctx hO hL cO cL oO oL ns2 : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m2) => p2rtK3 cR n vis ctx hO hL cO cL ns2 (snocW n m2 oO oL q)
def p2rtK3 (cR : CallM) (n : Nat) (vis ctx hO hL cO cL ns2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => p2rtW cR n m3 vis ctx hO hL (cO + 1) (cL - 1) ns2 (r.headD 0) (r.tail.headD 0)
end

mutual
/-- `nest_seeds_fuel`. -/
def p2sfW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, dO, dL, k, f =>
    if dL ≤ k then some ([f], m)
    else p2sfK n dO dL k f (wfWf n m (rdW (m.arr64 IW) (dO + k)))
def p2sfK (n : Nat) (dO dL k f : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => p2sfW n m1 dO dL (k + 1) (if f < r.headD 0 then r.headD 0 else f)
end

section arms
variable (cR : CallM) (n : Nat) (m m1 : Mem) (vis ctx hO hL cO cL ns oO oL ns2 q dO dL k f sO sL hi key nPc : Word)
  (r : List Word)
theorem p2sfK_some : p2sfK n dO dL k f (some (r, m1)) =
    p2sfW n m1 dO dL (k + 1) (if f < r.headD 0 then r.headD 0 else f) := by rw [p2sfK]
theorem p2sfW_done (h : dL ≤ k) : p2sfW (n + 1) m dO dL k f = some ([f], m) := by simp [p2sfW, h]
theorem p2sfW_step (h : ¬ dL ≤ k) : p2sfW (n + 1) m dO dL k f =
    p2sfK n dO dL k f (wfWf n m (rdW (m.arr64 IW) (dO + k))) := by simp [p2sfW, h]
end arms
attribute [ind_grind] p2sfW_done p2sfW_step p2sfK_some

section spec
variable {p : Prog} (L : RsLook p)
include L

theorem nestSeedsFuel_spec (n : Nat) : ∀ (s₀ : St) (dO dL k f : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_seeds_fuel" [dO, dL, k, f]
    ⦃fun r s' => LocEq s' s₀ ∧ p2sfW n s₀.mem dO dL k f = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ dO dL k f
    exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | succ n ih =>
    intro s₀ dO dL k f
    simp only [invoke_eq _ L.pfuel, callFn, nestSeedsFuelL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, whnfWalkFuel_spec' p L.nb n, ih] <;>
      finish (gen := 20) [rdW_eq]

end spec

end L.Ind

end
