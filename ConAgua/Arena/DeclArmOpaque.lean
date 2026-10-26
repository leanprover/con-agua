import ConAgua.Arena.DeclReducePin
import ConAgua.Arena.DeclArmLoop

/-!
# The opaque arm `check_decl_opaque(i, vis)` (lane `decls3`)

`checkDecl`'s `.opaqueDecl` arm: the constant check, the opaque check (the push of `axiomInfo cv`),
then for `Lean.reduceNat`/`Lean.reduceBool` the install pin (`check_reduce_pin`) at the pushed
view. At the loop's relation through the arms' text (`DeclArmLoop.lean`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt CVAt dw)

section model
variable (p : Prog)

/-- After `check_reduce_pin`: the pushed view. -/
def cdoK6 (w : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m6) => some ([w], m6)

/-- After the `reduceBool` pin: the install pin for the two reduce operations. -/
def cdoK5 (n : Nat) (vis nm v w a : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) =>
    if nm = a ∨ nm = r5.headD 0 then cdoK6 w (callW p n "check_reduce_pin" [vis, w, nm, v] m5)
    else some ([w], m5)

/-- After the `reduceNat` pin. -/
def cdoK4 (n : Nat) (vis nm v w : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => cdoK5 p n vis nm v w (r4.headD 0) (pinAtW m4 44)

/-- After `check_opaque_val`. -/
def cdoK3 (n : Nat) (vis nm v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => cdoK4 p n vis nm v (r3.headD 0) (pinAtW m3 43)

/-- After `check_constant_val`. -/
def cdoK2 (n : Nat) (vis q nm v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) => cdoK3 p n vis nm v (callW p n "check_opaque_val" [vis, q] m2)

/-- After `erec_ci`. -/
def cdoK1 (n : Nat) (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    cdoK2 p n vis (r1.headD 0) (rdW (m1.arr64 EREC) (r1.headD 0 + 1))
      (rdW (m1.arr64 EREC) (r1.headD 0 + 5))
      (callW p n "check_constant_val" [vis, r1.headD 0 + 1] m1)

/-- **The model of `check_decl_opaque(i, vis)`.** -/
def cdoW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, i, vis => cdoK1 p n vis (erecCiW n m i 0)

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (i vis q nm v w a : Word)
  (r1 r2 r3 r4 r5 r6 : List Word)
theorem cdoW_step : cdoW p (n + 1) m i vis = cdoK1 p n vis (erecCiW n m i 0) := rfl
theorem cdoK1_some : cdoK1 p n vis (some (r1, m1)) =
    cdoK2 p n vis (r1.headD 0) (rdW (m1.arr64 EREC) (r1.headD 0 + 1))
      (rdW (m1.arr64 EREC) (r1.headD 0 + 5))
      (callW p n "check_constant_val" [vis, r1.headD 0 + 1] m1) := rfl
theorem cdoK2_some : cdoK2 p n vis q nm v (some (r2, m2)) =
    cdoK3 p n vis nm v (callW p n "check_opaque_val" [vis, q] m2) := rfl
theorem cdoK3_some : cdoK3 p n vis nm v (some (r3, m3)) =
    cdoK4 p n vis nm v (r3.headD 0) (pinAtW m3 43) := rfl
theorem cdoK4_some : cdoK4 p n vis nm v w (some (r4, m4)) =
    cdoK5 p n vis nm v w (r4.headD 0) (pinAtW m4 44) := rfl
theorem cdoK5_some : cdoK5 p n vis nm v w a (some (r5, m5)) =
    if nm = a ∨ nm = r5.headD 0 then cdoK6 w (callW p n "check_reduce_pin" [vis, w, nm, v] m5)
    else some ([w], m5) := rfl
theorem cdoK6_some : cdoK6 w (some (r6, m6)) = some ([w], m6) := rfl
end arms

grind_pattern [ind_grind] cdoW_step => cdoW p (n + 1) m i vis
grind_pattern [ind_grind] cdoK1_some => cdoK1 p n vis (some (r1, m1))
grind_pattern [ind_grind] cdoK2_some => cdoK2 p n vis q nm v (some (r2, m2))
grind_pattern [ind_grind] cdoK3_some => cdoK3 p n vis nm v (some (r3, m3))
grind_pattern [ind_grind] cdoK4_some => cdoK4 p n vis nm v w (some (r4, m4))
grind_pattern [ind_grind] cdoK5_some => cdoK5 p n vis nm v w a (some (r5, m5))
grind_pattern [ind_grind] cdoK6_some => cdoK6 w (some (r6, m6))

set_option maxHeartbeats 1600000 in
theorem cdo_specW (hp : p.lookup "check_decl_opaque" = some checkDeclOpaque) (hR : RecProg p)
    (hpa : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (i vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_decl_opaque" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ cdoW p n s₀.mem i vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkDeclOpaque]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, erecCi_specW p hR n,
        callW_spec p n "check_constant_val", callW_spec p n "check_opaque_val",
        pinAt_specW p hpa n, callW_spec p n "check_reduce_pin"] <;>
      finish (gen := 20) [rdW_eq]

end model

local notation "V" => ConLeche.CheckMode.verified

end L.Arena
