import ConAgua.Arena.DeclReduceSpec2
import ConAgua.Arena.WhnfCoreApp
import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.RecGenSpec4

/-!
# `check_reduce_pin(vis, vis2, c, v)` refines `checkReducePin` (lane `decls3`)

The `Lean.reduceNat`/`Lean.reduceBool` install gate, after the opaque's push: the stored constant
at the pushed view `vis2` (`reduce_stored_ok`), then at the pre-insertion view `vis` the element
inductive, the pin's guards, the value against the pin, and the identity certificate. The stage
relation at `vis2` gives it at `vis` (`fe2.restrictTo vis`: the same index, `EnvR.restrictTo`) and
back. L change: a handle guard after `reduce_cert_var` (`is_def_eq_core`'s spec needs it).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-- The stage relation at another view of the same environment. -/
theorem StageR.restrict {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (h : StageR dn vis fe m a) (k : Word) :
    StageR dn k (fe.restrictTo k.toNat) m a :=
  ⟨⟨h.1.arena, h.1.core, h.1.pins, h.1.env.restrictTo k, h.1.mode⟩, h.2⟩

theorem IFEnv.restrictTo_restrictTo (fe : IFEnv) (j k : Nat) :
    (fe.restrictTo j).restrictTo k = fe.restrictTo k := rfl

theorem IFEnv.restrictTo_self (fe : IFEnv) : fe.restrictTo fe.visibleBelow = fe := rfl

/-! ## The model -/

section model
variable (p : Prog)

/-- After the second comparison. -/
def crpK8 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r8, m8) => if r8.headD 0 = 0 then none else some ([0], m8)

/-- After `mk_app`: the identity certificate. -/
def crpK7 (cl : CallM) (n : Nat) (vis x : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ax, m7) => crpK8 (cl n "is_def_eq_core" [vis, 1, ax, x] m7)

/-- After `reduce_cert_var`: the handle guard, the application. -/
def crpK6 (cl : CallM) (n : Nat) (vis v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) =>
    if 4294967296 ≤ r6.headD 0 then none else crpK7 cl n vis (r6.headD 0) (mkAppW m6 v (r6.headD 0))

/-- After the comparison with the pin. -/
def crpK5 (cl : CallM) (n : Nat) (vis c v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) =>
    if r5.headD 0 = 0 then none else crpK6 cl n vis v (callW p n "reduce_cert_var" [c] m5)

/-- After `reduce_decl_pin`. -/
def crpK4 (cl : CallM) (n : Nat) (vis c v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => crpK5 p cl n vis c v (cl n "is_def_eq_core" [vis, 0, v, r4.headD 0] m4)

/-- After `reduce_pin_guard`. -/
def crpK3 (cl : CallM) (n : Nat) (vis c v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then none else crpK4 p cl n vis c v (callW p n "reduce_decl_pin" [c] m3)

/-- After `reduce_elem_ok`. -/
def crpK2 (cl : CallM) (n : Nat) (vis c v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then none else crpK3 p cl n vis c v (callW p n "reduce_pin_guard" [vis, c] m2)

/-- After `reduce_stored_ok`. -/
def crpK1 (cl : CallM) (n : Nat) (vis c v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then none else crpK2 p cl n vis c v (callW p n "reduce_elem_ok" [vis, c] m1)

/-- **The model of `check_reduce_pin(vis, vis2, c, v)`.** -/
def crpW (cl : CallM) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, vis, vis2, c, v => crpK1 p cl n vis c v (callW p n "reduce_stored_ok" [vis2, c] m)

section arms
variable (cl : CallM) (n : Nat) (m m1 m2 m3 m4 m5 m6 m7 m8 : Mem) (vis vis2 c v x ax : Word)
  (r1 r2 r3 r4 r5 r6 r8 : List Word)
theorem crpW_step : crpW p cl (n + 1) m vis vis2 c v =
    crpK1 p cl n vis c v (callW p n "reduce_stored_ok" [vis2, c] m) := rfl
theorem crpK1_some : crpK1 p cl n vis c v (some (r1, m1)) =
    if r1.headD 0 = 0 then none else crpK2 p cl n vis c v (callW p n "reduce_elem_ok" [vis, c] m1) :=
  rfl
theorem crpK2_some : crpK2 p cl n vis c v (some (r2, m2)) =
    if r2.headD 0 = 0 then none
    else crpK3 p cl n vis c v (callW p n "reduce_pin_guard" [vis, c] m2) := rfl
theorem crpK3_some : crpK3 p cl n vis c v (some (r3, m3)) =
    if r3.headD 0 = 0 then none else crpK4 p cl n vis c v (callW p n "reduce_decl_pin" [c] m3) := rfl
theorem crpK4_some : crpK4 p cl n vis c v (some (r4, m4)) =
    crpK5 p cl n vis c v (cl n "is_def_eq_core" [vis, 0, v, r4.headD 0] m4) := rfl
theorem crpK5_some : crpK5 p cl n vis c v (some (r5, m5)) =
    if r5.headD 0 = 0 then none else crpK6 cl n vis v (callW p n "reduce_cert_var" [c] m5) := rfl
theorem crpK6_some : crpK6 cl n vis v (some (r6, m6)) =
    if 4294967296 ≤ r6.headD 0 then none else crpK7 cl n vis (r6.headD 0) (mkAppW m6 v (r6.headD 0)) :=
  rfl
theorem crpK7_some : crpK7 cl n vis x (some (ax, m7)) =
    crpK8 (cl n "is_def_eq_core" [vis, 1, ax, x] m7) := rfl
theorem crpK8_some : crpK8 (some (r8, m8)) = if r8.headD 0 = 0 then none else some ([0], m8) := rfl
end arms

grind_pattern [ind_grind] crpW_step => crpW p cl (n + 1) m vis vis2 c v
grind_pattern [ind_grind] crpK1_some => crpK1 p cl n vis c v (some (r1, m1))
grind_pattern [ind_grind] crpK2_some => crpK2 p cl n vis c v (some (r2, m2))
grind_pattern [ind_grind] crpK3_some => crpK3 p cl n vis c v (some (r3, m3))
grind_pattern [ind_grind] crpK4_some => crpK4 p cl n vis c v (some (r4, m4))
grind_pattern [ind_grind] crpK5_some => crpK5 p cl n vis c v (some (r5, m5))
grind_pattern [ind_grind] crpK6_some => crpK6 cl n vis v (some (r6, m6))
grind_pattern [ind_grind] crpK7_some => crpK7 cl n vis x (some (ax, m7))
grind_pattern [ind_grind] crpK8_some => crpK8 (some (r8, m8))

/-- The lookups of `check_reduce_pin`. -/
structure CrpProg (p : Prog) : Prop where
  red : RedProg p
  rcv : RcvProg p
  crp : p.lookup "check_reduce_pin" = some checkReducePinL
  rpg : p.lookup "reduce_pin_guard" = some reducePinGuardL
  rdp : p.lookup "reduce_decl_pin" = some reduceDeclPinL
  db : p.lookup "der_b" = some derB
  af : p.lookup "app_find" = some appFind
  ap : p.lookup "app_push" = some appPush
  ia : p.lookup "intern_app" = some internApp
  ma : p.lookup "mk_app" = some mkApp
  bvb : BvbProg p
  hf : HfF p
  /-- `all_level_params_defined`'s program (`reduce_pin_guard` under `StageT`, `DeclCrpT.lean`). -/
  apd : L.Ind.ApdF p

set_option maxHeartbeats 1600000 in
theorem crp_specW (h : CrpProg p) (cl : CallM) (hc : CallSpec p cl) (n : Nat) (s₀ : St) (vis vis2 c v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_reduce_pin" [vis, vis2, c, v]
    ⦃fun r s' => LocEq s' s₀ ∧ crpW p cl n s₀.mem vis vis2 c v = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.crp]
  simp only [callFn, checkReducePinL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        callW_spec p n "reduce_stored_ok", callW_spec p n "reduce_elem_ok",
        callW_spec p n "reduce_pin_guard", callW_spec p n "reduce_decl_pin",
        hc n "is_def_eq_core", callW_spec p n "reduce_cert_var",
        mkApp_spec p h.db h.af h.ap h.ia h.ma n] <;>
      finish (gen := 20)

end model

local notation "V" => ConLeche.CheckMode.verified

end L.Arena
