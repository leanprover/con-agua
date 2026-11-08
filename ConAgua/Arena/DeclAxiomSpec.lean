module

public import ConAgua.Arena.DeclReduceSpec2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclBasisSpec2
import ConAgua.Arena.DeclCvg
import ConAgua.Arena.DeclReduceSpec
import ConAgua.Arena.WhnfDeltaRefine
import ConAgua.L.LocNF
import Std.Tactic.BVDecide.Normalize.Bool
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# The `ofReduce*` axioms: `of_reduce_ax_ok(vis, q)` refines `ofReduceAxOk` (lane `decls3`)

The pinned `Eq` basis (`find_is` against `rom_ci(0)`), the element inductive and the stored reduce
opaque (`reduce_elem_ok`, `reduce_stored_ok`), the pin (`of_reduce_pin_a`, `matches_pin`). L
change: the axiom's name word loaded once into a local (it was loaded inside two call arguments).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

section model
variable (p : Prog)

/-- After `of_reduce_pin_a`: the comparison. -/
def oraK7 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r7, m7) => mpW m7 q (r7.headD 0)

/-- After `reduce_stored_ok`. -/
def oraK6 (n : Nat) (q nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) =>
    if r6.headD 0 = 0 then some ([0], m6) else oraK7 q (callW p n "of_reduce_pin_a" [nm] m6)

/-- After `reduce_elem_ok`. -/
def oraK5 (n : Nat) (vis q nm c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) =>
    if r5.headD 0 = 0 then some ([0], m5)
    else oraK6 p n q nm (callW p n "reduce_stored_ok" [vis, c] m5)

/-- After `find_is`. -/
def oraK4 (n : Nat) (vis q nm c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if r4.headD 0 = 0 then some ([0], m4)
    else oraK5 p n vis q nm c (callW p n "reduce_elem_ok" [vis, c] m4)

/-- After `rom_ci(0)`. -/
def oraK3 (n : Nat) (vis q nm c en : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => oraK4 p n vis q nm c (callW p n "find_is" [vis, en, r3.headD 0] m3)

/-- After the `Eq` pin. -/
def oraK2 (n : Nat) (vis q nm c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => oraK3 p n vis q nm c (r2.headD 0) (callW p n "rom_ci" [0] m2)

/-- After `of_reduce_op`. -/
def oraK1 (n : Nat) (vis q nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => oraK2 p n vis q nm (r1.headD 0) (pinAtW m1 0)

/-- **The model of `of_reduce_ax_ok(vis, q)`.** -/
def oraW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, q =>
    oraK1 p n vis q (rdW (m.arr64 EREC) q) (oroW m (rdW (m.arr64 EREC) q))

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 m7 : Mem) (vis q nm c en : Word)
  (r1 r2 r3 r4 r5 r6 r7 : List Word)
theorem oraW_step : oraW p (n + 1) m vis q =
    oraK1 p n vis q (rdW (m.arr64 EREC) q) (oroW m (rdW (m.arr64 EREC) q)) := rfl
theorem oraK1_some : oraK1 p n vis q nm (some (r1, m1)) =
    oraK2 p n vis q nm (r1.headD 0) (pinAtW m1 0) := rfl
theorem oraK2_some : oraK2 p n vis q nm c (some (r2, m2)) =
    oraK3 p n vis q nm c (r2.headD 0) (callW p n "rom_ci" [0] m2) := rfl
theorem oraK3_some : oraK3 p n vis q nm c en (some (r3, m3)) =
    oraK4 p n vis q nm c (callW p n "find_is" [vis, en, r3.headD 0] m3) := rfl
theorem oraK4_some : oraK4 p n vis q nm c (some (r4, m4)) =
    if r4.headD 0 = 0 then some ([0], m4)
    else oraK5 p n vis q nm c (callW p n "reduce_elem_ok" [vis, c] m4) := rfl
theorem oraK5_some : oraK5 p n vis q nm c (some (r5, m5)) =
    if r5.headD 0 = 0 then some ([0], m5)
    else oraK6 p n q nm (callW p n "reduce_stored_ok" [vis, c] m5) := rfl
theorem oraK6_some : oraK6 p n q nm (some (r6, m6)) =
    if r6.headD 0 = 0 then some ([0], m6) else oraK7 q (callW p n "of_reduce_pin_a" [nm] m6) := rfl
theorem oraK7_some : oraK7 q (some (r7, m7)) = mpW m7 q (r7.headD 0) := rfl
end arms

grind_pattern [ind_grind] oraW_step => oraW p (n + 1) m vis q
grind_pattern [ind_grind] oraK1_some => oraK1 p n vis q nm (some (r1, m1))
grind_pattern [ind_grind] oraK2_some => oraK2 p n vis q nm c (some (r2, m2))
grind_pattern [ind_grind] oraK3_some => oraK3 p n vis q nm c en (some (r3, m3))
grind_pattern [ind_grind] oraK4_some => oraK4 p n vis q nm c (some (r4, m4))
grind_pattern [ind_grind] oraK5_some => oraK5 p n vis q nm c (some (r5, m5))
grind_pattern [ind_grind] oraK6_some => oraK6 p n q nm (some (r6, m6))
grind_pattern [ind_grind] oraK7_some => oraK7 q (some (r7, m7))

/-- The lookups of `of_reduce_ax_ok`. -/
structure OraProg (p : Prog) : Prop where
  red : RedProg p
  ora : p.lookup "of_reduce_ax_ok" = some ofReduceAxOkL
  oro : p.lookup "of_reduce_op" = some ofReduceOpL
  orp : p.lookup "of_reduce_pin_a" = some ofReducePinAL

set_option maxHeartbeats 1600000 in
theorem ora_specW (h : OraProg p) (n : Nat) (s₀ : St) (vis q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "of_reduce_ax_ok" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ oraW p n s₀.mem vis q = some (r, s'.mem); ⊤⦄ := by
  sorry

end model

/-- **`of_reduce_ax_ok(vis, q)` refines `ofReduceAxOk`** (through the ROM stubs). -/
@[refines ConRon.Arena.ofReduceAxOk]
theorem ofReduceAxOk_refines (p : Prog) (h : OraProg p) (dn : NIdx → Option ConLeche.Name)
    (hdn : DnInj dn) (vis : Word) (fe : IFEnv) (q : Word) (cv : IConstantVal) :
    RefAM p "of_reduce_ax_ok" [vis, q]
      (fun m a => StageR vis fe m a ∧ decCV (erecP m) q.toNat = some cv)
      (ofReduceAxOk fe cv) (KeepPost vis fe decW0B) := by
  sorry

end L.Arena
