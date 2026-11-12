module

import ConAgua.Arena.DefEqStuckCert
import ConAgua.Arena.DefEqStuckShape
import ConAgua.Arena.IndView
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreProj
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.DefEqStuck

@[expose] public section

/-!
# `struct_unit_cert` refines `structUnitCert` (lane `defeq`, helper `defeq-top`)

In L's pieces: `struct_unit_cert` (`a`'s type, its unit-likeness by `unit_like_loop`) and
`struct_unit_tail` (`b`'s type against it). One refinement per piece for both outcomes (`RefE`
over its unified model, `Verdict/WhnfModels7E.lean`): the errors are the knot's slots'.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin in L's pieces -/

/-- `structUnitCert` once `a`'s type `wta` is unit-like, copied. -/
def suTailT (r : CoreFnsA) (depth : Nat) (b wta : EIdx) : AM Bool := do
  let tb ← r.inferIO depth b
  let wtb ← r.whnf depth tb
  let gb ← if isForallE wtb then ioNeutral b else pure true
  if !gb then pure false
  else r.defeq depth wta wtb

/-- **`struct_unit_tail` refines `suTailT`, both outcomes**: the errors are the `infer_io`, `whnf`
and `defeq` slots'. -/
@[refines_part ConRon.Arena.structUnitCert "b's type against a's (suTailT)"]
theorem sut_ref (p : Prog) (n : Nat) (hk : KnotUpTo p n) (F : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d b wta : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hwta : HW wta) :
    RefE (KnotUpToE p n) (sutE p (n + 1) s₀.mem mode vis d b wta)
      (suTailT (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE b) (decE wta)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  sorry

/-! ## `struct_unit_cert` -/

/-- **`struct_unit_cert` refines `structUnitCert`, both outcomes**: the errors are the `infer_io`,
`whnf` slots' and `struct_unit_head`'s. -/
theorem suc_ref (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (KnotUpToE p n) (sucE p (n + 1) s₀.mem mode vis d a b)
      (structUnitCert (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  sorry

/-- **`struct_unit_cert` refines `structUnitCert`** at the knot (`suc_ref`'s ok half). -/
@[refines ConRon.Arena.structUnitCert]
theorem suCert_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "struct_unit_cert" [mode, vis, d, a, b]
      (structUnitCert (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
      s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (sucE_spec p hq.toCertProg (n + 1) s₀ mode vis d a b)
    (suc_ref p hq hc n hk F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb)

end L.Arena
