module

public import ConAgua.Arena.NeedsRef2
public import ConAgua.Arena.DeclNatSpec
import ConAgua.Arena.DeclNatDeps
import ConAgua.Arena.StubNamesRefine
import ConAgua.Arena.RecLayout.CIDec
import ConAgua.Arena.RecLayout.CapsDec
import all ConAgua.Arena.Needs

@[expose] public section

/-!
# What a record reads, in L: the refinements, part 3 (lane compare, helper H1)

A pinned constant's fast-path names (`pin_footprint_reduce`, `pin_footprint_nat`, `pin_footprint`)
and a constant's laws (`needs_const`) against the twin's `pinFootprintReduce`, `pinFootprintNat`,
`pinFootprint`, `NeedsSt.const`. The twin returns the footprint as a list that `NeedsSt.const`
appends (`x.names fp`); L pushes it as it goes, so a refinement here says the stack grew by the
twin's list. `pin_footprint_nat` calls `nat_op_deps`, which allocates in the work pool `IW`: these
functions write `ndAW`, `ndCW` (the walk's state and the pool).
-/

open ConRon.Arena
open Std.WP

namespace L.Arena

open L.Ind L.Stubs

/-- The arrays a constant's walk writes: the walk's and the work pool. -/
def ndAW : List TieredArray := [NDM, NACC, IW]

/-- The control words a constant's walk writes: the walk's and the work pool's top. -/
def ndCW : List Word := [220, 221, NTOPC, 200]

/-- The functions `nat_op_deps` reaches. -/
def ndDepFns : List FnName :=
  ["nat_op_deps", "nat_op_pins", "nat_op_pins_a", "nat_op_pins_b", "nat_op_pins_c", "pin_at",
   "iw_alloc"]

/-- **What the footprint's refinements need of a program**: the walk's, the gate's (`nat_op_deps`'
refinement), and `nat_op_deps`' write set (decided on the concrete program). -/
structure NeedsFpProg (p : Prog) : Prop extends NeedsProg p where
  nat : NatGateProg p
  closedDeps : closedA p [IW] [200] ndDepFns = true

theorem ndFrame_w {m m' : Mem} (hf : MemFrame ndA ndC m m') : MemFrame ndAW ndCW m m' :=
  hf.mono (by simp [ndA, ndAW]) (by simp [ndC, ndCW])

theorem ndBeq {k : IdxKind} {x y : Word} (hx : HW x) (hy : HW y) :
    ((decI x : Idx k) == decI y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · have : (decI x : Idx k) ≠ decI y := fun e => h (decI_inj hx hy e)
    simp [h, this]

section steps
variable {p : Prog} (P : NeedsProg p) {vis : Word} {fe : IFEnv} {a : AState}
include P

/-- A `pin_at(k)` call on a filled table: the memory kept, the pin's word. -/
theorem pinCallF {n : Nat} {m m' : Mem} {k : Word} {r : List Word}
    (hc : callW p n "pin_at" [k] m = some (r, m')) (hS : StageR vis fe m a)
    (hF : PinsFull m a.pins) (hk : k.toNat < 51) :
    m = m' ∧ r.headD 0 = pinW m (1 + k.toNat) := by
  obtain ⟨hm, hw, hrun⟩ := pinCall P hc hS
  rw [pinAt_run hF _ hk] at hrun
  have := (Except.ok.inj hrun)
  exact ⟨hm, decI_inj hw (hF.names_lt _ hk) (Prod.mk.inj this).1.symm⟩

/-- **`pin_footprint_reduce(n)` refines `pinFootprintReduce`**: the element type of a
compiler-trust operation pushed (the twin appends it to `xs`). -/
@[refines ConRon.Arena.pinFootprintReduce]
theorem pinFootprintReduce_ref {n : Nat} {m m' : Mem} {w : Word} {r : List Word} {x : NeedsSt}
    (hc : callW p n "pin_footprint_reduce" [w] m = some (r, m')) (hS : StageR vis fe m a)
    (hx : NdR m x) (hF : PinsFull m a.pins) (hw : HW w) (xs : List NIdx) :
    ∃ ys, (pinFootprintReduce (decI w) xs).run a = .ok (xs ++ ys, a) ∧
      NdR m' ⟨x.seen, x.acc ++ ys⟩ ∧ MemFrame ndA ndC m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pinFootprintReduce_specW p P.pfr n _ w) hc
  have lt := hF.names_lt
  rcases n with _ | n
  · rw [pinFootprintReduceW.eq_1] at hW; cases hW
  rw [pinFootprintReduceW.arm1] at hW
  replace hW := opt_some hW (pinFootprintReduceW.k_pin_at.none _ _ _)
  obtain ⟨⟨r1, m1⟩, c1, hW⟩ := hW
  rw [pinFootprintReduceW.k_pin_at.arm1] at hW
  obtain ⟨rfl, e1⟩ := pinCallF P c1 hS hF (by decide)
  replace hW := opt_some hW (pinFootprintReduceW.k_pin_at_2.none _ _ _ _)
  obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
  obtain ⟨rfl, e2⟩ := pinCallF P c2 hS hF (by decide)
  simp only [UInt64.reduceToNat, Nat.reduceAdd] at e1 e2
  have hops : reduceOpNames.run a = .ok ([decI (pinW m 44), decI (pinW m 45)], a) := by
    simp [reduceOpNames, reduceNatName, reduceBoolName, pinReduceNat, pinReduceBool,
      PIN_REDUCE_NAT, PIN_REDUCE_BOOL, StateT.run_bind, pinAt_run hF, except_ok_bind] <;> rfl
  have i44 : (decI w : NIdx) = decI (pinW m 44) ↔ w = pinW m 44 :=
    decI_inj_iff hw (lt 43 (by decide))
  have i45 : (decI w : NIdx) = decI (pinW m 45) ↔ w = pinW m 45 :=
    decI_inj_iff hw (lt 44 (by decide))
  by_cases hin : w = r1.headD 0 ∨ w = r2.headD 0
  · rw [pinFootprintReduceW.k_pin_at_2.arm1 _ _ _ _ _ _ hin] at hW
    replace hW := opt_some hW (pinFootprintReduceW.k_pin_at_3.none _ _ _)
    obtain ⟨⟨r3, m3⟩, c3, hW⟩ := hW
    obtain ⟨rfl, e3⟩ := pinCallF P c3 hS hF (by decide)
    simp only [UInt64.reduceToNat, Nat.reduceAdd] at e3
    by_cases hn : w = r3.headD 0
    · rw [pinFootprintReduceW.k_pin_at_3.arm1 _ _ _ _ _ hn] at hW
      replace hW := opt_some hW (pinFootprintReduceW.k_pin_at_4.none _ _)
      obtain ⟨⟨r4, m4⟩, c4, hW⟩ := hW
      obtain ⟨rfl, e4⟩ := pinCallF P c4 hS hF (by decide)
      rw [pinFootprintReduceW.k_pin_at_4.arm1, pinFootprintReduceW.j2.arm1] at hW
      replace hW := opt_some hW (pinFootprintReduceW.k_needs_name.none _)
      obtain ⟨⟨r5, m5⟩, c5, hW⟩ := hW
      rw [pinFootprintReduceW.k_needs_name.arm1, pinFootprintReduceW.j1.arm1] at hW
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      simp only [UInt64.reduceToNat, Nat.reduceAdd] at e4
      rw [e4] at c5
      obtain ⟨hy, f5⟩ := needsName_step P c5 hx (lt 1 (by decide))
      refine ⟨[decI (pinW m 2)], ?_, hy, f5⟩
      rw [e3] at hn
      simp [pinFootprintReduce, reduceElemName, reduceNatName, pinReduceNat, pinNat, PIN_NAT,
        PIN_REDUCE_NAT, StateT.run_bind, hops, pinAt_run hF, except_ok_bind, hn]
      rfl
    · rw [pinFootprintReduceW.k_pin_at_3.arm2 _ _ _ _ _ hn] at hW
      replace hW := opt_some hW (pinFootprintReduceW.k_pin_at_4.none _ _)
      obtain ⟨⟨r4, m4⟩, c4, hW⟩ := hW
      obtain ⟨rfl, e4⟩ := pinCallF P c4 hS hF (by decide)
      rw [pinFootprintReduceW.k_pin_at_4.arm1, pinFootprintReduceW.j2.arm1] at hW
      replace hW := opt_some hW (pinFootprintReduceW.k_needs_name.none _)
      obtain ⟨⟨r5, m5⟩, c5, hW⟩ := hW
      rw [pinFootprintReduceW.k_needs_name.arm1, pinFootprintReduceW.j1.arm1] at hW
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      simp only [UInt64.reduceToNat, Nat.reduceAdd] at e4
      rw [e4] at c5
      obtain ⟨hy, f5⟩ := needsName_step P c5 hx (lt 29 (by decide))
      refine ⟨[decI (pinW m 30)], ?_, hy, f5⟩
      rw [e3] at hn
      have h45 : w = pinW m 45 := by rw [e1, e2] at hin; exact hin.resolve_left hn
      have nn : ¬ (decI (pinW m 45) : NIdx) = decI (pinW m 44) := fun e =>
        hn (h45.trans (decI_inj (lt 44 (by decide)) (lt 43 (by decide)) e))
      simp [pinFootprintReduce, reduceElemName, reduceNatName, pinReduceNat, boolName, pinBool,
        PIN_BOOL, PIN_REDUCE_NAT, StateT.run_bind, hops, pinAt_run hF, except_ok_bind,
        h45, nn]
      rfl
  · rw [pinFootprintReduceW.k_pin_at_2.arm2 _ _ _ _ _ _ hin, pinFootprintReduceW.j1.arm1] at hW
    obtain ⟨-, e⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [← e]
    refine ⟨[], ?_, by simpa using hx, MemFrame.refl _ _ _⟩
    rw [e1, e2] at hin
    simp [pinFootprintReduce, StateT.run_bind, hops, except_ok_bind, i44, i45, hin]
    rfl

end steps

end L.Arena
