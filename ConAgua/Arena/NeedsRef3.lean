module

public import ConAgua.Arena.NeedsRef2
public import ConAgua.Arena.DeclNatDeps
import ConAgua.Arena.CoreErec
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


/-- `pin_footprint_nat`'s tail at a nonzero flag: `Bool` and its constructors pushed. -/
theorem pfnTail {n : Nat} {mm m' : Mem} {r' : Word} {r : List Word} {x : NeedsSt}
    (hj : pinFootprintNatW.j1 p n r' mm = some (r, m')) (hr : r' ≠ 0) (hS : StageR vis fe mm a)
    (hx : NdR mm x) (hF : PinsFull mm a.pins) :
    NdR m' ⟨x.seen, x.acc ++ [decI (pinW mm 30), decI (pinW mm 31), decI (pinW mm 32)]⟩ ∧
      MemFrame ndA ndC mm m' := by
  have lt := hF.names_lt
  rw [pinFootprintNatW.j1.arm1 _ _ _ _ hr] at hj
  replace hj := opt_some hj (pinFootprintNatW.k_pin_at_13.none ..)
  obtain ⟨⟨q1, m1⟩, d1, hj⟩ := hj
  rw [pinFootprintNatW.k_pin_at_13.arm1] at hj
  obtain ⟨rfl, v1⟩ := pinCallF P d1 hS hF (by decide)
  replace hj := opt_some hj (pinFootprintNatW.k_pin_at_14.none ..)
  obtain ⟨⟨q2, m2⟩, d2, hj⟩ := hj
  rw [pinFootprintNatW.k_pin_at_14.arm1] at hj
  obtain ⟨rfl, v2⟩ := pinCallF P d2 hS hF (by decide)
  replace hj := opt_some hj (pinFootprintNatW.k_pin_at_15.none ..)
  obtain ⟨⟨q3, m3⟩, d3, hj⟩ := hj
  rw [pinFootprintNatW.k_pin_at_15.arm1] at hj
  obtain ⟨rfl, v3⟩ := pinCallF P d3 hS hF (by decide)
  simp only [UInt64.reduceToNat, Nat.reduceAdd] at v1 v2 v3
  replace hj := opt_some hj (pinFootprintNatW.k_needs_name_4.none ..)
  obtain ⟨⟨q4, m4⟩, d4, hj⟩ := hj
  rw [pinFootprintNatW.k_needs_name_4.arm1] at hj
  rw [v1] at d4
  obtain ⟨hx4, f4⟩ := needsName_step P d4 hx (lt 29 (by decide))
  replace hj := opt_some hj (pinFootprintNatW.k_needs_name_5.none ..)
  obtain ⟨⟨q5, m5⟩, d5, hj⟩ := hj
  rw [pinFootprintNatW.k_needs_name_5.arm1] at hj
  rw [v2] at d5
  obtain ⟨hx5, f5⟩ := needsName_step P d5 hx4 (lt 30 (by decide))
  replace hj := opt_some hj (pinFootprintNatW.k_needs_name_6.none ..)
  obtain ⟨⟨q6, m6⟩, d6, hj⟩ := hj
  rw [pinFootprintNatW.k_needs_name_6.arm1, pinFootprintNatW.j2.arm1] at hj
  rw [v3] at d6
  obtain ⟨hx6, f6⟩ := needsName_step P d6 hx5 (lt 31 (by decide))
  obtain ⟨-, e⟩ := Prod.mk.inj (Option.some.inj hj)
  rw [← e]
  exact ⟨by simpa [NeedsSt.name] using hx6, f4.trans (f5.trans f6)⟩

omit P in
/-- `pin_footprint_nat`'s tail at a zero flag: nothing more. -/
theorem pfnTail0 {n : Nat} {mm m' : Mem} {r : List Word}
    (hj : pinFootprintNatW.j1 p n 0 mm = some (r, m')) : m' = mm := by
  rw [pinFootprintNatW.j1.arm2 _ _ _ _ rfl, pinFootprintNatW.j2.arm1] at hj
  exact (Prod.mk.inj (Option.some.inj hj)).2.symm

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


/-- The div/mod names on a filled table (`natDivModNames`' list). -/
abbrev dmsL (m : Mem) : List NIdx :=
  [decI (pinW m 22), decI (pinW m 23), decI (pinW m 24), decI (pinW m 25), decI (pinW m 26),
   decI (pinW m 27), decI (pinW m 28), decI (pinW m 29)]

theorem ndPinW_frame {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (PINS : TieredArray) ∉ A) (i : Nat) : pinW m' i = pinW m i := by
  simp only [pinW]; rw [hf.arr _ hA (by decide)]

theorem PinsFull.frame {A : List TieredArray} {C : List Word} {m m' : Mem} {ps : Pins}
    (hf : MemFrame A C m m') (hA : (PINS : TieredArray) ∉ A) (h : PinsFull m ps) : PinsFull m' ps :=
  PinsFull.congr (hf.arr _ hA (by decide)) h


/-- The twin's `pinFootprintNat` on a filled table. -/
theorem pinFootprintNat_run {m : Mem} {a : AState} {w : Word} (hF : PinsFull m a.pins) (hw : HW w) :
    (pinFootprintNat (decI w) (dmsL m)).run a = .ok (
      (if w = pinW m 20 ∨ w = pinW m 21 ∨ (dmsL m).contains (decI w) = true then
        (depsW m w).map decI ++ [decI (pinW m 2), decI (pinW m 3), decI (pinW m 4)] ++
          [decI (pinW m 30), decI (pinW m 31), decI (pinW m 32)]
       else (depsW m w).map decI ++ [decI (pinW m 2), decI (pinW m 3), decI (pinW m 4)]), a) := by
  have lt := hF.names_lt
  have b20 : ((decI w : NIdx) == decI (pinW m 20)) = decide (w = pinW m 20) :=
    ndBeq hw (lt 19 (by decide))
  have b21 : ((decI w : NIdx) == decI (pinW m 21)) = decide (w = pinW m 21) :=
    ndBeq hw (lt 20 (by decide))
  simp only [pinFootprintNat, StateT.run_bind, natOpDeps_run hF hw, except_ok_bind,
    litGuardNames_run hF, natBeqName, natBleName, pinNatBeq, pinNatBle, PIN_NAT_BEQ, PIN_NAT_BLE,
    boolName, boolTrueName, boolFalseName, pinBool, pinBoolTrue, pinBoolFalse, PIN_BOOL,
    PIN_BOOL_TRUE, PIN_BOOL_FALSE, nidxAppend]
  have p19 := pinAt_run hF 19 (by decide)
  have p20 := pinAt_run hF 20 (by decide)
  have p29 := pinAt_run hF 29 (by decide)
  have p30 := pinAt_run hF 30 (by decide)
  have p31 := pinAt_run hF 31 (by decide)
  simp only [Nat.reduceAdd] at p19 p20 p29 p30 p31
  simp only [p19, p20, except_ok_bind, b20, b21, Nat.sub_zero, List.drop_zero]
  by_cases hc : w = pinW m 20 ∨ w = pinW m 21 ∨ (dmsL m).contains (decI w) = true
  · have hb : (decide (w = pinW m 20) || decide (w = pinW m 21) || (dmsL m).contains (decI w)) =
        true := by
      rcases hc with h | h | h
      · simp [h]
      · simp [h]
      · rw [h]; simp
    simp only [eq_true hc, ite_true]
    simp only [hb, ite_true, StateT.run_bind, p29, p30, p31, except_ok_bind]
    simp; rfl
  · have hb : (decide (w = pinW m 20) || decide (w = pinW m 21) || (dmsL m).contains (decI w)) =
        false := by
      simp only [not_or] at hc
      have h3 : (dmsL m).contains (decI w) = false := by simpa using hc.2.2
      rw [h3]; simp [hc.1, hc.2.1]
    simp only [eq_false hc, ite_false]
    simp only [hb, Bool.false_eq_true, ite_false]
    simp; rfl

section fp
variable {p : Prog} (P : NeedsFpProg p) {vis : Word} {fe : IFEnv} {a : AState}
include P

/-- **`pin_footprint_nat(n)` refines `pinFootprintNat`** (with the twin's `natDivModNames`): the
operation's dependencies, the `Nat` basis, and `Bool` for the comparisons and the division,
pushed. -/
@[refines ConRon.Arena.pinFootprintNat]
theorem pinFootprintNat_ref {n : Nat} {m m' : Mem} {w : Word} {r : List Word} {x : NeedsSt}
    (hc : callW p n "pin_footprint_nat" [w] m = some (r, m')) (hS : StageR vis fe m a)
    (hx : NdR m x) (hF : PinsFull m a.pins) (hw : HW w) :
    ∃ xs, (pinFootprintNat (decI w) (dmsL m)).run a = .ok (xs, a) ∧
      NdR m' ⟨x.seen, x.acc ++ xs⟩ ∧ StageR vis fe m' a ∧ IWGrow m m' ∧ MemFrame ndAW ndCW m m' := by
  have Q := P.toNeedsProg
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pinFootprintNat_specW p Q.pfn n _ w) hc
  have lt := hF.names_lt
  rcases n with _ | n
  · rw [pinFootprintNatW.eq_1] at hW; cases hW
  rw [pinFootprintNatW.arm1] at hW
  replace hW := opt_some hW (pinFootprintNatW.k_nat_op_deps.none _ _ _)
  obtain ⟨⟨r1, m1⟩, c1, hW⟩ := hW
  rw [pinFootprintNatW.k_nat_op_deps.arm1] at hW
  obtain ⟨deps, a1, hd, hS1, hg1, hdec⟩ := natOpDeps_ref (vis := vis) (fe := fe) P.nat w n m a r1 m1
    ⟨hS, hw⟩ c1
  rw [natOpDeps_run hF hw] at hd
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hd)
  have hf1 : MemFrame [IW] [200] m m1 :=
    (run_memFrame P.closedDeps (f := "nat_op_deps") (by decide) (run_of_callW c1)).1
  have hx1 := NdR.frame hf1 (by decide) (by decide) hx
  have hF1 := hF.frame hf1 (by decide)
  have hp1 := ndPinW_frame hf1 (by decide)
  replace hW := opt_some hW (pinFootprintNatW.k_pin_at.none ..)
  obtain ⟨⟨q1, n1⟩, d1, hW⟩ := hW
  rw [pinFootprintNatW.k_pin_at.arm1] at hW
  obtain ⟨rfl, v1⟩ := pinCallF Q d1 hS1 hF1 (by decide)
  replace hW := opt_some hW (pinFootprintNatW.k_pin_at_2.none ..)
  obtain ⟨⟨q2, n2⟩, d2, hW⟩ := hW
  rw [pinFootprintNatW.k_pin_at_2.arm1] at hW
  obtain ⟨rfl, v2⟩ := pinCallF Q d2 hS1 hF1 (by decide)
  replace hW := opt_some hW (pinFootprintNatW.k_pin_at_3.none ..)
  obtain ⟨⟨q3, n3⟩, d3, hW⟩ := hW
  rw [pinFootprintNatW.k_pin_at_3.arm1] at hW
  obtain ⟨rfl, v3⟩ := pinCallF Q d3 hS1 hF1 (by decide)
  replace hW := opt_some hW (pinFootprintNatW.k_pin_at_4.none ..)
  obtain ⟨⟨q4, n4⟩, d4, hW⟩ := hW
  rw [pinFootprintNatW.k_pin_at_4.arm1] at hW
  obtain ⟨rfl, v4⟩ := pinCallF Q d4 hS1 hF1 (by decide)
  replace hW := opt_some hW (pinFootprintNatW.k_pin_at_5.none ..)
  obtain ⟨⟨q5, n5⟩, d5, hW⟩ := hW
  rw [pinFootprintNatW.k_pin_at_5.arm1] at hW
  obtain ⟨rfl, v5⟩ := pinCallF Q d5 hS1 hF1 (by decide)
  replace hW := opt_some hW (pinFootprintNatW.k_pin_at_6.none ..)
  obtain ⟨⟨q6, n6⟩, d6, hW⟩ := hW
  rw [pinFootprintNatW.k_pin_at_6.arm1] at hW
  obtain ⟨rfl, v6⟩ := pinCallF Q d6 hS1 hF1 (by decide)
  replace hW := opt_some hW (pinFootprintNatW.k_pin_at_7.none ..)
  obtain ⟨⟨q7, n7⟩, d7, hW⟩ := hW
  rw [pinFootprintNatW.k_pin_at_7.arm1] at hW
  obtain ⟨rfl, v7⟩ := pinCallF Q d7 hS1 hF1 (by decide)
  replace hW := opt_some hW (pinFootprintNatW.k_pin_at_8.none ..)
  obtain ⟨⟨q8, n8⟩, d8, hW⟩ := hW
  rw [pinFootprintNatW.k_pin_at_8.arm1] at hW
  obtain ⟨rfl, v8⟩ := pinCallF Q d8 hS1 hF1 (by decide)
  replace hW := opt_some hW (pinFootprintNatW.k_pin_at_9.none ..)
  obtain ⟨⟨q9, n9⟩, d9, hW⟩ := hW
  rw [pinFootprintNatW.k_pin_at_9.arm1] at hW
  obtain ⟨rfl, v9⟩ := pinCallF Q d9 hS1 hF1 (by decide)
  replace hW := opt_some hW (pinFootprintNatW.k_pin_at_10.none ..)
  obtain ⟨⟨q10, n10⟩, d10, hW⟩ := hW
  rw [pinFootprintNatW.k_pin_at_10.arm1] at hW
  obtain ⟨rfl, v10⟩ := pinCallF Q d10 hS1 hF1 (by decide)
  simp only [UInt64.reduceToNat, Nat.reduceAdd, hp1] at v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  replace hW := opt_some hW (pinFootprintNatW.k_needs_names_iw.none ..)
  obtain ⟨⟨q11, n11⟩, d11, hW⟩ := hW
  rw [pinFootprintNatW.k_needs_names_iw.arm1] at hW
  have hns : hslice? (iwA m1) (r1.headD 0).toNat (r1.tail.headD 0).toNat =
      some (((depsW m w).map decI : List NIdx)) := by
    have g0 : r1.getD 0 0 = r1.headD 0 := by cases r1 <;> rfl
    have := hdec.1; simp only [decHL, g0, Nat.zero_add, L.getD_one] at this
    exact this
  obtain ⟨hx11, f11⟩ := needsNamesIw_step Q d11 hx1 hS1.iw.iwSize hns
  have hS11 := (hS1.ndFrame f11).1
  have hF11 := hF1.frame f11 (by decide)
  replace hW := opt_some hW (pinFootprintNatW.k_needs_name.none ..)
  obtain ⟨⟨q12, n12⟩, d12, hW⟩ := hW
  rw [pinFootprintNatW.k_needs_name.arm1] at hW
  rw [v1] at d12
  obtain ⟨hx12, f12⟩ := needsName_step Q d12 hx11 (lt 1 (by decide))
  replace hW := opt_some hW (pinFootprintNatW.k_needs_name_2.none ..)
  obtain ⟨⟨q13, n13⟩, d13, hW⟩ := hW
  rw [pinFootprintNatW.k_needs_name_2.arm1] at hW
  rw [v2] at d13
  obtain ⟨hx13, f13⟩ := needsName_step Q d13 hx12 (lt 2 (by decide))
  replace hW := opt_some hW (pinFootprintNatW.k_needs_name_3.none ..)
  obtain ⟨⟨q14, n14⟩, d14, hW⟩ := hW
  rw [pinFootprintNatW.k_needs_name_3.arm1] at hW
  rw [v3] at d14
  obtain ⟨hx14, f14⟩ := needsName_step Q d14 hx13 (lt 3 (by decide))
  have f3 := f12.trans (f13.trans f14)
  have hS14 := (hS11.ndFrame f3).1
  have hF14 := hF11.frame f3 (by decide)
  have hp14 : ∀ i, pinW n14 i = pinW m i := fun i => by
    rw [ndPinW_frame f3 (by decide), ndPinW_frame f11 (by decide), hp1]
  replace hW := opt_some hW (pinFootprintNatW.k_pin_at_11.none ..)
  obtain ⟨⟨q15, n15⟩, d15, hW⟩ := hW
  rw [pinFootprintNatW.k_pin_at_11.arm1] at hW
  obtain ⟨rfl, v15⟩ := pinCallF Q d15 hS14 hF14 (by decide)
  replace hW := opt_some hW (pinFootprintNatW.k_pin_at_12.none ..)
  obtain ⟨⟨q16, n16⟩, d16, hW⟩ := hW
  obtain ⟨rfl, v16⟩ := pinCallF Q d16 hS14 hF14 (by decide)
  simp only [UInt64.reduceToNat, Nat.reduceAdd, hp14] at v15 v16
  have hfa : MemFrame ndA ndC m1 n14 := f11.trans f3
  have hxs : NdR n14 ⟨x.seen, x.acc ++ ((depsW m w).map decI ++
      [decI (pinW m 2), decI (pinW m 3), decI (pinW m 4)])⟩ := by
    have tk : List.take (depsW m w).length ((depsW m w).map decI : List NIdx) =
        (depsW m w).map decI := List.take_of_length_le (by simp)
    simpa [NeedsSt.name, nidxAppend, List.append_assoc, tk] using hx14
  have hfin : ∀ {mf : Mem}, MemFrame ndA ndC n14 mf →
      StageR vis fe mf a ∧ IWGrow m mf ∧ MemFrame ndAW ndCW m mf := fun {mf} hf => by
    have ht := hfa.trans hf
    exact ⟨(hS1.ndFrame ht).1, hg1.trans (hS1.ndFrame ht).2,
      (hf1.mono (by simp [ndAW]) (by simp [ndCW])).trans (ndFrame_w ht)⟩
  have hrun := pinFootprintNat_run (a := a) hF hw
  have hdms := natDms_contains hF hw
  by_cases hne : w ≠ q15.headD 0 ∧ w ≠ q16.headD 0
  · rw [pinFootprintNatW.k_pin_at_12.arm1 _ _ _ _ _ _ hne] at hW
    replace hW := opt_some hW (pinFootprintNatW.k_pin_range_has.none ..)
    obtain ⟨⟨q17, m17⟩, d17, hW⟩ := hW
    rw [pinFootprintNatW.k_pin_range_has.arm1] at hW
    obtain ⟨s17, rfl, -, hW17⟩ := triple_of_callW (s₀ := ⟨n14, Locals.init []⟩)
      (prh_spec p Q.pin_range_has Q.pin_at n _ w 21 29) d17
    obtain ⟨e17, -, hi17⟩ := prhW_iff n _ _ w 21 29 _ (by decide) hW17
    simp only [UInt64.reduceToNat, hp14] at hi17
    rw [v15, v16] at hne
    by_cases hr0 : q17.headD 0 = 0
    · rw [hr0] at hW
      have em := pfnTail0 hW
      rw [← e17] at em
      have hc : ¬ (w = pinW m 20 ∨ w = pinW m 21 ∨ (dmsL m).contains (decI w) = true) := by
        rintro (h | h | h)
        · exact hne.1 h
        · exact hne.2 h
        · exact (hi17.mpr (hdms.mp h)) hr0
      simp only [eq_false hc, ite_false] at hrun
      obtain ⟨hS', hg', hf'⟩ := hfin (MemFrame.refl ndA ndC n14)
      rw [em]
      exact ⟨_, hrun, hxs, hS', hg', hf'⟩
    · rw [← e17] at hW
      obtain ⟨hy, ft⟩ := pfnTail Q hW hr0 hS14 hxs hF14
      have hc : w = pinW m 20 ∨ w = pinW m 21 ∨ (dmsL m).contains (decI w) = true :=
        .inr (.inr (hdms.mpr (hi17.mp hr0)))
      simp only [eq_true hc, ite_true] at hrun
      obtain ⟨hS', hg', hf'⟩ := hfin ft
      refine ⟨_, hrun, ?_, hS', hg', hf'⟩
      simpa [hp14, List.append_assoc] using hy
  · rw [pinFootprintNatW.k_pin_at_12.arm2 _ _ _ _ _ _ hne] at hW
    obtain ⟨hy, ft⟩ := pfnTail Q hW (by decide) hS14 hxs hF14
    rw [v15, v16] at hne
    have hc : w = pinW m 20 ∨ w = pinW m 21 ∨ (dmsL m).contains (decI w) = true := by
      rcases Classical.em (w = pinW m 20) with h | h
      · exact .inl h
      · exact .inr (.inl (Classical.not_not.mp fun h' => hne ⟨h, h'⟩))
    simp only [eq_true hc, ite_true] at hrun
    obtain ⟨hS', hg', hf'⟩ := hfin ft
    refine ⟨_, hrun, ?_, hS', hg', hf'⟩
    simpa [hp14, List.append_assoc] using hy


/-- **`pin_footprint(n)` refines `pinFootprint`**: the twin's footprint list pushed. -/
@[refines ConRon.Arena.pinFootprint]
theorem pinFootprint_ref {n : Nat} {m m' : Mem} {w : Word} {r : List Word} {x : NeedsSt}
    (hc : callW p n "pin_footprint" [w] m = some (r, m')) (hS : StageR vis fe m a)
    (hx : NdR m x) (hw : HW w) :
    ∃ fp, (pinFootprint (decI w)).run a = .ok (fp, a) ∧ NdR m' ⟨x.seen, x.acc ++ fp⟩ ∧
      StageR vis fe m' a ∧ IWGrow m m' ∧ MemFrame ndAW ndCW m m' := by
  have Q := P.toNeedsProg
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pinFootprint_specW p Q.pf n _ w) hc
  rcases n with _ | n
  · rw [pinFootprintW.eq_1] at hW; cases hW
  rw [pinFootprintW.arm1] at hW
  replace hW := opt_some hW (pinFootprintW.k_nat_op_name.none ..)
  obtain ⟨⟨r1, m1⟩, c1, hW⟩ := hW
  obtain ⟨s1, rfl, -, hn⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (non_spec p Q.nat_op_name Q.pin_range_has Q.pin_at n _ w) c1
  obtain ⟨e1, -, hi⟩ := nonW_iff hn
  have hF := hS.check.pins.full (nonW_flag hn)
  dsimp only at e1 hi
  rw [← e1] at hW
  have hops := natOps_contains hF hw
  have hdms := natDms_contains hF hw
  have hnames : (pinFootprint (decI w)).run a = (if
      ([(decI (pinW m 15) : NIdx), decI (pinW m 16), decI (pinW m 17), decI (pinW m 18),
        decI (pinW m 19), decI (pinW m 20), decI (pinW m 21)].contains (decI w) ||
       (dmsL m).contains (decI w)) = true then
      (do let xs ← pinFootprintNat (decI w) (dmsL m); pinFootprintReduce (decI w) xs)
      else pinFootprintReduce (decI w) []).run a := by
    simp only [pinFootprint, StateT.run_bind, natOpNames_run hF, natDivModNames_run hF,
      except_ok_bind]
  by_cases h0 : r1.headD 0 ≠ 0
  · rw [pinFootprintW.k_nat_op_name.arm1 _ _ _ _ _ h0] at hW
    replace hW := opt_some hW (pinFootprintW.k_pin_footprint_nat.none ..)
    obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
    rw [pinFootprintW.k_pin_footprint_nat.arm1, pinFootprintW.j1.arm1] at hW
    obtain ⟨xs, ex, hx2, hS2, hg2, hf2⟩ := pinFootprintNat_ref P c2 hS hx hF hw
    replace hW := opt_some hW (pinFootprintW.k_pin_footprint_reduce.none ..)
    obtain ⟨⟨r3, m3⟩, c3, hW⟩ := hW
    rw [pinFootprintW.k_pin_footprint_reduce.arm1] at hW
    obtain ⟨-, e⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [← e]
    have hF2 : PinsFull m2 a.pins := hF.frame hf2 (by decide)
    obtain ⟨ys, ey, hy, f3⟩ := pinFootprintReduce_ref Q c3 hS2 hx2 hF2 hw xs
    obtain ⟨i, h1, h2, h3⟩ := hi.mp h0
    have hc : ([(decI (pinW m 15) : NIdx), decI (pinW m 16), decI (pinW m 17), decI (pinW m 18),
        decI (pinW m 19), decI (pinW m 20), decI (pinW m 21)].contains (decI w) ||
       (dmsL m).contains (decI w)) = true := by
      rcases Nat.lt_or_ge i 21 with hl | hl
      · rw [hops.mpr ⟨i, h1, hl, h3⟩]; rfl
      · rw [hdms.mpr ⟨i, hl, h2, h3⟩]; simp
    refine ⟨xs ++ ys, ?_, by simpa [List.append_assoc] using hy, (hS2.ndFrame f3).1,
      hg2.trans (hS2.ndFrame f3).2, hf2.trans (ndFrame_w f3)⟩
    rw [hnames]; simp only [hc, ite_true]
    rw [StateT.run_bind, ex, except_ok_bind]
    exact ey
  · have h0' : r1.headD 0 = 0 := Classical.not_not.mp h0
    rw [pinFootprintW.k_nat_op_name.arm2 _ _ _ _ _ h0', pinFootprintW.j1.arm1] at hW
    replace hW := opt_some hW (pinFootprintW.k_pin_footprint_reduce.none ..)
    obtain ⟨⟨r3, m3⟩, c3, hW⟩ := hW
    rw [pinFootprintW.k_pin_footprint_reduce.arm1] at hW
    obtain ⟨-, e⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [← e]
    obtain ⟨ys, ey, hy, f3⟩ := pinFootprintReduce_ref Q c3 hS hx hF hw []
    have hc : ([(decI (pinW m 15) : NIdx), decI (pinW m 16), decI (pinW m 17), decI (pinW m 18),
        decI (pinW m 19), decI (pinW m 20), decI (pinW m 21)].contains (decI w) ||
       (dmsL m).contains (decI w)) = false := by
      have n1 : ¬ ∃ i, 14 ≤ i ∧ i < 29 ∧ pinW m (1 + i) = w := fun h => h0 (hi.mpr h)
      have a1 : ¬ _ := mt hops.mp (fun ⟨i, h1, h2, h3⟩ => n1 ⟨i, h1, by omega, h3⟩)
      have a2 : ¬ _ := mt hdms.mp (fun ⟨i, h1, h2, h3⟩ => n1 ⟨i, by omega, h2, h3⟩)
      simp only [Bool.not_eq_true] at a1 a2
      rw [a1, a2]; rfl
    refine ⟨ys, ?_, by simpa using hy, (hS.ndFrame f3).1, (hS.ndFrame f3).2, ndFrame_w f3⟩
    rw [hnames]; simp only [hc, Bool.false_eq_true, ite_false]
    simpa using ey


omit P in
theorem ci_name_cv (ci : IConstantInfo) : ci.name = ci.toConstantVal.name := by
  cases ci <;> rfl

/-- **`needs_const(c)` refines `NeedsSt.const`** at the constant record `c` decodes to. -/
@[refines ConRon.Arena.NeedsSt.const]
theorem needsConst_ref {n : Nat} {m m' : Mem} {c : Word} {r : List Word} {x : NeedsSt}
    {ci : IConstantInfo} (hc : callW p n "needs_const" [c] m = some (r, m'))
    (hS : StageR vis fe m a) (hx : NdR m x) (hci : decCI (erecP m) c.toNat = some ci) :
    ∃ y, (x.const ci).run a = .ok (y, a) ∧ NdR m' y ∧ StageR vis fe m' a ∧ IWGrow m m' ∧
      MemFrame ndAW ndCW m m' := by
  have Q := P.toNeedsProg
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (needsConst_specW p Q.const n _ c) hc
  have hR := erRdOK m
  obtain ⟨wn, en, -, -, wt, et⟩ := decCV_rd_ci hR (decCI_cv hci)
  have hsplit := decCI_splitE hci
  have hrec := decCI_rec_rd hR hci
  rcases n with _ | n
  · rw [needsConstW.eq_1] at hW; cases hW
  rw [needsConstW.arm1] at hW
  replace hW := opt_some hW (needsConstW.k_needs_expr.none ..)
  obtain ⟨⟨r1, m1⟩, c1, hW⟩ := hW
  obtain ⟨y1, e1, hy1, hS1, f1⟩ := needsExpr_ref Q c1 hS hx wt
  have e1' : (x.expr ci.toConstantVal.type).run a = .ok (y1, a) := by rw [et]; exact e1
  have hr1 : erRd m1 = erRd m := erRd_nd f1
  -- the kind's arms, then the footprint
  have tail : ∀ (y2 : NeedsSt) (m2 : Mem), NdR m2 y2 → MemFrame ndA ndC m m2 →
      needsConstW.j1 p n c m2 = some (r, s'.mem) →
      ∃ y, (do let fp ← pinFootprint ci.name; pure (y2.names fp) : AM NeedsSt).run a = .ok (y, a) ∧
        NdR s'.mem y ∧ StageR vis fe s'.mem a ∧ IWGrow m s'.mem ∧ MemFrame ndAW ndCW m s'.mem := by
    intro y2 m2 hy2 f2 hj
    rw [needsConstW.j1.arm1, erRd_nd f2] at hj
    replace hj := opt_some hj (needsConstW.k_pin_footprint.none ..)
    obtain ⟨⟨r3, m3⟩, c3, hj⟩ := hj
    rw [needsConstW.k_pin_footprint.arm1] at hj
    obtain ⟨-, e⟩ := Prod.mk.inj (Option.some.inj hj)
    rw [← e]
    obtain ⟨fp, efp, hy3, hS3, hg3, f3⟩ := pinFootprint_ref P c3 (hS.ndFrame f2).1 hy2 wn
    refine ⟨y2.names fp, ?_, by rw [names_eq]; exact hy3, hS3,
      (hS.ndFrame f2).2.trans hg3, (ndFrame_w f2).trans f3⟩
    rw [ci_name_cv, en, StateT.run_bind, efp, except_ok_bind]
    rfl
  by_cases k1 : erRd m c = 1
  · obtain ⟨cv, v, hint, rfl, -, ev, wv⟩ := hsplit.1 k1
    rw [needsConstW.k_needs_expr.arm1 _ _ _ _ _ (by rw [hr1]; exact k1)] at hW
    replace hW := opt_some hW (needsConstW.k_needs_expr_2.none ..)
    obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
    rw [needsConstW.k_needs_expr_2.arm1] at hW
    rw [hr1] at c2
    obtain ⟨y2, e2, hy2, -, f2⟩ := needsExpr_ref Q c2 hS1 hy1 wv
    have e2' : (y1.expr v).run a = .ok (y2, a) := by rw [ev]; exact e2
    obtain ⟨y, ey, rest⟩ := tail y2 m2 hy2 (f1.trans f2) hW
    refine ⟨y, ?_, rest⟩
    simp only [NeedsSt.const, StateT.run_bind, e1', except_ok_bind, e2'] at ey ⊢
    exact ey
  by_cases k5 : erRd m c = 5
  · obtain ⟨cv, rules, rfl, -, hrs⟩ := hrec.1 k5
    rw [needsConstW.k_needs_expr.arm2 _ _ _ _ _ (by rw [hr1]; exact k1)
      (by rw [hr1]; exact k5)] at hW
    replace hW := opt_some hW (needsConstW.k_needs_expr_2.none ..)
    obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
    rw [needsConstW.k_needs_expr_2.arm1] at hW
    rw [hr1] at c2
    rw [← erecP_nd f1] at hrs
    obtain ⟨y2, e2, hy2, -, f2⟩ := needsRules_ref Q c2 hS1 hy1 hrs
    obtain ⟨y, ey, rest⟩ := tail y2 m2 hy2 (f1.trans f2) hW
    refine ⟨y, ?_, rest⟩
    simp only [NeedsSt.const, StateT.run_bind, e1', except_ok_bind, e2] at ey ⊢
    exact ey
  by_cases k3 : erRd m c = 3
  · obtain ⟨cv, caps, rfl, -⟩ := hsplit.2.2.1 k3
    obtain ⟨-, -, -, -, hall, -⟩ := decCI_indInfo_rd hR hci
    rw [needsConstW.k_needs_expr.arm3 _ _ _ _ _ (by rw [hr1]; exact k1)
      (by rw [hr1]; exact k5) (by rw [hr1]; exact k3)] at hW
    replace hW := opt_some hW (needsConstW.k_needs_expr_2.none ..)
    obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
    rw [needsConstW.k_needs_expr_2.arm1] at hW
    rw [hr1, UInt64.add_assoc, show CI.indCaps + Caps.allOff + 1 = CI.indCaps + Caps.allLen from rfl]
      at c2
    rw [← erecP_nd f1] at hall
    obtain ⟨hy2, f2⟩ := needsNames_step Q c2 hy1 hall
    obtain ⟨y, ey, rest⟩ := tail _ m2 hy2 (f1.trans f2) hW
    refine ⟨y, ?_, rest⟩
    simp only [NeedsSt.const, StateT.run_bind, e1', except_ok_bind] at ey ⊢
    exact ey
  · rw [needsConstW.k_needs_expr.arm4 _ _ _ _ _ (by rw [hr1]; exact k1)
      (by rw [hr1]; exact k5) (by rw [hr1]; exact k3)] at hW
    obtain ⟨y, ey, rest⟩ := tail y1 m1 hy1 f1 hW
    refine ⟨y, ?_, rest⟩
    have n1 := hsplit.2.1 k1
    have n5 := hrec.2 k5
    have n3 := hsplit.2.2.2.1 k3
    cases ci with
    | defnInfo cv v h => exact absurd rfl (n1 cv v h)
    | recInfo cv a b c rs => exact absurd rfl (n5 cv a b c rs)
    | indInfo cv caps => exact absurd rfl (n3 cv caps)
    | _ =>
      simp only [NeedsSt.const, StateT.run_bind, e1', except_ok_bind] at ey ⊢
      exact ey

end fp

end L.Arena
