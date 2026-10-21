import ConAgua.Arena.NatArms
import ConAgua.Arena.Pins

/-!
# `natOpResult`, the whole dispatch, under `ArenaR` and `PinsR`

`natOpResult c a b` (`Arena/Core.lean:998`) reads fifteen pins, then compares `c` with them in a
fixed order and runs one arm. Under a filled table (`PinsFull`) the reads are pure reads of the
related words, so `natOpResult` runs as `natOpSel` (`natOpResult_sel`): the same if-chain, on
**word** comparisons (handle words are below `2^32`, so `decI` is injective on them). The L
dispatcher `nat_op_result` (`NatArms.lean`, in `natArmProg`) makes the same comparisons and calls
the arms refined in `NatArms.lean`/`Refine.lean`; the `beq`/`ble` arms' pin hypotheses are
discharged from `PinsFull` (`pinAt_run`, `pinEmptyLevels_run`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

theorem decI_inj {k : IdxKind} {v w : Word} (hv : v.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32)
    (h : (decI v : Idx k) = decI w) : v = w := by
  have := (word_decI (decI v : Idx k) w hw).mpr h
  rw [← this]
  apply UInt64.toNat_inj.mp
  simp [decI]; omega

theorem decI_beq {k : IdxKind} (v w : Word) (hv : v.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32) :
    ((decI v : Idx k) == decI w) = decide (v = w) := by
  by_cases h : v = w
  · subst h; simp
  · have : (decI v : Idx k) ≠ decI w := fun e => h (decI_inj hv hw e)
    simp [h, this]

theorem pinAt_bind_run {m : Mem} {a : AState} {β : Type} (h : PinsFull m a.pins) (i : Nat)
    (hi : i < 51) (k : NIdx → AM β) :
    (pinAt i >>= k).run a = (k (decI (pinW m (1 + i)))).run a := by
  rw [StateT.run_bind, pinAt_run h i hi]; rfl

/-- `natOpResult` with its pins read: word `w k` is pin word `k`. -/
def natOpSel (w : Nat → Word) (c : Word) (a b : Nat) : AM (Option EIdx) :=
  if c = w 15 then natPredArm a
  else if c = w 16 then natAddArm a b
  else if c = w 17 then natSubArm a b
  else if c = w 18 then natMulArm a b
  else if c = w 19 then natPowArm a b
  else if c = w 22 then natDivArm a b
  else if c = w 23 then natModArm a b
  else if c = w 24 then natGcdArm a b
  else if c = w 25 then natLandArm a b
  else if c = w 26 then natLorArm a b
  else if c = w 27 then natXorArm a b
  else if c = w 28 then natShlArm a b
  else if c = w 29 then natShrArm a b
  else if c = w 20 then natBeqArm a b
  else if c = w 21 then natBleArm a b
  else pure none

theorem natOpResult_sel {m : Mem} {a : AState} (h : PinsFull m a.pins) (c : Word)
    (hc : c.toNat < 2 ^ 32) (x y : Nat) :
    (natOpResult (decI c) x y).run a = (natOpSel (pinW m) c x y).run a := by
  have hb : ∀ i, i < 51 → ((decI c : NIdx) == decI (pinW m (1 + i))) = decide (c = pinW m (1 + i)) :=
    fun i hi => decI_beq _ _ hc (h.names_lt i hi)
  simp only [natOpResult, natPredName, natAddName, natSubName, natMulName, natPowName,
    natBeqName, natBleName, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatPred, pinNatAdd, pinNatSub,
    pinNatMul, pinNatPow, pinNatBeq, pinNatBle, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_PRED, PIN_NAT_ADD,
    PIN_NAT_SUB, PIN_NAT_MUL, PIN_NAT_POW, PIN_NAT_BEQ, PIN_NAT_BLE, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT,
    PIN_NAT_SHIFT_RIGHT, pinAt_bind_run h, Nat.reduceAdd, Nat.reduceLT]
  have e15 : (decI c == (decI (pinW m 15) : NIdx)) = decide (c = pinW m 15) := hb 14 (by decide)
  have e16 : (decI c == (decI (pinW m 16) : NIdx)) = decide (c = pinW m 16) := hb 15 (by decide)
  have e17 : (decI c == (decI (pinW m 17) : NIdx)) = decide (c = pinW m 17) := hb 16 (by decide)
  have e18 : (decI c == (decI (pinW m 18) : NIdx)) = decide (c = pinW m 18) := hb 17 (by decide)
  have e19 : (decI c == (decI (pinW m 19) : NIdx)) = decide (c = pinW m 19) := hb 18 (by decide)
  have e20 : (decI c == (decI (pinW m 20) : NIdx)) = decide (c = pinW m 20) := hb 19 (by decide)
  have e21 : (decI c == (decI (pinW m 21) : NIdx)) = decide (c = pinW m 21) := hb 20 (by decide)
  have e22 : (decI c == (decI (pinW m 22) : NIdx)) = decide (c = pinW m 22) := hb 21 (by decide)
  have e23 : (decI c == (decI (pinW m 23) : NIdx)) = decide (c = pinW m 23) := hb 22 (by decide)
  have e24 : (decI c == (decI (pinW m 24) : NIdx)) = decide (c = pinW m 24) := hb 23 (by decide)
  have e25 : (decI c == (decI (pinW m 25) : NIdx)) = decide (c = pinW m 25) := hb 24 (by decide)
  have e26 : (decI c == (decI (pinW m 26) : NIdx)) = decide (c = pinW m 26) := hb 25 (by decide)
  have e27 : (decI c == (decI (pinW m 27) : NIdx)) = decide (c = pinW m 27) := hb 26 (by decide)
  have e28 : (decI c == (decI (pinW m 28) : NIdx)) = decide (c = pinW m 28) := hb 27 (by decide)
  have e29 : (decI c == (decI (pinW m 29) : NIdx)) = decide (c = pinW m 29) := hb 28 (by decide)
  simp only [e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, decide_eq_true_eq]
  rfl

theorem AM.congr_run {α : Type} [Inhabited α] {x y : AM α} {a : AState} (h : x.run a = y.run a) :
    AM.ok x a = AM.ok y a ∧ AM.st x a = AM.st y a ∧ AM.res x a = AM.res y a := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [AM.ok, AM.st, AM.res, h]

/-- The `Nat.add` arm in `natArmProg`. -/
theorem natAddLit_arms : ArmRefinesA "nat_add_lit" natAddArm :=
  fun n s₀ a₀ hR oa la ob lb ha hb _ _ =>
    natAddLit_refines natArmProg rfl rfl rfl rfl rfl ArenaR (fun _ _ h => h.lit.1)
      (fun m m' a hR hg => ArenaR.grow m m' hg a hR) internLit_arms n s₀ a₀ hR oa la ob lb ha hb

-- the sixteen arms in one `vcgen`, about 17 s
set_option maxHeartbeats 2000000 in
/-- **`nat_op_result` refines `natOpResult`** under `ArenaR` and `PinsR`: the pin reads, the
dispatch and every arm. The operands are normalised slices (every `lit` record's is). -/
@[refines ConRon.Arena.natOpResult]
theorem natOpResultL_refines (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀)
    (hP : PinsR s₀.mem a₀.pins) (c oa la ob lb : Word) (hc : c.toNat < 2 ^ 32)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hna : Norm (s₀.mem.arr64 POOL) oa.toNat la.toNat)
    (hnb : Norm (s₀.mem.arr64 POOL) ob.toNat lb.toNat) :
    ⦃fun s => s = s₀⦄
    invoke natArmProg (exec natArmProg n) "nat_op_result" [c, oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natOpResult (decI c) (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) a₀ ∧
      ArenaR s'.mem (AM.st (natOpResult (decI c) (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) a₀) ∧
      AM.res (natOpResult (decI c) (pv (s₀.mem.arr64 POOL) oa.toNat la.toNat)
        (pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat)) a₀ = decOpt (r.headD 0) (r.tail.headD 0); ⊤⦄ := by
  rw [invoke_eq _ (show natArmProg.lookup "nat_op_result" = some natOpResultL from rfl)]
  simp only [callFn, natOpResultL]
  have hF : pinW s₀.mem 0 ≠ 0 → PinsFull s₀.mem a₀.pins := hP.full
  generalize hA : pv (s₀.mem.arr64 POOL) oa.toNat la.toNat = A
  generalize hB : pv (s₀.mem.arr64 POOL) ob.toNat lb.toNat = B
  have hsel : pinW s₀.mem 0 ≠ 0 →
      (natOpResult (decI c) A B).run a₀ = (natOpSel (pinW s₀.mem) c A B).run a₀ :=
    fun h => natOpResult_sel (hF h) c hc _ _
  have hok : pinW s₀.mem 0 ≠ 0 →
      AM.ok (natOpResult (decI c) A B) a₀ = AM.ok (natOpSel (pinW s₀.mem) c A B) a₀ :=
    fun h => (AM.congr_run (hsel h)).1
  have hst : pinW s₀.mem 0 ≠ 0 →
      AM.st (natOpResult (decI c) A B) a₀ = AM.st (natOpSel (pinW s₀.mem) c A B) a₀ :=
    fun h => (AM.congr_run (hsel h)).2.1
  have hres : pinW s₀.mem 0 ≠ 0 →
      AM.res (natOpResult (decI c) A B) a₀ = AM.res (natOpSel (pinW s₀.mem) c A B) a₀ :=
    fun h => (AM.congr_run (hsel h)).2.2
  clear hsel
  have hT : pinW s₀.mem 0 ≠ 0 → boolTrueName.run a₀ = .ok (decI (pinW s₀.mem 31), a₀) :=
    fun h => pinAt_run (hF h) 30 (by decide)
  have hFl : pinW s₀.mem 0 ≠ 0 → boolFalseName.run a₀ = .ok (decI (pinW s₀.mem 32), a₀) :=
    fun h => pinAt_run (hF h) 31 (by decide)
  have hE : pinW s₀.mem 0 ≠ 0 → emptyLevels.run a₀ = .ok (decI (pinW s₀.mem 52), a₀) :=
    fun h => pinEmptyLevels_run (hF h)
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        (natPredLit_refinesA n · a₀), (natAddLit_arms n · a₀), (natSubLit_refinesA n · a₀),
        (natMulLit_refinesA n · a₀), (natPowLit_refinesA n · a₀), (natDivLit_refinesA n · a₀),
        (natModLit_refinesA n · a₀), (natGcdLit_refinesA n · a₀), (natLandLit_refinesA n · a₀),
        (natLorLit_refinesA n · a₀), (natXorLit_refinesA n · a₀), (natShlLit_refinesA n · a₀),
        (natShrLit_refinesA n · a₀), (natBeqLit_refinesA n · a₀), (natBleLit_refinesA n · a₀)] <;>
      finish [natOpSel, pinW_eq, PinsFull.size, PinsFull.names_lt, PinsFull.lv_lt]

end L.Arena
