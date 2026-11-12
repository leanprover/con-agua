module

public import ConAgua.Arena.NatArms
import ConAgua.Arena.Pins
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.LdRd
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.NatArms

@[expose] public section

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
theorem natAddLit_arms : ArmRefinesS "nat_add_lit" natAddArm :=
  fun n s₀ a₀ hR hmx oa la ob lb ha hb _ _ hmode =>
    natAddLit_refines natArmProg rfl rfl rfl rfl rfl ArenaR (fun _ _ h => h.lit.1)
      (fun m m' a hR hg => ArenaR.grow m m' hg a hR) internLit_arms rfl rfl rfl n s₀ a₀ hR hmx
      oa la ob lb ha hb hmode

/-- The refinement of an arm that may refuse, under a relation `R` (`ArmRefinesS` at `R`). -/
abbrev ArmRefinesRS (R : Mem → AState → Prop) (g : FnName) (arm : Nat → Nat → AM (Option EIdx)) :
    Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState), R s₀.mem a₀ →
    (rdW (s₀.mem.arr64 PINS) 72).toNat = a₀.pins.maxNatSize → ∀ (oa la ob lb : Word),
    SliceOK s₀.mem oa la → SliceOK s₀.mem ob lb →
    Norm (vpool s₀.mem) oa.toNat la.toNat → Norm (vpool s₀.mem) ob.toNat lb.toNat →
    ModeOK s₀.mem →
    ⦃fun s => s = s₀⦄
    invoke natArmProg (exec natArmProg n) g [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      NatRes R (arm (pv (vpool s₀.mem) oa.toNat la.toNat) (pv (vpool s₀.mem) ob.toNat lb.toNat))
        a₀ (r.headD 0) s'.mem; ⊤⦄

/-- **The outcome of `nat_op_result`** `(f, h)`: flag `2` is the twin's refusal (the sentinel `h`),
any other the twin's `Option` result (`decOpt`). -/
def NatOpRes (R : Mem → AState → Prop) (arm : AM (Option EIdx)) (a₀ : AState) (f h : Word)
    (m' : Mem) : Prop :=
  (f ≠ 2 → AM.ok arm a₀ ∧ R m' (AM.st arm a₀) ∧ AM.res arm a₀ = decOpt f h) ∧
  (f = 2 → arm.run a₀ = .error (natRefusal h))

/-- A refusing arm's outcome as `nat_op_result`'s (the flag `1 + (h >>> 63)`). -/
theorem NatOpRes.ofNatRes {R : Mem → AState → Prop} {arm : AM (Option EIdx)} {a₀ : AState} {h : Word}
    {m' : Mem} (hr : NatRes R arm a₀ h m') : NatOpRes R arm a₀ ((1 : Word) + (h >>> 63)) h m' := by
  rcases Nat.lt_or_ge h.toNat (2 ^ 63) with hl | hl
  · have h0 : h >>> 63 = 0 := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_shiftRight]; simp; omega
    obtain ⟨hok, hR, hres, -⟩ := hr.1 hl
    rw [h0]
    exact ⟨fun _ => ⟨hok, hR, by rw [hres]; rfl⟩, fun e => absurd e (by decide)⟩
  · have h1 : h >>> 63 = 1 := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_shiftRight]
      have := h.toNat_lt; simp; omega
    rw [h1]
    exact ⟨fun e => absurd rfl e, fun _ => hr.2 hl⟩

/-- A refusing arm's outcome, through a run equal to the arm's. -/
theorem NatOpRes.ofSelRes {R : Mem → AState → Prop} {x arm : AM (Option EIdx)} {a₀ : AState}
    {h : Word} {m' : Mem} (hx : x.run a₀ = arm.run a₀) (hr : NatRes R arm a₀ h m') :
    NatOpRes R x a₀ ((1 : Word) + (h >>> 63)) h m' := by
  have e := AM.congr_run hx
  have := NatOpRes.ofNatRes hr
  unfold NatOpRes at this ⊢
  rw [e.1, e.2.1, e.2.2, hx]
  exact this

/-- A non-refusing arm's outcome as `nat_op_result`'s (the flag `1`). -/
theorem NatOpRes.ofSome {R : Mem → AState → Prop} {arm : AM (Option EIdx)} {a₀ : AState} {h : Word}
    {m' : Mem} (hok : AM.ok arm a₀) (hR : R m' (AM.st arm a₀)) (hres : AM.res arm a₀ = some (decE h)) :
    NatOpRes R arm a₀ 1 h m' :=
  ⟨fun _ => ⟨hok, hR, by rw [hres]; rfl⟩, fun e => absurd e (by decide)⟩

/-- The arm refinement for `natArmProg` under a relation `R`, with the operands' slices given
(`ArmRefinesA` at `R`). -/
abbrev ArmRefinesR (R : Mem → AState → Prop) (g : FnName) (arm : Nat → Nat → AM (Option EIdx)) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState), R s₀.mem a₀ → ∀ (oa la ob lb : Word),
    SliceOK s₀.mem oa la → SliceOK s₀.mem ob lb →
    Norm (vpool s₀.mem) oa.toNat la.toNat → Norm (vpool s₀.mem) ob.toNat lb.toNat →
    ModeOK s₀.mem →
    ⦃fun s => s = s₀⦄
    invoke natArmProg (exec natArmProg n) g [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (arm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ ∧
      R s'.mem (AM.st (arm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀) ∧
      AM.res (arm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)); ⊤⦄

/-- The `beq`/`ble` arm refinement under `R`, given the three pin reads. -/
abbrev CmpArmR (R : Mem → AState → Prop) (g : FnName) (arm : Nat → Nat → AM (Option EIdx)) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState), R s₀.mem a₀ → ∀ (oa la ob lb t f us : Word),
    SliceOK s₀.mem oa la → SliceOK s₀.mem ob lb →
    Norm (vpool s₀.mem) oa.toNat la.toNat → Norm (vpool s₀.mem) ob.toNat lb.toNat →
    t.toNat < 2 ^ 32 → f.toNat < 2 ^ 32 → us.toNat < 2 ^ 32 →
    boolTrueName.run a₀ = .ok (decI t, a₀) → boolFalseName.run a₀ = .ok (decI f, a₀) →
    emptyLevels.run a₀ = .ok (decI us, a₀) →
    ⦃fun s => s = s₀⦄
    invoke natArmProg (exec natArmProg n) g [oa, la, ob, lb, t, f, us]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (arm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ ∧
      R s'.mem (AM.st (arm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀) ∧
      AM.res (arm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)); ⊤⦄

/-- **The sixteen arms under a relation `R`** (what `nat_op_result`'s refinement needs of them). -/
structure NatArmsR (R : Mem → AState → Prop) : Prop where
  pred : ∀ (n : Nat) (s₀ : St) (a₀ : AState), R s₀.mem a₀ → ∀ (oa la : Word),
    SliceOK s₀.mem oa la → ModeOK s₀.mem →
    ⦃fun s => s = s₀⦄
    invoke natArmProg (exec natArmProg n) "nat_pred_lit" [oa, la]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natPredArm (pv (vpool s₀.mem) oa.toNat la.toNat)) a₀ ∧
      R s'.mem (AM.st (natPredArm (pv (vpool s₀.mem) oa.toNat la.toNat)) a₀) ∧
      AM.res (natPredArm (pv (vpool s₀.mem) oa.toNat la.toNat)) a₀ =
        some (decE (r.headD 0)); ⊤⦄
  pow : ArmRefinesRS R "nat_pow_lit" natPowArm
  add : ArmRefinesRS R "nat_add_lit" natAddArm
  sub : ArmRefinesRS R "nat_sub_lit" natSubArm
  mul : ArmRefinesRS R "nat_mul_lit" natMulArm
  div : ArmRefinesR R "nat_div_lit" natDivArm
  mod : ArmRefinesR R "nat_mod_lit" natModArm
  gcd : ArmRefinesR R "nat_gcd_lit" natGcdArm
  land : ArmRefinesR R "nat_land_lit" natLandArm
  lor : ArmRefinesR R "nat_lor_lit" natLorArm
  xor : ArmRefinesR R "nat_xor_lit" natXorArm
  shl : ArmRefinesRS R "nat_shl_lit" natShlArm
  shr : ArmRefinesR R "nat_shr_lit" natShrArm
  beq : CmpArmR R "nat_beq_lit" natBeqArm
  ble : CmpArmR R "nat_ble_lit" natBleArm

/-- The arms under `ArenaR`. -/
theorem natArmsR_arena : NatArmsR ArenaR :=
  ⟨natPredLit_refinesA, natPowLit_refinesA, natAddLit_arms, natSubLit_refinesA, natMulLit_refinesA,
    natDivLit_refinesA, natModLit_refinesA, natGcdLit_refinesA, natLandLit_refinesA,
    natLorLit_refinesA, natXorLit_refinesA, natShlLit_refinesA, natShrLit_refinesA,
    natBeqLit_refinesA, natBleLit_refinesA⟩

/-- A pin read by `ld64_rd_spec`, at a literal index, is `pinW`. -/
theorem rdW_PINS_ofNat (m : Mem) (k : Nat) :
    rdW (m.arr64 PINS) (no_index (OfNat.ofNat k : Word)) = pinW m (k % 2 ^ 64) := by
  simp only [rdW, pinW]
  rfl

-- the sixteen arms in one `vcgen`, then plain `grind` per goal (about 15 s)
set_option maxHeartbeats 2000000 in
/-- **`nat_op_result` refines `natOpResult`** under any relation `R` its arms keep (`NatArmsR`),
and `PinsR`: the pin reads, the dispatch and every arm. The operands are normalised slices (every
`lit` record's is). -/
theorem natOpResultL_refinesR (R : Mem → AState → Prop) (harms : NatArmsR R) (n : Nat) (s₀ : St)
    (a₀ : AState) (hR : R s₀.mem a₀)
    (hP : PinsR s₀.mem a₀.pins) (c oa la ob lb : Word) (hc : c.toNat < 2 ^ 32)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hna : Norm (vpool s₀.mem) oa.toNat la.toNat)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke natArmProg (exec natArmProg n) "nat_op_result" [c, oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      NatOpRes R (natOpResult (decI c) (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ (r.headD 0) (r.tail.headD 0) s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (show natArmProg.lookup "nat_op_result" = some natOpResultL from rfl)]
  simp only [callFn, natOpResultL]
  have hF : pinW s₀.mem 0 ≠ 0 → PinsFull s₀.mem a₀.pins := hP.full
  generalize hA : pv (vpool s₀.mem) oa.toNat la.toNat = A
  generalize hB : pv (vpool s₀.mem) ob.toNat lb.toNat = B
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
  have hT : pinW s₀.mem 0 ≠ 0 → boolTrueName.run a₀ = .ok (decI (pinW s₀.mem 31), a₀) :=
    fun h => pinAt_run (hF h) 30 (by decide)
  have hFl : pinW s₀.mem 0 ≠ 0 → boolFalseName.run a₀ = .ok (decI (pinW s₀.mem 32), a₀) :=
    fun h => pinAt_run (hF h) 31 (by decide)
  have hE : pinW s₀.mem 0 ≠ 0 → emptyLevels.run a₀ = .ok (decI (pinW s₀.mem 52), a₀) :=
    fun h => pinEmptyLevels_run (hF h)
  have hmx : pinW s₀.mem 0 ≠ 0 → (rdW (s₀.mem.arr64 PINS) 72).toNat = a₀.pins.maxNatSize :=
    fun h => (hF h).maxNatSize.symm
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec,
      (harms.pred n · a₀), (harms.add n · a₀), (harms.sub n · a₀),
      (harms.mul n · a₀), (harms.pow n · a₀), (harms.div n · a₀),
      (harms.mod n · a₀), (harms.gcd n · a₀), (harms.land n · a₀),
      (harms.lor n · a₀), (harms.xor n · a₀), (harms.shl n · a₀),
      (harms.shr n · a₀), (harms.beq n · a₀), (harms.ble n · a₀)]
    -- `harms` is spent: every goal would carry its fifteen triples into `grind`
    all_goals clear harms
    all_goals subst_vars
    all_goals (try exact LocEq.restore _ _)
    all_goals (try assumption)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, reduceIte,
      beq_iff_eq, rdW_PINS_ofNat, Nat.reduceMod, Nat.reducePow] at *)
    all_goals first
      | (obtain ⟨-, hN⟩ : _ ∧ NatRes _ _ _ _ _ := by assumption
         simp only [Sig.retVal, Sig.retOr, List.headD_cons, List.tail_cons, BinOp.eval]
         refine NatOpRes.ofSelRes ?_ hN
         rw [hsel (by assumption)]
         simp only [natOpSel]
         simp_all)
      | grind [lang_grind, arena_grind, natOpSel, PinsFull.size, PinsFull.names_lt, PinsFull.lv_lt,
          NatOpRes.ofNatRes, NatOpRes.ofSome, NatOpRes]

/-- **`nat_op_result` refines `natOpResult`** under `ArenaR` and `PinsR`. -/
@[refines ConRon.Arena.natOpResult]
theorem natOpResultL_refines (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀)
    (hP : PinsR s₀.mem a₀.pins) (c oa la ob lb : Word) (hc : c.toNat < 2 ^ 32)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hna : Norm (vpool s₀.mem) oa.toNat la.toNat)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke natArmProg (exec natArmProg n) "nat_op_result" [c, oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      NatOpRes ArenaR (natOpResult (decI c) (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ (r.headD 0) (r.tail.headD 0) s'.mem; ⊤⦄ :=
  natOpResultL_refinesR ArenaR natArmsR_arena n s₀ a₀ hR hP c oa la ob lb hc ha hb hna hnb hmode

end L.Arena
