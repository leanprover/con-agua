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
# `natBinOpResult`, the whole dispatch, under a relation the arms keep

`natBinOpResult op a b` (`Arena/Core.lean`) runs the arm of `op`. The L dispatcher
`nat_bin_op_result` (`NatArms.lean`, in `natArmProg`) takes the operation's word code
(`natBinOpW`) and calls the arms refined in `NatArms.lean`/`Refine.lean`; the `beq`/`ble` arms'
pin hypotheses are discharged from `PinsFull` (`pinAt_run`, `pinEmptyLevels_run`).
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

/-- `natBinOpResult` by operation: the arms of `NatArms.lean`. -/
def natBinOpArm : NatBinOp → Nat → Nat → AM (Option EIdx)
  | .add => natAddArm | .sub => natSubArm | .mul => natMulArm | .pow => natPowArm
  | .beq => natBeqArm | .ble => natBleArm | .div => natDivArm | .mod => natModArm
  | .gcd => natGcdArm | .land => natLandArm | .lor => natLorArm | .xor => natXorArm
  | .shiftLeft => natShlArm | .shiftRight => natShrArm

theorem natBinOpResult_arm (op : NatBinOp) (a b : Nat) : natBinOpResult op a b = natBinOpArm op a b := by
  cases op <;> rfl

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

/-- **The outcome of `nat_bin_op_result`** `(f, h)`: flag `2` is the twin's refusal (the sentinel `h`),
any other the twin's `Option` result (`decOpt`). -/
def NatOpRes (R : Mem → AState → Prop) (arm : AM (Option EIdx)) (a₀ : AState) (f h : Word)
    (m' : Mem) : Prop :=
  (f ≠ 2 → AM.ok arm a₀ ∧ R m' (AM.st arm a₀) ∧ AM.res arm a₀ = decOpt f h) ∧
  (f = 2 → arm.run a₀ = .error (natRefusal h))

/-- A refusing arm's outcome as `nat_bin_op_result`'s (the flag `1 + (h >>> 63)`). -/
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

/-- A non-refusing arm's outcome as `nat_bin_op_result`'s (the flag `1`). -/
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

/-- **The fourteen arms under a relation `R`** (what `nat_bin_op_result`'s refinement needs of them). -/
structure NatArmsR (R : Mem → AState → Prop) : Prop where
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
  ⟨natPowLit_refinesA, natAddLit_arms, natSubLit_refinesA, natMulLit_refinesA,
    natDivLit_refinesA, natModLit_refinesA, natGcdLit_refinesA, natLandLit_refinesA,
    natLorLit_refinesA, natXorLit_refinesA, natShlLit_refinesA, natShrLit_refinesA,
    natBeqLit_refinesA, natBleLit_refinesA⟩

/-- A pin read by `ld64_rd_spec`, at a literal index, is `pinW`. -/
theorem rdW_PINS_ofNat (m : Mem) (k : Nat) :
    rdW (m.arr64 PINS) (no_index (OfNat.ofNat k : Word)) = pinW m (k % 2 ^ 64) := by
  simp only [rdW, pinW]
  rfl

/-- **`nat_bin_op_result` refines `natBinOpResult`** under any relation `R` its arms keep
(`NatArmsR`), and the filled pin table (the `beq`/`ble` arms' pins, the maximum `Nat` size): the dispatch on the operation's code and
every arm. The operands are normalised slices (every `lit` record's is). -/
theorem natBinOpResultL_refinesR (R : Mem → AState → Prop) (harms : NatArmsR R) (n : Nat) (s₀ : St)
    (a₀ : AState) (hR : R s₀.mem a₀)
    (hP : PinsFull s₀.mem a₀.pins) (op : NatBinOp) (oa la ob lb : Word)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hna : Norm (vpool s₀.mem) oa.toNat la.toNat)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke natArmProg (exec natArmProg n) "nat_bin_op_result" [natBinOpW op, oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      NatOpRes R (natBinOpResult op (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ (r.headD 0) (r.tail.headD 0) s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (show natArmProg.lookup "nat_bin_op_result" = some natBinOpResultL from rfl)]
  simp only [callFn, natBinOpResultL, natBinOpResult_arm]
  generalize hA : pv (vpool s₀.mem) oa.toNat la.toNat = A
  generalize hB : pv (vpool s₀.mem) ob.toNat lb.toNat = B
  have hT : boolTrueName.run a₀ = .ok (decI (pinW s₀.mem 31), a₀) := pinAt_run hP 30 (by decide)
  have hFl : boolFalseName.run a₀ = .ok (decI (pinW s₀.mem 32), a₀) := pinAt_run hP 31 (by decide)
  have hE : emptyLevels.run a₀ = .ok (decI (pinW s₀.mem 52), a₀) := pinEmptyLevels_run hP
  have hsz := hP.size
  have hnl := hP.names_lt
  have hlv := hP.lv_lt
  have hmx : (rdW (s₀.mem.arr64 PINS) 72).toNat = a₀.pins.maxNatSize := hP.maxNatSize.symm
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    cases op <;> simp only [natBinOpW, natBinOpArm] <;>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec,
      (harms.add n · a₀), (harms.sub n · a₀),
      (harms.mul n · a₀), (harms.pow n · a₀), (harms.div n · a₀),
      (harms.mod n · a₀), (harms.gcd n · a₀), (harms.land n · a₀),
      (harms.lor n · a₀), (harms.xor n · a₀), (harms.shl n · a₀),
      (harms.shr n · a₀), (harms.beq n · a₀), (harms.ble n · a₀)]
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
         exact NatOpRes.ofNatRes hN)
      | grind [lang_grind, arena_grind, PinsFull.size, PinsFull.names_lt, PinsFull.lv_lt,
          NatOpRes.ofNatRes, NatOpRes.ofSome, NatOpRes]

/-- **`nat_bin_op_result` refines `natBinOpResult`** under `ArenaR` and the filled pin table. -/
@[refines ConRon.Arena.natBinOpResult]
theorem natBinOpResultL_refines (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀)
    (hP : PinsFull s₀.mem a₀.pins) (op : NatBinOp) (oa la ob lb : Word)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hna : Norm (vpool s₀.mem) oa.toNat la.toNat)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke natArmProg (exec natArmProg n) "nat_bin_op_result" [natBinOpW op, oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      NatOpRes ArenaR (natBinOpResult op (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ (r.headD 0) (r.tail.headD 0) s'.mem; ⊤⦄ :=
  natBinOpResultL_refinesR ArenaR natArmsR_arena n s₀ a₀ hR hP op oa la ob lb ha hb hna hnb hmode

end L.Arena
