import ConAgua.Arena.Tiers
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The pin table in L: the readers

`Tiers.lean`'s `PinsR` relates the word array `PINS` (128) to the twin's `a.pins`. This file
has the L readers and their refinements:

* `pin_at(i)`: the flag, the bound `i < 51`, then word `1 + i` (the twin's `pinAt i`: a bounds
  test on the table and a read). Refines `pinAt` at every `i` (`pinAt_refines`); each of the 51
  named readers (`pinNat`, …, and Core's `natAddName`, …) is `pin_at` at a literal.
* `pin_word(k)`: the flag, then word `k`, for the three interned values (`pinEmptyLevels`,
  `pinZeroLevel`, `pinSortOne`: words 52‥54).

A reader does not change the memory or the twin state. The twin-side facts are `pinAt_run` and
friends: under `PinsFull` each reader is a pure read of the related word.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin side: reads of a filled table -/

/-- The `simp` set that runs a pin read. -/
theorem pinAt_run {m : Mem} {a : AState} (h : PinsFull m a.pins) (i : Nat) (hi : i < 51) :
    (pinAt i).run a = .ok (decI (pinW m (1 + i)), a) := by
  have hs := h.names_size
  have := h.names i hi
  simp [pinAt, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Except.bind, pure, StateT.pure, Except.pure, hs, hi, this]

theorem pinsReady_true {m : Mem} {a : AState} (h : PinsFull m a.pins) : pinsReady a = true := by
  simp [pinsReady, h.names_size, pinCount]

theorem pinEmptyLevels_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    pinEmptyLevels.run a = .ok (decI (pinW m 52), a) := by
  have := pinsReady_true h
  simp [pinEmptyLevels, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Except.bind, pure, StateT.pure, Except.pure, this, h.emptyLevels]

theorem pinZeroLevel_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    pinZeroLevel.run a = .ok (decI (pinW m 53), a) := by
  have := pinsReady_true h
  simp [pinZeroLevel, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Except.bind, pure, StateT.pure, Except.pure, this, h.zeroLevel]

theorem pinSortOne_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    pinSortOne.run a = .ok (decI (pinW m 54), a) := by
  have := pinsReady_true h
  simp [pinSortOne, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Except.bind, pure, StateT.pure, Except.pure, this, h.sortOne]

theorem pinReserved_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    pinReserved.run a = .ok ((List.range 16).map fun i => decI (pinW m (55 + i)), a) := by
  have := pinsReady_true h
  simp [pinReserved, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Except.bind, pure, StateT.pure, Except.pure, this, h.reserved]

/-! ## The L readers -/

/-- `pin_at(i)`: `PINS[1 + i]`, after the flag and the bound. -/
-- con-ron: ConRon/Arena/Pins.lean:250-257 ConRon.Arena.pinAt
@[l_impl ConRon.Arena.pinAt]
def pinAtL : FunDecl := lfn (i) locals () {
  if PINS.u64[0] == 0 { abort };
  if 51 <= i { abort };
  return PINS.u64[1 + i]
}

/-- `pin_word(k)`: `PINS[k]`, after the flag (the three interned values, `k` = 52, 53, 54). -/
-- con-ron: ConRon/Arena/Pins.lean:250-257 ConRon.Arena.pinAt
def pinWordL : FunDecl := lfn (k) locals () {
  if PINS.u64[0] == 0 { abort };
  return PINS.u64[k]
}

theorem pinW_eq (m : Mem) (k : Nat) (h : k < (m.arr64 PINS).size) :
    pinW m k = (m.arr64 PINS)[k] := by simp [pinW, h]

theorem pinW_zero (m : Mem) (h : 0 < (m.arr64 PINS).size) (h0 : (m.arr64 PINS)[0] ≠ 0) :
    pinW m 0 ≠ 0 := by rwa [pinW_eq m 0 h]

/-- The read `pin_at` makes, at a set flag and `i < 51`. -/
theorem pinAt_word {m : Mem} {a : AState} (hP : PinsR m a.pins) (i : Word)
    (h0 : 0 < (m.arr64 PINS).size) (hf : (m.arr64 PINS)[0] ≠ 0) (hi : ¬ 51 ≤ i)
    (hb : (1 + i).toNat < (m.arr64 PINS).size) :
    (pinAt i.toNat).run a = .ok (decI ((m.arr64 PINS)[(1 + i).toNat]), a) ∧
      ((m.arr64 PINS)[(1 + i).toNat]).toNat < 2 ^ 32 := by
  have hF := hP.full (pinW_zero m h0 hf)
  have hi' : i.toNat < 51 := by
    have : ¬ (51 : Word).toNat ≤ i.toNat := fun h => hi (UInt64.le_iff_toNat_le.mpr h)
    simp at this; omega
  have h1 : (1 + i).toNat = 1 + i.toNat := by rw [UInt64.toNat_add]; simp; omega
  rw [← pinW_eq m _ hb, h1]
  exact ⟨pinAt_run hF _ hi', hF.names_lt _ hi'⟩

/-- **`pin_at` refines `pinAt`**: on a return, the memory is unchanged and the twin's read returns
the same handle and keeps the state. -/
@[refines ConRon.Arena.pinAt]
theorem pinAt_refines (p : Prog) (hp : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St)
    (a₀ : AState) (hP : PinsR s₀.mem a₀.pins) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "pin_at" [i]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      (pinAt i.toNat).run a₀ = .ok (decI (r.headD 0), a₀); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, pinAtL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have key := pinAt_word hP i
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish

/-! ## The named readers -/

/-- A named reader of slot `k` (`f = pinAt k`) refined by `pin_at(k)`. -/
abbrev PinSlotSpec (f : AM NIdx) (k : Nat) : Prop :=
  ∀ (p : Prog), p.lookup "pin_at" = some pinAtL → ∀ (n : Nat) (s₀ : St) (a₀ : AState),
    PinsR s₀.mem a₀.pins →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "pin_at" [UInt64.ofNat k]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      f.run a₀ = .ok (decI (r.headD 0), a₀); ⊤⦄

theorem pinSlot_refines (f : AM NIdx) (k : Nat) (hf : f = pinAt k) (hk : k < 51) :
    PinSlotSpec f k := by
  intro p hp n s₀ a₀ hP
  have := pinAt_refines p hp n s₀ a₀ hP (UInt64.ofNat k)
  have hk' : (UInt64.ofNat k).toNat = k := by simp; omega
  rw [hk', ← hf] at this
  exact this

/-- One of the three interned values (word `w`), refined by `pin_word(w)`. -/
abbrev PinWordSpec {κ : IdxKind} (f : AM (Idx κ)) (w : Nat) : Prop :=
  ∀ (p : Prog), p.lookup "pin_word" = some pinWordL → ∀ (n : Nat) (s₀ : St) (a₀ : AState),
    PinsR s₀.mem a₀.pins →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "pin_word" [UInt64.ofNat w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ f.run a₀ = .ok (decI (r.headD 0), a₀); ⊤⦄

theorem pinWord_refines {κ : IdxKind} (f : AM (Idx κ)) (w : Nat) (hw : w < 71)
    (hrun : ∀ {m : Mem} {a : AState}, PinsFull m a.pins → f.run a = .ok (decI (pinW m w), a)) :
    PinWordSpec f w := by
  intro p hp n s₀ a₀ hP
  have hw' : (UInt64.ofNat w).toNat = w := by simp; omega
  have hr : PinsFull s₀.mem a₀.pins → f.run a₀ = .ok (decI (pinW s₀.mem w), a₀) := hrun
  have hF : pinW s₀.mem 0 ≠ 0 → PinsFull s₀.mem a₀.pins := hP.full
  rw [invoke_eq _ hp]
  simp only [callFn, pinWordL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [pinW_eq]

@[refines ConRon.Arena.emptyLevels] theorem emptyLevels_refines : PinWordSpec emptyLevels 52 :=
  pinWord_refines _ _ (by decide) pinEmptyLevels_run
@[refines ConRon.Arena.zeroLevel] theorem zeroLevel_refines : PinWordSpec zeroLevel 53 :=
  pinWord_refines _ _ (by decide) pinZeroLevel_run
@[refines ConRon.Arena.sortOne] theorem sortOne_refines : PinWordSpec sortOne 54 :=
  pinWord_refines _ _ (by decide) pinSortOne_run
@[refines ConRon.Arena.natPredName] theorem natPredName_refines : PinSlotSpec natPredName PIN_NAT_PRED :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.natAddName] theorem natAddName_refines : PinSlotSpec natAddName PIN_NAT_ADD :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.natSubName] theorem natSubName_refines : PinSlotSpec natSubName PIN_NAT_SUB :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.natMulName] theorem natMulName_refines : PinSlotSpec natMulName PIN_NAT_MUL :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.natPowName] theorem natPowName_refines : PinSlotSpec natPowName PIN_NAT_POW :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.natBeqName] theorem natBeqName_refines : PinSlotSpec natBeqName PIN_NAT_BEQ :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.natBleName] theorem natBleName_refines : PinSlotSpec natBleName PIN_NAT_BLE :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.natDivName] theorem natDivName_refines : PinSlotSpec natDivName PIN_NAT_DIV :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.natModName] theorem natModName_refines : PinSlotSpec natModName PIN_NAT_MOD :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.natGcdName] theorem natGcdName_refines : PinSlotSpec natGcdName PIN_NAT_GCD :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.natLandName] theorem natLandName_refines : PinSlotSpec natLandName PIN_NAT_LAND :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.natLorName] theorem natLorName_refines : PinSlotSpec natLorName PIN_NAT_LOR :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.natXorName] theorem natXorName_refines : PinSlotSpec natXorName PIN_NAT_XOR :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.natShiftLeftName] theorem natShiftLeftName_refines : PinSlotSpec natShiftLeftName PIN_NAT_SHIFT_LEFT :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.natShiftRightName] theorem natShiftRightName_refines : PinSlotSpec natShiftRightName PIN_NAT_SHIFT_RIGHT :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.boolName] theorem boolName_refines : PinSlotSpec boolName PIN_BOOL :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.boolTrueName] theorem boolTrueName_refines : PinSlotSpec boolTrueName PIN_BOOL_TRUE :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.boolFalseName] theorem boolFalseName_refines : PinSlotSpec boolFalseName PIN_BOOL_FALSE :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.eagerReduceName] theorem eagerReduceName_refines : PinSlotSpec eagerReduceName PIN_EAGER_REDUCE :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinEq] theorem pinEq_refines : PinSlotSpec pinEq PIN_EQ :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNat] theorem pinNat_refines : PinSlotSpec pinNat PIN_NAT :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatZero] theorem pinNatZero_refines : PinSlotSpec pinNatZero PIN_NAT_ZERO :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatSucc] theorem pinNatSucc_refines : PinSlotSpec pinNatSucc PIN_NAT_SUCC :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinQuotSound] theorem pinQuotSound_refines : PinSlotSpec pinQuotSound PIN_QUOT_SOUND :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinString] theorem pinString_refines : PinSlotSpec pinString PIN_STRING :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinStringOfList] theorem pinStringOfList_refines : PinSlotSpec pinStringOfList PIN_STRING_OF_LIST :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinList] theorem pinList_refines : PinSlotSpec pinList PIN_LIST :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinListNil] theorem pinListNil_refines : PinSlotSpec pinListNil PIN_LIST_NIL :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinListCons] theorem pinListCons_refines : PinSlotSpec pinListCons PIN_LIST_CONS :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinChar] theorem pinChar_refines : PinSlotSpec pinChar PIN_CHAR :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinAnd] theorem pinAnd_refines : PinSlotSpec pinAnd PIN_AND :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinCharOfNat] theorem pinCharOfNat_refines : PinSlotSpec pinCharOfNat PIN_CHAR_OF_NAT :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinSorryAx] theorem pinSorryAx_refines : PinSlotSpec pinSorryAx PIN_SORRY_AX :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatPred] theorem pinNatPred_refines : PinSlotSpec pinNatPred PIN_NAT_PRED :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatAdd] theorem pinNatAdd_refines : PinSlotSpec pinNatAdd PIN_NAT_ADD :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatSub] theorem pinNatSub_refines : PinSlotSpec pinNatSub PIN_NAT_SUB :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatMul] theorem pinNatMul_refines : PinSlotSpec pinNatMul PIN_NAT_MUL :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatPow] theorem pinNatPow_refines : PinSlotSpec pinNatPow PIN_NAT_POW :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatBeq] theorem pinNatBeq_refines : PinSlotSpec pinNatBeq PIN_NAT_BEQ :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatBle] theorem pinNatBle_refines : PinSlotSpec pinNatBle PIN_NAT_BLE :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatDiv] theorem pinNatDiv_refines : PinSlotSpec pinNatDiv PIN_NAT_DIV :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatMod] theorem pinNatMod_refines : PinSlotSpec pinNatMod PIN_NAT_MOD :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatGcd] theorem pinNatGcd_refines : PinSlotSpec pinNatGcd PIN_NAT_GCD :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatLand] theorem pinNatLand_refines : PinSlotSpec pinNatLand PIN_NAT_LAND :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatLor] theorem pinNatLor_refines : PinSlotSpec pinNatLor PIN_NAT_LOR :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatXor] theorem pinNatXor_refines : PinSlotSpec pinNatXor PIN_NAT_XOR :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatShiftLeft] theorem pinNatShiftLeft_refines : PinSlotSpec pinNatShiftLeft PIN_NAT_SHIFT_LEFT :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNatShiftRight] theorem pinNatShiftRight_refines : PinSlotSpec pinNatShiftRight PIN_NAT_SHIFT_RIGHT :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinBool] theorem pinBool_refines : PinSlotSpec pinBool PIN_BOOL :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinBoolTrue] theorem pinBoolTrue_refines : PinSlotSpec pinBoolTrue PIN_BOOL_TRUE :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinBoolFalse] theorem pinBoolFalse_refines : PinSlotSpec pinBoolFalse PIN_BOOL_FALSE :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinPropext] theorem pinPropext_refines : PinSlotSpec pinPropext PIN_PROPEXT :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinChoice] theorem pinChoice_refines : PinSlotSpec pinChoice PIN_CHOICE :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinIff] theorem pinIff_refines : PinSlotSpec pinIff PIN_IFF :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinIffIntro] theorem pinIffIntro_refines : PinSlotSpec pinIffIntro PIN_IFF_INTRO :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinIffRec] theorem pinIffRec_refines : PinSlotSpec pinIffRec PIN_IFF_REC :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNonempty] theorem pinNonempty_refines : PinSlotSpec pinNonempty PIN_NONEMPTY :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNonemptyIntro] theorem pinNonemptyIntro_refines : PinSlotSpec pinNonemptyIntro PIN_NONEMPTY_INTRO :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinNonemptyRec] theorem pinNonemptyRec_refines : PinSlotSpec pinNonemptyRec PIN_NONEMPTY_REC :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinTrue] theorem pinTrue_refines : PinSlotSpec pinTrue PIN_TRUE :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinTrueIntro] theorem pinTrueIntro_refines : PinSlotSpec pinTrueIntro PIN_TRUE_INTRO :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinTrustCompiler] theorem pinTrustCompiler_refines : PinSlotSpec pinTrustCompiler PIN_TRUST_COMPILER :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinReduceNat] theorem pinReduceNat_refines : PinSlotSpec pinReduceNat PIN_REDUCE_NAT :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinReduceBool] theorem pinReduceBool_refines : PinSlotSpec pinReduceBool PIN_REDUCE_BOOL :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinOfReduceNat] theorem pinOfReduceNat_refines : PinSlotSpec pinOfReduceNat PIN_OF_REDUCE_NAT :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinOfReduceBool] theorem pinOfReduceBool_refines : PinSlotSpec pinOfReduceBool PIN_OF_REDUCE_BOOL :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinQuot] theorem pinQuot_refines : PinSlotSpec pinQuot PIN_QUOT :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinAndIntro] theorem pinAndIntro_refines : PinSlotSpec pinAndIntro PIN_AND_INTRO :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinAndRec] theorem pinAndRec_refines : PinSlotSpec pinAndRec PIN_AND_REC :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.pinEagerReduce] theorem pinEagerReduce_refines : PinSlotSpec pinEagerReduce PIN_EAGER_REDUCE :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.propextName] theorem propextName_refines : PinSlotSpec propextName PIN_PROPEXT :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.choiceName] theorem choiceName_refines : PinSlotSpec choiceName PIN_CHOICE :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.iffName] theorem iffName_refines : PinSlotSpec iffName PIN_IFF :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.iffIntroName] theorem iffIntroName_refines : PinSlotSpec iffIntroName PIN_IFF_INTRO :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.iffRecName] theorem iffRecName_refines : PinSlotSpec iffRecName PIN_IFF_REC :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.nonemptyName] theorem nonemptyName_refines : PinSlotSpec nonemptyName PIN_NONEMPTY :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.nonemptyIntroName] theorem nonemptyIntroName_refines : PinSlotSpec nonemptyIntroName PIN_NONEMPTY_INTRO :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.nonemptyRecName] theorem nonemptyRecName_refines : PinSlotSpec nonemptyRecName PIN_NONEMPTY_REC :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.trueName] theorem trueName_refines : PinSlotSpec trueName PIN_TRUE :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.trueIntroName] theorem trueIntroName_refines : PinSlotSpec trueIntroName PIN_TRUE_INTRO :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.trustCompilerName] theorem trustCompilerName_refines : PinSlotSpec trustCompilerName PIN_TRUST_COMPILER :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.reduceNatName] theorem reduceNatName_refines : PinSlotSpec reduceNatName PIN_REDUCE_NAT :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.reduceBoolName] theorem reduceBoolName_refines : PinSlotSpec reduceBoolName PIN_REDUCE_BOOL :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.ofReduceNatName] theorem ofReduceNatName_refines : PinSlotSpec ofReduceNatName PIN_OF_REDUCE_NAT :=
  pinSlot_refines _ _ rfl (by decide)
@[refines ConRon.Arena.ofReduceBoolName] theorem ofReduceBoolName_refines : PinSlotSpec ofReduceBoolName PIN_OF_REDUCE_BOOL :=
  pinSlot_refines _ _ rfl (by decide)

end L.Arena
