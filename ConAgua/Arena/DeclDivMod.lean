import ConAgua.Arena.DeclNatEq
import ConAgua.Arena.RecCheckSpec
import ConAgua.Rom.PinSets

/-!
# The `Nat.div` family's pin gate, bottom up (lane `decls3`, helper `decls3-divmod`)

Part 1: a pin variant's fields (`div_mod_slot`, `div_mod_decl_pin`, `div_mod_cert_proofs`) against
`divModDeclPin`, `divModCertProofs`. A variant is a 24-word `EREC` record (`PinSetR`, lane
`romload`): the eight pins at words `0‥7`, the eight certificate slices at `8 + 2j`, `9 + 2j`.
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open L.Rom (PinSetR pinsOf certsOf SliceR HdrR)

namespace L.Ind

open L.Arena

/-- The lookups of this part's proofs. -/
structure DmProg1 (p : Prog) : Prop extends NatEqProg p where
  lErToIw : p.lookup "er_to_iw" = some erToIw
  lErCopy : p.lookup "er_copy" = some erCopy
  lDivModSlot : p.lookup "div_mod_slot" = some divModSlot
  lDivModDeclPin : p.lookup "div_mod_decl_pin" = some divModDeclPinL
  lDivModCertProofs : p.lookup "div_mod_cert_proofs" = some divModCertProofsL

/-! ## Reading a variant's record -/

theorem word_lt32 {k : IdxKind} (x : Idx k) : x.word.toUInt64.toNat < 2 ^ 32 := by
  have := x.word.toNat_lt
  simpa using this

theorem hslice_words {k : IdxKind} (a : Array Word) : ∀ (ws : List Word) (o : Nat),
    (∀ w ∈ ws, w.toNat < 2 ^ 32) → (∀ j < ws.length, a[o + j]? = ws[j]?) →
    (hslice? a o ws.length : Option (List (Idx k))) = some (ws.map decI)
  | [], o, _, _ => by simp [hslice?]
  | w :: ws, o, hlt, hget => by
    simp only [List.length_cons, hslice?_succ]
    have h0 : a[o]? = some w := by simpa using hget 0 (by simp)
    have hw : w.toNat < 2 ^ 32 := hlt w (by simp)
    have ih := hslice_words (k := k) a ws (o + 1) (fun x hx => hlt x (by simp [hx]))
      (fun j hj => by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hget (j + 1) (by simpa using hj))
    simp [hd?, h0, hw, ih]

theorem rdW_grow {m m' : Mem} (hg : IWGrow m m') {i : Word} (hi : i.toNat < erecTop m) :
    rdW (m'.arr64 EREC) i = rdW (m.arr64 EREC) i := by
  simp only [rdW]; rw [hg.2.2.2 i.toNat hi]

theorem erecTop_lt (m : Mem) : erecTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt

theorem SliceR.grow {m m' : Mem} {o l : Word} {hs : List EIdx} (h : SliceR m o l hs)
    (hg : IWGrow m m') : SliceR m' o l hs := by
  obtain ⟨hb, hl, hv⟩ := h
  refine ⟨Nat.le_trans hb hg.2.1, hl, fun i hi' => ?_⟩
  have ht := erecTop_lt m
  have hx : (o + UInt64.ofNat i).toNat = o.toNat + i := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [← hv i hi']
  exact rdW_grow hg (by rw [hx]; omega)

theorem PinSetR.grow {m m' : Mem} {r : Word} {ip : INatOpPinSet} (h : PinSetR m r ip)
    (hg : IWGrow m m') : PinSetR m' r ip := by
  obtain ⟨hb, hp, hh⟩ := h
  refine ⟨Nat.le_trans hb hg.2.1, SliceR.grow hp hg, fun j hj => ?_⟩
  have h1 := hh j hj
  unfold HdrR at h1 ⊢
  have ht := erecTop_lt m
  have e1 : rdW (m'.arr64 EREC) (r + 8 + 2 * UInt64.ofNat j) = rdW (m.arr64 EREC) (r + 8 + 2 * UInt64.ofNat j) := by
    apply rdW_grow hg
    have : (r + 8 + 2 * UInt64.ofNat j).toNat = r.toNat + 8 + 2 * j := by
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
      simp; omega
    omega
  have e2 : rdW (m'.arr64 EREC) (r + 9 + 2 * UInt64.ofNat j) = rdW (m.arr64 EREC) (r + 9 + 2 * UInt64.ofNat j) := by
    apply rdW_grow hg
    have : (r + 9 + 2 * UInt64.ofNat j).toNat = r.toNat + 9 + 2 * j := by
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
      simp; omega
    omega
  rw [e1, e2]
  exact SliceR.grow h1 hg

/-- The `j`-th pin of the record. -/
theorem PinSetR.pin {m : Mem} {r : Word} {ip : INatOpPinSet} (h : PinSetR m r ip) {j : Word}
    (hj : j.toNat < 8) :
    rdW (m.arr64 EREC) (r + j) = ((pinsOf ip).getD j.toNat default).word.toUInt64 := by
  obtain ⟨-, ⟨-, hl, hv⟩, -⟩ := h
  have hl8 : (pinsOf ip).length = 8 := rfl
  have := hv j.toNat (by omega)
  rw [UInt64.ofNat_toNat] at this
  rw [this]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j.toNat < (pinsOf ip).length by omega)]

/-- The `j`-th certificate slice of the record. -/
theorem PinSetR.hdr {m : Mem} {r : Word} {ip : INatOpPinSet} (h : PinSetR m r ip) {j : Word}
    (hj : j.toNat < 8) :
    SliceR m (rdW (m.arr64 EREC) (r + 8 + 2 * j)) (rdW (m.arr64 EREC) (r + 9 + 2 * j))
      ((certsOf ip).getD j.toNat []) := by
  obtain ⟨-, -, hh⟩ := h
  have hl8 : (certsOf ip).length = 8 := rfl
  have := hh j.toNat (by omega)
  unfold HdrR at this
  rw [UInt64.ofNat_toNat] at this
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j.toNat < (certsOf ip).length by omega)] using this

/-! ## `div_mod_slot` -/

/-- The field index of op `c` in a variant. -/
def slotW (m : Mem) (c : Word) : Word :=
  if c = pinW m 22 then 0 else if c = pinW m 24 then 2 else if c = pinW m 25 then 3
  else if c = pinW m 26 then 4 else if c = pinW m 27 then 5 else if c = pinW m 28 then 6
  else if c = pinW m 29 then 7 else 1

theorem slotW_lt (m : Mem) (c : Word) : (slotW m c).toNat < 8 := by
  unfold slotW; repeat' split
  all_goals decide

def divModSlotW (m : Mem) (c : Word) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else some ([slotW m c], m)

theorem divModSlot_specW (p : Prog) (hpin : p.lookup "pin_at" = some pinAtL)
    (hp : p.lookup "div_mod_slot" = some divModSlot) (n : Nat) (s₀ : St) (c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "div_mod_slot" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ divModSlotW s₀.mem c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divModSlot]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, pinAt_pure p hpin n] <;>
    finish (gen := 20) [divModSlotW, slotW]

/-- A returning `div_mod_slot` leaves the memory, and returns the slot. -/
theorem divModSlot_model {p : Prog} (hpin : p.lookup "pin_at" = some pinAtL)
    (hp : p.lookup "div_mod_slot" = some divModSlot) {n : Nat} {m m' : Mem} {c : Word}
    {r : List Word} (h : callW p n "div_mod_slot" [c] m = some (r, m')) :
    m' = m ∧ pinW m 0 ≠ 0 ∧ r = [slotW m c] := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  have hw := callW_model (M := fun mm => divModSlotW mm c) (divModSlot_specW p hpin hp k · c) h
  unfold divModSlotW at hw
  by_cases h0 : pinW m 0 = 0
  · simp [h0] at hw
  · rw [if_neg h0] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨rfl, h0, rfl⟩

/-- The twin's choice of a pin: `divModDeclPin` is the field at the slot. -/
theorem divModDeclPin_run {m : Mem} {a : AState} (hF : PinsFull m a.pins) {c : Word} (hc : H c)
    (ip : INatOpPinSet) :
    (divModDeclPin ip (decI c)).run a = .ok ((pinsOf ip).getD (slotW m c).toNat default, a) := by
  have b21 : ((decI c : NIdx) = decI (pinW m 22)) ↔ c = pinW m 22 := decI_inj_iff hc (hF.names_lt 21 (by decide))
  have b23 : ((decI c : NIdx) = decI (pinW m 24)) ↔ c = pinW m 24 := decI_inj_iff hc (hF.names_lt 23 (by decide))
  have b24 : ((decI c : NIdx) = decI (pinW m 25)) ↔ c = pinW m 25 := decI_inj_iff hc (hF.names_lt 24 (by decide))
  have b25 : ((decI c : NIdx) = decI (pinW m 26)) ↔ c = pinW m 26 := decI_inj_iff hc (hF.names_lt 25 (by decide))
  have b26 : ((decI c : NIdx) = decI (pinW m 27)) ↔ c = pinW m 27 := decI_inj_iff hc (hF.names_lt 26 (by decide))
  have b27 : ((decI c : NIdx) = decI (pinW m 28)) ↔ c = pinW m 28 := decI_inj_iff hc (hF.names_lt 27 (by decide))
  have b28 : ((decI c : NIdx) = decI (pinW m 29)) ↔ c = pinW m 29 := decI_inj_iff hc (hF.names_lt 28 (by decide))
  have p21 : (pinAt 21).run a = .ok (decI (pinW m 22), a) := pinAt_run hF 21 (by decide)
  have p23 : (pinAt 23).run a = .ok (decI (pinW m 24), a) := pinAt_run hF 23 (by decide)
  have p24 : (pinAt 24).run a = .ok (decI (pinW m 25), a) := pinAt_run hF 24 (by decide)
  have p25 : (pinAt 25).run a = .ok (decI (pinW m 26), a) := pinAt_run hF 25 (by decide)
  have p26 : (pinAt 26).run a = .ok (decI (pinW m 27), a) := pinAt_run hF 26 (by decide)
  have p27 : (pinAt 27).run a = .ok (decI (pinW m 28), a) := pinAt_run hF 27 (by decide)
  have p28 : (pinAt 28).run a = .ok (decI (pinW m 29), a) := pinAt_run hF 28 (by decide)
  by_cases e0 : c = pinW m 22
  · have f0 : (decI c = decI (pinW m 22)) = True := eq_true (b21.2 e0)
    have hsl : slotW m c = 0 := by rw [slotW, if_pos e0]
    rw [hsl]
    simp [divModDeclPin, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, pinsOf]
    try rfl
  have f0 : (decI c = decI (pinW m 22)) = False := eq_false (fun h => e0 (b21.1 h))
  by_cases e1 : c = pinW m 24
  · have f1 : (decI c = decI (pinW m 24)) = True := eq_true (b23.2 e1)
    have hsl : slotW m c = 2 := by rw [slotW, if_neg e0, if_pos e1]
    rw [hsl]
    simp [divModDeclPin, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, f1, pinsOf]
    try rfl
  have f1 : (decI c = decI (pinW m 24)) = False := eq_false (fun h => e1 (b23.1 h))
  by_cases e2 : c = pinW m 25
  · have f2 : (decI c = decI (pinW m 25)) = True := eq_true (b24.2 e2)
    have hsl : slotW m c = 3 := by rw [slotW, if_neg e0, if_neg e1, if_pos e2]
    rw [hsl]
    simp [divModDeclPin, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, f1, f2, pinsOf]
    try rfl
  have f2 : (decI c = decI (pinW m 25)) = False := eq_false (fun h => e2 (b24.1 h))
  by_cases e3 : c = pinW m 26
  · have f3 : (decI c = decI (pinW m 26)) = True := eq_true (b25.2 e3)
    have hsl : slotW m c = 4 := by rw [slotW, if_neg e0, if_neg e1, if_neg e2, if_pos e3]
    rw [hsl]
    simp [divModDeclPin, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, f1, f2, f3, pinsOf]
    try rfl
  have f3 : (decI c = decI (pinW m 26)) = False := eq_false (fun h => e3 (b25.1 h))
  by_cases e4 : c = pinW m 27
  · have f4 : (decI c = decI (pinW m 27)) = True := eq_true (b26.2 e4)
    have hsl : slotW m c = 5 := by rw [slotW, if_neg e0, if_neg e1, if_neg e2, if_neg e3, if_pos e4]
    rw [hsl]
    simp [divModDeclPin, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, f1, f2, f3, f4, pinsOf]
    try rfl
  have f4 : (decI c = decI (pinW m 27)) = False := eq_false (fun h => e4 (b26.1 h))
  by_cases e5 : c = pinW m 28
  · have f5 : (decI c = decI (pinW m 28)) = True := eq_true (b27.2 e5)
    have hsl : slotW m c = 6 := by rw [slotW, if_neg e0, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_pos e5]
    rw [hsl]
    simp [divModDeclPin, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, f1, f2, f3, f4, f5, pinsOf]
    try rfl
  have f5 : (decI c = decI (pinW m 28)) = False := eq_false (fun h => e5 (b27.1 h))
  by_cases e6 : c = pinW m 29
  · have f6 : (decI c = decI (pinW m 29)) = True := eq_true (b28.2 e6)
    have hsl : slotW m c = 7 := by rw [slotW, if_neg e0, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5, if_pos e6]
    rw [hsl]
    simp [divModDeclPin, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, f1, f2, f3, f4, f5, f6, pinsOf]
    try rfl
  have f6 : (decI c = decI (pinW m 29)) = False := eq_false (fun h => e6 (b28.1 h))
  have hsl : slotW m c = 1 := by rw [slotW, if_neg e0, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5, if_neg e6]
  rw [hsl]
  simp [divModDeclPin, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, f1, f2, f3, f4, f5, f6, pinsOf]
  try rfl

/-- The twin's choice of a certificate list. -/
theorem divModCertProofs_run {m : Mem} {a : AState} (hF : PinsFull m a.pins) {c : Word} (hc : H c)
    (ip : INatOpPinSet) :
    (divModCertProofs ip (decI c)).run a = .ok ((certsOf ip).getD (slotW m c).toNat [], a) := by
  have b21 : ((decI c : NIdx) = decI (pinW m 22)) ↔ c = pinW m 22 := decI_inj_iff hc (hF.names_lt 21 (by decide))
  have b23 : ((decI c : NIdx) = decI (pinW m 24)) ↔ c = pinW m 24 := decI_inj_iff hc (hF.names_lt 23 (by decide))
  have b24 : ((decI c : NIdx) = decI (pinW m 25)) ↔ c = pinW m 25 := decI_inj_iff hc (hF.names_lt 24 (by decide))
  have b25 : ((decI c : NIdx) = decI (pinW m 26)) ↔ c = pinW m 26 := decI_inj_iff hc (hF.names_lt 25 (by decide))
  have b26 : ((decI c : NIdx) = decI (pinW m 27)) ↔ c = pinW m 27 := decI_inj_iff hc (hF.names_lt 26 (by decide))
  have b27 : ((decI c : NIdx) = decI (pinW m 28)) ↔ c = pinW m 28 := decI_inj_iff hc (hF.names_lt 27 (by decide))
  have b28 : ((decI c : NIdx) = decI (pinW m 29)) ↔ c = pinW m 29 := decI_inj_iff hc (hF.names_lt 28 (by decide))
  have p21 : (pinAt 21).run a = .ok (decI (pinW m 22), a) := pinAt_run hF 21 (by decide)
  have p23 : (pinAt 23).run a = .ok (decI (pinW m 24), a) := pinAt_run hF 23 (by decide)
  have p24 : (pinAt 24).run a = .ok (decI (pinW m 25), a) := pinAt_run hF 24 (by decide)
  have p25 : (pinAt 25).run a = .ok (decI (pinW m 26), a) := pinAt_run hF 25 (by decide)
  have p26 : (pinAt 26).run a = .ok (decI (pinW m 27), a) := pinAt_run hF 26 (by decide)
  have p27 : (pinAt 27).run a = .ok (decI (pinW m 28), a) := pinAt_run hF 27 (by decide)
  have p28 : (pinAt 28).run a = .ok (decI (pinW m 29), a) := pinAt_run hF 28 (by decide)
  by_cases e0 : c = pinW m 22
  · have f0 : (decI c = decI (pinW m 22)) = True := eq_true (b21.2 e0)
    have hsl : slotW m c = 0 := by rw [slotW, if_pos e0]
    rw [hsl]
    simp [divModCertProofs, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, certsOf]
    try rfl
  have f0 : (decI c = decI (pinW m 22)) = False := eq_false (fun h => e0 (b21.1 h))
  by_cases e1 : c = pinW m 24
  · have f1 : (decI c = decI (pinW m 24)) = True := eq_true (b23.2 e1)
    have hsl : slotW m c = 2 := by rw [slotW, if_neg e0, if_pos e1]
    rw [hsl]
    simp [divModCertProofs, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, f1, certsOf]
    try rfl
  have f1 : (decI c = decI (pinW m 24)) = False := eq_false (fun h => e1 (b23.1 h))
  by_cases e2 : c = pinW m 25
  · have f2 : (decI c = decI (pinW m 25)) = True := eq_true (b24.2 e2)
    have hsl : slotW m c = 3 := by rw [slotW, if_neg e0, if_neg e1, if_pos e2]
    rw [hsl]
    simp [divModCertProofs, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, f1, f2, certsOf]
    try rfl
  have f2 : (decI c = decI (pinW m 25)) = False := eq_false (fun h => e2 (b24.1 h))
  by_cases e3 : c = pinW m 26
  · have f3 : (decI c = decI (pinW m 26)) = True := eq_true (b25.2 e3)
    have hsl : slotW m c = 4 := by rw [slotW, if_neg e0, if_neg e1, if_neg e2, if_pos e3]
    rw [hsl]
    simp [divModCertProofs, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, f1, f2, f3, certsOf]
    try rfl
  have f3 : (decI c = decI (pinW m 26)) = False := eq_false (fun h => e3 (b25.1 h))
  by_cases e4 : c = pinW m 27
  · have f4 : (decI c = decI (pinW m 27)) = True := eq_true (b26.2 e4)
    have hsl : slotW m c = 5 := by rw [slotW, if_neg e0, if_neg e1, if_neg e2, if_neg e3, if_pos e4]
    rw [hsl]
    simp [divModCertProofs, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, f1, f2, f3, f4, certsOf]
    try rfl
  have f4 : (decI c = decI (pinW m 27)) = False := eq_false (fun h => e4 (b26.1 h))
  by_cases e5 : c = pinW m 28
  · have f5 : (decI c = decI (pinW m 28)) = True := eq_true (b27.2 e5)
    have hsl : slotW m c = 6 := by rw [slotW, if_neg e0, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_pos e5]
    rw [hsl]
    simp [divModCertProofs, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, f1, f2, f3, f4, f5, certsOf]
    try rfl
  have f5 : (decI c = decI (pinW m 28)) = False := eq_false (fun h => e5 (b27.1 h))
  by_cases e6 : c = pinW m 29
  · have f6 : (decI c = decI (pinW m 29)) = True := eq_true (b28.2 e6)
    have hsl : slotW m c = 7 := by rw [slotW, if_neg e0, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5, if_pos e6]
    rw [hsl]
    simp [divModCertProofs, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, f1, f2, f3, f4, f5, f6, certsOf]
    try rfl
  have f6 : (decI c = decI (pinW m 29)) = False := eq_false (fun h => e6 (b28.1 h))
  have hsl : slotW m c = 1 := by rw [slotW, if_neg e0, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5, if_neg e6]
  rw [hsl]
  simp [divModCertProofs, natDivName, natModName, natGcdName, natLandName, natLorName,
    natXorName, natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand,
    pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, p21, p23, p24, p25, p26, p27, p28, exc_ok_bind', f0, f1, f2, f3, f4, f5, f6, certsOf]
  try rfl


/-! ## The two reads -/

def divModDeclPinW (p : Prog) (n : Nat) (m : Mem) (ps c : Word) : Option (List Word × Mem) :=
  bW (callW p n "div_mod_slot" [c] m) fun r1 m1 => some ([rdW (m1.arr64 EREC) (ps + r1.headD 0)], m1)

theorem divModDeclPin_specW (p : Prog) (hp : p.lookup "div_mod_decl_pin" = some divModDeclPinL)
    (n : Nat) (s₀ : St) (ps c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "div_mod_decl_pin" [ps, c]
    ⦃fun r s' => LocEq s' s₀ ∧ divModDeclPinW p n s₀.mem ps c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divModDeclPinL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "div_mod_slot"] <;>
    finish (gen := 20) [divModDeclPinW, bW, rdW_eq]

theorem divModDeclPin_ref {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}
    (hD : DmProg1 p) (ps c : Word) (ip : INatOpPinSet) :
    CallRef p "div_mod_decl_pin" [ps, c] (fun m a => StageR dn vis fe m a ∧ H c ∧ PinSetR m ps ip)
      (divModDeclPin ip (decI c)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hc, hP⟩ hcall => ?_
  have hw := callW_model (M := fun mm => divModDeclPinW p k mm ps c)
    (divModDeclPin_specW p hD.lDivModDeclPin k · ps c) hcall
  unfold divModDeclPinW at hw
  cases h1 : callW p k "div_mod_slot" [c] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨hm1, h0, hr1⟩ := divModSlot_model hD.lPinAt hD.lDivModSlot h1
  have hm1' := hm1.symm
  subst hm1'
  subst hr1
  have hF := hS.1.pins.full h0
  refine ⟨_, a, divModDeclPin_run hF hc ip, hS, IWGrow.refl _, ?_⟩
  have := PinSetR.pin hP (j := slotW m c) (slotW_lt m c)
  simp only [List.headD_cons]
  rw [this]
  exact ⟨word_lt32 _, decI_word _⟩

theorem sliceR_get {m : Mem} {o l : Word} {hs : List EIdx} (h : SliceR m o l hs)
    (hsz : erecTop m ≤ (m.arr64 EREC).size) (j : Nat) (hj : j < hs.length) :
    (m.arr64 EREC)[o.toNat + j]? = some (hs[j].word.toUInt64) := by
  obtain ⟨hb, hl, hv⟩ := h
  have ht := erecTop_lt m
  have hx : (o + UInt64.ofNat j).toNat = o.toNat + j := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have := hv j hj
  simp only [rdW, hx] at this
  have hlt : o.toNat + j < (m.arr64 EREC).size := by omega
  rw [Array.getElem?_eq_getElem hlt] at this ⊢
  simpa using this

theorem sliceR_hslice {m : Mem} {o l : Word} {hs : List EIdx} (h : SliceR m o l hs)
    (hsz : erecTop m ≤ (m.arr64 EREC).size) :
    (hslice? (erA m) o.toNat l.toNat : Option (List EIdx)) = some hs := by
  have hl := h.2.1
  have := hslice_words (k := IdxKind.expr) (erA m) (hs.map fun x => x.word.toUInt64) o.toNat
    (fun w hw => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hw
      exact word_lt32 x)
    (fun j hj => by
      simp only [List.length_map] at hj
      simp only [erA, List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some]
      exact sliceR_get h hsz j hj)
  rw [hl]
  simpa [List.map_map, Function.comp_def, decI_word] using this

def divModCertProofsW (p : Prog) (n : Nat) (m : Mem) (ps c : Word) : Option (List Word × Mem) :=
  bW (callW p n "div_mod_slot" [c] m) fun r1 m1 =>
  erToIwW n m1 (rdW (m1.arr64 EREC) (ps + 8 + 2 * r1.headD 0))
    (rdW (m1.arr64 EREC) (ps + 9 + 2 * r1.headD 0))

theorem divModCertProofs_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw)
    (hp : p.lookup "div_mod_cert_proofs" = some divModCertProofsL) (n : Nat) (s₀ : St) (ps c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "div_mod_cert_proofs" [ps, c]
    ⦃fun r s' => LocEq s' s₀ ∧ divModCertProofsW p n s₀.mem ps c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divModCertProofsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "div_mod_slot", erToIw_specW2 p ha hc he n] <;>
    finish (gen := 20) [divModCertProofsW, bW, rdW_eq]

theorem divModCertProofs_ref {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}
    (hD : DmProg1 p) (ps c : Word) (ip : INatOpPinSet) :
    CallRef p "div_mod_cert_proofs" [ps, c] (fun m a => StageR dn vis fe m a ∧ H c ∧ PinSetR m ps ip)
      (divModCertProofs ip (decI c))
      (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hc, hP⟩ hcall => ?_
  have hw := callW_model (M := fun mm => divModCertProofsW p k mm ps c)
    (divModCertProofs_specW p hD.lIwAlloc hD.lErCopy hD.lErToIw hD.lDivModCertProofs k · ps c) hcall
  unfold divModCertProofsW at hw
  cases h1 : callW p k "div_mod_slot" [c] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  obtain ⟨hm1, h0, hr1⟩ := divModSlot_model hD.lPinAt hD.lDivModSlot h1
  have hm1' := hm1.symm
  subst hm1'
  subst hr1
  have hF := hS.1.pins.full h0
  simp only [List.headD_cons] at hw
  have hsl := PinSetR.hdr hP (j := slotW m c) (slotW_lt m c)
  have hsz : erecTop m ≤ (m.arr64 EREC).size := hS.2.2.1
  obtain ⟨hS2, hg2, hdec, htop, -⟩ := erToIwW_stage (k := IdxKind.expr) hw hS (by
    have := hsl.1; omega)
  have hd2 : decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat =
      some ((certsOf ip).getD (slotW m c).toNat []) := by
    rw [hdec]; exact sliceR_hslice hsl hsz
  refine ⟨(certsOf ip).getD (slotW m c).toNat [], a, divModCertProofs_run hF hc ip, hS2, hg2, ?_⟩
  unfold decRL
  rw [getD0, show (0 + 1 : Nat) = 1 from rfl, getD1]
  exact ⟨hd2, by omega⟩

@[refines ConRon.Arena.divModDeclPin]
theorem divModDeclPin_refines {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}
    (hD : DmProg1 p) (ps c : Word) (ip : INatOpPinSet) :
    RefAM p "div_mod_decl_pin" [ps, c] (fun m a => StageR dn vis fe m a ∧ H c ∧ PinSetR m ps ip)
      (divModDeclPin ip (decI c)) (KeepPost dn vis fe decW0E) :=
  (divModDeclPin_ref hD ps c ip).refAM

@[refines ConRon.Arena.divModCertProofs]
theorem divModCertProofs_refines {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {p : Prog} (hD : DmProg1 p) (ps c : Word) (ip : INatOpPinSet) :
    RefAM p "div_mod_cert_proofs" [ps, c] (fun m a => StageR dn vis fe m a ∧ H c ∧ PinSetR m ps ip)
      (divModCertProofs ip (decI c)) (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) :=
  (divModCertProofs_ref hD ps c ip).refAM

end L.Ind
