module

public import ConAgua.Arena.DeclNatEq
import ConAgua.Arena.RecCheckSpec.ErToIwWStage
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import ConAgua.Rom.PinSets
import all ConAgua.Arena.DeclArmsNat
import all ConAgua.Arena.IndIface

@[expose] public section

/-!
# DivModTypePins: `ConRon.Arena.divModCertProofs`, `ConRon.Arena.divModDeclPin`, `ConRon.Arena.divModTypePins`

The refinement theorems `divModTypePins_refines`, `divModDeclPin_refines`, `divModCertProofs_refines` and the lemmas only they use.
-/

set_option experimental.vcgen true

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
  lDivModTypePins : p.lookup "div_mod_type_pins" = some divModTypePinsL

/-! ## Reading a variant's record -/

theorem dmWord_lt32 {k : IdxKind} (x : Idx k) : x.word.toUInt64.toNat < 2 ^ 32 := by
  have := x.word.toNat_lt
  simpa using this

theorem hslice_words {k : IdxKind} (a : Array Word) : ∀ (ws : List Word) (o : Nat),
    (∀ w ∈ ws, w.toNat < 2 ^ 32) → (∀ j < ws.length, a[o + j]? = ws[j]?) →
    (hslice? (aread a) o ws.length : Option (List (Idx k))) = some (ws.map decI) := by
  sorry

theorem rdW_erec_grow {m m' : Mem} (hg : IWGrow m m') {i : Word} (hi : i.toNat < erecTop m) :
    rdW (m'.arr64 EREC) i = rdW (m.arr64 EREC) i := by
  simp only [rdW]; rw [hg.erGet i.toNat hi]

theorem erecTop_lt (m : Mem) : erecTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt

/-- **`EREC⦃a⦄` below the tier-0 top is the tier-0 word `a`** (the pool is addressable: `IWOK.erCap`),
so the ROM's relations (`PinSetR`, `TPinsR`, `SliceR`, over `m.arr64 EREC`) read what L reads. -/
theorem erRd_lo {m : Mem} (h : IWOK m) {a : Word} (ha : a.toNat < erecTop m) :
    erRd m a = rdW (m.arr64 EREC) a := by
  have h1 := h.er; have h2 := h.erCap
  have h40 : a.toNat < 2 ^ 40 := by unfold erTop at h1; unfold erecTop at ha; omega
  have e1 : a >>> 40 = 0 := UInt64.toNat_inj.mp (by rw [L.Arena.tag_tier_toNat]; simp; omega)
  have e2 : a &&& 1099511627775 = a :=
    UInt64.toNat_inj.mp (by rw [L.Arena.tag_idx_toNat]; omega)
  simp only [erRd, e1, e2]
  rfl

theorem SliceR.grow {m m' : Mem} {o l : Word} {hs : List EIdx} (h : SliceR m o l hs)
    (hg : IWGrow m m') : SliceR m' o l hs := by
  obtain ⟨hb, hl, hv⟩ := h
  refine ⟨Nat.le_trans hb hg.er, hl, fun i hi' => ?_⟩
  have ht := erecTop_lt m
  have hx : (o + UInt64.ofNat i).toNat = o.toNat + i := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [← hv i hi']
  exact rdW_erec_grow hg (by rw [hx]; omega)

theorem PinSetR.grow {m m' : Mem} {r : Word} {ip : INatOpPinSet} (h : PinSetR m r ip)
    (hg : IWGrow m m') : PinSetR m' r ip :=
  L.Rom.PinSetR.keep h ⟨hg.er, hg.erGet⟩

/-- The `j`-th pin of the record. -/
theorem PinSetR.pin {m : Mem} {r : Word} {ip : INatOpPinSet} (h : PinSetR m r ip) {j : Word}
    (hj : j.toNat < 8) :
    rdW (m.arr64 EREC) (r + j) = ((pinsOf ip).getD j.toNat default).word.toUInt64 := by
  obtain ⟨-, ⟨-, hl, hv⟩, -, -⟩ := h
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
  obtain ⟨-, -, hh, -⟩ := h
  have hl8 : (certsOf ip).length = 8 := rfl
  have := hh j.toNat (by omega)
  unfold HdrR at this
  rw [UInt64.ofNat_toNat] at this
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j.toNat < (certsOf ip).length by omega)] using this

/-- The `j`-th type-pin slice of the record. -/
theorem PinSetR.thdr {m : Mem} {r : Word} {ip : INatOpPinSet} (h : PinSetR m r ip) {j : Word}
    (hj : j.toNat < 8) :
    L.Rom.TPinsR m (rdW (m.arr64 EREC) (r + 24 + 2 * j)) (rdW (m.arr64 EREC) (r + 25 + 2 * j))
      ((L.Rom.tpinsOf ip).getD j.toNat []) := by
  obtain ⟨-, -, -, hh⟩ := h
  have hl8 : (L.Rom.tpinsOf ip).length = 8 := rfl
  have := hh j.toNat (by omega)
  unfold L.Rom.THdrR at this
  rw [UInt64.ofNat_toNat] at this
  simpa [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show j.toNat < (L.Rom.tpinsOf ip).length by omega)] using this

/-! ## `div_mod_slot` -/

/-- The field index of op `c` in a variant. -/
def dmSlotW (m : Mem) (c : Word) : Word :=
  if c = pinW m 22 then 0 else if c = pinW m 24 then 2 else if c = pinW m 25 then 3
  else if c = pinW m 26 then 4 else if c = pinW m 27 then 5 else if c = pinW m 28 then 6
  else if c = pinW m 29 then 7 else 1

theorem slotW_lt (m : Mem) (c : Word) : (dmSlotW m c).toNat < 8 := by
  unfold dmSlotW; repeat' split
  all_goals decide

def divModSlotW (m : Mem) (c : Word) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else some ([dmSlotW m c], m)

theorem divModSlot_specW (p : Prog) (hpin : p.lookup "pin_at" = some pinAtL)
    (hp : p.lookup "div_mod_slot" = some divModSlot) (n : Nat) (s₀ : St) (c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "div_mod_slot" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ divModSlotW s₀.mem c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divModSlot]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, pinAt_any p hpin n] <;>
    finish (gen := 20) [divModSlotW, dmSlotW]

/-- A returning `div_mod_slot` leaves the memory, and returns the slot. -/
theorem divModSlot_model {p : Prog} (hpin : p.lookup "pin_at" = some pinAtL)
    (hp : p.lookup "div_mod_slot" = some divModSlot) {n : Nat} {m m' : Mem} {c : Word}
    {r : List Word} (h : callW p n "div_mod_slot" [c] m = some (r, m')) :
    m' = m ∧ pinW m 0 ≠ 0 ∧ r = [dmSlotW m c] := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k =>
  have hw := callW_model (M := fun mm => divModSlotW mm c) (divModSlot_specW p hpin hp k · c) h
  unfold divModSlotW at hw
  by_cases h0 : pinW m 0 = 0
  · simp [h0] at hw
  · rw [ite_eq_right h0] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨rfl, h0, rfl⟩

/-- **The twin's choice by the op `c`**: the field of `xs` at the slot `dmSlotW`. -/
theorem dmChoose_run {γ : Type} (xs : List γ) (d : γ) {m : Mem} {a : AState} (hF : PinsFull m a.pins) {c : Word} (hc : H c) :
    (do
      if (decI c : NIdx) == (← natDivName) then pure (xs.getD 0 d)
      else if decI c == (← natGcdName) then pure (xs.getD 2 d)
      else if decI c == (← natLandName) then pure (xs.getD 3 d)
      else if decI c == (← natLorName) then pure (xs.getD 4 d)
      else if decI c == (← natXorName) then pure (xs.getD 5 d)
      else if decI c == (← natShiftLeftName) then pure (xs.getD 6 d)
      else if decI c == (← natShiftRightName) then pure (xs.getD 7 d)
      else pure (xs.getD 1 d) : AM γ).run a = .ok (xs.getD (dmSlotW m c).toNat d, a) := by
  simp only [natDivName, natGcdName, natLandName, natLorName, natXorName, natShiftLeftName, natShiftRightName,
    pinNatDiv, pinNatGcd, pinNatLand, pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT, dmSlotW]
  have p : ∀ i (hi : i < 51), (pinAt i).run a = .ok (decI (pinW m (1 + i)), a) := pinAt_run hF
  have b : ∀ i (hi : i < 51), ((decI c : NIdx) == decI (pinW m (1 + i))) = decide (c = pinW m (1 + i)) :=
    fun i hi => decI_beq _ _ hc (hF.names_lt i hi)
  simp only [StateT.run_bind, p 21 (by decide), exc_ok_bind', b 21 (by decide), decide_eq_true_eq]
  by_cases e0 : c = pinW m 22
  · rw [ite_eq_left e0, ite_eq_left e0]; rfl
  rw [ite_eq_right e0, ite_eq_right e0]
  simp only [StateT.run_bind, p 23 (by decide), exc_ok_bind', b 23 (by decide), decide_eq_true_eq]
  by_cases e1 : c = pinW m 24
  · rw [ite_eq_left e1, ite_eq_left e1]; rfl
  rw [ite_eq_right e1, ite_eq_right e1]
  simp only [StateT.run_bind, p 24 (by decide), exc_ok_bind', b 24 (by decide), decide_eq_true_eq]
  by_cases e2 : c = pinW m 25
  · rw [ite_eq_left e2, ite_eq_left e2]; rfl
  rw [ite_eq_right e2, ite_eq_right e2]
  simp only [StateT.run_bind, p 25 (by decide), exc_ok_bind', b 25 (by decide), decide_eq_true_eq]
  by_cases e3 : c = pinW m 26
  · rw [ite_eq_left e3, ite_eq_left e3]; rfl
  rw [ite_eq_right e3, ite_eq_right e3]
  simp only [StateT.run_bind, p 26 (by decide), exc_ok_bind', b 26 (by decide), decide_eq_true_eq]
  by_cases e4 : c = pinW m 27
  · rw [ite_eq_left e4, ite_eq_left e4]; rfl
  rw [ite_eq_right e4, ite_eq_right e4]
  simp only [StateT.run_bind, p 27 (by decide), exc_ok_bind', b 27 (by decide), decide_eq_true_eq]
  by_cases e5 : c = pinW m 28
  · rw [ite_eq_left e5, ite_eq_left e5]; rfl
  rw [ite_eq_right e5, ite_eq_right e5]
  simp only [StateT.run_bind, p 28 (by decide), exc_ok_bind', b 28 (by decide), decide_eq_true_eq]
  by_cases e6 : c = pinW m 29
  · rw [ite_eq_left e6, ite_eq_left e6]; rfl
  rw [ite_eq_right e6, ite_eq_right e6]
  rfl

/-- The twin's choice of a pin: `divModDeclPin` is the field at the slot. -/
theorem divModDeclPin_run {m : Mem} {a : AState} (hF : PinsFull m a.pins) {c : Word} (hc : H c)
    (ip : INatOpPinSet) :
    (divModDeclPin ip (decI c)).run a = .ok ((pinsOf ip).getD (dmSlotW m c).toNat default, a) :=
  dmChoose_run (pinsOf ip) default hF hc

/-- The twin's choice of a certificate list. -/
theorem divModCertProofs_run {m : Mem} {a : AState} (hF : PinsFull m a.pins) {c : Word} (hc : H c)
    (ip : INatOpPinSet) :
    (divModCertProofs ip (decI c)).run a = .ok ((certsOf ip).getD (dmSlotW m c).toNat [], a) :=
  dmChoose_run (certsOf ip) [] hF hc

/-- The twin's choice of a type-pin list. -/
theorem divModTypePins_run {m : Mem} {a : AState} (hF : PinsFull m a.pins) {c : Word} (hc : H c)
    (ip : INatOpPinSet) :
    (divModTypePins ip (decI c)).run a = .ok ((L.Rom.tpinsOf ip).getD (dmSlotW m c).toNat [], a) :=
  dmChoose_run (L.Rom.tpinsOf ip) [] hF hc

/-- A type-pin slice `(r[0], r[1])` of `EREC` holds `tps`. -/
def decTP (m : Mem) (r : List Word) (tps : List (NIdx × EIdx)) : Prop :=
  L.Rom.TPinsR m (r.headD 0) (r.tail.headD 0) tps

theorem decTP.grow {m m' : Mem} {r : List Word} {tps : List (NIdx × EIdx)} (h : decTP m r tps)
    (hg : IWGrow m m') : decTP m' r tps :=
  L.Rom.TPinsR.keep h ⟨hg.er, hg.erGet⟩

/-! ## The reads -/

/-- **`div_mod_decl_pin` is its model `divModDeclPinW`** (generated). -/
l_model divModDeclPin_specW (p : Prog) (hp : p.lookup "div_mod_decl_pin" = some divModDeclPinL)
  fns [hp ↦ divModDeclPinW list]
  specs [callW_spec p n "div_mod_slot"]
  grind [arena_grind] heartbeats 1600000 bind ntBW

theorem divModDeclPin_ref {vis : Word} {fe : IFEnv} {p : Prog}
    (hD : DmProg1 p) (ps c : Word) (ip : INatOpPinSet) :
    CallRef p "div_mod_decl_pin" [ps, c] (fun m a => StageR vis fe m a ∧ H c ∧ PinSetR m ps ip)
      (divModDeclPin ip (decI c)) (KeepPost vis fe decW0E) := by
  sorry

/-- **`div_mod_type_pins` is its model `divModTypePinsW`** (generated). -/
l_model divModTypePins_specW (p : Prog) (hp : p.lookup "div_mod_type_pins" = some divModTypePinsL)
  fns [hp ↦ divModTypePinsW list]
  specs [callW_spec p n "div_mod_slot"]
  grind [arena_grind] heartbeats 1600000 bind ntBW

theorem divModTypePins_ref {vis : Word} {fe : IFEnv} {p : Prog}
    (hD : DmProg1 p) (ps c : Word) (ip : INatOpPinSet) :
    CallRef p "div_mod_type_pins" [ps, c] (fun m a => StageR vis fe m a ∧ H c ∧ PinSetR m ps ip)
      (divModTypePins ip (decI c)) (KeepPost vis fe decTP) := by
  sorry

@[refines ConRon.Arena.divModTypePins]
theorem divModTypePins_refines {vis : Word} {fe : IFEnv}
    {p : Prog} (hD : DmProg1 p) (ps c : Word) (ip : INatOpPinSet) :
    RefAM p "div_mod_type_pins" [ps, c] (fun m a => StageR vis fe m a ∧ H c ∧ PinSetR m ps ip)
      (divModTypePins ip (decI c)) (KeepPost vis fe decTP) :=
  (divModTypePins_ref hD ps c ip).refAM

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
  sorry

/-- **`div_mod_cert_proofs` is its model `divModCertProofsW`** (generated). -/
l_model divModCertProofs_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw) (hp : p.lookup "div_mod_cert_proofs" = some divModCertProofsL)
  fns [hp ↦ divModCertProofsW list]
  specs [callW_spec p n "div_mod_slot", erToIw_specW p ha hc he n]
  grind [arena_grind] heartbeats 1600000 bind ntBW

theorem divModCertProofs_ref {vis : Word} {fe : IFEnv} {p : Prog}
    (hD : DmProg1 p) (ps c : Word) (ip : INatOpPinSet) :
    CallRef p "div_mod_cert_proofs" [ps, c] (fun m a => StageR vis fe m a ∧ H c ∧ PinSetR m ps ip)
      (divModCertProofs ip (decI c))
      (KeepPost vis fe (decRL (fun m => decHL m) 0)) := by
  sorry

@[refines ConRon.Arena.divModDeclPin]
theorem divModDeclPin_refines {vis : Word} {fe : IFEnv} {p : Prog}
    (hD : DmProg1 p) (ps c : Word) (ip : INatOpPinSet) :
    RefAM p "div_mod_decl_pin" [ps, c] (fun m a => StageR vis fe m a ∧ H c ∧ PinSetR m ps ip)
      (divModDeclPin ip (decI c)) (KeepPost vis fe decW0E) :=
  (divModDeclPin_ref hD ps c ip).refAM

@[refines ConRon.Arena.divModCertProofs]
theorem divModCertProofs_refines {vis : Word} {fe : IFEnv}
    {p : Prog} (hD : DmProg1 p) (ps c : Word) (ip : INatOpPinSet) :
    RefAM p "div_mod_cert_proofs" [ps, c] (fun m a => StageR vis fe m a ∧ H c ∧ PinSetR m ps ip)
      (divModCertProofs ip (decI c)) (KeepPost vis fe (decRL (fun m => decHL m) 0)) :=
  (divModCertProofs_ref hD ps c ip).refAM

end L.Ind
