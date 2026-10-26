import ConAgua.Arena.DeclNatEq
import ConAgua.Arena.RecCheckSpec
import ConAgua.Rom.PinSets
import ConAgua.L.ModelGen

/-!
# The `Nat.div` family's pin gate, bottom up (lane `decls3`, helper `decls3-divmod`)

Part 1: a pin variant's fields (`div_mod_slot`, `div_mod_decl_pin`, `div_mod_cert_proofs`) against
`divModDeclPin`, `divModCertProofs`. A variant is a 40-word `EREC` record (`PinSetR`, lane
`romload`): the eight pins at words `0‥7`, the eight certificate slices at `8 + 2j`, `9 + 2j`, the
eight type-pin slices (of pairs) at `24 + 2j`, `25 + 2j`.
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
    (hslice? a o ws.length : Option (List (Idx k))) = some (ws.map decI)
  | [], o, _, _ => by simp [hslice?]
  | w :: ws, o, hlt, hget => by
    simp only [List.length_cons, hslice?_succ]
    have h0 : a[o]? = some w := by simpa using hget 0 (by simp)
    have hw : w.toNat < 2 ^ 32 := hlt w (by simp)
    have ih := hslice_words (k := k) a ws (o + 1) (fun x hx => hlt x (by simp [hx]))
      (fun j hj => by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hget (j + 1) (by simpa using hj))
    simp [hd?, h0, hw, ih]

theorem rdW_erec_grow {m m' : Mem} (hg : IWGrow m m') {i : Word} (hi : i.toNat < erecTop m) :
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
  exact rdW_erec_grow hg (by rw [hx]; omega)

theorem PinSetR.grow {m m' : Mem} {r : Word} {ip : INatOpPinSet} (h : PinSetR m r ip)
    (hg : IWGrow m m') : PinSetR m' r ip :=
  L.Rom.PinSetR.keep h ⟨hg.2.1, hg.2.2.2⟩

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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, pinAt_pure p hpin n] <;>
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
  · rw [if_neg h0] at hw
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
    fun i hi => decI_beq_word hc (hF.names_lt i hi)
  simp only [StateT.run_bind, p 21 (by decide), exc_ok_bind', b 21 (by decide), decide_eq_true_eq]
  by_cases e0 : c = pinW m 22
  · rw [if_pos e0, if_pos e0]; rfl
  rw [if_neg e0, if_neg e0]
  simp only [StateT.run_bind, p 23 (by decide), exc_ok_bind', b 23 (by decide), decide_eq_true_eq]
  by_cases e1 : c = pinW m 24
  · rw [if_pos e1, if_pos e1]; rfl
  rw [if_neg e1, if_neg e1]
  simp only [StateT.run_bind, p 24 (by decide), exc_ok_bind', b 24 (by decide), decide_eq_true_eq]
  by_cases e2 : c = pinW m 25
  · rw [if_pos e2, if_pos e2]; rfl
  rw [if_neg e2, if_neg e2]
  simp only [StateT.run_bind, p 25 (by decide), exc_ok_bind', b 25 (by decide), decide_eq_true_eq]
  by_cases e3 : c = pinW m 26
  · rw [if_pos e3, if_pos e3]; rfl
  rw [if_neg e3, if_neg e3]
  simp only [StateT.run_bind, p 26 (by decide), exc_ok_bind', b 26 (by decide), decide_eq_true_eq]
  by_cases e4 : c = pinW m 27
  · rw [if_pos e4, if_pos e4]; rfl
  rw [if_neg e4, if_neg e4]
  simp only [StateT.run_bind, p 27 (by decide), exc_ok_bind', b 27 (by decide), decide_eq_true_eq]
  by_cases e5 : c = pinW m 28
  · rw [if_pos e5, if_pos e5]; rfl
  rw [if_neg e5, if_neg e5]
  simp only [StateT.run_bind, p 28 (by decide), exc_ok_bind', b 28 (by decide), decide_eq_true_eq]
  by_cases e6 : c = pinW m 29
  · rw [if_pos e6, if_pos e6]; rfl
  rw [if_neg e6, if_neg e6]
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
  L.Rom.TPinsR.keep h ⟨hg.2.1, hg.2.2.2⟩

/-! ## The reads -/

/-- **`div_mod_decl_pin` is its model `divModDeclPinW`** (generated). -/
l_model divModDeclPin_specW (p : Prog) (hp : p.lookup "div_mod_decl_pin" = some divModDeclPinL)
  fns [hp ↦ divModDeclPinW list]
  specs [callW_spec p n "div_mod_slot"]
  grind [arena_grind] heartbeats 1600000 bind ntBW simp [ntBW, rdW_eq]

theorem divModDeclPin_ref {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}
    (hD : DmProg1 p) (ps c : Word) (ip : INatOpPinSet) :
    CallRef p "div_mod_decl_pin" [ps, c] (fun m a => StageR dn vis fe m a ∧ H c ∧ PinSetR m ps ip)
      (divModDeclPin ip (decI c)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hc, hP⟩ hcall => ?_
  have hw := callW_model (M := fun mm => divModDeclPinW p (k + 1) mm ps c)
    (divModDeclPin_specW p hD.lDivModDeclPin (k + 1) · ps c) hcall
  rw [divModDeclPinW.arm1] at hw
  replace hw := ntBW_some hw; obtain ⟨r1, m1, h1, hw⟩ := hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨hm1, h0, hr1⟩ := divModSlot_model hD.lPinAt hD.lDivModSlot h1
  have hm1' := hm1.symm
  subst hm1'
  subst hr1
  have hF := hS.1.pins.full h0
  refine ⟨_, a, divModDeclPin_run hF hc ip, hS, IWGrow.refl _, ?_⟩
  have := PinSetR.pin hP (j := dmSlotW m c) (slotW_lt m c)
  simp only [List.headD_cons]
  rw [this]
  exact ⟨dmWord_lt32 _, decI_word _⟩

/-- **`div_mod_type_pins` is its model `divModTypePinsW`** (generated). -/
l_model divModTypePins_specW (p : Prog) (hp : p.lookup "div_mod_type_pins" = some divModTypePinsL)
  fns [hp ↦ divModTypePinsW list]
  specs [callW_spec p n "div_mod_slot"]
  grind [arena_grind] heartbeats 1600000 bind ntBW simp [ntBW, rdW_eq]

theorem divModTypePins_ref {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}
    (hD : DmProg1 p) (ps c : Word) (ip : INatOpPinSet) :
    CallRef p "div_mod_type_pins" [ps, c] (fun m a => StageR dn vis fe m a ∧ H c ∧ PinSetR m ps ip)
      (divModTypePins ip (decI c)) (KeepPost dn vis fe decTP) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hc, hP⟩ hcall => ?_
  have hw := callW_model (M := fun mm => divModTypePinsW p (k + 1) mm ps c)
    (divModTypePins_specW p hD.lDivModTypePins (k + 1) · ps c) hcall
  rw [divModTypePinsW.arm1] at hw
  replace hw := ntBW_some hw; obtain ⟨r1, m1, h1, hw⟩ := hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨hm1, h0, hr1⟩ := divModSlot_model hD.lPinAt hD.lDivModSlot h1
  have hm1' := hm1.symm
  subst hm1'
  subst hr1
  have hF := hS.1.pins.full h0
  refine ⟨_, a, divModTypePins_run hF hc ip, hS, IWGrow.refl _, ?_⟩
  have := PinSetR.thdr hP (j := dmSlotW m c) (slotW_lt m c)
  simpa [decTP] using this

@[refines ConRon.Arena.divModTypePins]
theorem divModTypePins_refines {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {p : Prog} (hD : DmProg1 p) (ps c : Word) (ip : INatOpPinSet) :
    RefAM p "div_mod_type_pins" [ps, c] (fun m a => StageR dn vis fe m a ∧ H c ∧ PinSetR m ps ip)
      (divModTypePins ip (decI c)) (KeepPost dn vis fe decTP) :=
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
  have hl := h.2.1
  have := hslice_words (k := IdxKind.expr) (erA m) (hs.map fun x => x.word.toUInt64) o.toNat
    (fun w hw => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hw
      exact dmWord_lt32 x)
    (fun j hj => by
      simp only [List.length_map] at hj
      simp only [erA, List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some]
      exact sliceR_get h hsz j hj)
  rw [hl]
  simpa [List.map_map, Function.comp_def, decI_word] using this

/-- **`div_mod_cert_proofs` is its model `divModCertProofsW`** (generated). -/
l_model divModCertProofs_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw) (hp : p.lookup "div_mod_cert_proofs" = some divModCertProofsL)
  fns [hp ↦ divModCertProofsW list]
  specs [callW_spec p n "div_mod_slot", erToIw_specW p ha hc he n]
  grind [arena_grind] heartbeats 1600000 bind ntBW simp [ntBW, rdW_eq]

theorem divModCertProofs_ref {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}
    (hD : DmProg1 p) (ps c : Word) (ip : INatOpPinSet) :
    CallRef p "div_mod_cert_proofs" [ps, c] (fun m a => StageR dn vis fe m a ∧ H c ∧ PinSetR m ps ip)
      (divModCertProofs ip (decI c))
      (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hc, hP⟩ hcall => ?_
  have hw := callW_model (M := fun mm => divModCertProofsW p (k + 1) mm ps c)
    (divModCertProofs_specW p hD.lIwAlloc hD.lErCopy hD.lErToIw hD.lDivModCertProofs (k + 1) · ps c) hcall
  rw [divModCertProofsW.arm1] at hw
  replace hw := ntBW_some hw; obtain ⟨r1, m1, h1, hw⟩ := hw
  obtain ⟨hm1, h0, hr1⟩ := divModSlot_model hD.lPinAt hD.lDivModSlot h1
  have hm1' := hm1.symm
  subst hm1'
  subst hr1
  have hF := hS.1.pins.full h0
  simp only [List.headD_cons] at hw
  obtain ⟨r2, m2, he2, he⟩ := ntBW_some hw
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hsl := PinSetR.hdr hP (j := dmSlotW m c) (slotW_lt m c)
  have hsz : erecTop m ≤ (m.arr64 EREC).size := hS.2.2.1
  obtain ⟨hS2, hg2, hdec, htop, -⟩ := erToIwW_stage (k := IdxKind.expr) he2 hS (Or.inr (by
    have := hsl.1; omega))
  have hd2 : decHL m2 (r2.headD 0).toNat (r2.tail.headD 0).toNat =
      some ((certsOf ip).getD (dmSlotW m c).toNat []) := by
    rw [hdec]; exact sliceR_hslice hsl hsz
  refine ⟨(certsOf ip).getD (dmSlotW m c).toNat [], a, divModCertProofs_run hF hc ip, hS2, hg2, ?_⟩
  unfold decRL
  rw [ntGetD0, show (0 + 1 : Nat) = 1 from rfl, ntGetD1]
  simp only [List.headD_cons, List.tail_cons]
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
