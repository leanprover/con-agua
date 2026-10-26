import ConAgua.Rom.CIReadRefBlock

/-!
# The ROM constant readers: the region's layout, the slot and the fresh memo (helper `decls4-rom`)

`rci_slot(s)` returns a position where the ROM holds the slot's entry (`ciEntries[s]`), for a
buffer that starts with `romData` (`slotCall`); `rci_fresh()` empties the expression memo and
puts the level stack at its base (`freshCall`).
-/


open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-! ## The offset table -/

theorem ciTable_len : ∀ (start : Nat) (es : List (List UInt8)), (ciTable start es).length = 8 * es.length
  | _, [] => rfl
  | start, e :: es => by simp [ciTable, ciTable_len _ es, u64B]; omega

/-- Slot `s`'s offset word. -/
theorem ciTable_drop : ∀ (es : List (List UInt8)) (start s : Nat), s < es.length →
    ∃ rest, (ciTable start es).drop (8 * s) =
      u64B (start + ((es.take s).map List.length).sum) ++ rest
  | [], _, _, h => by simp at h
  | e :: es, start, 0, _ => ⟨ciTable (start + e.length) es, by simp [ciTable]⟩
  | e :: es, start, s + 1, h => by
    obtain ⟨rest, hr⟩ := ciTable_drop es (start + e.length) s (by simp at h; omega)
    refine ⟨rest, ?_⟩
    have : 8 * (s + 1) = 8 + 8 * s := by omega
    rw [this, ciTable, ← List.drop_drop, List.drop_left' (by simp [u64B]), hr]
    simp [Nat.add_assoc]

/-- Entry `s` in the concatenation. -/
theorem flatten_drop : ∀ (es : List (List UInt8)) (s : Nat) (hs : s < es.length),
    ∃ rest, es.flatten.drop ((es.take s).map List.length).sum = es[s] ++ rest
  | [], _, h => by simp at h
  | e :: es, 0, _ => ⟨es.flatten, by simp⟩
  | e :: es, s + 1, h => by
    obtain ⟨rest, hr⟩ := flatten_drop es s (by simp at h; omega)
    refine ⟨rest, ?_⟩
    simp only [List.flatten_cons, List.take_succ_cons, List.map_cons, List.sum_cons,
      List.getElem_cons_succ]
    rw [← List.drop_drop, List.drop_left, hr]

theorem flatten_take_le (es : List (List UInt8)) (s : Nat) :
    ((es.take s).map List.length).sum ≤ es.flatten.length := by
  have : ((es.take s).map List.length).sum = (es.take s).flatten.length := by
    simp [List.length_flatten]
  rw [this]
  calc (es.take s).flatten.length ≤ (es.take s).flatten.length + (es.drop s).flatten.length :=
        Nat.le_add_right _ _
    _ = es.flatten.length := by rw [← List.length_append, ← List.flatten_append, List.take_append_drop]

theorem ciEntries_len : ciEntries.length = 31 := by
  simp [ciEntries, basisKinds, romCiVals, romCvVals, romExprVals]

theorem ciOff_toNat :
    ciOff.toNat = (encNames pinNames ++ encNames reservedBasisNameValues).length := by
  have := romData_len
  simp only [romData, List.length_append] at this
  simp only [ciOff, List.length_append, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

/-- **Where slot `s`'s entry is**: from the table word at `ciOff + 8 s`. -/
theorem slot_pos {rom : List UInt8} (hr : RomOK rom) (rest : List UInt8) (hrom : rom = romData ++ rest)
    (s : Word) (hs : s.toNat < 31) :
    ∃ rest', rom.drop (ciOff + u64W rom (ciOff + 8 * s)).toNat = ciEntries[s.toNat]'(by
      rw [ciEntries_len]; exact hs) ++ rest' := by
  have hrl := hr; simp only [RomOK] at hrl
  have hlenD := romData_len
  have hpre : rom.drop ciOff.toNat = romCIData ++ (encItems [] (itemsAllPins romPins) ++ rest) := by
    rw [hrom, ciOff_toNat, romData]; simp [List.append_assoc]
  have hlenR : ciOff.toNat + romCIData.length ≤ rom.length := by
    rw [hrom, ciOff_toNat]; simp [romData]; omega
  have hT := ciTable_len (8 * ciSlots) ciEntries
  rw [ciEntries_len] at hT
  obtain ⟨tr, htr⟩ := ciTable_drop ciEntries (8 * ciSlots) s.toNat (by rw [ciEntries_len]; exact hs)
  have hsum := flatten_take_le ciEntries s.toNat
  have hRD : romCIData.length = 8 * 31 + ciEntries.flatten.length := by
    simp [romCIData, hT]
  have h8s : (ciOff + 8 * s).toNat = ciOff.toNat + 8 * s.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  have hd1 : rom.drop (ciOff + 8 * s).toNat = u64B (8 * ciSlots + ((ciEntries.take s.toNat).map
      List.length).sum) ++ (tr ++ (ciEntries.flatten ++ (encItems [] (itemsAllPins romPins) ++ rest))) := by
    rw [h8s, ← List.drop_drop, hpre, romCIData, List.append_assoc,
      List.drop_append_of_le_length (by rw [hT]; omega), htr]
    simp [List.append_assoc]
  have hN : 8 * ciSlots + ((ciEntries.take s.toNat).map List.length).sum < 2 ^ 64 := by
    simp only [ciSlots]; omega
  rw [u64W_of_drop rom _ _ _ hd1 hN hr]
  have hP : (ciOff + UInt64.ofNat (8 * ciSlots + ((ciEntries.take s.toNat).map List.length).sum)).toNat =
      ciOff.toNat + 8 * 31 + ((ciEntries.take s.toNat).map List.length).sum := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hN]; simp only [ciSlots]; omega
  obtain ⟨fr, hfr⟩ := flatten_drop ciEntries s.toNat (by rw [ciEntries_len]; exact hs)
  refine ⟨fr ++ (encItems [] (itemsAllPins romPins) ++ rest), ?_⟩
  rw [hP, Nat.add_assoc, ← List.drop_drop, hpre, romCIData, List.append_assoc, ← List.drop_drop,
    List.drop_left' (by rw [hT])]
  rw [List.drop_append_of_le_length hsum, hfr, List.append_assoc]

/-! ## `rci_slot`, `rci_fresh` -/

section calls
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p)
include hL

theorem slotCall {n : Nat} {m m' : Mem} {s : Word} {r : List Word}
    (hc : callW p n "rci_slot" [s] m = some (r, m')) :
    m' = m ∧ r = [ciOff + u64W rom (ciOff + 8 * s)] := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => slotW p n mq s) (slot_specW rom p hL n · s) hc
  unfold slotW at hw
  replace hw := rdU_some hL hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  exact ⟨hw.2.symm, hw.1.symm⟩

theorem freshCall {m₀ : Mem} {a₀ : AState} {T : Nat} {n : Nat} {m m' : Mem} {a : AState} {r : List Word}
    (hI : RInv m₀ a₀ T m a) (hc : callW p n "rci_fresh" [] m = some (r, m')) :
    RInv m₀ a₀ T m' a ∧ MemoR m' [] (∅ : EMemo) ∧ stkTop m' = 0 ∧ m'.arr64 EREC = m.arr64 EREC ∧
      m'.arr64 IW = m.arr64 IW ∧ erTop m' = erTop m ∧ iwTop m' = iwTop m := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => freshW p n mq) (fresh_specW rom p hL n ·) hc
  unfold freshW at hw
  obtain ⟨r1, m1, h1, hw⟩ := ntBW_inv hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨s', rfl, -, -, hm⟩ := triple_of_callW (s₀ := ⟨_, Locals.init []⟩)
    (memoClearG_spec rsetSch p "rset_clear" hL.rset_clear n _) h1
  have hR : s'.mem = resetMem (m.set64 CTL 131 0) := hm
  rw [hR]
  have hcs : 200 < (m.arr64 CTL).size := hI.ok.2.2.2.2
  have hf : MemFrame [] [131, 132, 148, 149] m (resetMem (m.set64 CTL 131 0)) :=
    ((MemFrame.setCtl m 131 0).mono (by simp) (by simp)).trans ((resetMem_frame1 _).mono (by simp)
      (by simp))
  obtain ⟨hI1, hE, hIW, ht, hi⟩ := hI.expr (ArenaD.frameHi hf (by simp) (by
      intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide) hI.arena)
    (hI.mode.frame hf (by decide) (by decide))
    (hf.mono (by simp) (by
      intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [ExprC, RomC])) rfl
  refine ⟨hI1, MemoR.fresh _ (by rw [size_set64]; omega), ?_, hE, hIW, ht, hi⟩
  rw [resetMem_stk]; simp only [stkTop, rdW_set64]; simp; omega

end calls

end L.Rom
