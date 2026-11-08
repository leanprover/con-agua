module

import ConAgua.Rom.CIReadRefCaps
public import ConAgua.Rom.CIReadRefBase
public import ConAgua.Rom.CIReadSpec

@[expose] public section

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
  sorry

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
  sorry

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
  have hcs : 200 < (m.arr64 CTL).size := hI.ok.ctl
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
