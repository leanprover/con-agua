import ConAgua.Rom.PinReadSpec
import ConAgua.Rom.DecExpr

open ConRon.Arena

namespace L.Rom

theorem internAllPins_split (pins : List ConLeche.NatOpPinSet) :
    internAllPins pins = internAllPins [] >>= fun _ => internPinSets pins := by
  simp only [internAllPins, internPinSets, bind_assoc, pure_bind]

open L.Arena

/-- **`intern_all_pins` over a buffer that starts with `romData`, up to the variant list**: the
startup items are the twin's `internAllPins []`, and the variant list starts right after
`romData`. -/
theorem internAllPinsW_fixed (rom : List UInt8) (hr : RomOK rom) (rest : List UInt8)
    (hrom : rom = romData ++ rest) (n : Nat) (mem mem' : Mem) (a : AState) (hA : ArenaD mem a)
    (hP : PinsReadyP a) (hst : (stkTop mem).toNat < 2 ^ 61) (hc : 132 < (mem.arr64 CTL).size)
    (hW : internAllPinsW rom n mem = some mem') :
    ∃ (n' : Nat) (m₁ : Mem) (a₁ : AState) (v : List INatOpPinSet) (q' : Word),
      (internAllPins []).run a = .ok (v, a₁) ∧ ArenaD m₁ a₁ ∧ (RsetR mem → RsetR m₁) ∧
      stkTop m₁ = stkTop mem ∧ MemFrame ExprA ExprC mem m₁ ∧
      internPinSetsW rom n' m₁ (UInt64.ofNat romData.length) = some (q', mem') := by
  cases n with
  | zero => simp [internAllPinsW] at hW
  | succ n =>
  simp only [internAllPinsW] at hW
  split at hW
  case isFalse => cases hW
  rename_i hcl
  cases hI : romItemsW rom n (resetMem mem) allPinsOff with
  | none => rw [hI] at hW; simp [iapK] at hW
  | some r =>
  obtain ⟨q, m₁⟩ := r
  rw [hI] at hW
  simp only [iapK] at hW
  cases hS : internPinSetsW rom n m₁ q with
  | none => rw [hS] at hW; simp [iap2K] at hW
  | some r =>
  obtain ⟨q', m₂⟩ := r
  rw [hS] at hW
  simp only [iap2K, Option.some.injEq] at hW
  subst hW
  have hd : rom.drop allPinsOff.toNat = encItems [] (itemsAllPins []) ++ rest := by
    rw [hrom, allPinsOff_toNat, romData, romPins, ← List.append_assoc, List.append_assoc,
      List.drop_left]
  have hA' : ArenaD (resetMem mem) a := ArenaD.frameHi (resetMem_frame1 _) (by simp) (by simp) hA
  obtain ⟨m', a', -, hrunI, hR, -, hq, hf, hs, hz⟩ := romItemsW_ok rom hr _ allPins_fits n (resetMem mem) a
    allPinsOff rest [] ∅ q m₁ hA' (MemoR.fresh mem hc) hd (by rw [resetMem_stk]; exact hst)
    (by rw [(resetMem_frame1 _).2.2.1]; omega) hI
  obtain ⟨v, hv⟩ := simZ_internAllPins [] allPins_noProj ∅ a m' a' hP (by rw [runItems_reset]; exact hrunI)
  have hqd : q = UInt64.ofNat romData.length := by
    have hl := romData_len
    apply UInt64.toNat_inj.mp
    rw [hq, allPinsOff_toNat, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    simp [romData, romPins]; omega
  subst hqd
  exact ⟨n, m₁, a', v, q', hv, hR, fun h0 => hz (h0.reset hcl), by rw [hs, resetMem_stk],
    (resetMem_frame mem).trans hf, hS⟩

end L.Rom
