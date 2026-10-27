import ConAgua.Checker.ParDriverL
import ConAgua.Checker.CheckARun

/-!
# The sequential driver's two runs give `TwinAccepts` (lane parmode)

docs/design/parmode.md, "Redesign". `drv_twinAccepts`: entry 1 (`check` with the mode word `3`,
from the loaded memory) returning `2^63 + k`, then entry 2 in place (`check` with the mode word `2`
on a memory `w` that keeps entry 1's final word arrays phase B's loop names, the range `[0, k)`, an
empty seed, the view in the header) returning `ACCEPT`: the twin's pipeline accepts. Entry 1 is
`checkA_run` (phase A ends in `PhaseBStart`, the memory is the buffer's `parCompactMem`, with the
header only), entry 2 `runMode2_agree` (phase B on the worker, through non-interference), and the
two are `SeqAccepts`, i.e. `TwinAccepts` (`Final/Twin.lean`).
-/

open ConRon.Arena ConAgua.Final

namespace L.Checker

open L L.Arena L.Rom

/-- **The driver's two runs accept ⇒ the twin accepts.** -/
theorem drv_twinAccepts (b pb : ByteArray) (s8 s64 : List Nat) (hin : InputsOK b pb s64)
    (N₁ : Nat) (hN₁ : N₁ < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N₁ "check" [] (loadMemM b pb s8 s64 3) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat)
    (N₂ : Nat) (hN₂ : N₂ ≤ 2 ^ 62) (w : Mem) (rs₂ : List Word) (m₂ : Mem)
    (hw : ∀ a, phaseBS a = true → w.arr64 a = m₁.arr64 a) (hmode : w.glob MODE = 2)
    (hlo : w.glob PLO = 0) (hhi : w.glob PHI = rs₁.headD 0 - 9223372036854775808)
    (hctlf : (w.arr64 CTLF).size = 0) (hv : rd64 w HDRF 3 = rd64 m₁ OUT 3)
    (h₂ : L.run checkerProg N₂ "check" [] w = .ok (rs₂, m₂)) (hacc : rs₂.headD 0 = ACCEPT) :
    TwinAccepts [b] := by
  have hr : rs₁.headD 0 ≠ 1 := fun e => by rw [e] at hge; simp at hge
  obtain ⟨PA, m, v, hS, hPB, hpre, hok, hm₁, hres⟩ := checkA_run b pb s8 s64 hin 3 (Or.inr rfl) N₁ hN₁ rs₁ m₁ h₁ hr
  have hflag : modeFlag 3 = 0 := rfl
  rw [hflag] at hok hm₁
  -- the twin's facts behind the program bundle (as `foldStage_checker`)
  have hrom : RomOK pb.data.toList := by simpa [RomOK] using hin.2.2.1
  have hT := twinFold_of_prefix PA.pfx
  have hdn : L.Ind.DnInj (dnOf PA.sE.store) := dnOf_inj hT.stateOK.wf
  have hQd : QuotDn (dnOf PA.sE.store) := by
    obtain ⟨k, hk, hd⟩ := prefix_quotU PA.pfx
    exact ⟨k, by simp [dnOf, hk, hd]⟩
  have hLC := checkerProg_loopCalleesPB pb.data.toList hrom hpre (dnOf PA.sE.store) hdn
    (indArmSpec_checker _ hrom hpre _ hdn) hQd
  have hTop := checkerProg_loopTopPB pb.data.toList
  have hPB' : PhaseBProg (Prog.subPB pb.data.toList checkerProg) :=
    ⟨hTop.bracket, hLC.cvg, hLC.knot, hLC.leaf, hLC.loop, hTop.pc, hTop.pcg, hTop.pcx,
      hLC.cd.crp.apd, ⟨hLC.indMemo, hLC.crf⟩⟩
  -- entry 2's memory agrees with phase A's
  have hfr := parCompactMem_out m v 0
  rw [← hm₁] at hfr
  have hw' : ∀ a, phaseBS a = true → w.arr64 a = m.arr64 a := fun a ha => by
    rw [hw a ha, hfr.arr a (fun e => by subst e; revert ha; decide)]
  have h3 := (parCompactMem_hdr (vis := v) hok).2.2.2.1
  have hv' : rd64 w HDRF 3 = v := by
    rw [hv, hm₁]; exact h3
  have hk : (rs₁.headD 0 - 9223372036854775808).toNat = PA.pend.size := by
    have hc := hS.loop.pend.count
    have hlt : PA.pend.size < 2 ^ 64 := by rw [← hc]; exact UInt64.toNat_lt_size _
    have e : (9223372036854775808 : Word) + UInt64.ofNat PA.pend.size - 9223372036854775808 =
        UInt64.ofNat PA.pend.size := by rw [UInt64.add_comm, UInt64.add_sub_cancel]
    rw [hres, e, UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using hlt)]
  obtain ⟨s'', hB⟩ := runMode2_agree .verified PA.ipins (dnOf PA.sE.store) PA.ds PA.fe PA.pend
    pb.data.toList hPB' rfl N₂ hN₂ m PA.sF v _ hk hPB hS w hw' hmode hlo hhi hctlf hv' h₂ hacc
  obtain ⟨hA, hBp, hC, hD, hE⟩ := PA.pfx
  exact ⟨PA.pins, PA.sA, PA.sB, PA.sC, PA.sD, PA.sE, PA.sF, PA.pre, PA.rc, PA.ds, PA.ipins, PA.fe,
    hA, hBp, hC, hD, hE, PA.k, PA.pend, s'', PA.fold, hB⟩

end L.Checker
