import ConAgua.Final.DrvFinal
import ConAgua.Checker.VerdictTop

/-!
# The verdict theorem for the sequential driver of the committed file

`checkerFile_verdict`: the harness calls the driver `ca_start` of `checker.s` as `AbiCall` says.
The machine returns to the caller, and if it reports `rdx = 2` with a code whose class
`rax &&& 3` is `1` (reject) or `2` (decline), the twin's pipeline on `[b]` fails with an error of
that class (`TwinVerdict`): `invalid` for a reject, `notImplemented` for a decline. Every other
outcome (class `0`, `rdx = 1`) claims nothing.

From the machine-level driver (`drv_outcome`, its error half `DrvErr`) and the L-level claims of
the two entries (`SeqVerdicts`, `Checker/VerdictTop.lean`).
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

/-- **The driver's failure is the twin's**: `DrvErr` with a code of class other than `0`, under
the entries' verdict claims, gives `TwinVerdict [b]` at that class. -/
theorem drvErr_twin (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (k : Word)
    (hV : SeqVerdicts checkerProg)
    (h : DrvErr checkerProg checkerTab MODE PLO PHI OUT HDRF CTLF 132 b pb k) (hk : k &&& 3 ≠ 0) :
    TwinVerdict [b] (k &&& 3) := by
  obtain ⟨hb, hpb, h⟩ := h
  have hin : InputsOK b pb (List.replicate checkerTab.nw abiWords) :=
    ⟨h64, hb, hpb, fun n hn => by simp [List.mem_replicate] at hn; rw [hn.2]; simp [abiWords]⟩
  have hN : abiFuel < 2 ^ 62 := by simp [abiFuel]
  rcases h with ⟨e, he, hc⟩ | ⟨rs₁, m₁, h₁, hnw, hge, e, he, hc⟩
  · subst hc
    exact hV.entry1 b pb [] _ hin 3 (Or.inr rfl) abiFuel hN e he hk
  · subst hc
    have hsz : 242 < m₁.words.size := by rw [hnw]; decide
    rw [getD_zero_headD] at hge he
    refine hV.entry2 b pb [] _ hin abiFuel hN rs₁ m₁ h₁ hge abiFuel (by simp [abiFuel])
      (seqMem m₁ MODE PLO PHI OUT HDRF CTLF 132 0 (rs₁.headD 0 - 9223372036854775808))
      ?_ rfl rfl rfl ?_ ?_ e he hk
    · intro a ha
      rw [seqMem_arr64 _ _ _ hsz]
      have h1 : ¬ (a = OUT ∨ a = CTLF) := by
        rintro (rfl | rfl) <;> revert ha <;> decide
      have h2 : a ≠ HDRF := by rintro rfl; revert ha; decide
      simp only [h1, h2, if_false]
    · rw [seqMem_arr64 _ _ _ hsz]; simp
    · simp only [rd64, seqMem_arr64 _ _ _ hsz]
      simp only [show ¬ (HDRF = OUT ∨ HDRF = CTLF) by decide, if_false, if_true]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
      by_cases h3 : 3 < (m₁.arr64 OUT).size
      · have h4 : 3 < min 132 (m₁.arr64 OUT).size := by omega
        simp [h4]
      · have h4 : ¬ 3 < min 132 (m₁.arr64 OUT).size := by omega
        simp [h4, Array.getElem?_eq_none (Nat.le_of_not_lt h3)]

/-- **The verdict theorem for the driver of `checker.s`**: the machine returns to `ra`, and if it
reports `rdx = 2` with a code of class `1` or `2` (`rax &&& 3`), the twin's pipeline on `[b]`
fails with an error of that class, given the entries' verdict claims (`SeqVerdicts`). -/
theorem checkerFile_verdict [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (dm : MachineData) (ra : Word)
    (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (SeqVerdicts checkerProg → st.data.regs.rdx = 2 → st.data.regs.rax &&& 3 ≠ 0 →
          TwinVerdict [b] (st.data.regs.rax &&& 3)))
      dm (label abiStartL) :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, _, _, h⟩ => ⟨hpc, fun hV h2 hk => drvErr_twin b pb h64 _ hV (h h2) hk⟩)
    (drv_outcome checkerProg checkerTab checkerTab_abiOk checkerProg_wf (by decide) MODE PLO PHI OUT
      HDRF CTLF 132 frozenIdsL parOwnedL (by decide) (by decide) (by decide) checker_seqParamsOk k0
      (code_of_checkerFile_par hcode) L.Checker.checkL checkerProg_lookup_check (by decide) b pb dm ra hc)

/-- info: 'ConAgua.Final.checkerFile_verdict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_verdict

end ConAgua.Final
