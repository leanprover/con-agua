module

public import ConAgua.Final.CmpA
public import ConAgua.Final.ThreadsFinal
public import ConAgua.Final.CompareTwinI
public import ConAgua.Checker.CmpSPhaseThr
public import ConAgua.Checker.CompareChain6Run
public import ConAgua.Checker.AsmX
public import ConAgua.Checker.ProgI
public import ConAguaAsm.Checker
import ConAgua.Verdict.CmpVModes
import ConAgua.Checker.AsmFinal
import ConAgua.Checker.ProgIRef
import ConAgua.Checker.AsmXOk
import ConAgua.Checker.ProgWf
import ConAgua.Final.DrvFinal
import all ConAgua.Checker.Entry

@[expose] public section

/-!
# The threaded compared run's entry 1 of `checker.s` (lane compare2)

`cmpEntry1_regs`: `ca_start_ac` of the committed file on the machine (`cmpA_outcome_regs` at the
checker). For the harness (`Final/CpThreads.lean`): `cmpEntry1_out`, a return with `rdx = 0`,
`rax ≥ 2^63` leaves the frozen buffer `B` (the harness reads `OUT[0, OUT[1])`) as the L facts
`CmpOut` describe, with `rax - 2^63 = kS + kC` jobs; `cmpEntry1_fail`, a failing return of a class
other than `0` is the twin's pooled comparison rejecting or declining (`TwinCompareVerdictPooledI`,
a stage failing).
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena

/-- **A frozen buffer's header geometry** (one header of the compared run's buffer): the entries'
words inside the buffer, every entry inside it, the entries pairwise apart (or empty). -/
structure HdrOk (B : Array Word) : Prop where
  hdr : ∀ i < frozenIdsL.length, 9 + 2 * i < B.size
  ent : ∀ i < frozenIdsL.length, (bufEntry B i).1 + (bufEntry B i).2 ≤ B.size
  disj : ∀ i < frozenIdsL.length, ∀ i' < frozenIdsL.length, i ≠ i' →
    (bufEntry B i).1 + (bufEntry B i).2 ≤ (bufEntry B i').1 ∨
    (bufEntry B i').1 + (bufEntry B i').2 ≤ (bufEntry B i).1 ∨ (bufEntry B i).2 = 0 ∨ (bufEntry B i').2 = 0

/-- **What entry 1 of the compared run leaves** (L-level): the solution's preparation (`FoldOn`),
the challenge's (`F6`, `c` its job count), the solution's jobs' view `mS` (`CsViewS`); the buffer
`B` with header S at word `0` (the solution's `kS = B[2]` jobs, first calls as `mS`'s) and header
C at word `B[5]` (the challenge's, first calls as `m9`'s), and `k = kS + c`. -/
def CmpOut (bC bS pb : ByteArray) (B : Array Word) (k : Word) : Prop :=
  pb.size < 2 ^ 63 ∧ ∃ (PS : PhaseS bC bS) (m₇ m : Mem) (c : Word) (m9 mS : Mem),
    FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m ∧ F6 PS m c m9 ∧
    m9.bytes = m.bytes ∧ CsViewS m m9 mS ∧
    (∀ b ∈ parOwnedL, (mS.arr64 b).size = abiSz checkerTab b ∧ (m9.arr64 b).size = abiSz checkerTab b) ∧
    HdrOk B ∧ CsFirst B mS ∧ (B.getD 2 0).toNat = PS.dsS.size ∧
    B.getD 5 0 ≠ 0 ∧ (B.getD 5 0).toNat ≤ B.size ∧
    HdrOk (B.extract (B.getD 5 0).toNat B.size) ∧ CsFirst (B.extract (B.getD 5 0).toNat B.size) m9 ∧
    k = B.getD 2 0 + c ∧ (B.getD 2 0).toNat + c.toNat < 2 ^ 64

/-- **Stand-in (L level; H2c's mode `7`, H5's views)**: after the front and mode `7` returning
`2^63 + kC`, `OUT`'s length word lies inside `OUT`, and the buffer `OUT[0, OUT[1])` is as
`CmpOut` says, with `kS + kC` jobs. -/
theorem cmp7_out_standin (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64) {rs5 : List Word}
    {m5 : Mem} {rs7 : List Word} {m7 : Mem} (hf : CmpFront45 checkerTab checkerProg MODE bC bS pb rs5 m5)
    (h7 : cmpRun checkerProg (m5.setG MODE 7) = .ok (rs7, m7)) (hge7 : 2 ^ 63 ≤ (rs7.getD 0 0).toNat) :
    ((m7.arr64 OUT).getD 1 0).toNat ≤ (m7.arr64 OUT).size ∧
    CmpOut bC bS pb (cmpBuf OUT m7) ((rs5.getD 0 0 - 9223372036854775808) + (rs7.getD 0 0 - 9223372036854775808)) := by
  sorry

/-- The file's code as `ca_start_ac` sees it: the stub and the compiler's output, and the compared
run's entries. -/
theorem code_of_checkerFile_cmpE [Host] {k0 : Nat} (hcode : Code checkerFile k0) :
    (∃ k1, Code (abiStub checkerTab ++ compileProgX checkerX checkerTab checkerProgI "check") k1) ∧
    ∃ Kc, Code (cmpStubL checkerTab MODE) Kc := by
  have h := (code_of_checkerFile_cmp hcode).right
  have h1 := h
  rw [← List.append_assoc] at h1
  have h2 := h.right.right
  rw [cmpStub_lit] at h2
  exact ⟨⟨_, h1.left⟩, _, h2⟩

/-- **`ca_start_ac` of `checker.s` on the machine**: `cmpA_outcome_regs` at the checker. -/
theorem cmpEntry1_regs [Host] (k0 : Nat) (hcode : Code checkerFile k0) (bC bS pb : ByteArray)
    (sa : Word) (dm : MachineData) (ra : Word) (hc : CmpCall bC bS pb sa dm ra) :
    Ev (CmpPostH dm ra (CmpAccT checkerTab checkerProg MODE bC bS pb) (CmpErrT checkerTab checkerProg MODE bC bS pb)
      (CmpHiT checkerTab checkerProg MODE bC bS pb dm.regs.r8.toNat sa.toNat dm.regs.rdx.toNat))
      dm (label abiStartACL) := by
  obtain ⟨⟨k1, hcodeO⟩, Kc, hC⟩ := code_of_checkerFile_cmpE hcode
  exact cmpA_outcome_regs checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok
    checkerTab_abiIO checkerProgI_wf (by decide) MODE (by decide) (by decide +kernel) k1 hcodeO hC L.Checker.checkL
    checkerProg_lookup_check (by decide) bC bS pb sa dm ra hc

/-- **The harness's buffer is `OUT`'s first `OUT[1]` words**: on a memory holding `m` in the stub's
layout, a buffer `B` read at `OUT`'s slot whose length is the word at `OUT[1]`'s address. -/
theorem cmp_bufEq {base inp n pins np : Nat} {m : Mem} {d : DataMem}
    (hm : MemRel (abiLayout checkerTab base inp n pins np) m d)
    (hlen : ((m.arr64 OUT).getD 1 0).toNat ≤ (m.arr64 OUT).size) (B : Array Word)
    (hbufw : ∀ i (h : i < B.size), rdW d (A (outAddr base + 8 * i)) = some B[i])
    (hbuflen : ∃ w, rdW d (A (outAddr base + 8)) = some w ∧ w.toNat = B.size) :
    B = cmpBuf OUT m := by
  obtain ⟨-, hBw⟩ := cmp_buf_words checkerTab_abiOk checker_seqParamsOk hm hlen
  obtain ⟨hb, hs, -, -⟩ := cmp_out_pos checkerTab_abiOk checker_seqParamsOk base inp n pins np
  obtain ⟨dout, -⟩ := seqParamsOk_spec checker_seqParamsOk
  have hsz := hm.size64 _ dout
  simp only [abiLayout_tab] at hsz
  rw [hs] at hsz
  have hw1 := hm.get64 _ dout 1 (by change 1 < (m.arr64 (TieredArray.t0 OUT)).size; rw [hsz]; decide)
  simp only [abiLayout_tab] at hw1
  rw [hb] at hw1
  obtain ⟨w, hw, hwB⟩ := hbuflen
  have hcs : (cmpBuf OUT m).size = ((m.arr64 OUT).getD 1 0).toNat := by
    simp only [cmpBuf, Array.size_extract]; omega
  have ew : w = (m.arr64 OUT).getD 1 0 := by
    have : rdW d (A (outAddr base + 8)) = some ((m.arr64 (TieredArray.t0 OUT))[1]'(by
      change 1 < (m.arr64 (TieredArray.t0 OUT)).size; rw [hsz]; decide)) := by
      rw [← hw1]; rfl
    rw [hw] at this
    simp only [Option.some.injEq] at this
    rw [this]
    simp only [Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_eq_getElem]; rfl
  have hsize : B.size = (cmpBuf OUT m).size := by rw [hcs, ← hwB, ew]
  refine Array.ext hsize fun i h1 h2 => ?_
  have e1 := hbufw i h1
  have e2 := hBw i h2
  rw [show outAddr base = base + abiSlot * abiSlot64 checkerTab OUT from rfl, e2] at e1
  exact (Option.some.inj e1).symm

/-- **Entry 1 of the threaded compared run returns its buffer** (the harness's hypotheses: the
return `st₀` of a call `CmpCall` of `ca_start_ac`, `rdx = 0`, `rax ≥ 2^63`, the buffer `B` read at
`OUT`'s slot, its length from `OUT[1]`): the callee-saved registers are restored and `B` with
`rax - 2^63` jobs is as `CmpOut` says. -/
theorem cmpEntry1_out [Host] (k0 : Nat) (hcode : Code checkerFile k0) (bC bS pb : ByteArray)
    (h64 : System.Platform.numBits = 64) (sa : Word) (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState)
    (hc : CmpCall bC bS pb sa dm₀ ra₀) (hret : FirstReturn dm₀ (label abiStartACL) ra₀ st₀)
    (hrdx : st₀.data.regs.rdx = 0) (hrax : 9223372036854775808 ≤ st₀.data.regs.rax.toNat) (B : Array Word)
    (hbufw : ∀ i (h : i < B.size), rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * i)) = some B[i])
    (hbuflen : ∃ w, rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8)) = some w ∧ w.toNat = B.size) :
    RegsRestored dm₀.regs st₀.data.regs ∧ CmpOut bC bS pb B (st₀.data.regs.rax - 9223372036854775808) := by
  have hP := hret _ (cmpEntry1_regs k0 hcode bC bS pb sa dm₀ ra₀ hc) (fun s h => h.1.1)
  obtain ⟨⟨-, hRR, -, -⟩, hhi⟩ := hP
  refine ⟨hRR, ?_⟩
  obtain ⟨rs5, m5, rs7, m7, hfr, h7, hge7, hK, hM⟩ := hhi hrdx hrax
  obtain ⟨hlen, hout⟩ := cmp7_out_standin bC bS pb h64 hfr h7 hge7
  rw [cmp_bufEq hM hlen B hbufw hbuflen, hK]
  have e : (9223372036854775808 : Word) + ((rs5.getD 0 0 - 9223372036854775808) + (rs7.getD 0 0 - 9223372036854775808)) -
      9223372036854775808 = (rs5.getD 0 0 - 9223372036854775808) + (rs7.getD 0 0 - 9223372036854775808) := by
    rw [UInt64.add_comm, UInt64.add_sub_cancel]
  rw [e]; exact hout

/-- **A failing entry 1 of the threaded compared run is the twin's** (a class other than `0`): a
stage fails as the twin's does (modes `4`, `5`; mode `7` fails only with class `0`). -/
theorem cmpEntry1_fail [Host] (k0 : Nat) (hcode : Code checkerFile k0) (bC bS pb : ByteArray)
    (h64 : System.Platform.numBits = 64) (sa : Word) (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState)
    (hc : CmpCall bC bS pb sa dm₀ ra₀) (hret : FirstReturn dm₀ (label abiStartACL) ra₀ st₀)
    (hrdx : st₀.data.regs.rdx = 2) (hk : st₀.data.regs.rax &&& 3 ≠ 0) :
    TwinCompareVerdictPooledI bC bS (st₀.data.regs.rax &&& 3) := by
  have hP := hret _ (cmpEntry1_regs k0 hcode bC bS pb sa dm₀ ra₀ hc) (fun s h => h.1.1)
  obtain ⟨⟨-, -, -, herr⟩, -⟩ := hP
  rcases herr hrdx with ⟨hbC, hpb, ⟨e, he, hc'⟩ | ⟨rs4, m4, h4, hge4, hbS, e, he, hc'⟩⟩ |
      ⟨rs5, m5, -, e, he, hc'⟩
  · have hcls : e.cls = st₀.data.regs.rax &&& 3 := by rw [Err.cls, hc']
    rw [← hcls] at hk ⊢
    exact .inl (cmpV_a4 bC bS pb h64 hbC hpb e he hk)
  · have hcls : e.cls = st₀.data.regs.rax &&& 3 := by rw [Err.cls, hc']
    rw [← hcls] at hk ⊢
    exact .inl (cmpV_a5 bC bS pb h64 hbC hbS hpb rs4 m4 h4 hge4 e he hk)
  · have hcls : e.cls = st₀.data.regs.rax &&& 3 := by rw [Err.cls, hc']
    exact absurd (hcls ▸ cmpV_a67 (.inr (by simp [Mem.setG])) he) hk

end ConAgua.Final
