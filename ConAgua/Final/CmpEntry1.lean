module

public import ConAgua.Final.CmpA
public import ConAgua.Final.CmpC
public import ConAgua.Final.CpThreads
public import ConAgua.Final.CompareTwinVerdict
public import ConAgua.Checker.AsmX
public import ConAgua.Checker.ProgI
import ConAgua.Verdict.CmpVModes
import ConAgua.Checker.AsmFinal
import ConAgua.Checker.ProgIRef
import ConAgua.Checker.AsmXOk
import ConAgua.Checker.ProgWf
import ConAgua.Final.DrvFinal
import ConAgua.Final.CmpSeqTwin
public import ConAgua.Arena.FreezeCmpView
import ConAgua.Checker.C1Switch
import all ConAgua.Checker.Entry
import ConAgua.Final.CmpMain
public import ConAgua.Final.CmpOutcome
public import ConAgua.Checker.CmpSPhase
import ConAgua.Final.CmpChainC
import ConAgua.Checker.CompareChain6J
public import ConAgua.Final.CmpAbi
import ConAgua.Arena.IWFrame
import ConAgua.L.WordOff
public import ConAgua.Checker.CmpCall

@[expose] public section

/-!
# The threaded compared run's entry 1 of `checker.s` (lane compare2)

`cmpEntry1_regs`: `ca_start_ac` of the committed file on the machine (`cmpA_outcome_regs` at the
checker). For the harness (`Final/CpThreads.lean`): `cmpEntry1_out`, a return with `rdx = 0`,
`rax ≥ 2^63` leaves the frozen buffer `B` (the harness reads `OUT[0, OUT[1])`) as the L facts
`CmpOut` describe, with `rax - 2^63 = kS + kC` jobs; `cmpEntry1_fail`, a failing return of a class
other than `0` is a stage of the twin's comparison failing (`TwinCompareStagesFail`).
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena

/-- **What entry 1 of the compared run leaves** (L-level): the solution's preparation (`FoldOn`),
the challenge's (`F6`, `c` its job count), the solution's jobs' view `mS` (`CsViewS`); the buffer
`B` with header S at word `0` (the solution's `kS = B[2]` jobs; it shows `mS`, `HdrView`) and header
C at word `B[5]` (the challenge's; it shows `m9`), every frozen entry of the same length in both
headers (a thread's arrays have the same sizes in both phases), and `k = kS + c`. -/
def CmpOut (bC bS pb : ByteArray) (B : Array Word) (k : Word) : Prop :=
  pb.size < 2 ^ 63 ∧ ∃ (PS : PhaseS bC bS) (m₇ m : Mem) (c : Word) (m9 mS : Mem),
    FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m ∧ F6 PS m c m9 ∧
    m9.bytes = m.bytes ∧ CsViewS m m9 mS ∧
    (∀ b ∈ parOwnedL, (mS.arr64 b).size = abiSz checkerTab b ∧ (m9.arr64 b).size = abiSz checkerTab b) ∧
    HdrOk B ∧ HdrView B mS ∧ (B.getD 2 0).toNat = PS.dsS.size ∧
    B.getD 5 0 ≠ 0 ∧ (B.getD 5 0).toNat ≤ B.size ∧
    HdrOk (B.extract (B.getD 5 0).toNat B.size) ∧ HdrView (B.extract (B.getD 5 0).toNat B.size) m9 ∧
    (∀ i < frozen.length, fzExt mS (fzAt i) = fzExt m9 (fzAt i)) ∧
    k = B.getD 2 0 + c ∧ (B.getD 2 0).toNat + c.toNat < 2 ^ 64

/-- **Header S's view of mode `7`'s frozen memory** (`viewS m9`) is `CsViewS`: from the solution's
stash (`F6.csStash`) and the seed's patches. -/
theorem cmp_csViewS {bC bS pb : ByteArray} {PS : PhaseS bC bS} {m₇ m : Mem}
    (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) {c : Word} {m9 : Mem}
    (h6 : F6 PS m c m9) : CsViewS m m9 (viewS m9) := by
  have hcs := h6.csStash
  have hsz9 : ∀ b, (m9.arr64 b).size = abiSz checkerTab b := fun b => by rw [F6.size h6, hF.sizeAt]
  have hv := viewSArr_s m9
  have hD := hF.build.decls
  have b1 := hD.count; have b2 := hD.room; have b3 := hD.dsize; have b4 := hD.ptop; have b5 := hD.psize
  have g : ∀ a : Array Word, rdW a 0 = a[0]?.getD 0 := fun a => by simp [L.Arena.rdW]
  have hm1 := hF.sizeAt L.Front.DECL
  have hm2 := hF.sizeAt L.Front.DLP
  have hvs : (viewSCtl m9).size = (m9.arr64 CTL).size := by
    have hfs : ∀ (ks : List Nat) (c : Array Word),
        (ks.foldl (fun c k => c.setIfInBounds k ((m9.arr64 L.Checker.SCTL).getD k 0)) c).size = c.size := by
      intro ks; induction ks with
      | nil => intro c; rfl
      | cons k ks ih => intro c; rw [List.foldl_cons, ih, Array.size_setIfInBounds]
    unfold viewSCtl
    rw [Array.size_setIfInBounds, hfs, Array.size_setIfInBounds]
  have hctl : 256 ≤ (m9.arr64 CTL).size := by rw [hsz9]; decide
  have hrd : ∀ x : Word, rdW (viewSCtl m9) x = (viewSCtl m9).getD x.toNat 0 := fun x => by
    simp only [L.Arena.rdW, Array.getD_eq_getD_getElem?]
  have hrd' : ∀ (a : Array Word) (x : Word), rdW a x = a.getD x.toNat 0 := fun a x => by
    simp only [L.Arena.rdW, Array.getD_eq_getD_getElem?]
  refine ⟨⟨fun b hb hc => ?_, fun x hx => ?_, fun b => ?_⟩, fun gi hg => ?_, fun gi hg => ?_,
    fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, fun x hx => ?_, ?_, rfl⟩
  · apply viewS_arr
    intro hm
    simp only [vsChg, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact hc rfl | exact hb (by decide)
  · have hp : vsPatched x.toNat = false := by
      have h1 : ¬ x.toNat ∈ rrWs := fun h => hx ((csC_iff x).mpr h)
      rw [rrWs_iff] at h1
      simp only [vsPatched, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Bool.and_eq_false_iff,
        decide_eq_false_iff_not]
      omega
    rw [show (viewS m9).arr64 ↑CTL = viewSCtl m9 from viewS_ctl m9, hrd, hrd', viewSCtl_getD m9 _ hp]
  · show (viewSArr m9 b).size = _
    by_cases hb : b ∈ vsChg
    · simp only [vsChg, List.mem_cons, List.not_mem_nil, or_false] at hb
      unfold viewSArr
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ite_eq_left rfl]; rw [hsz9, hsz9]; decide
      · rw [ite_eq_right (by decide), ite_eq_left rfl]; rw [hsz9, hsz9]; decide
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]; rw [hsz9, hsz9]; decide
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]; rw [hsz9, hsz9]; decide
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]; rw [hsz9, hsz9]; decide
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]; rw [hsz9, hsz9]; decide
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]; rw [hsz9, hsz9]; decide
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]; rw [hsz9, hsz9]; decide
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]; rw [hsz9, hsz9]; decide
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]; exact hvs
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]; rw [hsz9, hsz9]; decide
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]; rw [hsz9, hsz9]; decide
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]; rw [hsz9, hsz9]; decide
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]; rw [hsz9, hsz9]; decide
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]; rw [hsz9, hsz9]; decide
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]; rw [hsz9, hsz9]; decide
    · rw [show viewSArr m9 b = (viewS m9).arr64 b from rfl, viewS_arr m9 b hb]
  · rcases (show gi = 0 ∨ gi = 1 ∨ gi = 2 by omega) with rfl | rfl | rfl <;> rfl
  · rcases (show gi = 0 ∨ gi = 1 ∨ gi = 2 by omega) with rfl | rfl | rfl <;> rfl
  · show (viewSArr m9 ↑FIRSTS)[j]? = _
    rw [hv.2.1]; exact hcs.firsts j hj
  · show (viewSArr m9 ↑L.Front.DECL)[j]? = _
    rw [hv.1]; exact hcs.decl j hj
  · show (viewSArr m9 ↑L.Front.DLP)[j]? = _
    rw [hv.2.2]; exact hcs.dlp j hj
  · show _ ≤ (viewSArr m9 ↑FIRSTS).size
    rw [hv.2.1, hsz9]
    have : abiSz checkerTab L.Front.DECL ≤ 8 * abiSz checkerTab L.Checker.SFIRSTS := by decide
    rw [g]; omega
  · show _ ≤ (viewSArr m9 ↑L.Front.DECL).size
    rw [hv.1, hsz9, show abiSz checkerTab L.Checker.SDECL = abiSz checkerTab L.Front.DECL by decide, g]; omega
  · show (viewSArr m9 ↑L.Front.DECL).size < _
    rw [hv.1, hsz9, show abiSz checkerTab L.Checker.SDECL = abiSz checkerTab L.Front.DECL by decide]; omega
  · show _ ≤ (viewSArr m9 ↑L.Front.DLP).size
    rw [hv.2.2, hsz9, show abiSz checkerTab L.Checker.SDLP = abiSz checkerTab L.Front.DLP by decide, g]; omega
  · show (viewSArr m9 ↑L.Front.DLP).size < _
    rw [hv.2.2, hsz9, show abiSz checkerTab L.Checker.SDLP = abiSz checkerTab L.Front.DLP by decide]; omega
  · rw [show (viewS m9).arr64 ↑CTL = viewSCtl m9 from viewS_ctl m9, hrd, hrd']
    have := viewSCtl_128 m9 (by omega)
    simpa using this
  · have hx' : 162 ≤ x.toNat ∧ x.toNat ≤ 173 := by
      simp only [frozenCtl, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [show (viewS m9).arr64 ↑CTL = viewSCtl m9 from viewS_ctl m9, hrd, viewSCtl_at m9 _ (by omega),
      ite_eq_right (by omega), ite_eq_left hx', ← hrd']
    exact hcs.frz x hx
  · rw [show (viewS m9).arr64 ↑CTL = viewSCtl m9 from viewS_ctl m9, hrd, viewSCtl_at m9 _ (by simp; omega)]
    simp

/-- **Mode `7`'s buffer** (L level): after the front and mode `7` returning `2^63 + kC`, `OUT`'s
length word lies inside `OUT`, and the buffer `OUT[0, OUT[1])` is as `CmpOut` says, with `kS + kC`
jobs: header S shows `viewS m9` (`cmpView_S`), header C `m9` (`cmpView_C`), both headers' entries
apart (`cmpApart_S`, `cmpApart_C`), of the same extents (`viewS_ext`). -/
theorem cmp7_out (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64) {rs5 : List Word}
    {m5 : Mem} {rs7 : List Word} {m7 : Mem} (hf : CmpFront45 checkerTab checkerProg MODE bC bS pb rs5 m5)
    (h7 : cmpRun checkerProg (m5.setG MODE 7) = .ok (rs7, m7)) (_hge7 : 2 ^ 63 ≤ (rs7.getD 0 0).toNat) :
    ((m7.arr64 OUT).getD 1 0).toNat ≤ (m7.arr64 OUT).size ∧
    CmpOut bC bS pb (cmpBuf OUT m7) ((rs5.getD 0 0 - 9223372036854775808) + (rs7.getD 0 0 - 9223372036854775808)) := by
  obtain ⟨PS, m₇, m, hF, hst, hk6, hm5, hres5⟩ := cmpFront_run bC bS pb h64 hf
  rw [hm5] at h7
  obtain ⟨-, hpb, -, -⟩ := hf
  have hN : abiFuel < 2 ^ 62 := by simp [abiFuel]
  have hsz6 : ∀ g ≤ 2, abiSz checkerTab (sixArr g) = abiSz checkerTab (eixArr g) ∧
      abiSz checkerTab (stxArr g) = abiSz checkerTab (tixArr g) := by
    intro g hg
    rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  have hO : OutEq m (m.setG MODE 7) := (⟨fun _ _ => rfl, fun _ => rfl, rfl⟩ : OutEq m m).setG MODE 7
  obtain ⟨c, hpost, hres7⟩ := checkC3_run PS hF hst hk6 cmp_absz hpb hsz6 hO 7 1
    (Or.inr ⟨rfl, rfl⟩) (by simp [Mem.setG]) abiFuel hN rs7 m7 h7
  obtain ⟨m9, hF6, hok, hS⟩ := hpost.2 (by decide)
  have hsz9 : ∀ b, (m9.arr64 b).size = abiSz checkerTab b := fun b => by rw [F6.size hF6, hF.sizeAt]
  have hlt : (m9.arr64 OUT).size < 2 ^ 64 := by rw [hsz9]; exact cmp_absz _
  obtain ⟨hS', rfl⟩ := hS (by rw [(parCompactMem_out_b m9 1 hdrWW).size, hsz9]; decide)
  have hcw : rd64 m9 CTL (Nat.toUInt64 cmpCW) = 1 := by
    have := (F6.ext hF hF6).1
    simpa [rd64, L.Arena.rdW, Array.getD_eq_getD_getElem?] using this
  obtain ⟨hVS, -⟩ := cmpView_S hok hlt hS' hcw
  obtain ⟨hVC, -⟩ := cmpView_C hok hlt hS'
  obtain ⟨hhdrC, hapC⟩ := cmpApart_C hok hlt hS'
  have hapS := cmpApart_S hok hlt hS' hcw
  obtain ⟨hsz, ho0, hlc, h256, hX1, hX2, h1, h5, -⟩ := cmpC_facts hok hlt hS'
  have hV := cmp_csViewS hF hF6
  have hhw := hdrW_eq
  have hL := frozenIdsL_length
  have hfl := frozen_length
  -- the buffer
  have hBe : cmpBuf OUT (cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)) =
      cmpBufS OUT (cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)) := rfl
  have hSz : (cmpBufS OUT (cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length))).size =
      (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).2.toNat := by
    simp only [cmpBufS, h1, Array.size_extract]; omega
  have hSg : ∀ k < (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).2.toNat,
      (cmpBufS OUT (cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length))).getD k 0 =
      ((cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).arr64 OUT).getD k 0 := by
    intro k hk'
    simp only [cmpBufS, h1]
    rw [getD_extract_lt _ _ _ _ (by simp only [Array.size_extract]; omega), Nat.zero_add]
  have h5' : (cmpBufS OUT (cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length))).getD 5 0 = hdrWW := by
    rw [hSg 5 (by omega), h5]
  have e154 : hdrWW.toNat = 154 := rfl
  -- word 2: the solution's count
  have hD := hF.build.decls
  have hw2 : (cmpBufS OUT (cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length))).getD 2 0 =
      (m.arr64 L.Front.DECL)[0]?.getD 0 := by
    have hc := hVS.cnt.1
    simp only [bufImg, hVS.hdr0, Nat.zero_add] at hc
    rw [getD_extract_lt _ _ _ _ (by simp only [Array.size_extract, hSz]; omega), Nat.zero_add] at hc
    rw [hc]
    show ((viewSArr m9 ↑L.Front.DECL).getD (UInt64.toNat 0) 0) = _
    rw [(viewSArr_s m9).1, Array.getD_eq_getD_getElem?]
    exact congrArg (·.getD 0) (hF6.csStash.decl 0 (by omega))
  have hc63 : c.toNat < 2 ^ 63 := by
    obtain ⟨m2, m3, dsC, sG, res, m4', I, a', h, -⟩ := F6.jobM hF hF6
    have := h.count.1
    have := h.decls.room; have := h.decls.dsize
    simp only [List.size_toArray] at *
    omega
  have f2 : OutFrame m9 (L.Arena.seedMem (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).1
      (hdrW.toUInt64 + fzOff m9 frozen.length)) :=
    (((parCompactMem_out_b m9 1 hdrWW).trans (OutFrame.hsMem _ _)).trans (OutFrame.xsGo _ _ _)).trans
      (((OutFrame.set64 _ _ _).trans (OutFrame.seedFold _ _ _)).trans (OutFrame.set64 _ _ _))
  have f3 : ∀ M o, OutFrame M (hsTail M o) := fun M o => by
    unfold hsTail
    exact (((((((OutFrame.set64 M _ _).trans (OutFrame.set64 _ _ _)).trans (OutFrame.set64 _ _ _)).trans
      (OutFrame.set64 _ _ _)).trans (OutFrame.set64 _ _ _)).trans (OutFrame.set64 _ _ _)).trans
      (OutFrame.set64 _ _ _)).trans (OutFrame.set64 _ _ _)
  have hFr : OutFrame m9 (cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)) := f2.trans (f3 _ _)
  have hcnt := hD.count
  have hroom := hD.room; have hds := hD.dsize
  have hk5 : rs5.getD 0 0 - 9223372036854775808 = UInt64.ofNat PS.dsS.size := by
    rw [L.getD_zero, hres5, UInt64.add_comm, UInt64.add_sub_cancel]
  have hk7 : rs7.getD 0 0 - 9223372036854775808 = c := by
    rw [L.getD_zero, hres7, UInt64.add_comm, UInt64.add_sub_cancel]
  have hw2' : (m.arr64 L.Front.DECL)[0]?.getD 0 = UInt64.ofNat PS.dsS.size := by
    apply UInt64.toNat_inj.mp
    rw [hcnt, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  refine ⟨by rw [h1, hsz]; exact hX2, ?_⟩
  rw [hBe]
  refine ⟨hpb, PS, m₇, m, c, m9, viewS m9, hF, hF6, (hFr.bytes.symm.trans (run_check_bytes h7)).trans rfl, hV,
    fun b _ => ⟨by rw [hV.frame.size, hsz9], hsz9 b⟩,
    ⟨fun i hi => by rw [hSz]; omega, hVS.inside, hapS⟩, hVS, by rw [hw2, hcnt],
    by rw [h5']; decide, by rw [h5', hSz, e154]; omega,
    ⟨fun i hi => hhdrC i hi, hVC.inside, hapC⟩, hVC, fun i hi => viewS_ext m9 hcw hi,
    by rw [hk5, hk7, hw2, hw2'], by rw [hw2, hcnt]; omega⟩

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
  obtain ⟨hlen, hout⟩ := cmp7_out bC bS pb h64 hfr h7 hge7
  rw [cmp_bufEq hM hlen B hbufw hbuflen, hK]
  have e : (9223372036854775808 : Word) + ((rs5.getD 0 0 - 9223372036854775808) + (rs7.getD 0 0 - 9223372036854775808)) -
      9223372036854775808 = (rs5.getD 0 0 - 9223372036854775808) + (rs7.getD 0 0 - 9223372036854775808) := by
    rw [UInt64.add_comm, UInt64.add_sub_cancel]
  rw [e]; exact hout

/-- **A failing entry 1 of the threaded compared run is the twin's** (a class other than `0`): a
stage fails as the twin's does (`TwinCompareStagesFail`; modes `4`, `5`; mode `7` fails only with class `0`). -/
theorem cmpEntry1_fail [Host] (k0 : Nat) (hcode : Code checkerFile k0) (bC bS pb : ByteArray)
    (h64 : System.Platform.numBits = 64) (sa : Word) (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState)
    (hc : CmpCall bC bS pb sa dm₀ ra₀) (hret : FirstReturn dm₀ (label abiStartACL) ra₀ st₀)
    (hrdx : st₀.data.regs.rdx = 2) (hk : st₀.data.regs.rax &&& 3 ≠ 0) :
    TwinCompareStagesFail bC bS (st₀.data.regs.rax &&& 3) := by
  have hP := hret _ (cmpEntry1_regs k0 hcode bC bS pb sa dm₀ ra₀ hc) (fun s h => h.1.1)
  obtain ⟨⟨-, -, -, herr⟩, -⟩ := hP
  rcases herr hrdx with ⟨hbC, hpb, ⟨e, he, hc'⟩ | ⟨rs4, m4, h4, hge4, hbS, e, he, hc'⟩⟩ |
      ⟨rs5, m5, -, e, he, hc'⟩
  · have hcls : e.cls = st₀.data.regs.rax &&& 3 := by rw [Err.cls, hc']
    rw [← hcls] at hk ⊢
    exact cmpV_a4 bC bS pb h64 hbC hpb e he hk
  · have hcls : e.cls = st₀.data.regs.rax &&& 3 := by rw [Err.cls, hc']
    rw [← hcls] at hk ⊢
    exact cmpV_a5 bC bS pb h64 hbC hbS hpb rs4 m4 h4 hge4 e he hk
  · have hcls : e.cls = st₀.data.regs.rax &&& 3 := by rw [Err.cls, hc']
    exact absurd (hcls ▸ cmpV_a67 (.inr (by simp [Mem.setG])) he) hk

/-- **`ca_start_c` of `checker.s` on the machine** (the sequential compared run):
`cmpC_outcome_regs` at the checker. From `ca_start_c`, called as `CmpCall` says, the machine
returns to `ra` with the callee-saved registers restored; an accept and an error mean the L runs
`CmpAccS`, `CmpErrS` say. -/
theorem cmpSeq_regs [Host] (k0 : Nat) (hcode : Code checkerFile k0) (bC bS pb : ByteArray)
    (sa : Word) (dm : MachineData) (ra : Word) (hc : CmpCall bC bS pb sa dm ra) :
    Ev (CmpPostH dm ra (CmpAccS checkerTab checkerProg MODE PLO PHI OUT HDRF CTLF hdrHw bC bS pb)
      (CmpErrS checkerTab checkerProg MODE PLO PHI OUT HDRF CTLF hdrHw bC bS pb) (fun _ _ => True))
      dm (label abiStartCL) := by
  obtain ⟨-, Kc, hC⟩ := code_of_checkerFile_cmpE hcode
  exact cmpC_outcome_regs checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok
    checkerTab_abiIO checkerProgI_wf (by decide) MODE PLO PHI OUT HDRF CTLF hdrHw frozenIdsL parOwnedL
    (by decide) (by decide) (by decide) checker_seqParamsOk (by decide +kernel) k0
    (code_of_checkerFile_par hcode) hC L.Checker.checkL checkerProg_lookup_check (by decide) bC bS pb sa dm ra hc

/-- info: 'ConAgua.Final.cmpSeq_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cmpSeq_regs

end ConAgua.Final
