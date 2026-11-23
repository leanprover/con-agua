module

public import ConAgua.Final.CmpAbi
public import ConAgua.Final.ThreadsFinal
public import ConAgua.Final.CompareTwin

@[expose] public section

/-!
# The threaded compared run at the L level: stand-ins (lane compare2, helper H3)

PLACEHOLDER until helper H2's L-level half lands (`Checker/CmpThreads*.lean`): mode `7`'s memory
`cmpM7`, the buffer's geometry after mode `7` and the composition `cmpThreads_twinPooled`, stated
here as agreed through the lead, with `sorry`. Removed when H2's land.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena

/-- Mode `7`'s memory: mode `5`'s final memory with the input replaced by the solution's bytes
(the setup stub's descriptor rewrite) and the mode word `7`. -/
def cmpM7 (mode : GVar) (m5 : Mem) (bS : ByteArray) : Mem := (cmpIn m5 bS).setG mode 7

/-- The buffer's geometry after mode `7` (as `checker_cmpBufOk` after mode `5`). -/
theorem checker_cmp7BufOk (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hbC : bC.size < 2 ^ 63) (hbS : bS.size < 2 ^ 63) (hpb : pb.size < 2 ^ 63)
    {rs4 : List Word} {m4 : Mem} {rs5 : List Word} {m5 : Mem} {rs7 : List Word} {m7 : Mem}
    (h4 : cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4))
    (hge4 : 2 ^ 63 ≤ (rs4.getD 0 0).toNat)
    (h5 : cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5))
    (hge5 : 2 ^ 63 ≤ (rs5.getD 0 0).toNat)
    (h7 : cmpRun checkerProg (cmpM7 MODE m5 bS) = .ok (rs7, m7))
    (hge7 : 2 ^ 63 ≤ (rs7.getD 0 0).toNat) :
    CmpBufOk frozenIdsL OUT m7 := sorry

/-- **The threaded compared run's L runs accept ⇒ the twin's pooled comparison accepts.** -/
theorem cmpThreads_twinPooled (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hbC : bC.size < 2 ^ 63) (hbS : bS.size < 2 ^ 63) (hpb : pb.size < 2 ^ 63)
    (rs4 : List Word) (m4 : Mem) (h4 : cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4))
    (hge4 : 2 ^ 63 ≤ (rs4.getD 0 0).toNat)
    (rs5 : List Word) (m5 : Mem) (h5 : cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5))
    (hge5 : 2 ^ 63 ≤ (rs5.getD 0 0).toNat)
    (thsS : List (Mem × List (Word × Nat × Mem)))
    (hthS : ∀ t ∈ thsS, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m5.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns (cmpBuf OUT m5) t.1 t.2 ∧ ∀ c ∈ t.2, c.1 < rs5.getD 0 0 - 9223372036854775808)
    (hcovS : ∀ j : Word, j < rs5.getD 0 0 - 9223372036854775808 → ∃ t ∈ thsS, ∃ c ∈ t.2, c.1 = j)
    (hincS : ∀ t ∈ thsS, (t.2.map (·.1)).Pairwise (· < ·))
    (rs7 : List Word) (m7 : Mem) (h7 : cmpRun checkerProg (cmpM7 MODE m5 bS) = .ok (rs7, m7))
    (hge7 : 2 ^ 63 ≤ (rs7.getD 0 0).toNat)
    (thsC : List (Mem × List (Word × Nat × Mem)))
    (hthC : ∀ t ∈ thsC, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m7.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns (cmpBuf OUT m7) t.1 t.2 ∧ ∀ c ∈ t.2, c.1 < rs7.getD 0 0 - 9223372036854775808)
    (hcovC : ∀ j : Word, j < rs7.getD 0 0 - 9223372036854775808 → ∃ t ∈ thsC, ∃ c ∈ t.2, c.1 = j)
    (hincC : ∀ t ∈ thsC, (t.2.map (·.1)).Pairwise (· < ·)) :
    TwinComparesAcceptsPooled bC bS := sorry

end ConAgua.Final
