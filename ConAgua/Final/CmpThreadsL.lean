module

public import ConAgua.Final.CmpAbi
public import ConAgua.Final.ThreadsFinal
public import ConAgua.Final.CompareTwin
public import ConAgua.Checker.CompareChain6Run
public import ConAgua.Checker.ParEntryA

@[expose] public section

/-!
# The threaded compared run at the L level: stand-ins (lane compare2, helper H3)

PLACEHOLDER until helper H2's parts land: mode `7`'s memory `cmpM7`, the generalized mode-6/7 run
the challenge's pooled phase (`cmpThreadsC_pooledJ`),
stated here as agreed through the lead, with `sorry`. Removed when H2's land.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

/-- Mode `7`'s memory: mode `5`'s final memory with the input replaced by the solution's bytes
(the setup stub's descriptor rewrite) and the mode word `7`. -/
def cmpM7 (mode : GVar) (m5 : Mem) (bS : ByteArray) : Mem := (cmpIn m5 bS).setG mode 7

/-- STAND-IN for H2's `cmpThreadsC_pooledJ`: **the challenge's threads accept ⇒ the twin's pool
with the solution accepts the challenge's phase**. After the solution's index build (`FoldOn`)
and its pooled accept, mode `7` (`F6`, then `par_compact(1)`: `m7`), threads on mode `7`'s buffer,
each a fresh region running its calls, every job index below `c` claimed, each thread's claims
increasing: the challenge's preparation and side records (`Side6`) and its pooled check with the
solution `solutionOf PS.IS res` (`PooledAcceptsJ`, from `sG` = `sH`, the side records' state). -/
theorem cmpThreadsC_pooledJ {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS) {m₇ m : Mem}
    (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    (hPS : PooledAccepts .verified PS.ipins PS.dsS PS.sE PS.IS PS.sF)
    {c : Word} {m9 m7 : Mem} (h6 : F6 PS m c m9) (hb9 : m9.bytes = m.bytes)
    (hok : parCompactOK m9 1 = true) (hm7 : m7 = parCompactMem m9 1)
    (ths : List (Mem × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m7.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns (cmpBuf OUT m7) t.1 t.2 ∧ ∀ c' ∈ t.2, c'.1 < c)
    (hcov : ∀ j : Word, j < c → ∃ t ∈ ths, ∃ c' ∈ t.2, c'.1 = j)
    (hinc : ∀ t ∈ ths, (t.2.map (·.1)).Pairwise (· < ·)) :
    ∃ (m2 m3 : Mem) (dsC : Array IDeclaration) (sG : AState) (res : List IDeclaration) (m4 : Mem)
      (I : IStreamIndex) (a' : AState),
      Side6 PS m c m2 m3 dsC sG res m4 ∧
      PooledAcceptsJ .verified PS.ipins (some (solutionOf PS.IS res)) res.toArray sG I a' := sorry

end ConAgua.Final
