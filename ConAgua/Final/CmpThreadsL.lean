module

public import ConAgua.Final.CmpAbi
public import ConAgua.Final.ThreadsFinal
public import ConAgua.Final.CompareTwin
public import ConAgua.Checker.CompareChain6Run
public import ConAgua.Checker.ParEntryA
public import ConAgua.Checker.CmpThreadsC

@[expose] public section

/-!
# The threaded compared run at the L level: mode 7's memory (lane compare2, helper H3)

Mode `7`'s memory `cmpM7`; the challenge's pooled phase is `cmpThreadsC_pooledJ`
(`Checker/CmpThreadsC.lean`).
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

/-- Mode `7`'s memory: mode `5`'s final memory with the input replaced by the solution's bytes
(the setup stub's descriptor rewrite) and the mode word `7`. -/
def cmpM7 (mode : GVar) (m5 : Mem) (bS : ByteArray) : Mem := (cmpIn m5 bS).setG mode 7

end ConAgua.Final
