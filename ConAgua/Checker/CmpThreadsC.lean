module

public import ConAgua.Final.CmpChainC
public import ConAgua.Checker.ParThreadTwin
import ConAgua.Checker.CmpThreadsPool
import ConAgua.Checker.CrsProgPB
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.JobsProg
import ConAgua.Checker.CheckARun
import ConAgua.Checker.AsmFinal
import ConAgua.Arena.FreezeFresh
import ConAgua.Arena.FreezeTrunc
import ConAgua.Arena.JobStart
import ConRon.Bridge.Compare.Mates

@[expose] public section

/-!
# The challenge's threads (lane compare2)

The threaded compared run's challenge phase at the L level: after mode `7` (`F6`, then
`par_compact(1)`: the challenge's frozen buffer, with the solution's rows), threads whose calls of
entry 2 claim every challenge record give the twin's pool with the solution (`PooledAcceptsJ`), as
`threads_pooledO` (`Checker/ParThreadTwin.lean`) does for the flat run:

* `solKeysIn_of`: the solution's keys (its index's and its mates') are tier-0 names below the
  name counts, from the twin's facts (`indexKeysIn_of`, `MatesRel`).
-/

open ConRon.Arena ConRon.Bridge

namespace L.Arena

/-- **The solution's keys in the store** (`SolKeysIn`), from its index denoting persistently and its
mates related (`MatesRel`: every key persistent and denoting). -/
theorem solKeysIn_of {m : Mem} {a : AState} {J : ISolution} {dsS : List ConLeche.Declaration}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)} (hR : ArenaR m a)
    (hIS : IndexDenotes a.store J.idx (ConLeche.Cached.buildIndex dsS.toArray))
    (hpIS : PersIFBase J.idx.base) (hmt : MatesRel a.store J.mates matesU) : SolKeysIn m J :=
  ⟨indexKeysIn_of hR hIS hpIS, fun n l e hn => by
    obtain ⟨nm, hdn, -⟩ := hmt.cover n l e
    exact nameIn_of hR (hmt.pers n l e).1 hdn hn⟩

end L.Arena

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena L.Rom

local notation "VM" => ConLeche.CheckMode.verified

end ConAgua.Final
