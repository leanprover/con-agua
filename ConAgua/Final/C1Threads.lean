module

public import ConAgua.Checker.CmpSPhaseThr
public import ConAgua.Checker.C1Back
public import ConAgua.Arena.C1Pool
public import ConAgua.Final.CpThreads
public import ConAgua.Final.CompareTwinI
import ConAgua.Checker.CmpThreadsC
import ConAgua.Checker.CmpThreadsPool
import ConAgua.Checker.CmpSPhaseT
import ConAgua.Checker.CrsProgPB
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.JobsProg
import ConAgua.Checker.CheckARun
import ConAgua.Checker.AsmFinal
import ConAgua.Arena.FreezeFresh
import ConAgua.Arena.FreezeTrunc
import ConAgua.Arena.FreezeFreshBase
import ConAgua.Arena.JobStart
import ConAgua.Arena.LoopStart
import ConRon.Bridge.Compare.Mates

@[expose] public section

/-!
# The threaded compared run's threads, both phases on one region (lane compare2, H7)

Each thread runs its solution calls over header S from a fresh region, then its challenge calls
over header C on the region as they left it.

* `c1_solPhase`: the solution's phase per thread (`pool_twinE`): each thread's list accepted from
  `sI.worker`, ending in a worker state where the thread's region is the solution's jobs' relation
  with `c1Q` (what the solution's jobs keep), and the twin's pool of the solution's jobs.
* `c1Thr_accepts`: then the switch (`c1_thrBack`) and the challenge's phase from each thread's end
  (`pool_twinJW`): `TwinComparesAcceptsThr`.
-/

open ConRon.Arena ConRon.Bridge

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena L.Rom

local notation "VM" => ConLeche.CheckMode.verified

/-- A thread's calls as a chain with its end (`runsEnd`). -/
theorem threadRuns_chainE (B : Array Word) :
    ∀ (cs : List (Word × Nat × Mem)) (r : Mem), ThreadRuns B r cs →
      JobChainE (fun k r r' => ∃ n rs, n ≤ 2 ^ 62 ∧
        L.run checkerProg n "check" [] (bufMem B r (UInt64.ofNat k)) = .ok (rs, r') ∧ BufKept B r')
        r (cs.map (·.1.toNat)) (runsEnd r cs)
  | [], r, _ => .nil r
  | (j, n, r') :: cs, r, ⟨hn, ⟨rs, hrun⟩, hkept, hrest⟩ =>
    .cons ⟨n, rs, hn, by rw [UInt64.ofNat_toNat]; exact hrun, hkept⟩ (threadRuns_chainE B cs r' hrest)

theorem c1_rdW_fresh (m : Mem) {x : Word} (hx : x.toNat < 256) :
    rdW ((freshMem m).arr64 CTL) x = rdW (m.arr64 CTL) x := by
  rw [c1_rdW, c1_rdW, freshMem_arr, ite_eq_left rfl, truncFrozen_ctl, getD_freshCtl, ite_eq_left hx]

end ConAgua.Final
