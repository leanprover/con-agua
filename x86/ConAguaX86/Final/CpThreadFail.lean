module

public import ConAguaX86.Final.CpThreads
public import ConAguaX86.Final.ThreadsVerdict
import ConAguaX86.Checker.AsmFinal
import all ConAgua.Checker.Entry
public import ConAgua.Verdict.ThreadsE

@[expose] public section

/-!
# A thread's failing call over a two-phase buffer (lane compare2)

`cpThreadFail_runs`: a thread whose calls before call `i` accepted and whose call `i` returned
`rdx = 2`, over the compared run's buffer (header S, header C at word `5`): the failure is an L
failure `e` (`rax = e.code`) of header S's job `j` (`j < kS`) after the thread's earlier calls, all
header S's, ran over `B` from the zero region (`ThreadFails`), or of header C's job `j - kS` after
the thread's header-S calls ran over `B` from the zero region and then its earlier header-C calls
over `B.extract L B.size` from the memory they left. The chain as in `cpThreadsAcc_runs`.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

/-- A chain of runs ending in a failure (`threadFails_range`, at any job indices). -/
theorem cp_fails (B : Array Word) (g : Nat → Word) (rm : Nat → Mem) (n : Nat) (j : Word) (e : Err)
    (h : ∀ i < n, (∃ rs, L.run checkerProg abiFuel "check" [] (bufMem B (rm i) (g i)) = .ok (rs, rm (i + 1))) ∧
      BufKept B (rm (i + 1)))
    (hf : L.run checkerProg abiFuel "check" [] (bufMem B (rm n) j) = .error e) :
    ∀ c s, s + c = n → ThreadFails B j abiFuel e (rm s) ((List.range' s c).map fun i => (g i, abiFuel, rm (i + 1)))
  | 0, s, hs => by
    obtain rfl : s = n := by omega
    exact ⟨by simp [abiFuel], hf⟩
  | c + 1, s, hs => by
    obtain ⟨h1, h2⟩ := h s (by omega)
    exact ⟨by simp [abiFuel], h1, h2, cp_fails B g rm n j e h hf c (s + 1) (by omega)⟩


/-- `cp_fails` from a lower bound `lo` on (calls `lo ≤ s, …, n - 1`, then the failing one). -/
theorem cp_fails' (B : Array Word) (g : Nat → Word) (rm : Nat → Mem) (lo n : Nat) (j : Word) (e : Err)
    (h : ∀ i, lo ≤ i → i < n →
      (∃ rs, L.run checkerProg abiFuel "check" [] (bufMem B (rm i) (g i)) = .ok (rs, rm (i + 1))) ∧
      BufKept B (rm (i + 1)))
    (hf : L.run checkerProg abiFuel "check" [] (bufMem B (rm n) j) = .error e) :
    ∀ c s, lo ≤ s → s + c = n →
      ThreadFails B j abiFuel e (rm s) ((List.range' s c).map fun i => (g i, abiFuel, rm (i + 1)))
  | 0, s, _, hs => by
    obtain rfl : s = n := by omega
    exact ⟨by simp [abiFuel], hf⟩
  | c + 1, s, hl, hs => by
    obtain ⟨h1, h2⟩ := h s hl (by omega)
    exact ⟨by simp [abiFuel], h1, h2, cp_fails' B g rm lo n j e h hf c (s + 1) (by omega) (by omega)⟩

set_option linter.constructorNameAsVariable false in
/-- **A thread's failing call over a two-phase buffer, at the L level** (the hypotheses are
`CmpThreadFail`'s thread fields). -/
theorem cpThreadFail_runs [Host] (k0 : Nat) (hcode : Code checkerFile k0) (dm₀ : MachineData)
    (B : Array Word) (hS : HdrOk B) (LC : Nat) (hL5 : (B.getD 5 0).toNat = LC) (hL0 : LC ≠ 0)
    (hC : HdrOk (B.extract LC B.size)) (kS : Word) (hk2 : B.getD 2 0 = kS) (t : ThreadM) (i : Nat)
    (calls : ∀ i' ≤ i, BufCallH B (t.dm i') (t.ra i') ∧
      (t.dm i').regs.rdi.toNat = outAddr dm₀.regs.r8.toNat ∧ (t.dm i').regs.rcx.toNat = t.base ∧
      (t.dm i').regs.r8.toNat = t.blen)
    (zero : ∀ x, t.base ≤ x → x < t.base + t.blen → (t.dm 0).dmem.get? (A x) = some 0)
    (ret : ∀ i' ≤ i, FirstReturn (t.dm i') (label abiCheckBL) (t.ra i') (t.st i'))
    (acc : ∀ i' < i, (t.st i').data.regs.rdx = 0 ∧ (t.st i').data.regs.rax = ACCEPT)
    (rdx : (t.st i).data.regs.rdx = 2)
    (kept : ∀ i' < i, ∀ q (h : q < B.size),
      rdW (t.st i').data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * q)) = some B[q])
    (next : ∀ i', i' < i → ∀ x, t.base ≤ x → x < t.base + t.blen →
      (t.dm (i' + 1)).dmem.get? (A x) = (t.st i').data.dmem.get? (A x))
    (incr : ∀ i₁ i₂, i₁ < i₂ → i₂ ≤ i → (t.dm i₁).regs.rdx < (t.dm i₂).regs.rdx) :
    ∃ e : Err, (t.st i).data.regs.rax = e.code ∧
      (((t.dm i).regs.rdx < kS ∧ ∃ cs : List (Word × Nat × Mem),
          ThreadFails B (t.dm i).regs.rdx abiFuel e (zeroMem checkerTab) cs ∧
          ∀ x ∈ cs, x.1 < (t.dm i).regs.rdx) ∨
       (kS ≤ (t.dm i).regs.rdx ∧ ∃ csS csC : List (Word × Nat × Mem),
          ThreadRuns B (zeroMem checkerTab) csS ∧ (∀ x ∈ csS, x.1 < kS) ∧ (csS.map (·.1)).Pairwise (· < ·) ∧
          ThreadFails (B.extract LC B.size) ((t.dm i).regs.rdx - kS) abiFuel e
            (runsEnd (zeroMem checkerTab) csS) csC ∧
          ∀ x ∈ csC, x.1 < (t.dm i).regs.rdx - kS)) := by
  obtain ⟨hH0, -, hcx0, h80⟩ := calls 0 (Nat.zero_le _)
  have hneed : workerNeed parOwnedL ≤ t.blen := h80 ▸ hH0.need
  have hfit : t.base + t.blen < 2 ^ 64 := hcx0 ▸ h80 ▸ hH0.fits
  obtain ⟨nS, hnS, hbelow, habove⟩ := cp_phases (i + 1) (fun k => (t.dm k).regs.rdx) kS
    (fun a b h1 h2 => incr a b h1 (by omega))
  have hpost : ∀ k ≤ i, ∀ r, RegionRel checkerTab t.base parOwnedL r (t.dm k).dmem →
      EntryPost (bufLayout checkerTab (cpA (outAddr dm₀.regs.r8.toNat) LC kS (t.dm k).regs.rdx)
        (cpB B LC kS (t.dm k).regs.rdx) t.base frozenIdsL parOwnedL) (t.dm k) (t.ra k)
        (L.run checkerProg abiFuel "check" [] (bufMemG frozenIdsL parOwnedL PLO PHI MODE
          (cpB B LC kS (t.dm k).regs.rdx) r (cpJ kS (t.dm k).regs.rdx))) (t.st k) := by
    intro k hk r hr
    obtain ⟨hH, hdi, hcx, -⟩ := calls k hk
    have hEv := cp_post k0 hcode B hS LC hL5 hL0 hC kS hk2 (t.dm k) (t.ra k) hH r (by rw [hcx]; exact hr)
    rw [hdi, hcx] at hEv
    exact ret k hk _ hEv (fun s h => h.1)
  -- the accepting calls before `i`, one chain
  obtain ⟨rm, h0, hrun, hreg⟩ := cp_chain checkerProg checkerTab frozenIdsL parOwnedL PLO PHI MODE
    checkerTab_abiOk (by decide) parOwnedL_not_frozen (fun k => cpB B LC kS (t.dm k).regs.rdx)
    (fun k => cpA (outAddr dm₀.regs.r8.toNat) LC kS (t.dm k).regs.rdx) (fun k => cpJ kS (t.dm k).regs.rdx)
    t.base t.blen i hneed hfit t.dm t.ra t.st (fun _ => zero) (fun k hk => hpost k (by omega))
    (fun k hk => acc k hk) (fun k hk => next k (by omega))
  -- call `i`
  have hregi : RegionRel checkerTab t.base parOwnedL (rm i) (t.dm i).dmem := hreg _ fun x h1 h2 => by
    rcases i with _ | i
    · exact zero x h1 h2
    · exact next i (by omega) x h1 h2
  obtain ⟨-, -, -, hout⟩ := hpost i (Nat.le_refl _) (rm i) hregi
  obtain ⟨e, he, hrax⟩ := outcome_err (hout.resolve_left (by rw [rdx]; decide)) rdx
  have hkeptS : ∀ k < i, (t.dm k).regs.rdx < kS → BufKept B (rm (k + 1)) := by
    intro k hk hph
    obtain ⟨rs, -, -, h3, -⟩ := hrun k hk
    simp only [cpB, cpA, UInt64.not_le.mpr hph, ite_false] at h3
    exact bufKept_of_memRel h3 hS.ent (kept k hk)
  refine ⟨e, hrax, ?_⟩
  by_cases hph : (t.dm i).regs.rdx < kS
  · -- phase S: every call is header S's
    have hnSi : i < nS := by
      refine Classical.byContradiction fun hn => ?_
      exact absurd hph (UInt64.not_lt.mpr (habove i (by omega) (by omega)))
    simp only [cpB, cpJ, UInt64.not_le.mpr hph, ite_false] at he
    refine .inl ⟨hph, (List.range' 0 i).map fun k => ((t.dm k).regs.rdx, abiFuel, rm (k + 1)), ?_, ?_⟩
    · rw [← h0]
      exact cp_fails B (fun k => (t.dm k).regs.rdx) rm i _ e (fun k hk => by
        obtain ⟨rs, h1, -⟩ := hrun k hk
        have hp := hbelow k (by omega)
        simp only [cpB, cpJ, UInt64.not_le.mpr hp, ite_false] at h1
        exact ⟨⟨rs, h1⟩, hkeptS k hk hp⟩) he i 0 (by omega)
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      exact incr k i (by have := List.mem_range'_1.mp hk; omega) (Nat.le_refl _)
  -- phase C: the header-S calls `0, …, nS - 1`, then header C's `nS, …, i - 1`
  have hge : kS ≤ (t.dm i).regs.rdx := UInt64.not_lt.mp hph
  have hnSi : nS ≤ i := by
    refine Classical.byContradiction fun hn => ?_
    exact absurd hge (UInt64.not_le.mpr (hbelow i (by omega)))
  simp only [cpB, cpJ, hge, ite_true] at he
  let csS := (List.range' 0 nS).map fun k => ((t.dm k).regs.rdx, abiFuel, rm (k + 1))
  have hRS : ThreadRuns B (zeroMem checkerTab) csS := by
    rw [← h0]
    refine cp_runs B (fun k => (t.dm k).regs.rdx) rm 0 nS (fun k _ hk => ?_) nS 0 (Nat.le_refl _) (by omega)
    obtain ⟨rs, h1, -⟩ := hrun k (by omega)
    have hp := hbelow k (by omega)
    simp only [cpB, cpJ, UInt64.not_le.mpr hp, ite_false] at h1
    exact ⟨⟨rs, h1⟩, hkeptS k (by omega) hp⟩
  have hend : runsEnd (zeroMem checkerTab) csS = rm nS := by
    rw [← h0]; exact (cp_runsEnd _ rm nS 0).trans (by rw [Nat.zero_add])
  refine .inr ⟨hge, csS, (List.range' nS (i - nS)).map fun k => ((t.dm k).regs.rdx - kS, abiFuel, rm (k + 1)),
    hRS, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    exact hbelow k (by have := List.mem_range'_1.mp hk; omega)
  · simp only [csS, List.map_map]
    rw [List.pairwise_map]
    refine (List.pairwise_lt_range' (s := 0) (n := nS)).imp_of_mem fun ha hb hab => ?_
    exact incr _ _ hab (by have := List.mem_range'_1.mp hb; omega)
  · rw [hend]
    have := cp_fails' (B.extract LC B.size) (fun k => (t.dm k).regs.rdx - kS) rm nS i _ e (fun k h1 h2 => by
      obtain ⟨rs, r1, -, r3, -⟩ := hrun k h2
      have hp := habove k h1 (by omega)
      simp only [cpB, cpA, cpJ, hp, ite_true] at r1 r3
      exact ⟨⟨rs, r1⟩, bufKept_of_memRel r3 hC.ent (cp_keptC (kept k h2))⟩) he (i - nS) nS
      (Nat.le_refl _) (by omega)
    exact this
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have hk' := List.mem_range'_1.mp hk
    have e1 := habove k (by omega) (by omega)
    have e3 := UInt64.lt_iff_toNat_lt.mp (incr k i (by omega) (Nat.le_refl _))
    show (t.dm k).regs.rdx - kS < _
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ e1, UInt64.toNat_sub_of_le _ _ hge]
    have := UInt64.le_iff_toNat_le.mp e1
    omega

end ConAgua.Final
