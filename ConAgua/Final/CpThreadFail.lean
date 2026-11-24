module

public import ConAgua.Final.CpThreads
public import ConAgua.Final.ThreadsVerdict
import ConAgua.Final.DrvFinal
import ConAgua.Final.BufAbi
import ConAgua.Checker.AsmFinal
import ConAgua.Checker.ProgIRef
import ConAgua.Checker.AsmXOk
import ConAgua.Checker.ProgWf
public import ConAgua.Checker.ProgTab
public import ConAguaAsm.Checker
import all ConAgua.Checker.Entry

@[expose] public section

/-!
# A thread's failing call over a two-phase buffer (lane compare2)

`cpThreadFail_runs`: a thread whose calls before call `i` accepted and whose call `i` returned
`rdx = 2`, over the compared run's buffer (header S, header C at word `5`): the failure is an L
failure `e` (`rax = e.code`) of header S's job `j` (`j < kS`) after the thread's earlier calls, all
header S's, ran over `B` from the zero region (`ThreadFails`), or of header C's job `j - kS` after the
thread's earlier header-C calls ran over `B.extract L B.size` from the zero region. The chains as in
`cpThreadsAcc_runs`.
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

set_option linter.constructorNameAsVariable false in
/-- **A thread's failing call over a two-phase buffer, at the L level** (the hypotheses are
`CmpThreadFail`'s thread fields). -/
theorem cpThreadFail_runs [Host] (k0 : Nat) (hcode : Code checkerFile k0) (dm₀ : MachineData)
    (B : Array Word) (hS : HdrOk B) (LC : Nat) (hL5 : (B.getD 5 0).toNat = LC) (hL0 : LC ≠ 0) (hLB : LC ≤ B.size)
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
       (kS ≤ (t.dm i).regs.rdx ∧ ∃ cs : List (Word × Nat × Mem),
          ThreadFails (B.extract LC B.size) ((t.dm i).regs.rdx - kS) abiFuel e (zeroMem checkerTab) cs ∧
          ∀ x ∈ cs, x.1 < (t.dm i).regs.rdx - kS)) := by
  have hc := code_of_checkerFile_par hcode
  have hnres : 1 ≤ checkerTab.nres := by decide
  have h5 : 5 < B.size := by have := hS.hdr 0 (by decide); omega
  obtain ⟨hH0, hdi0, hcx0, h80⟩ := calls 0 (Nat.zero_le _)
  have hneed : workerNeed parOwnedL ≤ t.blen := h80 ▸ hH0.need
  have hfit : t.base + t.blen < 2 ^ 64 := hcx0 ▸ h80 ▸ hH0.fits
  have hbend : outAddr dm₀.regs.r8.toNat + 8 * B.size < 2 ^ 64 := hdi0 ▸ hH0.bend
  have hapart : ∀ x, outAddr dm₀.regs.r8.toNat ≤ x → x < outAddr dm₀.regs.r8.toNat + 8 * B.size →
      x < t.base ∨ t.base + t.blen ≤ x := by
    rw [← hdi0, ← hcx0, ← h80]; exact hH0.apart
  -- the split point (over the calls `0, …, i`)
  obtain ⟨nS, hnS, hlt, hat⟩ := cp_split (i + 1) (fun k => kS ≤ (t.dm k).regs.rdx)
  have hbelow : ∀ k < nS, (t.dm k).regs.rdx < kS := fun k hk =>
    UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_not_le fun hle => hlt k hk (UInt64.le_iff_toNat_le.mpr hle))
  have habove : ∀ k, nS ≤ k → k ≤ i → kS ≤ (t.dm k).regs.rdx := by
    intro k h1 h2
    have hs := hat (by omega)
    rcases Nat.eq_or_lt_of_le h1 with e | lt
    · rw [← e]; exact hs
    · have := UInt64.lt_iff_toNat_lt.mp (incr _ _ lt h2)
      have := UInt64.le_iff_toNat_le.mp hs
      exact UInt64.le_iff_toNat_le.mpr (by omega)
  -- the header-S calls
  have hpostS : ∀ k < nS, ∀ r, RegionRel checkerTab t.base parOwnedL r (t.dm k).dmem →
      EntryPost (bufLayout checkerTab (outAddr dm₀.regs.r8.toNat) B t.base frozenIdsL parOwnedL) (t.dm k)
        (t.ra k) (L.run checkerProg abiFuel "check" [] (bufMemG frozenIdsL parOwnedL PLO PHI MODE B r
          (t.dm k).regs.rdx)) (t.st k) := by
    intro k hk r hr
    obtain ⟨hH, hdi, hcx, h8⟩ := calls k (by omega)
    have hbc : BufCall checkerTab frozenIdsL parOwnedL B (t.dm k) (t.ra k) :=
      ⟨⟨hH.need, hH.fits, hH.bend, hS.hdr, hS.ent, hS.disj, hH.apart⟩, hH.hB, hH.hmap, hH.hra, hH.hcs,
        hH.hcs24, hH.hcs8⟩
    have hEv := abiB_outcome checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok
      checkerProgI_wf MODE PLO PHI OUT HDRF CTLF hdrHw frozenIdsL parOwnedL (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) k0 hc L.Checker.checkL checkerProg_lookup_check (by decide)
      B r (t.dm k) (t.ra k) hbc (by rw [hcx]; exact hr) checker_bufMinOk h5 (.inl (hk2 ▸ hbelow k hk))
    rw [hdi, hcx] at hEv
    exact ret k (by omega) _ hEv (fun s h => h.1)
  -- the header-S chain: the calls before `min nS i`
  have hnSi : min nS i ≤ i := Nat.min_le_right _ _
  obtain ⟨rmS, h0S, hrunS⟩ := thread_chain checkerProg checkerTab checkerTab_abiOk hnres frozenIdsL parOwnedL
    parOwnedL_not_frozen PLO PHI MODE B (outAddr dm₀.regs.r8.toNat) t.base t.blen (min nS i) hneed hfit t.dm t.ra
    t.st (fun _ => zero) (fun k hk => hpostS k (by omega)) (fun k hk => acc k (by omega))
    (fun k hk => next k (by omega))
  have hregS : ∀ k ≤ min nS i, k < nS → RegionRel checkerTab t.base parOwnedL (rmS k) (t.dm k).dmem := by
    intro k hk hk'
    rcases k with _ | k
    · rw [h0S]; exact regionRel_zero checkerTab_abiOk hneed hfit _ zero
    · obtain ⟨-, -, -, h3, -⟩ := hrunS k (by omega)
      exact (RegionRel.of_memRel parOwnedL_not_frozen h3).transfer checkerTab_abiOk hneed (next k (by omega))
  by_cases hph : (t.dm i).regs.rdx < kS
  · -- phase S: every call is header S's
    have hnSi' : i < nS := by
      refine Classical.byContradiction fun hn => ?_
      have := habove i (by omega) (Nat.le_refl _)
      exact absurd hph (UInt64.not_lt.mpr this)
    rw [show min nS i = i by omega] at hrunS hregS
    obtain ⟨-, -, -, hout⟩ := hpostS i hnSi' (rmS i) (hregS i (Nat.le_refl _) hnSi')
    obtain ⟨e, he, hrax⟩ := outcome_err (hout.resolve_left (by rw [rdx]; decide)) rdx
    refine ⟨e, hrax, .inl ⟨hph, (List.range' 0 i).map fun k => ((t.dm k).regs.rdx, abiFuel, rmS (k + 1)), ?_, ?_⟩⟩
    · rw [← h0S]
      exact cp_fails B (fun k => (t.dm k).regs.rdx) rmS i _ e (fun k hk => by
        obtain ⟨rs, h1, -, h3, -⟩ := hrunS k hk
        exact ⟨⟨rs, h1⟩, bufKept_of_memRel h3 hS.ent (kept k hk)⟩) he i 0 (by omega)
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      exact incr k i (by have := List.mem_range'_1.mp hk; omega) (Nat.le_refl _)
  -- phase C
  have hge : kS ≤ (t.dm i).regs.rdx := UInt64.not_lt.mp hph
  have hnSi' : nS ≤ i := by
    refine Classical.byContradiction fun hn => ?_
    exact hlt i (by omega) hge
  rw [show min nS i = nS by omega] at hrunS hregS
  -- the second sub-region is zero at each call up to `nS`
  have hzero2 : ∀ k ≤ nS, ∀ x, t.base + workerNeed parOwnedL ≤ x → x < t.base + t.blen →
      (t.dm k).dmem.get? (A x) = some 0 := by
    intro k
    induction k with
    | zero => intro _ x h1 h2; exact zero x (by omega) h2
    | succ k ih =>
      intro hk x h1 h2
      rw [next k (by omega) x (by omega) h2]
      obtain ⟨hH, hdi, hcx, h8⟩ := calls k (by omega)
      obtain ⟨-, -, hF, -⟩ := hpostS k (by omega) (rmS k) (hregS k (by omega) (by omega))
      have hgS : BufGeom checkerTab frozenIdsL parOwnedL B (outAddr dm₀.regs.r8.toNat) t.base
          (workerNeed parOwnedL) :=
        ⟨Nat.le_refl _, by omega, hbend, hS.hdr, hS.ent, hS.disj, fun y h1 h2 => by
          rcases hapart y h1 h2 with h | h
          · exact .inl h
          · exact .inr (by omega)⟩
      have hw := hH.hcs
      rw [hcx, h8] at hw
      rw [cp_frameS hgS hF h1 (by omega) (fun hb => by rcases hapart x hb.1 hb.2 with h | h <;> omega)
        (by
          refine Classical.byContradiction fun hn => ?_
          simp only [not_or, Nat.not_lt, Nat.not_le] at hn
          rcases (hw x (by omega) (by omega)).2.1 with h | h <;> omega)]
      exact ih (by omega) x h1 h2
  -- the region holds both sub-regions (else call `i` declines)
  have hL5' : B.getD 5 0 ≠ 0 := fun h => hL0 (by rw [← hL5, h]; rfl)
  have hneed2 : 2 * workerNeed parOwnedL ≤ t.blen := by
    refine Classical.byContradiction fun hlt => ?_
    obtain ⟨hH, hdi, hcx, h8⟩ := calls i (Nat.le_refl _)
    have hEv := abiB_small checkerTab MODE PLO PHI OUT HDRF CTLF hdrHw frozenIdsL parOwnedL hc B (t.dm i) (t.ra i)
      h5 hH.hB (hk2 ▸ hge) hL5' (by rw [h8]; omega) hH.hra cp_wn2 hH.hcs8
      (bufLayout checkerTab 0 B 0 frozenIdsL parOwnedL) (.error .oob)
    have := (ret i (Nat.le_refl _) _ hEv (fun s h => h.1.1)).2
    rw [rdx] at this
    exact absurd this (by decide)
  have hb8 : outAddr dm₀.regs.r8.toNat + 8 * LC < 2 ^ 64 := by omega
  let BC := B.extract LC B.size
  have hBCs : BC.size = B.size - LC := by simp [BC]
  obtain ⟨dmC, hdmC⟩ : ∃ f : Nat → MachineData,
      ∀ k, f k = cpShift (t.dm (nS + k)) LC kS (workerNeed parOwnedL) := ⟨_, fun _ => rfl⟩
  have hdmem : ∀ k, (dmC k).dmem = (t.dm (nS + k)).dmem := fun k => by rw [hdmC]; exact cpShift_dmem ..
  have hrdxC : ∀ k, (dmC k).regs.rdx = (t.dm (nS + k)).regs.rdx - kS := fun k => by
    rw [hdmC]; exact cpShift_rdx ..
  have hdiC : ∀ k ≤ i - nS, (dmC k).regs.rdi.toNat = outAddr dm₀.regs.r8.toNat + 8 * LC := by
    intro k hk
    obtain ⟨-, hdi, -, -⟩ := calls (nS + k) (by omega)
    rw [hdmC, cpShift_rdi, hdi]
    exact UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using hb8)
  have hcxC : ∀ k ≤ i - nS, (dmC k).regs.rcx.toNat = t.base + workerNeed parOwnedL := by
    intro k hk
    obtain ⟨-, -, hcx, -⟩ := calls (nS + k) (by omega)
    rw [hdmC, cpShift_rcx, hcx]
    exact UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  have h8C : ∀ k ≤ i - nS, (dmC k).regs.r8.toNat = t.blen - workerNeed parOwnedL := by
    intro k hk
    obtain ⟨-, -, -, h8⟩ := calls (nS + k) (by omega)
    rw [hdmC, cpShift_r8, h8]
    exact UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  have hpostC : ∀ k ≤ i - nS, ∀ r, RegionRel checkerTab (t.base + workerNeed parOwnedL) parOwnedL r (dmC k).dmem →
      EntryPost (bufLayout checkerTab (outAddr dm₀.regs.r8.toNat + 8 * LC) BC (t.base + workerNeed parOwnedL)
        frozenIdsL parOwnedL) (dmC k) (t.ra (nS + k))
        (L.run checkerProg abiFuel "check" [] (bufMemG frozenIdsL parOwnedL PLO PHI MODE BC r
          (dmC k).regs.rdx)) (t.st (nS + k)) := by
    intro k hk r hr
    obtain ⟨hH, hdi, hcx, h8⟩ := calls (nS + k) (by omega)
    have hd : (dmC k).dmem = (t.dm (nS + k)).dmem := hdmem k
    have hsp : (dmC k).regs.rsp = (t.dm (nS + k)).regs.rsp := by rw [hdmC]; exact cpShift_rsp ..
    have hbc : BufCall checkerTab frozenIdsL parOwnedL BC (dmC k) (t.ra (nS + k)) := by
      refine ⟨⟨?_, ?_, ?_, hC.hdr, hC.ent, hC.disj, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h8C k hk]; omega
      · rw [hcxC k hk, h8C k hk]; omega
      · rw [hdiC k hk, hBCs]; omega
      · intro x h1 h2
        rw [hdiC k hk, hBCs] at *
        rw [hcxC k hk, h8C k hk]
        rcases hapart x (by omega) (by omega) with h | h
        · exact .inl (by omega)
        · exact .inr (by omega)
      · intro q hq
        rw [hdiC k hk, hd]
        have := hH.hB (LC + q) (by rw [hBCs] at hq; omega)
        rw [hdi, show outAddr dm₀.regs.r8.toNat + 8 * (LC + q) = outAddr dm₀.regs.r8.toNat + 8 * LC + 8 * q by omega]
          at this
        rw [this]
        simp [BC, Array.getElem_extract]
      · intro x h1 h2
        rw [hcxC k hk, h8C k hk] at *
        rw [hd]; exact hH.hmap x (by rw [hcx]; omega) (by rw [hcx, h8]; omega)
      · rw [hd, hsp]; exact hH.hra
      · intro x h1 h2
        rw [hsp] at h1 h2
        obtain ⟨q1, q2, q3⟩ := hH.hcs x h1 h2
        rw [hcx, h8] at q2
        rw [hdi] at q3
        refine ⟨by rw [hd]; exact q1, ?_, ?_⟩
        · rw [hcxC k hk, h8C k hk]
          rcases q2 with h | h
          · exact .inl (by omega)
          · exact .inr (by omega)
        · rw [hdiC k hk, hBCs]
          intro ⟨h3, h4⟩; exact q3 ⟨by omega, by omega⟩
      · rw [hsp]; exact hH.hcs24
      · rw [hsp]; exact hH.hcs8
    have hEv := abiB_outcome2 checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok
      checkerProgI_wf MODE PLO PHI OUT HDRF CTLF hdrHw frozenIdsL parOwnedL (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) k0 hc L.Checker.checkL checkerProg_lookup_check (by decide)
      B BC r (t.dm (nS + k)) (dmC k) (t.ra (nS + k)) h5 hH.hB (hk2 ▸ habove (nS + k) (by omega) (by omega)) hL5'
      (by rw [h8]; exact hneed2) hbc hd hsp (by rw [hdiC k hk, hdi, hL5]) (by rw [hcxC k hk, hcx])
      (by rw [h8C k hk, h8]) (by rw [hcxC k hk]; rw [hd] at hr; exact hr) checker_bufMinOk
    rw [hdiC k hk, hcxC k hk, hk2] at hEv
    have h := ret (nS + k) (by omega) _ hEv (fun s h => h.1)
    rwa [← entryPost_congr (dm' := dmC k) (dm := t.dm (nS + k)) hd hsp (by rw [hdmC]; exact cpShift_rbp ..)
      (by rw [hdmC]; exact cpShift_r14 ..) (by rw [hdmC]; exact cpShift_r15 ..) (by rw [hdmC]; exact cpShift_rbx ..)
      (by rw [hdmC]; exact cpShift_r12 ..) (by rw [hdmC]; exact cpShift_r13 ..), ← hrdxC k] at h
  -- the header-C chain: the calls `nS, …, i - 1`
  have hn2 : workerNeed parOwnedL ≤ t.blen - workerNeed parOwnedL := by omega
  have hf2 : t.base + workerNeed parOwnedL + (t.blen - workerNeed parOwnedL) < 2 ^ 64 := by omega
  obtain ⟨rmC, h0C, hrunC⟩ := thread_chain checkerProg checkerTab checkerTab_abiOk hnres frozenIdsL parOwnedL
    parOwnedL_not_frozen PLO PHI MODE BC (outAddr dm₀.regs.r8.toNat + 8 * LC) (t.base + workerNeed parOwnedL)
    (t.blen - workerNeed parOwnedL) (i - nS) hn2 hf2 dmC (fun k => t.ra (nS + k))
    (fun k => t.st (nS + k))
    (fun _ x h1 h2 => by
      rw [hdmem, Nat.add_zero]
      exact hzero2 nS (Nat.le_refl _) x h1 (by omega))
    (fun k hk => hpostC k (by omega)) (fun k hk => acc (nS + k) (by omega))
    (fun k hk x h1 h2 => by
      rw [hdmem]
      exact next (nS + k) (by omega) x (by omega) (by omega))
  -- the region at call `i`
  have hregC : RegionRel checkerTab (t.base + workerNeed parOwnedL) parOwnedL (rmC (i - nS)) (dmC (i - nS)).dmem := by
    rcases hiz : i - nS with _ | k
    · rw [h0C, hdmem, Nat.add_zero]
      exact regionRel_zero checkerTab_abiOk hn2 hf2 _ (fun x h1 h2 => hzero2 nS (Nat.le_refl _) x h1 (by omega))
    · obtain ⟨-, -, -, h3, -⟩ := hrunC k (by omega)
      refine (RegionRel.of_memRel parOwnedL_not_frozen h3).transfer checkerTab_abiOk hn2 fun x h1 h2 => ?_
      rw [hdmem]
      exact next (nS + k) (by omega) x (by omega) (by omega)
  obtain ⟨-, -, -, hout⟩ := hpostC (i - nS) (Nat.le_refl _) (rmC (i - nS)) hregC
  have hsi : nS + (i - nS) = i := by omega
  rw [hsi] at hout
  obtain ⟨e, he, hrax⟩ := outcome_err (hout.resolve_left (by rw [rdx]; decide)) rdx
  rw [hrdxC, hsi] at he
  refine ⟨e, hrax, .inr ⟨hge, (List.range' 0 (i - nS)).map fun k => ((dmC k).regs.rdx, abiFuel, rmC (k + 1)),
    ?_, ?_⟩⟩
  · rw [← h0C]
    exact cp_fails BC (fun k => (dmC k).regs.rdx) rmC (i - nS) _ e (fun k hk => by
      obtain ⟨rs, h1, -, h3, -⟩ := hrunC k hk
      refine ⟨⟨rs, h1⟩, bufKept_of_memRel h3 hC.ent fun q hq => ?_⟩
      have := kept (nS + k) (by omega) (LC + q) (by rw [hBCs] at hq; omega)
      rw [show outAddr dm₀.regs.r8.toNat + 8 * (LC + q) = outAddr dm₀.regs.r8.toNat + 8 * LC + 8 * q by omega]
        at this
      rw [this]
      simp [BC, Array.getElem_extract]) he (i - nS) 0 (by omega)
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have hk' := (List.mem_range'_1.mp hk).2
    have e1 := habove (nS + k) (by omega) (by omega)
    have e3 := UInt64.lt_iff_toNat_lt.mp (incr (nS + k) i (by omega) (Nat.le_refl _))
    show (dmC k).regs.rdx < _
    rw [hrdxC, UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ e1, UInt64.toNat_sub_of_le _ _ hge]
    have := UInt64.le_iff_toNat_le.mp e1
    omega

end ConAgua.Final
