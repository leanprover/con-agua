module

public import ConAgua.Final.ThreadsFinal
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
# A thread's calls over a buffer with two phases (lane compare2)

The compared run's entry 1 leaves one buffer with two headers: header S at the buffer's start
(word `2` the solution's job count `kS`, word `5` the offset `L` of header C, in words) and header
C at word `L`, whose entries are relative to it (the buffer's suffix `B.extract L B.size` is a
buffer of its own). `ca_check_b`'s prologue maps a job index `j < kS` to header S's job `j` on the
region's first `workerNeed` bytes, and `j ≥ kS` to header C's job `j - kS` on the bytes after
(`abiB_outcome`, `abiB_outcome2`).

`cpThreadsAcc_runs`: a thread of `ThreadsAcc` (the flat threaded harness's facts, unchanged) over
such a buffer ran two chains of L calls, each from the zero region (`ThreadRuns`): its calls with
an index below `kS` over header S (a prefix of its calls, since its claims increase), and its
calls with an index at least `kS` over header C, at the index less `kS`. The second sub-region is
zero at the thread's first header-C call: the header-S calls write only the first
(`cp_frameS`, `MemFrame` of `bufLayout` at the region's first `workerNeed` bytes).
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

/-- A buffer's header facts (`BufGeom`'s, for the frozen arrays): the header's entries inside the
buffer, and apart from each other. -/
structure HdrOk (B : Array Word) : Prop where
  hdr : ∀ i < frozenIdsL.length, 9 + 2 * i < B.size
  ent : ∀ i < frozenIdsL.length, (bufEntry B i).1 + (bufEntry B i).2 ≤ B.size
  disj : ∀ i < frozenIdsL.length, ∀ i' < frozenIdsL.length, i ≠ i' →
    (bufEntry B i).1 + (bufEntry B i).2 ≤ (bufEntry B i').1 ∨
    (bufEntry B i').1 + (bufEntry B i').2 ≤ (bufEntry B i).1 ∨ (bufEntry B i).2 = 0 ∨ (bufEntry B i').2 = 0

/-- A chain of runs over consecutive calls (`threadRuns_range`, at any count and job indices). -/
theorem cp_runs (B : Array Word) (g : Nat → Word) (rm : Nat → Mem) (n : Nat)
    (h : ∀ i < n, (∃ rs, L.run checkerProg abiFuel "check" [] (bufMem B (rm i) (g i)) = .ok (rs, rm (i + 1))) ∧
      BufKept B (rm (i + 1))) :
    ∀ c s, s + c = n → ThreadRuns B (rm s) ((List.range' s c).map fun i => (g i, abiFuel, rm (i + 1)))
  | 0, _, _ => trivial
  | c + 1, s, hs => by
    obtain ⟨h1, h2⟩ := h s (by omega)
    exact ⟨by simp [abiFuel], h1, h2, cp_runs B g rm n h c (s + 1) (by omega)⟩

/-- **A header-S call leaves the second sub-region alone**: a `MemFrame` of `ca_check_b`'s layout on
the region's first `workerNeed` bytes changes no byte past them that is outside the buffer and the
stack window. -/
theorem cp_frameS {B : Array Word} {buf base : Nat} {d d' : DataMem} {sp : Nat}
    (hg : BufGeom checkerTab frozenIdsL parOwnedL B buf base (workerNeed parOwnedL))
    (hF : MemFrame (bufLayout checkerTab buf B base frozenIdsL parOwnedL) sp d d') {x : Nat}
    (hx1 : base + workerNeed parOwnedL ≤ x) (hx2 : x < 2 ^ 64)
    (hbuf : ¬ (buf ≤ x ∧ x < buf + 8 * B.size)) (hwin : x < sp - 24 ∨ sp ≤ x) :
    d'.get? (A x) = d.get? (A x) := by
  have hok := checkerTab_abiOk
  refine hF.same x hx2 (fun h => ?_) (fun h => ?_) (fun h => ?_) hwin ?_
  · rcases buf_part hok hg (.inl h) with h' | h' <;> omega
  · rcases buf_part hok hg (.inr (.inl h)) with h' | h' <;> omega
  · rcases buf_part hok hg (.inr (.inr h)) with h' | h' <;> omega
  · refine Classical.byContradiction fun hn => ?_
    simp only [not_or, Nat.not_lt, Nat.not_le] at hn
    have := (buf_save hok hg hn.1 hn.2).2.1
    omega

/-- A split point of `[0, n)` for a property: none below it, and it holds there (if below `n`). -/
theorem cp_split (n : Nat) (P : Nat → Prop) : ∃ m ≤ n, (∀ i < m, ¬ P i) ∧ (m < n → P m) := by
  induction n with
  | zero => exact ⟨0, Nat.le_refl _, fun i h => absurd h (by omega), fun h => absurd h (by omega)⟩
  | succ n ih =>
    obtain ⟨m, hm, h1, h2⟩ := ih
    rcases Nat.lt_or_ge m n with h | h
    · exact ⟨m, by omega, h1, fun _ => h2 h⟩
    · obtain rfl : m = n := by omega
      by_cases hp : P m
      · exact ⟨m, by omega, h1, fun _ => hp⟩
      · exact ⟨m + 1, Nat.le_refl _, fun i hi => by
          rcases Nat.lt_or_ge i m with h' | h'
          · exact h1 i h'
          · obtain rfl : i = m := by omega
            exact hp, fun h => absurd h (by omega)⟩

/-- `a - b < c` from `a < b + c` without overflow and `b ≤ a`. -/
theorem cp_sub_lt {a b c : Word} (h1 : a < b + c) (h2 : b ≤ a) (hnov : b.toNat + c.toNat < 2 ^ 64) :
    a - b < c := by
  have e1 := UInt64.lt_iff_toNat_lt.mp h1; have e2 := UInt64.le_iff_toNat_le.mp h2
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt hnov] at e1
  exact UInt64.lt_iff_toNat_lt.mpr (by rw [UInt64.toNat_sub_of_le _ _ h2]; omega)

/-- The call as `ca_check_b` runs header C's job: the buffer at header C, the job index less `kS`,
the region's second sub-region (`w = workerNeed parOwnedL`). -/
def cpShift (dm : MachineData) (LC : Nat) (kS : Word) (w : Nat) : MachineData :=
  { dm with regs := { dm.regs with
      rdi := UInt64.ofNat (dm.regs.rdi.toNat + 8 * LC), rdx := dm.regs.rdx - kS,
      rcx := UInt64.ofNat (dm.regs.rcx.toNat + w), r8 := UInt64.ofNat (dm.regs.r8.toNat - w) } }

section
variable (dm : MachineData) (LC : Nat) (kS : Word) (w : Nat)
theorem cpShift_dmem : (cpShift dm LC kS w).dmem = dm.dmem := rfl
theorem cpShift_rsp : (cpShift dm LC kS w).regs.rsp = dm.regs.rsp := rfl
theorem cpShift_rbp : (cpShift dm LC kS w).regs.rbp = dm.regs.rbp := rfl
theorem cpShift_r14 : (cpShift dm LC kS w).regs.r14 = dm.regs.r14 := rfl
theorem cpShift_r15 : (cpShift dm LC kS w).regs.r15 = dm.regs.r15 := rfl
theorem cpShift_rbx : (cpShift dm LC kS w).regs.rbx = dm.regs.rbx := rfl
theorem cpShift_r12 : (cpShift dm LC kS w).regs.r12 = dm.regs.r12 := rfl
theorem cpShift_r13 : (cpShift dm LC kS w).regs.r13 = dm.regs.r13 := rfl
theorem cpShift_rdi : (cpShift dm LC kS w).regs.rdi = UInt64.ofNat (dm.regs.rdi.toNat + 8 * LC) := rfl
theorem cpShift_regsRestored (r : Reg64s) :
    RegsRestored (cpShift dm LC kS w).regs r = RegsRestored dm.regs r := rfl
theorem cpShift_rdx : (cpShift dm LC kS w).regs.rdx = dm.regs.rdx - kS := rfl
theorem cpShift_rcx : (cpShift dm LC kS w).regs.rcx = UInt64.ofNat (dm.regs.rcx.toNat + w) := rfl
theorem cpShift_r8 : (cpShift dm LC kS w).regs.r8 = UInt64.ofNat (dm.regs.r8.toNat - w) := rfl
end

/-- The worker region's two sub-regions are in the address space. -/
theorem cp_wn2 : 2 * workerNeed parOwnedL < 2 ^ 64 := by decide +kernel

set_option linter.constructorNameAsVariable false in
/-- **Each thread's calls over a two-phase buffer, at the L level**: for a buffer `B` with header
S (`HdrOk B`, word `2` = `kS`, word `5` = `L ≠ 0`) and header C at word `L` (`HdrOk BC`,
`BC = B.extract L B.size`), entry 1 returning `2^63 + kS + c`, a thread of `ThreadsAcc` ran a chain
of L calls over `B` from the zero region on its indices below `kS`, and one over `BC` from the zero
region on its indices at least `kS` (less `kS`, below `c`), each increasing; and every call
returned with the caller's registers. -/
theorem cpThreadsAcc_runs [Host] (k0 : Nat) (hcode : Code checkerFile k0) (dm₀ : MachineData)
    (st₀ : MachineState) (B : Array Word) (ths : List ThreadM) (hA : ThreadsAcc dm₀ st₀ B ths)
    (hS : HdrOk B) (LC : Nat) (hL5 : (B.getD 5 0).toNat = LC) (hL0 : LC ≠ 0) (hLB : LC ≤ B.size)
    (hC : HdrOk (B.extract LC B.size)) (kS c : Word) (hk2 : B.getD 2 0 = kS)
    (hk : st₀.data.regs.rax - 9223372036854775808 = kS + c) (hnov : kS.toNat + c.toNat < 2 ^ 64) :
    ∀ t, ∃ csS csC : List (Word × Nat × Mem), t ∈ ths →
      ThreadRuns B (zeroMem checkerTab) csS ∧ (∀ x ∈ csS, x.1 < kS) ∧ (csS.map (·.1)).Pairwise (· < ·) ∧
      ThreadRuns (B.extract LC B.size) (zeroMem checkerTab) csC ∧ (∀ x ∈ csC, x.1 < c) ∧
      (csC.map (·.1)).Pairwise (· < ·) ∧
      (∀ i < t.n, ((t.dm i).regs.rdx < kS ∧ ∃ x ∈ csS, x.1 = (t.dm i).regs.rdx) ∨
        (kS ≤ (t.dm i).regs.rdx ∧ ∃ x ∈ csC, x.1 = (t.dm i).regs.rdx - kS)) ∧
      (∀ i < t.n, RegsRestored (t.dm i).regs (t.st i).data.regs) := by
  have hc := code_of_checkerFile_par hcode
  have hnres : 1 ≤ checkerTab.nres := by decide
  have h5 : 5 < B.size := by have := hS.hdr 0 (by decide); omega
  intro t
  by_cases ht : t ∈ ths
  case neg => exact ⟨[], [], fun h => absurd h ht⟩
  by_cases hn0 : t.n = 0
  · exact ⟨[], [], fun _ => ⟨trivial, fun x h => absurd h (by simp), List.Pairwise.nil, trivial,
      fun x h => absurd h (by simp), List.Pairwise.nil, fun i hi => absurd hi (by omega),
      fun i hi => absurd hi (by omega)⟩⟩
  obtain ⟨hH0, hdi0, hcx0, h80⟩ := hA.calls t ht 0 (by omega)
  have hneed : workerNeed parOwnedL ≤ t.blen := h80 ▸ hH0.need
  have hfit : t.base + t.blen < 2 ^ 64 := hcx0 ▸ h80 ▸ hH0.fits
  have hbend : outAddr dm₀.regs.r8.toNat + 8 * B.size < 2 ^ 64 := hdi0 ▸ hH0.bend
  have hapart : ∀ x, outAddr dm₀.regs.r8.toNat ≤ x → x < outAddr dm₀.regs.r8.toNat + 8 * B.size →
      x < t.base ∨ t.base + t.blen ≤ x := by
    rw [← hdi0, ← hcx0, ← h80]; exact hH0.apart
  -- the split point: the thread's first call at or past `kS`
  obtain ⟨nS, hnS, hlt, hat⟩ := cp_split t.n (fun i => kS ≤ (t.dm i).regs.rdx)
  have hbelow : ∀ i < nS, (t.dm i).regs.rdx < kS := fun i hi =>
    UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_not_le fun hle => hlt i hi (UInt64.le_iff_toNat_le.mpr hle))
  have habove : ∀ i, nS ≤ i → i < t.n → kS ≤ (t.dm i).regs.rdx := by
    intro i h1 h2
    have hs := hat (by omega)
    rcases Nat.eq_or_lt_of_le h1 with e | lt
    · rw [← e]; exact hs
    · have := UInt64.lt_iff_toNat_lt.mp (hA.incr t ht _ _ lt h2)
      have := UInt64.le_iff_toNat_le.mp hs
      exact UInt64.le_iff_toNat_le.mpr (by omega)
  -- the header-S calls (`thread_chain`, `abiB_outcome`)
  have hpostS : ∀ i < nS, ∀ r, RegionRel checkerTab t.base parOwnedL r (t.dm i).dmem →
      EntryPost (bufLayout checkerTab (outAddr dm₀.regs.r8.toNat) B t.base frozenIdsL parOwnedL) (t.dm i)
        (t.ra i) (L.run checkerProg abiFuel "check" [] (bufMemG frozenIdsL parOwnedL PLO PHI MODE B r
          (t.dm i).regs.rdx)) (t.st i) := by
    intro i hi r hr
    obtain ⟨hH, hdi, hcx, h8⟩ := hA.calls t ht i (by omega)
    have hbc : BufCall checkerTab frozenIdsL parOwnedL B (t.dm i) (t.ra i) :=
      ⟨⟨hH.need, hH.fits, hH.bend, hS.hdr, hS.ent, hS.disj, hH.apart⟩, hH.hB, hH.hmap, hH.hra, hH.hcs,
        hH.hcs24, hH.hcs8⟩
    have hEv := abiB_outcome checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok
      checkerProgI_wf MODE PLO PHI OUT HDRF CTLF hdrHw frozenIdsL parOwnedL (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) k0 hc L.Checker.checkL checkerProg_lookup_check (by decide)
      B r (t.dm i) (t.ra i) hbc (by rw [hcx]; exact hr) checker_bufMinOk h5 (.inl (hk2 ▸ hbelow i hi))
    rw [hdi, hcx] at hEv
    exact hA.ret t ht i (by omega) _ hEv (fun s h => h.1)
  obtain ⟨rmS, h0S, hrunS⟩ := thread_chain checkerProg checkerTab checkerTab_abiOk hnres frozenIdsL parOwnedL
    parOwnedL_not_frozen PLO PHI MODE B (outAddr dm₀.regs.r8.toNat) t.base t.blen nS hneed hfit t.dm t.ra t.st
    (fun _ => hA.zero t ht (by omega)) hpostS (fun i hi => hA.acc t ht i (by omega))
    (fun i hi => hA.next t ht i (by omega))
  -- the region at each header-S call
  have hregS : ∀ i < nS, RegionRel checkerTab t.base parOwnedL (rmS i) (t.dm i).dmem := by
    intro i hi
    rcases i with _ | i
    · rw [h0S]; exact regionRel_zero checkerTab_abiOk hneed hfit _ (hA.zero t ht (by omega))
    · obtain ⟨-, -, -, h3, -⟩ := hrunS i (by omega)
      exact (RegionRel.of_memRel parOwnedL_not_frozen h3).transfer checkerTab_abiOk hneed
        (hA.next t ht i (by omega))
  -- the second sub-region is zero at each call up to `nS`
  have hzero2 : ∀ i ≤ nS, i < t.n → ∀ x, t.base + workerNeed parOwnedL ≤ x → x < t.base + t.blen →
      (t.dm i).dmem.get? (A x) = some 0 := by
    intro i
    induction i with
    | zero => intro _ _ x h1 h2; exact hA.zero t ht (by omega) x (by omega) h2
    | succ i ih =>
      intro hi hin x h1 h2
      rw [hA.next t ht i hin x (by omega) h2]
      obtain ⟨hH, hdi, hcx, h8⟩ := hA.calls t ht i (by omega)
      obtain ⟨-, -, hF, -⟩ := hpostS i (by omega) (rmS i) (hregS i (by omega))
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
      exact ih (by omega) (by omega) x h1 h2
  -- the header-S chain
  let csS := (List.range' 0 nS).map fun i => ((t.dm i).regs.rdx, abiFuel, rmS (i + 1))
  have hRS : ThreadRuns B (zeroMem checkerTab) csS := by
    rw [← h0S]
    refine cp_runs B (fun i => (t.dm i).regs.rdx) rmS nS (fun i hi => ?_) nS 0 (by omega)
    obtain ⟨rs, h1, -, h3, -⟩ := hrunS i hi
    exact ⟨⟨rs, h1⟩, bufKept_of_memRel h3 hS.ent (hA.kept t ht i (by omega))⟩
  have hcovS : ∀ i < nS, ∃ x ∈ csS, x.1 = (t.dm i).regs.rdx := fun i hi =>
    ⟨_, List.mem_map.mpr ⟨i, List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩, rfl⟩, rfl⟩
  have hcsS : ∀ x ∈ csS, x.1 < kS := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hbelow i (by have := List.mem_range'_1.mp hi; omega)
  have hincS : (csS.map (·.1)).Pairwise (· < ·) := by
    simp only [csS, List.map_map]
    rw [List.pairwise_map]
    refine (List.pairwise_lt_range' (s := 0) (n := nS)).imp_of_mem fun hi hj hij => ?_
    exact hA.incr t ht _ _ hij (by have := List.mem_range'_1.mp hj; omega)
  have hregsS : ∀ i < nS, RegsRestored (t.dm i).regs (t.st i).data.regs := fun i hi => by
    obtain ⟨_, -, -, -, h⟩ := hrunS i hi; exact h
  -- no header-C calls
  by_cases hnC : nS = t.n
  · refine ⟨csS, [], fun _ => ⟨hRS, hcsS, hincS, trivial, fun x h => absurd h (by simp), List.Pairwise.nil,
      fun i hi => .inl ⟨hbelow i (by omega), hcovS i (by omega)⟩, fun i hi => hregsS i (by omega)⟩⟩
  have hnC' : nS < t.n := by omega
  -- the header-C calls: the region holds both sub-regions (else the first one declines)
  have hL5' : B.getD 5 0 ≠ 0 := fun h => hL0 (by rw [← hL5, h]; rfl)
  have hwn2 : 2 * workerNeed parOwnedL < 2 ^ 64 := cp_wn2
  have hneed2 : 2 * workerNeed parOwnedL ≤ t.blen := by
    refine Classical.byContradiction fun hlt => ?_
    obtain ⟨hH, hdi, hcx, h8⟩ := hA.calls t ht nS hnC'
    have hEv := abiB_small checkerTab MODE PLO PHI OUT HDRF CTLF hdrHw frozenIdsL parOwnedL hc B (t.dm nS) (t.ra nS)
      h5 hH.hB (hk2 ▸ habove nS (Nat.le_refl _) hnC') hL5' (by rw [h8]; omega) hH.hra hwn2 hH.hcs8
      (bufLayout checkerTab 0 B 0 frozenIdsL parOwnedL) (.error .oob)
    have := (hA.ret t ht nS hnC' _ hEv (fun s h => h.1.1)).2
    rw [(hA.acc t ht nS hnC').1] at this
    exact absurd this (by decide)
  have hb8 : outAddr dm₀.regs.r8.toNat + 8 * LC < 2 ^ 64 := by omega
  -- the calls as `ca_check_b` runs them
  let BC := B.extract LC B.size
  have hBCs : BC.size = B.size - LC := by simp [BC]
  -- (opaque: unfolding `cpShift … (workerNeed parOwnedL)` evaluates the owned arrays' list)
  obtain ⟨dmC, hdmC⟩ : ∃ f : Nat → MachineData,
      ∀ i, f i = cpShift (t.dm (nS + i)) LC kS (workerNeed parOwnedL) := ⟨_, fun _ => rfl⟩
  have hdmem : ∀ i, (dmC i).dmem = (t.dm (nS + i)).dmem := fun i => by rw [hdmC]; exact cpShift_dmem ..
  have hrdxC : ∀ i, (dmC i).regs.rdx = (t.dm (nS + i)).regs.rdx - kS := fun i => by
    rw [hdmC]; exact cpShift_rdx ..
  have hdiC : ∀ i < t.n - nS, (dmC i).regs.rdi.toNat = outAddr dm₀.regs.r8.toNat + 8 * LC := by
    intro i hi
    obtain ⟨-, hdi, -, -⟩ := hA.calls t ht (nS + i) (by omega)
    rw [hdmC, cpShift_rdi, hdi]
    exact UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using hb8)
  have hcxC : ∀ i < t.n - nS, (dmC i).regs.rcx.toNat = t.base + workerNeed parOwnedL := by
    intro i hi
    obtain ⟨-, -, hcx, -⟩ := hA.calls t ht (nS + i) (by omega)
    rw [hdmC, cpShift_rcx, hcx]
    exact UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  have h8C : ∀ i < t.n - nS, (dmC i).regs.r8.toNat = t.blen - workerNeed parOwnedL := by
    intro i hi
    obtain ⟨-, -, -, h8⟩ := hA.calls t ht (nS + i) (by omega)
    rw [hdmC, cpShift_r8, h8]
    exact UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  have hpostC : ∀ i < t.n - nS, ∀ r, RegionRel checkerTab (t.base + workerNeed parOwnedL) parOwnedL r (dmC i).dmem →
      EntryPost (bufLayout checkerTab (outAddr dm₀.regs.r8.toNat + 8 * LC) BC (t.base + workerNeed parOwnedL)
        frozenIdsL parOwnedL) (dmC i) (t.ra (nS + i))
        (L.run checkerProg abiFuel "check" [] (bufMemG frozenIdsL parOwnedL PLO PHI MODE BC r
          (dmC i).regs.rdx)) (t.st (nS + i)) := by
    intro i hi r hr
    obtain ⟨hH, hdi, hcx, h8⟩ := hA.calls t ht (nS + i) (by omega)
    have hd : (dmC i).dmem = (t.dm (nS + i)).dmem := hdmem i
    have hsp : (dmC i).regs.rsp = (t.dm (nS + i)).regs.rsp := by rw [hdmC]; exact cpShift_rsp ..
    have hbc : BufCall checkerTab frozenIdsL parOwnedL BC (dmC i) (t.ra (nS + i)) := by
      refine ⟨⟨?_, ?_, ?_, hC.hdr, hC.ent, hC.disj, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h8C i hi]; omega
      · rw [hcxC i hi, h8C i hi]; omega
      · rw [hdiC i hi, hBCs]; omega
      · intro x h1 h2
        rw [hdiC i hi, hBCs] at *
        rw [hcxC i hi, h8C i hi]
        rcases hapart x (by omega) (by omega) with h | h
        · exact .inl (by omega)
        · exact .inr (by omega)
      · intro q hq
        rw [hdiC i hi, hd]
        have := hH.hB (LC + q) (by rw [hBCs] at hq; omega)
        rw [hdi, show outAddr dm₀.regs.r8.toNat + 8 * (LC + q) = outAddr dm₀.regs.r8.toNat + 8 * LC + 8 * q by omega]
          at this
        rw [this]
        simp [BC, Array.getElem_extract]
      · intro x h1 h2
        rw [hcxC i hi, h8C i hi] at *
        rw [hd]; exact hH.hmap x (by rw [hcx]; omega) (by rw [hcx, h8]; omega)
      · rw [hd, hsp]; exact hH.hra
      · intro x h1 h2
        rw [hsp] at h1 h2
        obtain ⟨q1, q2, q3⟩ := hH.hcs x h1 h2
        rw [hcx, h8] at q2
        rw [hdi] at q3
        refine ⟨by rw [hd]; exact q1, ?_, ?_⟩
        · rw [hcxC i hi, h8C i hi]
          rcases q2 with h | h
          · exact .inl (by omega)
          · exact .inr (by omega)
        · rw [hdiC i hi, hBCs]
          intro ⟨h3, h4⟩; exact q3 ⟨by omega, by omega⟩
      · rw [hsp]; exact hH.hcs24
      · rw [hsp]; exact hH.hcs8
    have hEv := abiB_outcome2 checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok
      checkerProgI_wf MODE PLO PHI OUT HDRF CTLF hdrHw frozenIdsL parOwnedL (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) k0 hc L.Checker.checkL checkerProg_lookup_check (by decide)
      B BC r (t.dm (nS + i)) (dmC i) (t.ra (nS + i)) h5 hH.hB (hk2 ▸ habove (nS + i) (by omega) (by omega)) hL5'
      (by rw [h8]; exact hneed2) hbc hd hsp (by rw [hdiC i hi, hdi, hL5]) (by rw [hcxC i hi, hcx])
      (by rw [h8C i hi, h8]) (by rw [hcxC i hi]; rw [hd] at hr; exact hr) checker_bufMinOk
    rw [hdiC i hi, hcxC i hi, hk2] at hEv
    have h := hA.ret t ht (nS + i) (by omega) _ hEv (fun s h => h.1)
    rwa [← entryPost_congr (dm' := dmC i) (dm := t.dm (nS + i)) hd hsp (by rw [hdmC]; exact cpShift_rbp ..)
      (by rw [hdmC]; exact cpShift_r14 ..) (by rw [hdmC]; exact cpShift_r15 ..) (by rw [hdmC]; exact cpShift_rbx ..)
      (by rw [hdmC]; exact cpShift_r12 ..) (by rw [hdmC]; exact cpShift_r13 ..), ← hrdxC i] at h
  obtain ⟨rmC, h0C, hrunC⟩ := thread_chain checkerProg checkerTab checkerTab_abiOk hnres frozenIdsL parOwnedL
    parOwnedL_not_frozen PLO PHI MODE BC (outAddr dm₀.regs.r8.toNat + 8 * LC) (t.base + workerNeed parOwnedL)
    (t.blen - workerNeed parOwnedL) (t.n - nS) (by omega) (by omega) dmC (fun i => t.ra (nS + i))
    (fun i => t.st (nS + i))
    (fun _ x h1 h2 => by
      rw [hdmem, Nat.add_zero]
      exact hzero2 nS (Nat.le_refl _) hnC' x h1 (by omega))
    hpostC (fun i hi => hA.acc t ht (nS + i) (by omega))
    (fun i hi x h1 h2 => by
      rw [hdmem]
      exact hA.next t ht (nS + i) (by omega) x (by omega) (by omega))
  let csC := (List.range' 0 (t.n - nS)).map fun i => ((dmC i).regs.rdx, abiFuel, rmC (i + 1))
  have hRC : ThreadRuns BC (zeroMem checkerTab) csC := by
    rw [← h0C]
    refine cp_runs BC (fun i => (dmC i).regs.rdx) rmC (t.n - nS) (fun i hi => ?_) (t.n - nS) 0 (by omega)
    obtain ⟨rs, h1, -, h3, -⟩ := hrunC i hi
    refine ⟨⟨rs, h1⟩, bufKept_of_memRel h3 hC.ent fun q hq => ?_⟩
    have := hA.kept t ht (nS + i) (by omega) (LC + q) (by rw [hBCs] at hq; omega)
    rw [show outAddr dm₀.regs.r8.toNat + 8 * (LC + q) = outAddr dm₀.regs.r8.toNat + 8 * LC + 8 * q by omega]
      at this
    rw [this]
    simp [BC, Array.getElem_extract]
  refine ⟨csS, csC, fun _ => ⟨hRS, hcsS, hincS, hRC, ?_, ?_, ?_, ?_⟩⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' := (List.mem_range'_1.mp hi).2
    have hcl := hA.claimed t ht (nS + i) (by omega)
    rw [hk] at hcl
    show (dmC i).regs.rdx < c
    rw [hrdxC]
    exact cp_sub_lt hcl (habove (nS + i) (by omega) (by omega)) hnov
  · simp only [csC, List.map_map]
    rw [List.pairwise_map]
    refine (List.pairwise_lt_range' (s := 0) (n := t.n - nS)).imp_of_mem fun hi hj hij => ?_
    have hj' := (List.mem_range'_1.mp hj).2
    rename_i a b
    have e1 := habove (nS + a) (by omega) (by omega)
    have e2 := habove (nS + b) (by omega) (by omega)
    have e3 := UInt64.lt_iff_toNat_lt.mp (hA.incr t ht (nS + a) (nS + b) (by omega) (by omega))
    simp only [Function.comp, hrdxC]
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ e1, UInt64.toNat_sub_of_le _ _ e2]
    have := UInt64.le_iff_toNat_le.mp e1
    omega
  · intro i hi
    rcases Nat.lt_or_ge i nS with h | h
    · exact .inl ⟨hbelow i h, hcovS i h⟩
    · refine .inr ⟨habove i h hi, _, List.mem_map.mpr ⟨i - nS, List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩, rfl⟩, ?_⟩
      simp only [hrdxC, show nS + (i - nS) = i by omega]
  · intro i hi
    rcases Nat.lt_or_ge i nS with h | h
    · exact hregsS i h
    · obtain ⟨_, -, -, -, hR⟩ := hrunC (i - nS) (by omega)
      rw [hdmC, cpShift_regsRestored] at hR
      simp only [show nS + (i - nS) = i by omega] at hR
      exact hR

end ConAgua.Final
