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
buffer of its own). `ca_check_b`'s prologue maps a job index `j < kS` to header S's job `j` and
`j ≥ kS` to header C's job `j - kS`, both on the thread's one region (`abiB_outcome`,
`abiB_outcome2`; `cp_post` picks the phase).

`cpThreadsAcc_runs`: a thread of `ThreadsAcc` (the flat threaded harness's facts, unchanged) over
such a buffer ran one chain of L calls from the zero region (`cp_chain`): first its calls with an
index below `kS` over header S (a prefix of its calls, since its claims increase), then, from the
memory they left (`runsEnd`), its calls with an index at least `kS` over header C, at the index
less `kS`.
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

/-- **The memory a thread's calls `cs` from `r` end in** (`r` if there are none). -/
def runsEnd : Mem → List (Word × Nat × Mem) → Mem
  | r, [] => r
  | _, (_, _, r') :: cs => runsEnd r' cs

/-- A chain of runs over consecutive calls `lo ≤ s, …, n - 1` (`threadRuns_range`, at any count,
start and job indices). -/
theorem cp_runs (B : Array Word) (g : Nat → Word) (rm : Nat → Mem) (lo n : Nat)
    (h : ∀ i, lo ≤ i → i < n →
      (∃ rs, L.run checkerProg abiFuel "check" [] (bufMem B (rm i) (g i)) = .ok (rs, rm (i + 1))) ∧
      BufKept B (rm (i + 1))) :
    ∀ c s, lo ≤ s → s + c = n → ThreadRuns B (rm s) ((List.range' s c).map fun i => (g i, abiFuel, rm (i + 1)))
  | 0, _, _, _ => trivial
  | c + 1, s, hl, hs => by
    obtain ⟨h1, h2⟩ := h s hl (by omega)
    exact ⟨by simp [abiFuel], h1, h2, cp_runs B g rm lo n h c (s + 1) (by omega) (by omega)⟩

/-- The end of such a chain. -/
theorem cp_runsEnd (g : Nat → Word) (rm : Nat → Mem) :
    ∀ c s, runsEnd (rm s) ((List.range' s c).map fun i => (g i, abiFuel, rm (i + 1))) = rm (s + c)
  | 0, s => rfl
  | c + 1, s => by
    rw [List.range'_succ, List.map_cons, runsEnd, cp_runsEnd g rm c (s + 1)]
    congr 1; omega

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

/-! ## The chain over calls of both phases -/

section
variable (p : Prog) (tab : Tab) (fz own : List TieredArray) (plo phi mode : GVar)

/-- **A thread's chain of accepting calls, each over its own buffer** (`thread_chain` with call
`i`'s buffer `Bf i` at `bf i` and job `jf i`): from the zero region, each call's run returns the
next region memory; and the region memory after `n` calls stands for any memory that agrees on
the region with the last call's return (or is zero, for `n = 0`). -/
theorem cp_chain (hok : abiTabOk tab = true) (hnres : 1 ≤ tab.nres) (hdisj : ∀ a ∈ own, a ∉ fz)
    (Bf : Nat → Array Word) (bf : Nat → Nat) (jf : Nat → Word)
    (base blen n : Nat) (hn : workerNeed own ≤ blen) (hf : base + blen < 2 ^ 64)
    (dm : Nat → MachineData) (ra : Nat → Word) (st : Nat → MachineState)
    (hzero : 0 < n → ∀ x, base ≤ x → x < base + blen → (dm 0).dmem.get? (A x) = some 0)
    (hpost : ∀ i < n, ∀ r, RegionRel tab base own r (dm i).dmem →
      EntryPost (bufLayout tab (bf i) (Bf i) base fz own) (dm i) (ra i)
        (L.run p abiFuel "check" [] (bufMemG fz own plo phi mode (Bf i) r (jf i))) (st i))
    (hacc : ∀ i < n, (st i).data.regs.rdx = 0 ∧ (st i).data.regs.rax = ACCEPT)
    (hnext : ∀ i, i + 1 < n → ∀ x, base ≤ x → x < base + blen →
      (dm (i + 1)).dmem.get? (A x) = (st i).data.dmem.get? (A x)) :
    ∃ rm : Nat → Mem, rm 0 = zeroMem tab ∧ (∀ i < n, ∃ rs,
      L.run p abiFuel "check" [] (bufMemG fz own plo phi mode (Bf i) (rm i) (jf i)) = .ok (rs, rm (i + 1)) ∧
      rs.getD 0 0 = ACCEPT ∧ MemRel (bufLayout tab (bf i) (Bf i) base fz own) (rm (i + 1)) (st i).data.dmem ∧
      RegsRestored (dm i).regs (st i).data.regs) ∧
    ∀ d : DataMem, (∀ x, base ≤ x → x < base + blen →
      d.get? (A x) = if n = 0 then some 0 else (st (n - 1)).data.dmem.get? (A x)) →
      RegionRel tab base own (rm n) d := by
  suffices H : ∀ m ≤ n, ∃ rm : Nat → Mem, rm 0 = zeroMem tab ∧
      (∀ i < m, ∃ rs, L.run p abiFuel "check" [] (bufMemG fz own plo phi mode (Bf i) (rm i) (jf i)) =
        .ok (rs, rm (i + 1)) ∧ rs.getD 0 0 = ACCEPT ∧
        MemRel (bufLayout tab (bf i) (Bf i) base fz own) (rm (i + 1)) (st i).data.dmem ∧
        RegsRestored (dm i).regs (st i).data.regs) ∧
      ∀ d : DataMem, (∀ x, base ≤ x → x < base + blen →
        d.get? (A x) = if m = 0 then some 0 else (st (m - 1)).data.dmem.get? (A x)) →
        RegionRel tab base own (rm m) d from H n (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨fun _ => zeroMem tab, rfl, fun i h => absurd h (by omega),
      fun d hd => regionRel_zero hok hn hf d fun x h1 h2 => by rw [hd x h1 h2]; rfl⟩
  | succ m ih =>
    intro hm
    obtain ⟨rm, h0, hrun, hreg⟩ := ih (by omega)
    have hregm : RegionRel tab base own (rm m) (dm m).dmem := hreg _ fun x h1 h2 => by
      rcases m with _ | m
      · exact hzero (by omega) x h1 h2
      · exact hnext m (by omega) x h1 h2
    obtain ⟨-, hRR, -, hout⟩ := hpost m (by omega) (rm m) hregm
    obtain ⟨hrdx, hrax⟩ := hacc m (by omega)
    have hout' := hout.resolve_left (by rw [hrdx]; decide)
    rcases hres : L.run p abiFuel "check" [] (bufMemG fz own plo phi mode (Bf m) (rm m) (jf m))
      with e | ⟨rs, m'⟩
    · rw [hres] at hout'
      cases e <;> simp only [OutcomeRel] at hout' <;> (rw [hrdx] at hout'; exact absurd hout'.1 (by decide))
    rw [hres] at hout'
    obtain ⟨-, hRes, hMem⟩ := hout'
    have hrax' : (st m).data.regs.rax = rs.getD 0 0 := hRes.1 0 (by simp only [bufLayout_tab]; omega) (by decide)
    refine ⟨fun i => if i ≤ m then rm i else m', by simp [h0], fun i hi => ?_, fun d hd => ?_⟩
    · by_cases him : i < m
      · obtain ⟨rs', h1, h2, h3, h4⟩ := hrun i him
        refine ⟨rs', ?_, h2, ?_, h4⟩
        · simp only [show i ≤ m by omega, show i + 1 ≤ m by omega, ite_true]
          exact h1
        · simp only [show i + 1 ≤ m by omega, ite_true]
          exact h3
      · obtain rfl : i = m := by omega
        refine ⟨rs, ?_, by rw [← hrax']; exact hrax, ?_, hRR⟩
        · simp only [Nat.le_refl, ite_true, show ¬ i + 1 ≤ i by omega, ite_false]
          exact hres
        · simp only [show ¬ i + 1 ≤ i by omega, ite_false]
          exact hMem
    · simp only [show ¬ m + 1 ≤ m by omega, ite_false]
      refine (RegionRel.of_memRel hdisj hMem).transfer hok hn fun x h1 h2 => ?_
      rw [hd x h1 h2]
      simp

end

/-! ## One call, in its phase -/

/-- The buffer a call of index `j` runs on: header C's (the suffix at `LC`) if `kS ≤ j`. -/
def cpB (B : Array Word) (LC : Nat) (kS j : Word) : Array Word := if kS ≤ j then B.extract LC B.size else B
/-- Its address. -/
def cpA (buf LC : Nat) (kS j : Word) : Nat := if kS ≤ j then buf + 8 * LC else buf
/-- Its job. -/
def cpJ (kS j : Word) : Word := if kS ≤ j then j - kS else j

set_option linter.constructorNameAsVariable false in
/-- **`ca_check_b` of `checker.s` over a two-phase buffer, either phase** (`abiB_outcome`,
`abiB_outcome2`): the run of `check` on the call's phase's buffer and job, on the call's region. -/
theorem cp_post [Host] (k0 : Nat) (hcode : Code checkerFile k0) (B : Array Word) (hS : HdrOk B) (LC : Nat)
    (hL5 : (B.getD 5 0).toNat = LC) (hL0 : LC ≠ 0) (hC : HdrOk (B.extract LC B.size))
    (kS : Word) (hk2 : B.getD 2 0 = kS) (dm : MachineData) (ra : Word) (hH : BufCallH B dm ra) (r : Mem)
    (hr : RegionRel checkerTab dm.regs.rcx.toNat parOwnedL r dm.dmem) :
    Ev (EntryPost (bufLayout checkerTab (cpA dm.regs.rdi.toNat LC kS dm.regs.rdx) (cpB B LC kS dm.regs.rdx)
        dm.regs.rcx.toNat frozenIdsL parOwnedL) dm ra
      (L.run checkerProg abiFuel "check" [] (bufMemG frozenIdsL parOwnedL PLO PHI MODE (cpB B LC kS dm.regs.rdx) r
        (cpJ kS dm.regs.rdx)))) dm (label abiCheckBL) := by
  have hc := code_of_checkerFile_par hcode
  have h5 : 5 < B.size := by have := hS.hdr 0 (by decide); omega
  by_cases hph : kS ≤ dm.regs.rdx
  · simp only [cpA, cpB, cpJ, hph, ite_true]
    have hL5' : B.getD 5 0 ≠ 0 := fun h => hL0 (by rw [← hL5, h]; rfl)
    have hLB : LC ≤ B.size := by
      have := hC.hdr 0 (by decide); simp only [Array.size_extract] at this; omega
    have hb8 : dm.regs.rdi.toNat + 8 * LC < 2 ^ 64 := by have := hH.bend; omega
    have hBCs : (B.extract LC B.size).size = B.size - LC := by simp
    let dm' : MachineData := { dm with regs := { dm.regs with
      rdi := UInt64.ofNat (dm.regs.rdi.toNat + 8 * LC) } }
    have hdi' : dm'.regs.rdi.toNat = dm.regs.rdi.toNat + 8 * LC :=
      UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using hb8)
    have hbc : BufCall checkerTab frozenIdsL parOwnedL (B.extract LC B.size) dm' ra := by
      refine ⟨⟨hH.need, hH.fits, ?_, hC.hdr, hC.ent, hC.disj, ?_⟩, ?_, hH.hmap, hH.hra, ?_, hH.hcs24, hH.hcs8⟩
      · rw [hdi', hBCs]; have := hH.bend; omega
      · intro x h1 h2
        rw [hdi', hBCs] at *
        exact hH.apart x (by omega) (by omega)
      · intro q hq
        rw [hdi']
        have := hH.hB (LC + q) (by rw [hBCs] at hq; omega)
        rw [show dm.regs.rdi.toNat + 8 * (LC + q) = dm.regs.rdi.toNat + 8 * LC + 8 * q by omega] at this
        rw [this]
        simp [Array.getElem_extract]
      · intro x h1 h2
        obtain ⟨q1, q2, q3⟩ := hH.hcs x h1 h2
        refine ⟨q1, q2, ?_⟩
        rw [hdi', hBCs]
        intro ⟨h3, h4⟩; exact q3 ⟨by omega, by omega⟩
    have hEv := abiB_outcome2 checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok
      checkerProgI_wf MODE PLO PHI OUT HDRF CTLF hdrHw frozenIdsL parOwnedL (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) k0 hc L.Checker.checkL checkerProg_lookup_check (by decide)
      B (B.extract LC B.size) r dm dm' ra h5 hH.hB (hk2 ▸ hph) hL5' hbc rfl rfl (by rw [hdi', hL5]) rfl rfl hr
      checker_bufMinOk
    rw [hdi', hk2] at hEv
    exact hEv
  · simp only [cpA, cpB, cpJ, hph, ite_false]
    have hbc : BufCall checkerTab frozenIdsL parOwnedL B dm ra :=
      ⟨⟨hH.need, hH.fits, hH.bend, hS.hdr, hS.ent, hS.disj, hH.apart⟩, hH.hB, hH.hmap, hH.hra, hH.hcs,
        hH.hcs24, hH.hcs8⟩
    exact abiB_outcome checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok
      checkerProgI_wf MODE PLO PHI OUT HDRF CTLF hdrHw frozenIdsL parOwnedL (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) k0 hc L.Checker.checkL checkerProg_lookup_check (by decide)
      B r dm ra hbc hr checker_bufMinOk h5 (.inl (hk2 ▸ UInt64.not_le.mp hph))

/-- Header C's words in place: the buffer's words at `buf + 8 · (LC + q)` are the suffix's. -/
theorem cp_keptC {B : Array Word} {LC : Nat} {d : DataMem} {buf : Nat}
    (h : ∀ q (h : q < B.size), rdW d (A (buf + 8 * q)) = some B[q]) :
    ∀ q (hq : q < (B.extract LC B.size).size),
      rdW d (A (buf + 8 * LC + 8 * q)) = some (B.extract LC B.size)[q] := by
  intro q hq
  have hq' : LC + q < B.size := by simp at hq; omega
  rw [show buf + 8 * LC + 8 * q = buf + 8 * (LC + q) by omega, h _ hq']
  simp [Array.getElem_extract]

/-- The phase split of a thread whose claims increase: the calls before `nS` are header S's, the
others header C's. -/
theorem cp_phases (n : Nat) (jf : Nat → Word) (kS : Word)
    (incr : ∀ i₁ i₂, i₁ < i₂ → i₂ < n → jf i₁ < jf i₂) :
    ∃ nS ≤ n, (∀ i < nS, jf i < kS) ∧ ∀ i, nS ≤ i → i < n → kS ≤ jf i := by
  obtain ⟨nS, hnS, hlt, hat⟩ := cp_split n (fun i => kS ≤ jf i)
  refine ⟨nS, hnS, fun i hi => UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_not_le fun hle =>
    hlt i hi (UInt64.le_iff_toNat_le.mpr hle)), fun i h1 h2 => ?_⟩
  have hs := hat (by omega)
  rcases Nat.eq_or_lt_of_le h1 with e | lt
  · rw [← e]; exact hs
  · have := UInt64.lt_iff_toNat_lt.mp (incr _ _ lt h2)
    have := UInt64.le_iff_toNat_le.mp hs
    exact UInt64.le_iff_toNat_le.mpr (by omega)

/-! ## A thread's accepting calls -/

set_option linter.constructorNameAsVariable false in
/-- **Each thread's calls over a two-phase buffer, at the L level**: for a buffer `B` with header
S (`HdrOk B`, word `2` = `kS`, word `5` = `LC ≠ 0`) and header C at word `LC` (`HdrOk BC`,
`BC = B.extract LC B.size`), entry 1 returning `2^63 + kS + c`, a thread of `ThreadsAcc` ran a
chain of L calls over `B` from the zero region on its indices below `kS`, then, from the memory
they left, one over `BC` on its indices at least `kS` (less `kS`, below `c`), each increasing; and
every call returned with the caller's registers. -/
theorem cpThreadsAcc_runs [Host] (k0 : Nat) (hcode : Code checkerFile k0) (dm₀ : MachineData)
    (st₀ : MachineState) (B : Array Word) (ths : List ThreadM) (hA : ThreadsAcc dm₀ st₀ B ths)
    (hS : HdrOk B) (LC : Nat) (hL5 : (B.getD 5 0).toNat = LC) (hL0 : LC ≠ 0)
    (hC : HdrOk (B.extract LC B.size)) (kS c : Word) (hk2 : B.getD 2 0 = kS)
    (hk : st₀.data.regs.rax - 9223372036854775808 = kS + c) (hnov : kS.toNat + c.toNat < 2 ^ 64) :
    ∀ t, ∃ csS csC : List (Word × Nat × Mem), t ∈ ths →
      ThreadRuns B (zeroMem checkerTab) csS ∧ (∀ x ∈ csS, x.1 < kS) ∧ (csS.map (·.1)).Pairwise (· < ·) ∧
      ThreadRuns (B.extract LC B.size) (runsEnd (zeroMem checkerTab) csS) csC ∧ (∀ x ∈ csC, x.1 < c) ∧
      (csC.map (·.1)).Pairwise (· < ·) ∧
      (∀ i < t.n, ((t.dm i).regs.rdx < kS ∧ ∃ x ∈ csS, x.1 = (t.dm i).regs.rdx) ∨
        (kS ≤ (t.dm i).regs.rdx ∧ ∃ x ∈ csC, x.1 = (t.dm i).regs.rdx - kS)) ∧
      (∀ i < t.n, RegsRestored (t.dm i).regs (t.st i).data.regs) := by
  intro t
  by_cases ht : t ∈ ths
  case neg => exact ⟨[], [], fun h => absurd h ht⟩
  by_cases hn0 : t.n = 0
  · exact ⟨[], [], fun _ => ⟨trivial, fun x h => absurd h (by simp), List.Pairwise.nil, trivial,
      fun x h => absurd h (by simp), List.Pairwise.nil, fun i hi => absurd hi (by omega),
      fun i hi => absurd hi (by omega)⟩⟩
  obtain ⟨hH0, -, hcx0, h80⟩ := hA.calls t ht 0 (by omega)
  have hneed : workerNeed parOwnedL ≤ t.blen := h80 ▸ hH0.need
  have hfit : t.base + t.blen < 2 ^ 64 := hcx0 ▸ h80 ▸ hH0.fits
  obtain ⟨nS, hnS, hbelow, habove⟩ := cp_phases t.n (fun i => (t.dm i).regs.rdx) kS (hA.incr t ht)
  -- one chain over all calls
  obtain ⟨rm, h0, hrun, -⟩ := cp_chain checkerProg checkerTab frozenIdsL parOwnedL PLO PHI MODE
    checkerTab_abiOk (by decide) parOwnedL_not_frozen (fun i => cpB B LC kS (t.dm i).regs.rdx)
    (fun i => cpA (outAddr dm₀.regs.r8.toNat) LC kS (t.dm i).regs.rdx) (fun i => cpJ kS (t.dm i).regs.rdx)
    t.base t.blen t.n hneed hfit t.dm t.ra t.st (fun h => hA.zero t ht h)
    (fun i hi r hr => by
      obtain ⟨hH, hdi, hcx, -⟩ := hA.calls t ht i hi
      have hEv := cp_post k0 hcode B hS LC hL5 hL0 hC kS hk2 (t.dm i) (t.ra i) hH r (by rw [hcx]; exact hr)
      rw [hdi, hcx] at hEv
      exact hA.ret t ht i hi _ hEv (fun s h => h.1))
    (fun i hi => hA.acc t ht i hi) (fun i hi => hA.next t ht i hi)
  -- the header-S chain
  let csS := (List.range' 0 nS).map fun i => ((t.dm i).regs.rdx, abiFuel, rm (i + 1))
  have hRS : ThreadRuns B (zeroMem checkerTab) csS := by
    rw [← h0]
    refine cp_runs B (fun i => (t.dm i).regs.rdx) rm 0 nS (fun i _ hi => ?_) nS 0 (Nat.le_refl _) (by omega)
    obtain ⟨rs, h1, -, h3, -⟩ := hrun i (by omega)
    have hn := UInt64.not_le.mpr (hbelow i hi)
    simp only [cpB, cpA, cpJ, hn, ite_false] at h1 h3
    exact ⟨⟨rs, h1⟩, bufKept_of_memRel h3 hS.ent (hA.kept t ht i (by omega))⟩
  have hend : runsEnd (zeroMem checkerTab) csS = rm nS := by
    rw [← h0]; exact (cp_runsEnd _ rm nS 0).trans (by rw [Nat.zero_add])
  -- the header-C chain
  let csC := (List.range' nS (t.n - nS)).map fun i => ((t.dm i).regs.rdx - kS, abiFuel, rm (i + 1))
  have hRC : ThreadRuns (B.extract LC B.size) (rm nS) csC := by
    refine cp_runs _ (fun i => (t.dm i).regs.rdx - kS) rm nS t.n (fun i h1 h2 => ?_) (t.n - nS) nS
      (Nat.le_refl _) (by omega)
    obtain ⟨rs, r1, -, r3, -⟩ := hrun i h2
    have hp := habove i h1 h2
    simp only [cpB, cpA, cpJ, hp, ite_true] at r1 r3
    exact ⟨⟨rs, r1⟩, bufKept_of_memRel r3 hC.ent (cp_keptC (hA.kept t ht i h2))⟩
  refine ⟨csS, csC, fun _ => ⟨hRS, ?_, ?_, by rw [hend]; exact hRC, ?_, ?_, ?_, ?_⟩⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hbelow i (by have := List.mem_range'_1.mp hi; omega)
  · simp only [csS, List.map_map]
    rw [List.pairwise_map]
    refine (List.pairwise_lt_range' (s := 0) (n := nS)).imp_of_mem fun hi hj hij => ?_
    exact hA.incr t ht _ _ hij (by have := List.mem_range'_1.mp hj; omega)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range'_1.mp hi
    have hcl := hA.claimed t ht i (by omega)
    rw [hk] at hcl
    exact cp_sub_lt hcl (habove i (by omega) (by omega)) hnov
  · simp only [csC, List.map_map]
    rw [List.pairwise_map]
    refine (List.pairwise_lt_range' (s := nS) (n := t.n - nS)).imp_of_mem fun hi hj hij => ?_
    have hi' := List.mem_range'_1.mp hi
    have hj' := List.mem_range'_1.mp hj
    rename_i a b
    have e1 := habove a (by omega) (by omega)
    have e2 := habove b (by omega) (by omega)
    have e3 := UInt64.lt_iff_toNat_lt.mp (hA.incr t ht a b hij (by omega))
    simp only [Function.comp]
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ e1, UInt64.toNat_sub_of_le _ _ e2]
    have := UInt64.le_iff_toNat_le.mp e1
    omega
  · intro i hi
    rcases Nat.lt_or_ge i nS with h | h
    · exact .inl ⟨hbelow i h, _, List.mem_map.mpr ⟨i, List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩, rfl⟩, rfl⟩
    · exact .inr ⟨habove i h hi, _, List.mem_map.mpr ⟨i, List.mem_range'_1.mpr ⟨h, by omega⟩, rfl⟩, rfl⟩
  · intro i hi
    obtain ⟨_, -, -, -, h⟩ := hrun i hi; exact h

end ConAgua.Final
