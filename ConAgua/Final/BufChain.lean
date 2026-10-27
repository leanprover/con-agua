import ConAgua.Final.BufLayout
import ConAgua.Final.ParAbi

/-!
# A thread's chain of `ca_check_b` calls (lane parmode)

A thread calls `ca_check_b` again and again on one region and the same buffer. What a call needs
of the region (`RegionRel … r`) holds on the first call for the zero memory (`regionRel_zero`),
and after each call for the L memory that call ended with (`RegionRel.of_memRel`, from the
call's `OutcomeRel`); the harness does not touch the region between calls (`RegionRel.transfer`).

`thread_chain`: given what each call's return state satisfies (`abiB_outcome`'s post, for the
region's memory at the call) and that every call accepted, there is a sequence of L memories,
the zero memory first, each the final memory of the run before, with every run accepting.
-/

namespace ConAgua.Final

open L L.Compiler L.Arena

/-- The memory of a zero region: every word array `abiWords` zeros, every global `0`. -/
def zeroMem (tab : Tab) : Mem where
  words := Array.replicate tab.nw (Array.replicate abiWords 0)

section
variable {tab : Tab} {fz own : List ArrId} {B : Array Word} {buf base blen : Nat}

/-- A zero region holds the zero memory. -/
theorem regionRel_zero (hok : abiTabOk tab = true) (hn : workerNeed own ≤ blen) (hf : base + blen < 2 ^ 64)
    (d : DataMem) (hz : ∀ x, base ≤ x → x < base + blen → d.get? (A x) = some 0) :
    RegionRel tab base own (zeroMem tab) d := by
  obtain ⟨hnb, htab, -⟩ := abiTabOk_spec hok
  unfold workerNeed at hn
  have hb31 : 2 ^ 31 ≤ blen := by simp only [abiSlot] at hn; omega
  refine ⟨by simp [zeroMem], fun a ha k _ => by simp [zeroMem, Mem.arr64, ha], fun a ha k hk i hi => ?_,
    fun g hg => ?_⟩
  · have hk' := idxOf?_lt hk
    have hle : abiSlot * (2 + k) + abiSlot ≤ abiSlot * (2 + own.length) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    have hi' : i < abiWords := by simpa [zeroMem, Mem.arr64, ha] using hi
    rw [rdW_of_zero (by simp only [abiSlot, abiWords] at hle hn hi' ⊢; omega) fun j hj =>
      hz _ (by omega) (by simp only [abiSlot, abiWords] at hle hn hi' ⊢; omega)]
    simp [zeroMem, Mem.arr64, ha]
  · rw [rdW_of_zero (by simp only [Tab.globOff, Tab.globBase] at *; omega) fun j hj =>
      hz _ (by omega) (by simp only [Tab.globOff, Tab.globBase] at *; omega)]
    rfl

/-- A call's final memory, in its layout, is what the next call needs of the region (the owned
arrays are none of the frozen ones). -/
theorem RegionRel.of_memRel (hdisj : ∀ a ∈ own, a ∉ fz) {m : Mem} {d : DataMem}
    (hm : MemRel (bufLayout tab buf B base fz own) m d) : RegionRel tab base own m d := by
  have hfz : ∀ a k, own.idxOf? a = some k → fz.idxOf? a = none := fun a k hk => by
    have ha : a ∈ own := List.mem_of_getElem? (by
      obtain ⟨h, e, -⟩ := List.idxOf?_eq_some_iff.mp hk
      exact List.getElem?_eq_some_iff.mpr ⟨h, e⟩)
    simpa [List.idxOf?_eq_none_iff] using hdisj a ha
  refine ⟨hm.nw, fun a ha k hk => ?_, fun a ha k hk i hi => ?_, fun g hg => ?_⟩
  · have := hm.size64 a ha
    simpa [bufL, hfz a k hk, hk] using this
  · have := hm.get64 a ha i hi
    simpa [bufB, hfz a k hk, hk] using this
  · have := hm.glob g hg
    rw [← Layout.globAddr_toNat] at this
    exact this

/-- What a call needs of the region reads only the region. -/
theorem RegionRel.transfer (hok : abiTabOk tab = true) (hn : workerNeed own ≤ blen)
    {r : Mem} {d d' : DataMem} (hr : RegionRel tab base own r d)
    (hsame : ∀ x, base ≤ x → x < base + blen → d'.get? (A x) = d.get? (A x)) : RegionRel tab base own r d' := by
  obtain ⟨hnb, htab, -⟩ := abiTabOk_spec hok
  unfold workerNeed at hn
  have hb31 : 2 ^ 31 ≤ blen := by simp only [abiSlot] at hn; omega
  refine ⟨hr.nw, hr.size, fun a ha k hk i hi => ?_, fun g hg => ?_⟩
  · have hk' := idxOf?_lt hk
    have hs := hr.size a ha k hk
    have hle : abiSlot * (2 + k) + abiSlot ≤ abiSlot * (2 + own.length) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    rw [← hr.get a ha k hk i hi]
    refine rdW_congr fun j hj => ?_
    rw [A_add]
    exact hsame _ (by omega) (by simp only [abiSlot, abiWords] at hle hn hs hi ⊢; omega)
  · rw [← hr.glob g hg]
    refine rdW_congr fun j hj => ?_
    rw [A_add]
    exact hsame _ (by omega) (by simp only [Tab.globOff, Tab.globBase] at *; omega)

end

/-- **A thread's chain of accepting `ca_check_b` calls.** Calls `0, …, n - 1` on the region
`[base, base + blen)` (zero at the first call) and the buffer at `buf` holding `B`; the return
state `st i` of call `i` satisfies `abiB_outcome`'s post for the region's memory at the call
(`hpost`), reports accept, and the harness hands the region to the next call unchanged. Then the
region's L memories `rm 0 = zeroMem`, `rm 1`, … are each the final memory of the run before,
every run accepts, and every call returns with the caller's registers (`RegsRestored`). -/
theorem thread_chain (p : Prog) (tab : Tab) (hok : abiTabOk tab = true) (hnres : 1 ≤ tab.nres)
    (fz own : List ArrId) (hdisj : ∀ a ∈ own, a ∉ fz) (plo phi mode : GVar) (B : Array Word)
    (buf base blen n : Nat) (hn : workerNeed own ≤ blen) (hf : base + blen < 2 ^ 64)
    (dm : Nat → MachineData) (ra : Nat → Word) (st : Nat → MachineState)
    (hzero : 0 < n → ∀ x, base ≤ x → x < base + blen → (dm 0).dmem.get? (A x) = some 0)
    (hpost : ∀ i < n, ∀ r, RegionRel tab base own r (dm i).dmem →
      EntryPost (bufLayout tab buf B base fz own) (dm i) (ra i)
        (L.run p abiFuel "check" [] (bufMemG fz own plo phi mode B r (dm i).regs.rdx)) (st i))
    (hacc : ∀ i < n, (st i).data.regs.rdx = 0 ∧ (st i).data.regs.rax = ACCEPT)
    (hnext : ∀ i, i + 1 < n → ∀ x, base ≤ x → x < base + blen →
      (dm (i + 1)).dmem.get? (A x) = (st i).data.dmem.get? (A x)) :
    ∃ rm : Nat → Mem, rm 0 = zeroMem tab ∧ ∀ i < n, ∃ rs,
      L.run p abiFuel "check" [] (bufMemG fz own plo phi mode B (rm i) (dm i).regs.rdx) = .ok (rs, rm (i + 1)) ∧
      rs.getD 0 0 = ACCEPT ∧ MemRel (bufLayout tab buf B base fz own) (rm (i + 1)) (st i).data.dmem ∧
      RegsRestored (dm i).regs (st i).data.regs := by
  -- the chain up to call `m`, and the region's memory at call `m`
  suffices H : ∀ m ≤ n, ∃ rm : Nat → Mem, rm 0 = zeroMem tab ∧
      (∀ i < m, ∃ rs, L.run p abiFuel "check" [] (bufMemG fz own plo phi mode B (rm i) (dm i).regs.rdx) =
        .ok (rs, rm (i + 1)) ∧ rs.getD 0 0 = ACCEPT ∧
        MemRel (bufLayout tab buf B base fz own) (rm (i + 1)) (st i).data.dmem ∧
        RegsRestored (dm i).regs (st i).data.regs) ∧
      (m < n → RegionRel tab base own (rm m) (dm m).dmem) by
    obtain ⟨rm, h0, h, -⟩ := H n (Nat.le_refl _)
    exact ⟨rm, h0, h⟩
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨fun _ => zeroMem tab, rfl, fun i h => absurd h (by omega),
      fun h => regionRel_zero hok hn hf _ (hzero h)⟩
  | succ m ih =>
    intro hm
    obtain ⟨rm, h0, hrun, hreg⟩ := ih (by omega)
    obtain ⟨-, hRR, -, hout⟩ := hpost m (by omega) (rm m) (hreg (by omega))
    obtain ⟨hrdx, hrax⟩ := hacc m (by omega)
    have hout' := hout.resolve_left (by rw [hrdx]; decide)
    rcases hres : L.run p abiFuel "check" [] (bufMemG fz own plo phi mode B (rm m) (dm m).regs.rdx)
      with e | ⟨rs, m'⟩
    · rw [hres] at hout'
      cases e <;> simp only [OutcomeRel] at hout' <;> (rw [hrdx] at hout'; exact absurd hout'.1 (by decide))
    rw [hres] at hout'
    obtain ⟨-, hRes, hMem⟩ := hout'
    have hrax' : (st m).data.regs.rax = rs.getD 0 0 := hRes.1 0 (by simp only [bufLayout_tab]; omega) (by decide)
    refine ⟨fun i => if i ≤ m then rm i else m', by simp [h0], fun i hi => ?_, fun hlt => ?_⟩
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
      exact (RegionRel.of_memRel hdisj hMem).transfer hok hn (hnext m hlt)

end ConAgua.Final
