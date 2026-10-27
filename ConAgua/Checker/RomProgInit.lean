import ConAgua.Final.Statement
import ConAgua.Rom.Stage
import ConAgua.Checker.CapCheck

/-!
# The loaded memory at the start of `check` (lane `pipeline`)

`ConAgua.Final.loadMem b pb s8 s64` has the word arrays of `initMem s64` (all zero) and the byte
arrays `b`, `pb`, then zeroed ones. Under `CapsOK` (`cap_check`, `CapCheck.lean`) the arena
relation holds at the twin's initial state (`arenaD_loadMem`), `RSET` is empty (`rsetR_loadMem`)
and the ROM stack is at `0` (`stkTop_loadMem`). The parse state relation holds at
`StateD.blank` (`stateDR_loadMem`: `DECL`, `DLP` have a word, `IFR`, `IFL` are below `2^62`
words). `CapsOK` survives runs that keep the sizes (`CapsOK.keep`).
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend

section
variable (b pb : ByteArray) (s8 s64 : List Nat)

theorem loadMem_arr (a : ArrId) :
    (loadMem b pb s8 s64).arr64 a = Array.replicate (s64[a]?.getD 0) 0 := by
  simp only [Mem.arr64, loadMem, Array.getD_eq_getD_getElem?]
  cases h : s64[a]? <;> simp [h]

theorem loadMem_rd (a : ArrId) (x : Word) : rdW ((loadMem b pb s8 s64).arr64 a) x = 0 := by
  rw [loadMem_arr]; simp only [rdW, Array.getElem?_replicate]; split <;> rfl

theorem loadMem_words_size : (loadMem b pb s8 s64).words.size = s64.length := by
  simp [loadMem]

/-- The pin-data buffer is byte array `PB`. -/
theorem loadMem_pb : (loadMem b pb s8 s64).arr8 PB = pb.data.toList.toArray := by
  simp [Mem.arr8, loadMem, PB]

/-- `CTL` exists: it has at least `ctlMin` words. -/
theorem loadMem_ctl_lt (hc : CapsOK (loadMem b pb s8 s64)) : CTL < (loadMem b pb s8 s64).words.size := by
  have h := hc.2.1
  rw [loadMem_arr] at h
  rw [loadMem_words_size]
  simp only [Array.size_replicate] at h
  cases hs : s64[CTL]? with
  | none => rw [hs] at h; simp [ctlMin] at h
  | some _ => exact (List.getElem?_eq_some_iff.1 hs).1

/-- **`ArenaR` at the start**, on the loaded memory (`arenaR_init`'s proof over `loadMem`). -/
theorem arenaR_loadMem (hc : CapsOK (loadMem b pb s8 s64)) :
    ArenaR (loadMem b pb s8 s64) (AState.init EStore.empty) := by
  have hz := loadMem_rd b pb s8 s64
  have hc' : 64 ≤ ((loadMem b pb s8 s64).arr64 CTL).size := by have := hc.2.1; simp [ctlMin] at this; omega
  have hp : ((loadMem b pb s8 s64).arr64 POOL).size < 2 ^ 40 := hc.2.2.2.2.1
  have hp1 : ((loadMem b pb s8 s64).arr64 POOL1).size < 2 ^ 40 := hc.2.2.2.2.2
  have hpc : pcap (loadMem b pb s8 s64) = 2 ^ 41 - 1 := pcap_of_small _ ⟨hp, hp1⟩
  have ht0 : (loadMem b pb s8 s64).top = 0 := by simp only [top_rdW, hz]
  have hpt0 : (loadMem b pb s8 s64).ptop0 = 0 := by
    simp only [Mem.ptop0]; rw [loadMem_arr]; simp only [Array.getElem?_replicate]; split <;> rfl
  have hw := loadMem_ctl_lt b pb s8 s64 hc
  have hsl : ∀ a ∈ slotArrs, a < wordArrays := by decide
  have hs : ∀ a, a ∈ slotArrs → a + 256 ∈ slotArrs → ∀ t,
      consMinWords ≤ ((loadMem b pb s8 s64).arr64 (tierA a t)).size ∧
      ((loadMem b pb s8 s64).arr64 (tierA a t)).size < 2 ^ 61 := fun a h0 h1 t => by
    rcases tierA_cases' a t with e | e <;> rw [e]
    · exact (hc.1 a (hsl a h0)).2 h0
    · exact (hc.1 _ (hsl _ h1)).2 h1
  refine ⟨⟨?_, consR_init hz (by simp [litCS, litCSk]; omega) (hs _ (by decide) (by decide))⟩,
    consR_init hz (by simp [appCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [sortCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [constCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [letCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [bvarCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [fvarCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [lamCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [forallCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [projCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [zeroCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [succCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [maxCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [imaxCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [paramCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [lsCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [nanonCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [nstrCS]; omega) (hs _ (by decide) (by decide)),
    consR_init hz (by simp [nnumCS]; omega) (hs _ (by decide) (by decide)), ?_,
    ⟨constT_empty _, constT_empty _⟩, ⟨constT_empty _, constT_empty _⟩,
    ⟨colT_empty _ _ _ _, colT_empty _ _ _ _⟩, ⟨colT_empty _ _ _ _, colT_empty _ _ _ _⟩,
    ⟨colT_empty _ _ _ _, colT_empty _ _ _ _⟩, ⟨colT_empty _ _ _ _, colT_empty _ _ _ _⟩,
    ⟨colT_empty _ _ _ _, colT_empty _ _ _ _⟩, ⟨colT_empty _ _ _ _, colT_empty _ _ _ _⟩,
    ⟨colT_empty _ _ _ _, colT_empty _ _ _ _⟩⟩
  · refine ⟨hw, by omega, by rw [hpc]; decide, by rw [ht0, hpc]; decide, by rw [hpt0]; simp,
      by rw [ht0]; simp⟩
  · exact ⟨memoRG_zero bmSch bmKey _ _ hz (by simp; omega),
      memoRG_zero lfSch lfKey _ _ hz (by simp; omega),
      memoRG_zero imSch lfKey _ _ hz (by simp; omega),
      memoRG_zero frSch bmKey _ _ hz (by simp; omega)⟩

/-- **`ArenaD` at the start**, on the loaded memory. -/
theorem arenaD_loadMem (hc : CapsOK (loadMem b pb s8 s64)) :
    ArenaD (loadMem b pb s8 s64) (AState.init EStore.empty) :=
  ⟨arenaR_loadMem b pb s8 s64 hc, derR_init _⟩

/-- **`RSET` is empty at the start.** -/
theorem rsetR_loadMem (hc : CapsOK (loadMem b pb s8 s64)) : RsetR (loadMem b pb s8 s64) :=
  RsetR_zero _ (loadMem_rd b pb s8 s64) (by have := hc.2.1; simp [ctlMin] at this; omega)

/-- **The ROM stack is at `0` at the start.** -/
theorem stkTop_loadMem : stkTop (loadMem b pb s8 s64) = 0 := loadMem_rd b pb s8 s64 CTL 131

/-- **The parse state relation at the start**, at the blank parse state (`stateDR_initMem`'s
proof over `loadMem`). -/
theorem stateDR_loadMem (hc : CapsOK (loadMem b pb s8 s64)) :
    StateDR (loadMem b pb s8 s64) StateD.blank := by
  have hctl : 73 ≤ ((loadMem b pb s8 s64).arr64 CTL).size := by
    have := hc.2.1; simp [ctlMin] at this; omega
  have h63 : ∀ a < wordArrays, ((loadMem b pb s8 s64).arr64 a).size < 2 ^ 63 := fun a ha => by
    have := hc.1 a ha; omega
  have hT : ∀ (a : ArrId) {k : IdxKind}, TblIx a → a < wordArrays →
      TblR (loadMem b pb s8 s64) a ({} : ConLeche.Frontend.IdTable (Idx k)) := fun a _ ha hs =>
    TblR.zero _ a ha (loadMem_rd b pb s8 s64) (h63 a hs) hctl
  have hf : ((loadMem b pb s8 s64).arr64 L.Front.Ind.IFR).size < 2 ^ 62 ∧
      ((loadMem b pb s8 s64).arr64 L.Front.Ind.IFL).size < 2 ^ 62 :=
    ⟨(hc.1 70 (by decide)).1, (hc.1 71 (by decide)).1⟩
  refine ⟨hT NID (.inl rfl) (by decide), hT LID (.inr (.inl rfl)) (by decide),
    hT EID (.inr (.inr rfl)) (by decide), ?_, hf⟩
  have hd : 1 ≤ ((loadMem b pb s8 s64).arr64 DECL).size := hc.2.2.1
  have hq : 1 ≤ ((loadMem b pb s8 s64).arr64 DLP).size := hc.2.2.2.1
  have hd2 := h63 DECL (by decide)
  have hq2 := h63 DLP (by decide)
  rw [loadMem_arr] at hd hq hd2 hq2 ⊢
  rw [loadMem_arr]
  simp only [Array.size_replicate] at hd hq hd2 hq2
  refine ⟨by simpa using hd2, by simpa using hq2, ?_, ?_, ?_, fun i h => by
    simp [StateD.blank] at h⟩
  · rw [Array.getElem?_replicate]; split <;> simp [StateD.blank]
  · simpa [StateD.blank] using hd
  · rw [Array.getElem?_replicate]; split <;> simp <;> omega

/-- The loaded word arrays' sizes are words when the harness's sizes are (`InputsOK`). -/
theorem loadMem_wordsFit (hs : ∀ n ∈ s64, n < 2 ^ 64) : WordsFit (loadMem b pb s8 s64) := by
  intro a _
  rw [loadMem_arr, Array.size_replicate]
  cases h : s64[a]? with
  | none => simp
  | some n => exact hs n (List.mem_of_getElem? h)

end

/-! ## Carried through runs (`Keep`: same byte arrays, same word-array sizes) -/

theorem CapsOK.keep {m m' : Mem} (hk : Keep m m') (h : CapsOK m) : CapsOK m' := by
  simp only [CapsOK, hk.size]; exact h

theorem WordsFit.keep {m m' : Mem} (hk : Keep m m') (h : WordsFit m) : WordsFit m' := by
  intro a ha; rw [hk.size]; exact h a ha

theorem CapsOK.ctl {m : Mem} (h : CapsOK m) : 151 < (m.arr64 CTL).size := by
  have := h.2.1; simp [ctlMin] at this; omega

theorem CapsOK.pool {m : Mem} (h : CapsOK m) : (m.arr64 POOL).size < 2 ^ 40 := h.2.2.2.2.1

theorem CapsOK.pool1 {m : Mem} (h : CapsOK m) : (m.arr64 POOL1).size < 2 ^ 40 := h.2.2.2.2.2

end L.Checker
