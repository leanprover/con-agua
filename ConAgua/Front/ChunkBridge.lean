import ConRon.Arena.Frontend.ExportC
import ConLeche.Frontend.Scan.Equiv
import ConLeche.Verify.Frontend.Chunks
import ConAgua.Census.Attr

/-!
# One chunk is the wholesale parse (lane `front3`)

The checker's statement runs the twin's streaming parse on one chunk, `parseChunks [b]`; the L
frontend `front_run` is the twin's wholesale `parseBytes b` (`L.Front.frontRun_refines`). The two
are the same function of the arena state whenever `b` fits in a machine word
(`parseChunks_single`): the one chunk's step feeds every complete line exactly as `parseBytes`
does, and the carried tail `b.extract tail b.size` is read by `applyFinalLine` at offset `0` as
`parseBytes` reads `b` at `tail`, because a line's scan depends only on the bytes from its start
(`scanLineFwd = scanLineSpec`, con-leche's `naiveLine` on `tailAt b i`), error offsets included
(they are reported relative to the line's start). So `front_run` refines the streaming driver too
(`frontRun_refines_chunks`): the chunked-driver targets are covered through it, and L has no
streaming driver of its own (docs/deviations.md, Deliberate).
-/

namespace ConAgua.Front.ChunkBridge

open ConRon.Arena ConRon.Arena.Frontend
open ConLeche.Frontend (scanLineFwd_eq scanLineSpec tailAt posAt toNat_usize tailAt_zero
  bytes_extract_tail)

/-- `applyFinalLine` reads only the bytes from its start. -/
theorem applyFinalLine_tail (st : StateD) (b c : ByteArray) (i j : USize) (n : Nat)
    (h : tailAt b i = tailAt c j) :
    applyFinalLine st b i n = applyFinalLine st c j n := by
  unfold applyFinalLine
  rw [scanLineFwd_eq, scanLineFwd_eq]
  unfold scanLineSpec
  rw [h]
  split
  · rfl
  · rfl
  · simp only [posAt]
    congr 6
    omega

/-- **One chunk is the wholesale parse**, for a buffer that fits in a machine word. -/
theorem parseChunks_single (b : ByteArray) (hb : b.size < USize.size) :
    parseChunks [b] = parseBytes b := by
  funext s
  have hge : ¬ b.size ≥ USize.size := by omega
  have hge0 : ¬ 0 + b.size ≥ USize.size := by omega
  simp only [parseChunks, parseBytes, parseChunksGo, chunkStep, hge, hge0, if_false,
    ByteArray.isEmpty, ByteArray.size_empty, beq_self_eq_true, if_true]
  simp only [bind, StateT.bind, pure, StateT.pure, Except.bind]
  cases hI : StateD.init s with
  | error e => rfl
  | ok p =>
    obtain ⟨st, s1⟩ := p
    simp only
    cases hF : feedChunk st b 0 0 s1 with
    | error e => rfl
    | ok q =>
      obtain ⟨r, s2⟩ := q
      cases r with
      | error e => rfl
      | ok t =>
        obtain ⟨st2, lineNo, tail⟩ := t
        simp only [chunkFinish, ByteArray.isEmpty, ByteArray.size_extract]
        have hu : b.usize.toNat = b.size := by
          rw [toNat_usize]; exact Nat.mod_eq_of_lt hb
        by_cases ht : tail < b.usize
        · have ht' : tail.toNat < b.size := by
            rw [← hu]; exact USize.lt_iff_toNat_lt.mp ht
          have hne : ¬ (min b.size b.size - tail.toNat == 0) = true := by
            simp only [Nat.min_self, beq_iff_eq]; omega
          simp only [hne, if_false, ht, if_true]
          rw [applyFinalLine_tail st2 (b.extract tail.toNat b.size) b 0 tail (lineNo + 1)
            (by rw [tailAt_zero, bytes_extract_tail tail hb])]
          rfl
        · have ht' : b.size ≤ tail.toNat := by
            rw [← hu]; exact Nat.le_of_not_lt (fun h => ht (USize.lt_iff_toNat_lt.mpr h))
          have he : (min b.size b.size - tail.toNat == 0) = true := by
            simp only [Nat.min_self, beq_iff_eq]; omega
          simp only [he, if_true, ht, if_false]
          rfl

end ConAgua.Front.ChunkBridge
