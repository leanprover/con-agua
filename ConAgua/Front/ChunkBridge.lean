module

import ConLeche.Verify.Frontend.Chunks
public import ConRon.Arena.Frontend.ExportC
public import ConLeche.Frontend.Scan.Equiv.Kit

@[expose] public section

/-!
# One chunk is the wholesale parse (lane `front3`)

The checker's statement runs the twin's streaming parse on one chunk, `parseChunks [b]`; the L
frontend `front_run` is the twin's wholesale `parseBytes b` (`L.Front.frontRun_ref`). The two
are the same function of the arena state whenever `b` fits in a machine word
(`parseChunks_single`): the one chunk's step feeds every complete line exactly as `parseBytes`
does, and the carried tail `b.extract tail b.size` is read by `applyFinalLine` at offset `0` as
`parseBytes` reads `b` at `tail`, because a line's scan depends only on the bytes from its start
(`scanLineFwd = scanLineSpec`, con-leche's `naiveLine` on `tailAt b i`), error offsets included
(they are reported relative to the line's start). So `front_run` refines the streaming driver too
(`frontRun_checker_chunks`): the chunked-driver targets are covered through it, and L has no
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
  cases ConLeche.Frontend.naiveLine (tailAt c j) with
  | ok v rest => obtain ⟨r, o⟩ := v; cases o <;> rfl
  | err t rest => simp only [posAt, Nat.add_sub_cancel_left]

/-- **One chunk is the wholesale parse**, for a buffer that fits in a machine word. -/
theorem parseChunks_single (b : ByteArray) (hb : b.size < USize.size) :
    parseChunks [b] = parseBytes b := by
  sorry

end ConAgua.Front.ChunkBridge
