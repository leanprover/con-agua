import ConLeche.Verify.Frontend.Chunks
import ConAgua.Front.FrontRun

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
(`frontAll_refines_chunks`)(`frontRun_refines_chunks`): the chunked-driver targets are covered through it, and L has no
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
  funext s
  have hge : ¬ b.size ≥ USize.size := by omega
  have hge0 : ¬ 0 + b.size ≥ USize.size := by omega
  simp only [parseChunks, parseBytes, parseChunksGo, chunkStep, hge, hge0, ite_false,
    ByteArray.isEmpty, ByteArray.size_empty, beq_self_eq_true, ite_true]
  simp only [bind, StateT.bind, pure, Except.bind]
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
        simp only [StateT.pure, pure, Except.pure, chunkFinish, ByteArray.isEmpty, ByteArray.size_extract,
          Nat.min_self]
        have hu : b.usize.toNat = b.size := by
          rw [toNat_usize]; exact Nat.mod_eq_of_lt hb
        by_cases ht : tail < b.usize
        · have ht' : tail.toNat < b.size := by
            rw [← hu]; exact USize.lt_iff_toNat_lt.mp ht
          have hne : (b.size - tail.toNat == 0) = false := by
            simp only [beq_eq_false_iff_ne]; omega
          simp only [hne, ht, Bool.false_eq_true, ite_false, ite_true]
          rw [applyFinalLine_tail st2 (b.extract tail.toNat b.size) b 0 tail (lineNo + 1)
            (by rw [tailAt_zero, bytes_extract_tail tail hb])]
          rfl
        · have ht' : b.size ≤ tail.toNat := by
            rw [← hu]; exact Nat.le_of_not_lt (fun h => ht (USize.lt_iff_toNat_lt.mpr h))
          have he : (b.size - tail.toNat == 0) = true := by
            simp only [beq_iff_eq]; omega
          simp only [he, ht, ite_true, ite_false]

open scoped Lean.Order in
open Std.WP L L.Front L.Arena in
/-- **`front_run` refines the twin's streaming parse of one chunk**, the form the checker's
statement takes (`parseChunks [b]`): `frontAll_refines` and `parseChunks_single`. -/
@[refines ConRon.Arena.Frontend.parseChunks]
theorem frontAll_refines_chunks (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data)
    (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63) (a₀ : AState) (hA : ArenaD s₀.mem a₀)
    (hD : StateDR s₀.mem StateD.blank) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke frontAllProg (exec frontAllProg n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseChunks [b]).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem st'; ⊤⦄ := by
  have hu : b.size < USize.size := by
    rw [show USize.size = 2 ^ 64 by simp [USize.size, h64]]; omega
  rw [parseChunks_single b hu]
  exact frontAll_refines b h64 hsize n s₀ hm hpool a₀ hA hD hok hoff hpins hmode

end ConAgua.Front.ChunkBridge
