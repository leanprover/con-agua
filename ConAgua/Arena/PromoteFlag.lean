import ConAgua.Arena.ArenaRel
import ConAgua.Arena.DerRel
import ConAgua.Arena.PromoteTwin

/-!
# The scratch flag `CTL[1]` written: the arena relation at the flags `onA b`

The promotion's bracket `pi_*` writes `CTL[1] := 0` around an interner and puts the old word
back. Under `ArenaR`, writing `CTL[1] := w` relates the same tables at the four stores' flags
`w != 0` (`onA`, `PromoteTwin.lean`): a table's relation reads the flag only in `ConsR`'s flag
clause (`ConsR.setFlag`), the tiers read their counts, the slot base and their own arrays. The
memos and the derived ranges do not read `CTL[1]`.
-/

open ConRon.Arena


namespace L.Arena

/-- The four flags of a related state agree (each table's relation has its store's flag equal to
`CTL[1] != 0`). -/
theorem ArenaR.flagsEq {m : Mem} {a : AState} (hR : ArenaR m a) : FlagsEq a.store :=
  ⟨(ConsR.flag hR.ls).symm.trans (ConsR.flag hR.app), (ConsR.flag hR.zero).symm.trans (ConsR.flag hR.app),
    (ConsR.flag hR.nanon).symm.trans (ConsR.flag hR.app)⟩

/-- The flag `CTL[1]` is the flag of the expression store. -/
theorem ArenaR.flag_eq {m : Mem} {a : AState} (hR : ArenaR m a) :
    (rdW (m.arr64 CTL) 1 != 0) = a.store.scratchOn := ConsR.flag hR.app

/-- **Writing `CTL[1]`** relates the same tables at the flags `w != 0`. -/
theorem ArenaR.flag {m : Mem} {a : AState} (hR : ArenaR m a) (w : Word) :
    ArenaR (m.set64 CTL 1 w) (onA (w != 0) a) := by
  have hf : MemFrame [] [1] m (m.set64 CTL 1 w) := MemFrame.setCtl m 1 w
  exact ⟨⟨hR.lit.1.frame (Mem.arr64_set64_ne _ _ _ _ _ (by decide))
        (Mem.arr64_set64_ne _ _ _ _ _ (by decide)) (Mem.arr64_set64_ne _ _ _ _ _ (by decide))
        (size_set64 ..) (by simp only [top_rdW, rdW_set64]; simp) (Mem.words_size_set64 ..),
      ConsR.setFlag litCS_wf litFrame hR.lit.2 w⟩,
    ConsR.setFlag appCS_wf appFrame hR.app w,
    ConsR.setFlag sortCS_wf sortFrame hR.sort w,
    ConsR.setFlag constCS_wf constFrame hR.const w,
    ConsR.setFlag letCS_wf letFrame hR.letE w,
    ConsR.setFlag bvarCS_wf bvarFrame hR.bvar w,
    ConsR.setFlag fvarCS_wf fvarFrame hR.fvar w,
    ConsR.setFlag lamCS_wf laFrame hR.lam w,
    ConsR.setFlag forallCS_wf faFrame hR.forallE w,
    ConsR.setFlag projCS_wf projFrame hR.proj w,
    ConsR.setFlag zeroCS_wf zeroFrame hR.zero w,
    ConsR.setFlag succCS_wf succFrame hR.succ w,
    ConsR.setFlag maxCS_wf maxFrame hR.max w,
    ConsR.setFlag imaxCS_wf imaxFrame hR.imax w,
    ConsR.setFlag paramCS_wf paramFrame hR.param w,
    ConsR.setFlag lsCS_wf lsFrame hR.ls w,
    ConsR.setFlag nanonCS_wf naFrame hR.nanon w,
    ConsR.setFlag nstrCS_wf nstrFrame hR.nstr w,
    ConsR.setFlag nnumCS_wf nnFrame hR.nnum w,
    hR.memos.frame (by simp) (by simp [memoCtl]) hf, hR.zeroHp, hR.paramHp,
    hR.succHp.frame (Mem.arr64_set64_ne _ CTL _ 1 w (by decide))
      (Mem.arr64_set64_ne _ CTL _ 1 w (by decide)), hR.maxHp.frame (Mem.arr64_set64_ne _ CTL _ 1 w (by decide))
      (Mem.arr64_set64_ne _ CTL _ 1 w (by decide)), hR.imaxHp.frame (Mem.arr64_set64_ne _ CTL _ 1 w (by decide))
      (Mem.arr64_set64_ne _ CTL _ 1 w (by decide)), hR.lsHp.frame (Mem.arr64_set64_ne _ CTL _ 1 w (by decide))
      (Mem.arr64_set64_ne _ CTL _ 1 w (by decide)), hR.sortLp.frame (Mem.arr64_set64_ne _ CTL _ 1 w (by decide))
      (Mem.arr64_set64_ne _ CTL _ 1 w (by decide)), hR.constLp.frame (Mem.arr64_set64_ne _ CTL _ 1 w (by decide))
      (Mem.arr64_set64_ne _ CTL _ 1 w (by decide)), hR.fvarLp.frame (Mem.arr64_set64_ne _ CTL _ 1 w (by decide))
      (Mem.arr64_set64_ne _ CTL _ 1 w (by decide))⟩

/-- The derived ranges read the expression tables only. -/
theorem DerR.onA {m : Mem} {a : AState} (hD : DerR m a) (b : Bool) : DerR m (onA b a) :=
  ⟨hD.bvar, hD.fvar, hD.sort, hD.const, hD.lit, hD.app, hD.lam, hD.forallE, hD.letE, hD.proj⟩

theorem DerR.setCtl {m : Mem} {a : AState} (hD : DerR m a) (c w : Word) :
    DerR (m.set64 CTL c w) a :=
  DerR.frameM [] [c] m _ (MemFrame.setCtl m c w) (by simp) a hD

/-- **Writing `CTL[1]`** under `ArenaD`. -/
theorem ArenaD.flag {m : Mem} {a : AState} (hD : ArenaD m a) (w : Word) :
    ArenaD (m.set64 CTL 1 w) (onA (w != 0) a) :=
  ⟨hD.1.flag w, (hD.2.setCtl 1 w).onA _⟩

/-! ## With the flag clear, an interning answers a persistent handle word

An `intern_*` model (`internM`) with `CTL[1] = 0` answers `hdW tag 0 i` for a node `i < 2^27` of
the persistent tier: a handle word below `2^32` with tier bit `0`. -/

/-- A persistent handle word: below `2^32`, tier bit `0`. -/
def PW (w : Word) : Prop := w.toNat < 2 ^ 32 ∧ tierW w = 0

/-- A persistent handle word decodes to a persistent handle. -/
theorem PW.pers {k : IdxKind} {w : Word} (h : PW w) : (decI w : Idx k).isPersistent = true := by
  rw [isPersistent_decI w h.1]; simp only [beq_iff_eq]; exact h.2

end L.Arena
