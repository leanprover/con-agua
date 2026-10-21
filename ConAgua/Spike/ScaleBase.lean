import ConAgua.Arena.ArenaRel
import ConAgua.Arena.WalkRefine

/-! Spike (lane `scale`): base relation with 0 dummy memo clauses. Not imported by `ConAgua`. -/

open ConRon.Arena
open Std.WP
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace L.Arena.Spike

macro "apart3" : tactic => `(tactic| simp [Apart, POOL, CTL, BMEMO, bmSch, LMEMO, lfSch, IMEMO, imSch, litSch, REC, SLOT, appSch, AREC, ASLOT, sortSch, SOREC, SOSLOT, constSch, CREC, CSLOT, letSch, LEREC, LESLOT, bvarSch, BREC, BSLOT, fvarSch, FVREC, FVSLOT, lamSch, LAREC, LASLOT, forallSch, FAREC, FASLOT, projSch, PJREC, PJSLOT, zeroSch, ZREC, ZSLOT, succSch, SREC, SSLOT, maxSch, MREC, MSLOT, imaxSch, IREC, ISLOT, paramSch, PREC, PSLOT, lsSch, LSREC, LSSLOT, nanonSch, NAREC, NASLOT, nstrSch, NSREC, NSSLOT, nnumSch, NNREC, NNSLOT])


theorem lift_app (m m' : Mem) (a a' : AState) (hR : ArenaR m a) (hX : AppR m' a')
    (hf : MemFrame [appSch.ra, appSch.sa] [appSch.ca, appSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = appLens.setP a t) ∨ (∃ t, a' = appLens.setS a t)) : ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

theorem lift_sort (m m' : Mem) (a a' : AState) (hR : ArenaR m a) (hX : SortR m' a')
    (hf : MemFrame [sortSch.ra, sortSch.sa] [sortSch.ca, sortSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = sortLens.setP a t) ∨ (∃ t, a' = sortLens.setS a t)) : ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

theorem lift_const (m m' : Mem) (a a' : AState) (hR : ArenaR m a) (hX : ConstR m' a')
    (hf : MemFrame [constSch.ra, constSch.sa] [constSch.ca, constSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = constLens.setP a t) ∨ (∃ t, a' = constLens.setS a t)) : ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

theorem lift_letE (m m' : Mem) (a a' : AState) (hR : ArenaR m a) (hX : LetR m' a')
    (hf : MemFrame [letSch.ra, letSch.sa] [letSch.ca, letSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = letLens.setP a t) ∨ (∃ t, a' = letLens.setS a t)) : ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

theorem lift_bvar (m m' : Mem) (a a' : AState) (hR : ArenaR m a) (hX : BVarR m' a')
    (hf : MemFrame [bvarSch.ra, bvarSch.sa] [bvarSch.ca, bvarSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = bvarLens.setP a t) ∨ (∃ t, a' = bvarLens.setS a t)) : ArenaR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> arena_build hR, hf with exact hX

theorem memo_set (m m' : Mem) (a : AState) (hR : ArenaR m a) (k v : Word)
    (hk : k.toNat < 2 ^ 32) (hs : msetG bmSch m k 0 v = some m') :
    ArenaR m' (withBC a (a.memos.bvarBC.insert (decE k) v.toNat)) := by
  have hf := msetG_frame bmSch bmSch_wf m m' k 0 v hs
  arena_build hR, hf with exact memoRG_set bmSch bmSch_wf bmKey _ m _ hR.memo k 0 v ⟨hk, rfl⟩ m' hs

theorem memo_clear (m : Mem) (a : AState) (hR : ArenaR m a)
    (h0 : rdW (m.arr64 CTL) 24 + 2 ≠ 0) : ArenaR (mclearG bmSch m) (withBC a ∅) := by
  have hf := mclearG_frame bmSch m
  arena_build hR, hf with exact memoRG_clear bmSch bmSch_wf bmKey _ m _ hR.memo h0

theorem grow (m m' : Mem) (hg : Grows m m') (a : AState) (hR : ArenaR m a) : ArenaR m' a := by
  have hf := grows_frame m m' hg
  arena_build hR, hf with
    first | exact LitR.grow m m' hg a hR.lit | exact LsR.grow m m' hg a hR.ls |
      exact NStrR.grow m m' hg a hR.nstr

end L.Arena.Spike
