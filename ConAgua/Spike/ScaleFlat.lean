import ConAgua.Arena.ArenaRel
import ConAgua.Arena.WalkRefine

/-! Spike (lane `scale`): flat relation with 44 dummy memo clauses. Not imported by `ConAgua`. -/

open ConRon.Arena
open Std.WP
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace L.Arena.Spike

def dS0 : MemoSch := ⟨100, 100⟩
theorem dS0_wf : dS0.WF := ⟨by decide, by decide⟩
def dS1 : MemoSch := ⟨101, 102⟩
theorem dS1_wf : dS1.WF := ⟨by decide, by decide⟩
def dS2 : MemoSch := ⟨102, 104⟩
theorem dS2_wf : dS2.WF := ⟨by decide, by decide⟩
def dS3 : MemoSch := ⟨103, 106⟩
theorem dS3_wf : dS3.WF := ⟨by decide, by decide⟩
def dS4 : MemoSch := ⟨104, 108⟩
theorem dS4_wf : dS4.WF := ⟨by decide, by decide⟩
def dS5 : MemoSch := ⟨105, 110⟩
theorem dS5_wf : dS5.WF := ⟨by decide, by decide⟩
def dS6 : MemoSch := ⟨106, 112⟩
theorem dS6_wf : dS6.WF := ⟨by decide, by decide⟩
def dS7 : MemoSch := ⟨107, 114⟩
theorem dS7_wf : dS7.WF := ⟨by decide, by decide⟩
def dS8 : MemoSch := ⟨108, 116⟩
theorem dS8_wf : dS8.WF := ⟨by decide, by decide⟩
def dS9 : MemoSch := ⟨109, 118⟩
theorem dS9_wf : dS9.WF := ⟨by decide, by decide⟩
def dS10 : MemoSch := ⟨110, 120⟩
theorem dS10_wf : dS10.WF := ⟨by decide, by decide⟩
def dS11 : MemoSch := ⟨111, 122⟩
theorem dS11_wf : dS11.WF := ⟨by decide, by decide⟩
def dS12 : MemoSch := ⟨112, 124⟩
theorem dS12_wf : dS12.WF := ⟨by decide, by decide⟩
def dS13 : MemoSch := ⟨113, 126⟩
theorem dS13_wf : dS13.WF := ⟨by decide, by decide⟩
def dS14 : MemoSch := ⟨114, 128⟩
theorem dS14_wf : dS14.WF := ⟨by decide, by decide⟩
def dS15 : MemoSch := ⟨115, 130⟩
theorem dS15_wf : dS15.WF := ⟨by decide, by decide⟩
def dS16 : MemoSch := ⟨116, 132⟩
theorem dS16_wf : dS16.WF := ⟨by decide, by decide⟩
def dS17 : MemoSch := ⟨117, 134⟩
theorem dS17_wf : dS17.WF := ⟨by decide, by decide⟩
def dS18 : MemoSch := ⟨118, 136⟩
theorem dS18_wf : dS18.WF := ⟨by decide, by decide⟩
def dS19 : MemoSch := ⟨119, 138⟩
theorem dS19_wf : dS19.WF := ⟨by decide, by decide⟩
def dS20 : MemoSch := ⟨120, 140⟩
theorem dS20_wf : dS20.WF := ⟨by decide, by decide⟩
def dS21 : MemoSch := ⟨121, 142⟩
theorem dS21_wf : dS21.WF := ⟨by decide, by decide⟩
def dS22 : MemoSch := ⟨122, 144⟩
theorem dS22_wf : dS22.WF := ⟨by decide, by decide⟩
def dS23 : MemoSch := ⟨123, 146⟩
theorem dS23_wf : dS23.WF := ⟨by decide, by decide⟩
def dS24 : MemoSch := ⟨124, 148⟩
theorem dS24_wf : dS24.WF := ⟨by decide, by decide⟩
def dS25 : MemoSch := ⟨125, 150⟩
theorem dS25_wf : dS25.WF := ⟨by decide, by decide⟩
def dS26 : MemoSch := ⟨126, 152⟩
theorem dS26_wf : dS26.WF := ⟨by decide, by decide⟩
def dS27 : MemoSch := ⟨127, 154⟩
theorem dS27_wf : dS27.WF := ⟨by decide, by decide⟩
def dS28 : MemoSch := ⟨128, 156⟩
theorem dS28_wf : dS28.WF := ⟨by decide, by decide⟩
def dS29 : MemoSch := ⟨129, 158⟩
theorem dS29_wf : dS29.WF := ⟨by decide, by decide⟩
def dS30 : MemoSch := ⟨130, 160⟩
theorem dS30_wf : dS30.WF := ⟨by decide, by decide⟩
def dS31 : MemoSch := ⟨131, 162⟩
theorem dS31_wf : dS31.WF := ⟨by decide, by decide⟩
def dS32 : MemoSch := ⟨132, 164⟩
theorem dS32_wf : dS32.WF := ⟨by decide, by decide⟩
def dS33 : MemoSch := ⟨133, 166⟩
theorem dS33_wf : dS33.WF := ⟨by decide, by decide⟩
def dS34 : MemoSch := ⟨134, 168⟩
theorem dS34_wf : dS34.WF := ⟨by decide, by decide⟩
def dS35 : MemoSch := ⟨135, 170⟩
theorem dS35_wf : dS35.WF := ⟨by decide, by decide⟩
def dS36 : MemoSch := ⟨136, 172⟩
theorem dS36_wf : dS36.WF := ⟨by decide, by decide⟩
def dS37 : MemoSch := ⟨137, 174⟩
theorem dS37_wf : dS37.WF := ⟨by decide, by decide⟩
def dS38 : MemoSch := ⟨138, 176⟩
theorem dS38_wf : dS38.WF := ⟨by decide, by decide⟩
def dS39 : MemoSch := ⟨139, 178⟩
theorem dS39_wf : dS39.WF := ⟨by decide, by decide⟩
def dS40 : MemoSch := ⟨140, 180⟩
theorem dS40_wf : dS40.WF := ⟨by decide, by decide⟩
def dS41 : MemoSch := ⟨141, 182⟩
theorem dS41_wf : dS41.WF := ⟨by decide, by decide⟩
def dS42 : MemoSch := ⟨142, 184⟩
theorem dS42_wf : dS42.WF := ⟨by decide, by decide⟩
def dS43 : MemoSch := ⟨143, 186⟩
theorem dS43_wf : dS43.WF := ⟨by decide, by decide⟩
macro "apart3" : tactic => `(tactic| simp [Apart, POOL, CTL, BMEMO, bmSch, LMEMO, lfSch, IMEMO, imSch, litSch, REC, SLOT, appSch, AREC, ASLOT, sortSch, SOREC, SOSLOT, constSch, CREC, CSLOT, letSch, LEREC, LESLOT, bvarSch, BREC, BSLOT, fvarSch, FVREC, FVSLOT, lamSch, LAREC, LASLOT, forallSch, FAREC, FASLOT, projSch, PJREC, PJSLOT, zeroSch, ZREC, ZSLOT, succSch, SREC, SSLOT, maxSch, MREC, MSLOT, imaxSch, IREC, ISLOT, paramSch, PREC, PSLOT, lsSch, LSREC, LSSLOT, nanonSch, NAREC, NASLOT, nstrSch, NSREC, NSSLOT, nnumSch, NNREC, NNSLOT, dS0 , dS1 , dS2 , dS3 , dS4 , dS5 , dS6 , dS7 , dS8 , dS9 , dS10 , dS11 , dS12 , dS13 , dS14 , dS15 , dS16 , dS17 , dS18 , dS19 , dS20 , dS21 , dS22 , dS23 , dS24 , dS25 , dS26 , dS27 , dS28 , dS29 , dS30 , dS31 , dS32 , dS33 , dS34 , dS35 , dS36 , dS37 , dS38 , dS39 , dS40 , dS41 , dS42 , dS43])

structure AR (m : Mem) (a : AState) : Prop where
  lit : LitR m a
  app : AppR m a
  sort : SortR m a
  const : ConstR m a
  letE : LetR m a
  bvar : BVarR m a
  fvar : FVarR m a
  lam : LamR m a
  forallE : ForallR m a
  proj : ProjR m a
  zero : ZeroR m a
  succ : SuccR m a
  max : MaxR m a
  imax : ImaxR m a
  param : ParamR m a
  ls : LsR m a
  nanon : NAnonR m a
  nstr : NStrR m a
  nnum : NNumR m a
  memo : MemoRG bmSch bmKey (·.toNat) m a.memos.bvarBC
  lmemo : MemoRG lfSch lfKey decE m a.memos.liftC
  imemo : MemoRG imSch lfKey decE m a.memos.inst1C
  d0 : MemoRG dS0 bmKey (·.toNat) m a.memos.fvarBC
  d1 : MemoRG dS1 bmKey (·.toNat) m a.memos.fvarBC
  d2 : MemoRG dS2 bmKey (·.toNat) m a.memos.fvarBC
  d3 : MemoRG dS3 bmKey (·.toNat) m a.memos.fvarBC
  d4 : MemoRG dS4 bmKey (·.toNat) m a.memos.fvarBC
  d5 : MemoRG dS5 bmKey (·.toNat) m a.memos.fvarBC
  d6 : MemoRG dS6 bmKey (·.toNat) m a.memos.fvarBC
  d7 : MemoRG dS7 bmKey (·.toNat) m a.memos.fvarBC
  d8 : MemoRG dS8 bmKey (·.toNat) m a.memos.fvarBC
  d9 : MemoRG dS9 bmKey (·.toNat) m a.memos.fvarBC
  d10 : MemoRG dS10 bmKey (·.toNat) m a.memos.fvarBC
  d11 : MemoRG dS11 bmKey (·.toNat) m a.memos.fvarBC
  d12 : MemoRG dS12 bmKey (·.toNat) m a.memos.fvarBC
  d13 : MemoRG dS13 bmKey (·.toNat) m a.memos.fvarBC
  d14 : MemoRG dS14 bmKey (·.toNat) m a.memos.fvarBC
  d15 : MemoRG dS15 bmKey (·.toNat) m a.memos.fvarBC
  d16 : MemoRG dS16 bmKey (·.toNat) m a.memos.fvarBC
  d17 : MemoRG dS17 bmKey (·.toNat) m a.memos.fvarBC
  d18 : MemoRG dS18 bmKey (·.toNat) m a.memos.fvarBC
  d19 : MemoRG dS19 bmKey (·.toNat) m a.memos.fvarBC
  d20 : MemoRG dS20 bmKey (·.toNat) m a.memos.fvarBC
  d21 : MemoRG dS21 bmKey (·.toNat) m a.memos.fvarBC
  d22 : MemoRG dS22 bmKey (·.toNat) m a.memos.fvarBC
  d23 : MemoRG dS23 bmKey (·.toNat) m a.memos.fvarBC
  d24 : MemoRG dS24 bmKey (·.toNat) m a.memos.fvarBC
  d25 : MemoRG dS25 bmKey (·.toNat) m a.memos.fvarBC
  d26 : MemoRG dS26 bmKey (·.toNat) m a.memos.fvarBC
  d27 : MemoRG dS27 bmKey (·.toNat) m a.memos.fvarBC
  d28 : MemoRG dS28 bmKey (·.toNat) m a.memos.fvarBC
  d29 : MemoRG dS29 bmKey (·.toNat) m a.memos.fvarBC
  d30 : MemoRG dS30 bmKey (·.toNat) m a.memos.fvarBC
  d31 : MemoRG dS31 bmKey (·.toNat) m a.memos.fvarBC
  d32 : MemoRG dS32 bmKey (·.toNat) m a.memos.fvarBC
  d33 : MemoRG dS33 bmKey (·.toNat) m a.memos.fvarBC
  d34 : MemoRG dS34 bmKey (·.toNat) m a.memos.fvarBC
  d35 : MemoRG dS35 bmKey (·.toNat) m a.memos.fvarBC
  d36 : MemoRG dS36 bmKey (·.toNat) m a.memos.fvarBC
  d37 : MemoRG dS37 bmKey (·.toNat) m a.memos.fvarBC
  d38 : MemoRG dS38 bmKey (·.toNat) m a.memos.fvarBC
  d39 : MemoRG dS39 bmKey (·.toNat) m a.memos.fvarBC
  d40 : MemoRG dS40 bmKey (·.toNat) m a.memos.fvarBC
  d41 : MemoRG dS41 bmKey (·.toNat) m a.memos.fvarBC
  d42 : MemoRG dS42 bmKey (·.toNat) m a.memos.fvarBC
  d43 : MemoRG dS43 bmKey (·.toNat) m a.memos.fvarBC

macro "ab3 " hR:term ", " hf:term " with " t:tacticSeq : tactic => `(tactic| exact ⟨
    by first | $t | exact ($hR).lit.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).app.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).sort.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).const.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).letE.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).bvar.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).fvar.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).lam.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).forallE.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).proj.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).zero.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).succ.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).max.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).imax.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).param.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).ls.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).nanon.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).nstr.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact ($hR).nnum.frame _ _ _ _ $hf _ (by apart3),
    by first | $t | exact memoRG_frame bmSch bmSch_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).memo,
    by first | $t | exact memoRG_frame lfSch lfSch_wf lfKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).lmemo,
    by first | $t | exact memoRG_frame imSch imSch_wf lfKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).imemo,
    by first | $t | exact memoRG_frame dS0 dS0_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d0,
    by first | $t | exact memoRG_frame dS1 dS1_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d1,
    by first | $t | exact memoRG_frame dS2 dS2_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d2,
    by first | $t | exact memoRG_frame dS3 dS3_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d3,
    by first | $t | exact memoRG_frame dS4 dS4_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d4,
    by first | $t | exact memoRG_frame dS5 dS5_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d5,
    by first | $t | exact memoRG_frame dS6 dS6_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d6,
    by first | $t | exact memoRG_frame dS7 dS7_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d7,
    by first | $t | exact memoRG_frame dS8 dS8_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d8,
    by first | $t | exact memoRG_frame dS9 dS9_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d9,
    by first | $t | exact memoRG_frame dS10 dS10_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d10,
    by first | $t | exact memoRG_frame dS11 dS11_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d11,
    by first | $t | exact memoRG_frame dS12 dS12_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d12,
    by first | $t | exact memoRG_frame dS13 dS13_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d13,
    by first | $t | exact memoRG_frame dS14 dS14_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d14,
    by first | $t | exact memoRG_frame dS15 dS15_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d15,
    by first | $t | exact memoRG_frame dS16 dS16_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d16,
    by first | $t | exact memoRG_frame dS17 dS17_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d17,
    by first | $t | exact memoRG_frame dS18 dS18_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d18,
    by first | $t | exact memoRG_frame dS19 dS19_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d19,
    by first | $t | exact memoRG_frame dS20 dS20_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d20,
    by first | $t | exact memoRG_frame dS21 dS21_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d21,
    by first | $t | exact memoRG_frame dS22 dS22_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d22,
    by first | $t | exact memoRG_frame dS23 dS23_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d23,
    by first | $t | exact memoRG_frame dS24 dS24_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d24,
    by first | $t | exact memoRG_frame dS25 dS25_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d25,
    by first | $t | exact memoRG_frame dS26 dS26_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d26,
    by first | $t | exact memoRG_frame dS27 dS27_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d27,
    by first | $t | exact memoRG_frame dS28 dS28_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d28,
    by first | $t | exact memoRG_frame dS29 dS29_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d29,
    by first | $t | exact memoRG_frame dS30 dS30_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d30,
    by first | $t | exact memoRG_frame dS31 dS31_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d31,
    by first | $t | exact memoRG_frame dS32 dS32_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d32,
    by first | $t | exact memoRG_frame dS33 dS33_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d33,
    by first | $t | exact memoRG_frame dS34 dS34_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d34,
    by first | $t | exact memoRG_frame dS35 dS35_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d35,
    by first | $t | exact memoRG_frame dS36 dS36_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d36,
    by first | $t | exact memoRG_frame dS37 dS37_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d37,
    by first | $t | exact memoRG_frame dS38 dS38_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d38,
    by first | $t | exact memoRG_frame dS39 dS39_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d39,
    by first | $t | exact memoRG_frame dS40 dS40_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d40,
    by first | $t | exact memoRG_frame dS41 dS41_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d41,
    by first | $t | exact memoRG_frame dS42 dS42_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d42,
    by first | $t | exact memoRG_frame dS43 dS43_wf bmKey _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).d43⟩)


theorem lift_app (m m' : Mem) (a a' : AState) (hR : AR m a) (hX : AppR m' a')
    (hf : MemFrame [appSch.ra, appSch.sa] [appSch.ca, appSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = appLens.setP a t) ∨ (∃ t, a' = appLens.setS a t)) : AR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> ab3 hR, hf with exact hX

theorem lift_sort (m m' : Mem) (a a' : AState) (hR : AR m a) (hX : SortR m' a')
    (hf : MemFrame [sortSch.ra, sortSch.sa] [sortSch.ca, sortSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = sortLens.setP a t) ∨ (∃ t, a' = sortLens.setS a t)) : AR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> ab3 hR, hf with exact hX

theorem lift_const (m m' : Mem) (a a' : AState) (hR : AR m a) (hX : ConstR m' a')
    (hf : MemFrame [constSch.ra, constSch.sa] [constSch.ca, constSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = constLens.setP a t) ∨ (∃ t, a' = constLens.setS a t)) : AR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> ab3 hR, hf with exact hX

theorem lift_letE (m m' : Mem) (a a' : AState) (hR : AR m a) (hX : LetR m' a')
    (hf : MemFrame [letSch.ra, letSch.sa] [letSch.ca, letSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = letLens.setP a t) ∨ (∃ t, a' = letLens.setS a t)) : AR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> ab3 hR, hf with exact hX

theorem lift_bvar (m m' : Mem) (a a' : AState) (hR : AR m a) (hX : BVarR m' a')
    (hf : MemFrame [bvarSch.ra, bvarSch.sa] [bvarSch.ca, bvarSch.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = bvarLens.setP a t) ∨ (∃ t, a' = bvarLens.setS a t)) : AR m' a' := by
  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> ab3 hR, hf with exact hX

theorem memo_set (m m' : Mem) (a : AState) (hR : AR m a) (k v : Word)
    (hk : k.toNat < 2 ^ 32) (hs : msetG bmSch m k 0 v = some m') :
    AR m' (withBC a (a.memos.bvarBC.insert (decE k) v.toNat)) := by
  have hf := msetG_frame bmSch bmSch_wf m m' k 0 v hs
  ab3 hR, hf with exact memoRG_set bmSch bmSch_wf bmKey _ m _ hR.memo k 0 v ⟨hk, rfl⟩ m' hs

theorem memo_clear (m : Mem) (a : AState) (hR : AR m a)
    (h0 : rdW (m.arr64 CTL) 24 + 2 ≠ 0) : AR (mclearG bmSch m) (withBC a ∅) := by
  have hf := mclearG_frame bmSch m
  ab3 hR, hf with exact memoRG_clear bmSch bmSch_wf bmKey _ m _ hR.memo h0

theorem grow (m m' : Mem) (hg : Grows m m') (a : AState) (hR : AR m a) : AR m' a := by
  have hf := grows_frame m m' hg
  ab3 hR, hf with
    first | exact LitR.grow m m' hg a hR.lit | exact LsR.grow m m' hg a hR.ls |
      exact NStrR.grow m m' hg a hR.nstr

end L.Arena.Spike
