module

public import ConAgua.Checker.CmpSeqBank
public import ConAgua.Checker.CmpSeqView
import ConAgua.Arena.FreezeSpec

@[expose] public section

/-!
# The solution's view after mode `8`'s switch (lane compare2, the sJ variant)

What `cq_bank_s` and `cq_ctl_s` (`Checker/CmpSeqBank.lean`, `Checker/CmpSeqMv.lean`) leave of the
challenge's frozen memory `m9`: a frame of `csAS`/`csC` (`cqS_frame`), each stream-index row array
the solution's below `2 · count` and the challenge's past it (`cqBankSM_eix`/`cqBankSM_tix`).
-/

namespace L.Checker

open L L.Arena L.Front

/-! ## Frames of single steps -/

theorem MemFrame.copyIn {A : List TieredArray} {C : List Word} {d : TieredArray} (hd : d ∈ A)
    (hc : d ≠ CTL) (m : Mem) (di : Word) (s : TieredArray) (si : Word) (n : Nat) :
    MemFrame A C m (m.copy64 d di s si n) :=
  ⟨fun b hb _ => arr64_copy64_ne _ _ _ _ _ _ (fun e => hb (e ▸ hd)),
   fun x _ => by rw [arr64_copy64_ne _ _ _ _ _ _ (Ne.symm hc)],
   fun b => size_copy64 _ _ _ _ _ _ _⟩

theorem MemFrame.setIn {A : List TieredArray} {C : List Word} {d : TieredArray} (hd : d ∈ A)
    (hc : d ≠ CTL) (m : Mem) (k v : Word) : MemFrame A C m (m.set64 d k v) :=
  (MemFrame.set64 m d hc k v).mono (fun b hb => by simp at hb; exact hb ▸ hd) (fun _ h => by simp at h)

theorem cqRowStep_frame {A : List TieredArray} {C : List Word} {c d s : ArrId} {ca k : Word}
    (hc : (c : TieredArray) ∈ A) (hd : (d : TieredArray) ∈ A) (hc1 : c ≠ CTL) (hd1 : d ≠ CTL) (hC : (CCTL : TieredArray) ∈ A) (m : Mem) :
    MemFrame A C m (cqRowStep c d s ca k m) :=
  ((MemFrame.copyIn hc (by simpa [TieredArray.t0] using hc1) m _ _ _ _).trans (MemFrame.copyIn hd (by simpa [TieredArray.t0] using hd1) _ _ _ _ _)).trans
    (MemFrame.setIn hC (by decide) _ _ _)

/-- **`cq_bank_s` writes only `csAS`**, no `CTL` word. -/
theorem cqBankSM_frame (C : List Word) (m : Mem) : MemFrame csAS C m (cqBankSM m) := by
  have hR : ∀ (c d s : ArrId) (ca k : Word), (c : TieredArray) ∈ csAS → (d : TieredArray) ∈ csAS →
      c ≠ CTL → d ≠ CTL → ∀ m, MemFrame csAS C m (cqRowStep c d s ca k m) :=
    fun c d s ca k hc hd hc1 hd1 m => cqRowStep_frame hc hd hc1 hd1 (by decide) m
  have h6 : MemFrame csAS C m (cqRowsS m) := by
    unfold cqRowsS
    exact (((((hR _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) _).trans (hR _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) _)).trans
      (hR _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) _)).trans (hR _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) _)).trans
      (hR _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) _)).trans (hR _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) _)
  refine h6.trans ?_
  unfold cqBankSM cqTailS
  generalize cqRowsS m = M
  simp only
  exact (((((((((MemFrame.setIn (by decide) (by decide) _ _ _).trans (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans
    (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans (MemFrame.setIn (by decide) (by decide) _ _ _)).trans
    (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans
    (MemFrame.setIn (by decide) (by decide) _ _ _)).trans (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans
    (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _))

/-- **Mode `8`'s switch is a frame of `csAS`/`csC`.** -/
theorem cqS_frame (m : Mem) : MemFrame csAS csC m (cqCtlSM (cqBankSM m)) :=
  (cqBankSM_frame csC m).trans ((cqCtlSM_frame _).mono (fun b hb => by simp at hb; subst hb; decide)
    (fun _ h => h))

/-! ## The rows after the switch -/

theorem cqRowStep_arr {c d s : ArrId} {ca k : Word} (m : Mem) {b : TieredArray} (h1 : b ≠ c) (h2 : b ≠ d)
    (h3 : b ≠ CCTL) : (cqRowStep c d s ca k m).arr64 b = m.arr64 b := by
  simp only [cqRowStep, cqRowsM, Mem.arr64_set64_ne _ _ _ _ _ h3, arr64_copy64_ne _ _ _ _ _ _ h1,
    arr64_copy64_ne _ _ _ _ _ _ h2]

/-- **One row swap's rows**: the solution's `s` below `2 · CTL[ca]`, the challenge's `d` past it. -/
theorem cqRowStep_rows {c d s : ArrId} {ca k : Word} {m : Mem} (hok : CqRowsOK c d s ca m)
    (hcd : c ≠ d) (hcs : c ≠ s) (hds : d ≠ s) (hdC : (d : TieredArray) ≠ CCTL) :
    RowsP ((cqRowStep c d s ca k m).arr64 d) (m.arr64 s) (m.arr64 d) (rdW (m.arr64 CTL) ca).toNat := by
  obtain ⟨h0, h1, h2, h3⟩ := hok
  have hN : (cqRowsN m ca).toNat = 2 * (rdW (m.arr64 CTL) ca).toNat := by
    simp [cqRowsN, UInt64.toNat_mul]; omega
  have hcs' : (c : TieredArray) ≠ s := by simpa [TieredArray.t0] using hcs
  have hcd' : (c : TieredArray) ≠ d := by simpa [TieredArray.t0] using hcd
  intro j
  simp only [cqRowStep, cqRowsM, Mem.arr64_set64_ne _ _ _ _ _ hdC]
  generalize hM : m.copy64 c 0 d 0 (cqRowsN m ca).toNat = M
  have hMs : M.arr64 s = m.arr64 s := by rw [← hM, arr64_copy64_ne _ _ _ _ _ _ (Ne.symm hcs')]
  have hMd : M.arr64 d = m.arr64 d := by rw [← hM, arr64_copy64_ne _ _ _ _ _ _ (Ne.symm hcd')]
  split
  · rw [cq_copy64_lo hds M (by omega) (by rw [hMd]; exact h2) (by rw [hMs]; exact h3) (by omega), hMs]
  · rw [cq_copy64_hi hds M (by omega) (by omega), hMd]

/-- The arrays `cq_bank_s`'s copies after the row swaps write. -/
def cqTailA : List TieredArray := [CCTL, CDECL, L.Front.DECL, CFIRSTS, FIRSTS, CDLP, L.Front.DLP]

theorem cqTailS_frame (C : List Word) (M : Mem) : MemFrame cqTailA C M (cqTailS M) := by
  unfold cqTailS
  simp only
  exact (((((((((MemFrame.setIn (by decide) (by decide) _ _ _).trans (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans
    (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans (MemFrame.setIn (by decide) (by decide) _ _ _)).trans
    (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans
    (MemFrame.setIn (by decide) (by decide) _ _ _)).trans (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans
    (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _))

/-- The row arrays after the whole switch are the row swaps'. -/
theorem cqS_arr_rows (m : Mem) {b : TieredArray} (h1 : b ∉ cqTailA) (h2 : b ≠ CTL) :
    (cqCtlSM (cqBankSM m)).arr64 b = (cqRowsS m).arr64 b := by
  rw [(cqCtlSM_frame _).arr b (by simp; intro e; subst e; revert h1; decide) h2]
  exact (cqTailS_frame [] _).arr b h1 h2

/-- **The stream index's rows after mode `8`'s switch**: the solution's below `2 · count`, the
challenge's past it. -/
theorem cqS_rows {m : Mem} (hok : CqRowsSOK m) (g : Nat) (hg : g ≤ 2) :
    RowsP ((cqCtlSM (cqBankSM m)).arr64 (eixArr g)) (m.arr64 (sixArr g)) (m.arr64 (eixArr g)) (nmCnt m g) ∧
    RowsP ((cqCtlSM (cqBankSM m)).arr64 (tixArr g)) (m.arr64 (stxArr g)) (m.arr64 (tixArr g)) (nmCnt m g) := by
  simp only [CqRowsSOK] at hok
  obtain ⟨o1, o2, o3, o4, o5, o6, -⟩ := hok
  have r1 := cqRowStep_rows (k := 0) o1 (by decide) (by decide) (by decide) (by decide)
  have r2 := cqRowStep_rows (k := 1) o2 (by decide) (by decide) (by decide) (by decide)
  have r3 := cqRowStep_rows (k := 2) o3 (by decide) (by decide) (by decide) (by decide)
  have r4 := cqRowStep_rows (k := 3) o4 (by decide) (by decide) (by decide) (by decide)
  have r5 := cqRowStep_rows (k := 4) o5 (by decide) (by decide) (by decide) (by decide)
  have r6 := cqRowStep_rows (k := 5) o6 (by decide) (by decide) (by decide) (by decide)
  clear o1 o2 o3 o4 o5 o6
  simp (disch := decide) only [cqRowStep_arr] at r1 r2 r3 r4 r5 r6
  have e : g = 0 ∨ g = 1 ∨ g = 2 := by omega
  rcases e with rfl | rfl | rfl
  · show RowsP ((cqCtlSM (cqBankSM m)).arr64 EIXA) (m.arr64 SIXA) (m.arr64 EIXA) (rdW (m.arr64 CTL) 34).toNat ∧
      RowsP ((cqCtlSM (cqBankSM m)).arr64 TIXA) (m.arr64 STXA) (m.arr64 TIXA) (rdW (m.arr64 CTL) 34).toNat
    rw [cqS_arr_rows m (by decide) (by decide), cqS_arr_rows m (by decide) (by decide)]
    simp (disch := decide) only [cqRowsS, cqRowStep_arr]
    exact ⟨r1, r2⟩
  · show RowsP ((cqCtlSM (cqBankSM m)).arr64 EIXS) (m.arr64 SIXS) (m.arr64 EIXS) (rdW (m.arr64 CTL) 36).toNat ∧
      RowsP ((cqCtlSM (cqBankSM m)).arr64 TIXS) (m.arr64 STXS) (m.arr64 TIXS) (rdW (m.arr64 CTL) 36).toNat
    rw [cqS_arr_rows m (by decide) (by decide), cqS_arr_rows m (by decide) (by decide)]
    simp (disch := decide) only [cqRowsS, cqRowStep_arr]
    exact ⟨r3, r4⟩
  · show RowsP ((cqCtlSM (cqBankSM m)).arr64 EIXN) (m.arr64 SIXN) (m.arr64 EIXN) (rdW (m.arr64 CTL) 38).toNat ∧
      RowsP ((cqCtlSM (cqBankSM m)).arr64 TIXN) (m.arr64 STXN) (m.arr64 TIXN) (rdW (m.arr64 CTL) 38).toNat
    rw [cqS_arr_rows m (by decide) (by decide), cqS_arr_rows m (by decide) (by decide)]
    simp (disch := decide) only [cqRowsS, cqRowStep_arr]
    exact ⟨r5, r6⟩

end L.Checker
