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
open ConRon.Arena ConRon.Arena.Frontend

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

/-! ## The records, firsts and declaration pool after the switch -/

theorem cqTailS_decl {M : Mem} (hok : CqTailSOK M) {j : Nat} (hj : j < 1 + 8 * (cqDeclA M).toNat) :
    ((cqTailS M).arr64 L.Front.DECL)[j]? = (M.arr64 SDECL)[j]? := by
  obtain ⟨-, -, -, -, hA, -, h1, h2, h3, -⟩ := hok
  have hn : (1 + 8 * cqDeclA M).toNat = 1 + 8 * (cqDeclA M).toNat := by
    simp [UInt64.toNat_add, UInt64.toNat_mul]; omega
  simp only [cqTailS]
  simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]
  rw [cq_copy64_lo (by decide) _ (by omega) (by simp [L.Mem.size64_set64]; omega)
    (by simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]; omega) (by omega)]
  simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]

theorem cqTailS_firsts {M : Mem} (hok : CqTailSOK M) {j : Nat} (hj : j < (cqDeclA M).toNat) :
    ((cqTailS M).arr64 FIRSTS)[j]? = (M.arr64 SFIRSTS)[j]? := by
  obtain ⟨-, -, -, -, hA, -, -, -, -, h4, h5, h6, -⟩ := hok
  simp only [cqTailS]
  simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]
  rw [cq_copy64_lo (by decide) _ (by omega) (by simp (disch := decide) only [size_copy64, L.Mem.size64_set64]; omega)
    (by simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]; omega) (by omega)]
  simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]

theorem cqTailS_dlp {M : Mem} (hok : CqTailSOK M) {j : Nat} (hj : j < 1 + (cqDlpA M).toNat) :
    ((cqTailS M).arr64 L.Front.DLP)[j]? = (M.arr64 SDLP)[j]? := by
  obtain ⟨-, -, -, -, -, hB, -, -, -, -, -, -, h7, h8, h9⟩ := hok
  have hn : (1 + cqDlpA M).toNat = 1 + (cqDlpA M).toNat := by
    simp [UInt64.toNat_add]; omega
  simp only [cqTailS]
  simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne, cqDlpA] at hn hj hB h7 h8 h9 ⊢
  rw [cq_copy64_lo (by decide) _ (by omega) (by simp (disch := decide) only [size_copy64, L.Mem.size64_set64]; omega)
    (by simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]; omega) (by omega)]
  simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]

/-! ## The solution's jobs' memory half after the switch -/

theorem cqMax_ge_right (a b : Word) : b.toNat ≤ (cqMax a b).toNat := by
  unfold cqMax; split
  · exact Nat.le_refl _
  · rename_i h; have := UInt64.not_lt.mp h; exact UInt64.le_iff_toNat_le.mp this

theorem cqRowsS_arr (m : Mem) {b : TieredArray} (h : b ∉ csAS) (hc : b ≠ CCTL)
    (h2 : b ≠ CEIXA ∧ b ≠ CEIXS ∧ b ≠ CEIXN ∧ b ≠ CTIXA ∧ b ≠ CTIXS ∧ b ≠ CTIXN) :
    (cqRowsS m).arr64 b = m.arr64 b := by
  have hn : ∀ x : TieredArray, x ∈ csA → b ≠ x := fun x hx e => h (e ▸ csA_sub_csAS hx)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h2
  simp only [cqRowsS]
  rw [cqRowStep_arr _ c6 (hn _ (by decide)) hc, cqRowStep_arr _ c3 (hn _ (by decide)) hc,
    cqRowStep_arr _ c5 (hn _ (by decide)) hc, cqRowStep_arr _ c2 (hn _ (by decide)) hc,
    cqRowStep_arr _ c4 (hn _ (by decide)) hc, cqRowStep_arr _ c1 (hn _ (by decide)) hc]

theorem cqS_arrT (m : Mem) {b : TieredArray} (h : b ∈ cqTailA) (hc : b ≠ CCTL) :
    (cqCtlSM (cqBankSM m)).arr64 b = (cqBankSM m).arr64 b :=
  (cqCtlSM_frame _).arr b (by simpa using hc) (fun e => by subst e; revert h; decide)

section
variable {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}

/-- **The solution's jobs' memory half at mode `8`'s switch**: from the challenge's at the frozen
memory `m9` (its solution's index `IS`), what `m9` keeps of the solution's index build `m`
(`CsStash`) and the solution's records `dsS`: the solution's (no solution, `CTL[224] = 0`) at the
switched memory, at the same owned state. -/
theorem _root_.L.Arena.JobM.csViewS {J : ISolution} {IS IC : IStreamIndex} {dsS dsC : Array IDeclaration}
    {m m9 : Mem} {a : AState}
    (hC : JobM pins dn dsC (some J) IC m9 a) (hJI : J.idx = IS) (hSt : CsStash m m9)
    (hIS : IndexR m IS) (hDS : DeclsF (m.arr64 L.Front.DECL) (m.arr64 L.Front.DLP) dsS) (hFS : FrozenR m IS)
    (hfs : IS.firsts.size = dsS.size) (hKS : IndexKeysIn m9 IS) (hKC : IndexKeysIn m9 IC)
    (hR : CqRowsSOK m9) (hT : CqTailSOK (cqRowsS m9)) (hCt : CqCtlSOK (cqBankSM m9)) :
    JobM pins dn dsS none IS (cqCtlSM (cqBankSM m9)) a := by
  have hf := cqS_frame m9
  have hBF := cqBankSM_frame [] m9
  have hctl := cqCtlSM_ctl hCt
  have hsol := hC.jsol.sol.2
  have hS : SolIdxR m9 IS := hJI ▸ ⟨hsol.base, hsol.btbl, hsol.next, hsol.size, hsol.rows⟩
  have hout : ∀ w : Word, w.toNat < 2 ^ 32 → rowTag w ≤ 2 → rowTier w = 0 →
      ¬ (idxW w).toNat < nmCnt m9 (rowTag w) → (baseRow m9 w).1 = 0 ∧ (baseTbl m9 w).1 = 0 := by
    intro w hw hg _ hl
    have e : (Idx.ofWord (k := .name) w.toUInt32).word.toUInt64 = w :=
      UInt64.toNat_inj.mp (by simp; omega)
    have := baseRow_out hC.idx hKC (Idx.ofWord w.toUInt32) (by rw [e]; exact hg) (by rw [e]; exact hl)
    rw [e] at this; exact this
  have hE : erecP (cqCtlSM (cqBankSM m9)) = erecP m9 :=
    erecP_congr' (hf.arr _ (by decide) (by decide)) (hf.arr _ (by decide) (by decide))
      (hf.ctl 129 (by decide)) (hf.ctl 130 (by decide))
  -- the records' extent
  have eD : (cqRowsS m9).arr64 L.Front.DECL = m9.arr64 L.Front.DECL := by
    simp only [cqRowsS]; simp (disch := decide) only [cqRowStep_arr]
  have eSD : (cqRowsS m9).arr64 SDECL = m9.arr64 SDECL := cqRowsS_arr m9 (by decide) (by decide) (by decide)
  have eSF : (cqRowsS m9).arr64 SFIRSTS = m9.arr64 SFIRSTS := cqRowsS_arr m9 (by decide) (by decide) (by decide)
  have eSP : (cqRowsS m9).arr64 SDLP = m9.arr64 SDLP := cqRowsS_arr m9 (by decide) (by decide) (by decide)
  have eP : (cqRowsS m9).arr64 L.Front.DLP = m9.arr64 L.Front.DLP := by
    simp only [cqRowsS]; simp (disch := decide) only [cqRowStep_arr]
  have hcnt : (rdW (m.arr64 L.Front.DECL) 0).toNat = dsS.size := hDS.count
  have hsd0 : rdW (m9.arr64 SDECL) 0 = rdW (m.arr64 L.Front.DECL) 0 := by
    simp only [rdW, UInt64.toNat_zero]; rw [hSt.decl 0 (by omega)]
  have hA : dsS.size ≤ (cqDeclA (cqRowsS m9)).toNat := by
    have := cqMax_ge_right (rdW ((cqRowsS m9).arr64 L.Front.DECL) 0) (rdW ((cqRowsS m9).arr64 SDECL) 0)
    rw [eSD, hsd0, hcnt] at this; simp only [cqDeclA]; rw [eSD, hsd0]; exact this
  have hsp0 : rdW (m9.arr64 SDLP) 0 = rdW (m.arr64 L.Front.DLP) 0 := by
    simp only [rdW, UInt64.toNat_zero]; rw [hSt.dlp 0 (by omega)]
  have hB : (rdW (m.arr64 L.Front.DLP) 0).toNat ≤ (cqDlpA (cqRowsS m9)).toNat := by
    have := cqMax_ge_right (rdW ((cqRowsS m9).arr64 L.Front.DLP) 0) (rdW ((cqRowsS m9).arr64 SDLP) 0)
    rw [eSP, hsp0] at this; simp only [cqDlpA]; rw [eSP, hsp0]; exact this
  have hsz : ∀ b, ((cqCtlSM (cqBankSM m9)).arr64 b).size = (m9.arr64 b).size := hf.size
  have hszR : ∀ b, ((cqRowsS m9).arr64 b).size = (m9.arr64 b).size := fun b => by
    rw [← (cqBankSM_frame [] m9).size b]; simp only [cqBankSM]; exact ((cqTailS_frame [] _).size b).symm
  have ⟨_, _, _, _, hA59, _, _, hT2, _, _, hT5, _, _, hT8, _⟩ := hT
  have eB : cqBankSM m9 = cqTailS (cqRowsS m9) := rfl
  have e0 : ∀ P : Array Word, P[0]?.getD 0 = rdW P 0 := fun P => by simp [rdW]
  have hfst : ∀ i (h : i < IS.firsts.size),
      (rdW ((cqCtlSM (cqBankSM m9)).arr64 FIRSTS) (UInt64.ofNat i)).toNat = IS.firsts[i] := by
    intro i h
    have hi : i < dsS.size := hfs ▸ h
    have hn : (UInt64.ofNat i).toNat = i := by simp; omega
    have e1 : rdW ((cqCtlSM (cqBankSM m9)).arr64 FIRSTS) (UInt64.ofNat i) =
        rdW (m.arr64 FIRSTS) (UInt64.ofNat i) := by
      simp only [rdW, hn]
      rw [cqS_arrT m9 (by decide) (by decide), eB, cqTailS_firsts hT (by omega), eSF,
        hSt.firsts i (by omega)]
    rw [e1]; exact hIS.firsts i h
  have hfsz : IS.firsts.size ≤ ((cqCtlSM (cqBankSM m9)).arr64 FIRSTS).size := by
    rw [hsz, ← hszR]; omega
  have h128 : rdW ((cqCtlSM (cqBankSM m9)).arr64 CTL) 128 = rdW (m9.arr64 CTL) 225 := by
    rw [hctl.1]; exact hBF.ctl 225 (by simp)
  have hI : IndexR (cqCtlSM (cqBankSM m9)) IS :=
    csIndexRP hS hKS hout (fun g hg => (cqS_rows hR g hg).1) (fun g hg => (cqS_rows hR g hg).2) hE hfst
      hfsz h128
  have hD : DeclsF ((cqCtlSM (cqBankSM m9)).arr64 L.Front.DECL) ((cqCtlSM (cqBankSM m9)).arr64 L.Front.DLP) dsS :=
    DeclsF.agree hDS
      (fun j hj => by
        rw [cqS_arrT m9 (by decide) (by decide), eB, cqTailS_decl hT (by omega), eSD, hSt.decl j (by omega)])
      (fun j hj => by
        rw [e0] at hj
        rw [cqS_arrT m9 (by decide) (by decide), eB, cqTailS_dlp hT (by omega), eSP, hSt.dlp j (by omega)])
      (by rw [hsz]; exact hC.decls.dsize) (by rw [hsz]; exact hC.decls.psize)
      (by rw [hsz, ← hszR]; omega) (by rw [e0, hsz, ← hszR]; omega)
  have hfz : FrozenR (cqCtlSM (cqBankSM m9)) IS := hFS.congr fun x hx => by
    have hx' : 162 ≤ x.toNat ∧ x.toNat ≤ 173 := by
      simp only [frozenCtl, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hctl.2.1 x hx'.1 hx'.2, hBF.arr SCTL (by decide) (by decide)]; exact hSt.frz x hx
  exact hC.csSwapJ hf hI hD hfz hfs (JSol.none hctl.2.2)

end

end L.Checker
