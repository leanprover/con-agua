module

public import ConAgua.Checker.CmpSeqViewS
public import ConAgua.Checker.CmpSeqCheck
public import ConAgua.Checker.CmpSeqW
import ConAgua.Arena.FreezeSpec
import ConAgua.Arena.ScratchRefine

@[expose] public section

/-!
# The challenge's view back after the solution's jobs (lane compare2, the sJ variant)

Mode `8`'s switch (`cq_bank_s`) copies each array of the challenge's view (`EIX*`, `TIX*`, `DECL`,
`FIRSTS`, `DLP`) to its stash (`CEIX*`, …) up to an extent kept in `CCTL[0‥8]`, then the
solution's prefix over it. The solution's jobs never store to the stash arrays, the stream index's
arrays nor `CCTL` (`cq_checkJobs_frame0`), so mode `9`'s `cq_bank_c` (copying each stash prefix
back) restores the stream index's arrays exactly and the records and the pool in their used words
(`cqC_view`: `CsViewC`), and the jobs kept what `CsKeep` needs (`cqS_keep`).
-/

namespace L.Checker

open L L.Arena L.Front

/-- The stashed arrays: (array, its stash, the extent's `CCTL` slot). -/
def cqPairs : List (ArrId × ArrId × Word) :=
  [(EIXA, CEIXA, 0), (TIXA, CTIXA, 1), (EIXS, CEIXS, 2), (TIXS, CTIXS, 3), (EIXN, CEIXN, 4),
   (TIXN, CTIXN, 5), (L.Front.DECL, CDECL, 6), (FIRSTS, CFIRSTS, 7), (L.Front.DLP, CDLP, 8)]

/-- **`c` holds `m`'s `b` below the extent `CCTL[k]` of `A`** (in bounds). -/
structure CqSv (m A : Mem) (b c : ArrId) (k : Word) : Prop where
  n63 : (rdW (A.arr64 CCTL) k).toNat < 2 ^ 63
  nb : (rdW (A.arr64 CCTL) k).toNat ≤ (m.arr64 b).size
  nc : (rdW (A.arr64 CCTL) k).toNat ≤ (A.arr64 c).size
  lo : ∀ j, j < (rdW (A.arr64 CCTL) k).toNat → (A.arr64 c)[j]? = (m.arr64 b)[j]?

/-- `A`'s `b` is `m`'s past the extent `CCTL[k]`. -/
def CqHi (m A : Mem) (b : ArrId) (k : Word) : Prop :=
  ∀ j, (rdW (A.arr64 CCTL) k).toNat ≤ j → (A.arr64 b)[j]? = (m.arr64 b)[j]?

theorem CqSv.congr {m A A' : Mem} {b c : ArrId} {k : Word} (h : CqSv m A b c k)
    (ec : A'.arr64 c = A.arr64 c) (ek : rdW (A'.arr64 CCTL) k = rdW (A.arr64 CCTL) k) :
    CqSv m A' b c k :=
  ⟨by rw [ek]; exact h.n63, by rw [ek]; exact h.nb, by rw [ek, ec]; exact h.nc,
   fun j hj => by rw [ec]; exact h.lo j (by rw [← ek]; exact hj)⟩

theorem CqSv.orig {m m' A : Mem} {b c : ArrId} {k : Word} (h : CqSv m A b c k)
    (e : m'.arr64 b = m.arr64 b) : CqSv m' A b c k :=
  ⟨h.n63, by rw [e]; exact h.nb, h.nc, fun j hj => by rw [e]; exact h.lo j hj⟩

theorem CqHi.congr {m A A' : Mem} {b : ArrId} {k : Word} (h : CqHi m A b k)
    (eb : A'.arr64 b = A.arr64 b) (ek : rdW (A'.arr64 CCTL) k = rdW (A.arr64 CCTL) k) :
    CqHi m A' b k :=
  fun j hj => by rw [eb]; exact h j (by rw [← ek]; exact hj)

theorem CqHi.orig {m m' A : Mem} {b : ArrId} {k : Word} (h : CqHi m A b k)
    (e : m'.arr64 b = m.arr64 b) : CqHi m' A b k :=
  fun j hj => by rw [e]; exact h j hj

/-- **One stash-and-overwrite step**: `c := d`, `d := s` below `N`, `N` in slot `k`. -/
theorem cqSv_core {c d s : ArrId} (hcd : c ≠ d) (hds : d ≠ s) {M A : Mem} {k N : Word}
    (hn : N.toNat < 2 ^ 63) (hc : N.toNat ≤ (M.arr64 c).size) (hd : N.toNat ≤ (M.arr64 d).size)
    (eC : A.arr64 c = ((M.copy64 c 0 d 0 N.toNat).copy64 d 0 s 0 N.toNat).arr64 c)
    (eD : A.arr64 d = ((M.copy64 c 0 d 0 N.toNat).copy64 d 0 s 0 N.toNat).arr64 d)
    (eK : rdW (A.arr64 CCTL) k = N) : CqSv M A d c k ∧ CqHi M A d k := by
  have hcd' : (c : TieredArray) ≠ d := by simpa [TieredArray.t0] using hcd
  refine ⟨⟨by rw [eK]; exact hn, by rw [eK]; exact hd, by rw [eK, eC, size_copy64, size_copy64]; exact hc,
    fun j hj => ?_⟩, fun j hj => ?_⟩
  · rw [eK] at hj
    rw [eC, arr64_copy64_ne _ _ _ _ _ _ hcd', cq_copy64_lo hcd M hn hc hd hj]
  · rw [eK] at hj
    rw [eD, cq_copy64_hi hds _ hn (by omega), arr64_copy64_ne _ _ _ _ _ _ (Ne.symm hcd')]

/-- **A row swap of `cq_bank_s` stashes its row**. -/
theorem cqRowStep_sv {c d s : ArrId} {ca k : Word} {M : Mem} (hok : CqRowsOK c d s ca M)
    (hk : k.toNat < (M.arr64 CCTL).size) (hcd : c ≠ d) (hds : d ≠ s) (hcC : (c : TieredArray) ≠ CCTL)
    (hdC : (d : TieredArray) ≠ CCTL) :
    CqSv M (cqRowStep c d s ca k M) d c k ∧ CqHi M (cqRowStep c d s ca k M) d k := by
  obtain ⟨h0, h1, h2, -⟩ := hok
  have hN : (cqRowsN M ca).toNat = 2 * (rdW (M.arr64 CTL) ca).toNat := by
    simp [cqRowsN, UInt64.toNat_mul]; omega
  exact cqSv_core hcd hds (by omega) h1 h2
    (by simp only [cqRowStep, cqRowsM, Mem.arr64_set64_ne _ _ _ _ _ hcC])
    (by simp only [cqRowStep, cqRowsM, Mem.arr64_set64_ne _ _ _ _ _ hdC])
    (by simp only [cqRowStep]; exact cq_rdW_hit (by simp only [cqRowsM, size_copy64]; exact hk))

theorem cqRowStep_cctl {c d s : ArrId} {ca k k' : Word} (m : Mem) (hk : k' ≠ k)
    (hc : (CCTL : TieredArray) ≠ c) (hd : (CCTL : TieredArray) ≠ d) :
    rdW ((cqRowStep c d s ca k' m).arr64 CCTL) k = rdW (m.arr64 CCTL) k := by
  simp only [cqRowStep, cqRowsM]
  rw [cq_rdW_idx hk, arr64_copy64_ne _ _ _ _ _ _ hd, arr64_copy64_ne _ _ _ _ _ _ hc]

theorem cqRowStep_csize {c d s : ArrId} {ca k : Word} (m : Mem) :
    ((cqRowStep c d s ca k m).arr64 CCTL).size = (m.arr64 CCTL).size := by
  simp only [cqRowStep, cqRowsM, L.Mem.size64_set64, size_copy64]

/-! ## The tail's stashes -/

theorem cqTailS_cctl_lo (M : Mem) {k : Word} (hk : k.toNat < 6) :
    rdW ((cqTailS M).arr64 CCTL) k = rdW (M.arr64 CCTL) k := by
  have h6 : (6 : Word) ≠ k := fun e => by subst e; simp at hk
  have h7 : (7 : Word) ≠ k := fun e => by subst e; simp at hk
  have h8 : (8 : Word) ≠ k := fun e => by subst e; simp at hk
  simp only [cqTailS]
  simp (disch := decide) only [arr64_copy64_ne]
  rw [cq_rdW_idx h8]
  simp (disch := decide) only [arr64_copy64_ne]
  rw [cq_rdW_idx h7]
  simp (disch := decide) only [arr64_copy64_ne]
  rw [cq_rdW_idx h6]

theorem cqTailS_slot6 (M : Mem) (hcc : 9 ≤ (M.arr64 CCTL).size) :
    rdW ((cqTailS M).arr64 CCTL) 6 = 1 + 8 * cqDeclA M := by
  simp only [cqTailS]
  simp (disch := decide) only [arr64_copy64_ne]
  rw [cq_rdW_idx (by decide : (8 : Word) ≠ 6)]
  simp (disch := decide) only [arr64_copy64_ne]
  rw [cq_rdW_idx (by decide : (7 : Word) ≠ 6)]
  simp (disch := decide) only [arr64_copy64_ne]
  rw [cq_rdW_hit (by simp; omega)]

theorem cqTailS_slot7 (M : Mem) (hcc : 9 ≤ (M.arr64 CCTL).size) :
    rdW ((cqTailS M).arr64 CCTL) 7 = cqDeclA M := by
  simp only [cqTailS]
  simp (disch := decide) only [arr64_copy64_ne]
  rw [cq_rdW_idx (by decide : (8 : Word) ≠ 7)]
  simp (disch := decide) only [arr64_copy64_ne]
  rw [cq_rdW_hit (by simp (disch := decide) only [size_copy64, L.Mem.size64_set64]; simp; omega)]

theorem cqTailS_slot8 (M : Mem) (hcc : 9 ≤ (M.arr64 CCTL).size) :
    rdW ((cqTailS M).arr64 CCTL) 8 = 1 + cqDlpA M := by
  simp only [cqTailS]
  simp (disch := decide) only [arr64_copy64_ne]
  rw [cq_rdW_hit (by simp (disch := decide) only [size_copy64, L.Mem.size64_set64]; simp; omega)]
  simp (disch := decide) only [cqDlpA, arr64_copy64_ne, Mem.arr64_set64_ne]

theorem cqTailS_cdecl {M : Mem} (hok : CqTailSOK M) {j : Nat} (hj : j < 1 + 8 * (cqDeclA M).toNat) :
    ((cqTailS M).arr64 CDECL)[j]? = (M.arr64 L.Front.DECL)[j]? := by
  obtain ⟨-, -, -, -, hA, -, h1, h2, h3, -⟩ := hok
  have hn : (1 + 8 * cqDeclA M).toNat = 1 + 8 * (cqDeclA M).toNat := by
    simp [UInt64.toNat_add, UInt64.toNat_mul]; omega
  simp only [cqTailS]
  simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]
  rw [cq_copy64_lo (by decide) _ (by omega) (by simp [L.Mem.size64_set64]; omega)
    (by simp (disch := decide) only [Mem.arr64_set64_ne]; omega) (by omega)]
  simp (disch := decide) only [Mem.arr64_set64_ne]

theorem cqTailS_cfirsts {M : Mem} (hok : CqTailSOK M) {j : Nat} (hj : j < (cqDeclA M).toNat) :
    ((cqTailS M).arr64 CFIRSTS)[j]? = (M.arr64 FIRSTS)[j]? := by
  obtain ⟨-, -, -, -, hA, -, -, -, -, h4, h5, h6, -⟩ := hok
  simp only [cqTailS]
  simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]
  rw [cq_copy64_lo (by decide) _ (by omega) (by simp (disch := decide) only [size_copy64, L.Mem.size64_set64]; omega)
    (by simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]; omega) (by omega)]
  simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]

theorem cqTailS_firsts_hi {M : Mem} (hok : CqTailSOK M) {j : Nat} (hj : (cqDeclA M).toNat ≤ j) :
    ((cqTailS M).arr64 FIRSTS)[j]? = (M.arr64 FIRSTS)[j]? := by
  obtain ⟨-, -, -, -, hA, -⟩ := hok
  simp only [cqTailS]
  simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]
  rw [cq_copy64_hi (by decide) _ (by omega) (by omega)]
  simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]

theorem cqTailS_cdlp {M : Mem} (hok : CqTailSOK M) {j : Nat} (hj : j < 1 + (cqDlpA M).toNat) :
    ((cqTailS M).arr64 CDLP)[j]? = (M.arr64 L.Front.DLP)[j]? := by
  obtain ⟨-, -, -, -, -, hB, -, -, -, -, -, -, h7, h8, h9⟩ := hok
  have hn : (1 + cqDlpA M).toNat = 1 + (cqDlpA M).toNat := by
    simp [UInt64.toNat_add]; omega
  simp only [cqTailS]
  simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne, cqDlpA] at hn hj hB h7 h8 h9 ⊢
  rw [cq_copy64_lo (by decide) _ (by omega) (by simp (disch := decide) only [size_copy64, L.Mem.size64_set64]; omega)
    (by simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]; omega) (by omega)]
  simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne]

/-! ## The stashes after mode `8`'s switch -/

theorem cqMax_ge_left (a b : Word) : a.toNat ≤ (cqMax a b).toNat := by
  unfold cqMax; split
  · rename_i h; exact Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp h)
  · exact Nat.le_refl _

set_option hygiene false in
/-- The bank's array as the row swaps' (`eA` in scope). -/
local macro "cq_ec" : tactic =>
  `(tactic| (rw [eA _ (by decide) (by decide)]; simp (disch := decide) only [cqRowsS, cqRowStep_arr]))

set_option hygiene false in
/-- The bank's slot as the row swaps' (`eK` in scope). -/
local macro "cq_ek" : tactic =>
  `(tactic| (rw [eK _ (by decide)]; simp (disch := decide) only [cqRowsS, cqRowStep_cctl]))

/-- The row before a swap is the frozen memory's. -/
local macro "cq_eo" : tactic => `(tactic| simp (disch := decide) only [cqRowStep_arr])

/-- **`cq_bank_s`'s row swaps stash the rows**: each row's stash holds the frozen memory's row
below its extent, and the row past it is the frozen memory's. -/
theorem cqBankSM_rows {m9 : Mem} (hR : CqRowsSOK m9) :
    ∀ p ∈ cqPairs.take 6, CqSv m9 (cqBankSM m9) p.1 p.2.1 p.2.2 ∧ CqHi m9 (cqBankSM m9) p.1 p.2.2 := by
  simp only [CqRowsSOK] at hR
  obtain ⟨o1, o2, o3, o4, o5, o6, h9⟩ := hR
  have hs : ∀ (c d s : ArrId) (ca k : Word) (m : Mem), ((cqRowStep c d s ca k m).arr64 CCTL).size =
      (m.arr64 CCTL).size := fun _ _ _ _ _ m => cqRowStep_csize m
  have s1 := cqRowStep_sv (k := 0) o1 (by simp only [UInt64.toNat_zero]; omega) (by decide) (by decide) (by decide) (by decide)
  have s2 := cqRowStep_sv (k := 1) o2 (by simp only [hs]; simp; omega) (by decide) (by decide) (by decide) (by decide)
  have s3 := cqRowStep_sv (k := 2) o3 (by simp only [hs]; simp; omega) (by decide) (by decide) (by decide) (by decide)
  have s4 := cqRowStep_sv (k := 3) o4 (by simp only [hs]; simp; omega) (by decide) (by decide) (by decide) (by decide)
  have s5 := cqRowStep_sv (k := 4) o5 (by simp only [hs]; simp; omega) (by decide) (by decide) (by decide) (by decide)
  have s6 := cqRowStep_sv (k := 5) o6 (by simp only [hs]; simp; omega) (by decide) (by decide) (by decide) (by decide)
  clear o1 o2 o3 o4 o5 o6
  have eA : ∀ b : ArrId, (b : TieredArray) ∉ cqTailA → (b : TieredArray) ≠ CTL →
      (cqBankSM m9).arr64 b = (cqRowsS m9).arr64 b :=
    fun b h hc => (cqTailS_frame [] _).arr b h hc
  have eK : ∀ k : Word, k.toNat < 6 → rdW ((cqBankSM m9).arr64 CCTL) k = rdW ((cqRowsS m9).arr64 CCTL) k :=
    fun k hk => cqTailS_cctl_lo _ hk
  intro p hp
  simp only [cqPairs, List.take, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only
  · exact ⟨s1.1.congr (by cq_ec) (by cq_ek), s1.2.congr (by cq_ec) (by cq_ek)⟩
  · exact ⟨(s2.1.congr (by cq_ec) (by cq_ek)).orig (by cq_eo), (s2.2.congr (by cq_ec) (by cq_ek)).orig (by cq_eo)⟩
  · exact ⟨(s3.1.congr (by cq_ec) (by cq_ek)).orig (by cq_eo), (s3.2.congr (by cq_ec) (by cq_ek)).orig (by cq_eo)⟩
  · exact ⟨(s4.1.congr (by cq_ec) (by cq_ek)).orig (by cq_eo), (s4.2.congr (by cq_ec) (by cq_ek)).orig (by cq_eo)⟩
  · exact ⟨(s5.1.congr (by cq_ec) (by cq_ek)).orig (by cq_eo), (s5.2.congr (by cq_ec) (by cq_ek)).orig (by cq_eo)⟩
  · exact ⟨(s6.1.congr (by cq_ec) (by cq_ek)).orig (by cq_eo), (s6.2.congr (by cq_ec) (by cq_ek)).orig (by cq_eo)⟩

/-- **`cq_bank_s`'s tail stashes the records, the firsts and the pool.** -/
theorem cqBankSM_tail {m9 : Mem} (hR : CqRowsSOK m9) (hT : CqTailSOK (cqRowsS m9)) :
    CqSv m9 (cqBankSM m9) L.Front.DECL CDECL 6 ∧ CqSv m9 (cqBankSM m9) FIRSTS CFIRSTS 7 ∧
      CqHi m9 (cqBankSM m9) FIRSTS 7 ∧ CqSv m9 (cqBankSM m9) L.Front.DLP CDLP 8 := by
  have h9 : 9 ≤ ((cqRowsS m9).arr64 CCTL).size := by
    simp only [cqRowsS, cqRowStep_csize]; exact hR.2.2.2.2.2.2
  have eB : cqBankSM m9 = cqTailS (cqRowsS m9) := rfl
  have eR : ∀ b : ArrId, b = L.Front.DECL ∨ b = FIRSTS ∨ b = L.Front.DLP →
      (cqRowsS m9).arr64 b = m9.arr64 b := by
    intro b hb; rcases hb with rfl | rfl | rfl <;> simp (disch := decide) only [cqRowsS, cqRowStep_arr]
  have hz : ∀ b, ((cqBankSM m9).arr64 b).size = ((cqRowsS m9).arr64 b).size :=
    fun b => (cqTailS_frame [] _).size b
  have hz9 : ∀ b, ((cqRowsS m9).arr64 b).size = (m9.arr64 b).size := fun b => by
    rw [← (cqBankSM_frame [] m9).size b, hz]
  have hT' := hT
  obtain ⟨-, -, -, -, hA, hB, k1, k2, -, k4, k5, -, k7, k8, -⟩ := hT'
  have n6 : (rdW ((cqBankSM m9).arr64 CCTL) 6).toNat = 1 + 8 * (cqDeclA (cqRowsS m9)).toNat := by
    rw [eB, cqTailS_slot6 _ h9]; simp [UInt64.toNat_add, UInt64.toNat_mul]; omega
  have n7 : (rdW ((cqBankSM m9).arr64 CCTL) 7).toNat = (cqDeclA (cqRowsS m9)).toNat := by
    rw [eB, cqTailS_slot7 _ h9]
  have n8 : (rdW ((cqBankSM m9).arr64 CCTL) 8).toNat = 1 + (cqDlpA (cqRowsS m9)).toNat := by
    rw [eB, cqTailS_slot8 _ h9]; simp [UInt64.toNat_add]; omega
  refine ⟨⟨?_, ?_, ?_, fun j hj => ?_⟩, ⟨?_, ?_, ?_, fun j hj => ?_⟩, fun j hj => ?_, ⟨?_, ?_, ?_, fun j hj => ?_⟩⟩
  · rw [n6]; omega
  · rw [n6, ← hz9]; omega
  · rw [n6, hz]; omega
  · rw [n6] at hj; rw [eB, cqTailS_cdecl hT hj, eR _ (.inl rfl)]
  · rw [n7]; omega
  · rw [n7, ← hz9]; omega
  · rw [n7, hz]; omega
  · rw [n7] at hj; rw [eB, cqTailS_cfirsts hT hj, eR _ (.inr (.inl rfl))]
  · rw [n7] at hj; rw [eB, cqTailS_firsts_hi hT hj, eR _ (.inr (.inl rfl))]
  · rw [n8]; omega
  · rw [n8, ← hz9]; omega
  · rw [n8, hz]; omega
  · rw [n8] at hj; rw [eB, cqTailS_cdlp hT hj, eR _ (.inr (.inr rfl))]

/-! ## Mode `9`'s switch back -/

/-- `cq_bank_c` copies each stash back, as one prefix copy of its arrays. -/
theorem cqBankCM_pair (M : Mem) {b c : ArrId} {k : Word} (h : (b, c, k) ∈ cqPairs) :
    b ≠ c ∧ ∃ M' : Mem, M'.arr64 b = M.arr64 b ∧ M'.arr64 c = M.arr64 c ∧
      (cqBankCM M).arr64 b = (M'.copy64 b 0 c 0 (rdW (M.arr64 CCTL) k).toNat).arr64 b := by
  simp only [cqPairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  · simp only [cqBankCM]
    refine ⟨by decide, ?_⟩
    try simp (disch := decide) only [arr64_copy64_ne]
    refine ⟨_, ?_, ?_, rfl⟩ <;> simp (disch := decide) only [arr64_copy64_ne]

/-- **`cq_bank_c` restores the stashed words.** -/
theorem CqSv.back_lo {m A : Mem} {b c : ArrId} {k : Word} (h : CqSv m A b c k) (hp : (b, c, k) ∈ cqPairs)
    (hsz : (A.arr64 b).size = (m.arr64 b).size) :
    ∀ j, j < (rdW (A.arr64 CCTL) k).toNat → ((cqBankCM A).arr64 b)[j]? = (m.arr64 b)[j]? := by
  intro j hj
  obtain ⟨hbc, M', e1, e2, e3⟩ := cqBankCM_pair A hp
  rw [e3, cq_copy64_lo hbc M' h.n63 (by rw [e1, hsz]; exact h.nb) (by rw [e2]; exact h.nc) hj, e2]
  exact h.lo j hj

/-- **`cq_bank_c` restores a stashed array** whose words past the extent were kept. -/
theorem CqSv.back {m A : Mem} {b c : ArrId} {k : Word} (h : CqSv m A b c k) (hH : CqHi m A b k)
    (hp : (b, c, k) ∈ cqPairs) (hsz : (A.arr64 b).size = (m.arr64 b).size) :
    (cqBankCM A).arr64 b = m.arr64 b := by
  apply Array.ext_getElem?
  intro j
  by_cases hj : j < (rdW (A.arr64 CCTL) k).toNat
  · exact h.back_lo hp hsz j hj
  · obtain ⟨hbc, M', e1, e2, e3⟩ := cqBankCM_pair A hp
    rw [e3, cq_copy64_hi hbc M' h.n63 hj, e1]
    exact hH j (by omega)

/-- **`cq_bank_c` writes only `csA`**, no `CTL` word. -/
theorem cqBankCM_frame (C : List Word) (m : Mem) : MemFrame csA C m (cqBankCM m) := by
  unfold cqBankCM
  exact ((((((((MemFrame.copyIn (by decide) (by decide) _ _ _ _ _).trans (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans
    (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans
    (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans
    (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans
    (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)

/-! ## Header C's view after the solution's jobs -/

theorem cq_stash_not_cqA {b : TieredArray} (h : cqStash b = true) : b ∉ cqA :=
  cq_not_cqA (.inr (.inr (.inr h)))

theorem cq_idx_not_cqA {b : TieredArray} (h : IdxArr b = true) : b ∉ cqA :=
  cq_not_cqA (.inl (cq_not_cdA (.inl h)))

/-- **The solution's rows after the solution's jobs** are the frozen memory's (mode `8`'s copies
and the jobs' stores avoid them). -/
theorem cqS_sol {m9 mS : Mem} (hJ : MemFrame cqA cqC (cqSM m9) mS) :
    ∀ b ∈ solArrs, mS.arr64 b = m9.arr64 b := by
  have fS := cqS_frame m9
  have f2 := flushMem_frame (cqCtlSM (cqBankSM m9))
  have hJ' : MemFrame cqA cqC (flushMem (cqCtlSM (cqBankSM m9))) mS := hJ
  have nS : ∀ b ∈ solArrs, b ∉ cqA := fun b hb => cq_not_cqA (.inl (cq_not_cdA (.inr (.inr (by
    have := solArrs_arr hb; simp only [SolArr, this.2.2, beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
      decide_eq_true_eq]; omega)))))
  intro b hb
  have hc : b ≠ CTL := fun e => by subst e; revert hb; decide
  rw [hJ'.arr b (nS b hb) hc, f2.arr b (by simp) hc,
    fS.arr b (fun hm => by have := csAS_arr hm; have := solArrs_arr hb; omega) hc]

/-- **Mode `9`'s switch restores the challenge's view** (`CsViewC`) after the solution's jobs, which
stored only to the flag-`0` write set (`cq_checkJobs_frame0`) from mode `8`'s memory. -/
theorem cqC_view {m9 mS : Mem} (hR : CqRowsSOK m9) (hT : CqTailSOK (cqRowsS m9))
    (hCt : CqCtlSOK (cqBankSM m9)) (hJ : MemFrame cqA cqC (cqSM m9) mS) (hCC : CqCtlCOK (cqBankCM mS)) :
    CsViewC m9 mS (cqCtlCM (cqBankCM mS)) := by
  have f1 := cqCtlSM_frame (cqBankSM m9)
  have f2 := flushMem_frame (cqCtlSM (cqBankSM m9))
  have eS : ∀ b : TieredArray, b ∉ cqA → b ≠ CTL → mS.arr64 b = (cqCtlSM (cqBankSM m9)).arr64 b :=
    fun b h1 h2 => (hJ.arr b h1 h2).trans (f2.arr b (by simp) h2)
  have eC : mS.arr64 CCTL = (cqCtlSM (cqBankSM m9)).arr64 CCTL :=
    eS _ (cq_stash_not_cqA (by decide)) (by decide)
  have eSB : ∀ b : TieredArray, b ∉ cqA → b ≠ CTL → b ≠ CCTL → mS.arr64 b = (cqBankSM m9).arr64 b :=
    fun b h1 h2 h3 => (eS b h1 h2).trans (f1.arr b (by simp [h3]) h2)
  have eK : ∀ k : Word, k.toNat < 16 → rdW (mS.arr64 CCTL) k = rdW ((cqBankSM m9).arr64 CCTL) k :=
    fun k hk => by rw [eC]; exact cqCtlSM_cctl_keep _ k (.inl hk)
  have hsz : ∀ b, (mS.arr64 b).size = (m9.arr64 b).size := fun b => by
    rw [hJ.size]; show ((flushMem (cqCtlSM (cqBankSM m9))).arr64 b).size = _
    rw [f2.size, f1.size, (cqBankSM_frame [] m9).size]
  -- the stashes at `mS`
  have hr := cqBankSM_rows hR
  have ⟨t6, t7, t7h, t8⟩ := cqBankSM_tail hR hT
  have sv : ∀ {b c : ArrId} {k : Word}, CqSv m9 (cqBankSM m9) b c k → cqStash c = true →
      (c : TieredArray) ≠ CTL → (c : TieredArray) ≠ CCTL → k.toNat < 16 → CqSv m9 mS b c k :=
    fun h hc h1 h2 hk => h.congr (eSB _ (cq_stash_not_cqA hc) h1 h2) (eK _ hk)
  have back : ∀ {b c : ArrId} {k : Word}, (b, c, k) ∈ cqPairs → CqSv m9 (cqBankSM m9) b c k →
      CqHi m9 (cqBankSM m9) b k → cqStash c = true → (c : TieredArray) ≠ CTL → (c : TieredArray) ≠ CCTL →
      IdxArr b = true → (b : TieredArray) ≠ CTL → (b : TieredArray) ≠ CCTL → k.toNat < 16 →
      (cqCtlCM (cqBankCM mS)).arr64 b = m9.arr64 b := fun hp h hH hc h1 h2 hb h3 h4 hk => by
    rw [cqCtlCM_arr _ _ h3]
    exact (sv h hc h1 h2 hk).back (hH.congr (eSB _ (cq_idx_not_cqA hb) h3 h4) (eK _ hk)) hp (hsz _)
  have bF := (cqBankCM_frame csC mS)
  have hfr : MemFrame csA csC mS (cqCtlCM (cqBankCM mS)) := bF.trans ((cqCtlCM_frame _).mono (by simp) (fun _ h => h))
  have hrows : ∀ b ∈ solRowsS, (cqCtlCM (cqBankCM mS)).arr64 b = m9.arr64 b := by
    intro b hb
    have hsa : b ∈ solArrs := by
      simp only [solRowsS, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have ha := solArrs_arr hsa
    rw [hfr.arr b (fun hm => by have := csA_arr hm; omega) (fun e => by subst e; revert hsa; decide),
      cqS_sol hJ b hsa]
  refine ⟨hfr.mono (fun _ h => csA_sub_csAV h) (fun _ h => h), hrows, fun b hb => ?_, fun j hj => ?_,
    fun j hj => ?_, ?_, ?_, fun x hx => ?_⟩
  · obtain ⟨n, hi⟩ := b
    simp only [IdxArr, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hb
    obtain ⟨rfl, h1⟩ := hb
    have : n = 129 ∨ n = 130 ∨ n = 131 ∨ n = 132 ∨ n = 133 ∨ n = 134 ∨ n = 137 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact back (b := TIXA) (c := CTIXA) (k := 1) (by decide) (hr (TIXA, CTIXA, 1) (by decide)).1
        (hr (TIXA, CTIXA, 1) (by decide)).2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact back (b := TIXS) (c := CTIXS) (k := 3) (by decide) (hr (TIXS, CTIXS, 3) (by decide)).1
        (hr (TIXS, CTIXS, 3) (by decide)).2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact back (b := TIXN) (c := CTIXN) (k := 5) (by decide) (hr (TIXN, CTIXN, 5) (by decide)).1
        (hr (TIXN, CTIXN, 5) (by decide)).2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact back (b := EIXA) (c := CEIXA) (k := 0) (by decide) (hr (EIXA, CEIXA, 0) (by decide)).1
        (hr (EIXA, CEIXA, 0) (by decide)).2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact back (b := EIXS) (c := CEIXS) (k := 2) (by decide) (hr (EIXS, CEIXS, 2) (by decide)).1
        (hr (EIXS, CEIXS, 2) (by decide)).2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact back (b := EIXN) (c := CEIXN) (k := 4) (by decide) (hr (EIXN, CEIXN, 4) (by decide)).1
        (hr (EIXN, CEIXN, 4) (by decide)).2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact back (b := FIRSTS) (c := CFIRSTS) (k := 7) (by decide) t7 t7h (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)
  · -- the records' used words
    have s6 := sv t6 (by decide) (by decide) (by decide) (by decide)
    have hle : 1 + 8 * (rdW (m9.arr64 L.Front.DECL) 0).toNat ≤ (rdW (mS.arr64 CCTL) 6).toNat := by
      rw [eK _ (by decide), show cqBankSM m9 = cqTailS (cqRowsS m9) from rfl,
        cqTailS_slot6 _ (by simp only [cqRowsS, cqRowStep_csize]; exact hR.2.2.2.2.2.2)]
      have hA := hT.2.2.2.2.1
      have h0 := cqMax_ge_left (rdW ((cqRowsS m9).arr64 L.Front.DECL) 0) (rdW ((cqRowsS m9).arr64 SDECL) 0)
      have e : (cqRowsS m9).arr64 L.Front.DECL = m9.arr64 L.Front.DECL := by
        simp (disch := decide) only [cqRowsS, cqRowStep_arr]
      rw [e] at h0
      simp only [cqDeclA, e] at hA ⊢
      simp [UInt64.toNat_add, UInt64.toNat_mul]; omega
    rw [cqCtlCM_arr _ _ (by decide)]
    exact s6.back_lo (by decide) (hsz _) j (by omega)
  · -- the pool's used words
    have s8 := sv t8 (by decide) (by decide) (by decide) (by decide)
    have hle : 1 + (rdW (m9.arr64 L.Front.DLP) 0).toNat ≤ (rdW (mS.arr64 CCTL) 8).toNat := by
      rw [eK _ (by decide), show cqBankSM m9 = cqTailS (cqRowsS m9) from rfl,
        cqTailS_slot8 _ (by simp only [cqRowsS, cqRowStep_csize]; exact hR.2.2.2.2.2.2)]
      have hB := hT.2.2.2.2.2.1
      have h0 := cqMax_ge_left (rdW ((cqRowsS m9).arr64 L.Front.DLP) 0) (rdW ((cqRowsS m9).arr64 SDLP) 0)
      have e : (cqRowsS m9).arr64 L.Front.DLP = m9.arr64 L.Front.DLP := by
        simp (disch := decide) only [cqRowsS, cqRowStep_arr]
      rw [e] at h0
      simp only [cqDlpA, e] at hB ⊢
      simp [UInt64.toNat_add]; omega
    rw [cqCtlCM_arr _ _ (by decide)]
    exact s8.back_lo (by decide) (hsz _) j (by omega)
  · rw [cqCtlCM_arr _ _ (by decide), bF.size, hsz]
  · rw [cqCtlCM_arr _ _ (by decide), bF.size, hsz]
  · rw [cqCtlCM_ctl hCC x hx, bF.arr _ (by decide) (by decide), eC, cqCtlSM_cctl hCt x hx]
    exact (cqBankSM_frame [] m9).ctl x (by simp)

/-- **What the solution's jobs keep of the frozen memory** (`CsKeep`): they stored only to the
flag-`0` write set from mode `8`'s memory, and grew the record pool. -/
theorem cqS_keep {m9 mS : Mem} (hJ : MemFrame cqA cqC (cqSM m9) mS)
    (hx : ArrExt (erecP (cqSM m9)) (erecP mS)) (hW : WalkMem m9) : CsKeep m9 mS := by
  have fS := cqS_frame m9
  have f2 := flushMem_frame (cqCtlSM (cqBankSM m9))
  have hJ' : MemFrame cqA cqC (flushMem (cqCtlSM (cqBankSM m9))) mS := hJ
  have nS : ∀ b ∈ solArrs, b ∉ cqA := fun b hb => cq_not_cqA (.inl (cq_not_cdA (.inr (.inr (by
    have := solArrs_arr hb; simp only [SolArr, this.2.2, beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
      decide_eq_true_eq]; omega)))))
  have eS : ∀ b ∈ solArrs, mS.arr64 b = m9.arr64 b := fun b hb => by
    have hc : b ≠ CTL := fun e => by subst e; revert hb; decide
    rw [hJ'.arr b (nS b hb) hc, f2.arr b (by simp) hc,
      fS.arr b (fun hm => by have := csAS_arr hm; have := solArrs_arr hb; omega) hc]
  have eC : ∀ x : Word, x ∉ cqC → x ∉ flushCtl → x ∉ csC → rdW (mS.arr64 CTL) x = rdW (m9.arr64 CTL) x :=
    fun x h1 h2 h3 => by rw [hJ'.ctl x h1, f2.ctl x h2, fS.ctl x h3]
  have hE : erecP (cqSM m9) = erecP m9 := by
    have e1 : ∀ b : TieredArray, b ∉ csAS → b ≠ CTL → (cqSM m9).arr64 b = m9.arr64 b := fun b hb hc => by
      show (flushMem (cqCtlSM (cqBankSM m9))).arr64 b = _
      rw [f2.arr b (by simp) hc, fS.arr b hb hc]
    have e2 : ∀ x : Word, x = 129 ∨ x = 130 → rdW ((cqSM m9).arr64 CTL) x = rdW (m9.arr64 CTL) x :=
      fun x hx => by
        show rdW ((flushMem (cqCtlSM (cqBankSM m9))).arr64 CTL) x = _
        rcases hx with rfl | rfl <;> rw [f2.ctl _ (by decide), fS.ctl _ (by decide)]
    exact erecP_congr' (e1 _ (by decide) (by decide)) (e1 _ (by decide) (by decide)) (e2 _ (.inl rfl)) (e2 _ (.inr rfl))
  refine ⟨fun b hb _ => eS b hb, eC _ (cq_not_cqC (.inl (cq_not_cdC (by decide)))) (by decide) (by decide),
    eC _ (cq_not_cqC (.inl (cq_not_cdC (by decide)))) (by decide) (by decide), hE ▸ hx, ?_⟩
  exact ((hW.frame fS (by decide) (by decide) (by decide) (by decide)).frame f2 (by simp) (by simp)
    (by decide) (by decide)).frame hJ' (cq_not_cqA (.inr (.inl rfl))) (cq_not_cqA (.inr (.inr (.inl rfl))))
    (cq_not_cqC (.inr (by decide))) (cq_not_cqC (.inr (by decide)))

end L.Checker
