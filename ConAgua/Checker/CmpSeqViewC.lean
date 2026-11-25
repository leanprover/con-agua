module

public import ConAgua.Checker.CmpSeqViewS
public import ConAgua.Checker.CmpSeqCheck
public import ConAgua.Checker.CmpSeqW
import ConAgua.Arena.FreezeSpec
import ConAgua.Arena.IWFrame

@[expose] public section

/-!
# The challenge's view back after the solution's jobs (lane compare2, the sJ variant)

Mode `8`'s switch (`cq_bank_s`) exchanges the stream index's rows (`EIX*`, `TIX*`) with the
solution's (`SIX*`, `STX*`) below an extent kept in `CCTL[0‥5]` (`CqX`), and copies `DECL`, `FIRSTS`,
`DLP` to their stashes (`CDECL`, …) up to an extent kept in `CCTL[6‥8]`, then the solution's
prefix over them (`CqSv`). The solution's jobs never store to the stash arrays, either row set nor
`CCTL` (`cq_checkJobs_frame0`), so mode `9`'s `cq_bank_c` (the same exchanges, and each stash
prefix copied back) restores both row sets exactly and the records and the pool in their used words
(`cqC_view`: `CsViewC`), and the jobs kept what `CsKeep` needs (`cqS_keep`).
-/

namespace L.Checker

open L L.Arena L.Front

/-- The stashed arrays: (array, its stash, the extent's `CCTL` slot). -/
def cqPairs : List (ArrId × ArrId × Word) :=
  [(L.Front.DECL, CDECL, 6), (FIRSTS, CFIRSTS, 7), (L.Front.DLP, CDLP, 8)]

/-- The exchanged rows: (the stream index's row, the solution's, the extent's `CCTL` slot). -/
def cqXPairs : List (ArrId × ArrId × Word) :=
  [(EIXA, SIXA, 0), (TIXA, STXA, 1), (EIXS, SIXS, 2), (TIXS, STXS, 3), (EIXN, SIXN, 4), (TIXN, STXN, 5)]

/-- **`A`'s `d` and `s` are `m`'s exchanged below the extent `CCTL[k]` of `A`** (in bounds). -/
structure CqX (m A : Mem) (d s : ArrId) (k : Word) : Prop where
  nd : (rdW (A.arr64 CCTL) k).toNat ≤ (m.arr64 d).size
  ns : (rdW (A.arr64 CCTL) k).toNat ≤ (m.arr64 s).size
  ed : A.arr64 d = (xchgM d s m (rdW (A.arr64 CCTL) k).toNat).arr64 d
  es : A.arr64 s = (xchgM d s m (rdW (A.arr64 CCTL) k).toNat).arr64 s

theorem CqX.congr {m A A' : Mem} {d s : ArrId} {k : Word} (h : CqX m A d s k)
    (ed : A'.arr64 d = A.arr64 d) (es : A'.arr64 s = A.arr64 s)
    (ek : rdW (A'.arr64 CCTL) k = rdW (A.arr64 CCTL) k) : CqX m A' d s k :=
  ⟨by rw [ek]; exact h.nd, by rw [ek]; exact h.ns, by rw [ed, ek]; exact h.ed, by rw [es, ek]; exact h.es⟩

/-- An exchange's rows depend only on its two arrays. -/
theorem xchgM_congr {d s : TieredArray} (hds : d ≠ s) {m M : Mem} (hd : M.arr64 d = m.arr64 d)
    (hs : M.arr64 s = m.arr64 s) (j : Nat) :
    (xchgM d s M j).arr64 d = (xchgM d s m j).arr64 d ∧ (xchgM d s M j).arr64 s = (xchgM d s m j).arr64 s := by
  induction j with
  | zero => exact ⟨hd, hs⟩
  | succ j ih =>
    simp only [xchgM, Mem.arr64_set64_ne _ _ _ _ _ hds, Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hds),
      Mem.arr64_set64_same, ih.1, ih.2, and_self]

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

/-- **A row swap of `cq_bank_s` exchanges its rows** (from a memory whose rows are `m`'s). -/
theorem cqRowStep_x {d s : ArrId} {ca k : Word} {M m : Mem} (hok : CqRowsOK d s ca M)
    (hk : k.toNat < (M.arr64 CCTL).size) (hds : d ≠ s) (hdC : (d : TieredArray) ≠ CCTL)
    (hsC : (s : TieredArray) ≠ CCTL) (ed : M.arr64 d = m.arr64 d) (es : M.arr64 s = m.arr64 s) :
    CqX m (cqRowStep d s ca k M) d s k := by
  obtain ⟨-, h2, h3⟩ := hok
  have hds' : (d : TieredArray) ≠ s := by simpa [TieredArray.t0] using hds
  have eK : rdW ((cqRowStep d s ca k M).arr64 CCTL) k = cqRowsN M ca := by
    simp only [cqRowStep]; exact cq_rdW_hit (by simp only [cqRowsM, xchgM_size]; exact hk)
  have c := xchgM_congr hds' ed es (cqRowsN M ca).toNat
  refine ⟨by rw [eK, ← ed]; exact h2, by rw [eK, ← es]; exact h3, ?_, ?_⟩
  · rw [eK, ← c.1]; simp only [cqRowStep, cqRowsM, Mem.arr64_set64_ne _ _ _ _ _ hdC]
  · rw [eK, ← c.2]; simp only [cqRowStep, cqRowsM, Mem.arr64_set64_ne _ _ _ _ _ hsC]

theorem cqRowStep_cctl {d s : ArrId} {ca k k' : Word} (m : Mem) (hk : k' ≠ k)
    (hd : (CCTL : TieredArray) ≠ d) (hs : (CCTL : TieredArray) ≠ s) :
    rdW ((cqRowStep d s ca k' m).arr64 CCTL) k = rdW (m.arr64 CCTL) k := by
  simp only [cqRowStep, cqRowsM]
  rw [cq_rdW_idx hk, xchgM_ne _ _ _ _ hd hs]

theorem cqRowStep_csize {d s : ArrId} {ca k : Word} (m : Mem) :
    ((cqRowStep d s ca k m).arr64 CCTL).size = (m.arr64 CCTL).size := by
  simp only [cqRowStep, cqRowsM, L.Mem.size64_set64, xchgM_size]

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

/-- **`cq_bank_s`'s row swaps exchange the rows** with the solution's, below their extents. -/
theorem cqBankSM_rows {m9 : Mem} (hR : CqRowsSOK m9) :
    ∀ p ∈ cqXPairs, CqX m9 (cqBankSM m9) p.1 p.2.1 p.2.2 := by
  simp only [CqRowsSOK] at hR
  obtain ⟨o1, o2, o3, o4, o5, o6, h9⟩ := hR
  have hs : ∀ (d s : ArrId) (ca k : Word) (m : Mem), ((cqRowStep d s ca k m).arr64 CCTL).size =
      (m.arr64 CCTL).size := fun _ _ _ _ m => cqRowStep_csize m
  have s1 := cqRowStep_x (m := m9) (k := 0) o1 (by simp only [UInt64.toNat_zero]; omega) (by decide) (by decide) (by decide) rfl rfl
  have s2 := cqRowStep_x (m := m9) (k := 1) o2 (by simp only [hs]; simp; omega) (by decide) (by decide) (by decide) (by cq_eo) (by cq_eo)
  have s3 := cqRowStep_x (m := m9) (k := 2) o3 (by simp only [hs]; simp; omega) (by decide) (by decide) (by decide) (by cq_eo) (by cq_eo)
  have s4 := cqRowStep_x (m := m9) (k := 3) o4 (by simp only [hs]; simp; omega) (by decide) (by decide) (by decide) (by cq_eo) (by cq_eo)
  have s5 := cqRowStep_x (m := m9) (k := 4) o5 (by simp only [hs]; simp; omega) (by decide) (by decide) (by decide) (by cq_eo) (by cq_eo)
  have s6 := cqRowStep_x (m := m9) (k := 5) o6 (by simp only [hs]; simp; omega) (by decide) (by decide) (by decide) (by cq_eo) (by cq_eo)
  clear o1 o2 o3 o4 o5 o6
  have eA : ∀ b : ArrId, (b : TieredArray) ∉ cqTailA → (b : TieredArray) ≠ CTL →
      (cqBankSM m9).arr64 b = (cqRowsS m9).arr64 b :=
    fun b h hc => (cqTailS_frame [] _).arr b h hc
  have eK : ∀ k : Word, k.toNat < 6 → rdW ((cqBankSM m9).arr64 CCTL) k = rdW ((cqRowsS m9).arr64 CCTL) k :=
    fun k hk => cqTailS_cctl_lo _ hk
  intro p hp
  simp only [cqXPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only
  · exact s1.congr (by cq_ec) (by cq_ec) (by cq_ek)
  · exact s2.congr (by cq_ec) (by cq_ec) (by cq_ek)
  · exact s3.congr (by cq_ec) (by cq_ec) (by cq_ek)
  · exact s4.congr (by cq_ec) (by cq_ec) (by cq_ek)
  · exact s5.congr (by cq_ec) (by cq_ec) (by cq_ek)
  · exact s6.congr (by cq_ec) (by cq_ec) (by cq_ek)

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
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  · simp only [cqBankCM]
    refine ⟨by decide, ?_⟩
    try simp (disch := decide) only [arr64_copy64_ne]
    refine ⟨_, ?_, ?_, rfl⟩ <;> simp (disch := decide) only [arr64_copy64_ne, cqRowsC, xchgM_ne]

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

/-- `cq_bank_c` exchanges each row pair once, as one exchange of a memory with its arrays. -/
theorem cqRowsC_pair (M : Mem) {d s : ArrId} {k : Word} (h : (d, s, k) ∈ cqXPairs) :
    ∃ B : Mem, B.arr64 d = M.arr64 d ∧ B.arr64 s = M.arr64 s ∧
      (cqBankCM M).arr64 d = (xchgM d s B (rdW (M.arr64 CCTL) k).toNat).arr64 d ∧
      (cqBankCM M).arr64 s = (xchgM d s B (rdW (M.arr64 CCTL) k).toNat).arr64 s := by
  simp only [cqXPairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ <;>
  · simp only [cqBankCM, cqRowsC]
    simp (disch := decide) only [arr64_copy64_ne, xchgM_ne]
    refine ⟨_, ?_, ?_, rfl, rfl⟩ <;> simp (disch := decide) only [xchgM_ne]

/-- **`cq_bank_c` exchanges the rows back**: from a memory whose rows and extent are mode `8`'s. -/
theorem CqX.back {m A M : Mem} {d s : ArrId} {k : Word} (h : CqX m A d s k) (hp : (d, s, k) ∈ cqXPairs)
    (hds : d ≠ s) (ed : M.arr64 d = A.arr64 d) (es : M.arr64 s = A.arr64 s)
    (ek : rdW (M.arr64 CCTL) k = rdW (A.arr64 CCTL) k) :
    (cqBankCM M).arr64 d = m.arr64 d ∧ (cqBankCM M).arr64 s = m.arr64 s := by
  have hds' : (d : TieredArray) ≠ s := by simpa [TieredArray.t0] using hds
  obtain ⟨B, e1, e2, e3, e4⟩ := cqRowsC_pair M hp
  rw [e3, e4, ek]
  exact xchgM_back hds' m B (UInt64.toNat_lt _) h.nd h.ns (by rw [e1, ed]; exact h.ed) (by rw [e2, es]; exact h.es)

/-- **`cq_bank_c` writes only `csAV`** (`csA` and the solution's rows), no `CTL` word. -/
theorem cqBankCM_frame (C : List Word) (m : Mem) : MemFrame csAV C m (cqBankCM m) := by
  unfold cqBankCM cqRowsC
  exact ((((((((MemFrame.xchgIn (by decide) (by decide) (by decide) (by decide) _ _).trans
    (MemFrame.xchgIn (by decide) (by decide) (by decide) (by decide) _ _)).trans
    (MemFrame.xchgIn (by decide) (by decide) (by decide) (by decide) _ _)).trans
    (MemFrame.xchgIn (by decide) (by decide) (by decide) (by decide) _ _)).trans
    (MemFrame.xchgIn (by decide) (by decide) (by decide) (by decide) _ _)).trans
    (MemFrame.xchgIn (by decide) (by decide) (by decide) (by decide) _ _)).trans
    (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)).trans
    (MemFrame.copyIn (by decide) (by decide) _ _ _ _ _)

/-! ## Header C's view after the solution's jobs -/

theorem cq_stash_not_cqA {b : TieredArray} (h : cqStash b = true) : b ∉ cqA :=
  cq_not_cqA (.inr (.inr (.inr h)))

theorem cq_idx_not_cqA {b : TieredArray} (h : IdxArr b = true) : b ∉ cqA :=
  cq_not_cqA (.inl (cq_not_cdA (.inl h)))

/-- The solution's arrays a bank switch does not exchange (the mates) are not in its write set. -/
theorem sol_not_csAS {b : TieredArray} (hb : b ∈ solArrs) (hn : b ∉ solRowsS) : b ∉ csAS := by
  simp only [solArrs, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd (by decide) hn | decide

/-- The solution's arrays are not in the flag-`0` jobs' write set. -/
theorem sol_not_cqA {b : TieredArray} (hb : b ∈ solArrs) : b ∉ cqA :=
  cq_not_cqA (.inl (cq_not_cdA (.inr (.inr (by
    have := solArrs_arr hb; simp only [SolArr, this.2.2, beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
      decide_eq_true_eq]; omega)))))

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
  -- the exchanged rows back
  have xback : ∀ {d s : ArrId} {k : Word}, (d, s, k) ∈ cqXPairs → d ≠ s → IdxArr d = true →
      (s : TieredArray) ∈ solArrs → (d : TieredArray) ≠ CTL → (s : TieredArray) ≠ CTL →
      (d : TieredArray) ≠ CCTL → (s : TieredArray) ≠ CCTL → k.toNat < 16 →
      (cqCtlCM (cqBankCM mS)).arr64 d = m9.arr64 d ∧ (cqCtlCM (cqBankCM mS)).arr64 s = m9.arr64 s :=
    fun hp hds hd hs hdT hsT hdC hsC hk => by
      rw [cqCtlCM_arr _ _ hdT, cqCtlCM_arr _ _ hsT]
      exact (hr _ hp).back hp hds (eSB _ (cq_idx_not_cqA hd) hdT hdC) (eSB _ (sol_not_cqA hs) hsT hsC) (eK _ hk)
  have bF := (cqBankCM_frame csC mS)
  have hfr : MemFrame csAV csC mS (cqCtlCM (cqBankCM mS)) :=
    bF.trans ((cqCtlCM_frame _).mono (by simp) (fun _ h => h))
  have hrows : ∀ b ∈ solRowsS, (cqCtlCM (cqBankCM mS)).arr64 b = m9.arr64 b := by
    intro b hb
    simp only [solRowsS, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (xback (d := EIXA) (s := SIXA) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2
    · exact (xback (d := EIXS) (s := SIXS) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2
    · exact (xback (d := EIXN) (s := SIXN) (k := 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2
    · exact (xback (d := TIXA) (s := STXA) (k := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2
    · exact (xback (d := TIXS) (s := STXS) (k := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2
    · exact (xback (d := TIXN) (s := STXN) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).2
  refine ⟨hfr, hrows, fun b hb => ?_, fun j hj => ?_,
    fun j hj => ?_, ?_, ?_, fun x hx => ?_⟩
  · obtain ⟨n, hi⟩ := b
    simp only [IdxArr, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hb
    obtain ⟨rfl, h1⟩ := hb
    have : n = 129 ∨ n = 130 ∨ n = 131 ∨ n = 132 ∨ n = 133 ∨ n = 134 ∨ n = 137 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (xback (d := TIXA) (s := STXA) (k := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1
    · exact (xback (d := TIXS) (s := STXS) (k := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1
    · exact (xback (d := TIXN) (s := STXN) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1
    · exact (xback (d := EIXA) (s := SIXA) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1
    · exact (xback (d := EIXS) (s := SIXS) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1
    · exact (xback (d := EIXN) (s := SIXN) (k := 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1
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
  have eS : ∀ b ∈ solArrs, b ∉ solRowsS → mS.arr64 b = m9.arr64 b := fun b hb hn => by
    have hc : b ≠ CTL := fun e => by subst e; revert hb; decide
    rw [hJ'.arr b (sol_not_cqA hb) hc, f2.arr b (by simp) hc, fS.arr b (sol_not_csAS hb hn) hc]
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
  refine ⟨fun b hb hn => eS b hb hn, eC _ (cq_not_cqC (.inl (cq_not_cdC (by decide)))) (by decide) (by decide),
    eC _ (cq_not_cqC (.inl (cq_not_cdC (by decide)))) (by decide) (by decide), hE ▸ hx, ?_⟩
  exact ((hW.frame fS (by decide) (by decide) (by decide) (by decide)).frame f2 (by simp) (by simp)
    (by decide) (by decide)).frame hJ' (cq_not_cqA (.inr (.inl rfl))) (cq_not_cqA (.inr (.inr (.inl rfl))))
    (cq_not_cqC (.inr (by decide))) (cq_not_cqC (.inr (by decide)))

end L.Checker
