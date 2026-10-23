import ConAgua.Arena.IndRealLvlZ
import ConAgua.Arena.TwinStep
import ConAgua.Arena.InferFieldSort
import ConAgua.Arena.CapsNeverZeroCore

/-!
# `lv_zero_caps` under `StageT` (lane `indproofs4`, helper `lvl`)

`lzcF_simT`: a run of `lv_zero_caps(l)` (its model `lzcF`, `IndRealLvlZ.lean`) from a memory in
`StageT`, the handle `l` reading back to `lv`, is the twin's `readLevelM l` (which returns `lv` and
caches it), `StageT` after, the pools grown, and the three result words the zero-ness of `lv`
(`decZC`). Through lane `levels`' `zeroW_ok` (`lv_zero` is `zeronessOf` on the heap), the heap
frame (`StageT.of_heap`) and the record-pool writer `StageR.erec`.

The names of the `ifAllZero` datum decode by the **name store** (`denoteN`), not by the record
decoder `dn` of the stage relation: `dn` is only known to agree with the store where it is defined
(`StoreDen.dnN`), so `decZC dn` follows for a `dn` that decodes every stored name (`decZC_mono`).
This is why the stub contract `IndStubs.lvZeroCaps_spec` (`StageR` only, `decZC dn`) is not proved
from it: `StageR` lacks the twin's invariants (`TwinOK`: the readback cache holds readbacks) and
the handle's readback, and the decoder is `dn`.
-/

set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **A name slice on an array, copied word by word, decodes as a handle slice** reading back to
the names (the converse of `nmsR_of_hslice`). -/
theorem hslice_of_nmsR (ns : NStore) {m : Mem} {A : ArrId} {o k : Word} {ps : List ConLeche.Name}
    (h : NmsR (nameN ns) m A o k ps) :
    o.toNat + k.toNat < 2 ^ 64 → ∀ (arr : Array Word) (q : Nat),
      (∀ j < k.toNat, arr[q + j]? = some ((m.arr64 A)[o.toNat + j]?.getD 0)) →
      ∃ lps : List NIdx, hslice? arr q k.toNat = some lps ∧ lps.mapM (denoteN ns) = some ps := by
  induction h with
  | nil => intro _ arr q _; exact ⟨[], by simp [hslice?], rfl⟩
  | @cons o k x xs hk hx _ ih =>
    intro hb arr q hget
    have hk1 : 1 ≤ k.toNat := by
      rcases Nat.eq_zero_or_pos k.toNat with e | e
      · exact absurd (UInt64.toNat_inj.mp (by simpa using e)) hk
      · exact e
    have ho : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hk' : (k - 1).toNat = k.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    obtain ⟨lps, hs, hm⟩ := ih (by rw [ho, hk']; omega) arr (q + 1) (fun j hj => by
      have := hget (j + 1) (by rw [hk'] at hj; omega)
      rw [ho, show q + 1 + j = q + (j + 1) by omega, show o.toNat + 1 + j = o.toNat + (j + 1) by omega]
      exact this)
    have h0 := hget 0 (by omega)
    simp only [Nat.add_zero] at h0
    obtain ⟨hw, hd⟩ := hx
    refine ⟨decI (rdW (m.arr64 A) o) :: lps, ?_, ?_⟩
    · rw [show k.toNat = (k - 1).toNat + 1 by rw [hk']; omega, hslice?_succ]
      simp only [hd?, h0, Option.bind_eq_bind, Option.bind_some]
      rw [if_pos (by simpa [rdW] using hw)]
      simp [hs]; rfl
    · simp only [List.mapM_cons, hd, hm]; rfl

/-- `decZC` for a decoder that decodes at least what another one does. -/
theorem decZC_mono {dz dz' : NIdx → Option ConLeche.Name} {m : Mem} {r : List Word}
    {lv : ConLeche.Level} (h : decZC dz m r lv) (hd : ∀ k y, dz k = some y → dz' k = some y) :
    decZC dz' m r lv := by
  intro a ha
  have := h a ha
  revert this
  unfold pwWords
  split
  · exact id
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq]
    rintro ⟨ns, hns, ys, hys, e⟩
    exact ⟨ns, hns, ys, mapM_of_sub hd ns ys hys, e⟩
  · exact id

/-- `erec_alloc(k)` unpacked: the old top, the new top `k` further within the array. -/
theorem lzc_alloc {m m2 : Mem} {k q : Word} (h : erAllocW m k = some (q, m2))
    (hEs : (m.arr64 EREC).size < 2 ^ 64) (hc : 129 < (m.arr64 CTL).size) :
    q = rdW (m.arr64 CTL) 129 ∧ m2 = erAllocMem m k ∧ q.toNat + k.toNat ≤ (m.arr64 EREC).size ∧
      erTop m2 = q.toNat + k.toNat := by
  simp only [erAllocW] at h
  by_cases h1 : m.len64 EREC < rdW (m.arr64 CTL) 129
  · simp [h1] at h
  by_cases h2 : m.len64 EREC - rdW (m.arr64 CTL) 129 < k
  · simp [h1, h2] at h
  simp only [h1, h2, if_false, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hlen : (m.len64 EREC).toNat = (m.arr64 EREC).size := by simp [Mem.len64]; omega
  have hq : (rdW (m.arr64 CTL) 129).toNat ≤ (m.arr64 EREC).size := by
    have : ¬ (m.len64 EREC).toNat < (rdW (m.arr64 CTL) 129).toNat := h1
    omega
  have hroom : (rdW (m.arr64 CTL) 129).toNat + k.toNat ≤ (m.arr64 EREC).size := by
    have : ¬ (m.len64 EREC - rdW (m.arr64 CTL) 129).toNat < k.toNat := h2
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)] at this
    omega
  refine ⟨rfl, rfl, hroom, ?_⟩
  have h129 : (129 : Word).toNat < (m.arr64 CTL).size := by simp; omega
  simp only [erTop, erAllocMem, rdW_set64]
  rw [if_pos ⟨trivial, trivial, h129⟩, UInt64.toNat_add]
  omega

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`lv_zero_caps` under `StageT`** (replaces `IndStubs.lvZeroCaps_spec` for a caller carrying
`StageT` and the handle's readback): the twin's `readLevelM l`, `StageT` after, the pools grown,
the zero-ness of the level as three words, its names decoded by the name store. -/
theorem lzcF_simT {m : Mem} {a : AState} (hT : StageT dn vis fe m a) (l : Word) (hl : H l)
    (lv : ConLeche.Level) (hd : denoteL a.store.ls (decI l) = some lv) :
    Sim (lzcF m [l]) (readLevelM (decI l)) a
      (fun r x m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧
        decZC (denoteN a.store.lss.ls.ns) m' r x) := by
  intro r m' h
  obtain ⟨k, hw⟩ := lzcF_lzcW h
  obtain ⟨M, hC⟩ := hT.core
  have hlv := denoteL_lvR hC.arena.1 (decI l) lv hd
  rw [word_decI _ _ hl |>.mpr rfl] at hlv
  obtain ⟨X, hrun, hcX⟩ := readLevelM_run' a (decI l) lv hd hC.readL
  have hC' := hC.withReadLC X hcX
  refine ⟨lv, _, hrun, ?_⟩
  rcases k with _ | n
  · simp [lzcW] at hw
  simp only [lzcW] at hw
  cases hz : zeroW n m l with
  | none => rw [hz] at hw; simp [lzcK1] at hw
  | some zm =>
  obtain ⟨z, m1⟩ := zm
  rw [hz] at hw
  obtain ⟨he, hZ⟩ := zeroW_ok n m m1 l z lv hlv hz
  have hfH : ∀ v, MemFrame [LH] [192] m (m1.set64 CTL 192 v) := fun v =>
    he.memFrame.trans ((MemFrame.setCtl m1 192 v).mono (by simp) (by simp))
  rcases hZ with ⟨rfl, hpw⟩ | ⟨rfl, ps, hpw, hnm⟩
  · -- `never`: the heap top restored
    simp only [lzcK1, ne_eq, show (1 : Word) ≠ 0 by decide, not_false_eq_true, ↓reduceIte,
      Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨hT', hg⟩ := StageT.of_heap hT hC' (hfH _)
    refine ⟨hT', hg, fun arr _ => ?_⟩
    rw [hpw]; rfl
  -- `ifAllZero ps`: the names copied to a fresh record slice
  simp only [lzcK1, ne_eq, not_true_eq_false, ↓reduceIte] at hw
  obtain ⟨hT1, hg1⟩ := StageT.of_heap hT hC' he.memFrame
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hT1.stage.2
  generalize hkk : htop m1 - htop m = kk at hw hnm
  have htop1 := he.top
  have hkkN : kk.toNat = (htop m1).toNat - (htop m).toNat := by
    rw [← hkk, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
  cases ha : erAllocW m1 kk with
  | none => rw [ha] at hw; simp [lzcK2] at hw
  | some qm =>
  obtain ⟨q, m2⟩ := qm
  rw [ha] at hw
  obtain ⟨hq, rfl, hroom, htop2⟩ := lzc_alloc ha hEs (by omega)
  simp only [lzcK2] at hw
  cases hcp : lheCopyW n (erAllocMem m1 kk) q (htop m) kk with
  | none => rw [hcp] at hw; simp [lzcK3] at hw
  | some m3 =>
  rw [hcp] at hw
  simp only [lzcK3, Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hE2 : (erAllocMem m1 kk).arr64 EREC = m1.arr64 EREC := by
    simp only [erAllocMem]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hL2 : (erAllocMem m1 kk).arr64 LH = m1.arr64 LH := by
    simp only [erAllocMem]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  obtain ⟨hA3, hS3, hW3, hG3⟩ := lheCopyW_get n _ _ _ _ _ hcp
    (by have := (htop m1).toNat_lt; omega) (by rw [hE2]; exact hroom) (by rw [hE2]; exact hEs)
  rw [hE2, hL2] at hG3
  rw [hE2] at hS3
  have hq1 : q.toNat = erTop m1 := by rw [hq]; rfl
  -- the record pool writer: `m1 → m3`
  have hf3 : MemFrame [EREC] [129] m1 m3 := by
    refine ⟨fun b hb hcb => ?_, fun x hx => ?_, fun b => ?_, ?_⟩
    · rw [hA3 b (by simpa using hb), erAllocMem, Mem.arr64_set64_ne _ _ _ _ _ hcb]
    · rw [hA3 CTL (by decide)]; simp only [erAllocMem, rdW_set64]
      have hx' : ¬ (x = 129) := by simpa using hx
      simp [show (129 : Word) ≠ x from fun e => hx' e.symm]
    · by_cases hb : b = EREC
      · subst hb; exact hS3
      · rw [hA3 b hb]; simp only [erAllocMem]
        by_cases hbc : b = CTL
        · subst hbc; exact size_set64 _ _ _ _ _
        · rw [Mem.arr64_set64_ne _ _ _ _ _ hbc]
    · rw [hW3]; exact Mem.words_size_set64 _ _ _ _
  have htop3 : erTop m3 = q.toNat + kk.toNat := by
    rw [← htop2]; simp only [erTop]; rw [hA3 CTL (by decide)]
  obtain ⟨hS3', hg3⟩ := StageR.erec hT1.stage hf3
    (fun i hi => by rw [hG3, if_neg (by omega)])
    (by rw [htop3]; omega) (by rw [htop3, hS3]; omega)
  have hT3 : StageT dn vis fe m3 _ := ⟨hS3', hT1.twin.frame hf3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide), by rw [pinW_frame hf3 (by decide)]; exact hT1.flag⟩
  obtain ⟨M3, hC3⟩ := hT3.core
  obtain ⟨hT4, hg4⟩ := StageT.of_heap hT3 hC3
    ((MemFrame.setCtl m3 192 (htop m)).mono (by simp) (by simp))
  refine ⟨hT4, hg1.trans (hg3.trans hg4), fun arr hagr => ?_⟩
  have hE4 : (m3.set64 CTL 192 (htop m)).arr64 EREC = m3.arr64 EREC :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have htop4 : erTop (m3.set64 CTL 192 (htop m)) = erTop m3 := by
    simp only [erTop]; rw [(MemFrame.setCtl m3 192 (htop m)).2.1 129 (by decide)]
  obtain ⟨lps, hs, hm⟩ := hslice_of_nmsR _ hnm (by have := (htop m1).toNat_lt; omega) arr q.toNat
    (fun j hj => by
      rw [hagr _ (by rw [htop4, htop3]; omega)]
      simp only [erA, hE4]
      rw [hG3, if_pos (by omega)]
      congr 3; omega)
  rw [hpw]
  simp only [pwWords, List.headD_cons, List.tail_cons, show (1 : Word).toNat = 1 from rfl, hs,
    Option.bind_eq_bind, Option.bind_some, hm]
  rfl

/-- **`lv_zero_caps` under `StageT`, as a call** in a program with `lzcP`. -/
theorem lzc_simT {p : Prog} (hp : LzcF p) (n : Nat) {m : Mem} {a : AState}
    (hT : StageT dn vis fe m a) (l : Word) (hl : H l) (lv : ConLeche.Level)
    (hd : denoteL a.store.ls (decI l) = some lv) :
    Sim (callW p n "lv_zero_caps" [l] m) (readLevelM (decI l)) a
      (fun r x m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧
        decZC (denoteN a.store.lss.ls.ns) m' r x) := by
  intro r m' e
  obtain ⟨s', rfl, -, hw⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (lzcF_spec p hp n _ [l]) e
  exact lzcF_simT hT l hl lv hd r _ hw

end

end L.Ind
