import ConAgua.Arena.Scratch
import ConAgua.Arena.Tiers
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The scratch lifecycle refines `enterScratch` / `dropScratch` under `ArenaD`

`scratch_reset(f)` (`Scratch.lean`) writes `CTL` words only: the slot base `CTL[62]`, the flag
`CTL[1]` and the 19 tier-1 counts. Each table's relation moves across it by the store library's
`ConsR.reset` (tier 0 unchanged, tier 1 empty, no slot read), the memos by their frame, the
derived ranges trivially (the scratch tables are empty, the persistent ones did not move). With
the four memo clears this is `enterScratch`; after `flush_caches()` (`CoreR.flush`) it is
`dropScratch`.

* `ArenaD.reset`: `ArenaD m a → ArenaD (resetMem m f) a'` for `a'` with every scratch table
  emptied and every flag `f ≠ 0`.
* `scratchEnter_refines`, `scratchDrop_refines`: the L runs refine the twin's bracket, to
  `CheckR` (`scratchEnter_refinesC`, `scratchDrop_refinesC`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## Reads of `resetMem` -/

theorem zeroCtl_frame : ∀ (xs : List Word) (m : Mem), MemFrame [] xs m (zeroCtl m xs) := by
  intro xs; induction xs with
  | nil => intro m; exact MemFrame.refl _ _ _
  | cons x xs ih =>
    intro m
    exact ((MemFrame.setCtl m x 0).mono (by simp) (by simp)).trans
      ((ih _).mono (by simp) (fun y h => by simp [h]))

theorem zeroCtl_rd (x : Word) :
    ∀ (xs : List Word) (m : Mem), x ∈ xs → rdW ((zeroCtl m xs).arr64 CTL) x = 0 := by
  intro xs; induction xs with
  | nil => intro m h; simp at h
  | cons y xs ih =>
    intro m h
    by_cases hx : x ∈ xs
    · exact ih _ hx
    · have hy : x = y := by simpa [hx] using h
      subst hy
      rw [zeroCtl, (zeroCtl_frame xs _).2.1 x hx, rdW_set64]
      split
      · rfl
      · simp only [rdW]; rw [Array.getElem?_eq_none (by grind)]; rfl

/-- The `CTL` words `scratch_reset` writes. -/
def resetCtl : List Word := SCB :: 1 :: scratchCnts

theorem resetMemA_frame (m : Mem) (f : Word) : MemFrame [] resetCtl m (resetMemA m f) := by
  rw [resetMemA_eq]
  have h1 := MemFrame.setCtl m SCB (rdW (m.arr64 CTL) SCB + 4294967296)
  have h2 := MemFrame.setCtl (m.set64 CTL SCB (rdW (m.arr64 CTL) SCB + 4294967296)) 1 f
  exact ((h1.mono (by simp) (by simp [resetCtl])).trans (h2.mono (by simp) (by simp [resetCtl]))).trans
    ((zeroCtl_frame _ _).mono (by simp) (fun y h => by simp [resetCtl, h]))

theorem resetMemA_base (m : Mem) (f : Word) (h : SCB.toNat < (m.arr64 CTL).size) :
    rdW ((resetMemA m f).arr64 CTL) SCB = rdW (m.arr64 CTL) SCB + 4294967296 := by
  rw [resetMemA_eq, (zeroCtl_frame _ _).2.1 SCB (by simp [scratchCnts, SCB]), rdW_set64, rdW_set64]
  simp [SCB] at h ⊢; omega

theorem resetMemA_flag (m : Mem) (f : Word) (h : SCB.toNat < (m.arr64 CTL).size) :
    rdW ((resetMemA m f).arr64 CTL) 1 = f := by
  rw [resetMemA_eq, (zeroCtl_frame _ _).2.1 1 (by simp [scratchCnts]), rdW_set64, size_set64]
  simp [SCB] at h ⊢; omega

theorem resetMemA_top (m : Mem) (f : Word) : (resetMemA m f).top = m.top := by
  simp only [top_rdW]; exact (resetMemA_frame m f).2.1 0 (by simp [resetCtl, scratchCnts, SCB])

theorem resetMemA_pt0 (m : Mem) (f : Word) : (resetMemA m f).arr64 PT0 = m.arr64 PT0 :=
  (resetMemA_frame m f).1 PT0 (by simp) (by decide)

/-! ## The tops' stores (lane tierpool) -/

theorem resetTop_frame (m : Mem) (f : Word) : MemFrame [PT0] [0] m (resetTopMem m f) := by
  unfold resetTopMem
  have hA : MemFrame [PT0] [0] m (if m.top >>> 40 = 0 then m.set64 PT0 0 m.top else m) := by
    split
    · exact (MemFrame.set64 m PT0 (by decide) 0 m.top).mono (by simp) (by simp)
    · exact MemFrame.refl _ _ _
  exact hA.trans ((MemFrame.setCtl _ 0 _).mono (by simp) (by simp))

theorem resetMem_frame (m : Mem) (f : Word) : MemFrame [PT0] (0 :: resetCtl) m (resetMem m f) :=
  ((resetMemA_frame m f).mono (by simp) (fun x h => List.mem_cons_of_mem _ h)).trans
    ((resetTop_frame _ f).mono (by simp) (fun x h => by simp at h; simp [h]))

theorem resetMem_base (m : Mem) (f : Word) (h : SCB.toNat < (m.arr64 CTL).size) :
    rdW ((resetMem m f).arr64 CTL) SCB = rdW (m.arr64 CTL) SCB + 4294967296 := by
  rw [resetMem, (resetTop_frame _ f).2.1 SCB (by simp [SCB]), resetMemA_base m f h]

theorem resetMem_flag (m : Mem) (f : Word) (h : SCB.toNat < (m.arr64 CTL).size) :
    rdW ((resetMem m f).arr64 CTL) 1 = f := by
  rw [resetMem, (resetTop_frame _ f).2.1 1 (by simp), resetMemA_flag m f h]

/-! ## The wrap (`preMem`) -/

theorem preMem_ctl_size (m : Mem) : ((preMem m).arr64 CTL).size = (m.arr64 CTL).size := by
  unfold preMem; split
  · rw [size_set64, vacL_ctl]
  · rfl

theorem preMem_top (m : Mem) : (preMem m).top = m.top := by
  simp only [top_rdW]; unfold preMem; split
  · rw [rdW_set64, vacL_ctl]; simp [SCB]
  · rfl

theorem preMem_pt0 (m : Mem) : (preMem m).arr64 PT0 = m.arr64 PT0 := by
  unfold preMem; split
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), vacL_pt0]
  · rfl

theorem preMem_eq_of_lt (m : Mem) (h : ¬ SCBLIM ≤ rdW (m.arr64 CTL) SCB) : preMem m = m :=
  ite_eq_right h

theorem slot1Arrs_ge : ∀ b ∈ slot1Arrs, 256 ≤ b := by decide

theorem not_mem_slot1 {b : ArrId} (h : b < 256) : b ∉ slot1Arrs := fun hb => by
  have := slot1Arrs_ge b hb; simp only [ArrId] at *; omega

theorem GFr.memFrame {sa : ArrId} {m m' : Mem} (h : GFr sa m m') (hc : sa ≠ CTL) :
    MemFrame [sa] [] m m' :=
  ⟨fun b hb _ => h.1 b (by simpa using hb), fun x _ => by rw [h.1 CTL (Ne.symm hc)],
    h.2.1, h.2.2⟩

theorem vacL_frame : ∀ (l : List ArrId) (m : Mem), MemFrame (l.map (tierA · 1)) [] m (vacL l m)
  | [], m => MemFrame.refl _ _ m
  | a :: as, m => by
    simp only [vacL]
    have h1 : MemFrame [tierA a 1] [] m (vacW a m) :=
      GFr.memFrame (kzeroW_fr (tierA a 1) _ _ m) (by rw [tierA_one]; simp only [CTL, ArrId]; omega)
    exact (h1.mono (by simp) (by simp)).trans
      ((vacL_frame as _).mono (fun b hb => List.mem_cons_of_mem _ hb) (by simp))

/-- **The wrap's frame**: the scratch tables' slot arrays and the slot base. -/
theorem preMem_frame (m : Mem) : MemFrame slot1Arrs [SCB] m (preMem m) := by
  unfold preMem; split
  · exact ((vacL_frame scrSlots m).mono (by simp [slot1Arrs_eq]) (by simp)).trans
      ((MemFrame.setCtl _ SCB 0).mono (by simp) (by simp))
  · exact MemFrame.refl _ _ _

/-- `scratch_reset(f)`'s frame: the wrap's arrays, the saved top, the reset's `CTL` words. -/
theorem resetMemP_frame (m : Mem) (f : Word) :
    MemFrame scrArrs (0 :: resetCtl) m (resetMem (preMem m) f) :=
  ((preMem_frame m).mono (fun b h => List.mem_cons_of_mem _ h) (by simp [resetCtl])).trans
    ((resetMem_frame (preMem m) f).mono (by simp) (fun x h => h))

/-- **The wrap zeroes a scratch table**: the `8 ⌊n / 4⌋` words of tier 1's table of slot array
`sa` (from word `2 + o`), and nothing else of its array. -/
theorem vacL_rd (sa : ArrId) (hsa : sa < 256) : ∀ (l : List ArrId) (m : Mem), l.Nodup →
    (∀ a ∈ l, a < 256) → sa ∈ l →
    (koW sa m 1 + 2).toNat + 8 * (knW sa m 1 >>> 2).toNat < 2 ^ 64 →
    ((vacL l m).arr64 (tierA sa 1)).size = (m.arr64 (tierA sa 1)).size ∧
    ∀ y, rdW ((vacL l m).arr64 (tierA sa 1)) y =
      if (koW sa m 1 + 2).toNat ≤ y.toNat ∧ y.toNat < (koW sa m 1 + 2).toNat + 8 * (knW sa m 1 >>> 2).toNat
      then 0 else rdW (m.arr64 (tierA sa 1)) y
  | [], _, _, _, h, _ => absurd h (by simp)
  | a :: as, m, hnd, hlt, hin, hb => by
    simp only [vacL]
    obtain ⟨hna, hnd'⟩ := List.nodup_cons.mp hnd
    by_cases ha : a = sa
    · subst ha
      have e : (vacL as (vacW a m)).arr64 (tierA a 1) = (vacW a m).arr64 (tierA a 1) :=
        vacL_arr as _ _ (fun b hb' => tierA_ne hsa (hlt b (List.mem_cons_of_mem _ hb'))
          (fun h => hna (h ▸ hb')) 1 1)
      rw [e]
      exact ⟨(kzeroW_fr _ _ _ m).2.1 _, kzeroW_rd _ _ _ m hb⟩
    · have hin' : sa ∈ as := by simpa [Ne.symm ha] using hin
      have e : (vacW a m).arr64 (tierA sa 1) = m.arr64 (tierA sa 1) :=
        vacW_arr a m _ (tierA_ne hsa (hlt a List.mem_cons_self) (Ne.symm ha) 1 1)
      have ek : koW sa (vacW a m) 1 = koW sa m 1 := by simp only [koW, e]
      have en : knW sa (vacW a m) 1 = knW sa m 1 := by simp only [knW, e]
      have := vacL_rd sa hsa as (vacW a m) hnd' (fun b hb' => hlt b (List.mem_cons_of_mem _ hb'))
        hin' (by rw [ek, en]; exact hb)
      rw [ek, en, e] at this
      exact this

/-- After the tops' stores: the top and the saved tier-0 top. -/
theorem resetTop_tops (m : Mem) (f : Word) (hc : 0 < (m.arr64 CTL).size)
    (hpt : m.top >>> 40 = 0 → 0 < (m.arr64 PT0).size) :
    (resetTopMem m f).ptop0 = (if m.top >>> 40 = 0 then m.top else m.ptop0) ∧
    (resetTopMem m f).top = (if f ≠ 0 then 1099511627776 else
      (if m.top >>> 40 = 0 then m.top else m.ptop0)) := by
  unfold resetTopMem
  by_cases ht : m.top >>> 40 = 0
  · have h1 := hpt ht
    have hp : (m.set64 PT0 0 m.top).ptop0 = m.top := Mem.ptop0_set64 _ _ h1
    have hc' : 0 < ((m.set64 PT0 0 m.top).arr64 CTL).size := by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact hc
    simp only [ht, ↓reduceIte]
    constructor
    · rw [Mem.ptop0_set64_ne _ CTL _ _ (by decide), hp]
    · rw [Mem.top_set64 _ _ hc', hp]
  · simp only [ht, ↓reduceIte]
    exact ⟨Mem.ptop0_set64_ne _ CTL _ _ (by decide), Mem.top_set64 _ _ hc⟩

theorem tier0_iff (x : Word) : x >>> 40 = 0 ↔ x.toNat < 2 ^ 40 := by
  constructor
  · intro h; have := congrArg UInt64.toNat h; rw [tag_tier_toNat] at this; simp at this; omega
  · intro h; exact UInt64.toNat_inj.mp (by rw [tag_tier_toNat]; simp; omega)

/-- **A persistent node's slice across the tops' stores**: in tier 0 below the saved tier-0 top
(`RSlice`'s tier condition), it stays in use. -/
theorem rslice_resetTop (m : Mem) (f : Word) (hp : PoolOK m)
    (hpt : m.top >>> 40 = 0 → 0 < (m.arr64 PT0).size) {o l : Word} (h : RSlice m 0 o l) :
    RSlice (resetTopMem m f) 0 o l := by
  obtain ⟨hp0, hpt0⟩ := resetTop_tops m f hp.2.1 hpt
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have ho := h3 rfl
  have hsz := hp.small.1
  have h5 := hp.2.2.2.2.1
  have e40 : (1099511627776 : Word).toNat = 2 ^ 40 := rfl
  have htl : m.top >>> 40 = 0 ↔ m.top.toNat < 2 ^ 40 := tier0_iff _
  refine ⟨⟨?_, ?_⟩, fun _ => ho⟩
  · rw [hpt0]
    by_cases ht : m.top >>> 40 = 0
    · have := htl.mp ht
      by_cases hf : f ≠ 0
      · rw [ite_eq_left hf, e40]; omega
      · rw [ite_eq_right hf, ite_eq_left ht]; omega
    · have : ¬ m.top.toNat < 2 ^ 40 := fun e => ht (htl.mpr e)
      by_cases hf : f ≠ 0
      · rw [ite_eq_left hf, e40]; omega
      · rw [ite_eq_right hf, ite_eq_right ht]; omega
  · rw [hp0]; right; right
    by_cases ht : m.top >>> 40 = 0
    · rw [ite_eq_left ht]; omega
    · have : ¬ m.top.toNat < 2 ^ 40 := fun e => ht (htl.mpr e)
      rw [ite_eq_right ht]; omega

/-- An array of id below 256 other than `PT0` and `CTL` stays across the tops' stores. -/
theorem resetTop_arr (m : Mem) (f : Word) {a : ArrId} (ha : a < 256) (h1 : PT0 ≠ a) (h2 : CTL ≠ a)
    (t : Word) : (resetTopMem m f).arr64 (tierA a t) = m.arr64 (tierA a t) :=
  (resetTop_frame m f).1 _ (by simp only [List.mem_singleton]; exact tierA_ne_small _ _ ha (by decide) h1 t)
    (tierA_ne_small _ _ ha (by decide) h2 t)

theorem resetTop_vpool (m : Mem) (f : Word) : vpool (resetTopMem m f) = vpool m :=
  vpool_congr ((resetTop_frame m f).1 POOL (by decide) (by decide))
    ((resetTop_frame m f).1 POOL1 (by decide) (by decide))

theorem resetTop_tpool (m : Mem) (f : Word) : tpool (resetTopMem m f) = tpool m :=
  tpool_congr ((resetTop_frame m f).1 POOL (by decide) (by decide))
    ((resetTop_frame m f).1 POOL1 (by decide) (by decide))

section pooltabs
variable (m : Mem) (f : Word) (hp : PoolOK m) (hpt : m.top >>> 40 = 0 → 0 < (m.arr64 PT0).size)

include hp hpt in
theorem recRel_resetTop (i : Word) (k : LitNode) (h : RecRel m 0 i k) :
    RecRel (resetTopMem m f) 0 i k := by
  have htf : ∀ j, tfld (resetTopMem m f) LIT 0 i j = tfld m LIT 0 i j := fun j => by
    simp only [tfld]; rw [resetTop_arr m f (by decide) (by decide) (by decide)]
  have hv := resetTop_vpool m f
  have hq := resetTop_tpool m f
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k
  · simp only [RecRel, NatRec, htf, hv, hq] at h ⊢
    exact ⟨h.1, rslice_resetTop m f hp hpt h.2.1, h.2.2⟩
  · simp only [RecRel, StrRec, htf, hv, hq] at h ⊢
    exact ⟨h.1, rslice_resetTop m f hp hpt h.2.1, h.2.2⟩

include hp hpt in
theorem nsRecRel_resetTop (i : Word) (k : StrNode) (h : NsRecRel m 0 i k) :
    NsRecRel (resetTopMem m f) 0 i k := by
  have htf : ∀ j, tfld (resetTopMem m f) NSTR 0 i j = tfld m NSTR 0 i j := fun j => by
    simp only [tfld]; rw [resetTop_arr m f (by decide) (by decide) (by decide)]
  have hv := resetTop_vpool m f
  have hq := resetTop_tpool m f
  simp only [NsRecRel, htf, hv, hq] at h ⊢
  exact ⟨h.1, rslice_resetTop m f hp hpt h.2.1, h.2.2⟩

include hp hpt in
theorem lsRecRel_resetTop (i : Word) (k : ListNode) (h : LsRecRel m 0 i k) :
    LsRecRel (resetTopMem m f) 0 i k := by
  have htf : ∀ j, tfld (resetTopMem m f) LVLS 0 i j = tfld m LVLS 0 i j := fun j => by
    simp only [tfld]; rw [resetTop_arr m f (by decide) (by decide) (by decide)]
  have hv := resetTop_vpool m f
  have hq := resetTop_tpool m f
  simp only [LsRecRel, htf, hv, hq] at h ⊢
  exact ⟨rslice_resetTop m f hp hpt h.1, h.2⟩

end pooltabs

/-- The pool invariant across the tops' stores. -/
theorem poolOK_resetTop (m : Mem) (f : Word) (hp : PoolOK m)
    (hpt : m.top >>> 40 = 0 → 0 < (m.arr64 PT0).size) : PoolOK (resetTopMem m f) := by
  obtain ⟨hp0, hpt0⟩ := resetTop_tops m f hp.2.1 hpt
  have hf := resetTop_frame m f
  have hs := hp.small
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hp
  have hpc : pcap (resetTopMem m f) = pcap m := pcap_congr (hf.2.2.1 _) (hf.2.2.1 _)
  have e0 : (resetTopMem m f).arr64 POOL = m.arr64 POOL := hf.1 POOL (by simp) (by decide)
  have hpcv : pcap m = 2 ^ 41 - 1 := pcap_of_small m hs
  have hsz0 := hs.1
  have e40 : (1099511627776 : Word).toNat = 2 ^ 40 := rfl
  -- the new top is a tier-0 address in tier 0's array, or the scratch tier's base
  have hq : (if m.top >>> 40 = 0 then m.top else m.ptop0).toNat ≤ (m.arr64 POOL).size := by
    by_cases ht : m.top >>> 40 = 0
    · have htl := (tier0_iff _).mp ht
      have hidx : (m.top &&& 1099511627775) = m.top :=
        UInt64.toNat_inj.mp (by rw [tag_idx_toNat]; omega)
      rw [ht, tierA_pool0, hidx] at a6
      simp only [ht, ↓reduceIte]; exact a6
    · simp only [ht, ↓reduceIte]
      rcases a5 with a5 | a5
      · exact absurd ((tier0_iff _).mpr a5) ht
      · exact a5
  refine ⟨by rw [hf.2.2.2]; exact a1, by rw [hf.2.2.1]; exact a2, by rw [hpc]; exact a3, ?_, ?_, ?_⟩
  · rw [hpt0, hpc, hpcv]
    by_cases hf' : f ≠ 0
    · rw [ite_eq_left hf', e40]; omega
    · rw [ite_eq_right hf']; omega
  · rw [hp0, e0]; exact .inr hq
  · rw [hpt0]
    by_cases hf' : f ≠ 0
    · rw [ite_eq_left hf', show ((1099511627776 : Word) &&& 1099511627775) = 0 from by decide]
      simp
    · rw [ite_eq_right hf']
      generalize (if m.top >>> 40 = 0 then m.top else m.ptop0) = T at hq ⊢
      have hTl : T.toNat < 2 ^ 40 := by omega
      have hidx : (T &&& 1099511627775) = T := UInt64.toNat_inj.mp (by rw [tag_idx_toNat]; omega)
      rw [hidx, (tier0_iff T).mpr hTl, tierA_pool0, e0]; exact hq

/-! ## One table -/

section table
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]

/-- **A table across `scratch_reset(f)`'s wrap and counts**: tier 0 as before (its records, the
arrays `A₀` and words `C₀` they refer to are not written), tier 1 empty (its slots read free:
against the raised base, or zeroed by the wrap), the flag `f ≠ 0`. -/
theorem consR_resetP {C : ConsSch} {R : Mem → Word → Word → α → Prop} {A₀ : List ArrId}
    {C₀ : List Word} (hW : C.WF) (hl : RLocal C.sch R C.hsM A₀ C₀)
    (hA₀ : ∀ b ∈ A₀, b ∉ slot1Arrs ∧ b ≠ CTL) (hC₀ : ∀ x ∈ C₀, x ∉ resetCtl)
    (hca : C.ca ∉ scratchCnts ∧ C.ca + 1 ∈ scratchCnts) (hsa : C.sa ∈ scrSlots)
    (hra : tier1 C.ra ∉ slot1Arrs)
    (m : Mem) (f : Word) (hlo : (rdW ((preMem m).arr64 CTL) SCB).toNat < 2 ^ 62)
    (h62 : SCB.toNat < ((preMem m).arr64 CTL).size) {on : Bool} {tbP tbS : Tbl α (Idx k) δ}
    (hR : ConsR C R m on tbP tbS) :
    ConsR C R (resetMemA (preMem m) f) (f != 0) tbP (Tbl.empty : Tbl α (Idx k) δ) := by
  have hS := hW.sch
  have hsc := hS.scb
  simp only [ConsSch.sch] at hsc
  have hfA := resetMemA_frame (preMem m) f
  have hF : MemFrame slot1Arrs resetCtl m (resetMemA (preMem m) f) :=
    ((preMem_frame m).mono (by simp) (by simp [resetCtl])).trans (hfA.mono (by simp) (by simp))
  have hsalt : C.sa < 256 := hS.sa_lt
  have hralt : C.ra < 256 := hS.ra_lt
  have hra' : ∀ t, (resetMemA (preMem m) f).arr64 (tierA C.ra t) = m.arr64 (tierA C.ra t) :=
    fun t => hF.tier C.ra (not_mem_slot1 hralt) hra hS.ra_ctl t
  have e1 : (resetMemA (preMem m) f).arr64 (tierA C.sa 1) = (preMem m).arr64 (tierA C.sa 1) :=
    hfA.1 _ (by simp) (hS.sa_ctl' 1)
  have hb : rdW ((resetMemA (preMem m) f).arr64 CTL) SCB = rdW ((preMem m).arr64 CTL) SCB + 4294967296 :=
    resetMemA_base (preMem m) f h62
  -- the tier-1 slot array: its size, count and offset words, and its slots free
  have hT1 : ((resetMemA (preMem m) f).arr64 (tierA C.sa 1)).size = (m.arr64 (tierA C.sa 1)).size ∧
      rdW ((resetMemA (preMem m) f).arr64 (tierA C.sa 1)) 0 = rdW (m.arr64 (tierA C.sa 1)) 0 ∧
      rdW ((resetMemA (preMem m) f).arr64 (tierA C.sa 1)) 1 = rdW (m.arr64 (tierA C.sa 1)) 1 ∧
      ∀ j : Word, j < nSl C.sch m 1 → slotW C.sch (resetMemA (preMem m) f) 1 j = 0 := by
    by_cases hw : SCBLIM ≤ rdW (m.arr64 CTL) SCB
    · have e2 : (preMem m).arr64 (tierA C.sa 1) = (vacL scrSlots m).arr64 (tierA C.sa 1) := by
        rw [preMem, ite_eq_left hw, Mem.arr64_set64_ne _ _ _ _ _ (show tierA C.sa 1 ≠ CTL from hS.sa_ctl' 1)]
      obtain ⟨l1, l2, l3, l4⟩ := hR.lay1
      have hn4 : 8 * (knW C.sa m 1 >>> 2).toNat = 2 * (knW C.sa m 1).toNat := by
        rw [UInt64.toNat_shiftRight]; simp; omega
      have ho2 : (koW C.sa m 1 + 2).toNat = (koW C.sa m 1).toNat + 2 := by
        rw [UInt64.toNat_add]; simp; omega
      obtain ⟨hsz', hrd⟩ := vacL_rd C.sa hsalt scrSlots m (by decide) (by decide) hsa
        (by rw [hn4, ho2]; omega)
      rw [hn4, ho2] at hrd
      refine ⟨by rw [e1, e2, hsz'], by rw [e1, e2, hrd]; simp, by rw [e1, e2, hrd]; simp, ?_⟩
      refine hR.free_zero (by rw [e1, e2, hrd]; simp) (fun y h1 h2 => ?_)
      simp only [krW] at h1 h2
      rw [e1, e2, hrd, ite_eq_left ⟨by omega, by omega⟩]
    · have ep := preMem_eq_of_lt m hw
      have e1' : (resetMemA (preMem m) f).arr64 (tierA C.sa 1) = m.arr64 (tierA C.sa 1) := by
        rw [e1, ep]
      have hb' : rdW ((resetMemA (preMem m) f).arr64 CTL) SCB = rdW (m.arr64 CTL) SCB + 4294967296 := by
        rw [hb, ep]
      refine ⟨by rw [e1'], by rw [e1'], by rw [e1'], ?_⟩
      exact hR.free_raise e1' (by simpa only [ep] using hlo) hb'
  obtain ⟨t1, t2, t3, t4⟩ := hT1
  have hloc := hl m (resetMemA (preMem m) f) hra' (fun b hb' => hF.1 b (hA₀ b hb').1 (hA₀ b hb').2)
    (fun x hx => hF.2.1 x (hC₀ x hx))
  refine hR.resetG hra' (hF.1 _ (not_mem_slot1 hsalt) hS.sa_ctl) t1 t2 t3 t4 (hF.2.2.1 CTL) ?_ ?_ ?_
    (by rw [resetMemA_flag (preMem m) f h62]) (hloc.1 0) (hloc.2 0)
  · simp only [cntC, UInt64.add_zero]
    exact hF.2.1 _ (by simp only [resetCtl, List.mem_cons, not_or]; exact ⟨hsc.1, hsc.2.2.1, hca.1⟩)
  · simp only [cntC]
    rw [resetMemA_eq]; exact zeroCtl_rd _ _ _ hca.2
  · rw [hb]; rw [UInt64.toNat_add]; simp; omega

/-- **A table across the tops' stores**, its scratch tier empty: its persistent nodes as given. -/
theorem consR_resetTop {C : ConsSch} {R : Mem → Word → Word → α → Prop} (m : Mem) (f : Word)
    (hra : ∀ t, tierA C.ra t ≠ PT0 ∧ tierA C.ra t ≠ CTL) (hsa : ∀ t, tierA C.sa t ≠ PT0 ∧ tierA C.sa t ≠ CTL)
    (hca : C.ca ≠ 0 ∧ C.ca + 1 ≠ 0) {on : Bool} {tbP : Tbl α (Idx k) δ}
    (hR0 : ∀ i a, R m 0 i a → R (resetTopMem m f) 0 i a)
    (hh : ∀ t i, C.hsM (resetTopMem m f) t i = C.hsM m t i)
    (h : ConsR C R m on tbP (Tbl.empty : Tbl α (Idx k) δ)) :
    ConsR C R (resetTopMem m f) on tbP (Tbl.empty : Tbl α (Idx k) δ) := by
  have hf := resetTop_frame m f
  refine h.mono' (fun t => hf.1 _ (by simp [(hra t).1]) (hra t).2)
    (fun t => hf.1 _ (by simp [(hsa t).1]) (hsa t).2) (hf.2.2.1 CTL) (fun x hx => hf.2.1 x ?_)
    (fun i a _ hr => hR0 i a hr) (fun i a hi _ => by simp [Tbl.empty] at hi) hh
  rcases hx with rfl | rfl | rfl | rfl
  · simp
  · simp [SCB]
  · simp [hca.1]
  · simp [hca.2]

end table

/-! ## The whole arena -/

/-- `a` with every scratch table emptied and every scratch flag `on`: the store part of
`enterScratch` (`on = true`) and of `dropScratch` (`on = false`). -/
def EStore.reset (st : EStore) (on : Bool) : EStore :=
  if on then st.enableScratch else st.dropScratch

/-- Phase A: **`scratch_reset(f)`'s counts keep `ArenaD`**, with every scratch table emptied and every flag
`f ≠ 0`; the memos stay. -/
theorem ArenaD.resetA (m : Mem) (a : AState) (hD : ArenaD m a) (f : Word)
    (hlo : (rdW ((preMem m).arr64 CTL) SCB).toNat < 2 ^ 62)
    (h62 : SCB.toNat < ((preMem m).arr64 CTL).size) :
    ArenaD (resetMemA (preMem m) f) { a with store := EStore.reset a.store (f != 0) } := by
  obtain ⟨hR, hDer⟩ := hD
  have hf : MemFrame slot1Arrs resetCtl m (resetMemA (preMem m) f) :=
    ((preMem_frame m).mono (by simp) (by simp [resetCtl])).trans
      ((resetMemA_frame (preMem m) f).mono (by simp) (by simp))
  have e : ∀ {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] {A₀ : List ArrId} {C₀ : List Word}
      (C : ConsSch) (R : Mem → Word → Word → α → Prop), C.WF →
      RLocal C.sch R C.hsM A₀ C₀ → (∀ b ∈ A₀, b ∉ slot1Arrs ∧ b ≠ CTL) → (∀ x ∈ C₀, x ∉ resetCtl) →
      C.ca ∉ scratchCnts ∧ C.ca + 1 ∈ scratchCnts → C.sa ∈ scrSlots → tier1 C.ra ∉ slot1Arrs →
      ∀ (on' : Bool) (tbP tbS : Tbl α (Idx k) δ),
      ConsR C R m on' tbP tbS → ConsR C R (resetMemA (preMem m) f) (f != 0) tbP Tbl.empty :=
    fun C R hW hl hA₀ hC₀ hca hsa hra on' tbP tbS h =>
      consR_resetP hW hl hA₀ hC₀ hca hsa hra m f hlo h62 h
  have hpool : PoolOK (resetMemA (preMem m) f) :=
    hR.lit.1.frame (hf.1 POOL (by decide) (by decide)) (hf.1 POOL1 (by decide) (by decide))
      (hf.1 PT0 (by decide) (by decide)) (hf.2.2.1 CTL) (by rw [resetMemA_top, preMem_top])
      hf.2.2.2
  have hM : MemosR (resetMemA (preMem m) f) a.memos :=
    hR.memos.frame (by decide) (by simp [resetCtl, scratchCnts, memoCtl, SCB]) hf
  have hcP : ∀ {α : Type} A, A ≠ CTL → A ∉ slot1Arrs → tier1 A ∉ slot1Arrs →
      cP (α := α) A (resetMemA (preMem m) f) = cP A m := fun A hA h1 h2 => by
    funext t i x d; simp only [cP, hf.tier A h1 h2 hA]
  have hE : ∀ {α : Type} [BEq α] [Hashable α] (P : Nat → α → UInt64 → Prop),
      DerT (Tbl.empty : Tbl α EIdx UInt64) P := fun P => ⟨rfl, fun i x h => by simp [Tbl.empty] at h⟩
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hDer
  cases hb : (f != 0) <;> rw [hb] at e <;>
  exact ⟨⟨⟨hpool, e litCS RecRel litCS_wf litLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, litCS, litCSk]) (by simp only [litCS, litCSk]; decide) (by simp only [litCS, litCSk]; decide) _ _ _ hR.lit.2⟩,
    e appCS ARecRel appCS_wf appLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, appCS]) (by simp only [appCS]; decide) (by simp only [appCS]; decide) _ _ _ hR.app,
    e sortCS SoRecRel sortCS_wf sortLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, sortCS]) (by simp only [sortCS]; decide) (by simp only [sortCS]; decide) _ _ _ hR.sort,
    e constCS CeRecRel constCS_wf constLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, constCS]) (by simp only [constCS]; decide) (by simp only [constCS]; decide) _ _ _ hR.const,
    e letCS LeRecRel letCS_wf letELocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, letCS]) (by simp only [letCS]; decide) (by simp only [letCS]; decide) _ _ _ hR.letE,
    e bvarCS BRecRel bvarCS_wf bvarLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, bvarCS]) (by simp only [bvarCS]; decide) (by simp only [bvarCS]; decide) _ _ _ hR.bvar,
    e fvarCS FVRecRel fvarCS_wf fvarLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, fvarCS]) (by simp only [fvarCS]; decide) (by simp only [fvarCS]; decide) _ _ _ hR.fvar,
    e lamCS LaRecRel lamCS_wf lamLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, lamCS]) (by simp only [lamCS]; decide) (by simp only [lamCS]; decide) _ _ _ hR.lam,
    e forallCS FaRecRel forallCS_wf forallELocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, forallCS]) (by simp only [forallCS]; decide) (by simp only [forallCS]; decide) _ _ _ hR.forallE,
    e projCS PJRecRel projCS_wf projLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, projCS]) (by simp only [projCS]; decide) (by simp only [projCS]; decide) _ _ _ hR.proj,
    e zeroCS ZRecRel zeroCS_wf zeroLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, zeroCS]) (by simp only [zeroCS]; decide) (by simp only [zeroCS]; decide) _ _ _ hR.zero,
    e succCS SRecRel succCS_wf succLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, succCS]) (by simp only [succCS]; decide) (by simp only [succCS]; decide) _ _ _ hR.succ,
    e maxCS MRecRel maxCS_wf maxLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, maxCS]) (by simp only [maxCS]; decide) (by simp only [maxCS]; decide) _ _ _ hR.max,
    e imaxCS IRecRel imaxCS_wf imaxLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, imaxCS]) (by simp only [imaxCS]; decide) (by simp only [imaxCS]; decide) _ _ _ hR.imax,
    e paramCS PRecRel paramCS_wf paramLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, paramCS]) (by simp only [paramCS]; decide) (by simp only [paramCS]; decide) _ _ _ hR.param,
    e lsCS LsRecRel lsCS_wf lsLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, lsCS]) (by simp only [lsCS]; decide) (by simp only [lsCS]; decide) _ _ _ hR.ls,
    e nanonCS NaRecRel nanonCS_wf nanonLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, nanonCS]) (by simp only [nanonCS]; decide) (by simp only [nanonCS]; decide) _ _ _ hR.nanon,
    e nstrCS NsRecRel nstrCS_wf nstrLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, nstrCS]) (by simp only [nstrCS]; decide) (by simp only [nstrCS]; decide) _ _ _ hR.nstr,
    e nnumCS NnRecRel nnumCS_wf nnumLocal (by decide) (by simp [resetCtl, scratchCnts, SCB]) (by simp [scratchCnts, nnumCS]) (by simp only [nnumCS]; decide) (by simp only [nnumCS]; decide) _ _ _ hR.nnum,
    hM, ⟨hR.zeroHp.1, constT_empty _⟩, ⟨hR.paramHp.1, constT_empty _⟩,
    ⟨colT_mono hR.succHp.1 (fun _ _ => by rw [hf.tier SHP (by decide) (by decide) (by decide)]), colT_empty _ _ _ _⟩,
    ⟨colT_mono hR.maxHp.1 (fun _ _ => by rw [hf.tier MHP (by decide) (by decide) (by decide)]), colT_empty _ _ _ _⟩,
    ⟨colT_mono hR.imaxHp.1 (fun _ _ => by rw [hf.tier IHP (by decide) (by decide) (by decide)]), colT_empty _ _ _ _⟩,
    ⟨colT_mono hR.lsHp.1 (fun _ _ => by rw [hf.tier LSHP (by decide) (by decide) (by decide)]), colT_empty _ _ _ _⟩,
    ⟨colT_mono hR.sortLp.1 (fun _ _ => by rw [hf.tier SOLP (by decide) (by decide) (by decide)]), colT_empty _ _ _ _⟩,
    ⟨colT_mono hR.constLp.1 (fun _ _ => by rw [hf.tier CLP (by decide) (by decide) (by decide)]), colT_empty _ _ _ _⟩,
    ⟨colT_mono hR.fvarLp.1 (fun _ _ => by rw [hf.tier FVLP (by decide) (by decide) (by decide)]), colT_empty _ _ _ _⟩⟩,
    ⟨⟨d1.1, hE _⟩, ⟨d2.1, hE _⟩, ⟨d3.1, hE _⟩, ⟨d4.1, hE _⟩, ⟨d5.1, hE _⟩,
      ⟨by rw [hcP ADER (by decide) (by decide) (by decide)]; exact d6.1, hE _⟩,
      ⟨by rw [hcP LADER (by decide) (by decide) (by decide)]; exact d7.1, hE _⟩,
      ⟨by rw [hcP FADER (by decide) (by decide) (by decide)]; exact d8.1, hE _⟩,
      ⟨by rw [hcP LEDER (by decide) (by decide) (by decide)]; exact d9.1, hE _⟩,
      ⟨by rw [hcP PJDER (by decide) (by decide) (by decide)]; exact d10.1, hE _⟩⟩⟩


/-- Phase B: **the tops' stores keep `ArenaD`**, the scratch tables empty: the pool tables' persistent
records lie in tier 0 below the saved tier-0 top, every other table and the derived ranges by the
frame. -/
theorem ArenaD.resetTop (m : Mem) (a : AState) (f : Word) (on : Bool)
    (hD : ArenaD m { a with store := EStore.reset a.store on })
    (hpt : m.top >>> 40 = 0 → 0 < (m.arr64 PT0).size) :
    ArenaD (resetTopMem m f) { a with store := EStore.reset a.store on } := by
  have hf := resetTop_frame m f
  have hpt' := hpt
  obtain ⟨hR, hDer⟩ := hD
  have hp := hR.lit.1
  refine ⟨?_, DerR.frameM [PT0] [0] m _ hf (by intro b hb; simp at hb; subst hb; decide) _ hDer⟩
  have hra : ∀ {a : ArrId}, a < 256 → PT0 ≠ a → CTL ≠ a → ∀ t, tierA a t ≠ PT0 ∧ tierA a t ≠ CTL :=
    fun ha h1 h2 t => ⟨tierA_ne_small _ _ ha (by decide) h1 t, tierA_ne_small _ _ ha (by decide) h2 t⟩
  have hpo := poolOK_resetTop m f hp hpt'
  cases on <;>
  arena_build hR, hf with
    first
    | exact ⟨hpo, consR_resetTop (C := litCS) (R := RecRel) m f (hra (by decide) (by decide) (by decide))
        (hra (by decide) (by decide) (by decide)) (by decide) (recRel_resetTop m f hp hpt')
        (fun t i => by simp only [litCS, litCSk, litH, resetTop_arr m f (a := REC) (by decide) (by decide) (by decide)]) hR.lit.2⟩
    | exact consR_resetTop (C := lsCS) (R := LsRecRel) m f (hra (by decide) (by decide) (by decide))
        (hra (by decide) (by decide) (by decide)) (by decide) (lsRecRel_resetTop m f hp hpt')
        (fun t i => by simp only [lsCS, lshash, resetTop_arr m f (a := LSREC) (by decide) (by decide) (by decide)]) hR.ls
    | exact consR_resetTop (C := nstrCS) (R := NsRecRel) m f (hra (by decide) (by decide) (by decide))
        (hra (by decide) (by decide) (by decide)) (by decide) (nsRecRel_resetTop m f hp hpt')
        (fun t i => by simp only [nstrCS, nshash, resetTop_arr m f (a := NSREC) (by decide) (by decide) (by decide)]) hR.nstr

/-- **`scratch_reset(f)` keeps `ArenaD`**, with every scratch table emptied and every flag
`f ≠ 0`; the memos stay. -/
@[refines_part ConRon.Arena.EStore.enableScratch "ArenaD"]
theorem ArenaD.reset (m : Mem) (a : AState) (hD : ArenaD m a) (f : Word)
    (hlo : (rdW ((preMem m).arr64 CTL) SCB).toNat < 2 ^ 62)
    (h62 : SCB.toNat < ((preMem m).arr64 CTL).size)
    (hpt : (resetMemA (preMem m) f).top >>> 40 = 0 ∨ f = 0 →
      0 < ((resetMemA (preMem m) f).arr64 PT0).size) :
    ArenaD (resetMem (preMem m) f) { a with store := EStore.reset a.store (f != 0) } :=
  ArenaD.resetTop _ a f _ (ArenaD.resetA m a hD f hlo h62) (fun h => hpt (Or.inl h))

/-! ## The twin's bracket -/



theorem enterScratch_run (a : AState) :
    enterScratch.run a = .ok ((), { a with store := EStore.reset a.store true, memos := Memos.empty }) :=
  rfl

theorem dropScratch_run (a : AState) :
    dropScratch.run a =
      .ok ((), { a with caches := Caches.empty, store := EStore.reset a.store false }) :=
  rfl

/-- The `CTL` words `flush_caches()` writes. -/
def flushCtl : List Word :=
  [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113,
   116, 117, 118, 119]

theorem flushMem_frame (m : Mem) : MemFrame [] flushCtl m (flushMem m) :=
  (clearsL_frame coreSchs m).mono (by simp) (fun x h => by
    simp only [coreSchs, List.flatMap_cons, List.flatMap_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at h
    simp only [flushCtl, List.mem_cons, List.not_mem_nil, or_false]
    rcases h with ((rfl | rfl) | (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | (rfl | rfl) |
      (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | rfl | rfl) <;> decide)

theorem flushCtl_ge : ∀ x ∈ flushCtl, 64 ≤ x.toNat := by simp [flushCtl]

theorem flushCtl_lt : ∀ x ∈ flushCtl, x.toNat < 128 := by simp [flushCtl]

/-- The four memo clears of `scratch_enter`, as one frame of the memo tier's `CTL` words. -/
theorem clears_frame (m : Mem) :
    MemFrame [] memoCtl m (mclearG frSch (mclearG imSch (mclearG lfSch (mclearG bmSch m)))) := by
  have h := fun (S : MemoSch) (m : Mem) (hS : S.cs ∈ memoCtl ∧ S.cs + 1 ∈ memoCtl) =>
    (mclearG_frame S m).mono (A' := []) (C' := memoCtl) (by simp)
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                      rcases hx with rfl | rfl <;> simp [hS])
  exact (((h bmSch _ (by simp [memoCtl])).trans (h lfSch _ (by simp [memoCtl]))).trans
    (h imSch _ (by simp [memoCtl]))).trans (h frSch _ (by simp [memoCtl]))

/-- **`scratch_enter`'s memory after `ArenaD` is `enterScratch`'s state.** -/
theorem ArenaD.enter (m : Mem) (a : AState) (hD : ArenaD m a)
    (hlo : (rdW ((preMem m).arr64 CTL) SCB).toNat < 2 ^ 62)
    (h62 : SCB.toNat < ((preMem m).arr64 CTL).size)
    (c1 : rdW ((resetMem (preMem m) 1).arr64 CTL) bmSch.cs + 2 ≠ 0)
    (c2 : rdW ((mclearG bmSch (resetMem (preMem m) 1)).arr64 CTL) lfSch.cs + 2 ≠ 0)
    (c3 : rdW ((mclearG lfSch (mclearG bmSch (resetMem (preMem m) 1))).arr64 CTL) imSch.cs + 2 ≠ 0)
    (c4 : rdW ((mclearG imSch (mclearG lfSch (mclearG bmSch (resetMem (preMem m) 1)))).arr64 CTL)
      frSch.cs + 2 ≠ 0)
    (hpt : (resetMemA (preMem m) 1).top >>> 40 = 0 ∨ (1 : Word) = 0 →
      0 < ((resetMemA (preMem m) 1).arr64 PT0).size) :
    ArenaD (enterMem m) { a with store := EStore.reset a.store true, memos := Memos.empty } := by
  obtain ⟨hR, hDer⟩ := ArenaD.reset m a hD 1 hlo h62 hpt
  simp only [show ((1 : Word) != 0) = true from rfl] at hR hDer
  have hf := clears_frame (resetMem (preMem m) 1)
  generalize hm1 : resetMem (preMem m) 1 = m1 at *
  -- each memo: cleared at its step, framed across the later clears
  have hb := memoRG_clear bmSch bmSch_wf bmKey _ m1 _ hR.memos.bvar c1
  have fb := fun (S : MemoSch) (m₀ : Mem) (h : MemoRG bmSch bmKey (·.toNat) m₀ ∅)
      (hc1 : bmSch.cs ≠ S.cs) (hc2 : bmSch.cs ≠ S.cs + 1) =>
    memoRG_frame bmSch bmSch_wf bmKey _ [] [S.cs, S.cs + 1] (by simp) (by simp [hc1, hc2]) _ _
      (mclearG_frame S m₀) _ h
  have hl1 := memoRG_frame lfSch lfSch_wf lfKey _ [] [bmSch.cs, bmSch.cs + 1] (by simp) (by simp)
    _ _ (mclearG_frame bmSch m1) _ hR.memos.lift
  have hl := memoRG_clear lfSch lfSch_wf lfKey _ _ _ hl1 c2
  have hi1 := memoRG_frame imSch imSch_wf lfKey _ [] [lfSch.cs, lfSch.cs + 1] (by simp) (by simp)
    _ _ (mclearG_frame lfSch _) _ (memoRG_frame imSch imSch_wf lfKey _ [] [bmSch.cs, bmSch.cs + 1]
      (by simp) (by simp) _ _ (mclearG_frame bmSch m1) _ hR.memos.inst1)
  have hi := memoRG_clear imSch imSch_wf lfKey _ _ _ hi1 c3
  have hr1 := memoRG_frame frSch frSch_wf bmKey _ [] [imSch.cs, imSch.cs + 1] (by simp) (by simp)
    _ _ (mclearG_frame imSch _) _ (memoRG_frame frSch frSch_wf bmKey _ [] [lfSch.cs, lfSch.cs + 1]
      (by simp) (by simp) _ _ (mclearG_frame lfSch _) _ (memoRG_frame frSch frSch_wf bmKey _ []
        [bmSch.cs, bmSch.cs + 1] (by simp) (by simp) _ _ (mclearG_frame bmSch m1) _ hR.memos.fvar))
  have hr := memoRG_clear frSch frSch_wf bmKey _ _ _ hr1 c4
  have hM : MemosR (mclearG frSch (mclearG imSch (mclearG lfSch (mclearG bmSch m1)))) Memos.empty :=
    ⟨fb frSch _ (fb imSch _ (fb lfSch _ hb (by decide) (by decide)) (by decide) (by decide))
        (by decide) (by decide),
     memoRG_frame lfSch lfSch_wf lfKey _ [] [frSch.cs, frSch.cs + 1] (by simp) (by simp) _ _
       (mclearG_frame frSch _) _ (memoRG_frame lfSch lfSch_wf lfKey _ [] [imSch.cs, imSch.cs + 1]
         (by simp) (by simp) _ _ (mclearG_frame imSch _) _ hl),
     memoRG_frame imSch imSch_wf lfKey _ [] [frSch.cs, frSch.cs + 1] (by simp) (by simp) _ _
       (mclearG_frame frSch _) _ hi,
     hr⟩
  have e : enterMem m = mclearG frSch (mclearG imSch (mclearG lfSch (mclearG bmSch m1))) := by
    rw [← hm1]; rfl
  rw [e]
  exact ⟨hR.with_memos hf (by simp) (by simp [memoCtl, storeCtl]) hM,
    DerR.of_store _ _ _ (DerR.frameM _ _ _ _ hf (by simp) _ hDer) rfl⟩

/-- **`scratch_drop()` refines `dropScratch`** under `ArenaD`. -/
theorem scratchDrop_refines (p : Prog) (hp : p.lookup "scratch_drop" = some scratchDrop)
    (hr : p.lookup "scratch_reset" = some scratchReset) (hfl : FlushProg p)
    (a₀ : AState) (n : Nat) (s₀ : St) (hD : ArenaD s₀.mem a₀) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scratch_drop" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok dropScratch a₀ ∧ ArenaD s'.mem (AM.st dropScratch a₀); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, -, hlo, h62, hpt, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchDrop_spec p hp hr hfl n s₀)
  subst hs
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ (dropScratch_run a₀)
  refine ⟨hloc, hok, ?_⟩
  rw [hst, hm]
  have hD' : ArenaD (flushMem s.mem) a₀ :=
    ⟨ArenaR.frame_ext [] _ (by simp) flushCtl_ge _ _ (flushMem_frame _) _ hD.1,
      DerR.frameM [] _ _ _ (flushMem_frame _) (by simp) _ hD.2⟩
  obtain ⟨hR, hDer⟩ := ArenaD.reset _ _ hD' 0 hlo h62 hpt
  simp only [show ((0 : Word) != 0) = false from rfl] at hR hDer
  exact ⟨by cases hR; constructor <;> assumption, DerR.of_store _ _ _ hDer rfl⟩

/-- **`scratch_reset(0)` refines `EStore.dropScratch`**: `ArenaD` represents the whole store (every
table's two tiers, the flag, the derived ranges), and after the call it represents the store with
the scratch tables emptied and the flag off; the memos stay. It aborts only when the slot epoch
`CTL[62]` reaches `2^62`: then it vacates the scratch tables and restarts the base (con-ron's
`clear` at `EPOCH_MAX`), so it never aborts. -/
@[refines ConRon.Arena.EStore.dropScratch]
theorem scratchReset_dropScratch (p : Prog) (hr : p.lookup "scratch_reset" = some scratchReset)
    (a : AState) (n : Nat) (s₀ : St) (hD : ArenaD s₀.mem a) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scratch_reset" [0]
    ⦃fun _ s' => LocEq s' s₀ ∧ ArenaD s'.mem { a with store := a.store.dropScratch }; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hlo, h62, hpt, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchReset_spec p hr n s₀ 0)
  subst hs
  refine ⟨hloc, ?_⟩
  rw [hm]
  exact ArenaD.reset _ _ hD 0 hlo h62 hpt

/-! ## The mode across the bracket -/

theorem flag_rdW (m : Mem) : m.flag = rdW (m.arr64 CTL) 1 := rfl

/-- **`scratch_reset(f)` establishes `ModeOK`**: with the flag on it holds by the flag; with it off
the top is the saved tier-0 top, below `2^40`. -/
theorem modeOK_resetMem (m : Mem) (f : Word) (hp : PoolOK m) (h62 : SCB.toNat < (m.arr64 CTL).size)
    (hpt : (resetMemA m f).top >>> 40 = 0 ∨ f = 0 → 0 < ((resetMemA m f).arr64 PT0).size) :
    ModeOK (resetMem m f) := by
  by_cases hf : f = 0
  · right
    have hfA := resetMemA_frame m f
    have hpA : PoolOK (resetMemA m f) :=
      hp.frame (hfA.1 POOL (by simp) (by decide)) (hfA.1 POOL1 (by simp) (by decide))
        (hfA.1 PT0 (by simp) (by decide)) (hfA.2.2.1 CTL) (resetMemA_top m f) hfA.2.2.2
    obtain ⟨-, ht⟩ := resetTop_tops (resetMemA m f) f hpA.2.1 (fun h => hpt (Or.inl h))
    show (resetTopMem (resetMemA m f) f).top.toNat < 2 ^ 40
    rw [ht, ite_eq_right (by simpa using hf)]
    by_cases h0 : (resetMemA m f).top >>> 40 = 0
    · rw [ite_eq_left h0]; exact (tier0_iff _).mp h0
    · rw [ite_eq_right h0]
      have := hpA.2.2.2.2.1
      have := hpA.small.1
      have := mt (tier0_iff _).mpr h0
      omega
  · left
    rw [flag_rdW, resetMem_flag m f h62]; exact hf

/-- **`scratch_enter` establishes `ModeOK`** (by the flag). -/
theorem modeOK_enterMem (m : Mem) (h62 : SCB.toNat < ((preMem m).arr64 CTL).size) :
    ModeOK (enterMem m) := by
  left
  have hf := clears_frame (resetMem (preMem m) 1)
  have e : enterMem m =
      mclearG frSch (mclearG imSch (mclearG lfSch (mclearG bmSch (resetMem (preMem m) 1)))) := rfl
  rw [e, flag_rdW, hf.2.1 1 (by simp [memoCtl]), resetMem_flag (preMem m) 1 h62]; decide

/-! ## The other tiers -/

theorem enterMem_frame (m : Mem) : MemFrame scrArrs ((0 :: resetCtl) ++ memoCtl) m (enterMem m) :=
  ((resetMemP_frame m 1).mono (by simp) (fun x h => List.mem_append_left _ h)).trans
    ((clears_frame _).mono (by simp) (fun x h => List.mem_append_right _ h))

theorem resetCtl_lt : ∀ x ∈ (0 :: resetCtl) ++ memoCtl, x.toNat < 64 := by
  simp [resetCtl, scratchCnts, memoCtl, SCB]

theorem scrArrs_low : ∀ b ∈ scrArrs, b < 64 ∨ (256 ≤ b ∧ b < 320) := by decide

/-- The bracket keeps the pins and the environment: it writes arrays below 64 and `CTL` words
below 128 only. -/
theorem CheckR.of_bracket {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {vis : Word} {fe : IFEnv} {A : List ArrId} {C : List Word} (hR : CheckR dn m a vis fe)
    (hD : ArenaD m' a') (hc : CoreR m' a'.caches) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320))
    (hC : ∀ x ∈ C, x.toNat < 128) (hp : a'.pins = a.pins) (hmode : ModeOK m') :
    CheckR dn m' a' vis fe :=
  ⟨hD, hc, by rw [hp]; exact hR.pins.frame (.of_low hA (by decide) (by decide)) hf,
    hR.env.frame (.of_low hA (by decide) (by decide)) (.of_lt hC (by decide)) hf (.of_lowT hA), hmode⟩

/-- `scratch_enter()` refines `enterScratch` under `CheckR`. -/
@[refines ConRon.Arena.enterScratch]
theorem scratchEnter_refinesC (p : Prog) (hp : p.lookup "scratch_enter" = some scratchEnter)
    (hr : p.lookup "scratch_reset" = some scratchReset)
    (hb : p.lookup "bm_clear" = some (memoClearG bmSch))
    (hl : p.lookup "lf_clear" = some (memoClearG lfSch))
    (hi : p.lookup "if_clear" = some (memoClearG imSch))
    (hf : p.lookup "fm_clear" = some (memoClearG frSch))
    (a₀ : AState) (n : Nat) (s₀ : St) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (hC : CheckR dn s₀.mem a₀ vis fe) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scratch_enter" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok enterScratch a₀ ∧
      CheckR dn s'.mem (AM.st enterScratch a₀) vis fe; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hlo, h62, c1, c2, c3, c4, hpt, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchEnter_spec p hp hr hb hl hi hf n s₀)
  subst hs
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ (enterScratch_run a₀)
  refine ⟨hloc, hok, ?_⟩
  rw [hst, hm]
  exact hC.of_bracket (C := (0 :: resetCtl) ++ memoCtl)
    (ArenaD.enter _ _ hC.arena hlo h62 c1 c2 c3 c4 hpt)
    (hC.core.frame (.of_low scrArrs_low (by decide) (by decide))
      (.of_lt (fun x h => resetCtl_lt x h) (by decide)) (enterMem_frame _))
    (enterMem_frame _) scrArrs_low (fun x h => Nat.lt_trans (resetCtl_lt x h) (by decide)) rfl
    (modeOK_enterMem _ h62)

/-- `scratch_drop()` refines `dropScratch` under `CheckR`. -/
@[refines ConRon.Arena.dropScratch]
theorem scratchDrop_refinesC (p : Prog) (hp : p.lookup "scratch_drop" = some scratchDrop)
    (hr : p.lookup "scratch_reset" = some scratchReset) (hfl : FlushProg p)
    (a₀ : AState) (n : Nat) (s₀ : St) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (hC : CheckR dn s₀.mem a₀ vis fe) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scratch_drop" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok dropScratch a₀ ∧
      CheckR dn s'.mem (AM.st dropScratch a₀) vis fe; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, -, hD⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchDrop_refines p hp hr hfl a₀ n s₀ hC.arena)
  obtain ⟨-, hfok, -, h62, hpt, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchDrop_spec p hp hr hfl n s₀)
  subst hs
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ (dropScratch_run a₀)
  have hrf : MemFrame scrArrs (0 :: resetCtl) (flushMem s.mem) (resetMem (preMem (flushMem s.mem)) 0) :=
    resetMemP_frame _ 0
  have hcore : CoreR (resetMem (preMem (flushMem s.mem)) 0) Caches.empty :=
    (hC.core.flush hfok).frame (.of_low scrArrs_low (by decide) (by decide))
      (.of_lt (fun x h => resetCtl_lt x (List.mem_append_left _ h)) (by decide)) hrf
  refine ⟨hloc, hok, hC.of_bracket (A := scrArrs) (C := flushCtl ++ (0 :: resetCtl)) hD
    (by rw [hst, hm]; exact hcore) ?_ scrArrs_low ?_ (by rw [hst]) ?_⟩
  · rw [hm]
    exact ((flushMem_frame _).mono (by simp) (fun x h => List.mem_append_left _ h)).trans
      (hrf.mono (by simp) (fun x h => List.mem_append_right _ h))
  · intro x h
    rcases List.mem_append.mp h with h | h
    · exact flushCtl_lt x h
    · exact Nat.lt_trans (resetCtl_lt x (List.mem_append_left _ h)) (by decide)
  · rw [hm]
    have hff : MemFrame slot1Arrs (flushCtl ++ [SCB]) s.mem (preMem (flushMem s.mem)) :=
      ((flushMem_frame s.mem).mono (by simp) (fun x h => List.mem_append_left _ h)).trans
        ((preMem_frame _).mono (fun b h => h) (fun x h => List.mem_append_right _ h))
    have hp := hC.arena.1.lit.1
    refine modeOK_resetMem _ 0 (hp.frame (hff.1 POOL (by decide) (by decide))
      (hff.1 POOL1 (by decide) (by decide)) (hff.1 PT0 (by decide) (by decide)) (hff.2.2.1 CTL)
      (hff.top_eq (by decide)) hff.2.2.2) h62 hpt

/- Two scratch rounds: the base rises by `2^32` each time, the flag follows. -/
#guard
  let m : Mem := { words := #[#[], Array.replicate 120 0] ++ Array.replicate 60 #[] ++ #[#[0]] ++
    Array.replicate 47 #[] }
  match run scratchProg 100 "scratch_enter" [] m with
  | .ok (_, m1) => match run scratchProg 100 "scratch_drop" [] m1 with
    | .ok (_, m2) => (m1.arr64 1)[62]! == 4294967296 && (m1.arr64 1)[1]! == 1 &&
        (m2.arr64 1)[62]! == 8589934592 && (m2.arr64 1)[1]! == 0
    | .error _ => false
  | .error _ => false

/- The wrap: from a base just below the limit, `scratch_enter` raises it to `2^62` (no slot
written), and the next reset (`scratch_drop`) vacates every scratch table (a grown one in tier 1
of `ASLOT`: 16 slots at offset 2) and restarts the base: `2^32`. -/
#guard
  let ctl : Array Word := (Array.replicate 120 0).set! 62 (4611686018427387904 - 4294967296)
  let slot (a : Nat) : Array Word :=
    if a = 261 then #[8, 2, 5, 5] ++ Array.replicate 32 7
    else if a ∈ slot1Arrs then #[0, 0] ++ Array.replicate 16 7 else #[]
  let m : Mem := { words := (List.range 320).toArray.map fun a =>
    if a = 1 then ctl else if a = 62 then #[0] else slot a }
  match run scratchProg 100 "scratch_enter" [] m with
  | .ok (_, m1) => match run scratchProg 100 "scratch_drop" [] m1 with
    | .ok (_, m2) => (m1.arr64 1)[62]! == 4611686018427387904 && (m1.arr64 259)[2]! == 7 &&
        (m2.arr64 1)[62]! == 4294967296 && (m2.arr64 1)[1]! == 0 &&
        m2.arr64 261 == #[8, 2, 5, 5] ++ Array.replicate 32 0 &&
        slot1Arrs.all (fun a => a == 261 || m2.arr64 a == #[0, 0] ++ Array.replicate 16 0)
    | .error _ => false
  | .error _ => false

end L.Arena
