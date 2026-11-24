module

public import ConAgua.Checker.C1Switch
public import ConAgua.Checker.C1Keep
import ConAgua.Arena.FreezeFreshBase
import ConAgua.Arena.FreezeTruncBase
import ConAgua.Arena.IndexRel

@[expose] public section

/-!
# Back to the challenge's view after the solution's calls, on one region (lane compare2, H7)

The solution's jobs' witness `X` (from `freshMem mS`, header S's fresh memory, with `c1Q`) patched
with `freshMem m9`'s stream index (`c1Patch`) holds the challenge's jobs' memory half
(`c1_back`, through `JobM.csBack`), given both views of the same extents.
-/

namespace L.Checker

open L L.Arena ConRon.Arena ConRon.Bridge

section views
variable {mS m9 : Mem} (hfr : MemFrame csA csC m9 mS)
  (hext : ∀ i < frozen.length, fzExt mS (fzAt i) = fzExt m9 (fzAt i))
include hfr hext

/-- Off the stream index's arrays, both views cut alike. -/
theorem c1_trunc_eq {b : TieredArray} (hb : b ∉ csA) (hc : b ≠ CTL) :
    (truncFrozen mS).arr64 b = (truncFrozen m9).arr64 b := by
  by_cases hs : b ∈ fzSrcs
  · rw [← frozen_srcs, List.mem_map] at hs
    obtain ⟨e, he, rfl⟩ := hs
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hi' : i + 1 < frozen.length := by simp at hi; omega
    have hz : (frozen.drop 1)[i] = (frozen[i + 1].1, fzAt (i + 1)) := by
      simp only [List.getElem_drop, fzAt, List.getElem?_eq_getElem hi', Option.map_some, Option.getD_some]
      simp only [Nat.add_comm 1 i]
    rw [hz] at he ⊢
    rw [truncFrozen_mem mS he, truncFrozen_mem m9 he, hext _ hi', hfr.arr _ (by rwa [hz] at hb) (by rwa [hz] at hc)]
  · rw [truncFrozen_other _ _ hs, truncFrozen_other _ _ hs, hfr.arr _ hb hc]

/-- The cut stream index's arrays have the same sizes under both views. -/
theorem c1_trunc_size (b : TieredArray) :
    ((truncFrozen mS).arr64 b).size = ((truncFrozen m9).arr64 b).size := by
  by_cases hs : b ∈ fzSrcs
  · rw [← frozen_srcs, List.mem_map] at hs
    obtain ⟨e, he, rfl⟩ := hs
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hi' : i + 1 < frozen.length := by simp at hi; omega
    have hz : (frozen.drop 1)[i] = (frozen[i + 1].1, fzAt (i + 1)) := by
      simp only [List.getElem_drop, fzAt, List.getElem?_eq_getElem hi', Option.map_some, Option.getD_some]
      simp only [Nat.add_comm 1 i]
    rw [hz] at he ⊢
    rw [truncFrozen_mem mS he, truncFrozen_mem m9 he, hext _ hi', size_extract0, size_extract0, hfr.size]
  · rw [truncFrozen_other _ _ hs, truncFrozen_other _ _ hs, hfr.size]

/-- **The fresh memories of both views are a frame of the stream index's arrays and words.** -/
theorem c1_fresh_frame : MemFrame csA csC (freshMem m9) (freshMem mS) := by
  refine ⟨fun b hb hc => ?_, fun x hx => ?_, fun b => ?_⟩
  · rw [freshMem_arr, freshMem_arr, ite_eq_right hc, ite_eq_right hc]
    split
    · rw [c1_trunc_size hfr hext]
    · exact c1_trunc_eq hfr hext hb hc
  · rw [freshMem_arr, freshMem_arr, ite_eq_left rfl, ite_eq_left rfl, truncFrozen_ctl, truncFrozen_ctl]
    simp only [rdW, ← Array.getD_eq_getD_getElem?]
    rw [getD_freshCtl, getD_freshCtl]
    split
    · simp only [Array.getD_eq_getD_getElem?]; exact hfr.ctl x hx
    · rfl
  · rw [freshMem_arr, freshMem_arr]
    split
    · simp [freshCtl, truncFrozen_ctl, hfr.size]
    · split <;> simp [zeros, c1_trunc_size hfr hext]

omit hfr hext in
theorem c1_rdW (a : Array Word) (x : Word) : rdW a x = a.getD x.toNat 0 := by
  simp only [rdW, Array.getD_eq_getD_getElem?]

/-- **The challenge's jobs' memory half after the solution's calls on one region**: the solution's
at `X` (reached from `freshMem mS` keeping `c1Q`), the challenge's at `freshMem m9`: the
challenge's at `X` patched with `freshMem m9`'s stream index, at the solution's state. -/
theorem c1_back {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {J : ISolution}
    {IS IC : IStreamIndex} {dsS dsC : Array IDeclaration} {X : Mem} {a a9 : AState}
    (hS : JobM pins dn dsS none IS X a) (hC : JobM pins dn dsC (some J) IC (freshMem m9) a9)
    (hQ : c1Q (freshMem mS) X) : JobM pins dn dsC (some J) IC (c1Patch (freshMem m9) X) a := by
  have hF := c1_fresh_frame hfr hext
  have hXs : (X.arr64 CTL).size = ((freshMem m9).arr64 CTL).size := by rw [hQ.1.size, hF.size]
  have harr : ∀ b ∈ csA, (c1Patch (freshMem m9) X).arr64 b = (freshMem m9).arr64 b := fun b hb => by
    rw [c1Patch_arr, ite_eq_left hb]
  have hD : (c1Patch (freshMem m9) X).arr64 L.Front.DECL = (freshMem m9).arr64 L.Front.DECL := harr _ (by decide)
  have hP : (c1Patch (freshMem m9) X).arr64 L.Front.DLP = (freshMem m9).arr64 L.Front.DLP := harr _ (by decide)
  have hV : CsViewC (freshMem m9) X (c1Patch (freshMem m9) X) := by
    refine ⟨⟨fun b hb hc => ?_, fun x hx => ?_, fun b => ?_⟩, fun b hb => ?_, fun i _ => by rw [hD],
      fun i _ => by rw [hP], by rw [hD], by rw [hP], fun x hx => ?_⟩
    · rw [c1Patch_arr, ite_eq_right hb, ite_eq_right hc]
    · rw [c1Patch_arr, ite_eq_right (by decide), ite_eq_left rfl, c1_rdW, c1_rdW, getD_c1CtlP]
      have : x.toNat ∉ rrWs := fun h => hx ((csC_iff x).mpr h)
      split <;> simp_all
    · rw [c1Patch_arr]
      split
      · rw [hQ.1.size, hF.size]
      · split
        · subst ‹b = CTL›; rw [size_c1CtlP]
        · rfl
    · simp only [IdxArr, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hb
      exact harr b (csA_of_idx hb.1 hb.2)
    · rw [c1Patch_arr, ite_eq_right (by decide), ite_eq_left rfl, c1_rdW, c1_rdW, getD_c1CtlP]
      have := (csC_iff x).mp hx
      split
      · simp_all
      · simp only [Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_none (show ((freshMem m9).arr64 CTL).size ≤ x.toNat by omega)]; rfl
  have n225 : (225 : Word) ∉ cqC := cq_not_cqC (.inl (cq_not_cdC (by decide)))
  have n226 : (226 : Word) ∉ cqC := cq_not_cqC (.inl (cq_not_cdC (by decide)))
  have hK : CsKeep (freshMem m9) X := by
    refine ⟨fun b hb => ?_, ?_, ?_, fun i v hv => ?_, ?_⟩
    · have ha := solArrs_arr hb
      have hc : b ≠ CTL := fun e => by subst e; revert ha; decide
      rw [hQ.1.arr b (cq_not_cqA (.inl fun h => cdA_sol h hb)) hc,
        hF.arr b (fun h => by have := csA_arr h; omega) hc]
    · show rdW (X.arr64 CTL) 225 = rdW ((freshMem m9).arr64 CTL) 225
      rw [hQ.1.ctl 225 n225, hF.ctl 225 (by decide)]
    · show rdW (X.arr64 CTL) 226 = rdW ((freshMem m9).arr64 CTL) 226
      rw [hQ.1.ctl 226 n226, hF.ctl 226 (by decide)]
    · rw [erecP_congr' (m := freshMem mS) (hF.arr _ (by decide) (by decide)).symm
        (hF.arr _ (by decide) (by decide)).symm (hF.ctl 129 (by decide)).symm (hF.ctl 130 (by decide)).symm] at hv
      exact hQ.2 i v hv
    · exact (((hC.jsol.walk J rfl).1.frame hF (by decide) (by decide) (by decide) (by decide)).frame hQ.1
        (cq_not_cqA (.inr (.inl rfl))) (cq_not_cqA (.inr (.inr (.inl rfl))))
        (cq_not_cqC (.inr (by decide))) (cq_not_cqC (.inr (by decide))))
  exact hS.csBack hC hV hK

/-- **The switch at a thread's call**: a region `r` whose next solution call is the solution's
jobs' relation at `a` (with `c1Q`) has its next challenge call the challenge's at `a`. -/
theorem c1_thrBack {B BC : Array Word} (hB : HdrView B mS) (hC : HdrView BC m9)
    {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {J : ISolution}
    {IS IC : IStreamIndex} {dsS dsC : Array IDeclaration} {a₀ a9 : AState} {bs : List UInt8}
    (hCm : JobM pins dn dsC (some J) IC (freshMem m9) a9) {r : Mem} {a : AState} (j : Word)
    (hR : ThrAtQ (c1Q (freshMem mS)) pins dn dsS IS a₀ bs (seedMem (bufMem B r j)) a none) :
    ThrAt pins dn dsC IC a₀ bs (seedMem (bufMem BC r j)) a (some J) := by
  obtain ⟨X, ⟨a1, ⟨hJR, hx, hp⟩, hSE⟩, hQ, hPB, hag⟩ := hR
  have hsz : 256 ≤ (r.arr64 CTL).size := by
    have e1 := hag CTL (by decide)
    rw [← bufMem_ctl B r j, ← seedMem_ctl_size, e1, hQ.1.size, freshMem_arr, ite_eq_left rfl]
    simp only [freshCtl, zeros, Array.size_append, size_extract0, Array.size_replicate, truncFrozen_ctl]
    have := (c1_hdr_seed hB).2
    omega
  refine ⟨c1Patch (freshMem m9) X, ⟨a1, ⟨⟨c1_back hfr hext hJR.toJobM hCm hQ, hJR.state,
    hJR.off, hJR.caches⟩, hx, hp⟩, hSE⟩, hPB, fun t ht => ?_⟩
  rw [c1_switch hB hC hfr hext r j hsz t ht, c1Patch_arr, c1Patch_arr, hag CTL (by decide), hag t ht]

end views

end L.Checker
