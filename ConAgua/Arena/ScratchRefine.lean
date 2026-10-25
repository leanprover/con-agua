import ConAgua.Arena.Scratch
import ConAgua.Arena.Tiers
import ConRon.Arena.Core
import ConAgua.Census.Attr

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

theorem resetMem_frame (m : Mem) (f : Word) : MemFrame [] resetCtl m (resetMem m f) := by
  rw [resetMem_eq]
  have h1 := MemFrame.setCtl m SCB (rdW (m.arr64 CTL) SCB + 4294967296)
  have h2 := MemFrame.setCtl (m.set64 CTL SCB (rdW (m.arr64 CTL) SCB + 4294967296)) 1 f
  exact ((h1.mono (by simp) (by simp [resetCtl])).trans (h2.mono (by simp) (by simp [resetCtl]))).trans
    ((zeroCtl_frame _ _).mono (by simp) (fun y h => by simp [resetCtl, h]))

theorem resetMem_base (m : Mem) (f : Word) (h : SCB.toNat < (m.arr64 CTL).size) :
    rdW ((resetMem m f).arr64 CTL) SCB = rdW (m.arr64 CTL) SCB + 4294967296 := by
  rw [resetMem_eq, (zeroCtl_frame _ _).2.1 SCB (by simp [scratchCnts, SCB]), rdW_set64, rdW_set64]
  simp [SCB] at h ⊢; omega

theorem resetMem_flag (m : Mem) (f : Word) (h : SCB.toNat < (m.arr64 CTL).size) :
    rdW ((resetMem m f).arr64 CTL) 1 = f := by
  rw [resetMem_eq, (zeroCtl_frame _ _).2.1 1 (by simp [scratchCnts]), rdW_set64, size_set64]
  simp [SCB] at h ⊢; omega

/-! ## One table -/

section table
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]

/-- **A table across `scratch_reset(f)`**: tier 0 as before, tier 1 empty, the flag `f ≠ 0`. -/
theorem consR_resetMem {C : ConsSch} {R : Mem → Word → Word → α → Prop}
    (hW : C.WF) (hfr : RFrame C.sch R C.hsM) (hca : C.ca ∉ scratchCnts ∧ C.ca + 1 ∈ scratchCnts)
    (m : Mem) (f : Word) (hlo : (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 62)
    (h62 : SCB.toNat < (m.arr64 CTL).size) {on : Bool} {tbP tbS : Tbl α (Idx k) δ}
    (hR : ConsR C R m on tbP tbS) :
    ConsR C R (resetMem m f) (f != 0) tbP (Tbl.empty : Tbl α (Idx k) δ) := by
  have hf := resetMem_frame m f
  have hsc := hW.sch.scb
  simp only [ConsSch.sch] at hsc
  refine hR.reset hW hfr (fun b hb => hf.1 b (by simp) hb) (hf.2.2.1 CTL)
    (hf.2.1 0 (by simp [resetCtl, scratchCnts, SCB])) ?_ ?_ hlo (resetMem_base m f h62)
    (by rw [resetMem_flag m f h62])
  · simp only [cntC, UInt64.add_zero]
    exact hf.2.1 _ (by simp only [resetCtl, List.mem_cons, not_or]; exact ⟨hsc.1, hsc.2.2.1, hca.1⟩)
  · simp only [cntC]
    rw [resetMem_eq]; exact zeroCtl_rd _ _ _ hca.2

end table

/-! ## The whole arena -/

/-- `a` with every scratch table emptied and every scratch flag `on`: the store part of
`enterScratch` (`on = true`) and of `dropScratch` (`on = false`). -/
def EStore.reset (st : EStore) (on : Bool) : EStore :=
  if on then st.enableScratch else st.dropScratch

/-- **`scratch_reset(f)` keeps `ArenaD`**, with every scratch table emptied and every flag
`f ≠ 0`; the memos stay. -/
@[refines_part ConRon.Arena.EStore.enableScratch "ArenaD"]
theorem ArenaD.reset (m : Mem) (a : AState) (hD : ArenaD m a) (f : Word)
    (hlo : (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 62) (h62 : SCB.toNat < (m.arr64 CTL).size) :
    ArenaD (resetMem m f) { a with store := EStore.reset a.store (f != 0) } := by
  obtain ⟨hR, hDer⟩ := hD
  have hf := resetMem_frame m f
  have e : ∀ {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] (C : ConsSch)
      (R : Mem → Word → Word → α → Prop), C.WF → RFrame C.sch R C.hsM →
      C.ca ∉ scratchCnts ∧ C.ca + 1 ∈ scratchCnts → ∀ (on' : Bool) (tbP tbS : Tbl α (Idx k) δ),
      ConsR C R m on' tbP tbS → ConsR C R (resetMem m f) (f != 0) tbP Tbl.empty :=
    fun C R hW hfr hca on' tbP tbS h => consR_resetMem hW hfr hca m f hlo h62 h
  have hpool : PoolOK (resetMem m f) := by
    obtain ⟨h1, h2, h3, h4⟩ := hR.lit.1
    refine ⟨by rw [hf.2.2.2]; exact h1, by rw [hf.2.2.1]; exact h2,
      by rw [hf.1 POOL (by simp) (by decide)]; exact h3, ?_⟩
    simp only [top_rdW] at h4 ⊢
    rw [hf.2.1 0 (by simp [resetCtl, scratchCnts, SCB]), hf.1 POOL (by simp) (by decide)]; exact h4
  have hM : MemosR (resetMem m f) a.memos :=
    hR.memos.frame (by simp) (by simp [resetCtl, scratchCnts, memoCtl, SCB]) hf
  have hcP : ∀ {α : Type} A, A ≠ CTL → cP (α := α) A (resetMem m f) = cP A m := fun A hA => by
    funext t i x d; simp only [cP, hf.tier A (by simp) (by simp) hA]
  have hE : ∀ {α : Type} [BEq α] [Hashable α] (P : Nat → α → UInt64 → Prop),
      DerT (Tbl.empty : Tbl α EIdx UInt64) P := fun P => ⟨rfl, fun i x h => by simp [Tbl.empty] at h⟩
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hDer
  cases hb : (f != 0) <;> rw [hb] at e <;>
  exact ⟨⟨⟨hpool, e litCS RecRel litCS_wf litFrame (by simp [scratchCnts, litCS, litCSk]) _ _ _ hR.lit.2⟩,
    e appCS ARecRel appCS_wf appFrame (by simp [scratchCnts, appCS]) _ _ _ hR.app,
    e sortCS SoRecRel sortCS_wf sortFrame (by simp [scratchCnts, sortCS]) _ _ _ hR.sort,
    e constCS CeRecRel constCS_wf constFrame (by simp [scratchCnts, constCS]) _ _ _ hR.const,
    e letCS LeRecRel letCS_wf letFrame (by simp [scratchCnts, letCS]) _ _ _ hR.letE,
    e bvarCS BRecRel bvarCS_wf bvarFrame (by simp [scratchCnts, bvarCS]) _ _ _ hR.bvar,
    e fvarCS FVRecRel fvarCS_wf fvarFrame (by simp [scratchCnts, fvarCS]) _ _ _ hR.fvar,
    e lamCS LaRecRel lamCS_wf laFrame (by simp [scratchCnts, lamCS]) _ _ _ hR.lam,
    e forallCS FaRecRel forallCS_wf faFrame (by simp [scratchCnts, forallCS]) _ _ _ hR.forallE,
    e projCS PJRecRel projCS_wf projFrame (by simp [scratchCnts, projCS]) _ _ _ hR.proj,
    e zeroCS ZRecRel zeroCS_wf zeroFrame (by simp [scratchCnts, zeroCS]) _ _ _ hR.zero,
    e succCS SRecRel succCS_wf succFrame (by simp [scratchCnts, succCS]) _ _ _ hR.succ,
    e maxCS MRecRel maxCS_wf maxFrame (by simp [scratchCnts, maxCS]) _ _ _ hR.max,
    e imaxCS IRecRel imaxCS_wf imaxFrame (by simp [scratchCnts, imaxCS]) _ _ _ hR.imax,
    e paramCS PRecRel paramCS_wf paramFrame (by simp [scratchCnts, paramCS]) _ _ _ hR.param,
    e lsCS LsRecRel lsCS_wf lsFrame (by simp [scratchCnts, lsCS]) _ _ _ hR.ls,
    e nanonCS NaRecRel nanonCS_wf naFrame (by simp [scratchCnts, nanonCS]) _ _ _ hR.nanon,
    e nstrCS NsRecRel nstrCS_wf nstrFrame (by simp [scratchCnts, nstrCS]) _ _ _ hR.nstr,
    e nnumCS NnRecRel nnumCS_wf nnFrame (by simp [scratchCnts, nnumCS]) _ _ _ hR.nnum,
    hM, ⟨hR.zeroHp.1, constT_empty _⟩, ⟨hR.paramHp.1, constT_empty _⟩,
    ⟨colT_mono hR.succHp.1 (fun _ _ => by rw [hf.tier SHP (by simp) (by simp) (by decide)]), colT_empty _ _ _ _⟩,
    ⟨colT_mono hR.maxHp.1 (fun _ _ => by rw [hf.tier MHP (by simp) (by simp) (by decide)]), colT_empty _ _ _ _⟩,
    ⟨colT_mono hR.imaxHp.1 (fun _ _ => by rw [hf.tier IHP (by simp) (by simp) (by decide)]), colT_empty _ _ _ _⟩,
    ⟨colT_mono hR.lsHp.1 (fun _ _ => by rw [hf.tier LSHP (by simp) (by simp) (by decide)]), colT_empty _ _ _ _⟩,
    ⟨colT_mono hR.sortLp.1 (fun _ _ => by rw [hf.tier SOLP (by simp) (by simp) (by decide)]), colT_empty _ _ _ _⟩,
    ⟨colT_mono hR.constLp.1 (fun _ _ => by rw [hf.tier CLP (by simp) (by simp) (by decide)]), colT_empty _ _ _ _⟩,
    ⟨colT_mono hR.fvarLp.1 (fun _ _ => by rw [hf.tier FVLP (by simp) (by simp) (by decide)]), colT_empty _ _ _ _⟩⟩,
    ⟨⟨d1.1, hE _⟩, ⟨d2.1, hE _⟩, ⟨d3.1, hE _⟩, ⟨d4.1, hE _⟩, ⟨d5.1, hE _⟩,
      ⟨by rw [hcP ADER (by decide)]; exact d6.1, hE _⟩,
      ⟨by rw [hcP LADER (by decide)]; exact d7.1, hE _⟩,
      ⟨by rw [hcP FADER (by decide)]; exact d8.1, hE _⟩,
      ⟨by rw [hcP LEDER (by decide)]; exact d9.1, hE _⟩,
      ⟨by rw [hcP PJDER (by decide)]; exact d10.1, hE _⟩⟩⟩

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
    (hlo : (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 62) (h62 : SCB.toNat < (m.arr64 CTL).size)
    (c1 : rdW ((resetMem m 1).arr64 CTL) bmSch.cs + 2 ≠ 0)
    (c2 : rdW ((mclearG bmSch (resetMem m 1)).arr64 CTL) lfSch.cs + 2 ≠ 0)
    (c3 : rdW ((mclearG lfSch (mclearG bmSch (resetMem m 1))).arr64 CTL) imSch.cs + 2 ≠ 0)
    (c4 : rdW ((mclearG imSch (mclearG lfSch (mclearG bmSch (resetMem m 1)))).arr64 CTL)
      frSch.cs + 2 ≠ 0) :
    ArenaD (enterMem m) { a with store := EStore.reset a.store true, memos := Memos.empty } := by
  obtain ⟨hR, hDer⟩ := ArenaD.reset m a hD 1 hlo h62
  simp only [show ((1 : Word) != 0) = true from rfl] at hR hDer
  have hf := clears_frame (resetMem m 1)
  generalize hm1 : resetMem m 1 = m1 at *
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
  obtain ⟨hloc, -, hlo, h62, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchDrop_spec p hp hr hfl n s₀)
  subst hs
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ (dropScratch_run a₀)
  refine ⟨hloc, hok, ?_⟩
  rw [hst, hm]
  have hD' : ArenaD (flushMem s.mem) a₀ :=
    ⟨ArenaR.frame_ext [] _ (by simp) flushCtl_ge _ _ (flushMem_frame _) _ hD.1,
      DerR.frameM [] _ _ _ (flushMem_frame _) (by simp) _ hD.2⟩
  obtain ⟨hR, hDer⟩ := ArenaD.reset _ _ hD' 0 hlo h62
  simp only [show ((0 : Word) != 0) = false from rfl] at hR hDer
  exact ⟨by cases hR; constructor <;> assumption, DerR.of_store _ _ _ hDer rfl⟩

/-- **`scratch_reset(0)` refines `EStore.dropScratch`**: `ArenaD` represents the whole store (every
table's two tiers, the flag, the derived ranges), and after the call it represents the store with
the scratch tables emptied and the flag off; the memos stay. It aborts only when the slot epoch
`CTL[62]` reaches `2^62` (a capacity). -/
@[refines ConRon.Arena.EStore.dropScratch]
theorem scratchReset_dropScratch (p : Prog) (hr : p.lookup "scratch_reset" = some scratchReset)
    (a : AState) (n : Nat) (s₀ : St) (hD : ArenaD s₀.mem a) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "scratch_reset" [0]
    ⦃fun _ s' => LocEq s' s₀ ∧ ArenaD s'.mem { a with store := a.store.dropScratch }; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hlo, h62, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchReset_spec p hr n s₀ 0)
  subst hs
  refine ⟨hloc, ?_⟩
  rw [hm]
  exact ArenaD.reset _ _ hD 0 hlo h62

/-! ## The other tiers -/

theorem enterMem_frame (m : Mem) : MemFrame [] (resetCtl ++ memoCtl) m (enterMem m) :=
  ((resetMem_frame m 1).mono (by simp) (fun x h => List.mem_append_left _ h)).trans
    ((clears_frame _).mono (by simp) (fun x h => List.mem_append_right _ h))

theorem resetCtl_lt : ∀ x ∈ resetCtl ++ memoCtl, x.toNat < 64 := by
  simp [resetCtl, scratchCnts, memoCtl, SCB]

/-- The bracket keeps the pins and the environment: it writes `CTL` words below 128 only. -/
theorem CheckR.of_bracket {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {vis : Word} {fe : IFEnv} {C : List Word} (hR : CheckR dn m a vis fe) (hD : ArenaD m' a')
    (hc : CoreR m' a'.caches) (hf : MemFrame [] C m m') (hC : ∀ x ∈ C, x.toNat < 128)
    (hp : a'.pins = a.pins) : CheckR dn m' a' vis fe :=
  ⟨hD, hc, by rw [hp]; exact hR.pins.frame (.of_lt (k := 0) (by simp) (by decide)) hf,
    hR.env.frame (.of_lt (k := 0) (by simp) (by decide)) (.of_lt hC (by decide)) hf⟩

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
  obtain ⟨hloc, hlo, h62, c1, c2, c3, c4, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchEnter_spec p hp hr hb hl hi hf n s₀)
  subst hs
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ (enterScratch_run a₀)
  refine ⟨hloc, hok, ?_⟩
  rw [hst, hm]
  exact hC.of_bracket (C := resetCtl ++ memoCtl) (ArenaD.enter _ _ hC.arena hlo h62 c1 c2 c3 c4)
    (hC.core.frame (.of_lt (k := 0) (by simp) (by decide))
      (.of_lt (fun x h => resetCtl_lt x h) (by decide)) (enterMem_frame _))
    (enterMem_frame _) (fun x h => Nat.lt_trans (resetCtl_lt x h) (by decide)) rfl

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
  obtain ⟨-, hfok, -, -, hm⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (scratchDrop_spec p hp hr hfl n s₀)
  subst hs
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ (dropScratch_run a₀)
  have hrf : MemFrame [] resetCtl (flushMem s.mem) (resetMem (flushMem s.mem) 0) :=
    resetMem_frame _ 0
  have hcore : CoreR (resetMem (flushMem s.mem) 0) Caches.empty :=
    (hC.core.flush hfok).frame (.of_lt (k := 0) (by simp) (by decide))
      (.of_lt (fun x h => resetCtl_lt x (List.mem_append_left _ h)) (by decide)) hrf
  refine ⟨hloc, hok, hC.of_bracket (C := flushCtl ++ resetCtl) hD (by rw [hst, hm]; exact hcore)
    ?_ ?_ (by rw [hst])⟩
  · rw [hm]
    exact ((flushMem_frame _).mono (by simp) (fun x h => List.mem_append_left _ h)).trans
      (hrf.mono (by simp) (fun x h => List.mem_append_right _ h))
  · intro x h
    rcases List.mem_append.mp h with h | h
    · exact flushCtl_lt x h
    · exact Nat.lt_trans (resetCtl_lt x (List.mem_append_left _ h)) (by decide)

/- Two scratch rounds: the base rises by `2^32` each time, the flag follows. -/
#guard
  let m : Mem := { words := #[#[], Array.replicate 120 0] ++ Array.replicate 47 #[] }
  match run scratchProg 100 "scratch_enter" [] m with
  | .ok (_, m1) => match run scratchProg 100 "scratch_drop" [] m1 with
    | .ok (_, m2) => (m1.arr64 1)[62]! == 4294967296 && (m1.arr64 1)[1]! == 1 &&
        (m2.arr64 1)[62]! == 8589934592 && (m2.arr64 1)[1]! == 0
    | .error _ => false
  | .error _ => false

end L.Arena
