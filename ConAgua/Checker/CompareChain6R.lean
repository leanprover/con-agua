module

public import ConAgua.Checker.CompareChain6C
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.PrepProgExt
import ConAgua.Checker.PrepProgHoist
import ConAgua.Checker.PrepRef
import ConAgua.Checker.PreLoopWSPart2
import ConAgua.Checker.TwinCaches
public import ConAgua.Arena.IndSumSpec.McGoStep
import ConAgua.Arena.IndPosSpec.FgW
public import ConAgua.Arena.JustifySideRefMates
import ConAgua.Checker.LoopProgTac
import all ConAgua.Checker.Entry
import all ConAgua.Checker.CompareEntry

@[expose] public section

/-!
# Mode `6`'s steps at the checker (lane compare)

The step specs `checkC3_of_stages` takes, at `checkerProg`, after the solution's index build
(`FoldOn` at a `PhaseS`, its challenge's records `Stash`, `Keep6`): each step's memory predicate
records the step's raw facts on top of the previous one's (`Q61` … ); the semantic facts the next
step's refinement needs are derived from them (`pre_prep`, …).
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend
open Std.WP

section steps
variable {bC bS pb : ByteArray} {sz : TieredArray → Nat} (PS : PhaseS bC bS) (m₇ m : Mem)

/-- After the move. -/
def Q61 (m1 : Mem) : Prop :=
  ∃ m0, OutEq m m0 ∧ SolIdxR m1 PS.IS ∧ IndexR m1 {} ∧ MemFrame moveA moveC m0 m1

/-- After `cmp_restore`. -/
def Q62 (m2 : Mem) : Prop := ∃ m1, Q61 PS m m1 ∧ RestoreOK m1 ∧ m2 = restoreM m1

variable {PS m₇ m}

/-- The word arrays' sizes after the solution's index build are the loaded memory's. -/
theorem FoldOn.sizeAt {b : ByteArray} {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    {sE : AState} {I : IStreamIndex} {sF : AState}
    (hF : FoldOn b pb sz ds ipins sE I sF m₇ m) (t : TieredArray) : (m.arr64 t).size = sz t := by
  rw [hF.frame.size, hF.r7.since.frame.size, loadMem_arr, Array.size_replicate]

/-- **The move, as a step**: from a memory that agrees with the solution's index build's but in
`OUT`, at the count `DECL[0]`. -/
theorem moveStep6 (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    (hsz6 : ∀ g ≤ 2, sz (sixArr g) = sz (eixArr g) ∧ sz (stxArr g) = sz (tixArr g)) :
    StageSpecC checkerProg "index_to_solution" (fun c m0 => OutEq m m0 ∧ CntAt c m0)
      fun _ m1 => Q61 PS m m1 := by
  intro n _ s₀ c
  refine triple_post (callW_spec checkerProg n "index_to_solution" [c] s₀) fun _ s' ⟨hl, hc⟩ =>
    ⟨hl, fun ⟨hO, hcnt⟩ => ?_⟩
  have hD0 : 0 < (s₀.mem.arr64 L.Front.DECL).size := by
    rw [hO.size, hF.sizeAt]; have := hF.build.decls.room; rw [hF.sizeAt] at this; omega
  have hcnt' : c.toNat = PS.dsS.size := by
    have := hF.build.decls.count
    rw [← hO.arr _ (by decide)] at this
    rw [hcnt hD0]; simpa [hD0] using this
  obtain ⟨h1, h2, h3⟩ := move_step PS hF hO hsz6 hc hcnt'
  exact ⟨s₀.mem, hO, h1, h2, h3⟩

/-- **`cmp_restore`, as a step.** -/
theorem restoreStep6 : StageSpec checkerProg "cmp_restore" (Q61 PS m) fun _ => Q62 PS m := by
  intro n _ s₀
  exact triple_post (cmpRestore_spec checkerProg (by chk_lk) n s₀) fun _ _ ⟨hl, hok, hm⟩ =>
    ⟨hl, fun h1 => ⟨_, h1, hok, hm⟩⟩

/-- **Before the challenge's preparation** (after the move and `cmp_restore`): the stage relation
at the empty index's environment, the prelude's and the challenge's records in `DECL`, the
hoist's memos and the prelude's count. -/
structure Prep6 (pre : PreludeIx) (rC : ParseResultD) (sF : AState) (m2 : Mem) : Prop where
  stage : L.Ind.StageR 0 (fe0 sF.pins) m2 sF
  decls : DeclsF (m2.arr64 L.Front.DECL) (m2.arr64 L.Front.DLP) (pre.decls ++ rC.decls)
  rok : ∀ x < (pre.decls ++ rC.decls).size, RecOK (m2.arr64 L.Front.DECL) (m2.arr64 L.Front.DLP) x
  keep : Keep6 m2 pre
  memos : IndMemos m2

theorem moveA_memos : ∀ b ∈ (([OUT] : List TieredArray) ++ moveA),
    b ≠ ILFM ∧ b ≠ L.Stubs.CRM ∧ (b.arr < 201 ∨ 208 < b.arr) := by
  intro b hb
  rcases List.mem_append.mp hb with h | h
  · simp only [List.mem_singleton] at h; subst h; decide
  · obtain ⟨-, h1 | h1⟩ := moveA_facts b h <;>
      exact ⟨fun e => by subst e; revert h1; decide, fun e => by subst e; revert h1; decide, by omega⟩

theorem prep6_of (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) (hst : Stash m PS.pre PS.rC)
    (hk6 : Keep6 m PS.pre) {m2 : Mem} (h : Q62 PS m m2) : Prep6 PS.pre PS.rC PS.sF m2 := by
  obtain ⟨m1, ⟨m0, hO, -, hI, hf⟩, hok, rfl⟩ := h
  have hf' : MemFrame (([OUT] : List TieredArray) ++ moveA) moveC m m1 :=
    (hO.memFrame.mono (by simp) (by simp)).trans (hf.mono (fun b hb => List.mem_append_right _ hb) (by simp))
  have hst1 : Stash m1 PS.pre PS.rC := hst.frame hf' (by decide) (by decide)
  have hD1 : (m1.arr64 L.Front.DECL).size < 2 ^ 63 := by
    rw [hf'.size]; exact hF.build.decls.dsize
  obtain ⟨hD, hR⟩ := restore_of hst1.decls hst1.rok hok hD1
  refine ⟨(stage_moved hF hO hI hf).frame_front (restoreM_frame m1) |>.1, hD, hR, ?_, ?_⟩
  · exact (hk6.frame hf' (by decide) (by decide) (by decide) (by decide) (by decide)).frame
      (restoreM_frame m1) (by decide) (by decide) (by simp) (by simp) (by simp)
  · refine ((hF.build.memos.frame hf' moveA_memos fun x hx => ?_).frame (restoreM_frame m1)
      (by decide) (by simp))
    simp only [moveC, SNEXTC, SCNTC, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> decide

/-- What `prepare_prelude` leaves (`preparePrelude_refines`' post, from the memory `m2` before it). -/
structure PrepPost (pre : PreludeIx) (rC : ParseResultD) (a : AState) (m2 m3 : Mem)
    (ds' : Array IDeclaration) (a' : AState) : Prop where
  run : preparePrelude pre rC.decls a = .ok (ds', a')
  cnt : (rdW (m3.arr64 L.Front.DECL) 0).toNat = ds'.size
  recs : ∀ x (h : x < ds'.size), DeclAtF (m3.arr64 L.Front.DECL) (m3.arr64 L.Front.DLP) x ds'[x] ∧
    RecOK (m3.arr64 L.Front.DECL) (m3.arr64 L.Front.DLP) x
  arena : ArenaR m3 a'
  iw : L.Ind.IWOK m3
  pins : PinsR m3 a'.pins
  dlp : m3.arr64 L.Front.DLP = m2.arr64 L.Front.DLP
  dsize : (m3.arr64 L.Front.DECL).size = (m2.arr64 L.Front.DECL).size
  pers : a'.store.pers = a.store.pers
  scr : a'.store.scr = a.store.scr
  pinsEq : a'.pins = a.pins
  le : ds'.size ≤ (pre.decls ++ rC.decls).size
  seen : ∃ s, SeenR m3 s
  nix : ∃ idx, NixR m3 idx
  frame : MemFrame stageA_prepare_prelude stageC_prepare_prelude m2 m3

/-- After the challenge's preparation. -/
def Q63 (PS : PhaseS bC bS) (m m3 : Mem) : Prop :=
  ∃ m2 dsC sG, Q62 PS m m2 ∧ PrepPost PS.pre PS.rC PS.sF m2 m3 dsC sG

/-- **`prepare_prelude`, as a step** (`preparePrelude_refines` at the twin's state after the
solution's index build). -/
theorem prepStep6 (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) (hst : Stash m PS.pre PS.rC)
    (hk6 : Keep6 m PS.pre) :
    StageSpec checkerProg "prepare_prelude" (Q62 PS m) fun _ => Q63 PS m := by
  intro n _ s₀
  apply M.triple_of_run
  rintro s rs s' rfl hrun
  obtain ⟨hl, -⟩ := M.of_run (P := fun x => x = s) rfl hrun
    (callW_spec checkerProg n "prepare_prelude" [] s)
  refine ⟨hl, fun hQ => ?_⟩
  have P6 := prep6_of hF hst hk6 hQ
  have hfr := (M.of_run (P := fun x => x = s) rfl hrun (stageFrame_prepare_prelude n s))
  have hdsz : (s.mem.arr64 L.Front.DECL).size < 2 ^ 64 := by
    have := P6.decls.dsize; omega
  obtain ⟨-, ds', a', hr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    M.of_run (P := fun x => x = s) rfl hrun
      (preparePrelude_refines checkerProg checkerProg_prepProg checkerProg_prepExt
        checkerProg_hoistProg checkerProg_hoistExt n s PS.sF PS.pre PS.rC.decls
        (fun x hx => ⟨P6.decls.recs x hx, P6.rok x hx⟩) (by simpa [rdW] using P6.decls.count)
        P6.keep.np P6.decls.room hdsz P6.stage.check.arena.base P6.keep.seen P6.keep.nix
        P6.stage.iw P6.stage.check.pins)
  exact ⟨s.mem, ds', a', hQ, ⟨hr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hfr⟩⟩

theorem checkerProg_sideProg : SideProg checkerProg :=
  ⟨by chk_lk, by chk_lk, by chk_lk, by chk_lk, by chk_lk, by chk_lk, by chk_lk, by chk_lk, by chk_lk,
    by chk_lk⟩

theorem checkerProg_matesProg : MatesProg checkerProg :=
  ⟨by chk_lk, by chk_lk, by chk_lk, by chk_lk, by chk_lk, by chk_lk, by chk_lk⟩

theorem stageA_prep_facts : ∀ b ∈ stageA_prepare_prelude,
    b.arr = 33 ∨ b.arr = 34 ∨ b.arr = 67 ∨ b.arr = 75 ∨ b.arr = 76 ∨ b.arr = 200 := by decide

theorem stageC_prep_facts : ∀ x ∈ stageC_prepare_prelude,
    x = 34 ∨ x = 35 ∨ x = 73 ∨ x = 74 ∨ x = 75 ∨ x = 76 ∨ x = 200 := by
  intro x hx; simp only [stageC_prepare_prelude, List.mem_cons, List.not_mem_nil, or_false] at hx
  exact hx

theorem envArrs_ge : ∀ b ∈ envArrs, 129 ≤ b.arr := by decide

/-- **The stage relation after the challenge's preparation**, at its twin state. -/
theorem PrepPost.stage {pre : PreludeIx} {rC : ParseResultD} {a : AState} {m2 m3 : Mem}
    {ds' : Array IDeclaration} {a' : AState} (h : PrepPost pre rC a m2 m3 ds' a')
    (hS : L.Ind.StageR 0 (fe0 a.pins) m2 a) : L.Ind.StageR 0 (fe0 a.pins) m3 a' := by
  have hc : a'.caches = a.caches := ((TwinCaches.keeps_preparePrelude pre rC.decls).run h.run).1
  have hA : ∀ b ∈ stageA_prepare_prelude, b.arr < 42 ∨ 46 < b.arr := fun b hb => by
    have := stageA_prep_facts b hb; omega
  have hE : ∀ b ∈ stageA_prepare_prelude, b ∉ envArrs := fun b hb he => by
    have := stageA_prep_facts b hb; have := envArrs_ge b he; have := envArrs_le b he; omega
  have hEC : ∀ x ∈ stageC_prepare_prelude, x ∉ envCtl := fun x hx he => by
    rcases stageC_prep_facts x hx with e | e | e | e | e | e | e <;> subst e <;> revert he <;> decide
  have hCA : AvoidA 96 128 stageA_prepare_prelude := by
    unfold AvoidA; intro b hb; have := stageA_prep_facts b hb; omega
  have hCC : AvoidC 96 128 stageC_prepare_prelude := by
    unfold AvoidC; intro x hx
    rcases stageC_prep_facts x hx with e | e | e | e | e | e | e <;> subst e <;> decide
  have h0 : (0 : Word) ∉ stageC_prepare_prelude := fun hx => by
    rcases stageC_prep_facts _ hx with e | e | e | e | e | e | e <;> revert e <;> decide
  have h1 : (1 : Word) ∉ stageC_prepare_prelude := fun hx => by
    rcases stageC_prep_facts _ hx with e | e | e | e | e | e | e <;> revert e <;> decide
  refine ⟨⟨⟨h.arena, DerR.congrSt h.pers h.scr (DerR.frameM _ _ _ _ h.frame hA _
      hS.check.arena.der)⟩, ?_, h.pins, hS.check.env.frame hE hEC h.frame,
    hS.check.mode.frame h.frame h0 h1⟩, h.iw⟩
  rw [hc]; exact hS.check.core.frame hCA hCC h.frame

/-- `DECL` after the preparation holds the prepared records. -/
theorem PrepPost.declsF {pre : PreludeIx} {rC : ParseResultD} {a : AState} {m2 m3 : Mem}
    {ds' : Array IDeclaration} {a' : AState} (h : PrepPost pre rC a m2 m3 ds' a')
    (hD : DeclsF (m2.arr64 L.Front.DECL) (m2.arr64 L.Front.DLP) (pre.decls ++ rC.decls)) :
    DeclsF (m3.arr64 L.Front.DECL) (m3.arr64 L.Front.DLP) ds' := by
  refine ⟨by rw [h.dsize]; exact hD.dsize, by rw [h.dlp]; exact hD.psize,
    by simpa [rdW] using h.cnt, ?_, by rw [h.dlp]; exact hD.ptop, fun i hi => (h.recs i hi).1,
    fun i hi b' nP e => by
      have h1 := (h.recs i hi).1
      rw [e] at h1
      obtain ⟨h6, h4, -⟩ := h1
      rw [← h4]; exact ((h.recs i hi).2.2 h6).2.2⟩
  rw [h.dsize]; have := hD.room; have := h.le; omega

/-- `IndMemos` after the preparation. -/
theorem PrepPost.memos {pre : PreludeIx} {rC : ParseResultD} {a : AState} {m2 m3 : Mem}
    {ds' : Array IDeclaration} {a' : AState} (h : PrepPost pre rC a m2 m3 ds' a') (hM : IndMemos m2) :
    IndMemos m3 :=
  hM.frame h.frame (fun b hb => by
      have := stageA_prep_facts b hb
      exact ⟨fun e => by subst e; revert this; decide, fun e => by subst e; revert this; decide, by omega⟩)
    (fun x hx => by rcases stageC_prep_facts x hx with e | e | e | e | e | e | e <;> subst e <;> decide)

/-- What the steps up to the side records leave, at the count `c`. -/
structure Side6 (PS : PhaseS bC bS) (m : Mem) (c : Word) (m2 m3 : Mem) (dsC : Array IDeclaration)
    (sG : AState) (res : List IDeclaration) (m4 : Mem) : Prop where
  q62 : Q62 PS m m2
  prep : PrepPost PS.pre PS.rC PS.sF m2 m3 dsC sG
  cnt : CntAt c m3
  run : (sideRecordsGo [] dsC.toList).run sG = .ok (res, sG)
  decls : DeclsF (m4.arr64 L.Front.DECL) (m4.arr64 L.Front.DLP) res.toArray
  stage : L.Ind.StageR 0 (fe0 PS.sF.pins) m4 sG
  mc : ∃ mp, L.Ind.mcMR m4 mp
  frame : MemFrame [L.Front.DECL, L.Ind.MCM] [L.Ind.mcSch.cs, L.Ind.mcSch.cs + 1] m3 m4
  kind : KindStep (m3.arr64 L.Front.DECL) (m4.arr64 L.Front.DECL)

/-- After the side records, at the count `c`. -/
def Q64 (PS : PhaseS bC bS) (m : Mem) (c : Word) (m4 : Mem) : Prop :=
  ∃ m2 m3 dsC sG res, Side6 PS m c m2 m3 dsC sG res m4

/-- **`side_records(c)`, as a step** (`sideRecords_ref`). -/
theorem sideStep6 (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) (hst : Stash m PS.pre PS.rC)
    (hk6 : Keep6 m PS.pre) :
    StageSpecC checkerProg "side_records" (fun c m3 => Q63 PS m m3 ∧ CntAt c m3) (Q64 PS m) := by
  intro n _ s₀ c
  refine triple_post (callW_spec checkerProg n "side_records" [c] s₀) fun _ s' ⟨hl, hc⟩ =>
    ⟨hl, fun ⟨⟨m2, dsC, sG, hQ, hP⟩, hcnt⟩ => ?_⟩
  have P6 := prep6_of hF hst hk6 hQ
  have hS3 := hP.stage P6.stage
  have hD3 := hP.declsF P6.decls
  have hM3 := hP.memos P6.memos
  have hD0 : 0 < (s₀.mem.arr64 L.Front.DECL).size := by have := hD3.room; omega
  have hc' : c.toNat = dsC.size := by
    have := hD3.count; rw [hcnt hD0]; simpa [hD0] using this
  obtain ⟨res, hr, h1, h2, h3, h4, h5⟩ := sideRecords_ref checkerProg_sideProg hc hS3 hM3.stage.mc hD3 hc'
  have hp : PS.sF.pins = PS.sF.pins := rfl
  exact ⟨m2, s₀.mem, dsC, sG, res, hQ, hP, hcnt, hr, h1, by rw [← hP.pinsEq] at h2 ⊢; exact h2, h3, h4, h5⟩

/-- The arrays mode `6` writes before the mates. -/
def A64 : List TieredArray :=
  ([OUT] : List TieredArray) ++ moveA ++ ([L.Front.DECL] : List TieredArray) ++ stageA_prepare_prelude ++
    ([L.Front.DECL, L.Ind.MCM] : List TieredArray)

/-- The control words mode `6` writes before the mates. -/
def C64 : List Word := moveC ++ stageC_prepare_prelude ++ [L.Ind.mcSch.cs, L.Ind.mcSch.cs + 1]

theorem A64_arr : ∀ b ∈ A64, (129 ≤ b.arr ∧ b.arr ≤ 134) ∨ (210 ≤ b.arr ∧ b.arr ≤ 215) ∨
    b.arr = 240 ∨ b.arr = 67 ∨ b.arr = 208 ∨ b.arr = 33 ∨ b.arr = 34 ∨ b.arr = 75 ∨ b.arr = 76 ∨
    b.arr = 200 := by
  intro b hb
  simp only [A64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with (((h | h) | h) | h) | h | h
  · subst h; decide
  · have := moveA_facts b h; omega
  · subst h; decide
  · have := stageA_prep_facts b h; omega
  · subst h; decide
  · subst h; decide

theorem C64_val : ∀ x ∈ C64, x = 225 ∨ x = 226 ∨ x = 128 ∨ x = 34 ∨ x = 35 ∨ x = 73 ∨ x = 74 ∨
    x = 75 ∨ x = 76 ∨ x = 200 ∨ x = 216 ∨ x = 217 := by
  intro x hx
  simp only [C64, List.mem_append] at hx
  rcases hx with (h | h) | h
  · simp only [moveC, SNEXTC, SCNTC, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide
  · rcases stageC_prep_facts x h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [L.Ind.mcSch, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h <;> subst h <;> decide

/-- **Mode `6`'s frame up to the side records**, from the solution's index build's memory. -/
theorem Side6.frameM {c : Word} {m2 m3 : Mem} {dsC : Array IDeclaration} {sG : AState}
    {res : List IDeclaration} {m4 : Mem} (h : Side6 PS m c m2 m3 dsC sG res m4) : MemFrame A64 C64 m m4 := by
  obtain ⟨m1, ⟨m0, hO, -, -, hf⟩, -, rfl⟩ := h.q62
  have e1 := hO.memFrame.mono (A' := A64) (C' := C64) (by simp [A64]) (by simp)
  have e2 := hf.mono (A' := A64) (C' := C64) (fun b hb => by simp [A64, hb]) (fun x hx => by simp [C64, hx])
  have e3 := (restoreM_frame m1).mono (A' := A64) (C' := C64) (by simp [A64]) (by simp)
  have e4 := h.prep.frame.mono (A' := A64) (C' := C64) (fun b hb => by simp [A64, hb]) (fun x hx => by simp [C64, hx])
  have e5 := h.frame.mono (A' := A64) (C' := C64) (by simp [A64]) (by simp [C64])
  exact (((e1.trans e2).trans e3).trans e4).trans e5

theorem OutEq.refl (m : Mem) : OutEq m m := ⟨fun _ _ => rfl, fun _ => rfl, rfl⟩

/-- The records' count after the side records is the count the steps were called with. -/
theorem Side6.count {c : Word} {m2 m3 : Mem} {dsC : Array IDeclaration} {sG : AState}
    {res : List IDeclaration} {m4 : Mem} (h : Side6 PS m c m2 m3 dsC sG res m4) :
    c.toNat = res.length ∧ res.length = dsC.size := by
  have h4 := h.decls.count
  have h0 : 0 < (m3.arr64 L.Front.DECL).size := by
    have := h.decls.room; rw [h.kind.1] at this; omega
  have hk : rdN (m4.arr64 L.Front.DECL) 0 = rdN (m3.arr64 L.Front.DECL) 0 := by
    rcases h.kind.2 0 with e | ⟨e, -⟩
    · exact e
    · simp at e
  have hc := h.cnt h0
  have h3 := h.prep.cnt
  simp only [rdN] at hk
  simp only [rdW, UInt64.toNat_zero] at h3
  rw [hk] at h4
  simp only [List.size_toArray] at h4
  refine ⟨?_, by rw [← h4, h3]⟩
  rw [hc, ← h4]; simp [h0]

/-- After the mates, at the count `c`. -/
def Q65 (PS : PhaseS bC bS) (m : Mem) (c : Word) (m5 : Mem) : Prop :=
  ∃ m2 m3 dsC sG res m4, Side6 PS m c m2 m3 dsC sG res m4 ∧
    MatesR m5 (recordMatesGo ∅ res.toArray.toList) ∧ MInv m5 ∧ MKeep m4 m5

/-- **`solution_of(c)`, as a step** (`solutionOf_ref`). -/
theorem matesStep6 (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) :
    StageSpecC checkerProg "solution_of" (Q64 PS m) (Q65 PS m) := by
  intro n _ s₀ c
  refine triple_post (callW_spec checkerProg n "solution_of" [c] s₀) fun _ s' ⟨hl, hc⟩ =>
    ⟨hl, fun ⟨m2, m3, dsC, sG, res, h⟩ => ?_⟩
  obtain ⟨hcr, hrd⟩ := h.count
  have hfr := h.frameM
  have hR3 : ∀ x < res.toArray.size, RecOK (m3.arr64 L.Front.DECL) (m3.arr64 L.Front.DLP) x :=
    fun x hx => (h.prep.recs x (by simp at hx; omega)).2
  have hR := sideRecords_recOK h.kind h.frame
  have hz : ∀ g ≤ 2, ∀ j, rdN (s₀.mem.arr64 (matArr g)) j = 0 := by
    intro g _ j
    have hg : 216 ≤ (matArr g : TieredArray).arr ∧ (matArr g : TieredArray).arr ≤ 218 := by
      unfold matArr; split <;> (try split) <;> decide
    have hn : (matArr g : TieredArray) ∉ A64 := fun hm => by have := A64_arr _ hm; omega
    rw [hfr.arr _ hn (fun e => by rw [e] at hg; simp [CTL] at hg),
      cmp_zero6 hF (OutEq.refl m) (by omega)]
    exact rdN_replicate _ _
  have hctl : 228 < (s₀.mem.arr64 CTL).size := by
    rw [hfr.size, hF.sizeAt]
    have := hF.r7.since.caps.2.1; rw [loadMem_arr, Array.size_replicate] at this
    simp only [ctlMin] at this; omega
  obtain ⟨h1, h2, h3⟩ := solutionOf_ref checkerProg_matesProg hc h.decls
    (fun x hx => hR.1 x (hR3 x hx)) (by rw [hcr]; simp) hz (Nat.le_of_lt h.stage.iw.erCap)
    h.stage.iw.er hctl
  exact ⟨m2, m3, dsC, sG, res, s₀.mem, h, h1, h2, h3⟩

/-- The arrays written from the move's end to the side records' (`cmp_restore`, the preparation,
the side records). -/
def A14 : List TieredArray :=
  ([L.Front.DECL] : List TieredArray) ++ stageA_prepare_prelude ++ ([L.Front.DECL, L.Ind.MCM] : List TieredArray)

/-- The control words written from the move's end to the side records'. -/
def C14 : List Word := stageC_prepare_prelude ++ [L.Ind.mcSch.cs, L.Ind.mcSch.cs + 1]

theorem A14_arr : ∀ b ∈ A14, b.arr = 67 ∨ b.arr = 208 ∨ b.arr = 33 ∨ b.arr = 34 ∨ b.arr = 75 ∨
    b.arr = 76 ∨ b.arr = 200 := by
  intro b hb
  simp only [A14, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with (h | h) | h | h
  · subst h; decide
  · have := stageA_prep_facts b h; omega
  · subst h; decide
  · subst h; decide

theorem C14_val : ∀ x ∈ C14, x = 34 ∨ x = 35 ∨ x = 73 ∨ x = 74 ∨ x = 75 ∨ x = 76 ∨ x = 200 ∨
    x = 216 ∨ x = 217 := by
  intro x hx
  simp only [C14, List.mem_append] at hx
  rcases hx with h | h
  · rcases stageC_prep_facts x h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [L.Ind.mcSch, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h <;> subst h <;> decide

/-- **From the move's end to the side records'**: the move's memory and the frame. -/
theorem Side6.from1 {c : Word} {m2 m3 : Mem} {dsC : Array IDeclaration} {sG : AState}
    {res : List IDeclaration} {m4 : Mem} (h : Side6 PS m c m2 m3 dsC sG res m4) :
    ∃ m1, Q61 PS m m1 ∧ m2 = restoreM m1 ∧ MemFrame A14 C14 m1 m4 := by
  obtain ⟨m1, hQ, -, rfl⟩ := h.q62
  refine ⟨m1, hQ, rfl, ?_⟩
  have e3 := (restoreM_frame m1).mono (A' := A14) (C' := C14) (by simp [A14]) (by simp)
  have e4 := h.prep.frame.mono (A' := A14) (C' := C14) (fun b hb => by simp [A14, hb]) (fun x hx => by simp [C14, hx])
  have e5 := h.frame.mono (A' := A14) (C' := C14) (by simp [A14]) (by simp [C14])
  exact (e3.trans e4).trans e5

/-- **The empty index after the side records** (the rows untouched since the move). -/
theorem Side6.idx {c : Word} {m2 m3 : Mem} {dsC : Array IDeclaration} {sG : AState}
    {res : List IDeclaration} {m4 : Mem} (h : Side6 PS m c m2 m3 dsC sG res m4) : IndexR m4 {} := by
  obtain ⟨m1, ⟨m0, -, -, hI, -⟩, -, hf⟩ := h.from1
  have hx : erecP m4 = erecP m1 :=
    erecP_congr' (hf.arr _ (fun h => by have := A14_arr _ h; simp [EREC] at this) (by decide))
      (hf.arr _ (fun h => by have := A14_arr _ h; simp [EREC] at this) (by decide))
      (hf.ctl _ (fun h => by rcases C14_val _ h with e | e | e | e | e | e | e | e | e <;> revert e <;> decide))
      (hf.ctl _ (fun h => by rcases C14_val _ h with e | e | e | e | e | e | e | e | e <;> revert e <;> decide))
  refine hI.grow (fun b _ hb => hf.arr b (fun h => by have := A14_arr _ h; omega)
    (fun e => by subst e; simp [CTL] at hb))
    (hf.ctl _ (fun h => by rcases C14_val _ h with e | e | e | e | e | e | e | e | e <;> revert e <;> decide))
    (by rw [hx]; exact fun _ _ h => h)

/-- `IWOK` across the mates (the record pool's tier 0 grows inside its bounds, `MInv`). -/
theorem _root_.L.Ind.IWOK.mates {m4 m5 : Mem} (h : L.Ind.IWOK m4) (hK : MKeep m4 m5) (hI : MInv m5) : L.Ind.IWOK m5 := by
  have f := hK.frame
  have eIW : m5.arr64 L.Ind.IW = m4.arr64 L.Ind.IW := f.arr _ (by decide) (by decide)
  have eE1 : m5.arr64 (tier1 EREC) = m4.arr64 (tier1 EREC) := f.arr _ (by decide) (by decide)
  have c200 : rdW (m5.arr64 CTL) 200 = rdW (m4.arr64 CTL) 200 := f.ctl _ (by decide)
  have c130 : rdW (m5.arr64 CTL) 130 = rdW (m4.arr64 CTL) 130 := f.ctl _ (by decide)
  have hsE : (m5.arr64 EREC).size = (m4.arr64 EREC).size := f.size _
  have hsC : (m5.arr64 CTL).size = (m4.arr64 CTL).size := f.size _
  refine ⟨?_, hI.top, by rw [eIW]; exact h.iwSize, by rw [hsE]; exact h.erSize, by rw [hsC]; exact h.ctl,
    ?_, by rw [eE1]; exact h.er1Size, by rw [hsE]; exact h.erCap, by rw [eE1]; exact h.er1Cap⟩
  · simp only [L.Ind.iwTop, eIW, c200]; exact h.iw
  · simp only [erecTop1, eE1, c130]; exact h.er1

/-- **The stage relation and the empty index after the mates.** -/
theorem Side6.stage5 {c : Word} {m2 m3 : Mem} {dsC : Array IDeclaration} {sG : AState}
    {res : List IDeclaration} {m4 m5 : Mem} (h : Side6 PS m c m2 m3 dsC sG res m4) (hK : MKeep m4 m5)
    (hMI : MInv m5) : L.Ind.StageR 0 (fe0 PS.sF.pins) m5 sG ∧ IndexR m5 {} := by
  have hI5 : IndexR m5 {} := h.idx.grow (fun b _ hb => hK.frame.arr b (fun hm => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> revert hb <;> decide)
      (fun e => by subst e; simp [CTL] at hb)) (hK.frame.ctl _ (by decide)) hK.grow.ext
  refine ⟨h.stage.frameG hK.frame (fun b hb => ?_) (fun x hx => ?_) hK.grow.ext hI5
    (h.stage.iw.mates hK hMI), hI5⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; decide

/-- **`IndMemos` across the side records**: `mentions_const`'s memo from the side records, the
others by the frame. -/
theorem _root_.L.Arena.IndMemos.side {m m' : Mem} (h : IndMemos m)
    (hf : MemFrame [L.Front.DECL, L.Ind.MCM] [L.Ind.mcSch.cs, L.Ind.mcSch.cs + 1] m m')
    (hmc : ∃ mp, L.Ind.mcMR m' mp) : IndMemos m' := by
  have hM : L.Ind.MFr [L.Ind.MCM] [216, 217] m m' :=
    ⟨_, _, hf, fun b hb => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact .inl (by decide)
        · exact .inr (.inr (by simp)),
      fun x hx => by
        simp only [L.Ind.mcSch, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact .inr (.inr (by simp))
        · exact .inr (.inr (by simp))⟩
  obtain ⟨⟨hp, ⟨a, ha⟩, -, ⟨c, hc⟩⟩, hi, hcr⟩ := h
  exact ⟨⟨hp.mfr hM (by simp [L.Ind.PosAv]; decide), ⟨a, L.Arena.memoRG_frame L.Ind.maSch L.Ind.maSch_wf _ _ _ _
      (by decide) (by simp [L.Ind.mcSch, L.Ind.maSch]) _ _ hf a ha⟩, hmc,
    ⟨c, L.Arena.memoRG_frame L.Ind.taSch L.Ind.taSch_wf _ _ _ _ (by decide)
      (by simp [L.Ind.mcSch, L.Ind.taSch]) _ _ hf c hc⟩⟩,
    L.Ind.I1Memo.frame hi hf (by decide) (by simp [L.Ind.mcSch]),
    L.Arena.CrOK.frame hcr hf (by decide) (by simp [L.Ind.mcSch])⟩

/-- **A step keeps the bytes** (the checker stores no byte). -/
theorem StageSpecC.keepB {f : FnName} {Pre Post : Word → Mem → Prop}
    (h : StageSpecC checkerProg f Pre Post) (B : Mem → Prop) (hB : ∀ m m', L.Keep m m' → B m → B m') :
    StageSpecC checkerProg f (fun c m' => Pre c m' ∧ B m') (fun c m' => Post c m' ∧ B m') := by
  intro n hn s₀ c
  exact triple_post (Triple.keep checkerProg_noSt8 (h n hn s₀ c)) fun _ _ ⟨⟨hl, hP⟩, hk, _⟩ =>
    ⟨hl, fun ⟨h1, h2⟩ => ⟨hP h1, hB _ _ hk h2⟩⟩

theorem StageSpec.keepB {f : FnName} {Pre : Mem → Prop} {Post : List Word → Mem → Prop}
    (h : StageSpec checkerProg f Pre Post) (B : Mem → Prop) (hB : ∀ m m', L.Keep m m' → B m → B m') :
    StageSpec checkerProg f (fun m' => Pre m' ∧ B m') (fun r m' => Post r m' ∧ B m') := by
  intro n hn s₀
  exact triple_post (Triple.keep checkerProg_noSt8 (h n hn s₀)) fun _ _ ⟨⟨hl, hP⟩, hk, _⟩ =>
    ⟨hl, fun ⟨h1, h2⟩ => ⟨hP h1, hB _ _ hk h2⟩⟩

end steps

end L.Checker
