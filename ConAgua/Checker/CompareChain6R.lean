module

public import ConAgua.Checker.CompareChain6C
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.PrepProgExt
import ConAgua.Checker.PrepProgHoist
import ConAgua.Checker.PrepRef
import ConAgua.Checker.PreLoopWSPart2
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

theorem prep6_of (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) (hst : Stash m PS.pre PS.rC)
    (hk6 : Keep6 m PS.pre) {m2 : Mem} (h : Q62 PS m m2) : Prep6 PS.pre PS.rC PS.sF m2 := by
  obtain ⟨m1, ⟨m0, hO, -, hI, hf⟩, hok, rfl⟩ := h
  have hf' : MemFrame (([OUT] : List TieredArray) ++ moveA) moveC m m1 :=
    (hO.memFrame.mono (by simp) (by simp)).trans (hf.mono (fun b hb => List.mem_append_right _ hb) (by simp))
  have hst1 : Stash m1 PS.pre PS.rC := hst.frame hf' (by decide) (by decide)
  have hD1 : (m1.arr64 L.Front.DECL).size < 2 ^ 63 := by
    rw [hf'.size]; exact hF.build.decls.dsize
  obtain ⟨hD, hR⟩ := restore_of hst1.decls hst1.rok hok hD1
  refine ⟨(stage_moved hF hO hI hf).frame_front (restoreM_frame m1) |>.1, hD, hR, ?_⟩
  exact (hk6.frame hf' (by decide) (by decide) (by decide) (by decide) (by decide)).frame
    (restoreM_frame m1) (by decide) (by decide) (by simp) (by simp) (by simp)

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

end steps

end L.Checker
