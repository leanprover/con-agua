module

public import ConAgua.Checker.CompareTwinFacts
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

@[expose] public section

/-!
# The compared run at the L level, mode `5` (lane compare)

`check` with the mode word `5` runs `check_c2()` (`Checker/CompareEntry.lean`): the solution's
`front_run`, `prepare_prelude`, `intern_all_pins`, `build_index` and `par_compact(1)`. They are
entry 1's stages after `builtin_prelude`, at the loaded memory of the solution's bytes (mode `4`
leaves `R4` there, `CmpAt4`), with the compared run's twin (`CmpPfx2`, `StagesOut.cmp`); along
them the challenge's records in `CDECL` stay (`Stash`): the stages do not write `CDECL`, and the
solution's parse keeps the pool `DLP` up to its top (`DLPKeep`).
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

/-! ## The challenge's records across the solution's stages -/

theorem mapM_isSome {α β : Type} {f : α → Option β} :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' → ∀ x ∈ l, (f x).isSome
  | [], _, _, x, hx => absurd hx (by simp)
  | y :: ys, l', h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases hy : f y with
    | none => simp [hy] at h
    | some v =>
      rw [hy] at h
      simp only [Option.bind_some] at h
      cases hys : ys.mapM f with
      | none => simp [hys] at h
      | some vs =>
        rcases List.mem_cons.mp hx with rfl | hx
        · simp [hy]
        · exact mapM_isSome ys vs hys x hx

/-- The words an inductive block's record slice reads are below the array's end. -/
theorem decCIs_lt {a : Array Word} {off cnt : Nat} {l : List IConstantInfo}
    (h : decCIs a off cnt = some l) {j : Nat} (hj : j < cnt) : off + j < a.size := by
  have hs := mapM_isSome _ _ h j (List.mem_range.mpr hj)
  simp only [Option.isSome_iff_exists] at hs
  obtain ⟨c, hc⟩ := hs
  simp only [Option.bind_eq_bind] at hc
  cases hn : L.Arena.nat? (L.Arena.aread a) (off + j) with
  | none => simp [hn] at hc
  | some p =>
    simp only [L.Arena.nat?, L.Arena.aread_apply, Option.map_eq_some_iff] at hn
    obtain ⟨w, hw, -⟩ := hn
    exact (Array.getElem?_eq_some_iff.mp hw).1

theorem trunc_size_le (P : Array Word) (t : Nat) : (trunc P t).size ≤ t + 1 := by
  simp [trunc]; omega

/-- **`RecOK` at a pool that agrees up to the top** (a record's slice is below the top). -/
theorem recOK_congrP {D P P' : Array Word} {r : Nat} {d : IDeclaration} (h : RecOK D P r)
    (hd : DeclAtF D P r d) (hP : ∀ j, 0 < j → j ≤ (P[0]?.getD 0).toNat → P'[j]? = P[j]?) :
    RecOK D P' r := by
  refine ⟨h.1, fun h6 => ?_⟩
  obtain ⟨h2, h3, h4⟩ := h.2 h6
  refine ⟨h2, fun j hj => ?_, h4⟩
  cases d with
  | indDecl blk nP =>
    obtain ⟨-, -, t, ht, hdec⟩ := hd
    have hlt := decCIs_lt hdec hj
    have := trunc_size_le P t
    have h0 : 0 < (dw D r 2).toNat := Nat.pos_of_ne_zero h2
    rw [hP _ (by omega) (by omega)]
    exact h3 j hj
  | _ => simp only [DeclAtF, DeclAt] at hd; rw [hd.1] at h6; exact absurd h6 (by decide)

/-- `Stash` across a frame that writes neither `CDECL` nor `DLP`. -/
theorem Stash.frame {A : List TieredArray} {C : List Word} {m m' : Mem} {pre : PreludeIx}
    {rC : ParseResultD} (h : Stash m pre rC) (hf : MemFrame A C m m') (hc : (CDECL : TieredArray) ∉ A)
    (hd : (DLP : TieredArray) ∉ A) : Stash m' pre rC := by
  have e1 : m'.arr64 CDECL = m.arr64 CDECL := hf.arr _ hc (by decide)
  have e2 : m'.arr64 DLP = m.arr64 DLP := hf.arr _ hd (by decide)
  exact ⟨by rw [e1, e2]; exact h.decls, by rw [e1, e2]; exact h.rok⟩

/-- **`Stash` across the solution's parse**: `CDECL` unchanged, `DLP` kept up to its old top
(`DLPKeep`), of the same size, its new top inside. -/
theorem Stash.front {m m' : Mem} {pre : PreludeIx} {rC : ParseResultD} (h : Stash m pre rC)
    (hc : m'.arr64 CDECL = m.arr64 CDECL) (hk : DLPKeep m m')
    (hsz : (m'.arr64 DLP).size = (m.arr64 DLP).size) (htop : dtop m' + 1 ≤ (m'.arr64 DLP).size) :
    Stash m' pre rC := by
  have hP : ∀ j, 0 < j → j < 1 + ((m.arr64 DLP)[0]?.getD 0).toNat →
      (m'.arr64 DLP)[j]? = (m.arr64 DLP)[j]? := fun j h0 hj => hk.1 j h0 (by simp only [dtop]; omega)
  refine ⟨?_, ?_⟩
  · rw [hc]; exact h.decls.congr h.decls.dsize h.decls.room hsz (fun _ _ => rfl) hP hk.2 htop
  · intro x hx; rw [hc]; exact recOK_congrP (h.rok x hx) (h.decls.recs x hx) fun j h0 hj => hk.1 j h0 hj

/-! ## The stages' relations with the frame -/

/-- A relational spec with the stage's write set, from the start memory `m₀`. -/
theorem RelSpec.withFrame {p : Prog} {f : FnName} {Pre : Mem → Prop} {Post : List Word → Mem → Prop}
    {A : List TieredArray} {C : List Word} (h : RelSpec p f Pre Post)
    (hfr : ∀ n (s₀ : St), ⦃fun s => s = s₀⦄ invoke p (exec p n) f []
      ⦃fun _ s' => MemFrame A C s₀.mem s'.mem; ⊤⦄) (m₀ : Mem) :
    RelSpec p f (fun m => m = m₀ ∧ Pre m) (fun r m => Post r m ∧ MemFrame A C m₀ m) := by
  intro n hn s₀ ⟨hm, hP⟩
  subst hm
  exact triple_post (triple_and (h n hn s₀ hP) (hfr n s₀)) fun _ _ ⟨⟨hl, h1⟩, h2⟩ => ⟨hl, h1, h2⟩

/-- `R4` across a memory with the same word arrays and bytes (the mode word set). -/
theorem R4.frame0 {l m m' : Mem} {pb : ByteArray} {pre : PreludeIx} {a : AState}
    (h : R4 l m pb pre a) (hf : MemFrame [] [] m m') (hb : m'.bytes = m.bytes) : R4 l m' pb pre a := by
  refine ⟨⟨⟨hb.trans h.since.keep.1, fun x => (hf.size x).trans (h.since.keep.2 x)⟩, h.since.caps,
    h.since.pbpre, h.since.frame.trans ((hf.mono (by simp) (by simp)))⟩,
    h.arena.frameHi hf (by simp) (by simp), h.sdr.frame hf (by simp) (by simp), ?_,
    h.pf.frame hf (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), h.twin,
    h.hz.frame hf (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
    h.rok.frame hf (by simp) (by simp), h.mode.frame hf (by simp) (by simp)⟩
  rw [hf.ctl 240 (by simp)]; exact h.np

/-! ## The memory predicates between mode `5`'s stages -/

section preds
variable (bC bS pb : ByteArray) (sz : TieredArray → Nat)

/-- Before the solution's `front_run`. -/
def QS4 (m : Mem) : Prop :=
  ∃ sA pre sB rC sC, CmpPfx1 bC sA pre sB rC sC ∧ R4 (loadMem bS pb sz) m pb pre sC ∧ Stash m pre rC

/-- After the solution's `front_run`. -/
def QS5 (m : Mem) : Prop :=
  ∃ sA pre sB rC sC rS sC', CmpPfx1 bC sA pre sB rC sC ∧ parseChunks [bS] sC = .ok (.ok rS, sC') ∧
    R5 (loadMem bS pb sz) m pb pre rS sC' ∧ Stash m pre rC

/-- After the solution's `prepare_prelude`. -/
def QS6 (m : Mem) : Prop :=
  ∃ sA pre sB rC sC rS sC' dsS sD, CmpPfx2 bC bS sA pre sB rC sC rS sC' dsS sD ∧
    R6 (loadMem bS pb sz) m pb dsS sD ∧ Stash m pre rC

/-- After `intern_all_pins`. -/
def QS7 (m : Mem) : Prop :=
  ∃ sA pre sB rC sC rS sC' dsS sD pins ipins sE, CmpPfx2 bC bS sA pre sB rC sC rS sC' dsS sD ∧
    internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE) ∧
    R7 (loadMem bS pb sz) m pb dsS ipins sE ∧ Stash m pre rC

end preds

theorem frontStageC_checker (bC bS pb : ByteArray) (sz : TieredArray → Nat)
    (h64 : System.Platform.numBits = 64) (hb : bS.size < 2 ^ 63) :
    StageSpec checkerProg "front_run" (QS4 bC bS pb sz) fun r m => r.headD 0 = 0 → QS5 bC bS pb sz m :=
  StageSpec.of_rel (fun x : Mem × PreludeIx × AState => fun m => m = x.1 ∧ R4 (loadMem bS pb sz) m pb x.2.1 x.2.2) _
    (fun x => frontStageD_checker h64 bS pb hb sz x.2.1 x.2.2 x.1)
    fun m ⟨sA, pre, sB, rC, sC, hpx, h4, hst⟩ => ⟨(m, pre, sC), ⟨rfl, h4⟩, fun _ m' h h0 => by
      obtain ⟨rS, sC', st, hp, h5, -, -, hk, hke, hsf⟩ := h h0
      refine ⟨sA, pre, sB, rC, sC, rS, sC', hpx, hp, h5, hst.front ?_ hk (hke.2 _) ?_⟩
      · exact hsf.arr _ (by decide +kernel) (by decide)
      · have := h5.decls.ptop; simp only [dtop]; omega⟩

theorem prepareStageC_checker (bC bS pb : ByteArray) (sz : TieredArray → Nat) :
    StageSpec checkerProg "prepare_prelude" (QS5 bC bS pb sz) fun _ => QS6 bC bS pb sz :=
  StageSpec.of_rel (fun x : Mem × PreludeIx × ParseResultD × AState =>
      fun m => m = x.1 ∧ R5 (loadMem bS pb sz) m pb x.2.1 x.2.2.1 x.2.2.2) _
    (fun x => (prepareStage_checker bS pb sz x.2.1 x.2.2.1 x.2.2.2).withFrame
      (fun n s₀ => stageFrame_prepare_prelude n s₀) x.1)
    fun m ⟨sA, pre, sB, rC, sC, rS, sC', hpx, hp, h5, hst⟩ => ⟨(m, pre, rS, sC'), ⟨rfl, h5⟩,
      fun _ m' ⟨⟨dsS, sD, hD, h6⟩, hf⟩ => ⟨sA, pre, sB, rC, sC, rS, sC', dsS, sD, ⟨hpx, hp, hD⟩, h6,
        hst.frame hf (by decide +kernel) (by decide +kernel)⟩⟩

theorem pinsStageC_checker (bC bS pb : ByteArray) (sz : TieredArray → Nat) (hpb : pb.size < 2 ^ 63) :
    StageSpec checkerProg "intern_all_pins" (QS6 bC bS pb sz) fun _ => QS7 bC bS pb sz :=
  StageSpec.of_rel (fun x : Mem × Array IDeclaration × AState =>
      fun m => m = x.1 ∧ PinsPre x.2.2 ∧ R6 (loadMem bS pb sz) m pb x.2.1 x.2.2)
    (fun x _ m => (∃ pins ipins a', internAllPins pins maxNatSizeDefault x.2.2 = .ok (ipins, a') ∧
        R7 (loadMem bS pb sz) m pb x.2.1 ipins a') ∧
      MemFrame stageA_intern_all_pins stageC_intern_all_pins x.1 m)
    (fun x n hn s₀ ⟨hm, hpp, h6⟩ =>
      ((pinsStage_gen bS pb sz hpb x.2.1 x.2.2 hpp).withFrame
        (fun n s₀ => stageFrame_intern_all_pins n s₀) x.1) n hn s₀ ⟨hm, h6⟩)
    fun m ⟨sA, pre, sB, rC, sC, rS, sC', dsS, sD, hpx, h6, hst⟩ => ⟨(m, dsS, sD),
      ⟨rfl, PinsPre.cmp hpx, h6⟩, fun _ m' ⟨⟨pins, ipins, sE, hE, h7⟩, hf⟩ =>
        ⟨sA, pre, sB, rC, sC, rS, sC', dsS, sD, pins, ipins, sE, hpx, hE, h7,
          hst.frame hf (by decide +kernel) (by decide +kernel)⟩⟩

end L.Checker
