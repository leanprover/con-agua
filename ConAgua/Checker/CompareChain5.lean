module

public import ConAgua.Checker.CompareTwinFacts
import ConAgua.Arena.GrindAttr
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.HoistWalkRef
import ConAgua.Checker.HoistClosureL
import ConAgua.Checker.IndDeclConstsProg
import ConAgua.L.GrindAttr
import all ConAgua.Checker.Entry
import all ConAgua.Checker.CompareEntry
import ConAgua.Checker.CheckARun
meta import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.LoopProgTac

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

set_option experimental.vcgen true

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

/-- **What mode `6`'s preparation needs beyond the stage relation**: the prelude's record count
`CTL[240]`, the hoist's memos well formed. -/
structure Keep6 (m : Mem) (pre : PreludeIx) : Prop where
  np : (rdW (m.arr64 CTL) 240).toNat = pre.decls.size
  seen : ∃ s, SeenR m s
  nix : ∃ idx, NixR m idx

theorem Keep6.frame {A : List TieredArray} {C : List Word} {m m' : Mem} {pre : PreludeIx}
    (h : Keep6 m pre) (hf : MemFrame A C m m') (h1 : (HSEEN : TieredArray) ∉ A)
    (h2 : (HNIX : TieredArray) ∉ A) (c1 : (73 : Word) ∉ C) (c2 : (75 : Word) ∉ C) (c3 : (240 : Word) ∉ C) :
    Keep6 m' pre := by
  obtain ⟨hn, ⟨s, hs⟩, ⟨idx, hx⟩⟩ := h
  exact ⟨by rw [hf.ctl 240 c3]; exact hn, ⟨s, memoRG_frame hsSch hsSch_wf bmKey _ A C h1 c1 m m' hf _ hs⟩,
    ⟨idx, memoRV_frame hnSch hnSch_wf nmKey _ A C h2 c2 m m' hf (fun _ _ h => h) idx hx⟩⟩

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
    R6 (loadMem bS pb sz) m pb dsS sD ∧ Stash m pre rC ∧ (rdW (m.arr64 CTL) 240).toNat = pre.decls.size

/-- After `intern_all_pins`. -/
def QS7 (m : Mem) : Prop :=
  ∃ sA pre sB rC sC rS sC' dsS sD pins ipins sE, CmpPfx2 bC bS sA pre sB rC sC rS sC' dsS sD ∧
    internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE) ∧
    R7 (loadMem bS pb sz) m pb dsS ipins sE ∧ Stash m pre rC ∧ Keep6 m pre

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
        hst.frame hf (by decide +kernel) (by decide +kernel),
        by rw [hf.ctl 240 (stageC_prepare_prelude_off _ (by decide))]; exact h5.np⟩⟩

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
    fun m ⟨sA, pre, sB, rC, sC, rS, sC', dsS, sD, hpx, h6, hst, hnp⟩ => ⟨(m, dsS, sD),
      ⟨rfl, PinsPre.cmp hpx, h6⟩, fun _ m' ⟨⟨pins, ipins, sE, hE, h7⟩, hf⟩ =>
        ⟨sA, pre, sB, rC, sC, rS, sC', dsS, sD, pins, ipins, sE, hpx, hE, h7,
          hst.frame hf (by decide +kernel) (by decide +kernel),
          Keep6.frame ⟨hnp, h6.seen, h6.nix⟩ hf (by decide +kernel) (by decide +kernel)
            (by decide +kernel) (by decide +kernel) (stageC_intern_all_pins_off _ (by decide))⟩⟩

/-! ## The solution's index build -/

/-- **The compared run's twin up to the solution's index**: `TwinComparesAccepts`' first states. -/
structure PhaseS (bC bS : ByteArray) where
  pins : List ConLeche.NatOpPinSet
  sA : AState
  pre : PreludeIx
  sB : AState
  rC : ParseResultD
  sC : AState
  rS : ParseResultD
  sC' : AState
  dsS : Array IDeclaration
  sD : AState
  ipins : List INatOpPinSet
  sE : AState
  IS : IStreamIndex
  sF : AState
  pfx : CmpPfx2 bC bS sA pre sB rC sC rS sC' dsS sD
  pinsR : internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE)
  idx : buildIndex dsS sE = .ok (.ok IS, sF)

/-- **What an index build leaves** (`FoldAt` at explicit twin values): `R7` at the memory `m₇`
before the build, `BuildR` at the built index after it, the record pool's prefix kept, and the
build's write set. -/
structure FoldOn (b pb : ByteArray) (sz : TieredArray → Nat) (ds : Array IDeclaration)
    (ipins : List INatOpPinSet) (sE : AState) (I : IStreamIndex) (sF : AState) (m₇ m : Mem) : Prop where
  r7 : R7 (loadMem b pb sz) m₇ pb ds ipins sE
  build : BuildR (dnOf sE.store) ds m sF I
  frozen : FrozenR m I
  fsize : I.firsts.size = ds.size
  grow : BKeep m₇ m
  frame : MemFrame biA biC m₇ m
  bytes : m.bytes = m₇.bytes

/-- After the solution's index build: the twin's phase, `FoldOn` and the challenge's records. -/
def FS (bC bS pb : ByteArray) (sz : TieredArray → Nat) (m : Mem) : Prop :=
  ∃ (PS : PhaseS bC bS) (m₇ : Mem), FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m ∧
    Stash m PS.pre PS.rC ∧ Keep6 m PS.pre

theorem buildStageC_checker (bC bS pb : ByteArray) (sz : TieredArray → Nat) (hpb : pb.size < 2 ^ 63)
    (hsz : ∀ s, sz s < 2 ^ 64) :
    ∀ n, n ≤ 2 ^ 62 → ∀ (s₀ : St) (cnt : Word),
      ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "build_index" [cnt]
      ⦃fun _ s' => LocEq s' s₀ ∧ (QS7 bC bS pb sz s₀.mem →
        (∀ h : 0 < (s₀.mem.arr64 L.Front.DECL).size, cnt = (s₀.mem.arr64 L.Front.DECL)[0]) →
        FS bC bS pb sz s'.mem ∧ s'.mem.arr64 L.Front.DECL = s₀.mem.arr64 L.Front.DECL); ⊤⦄ := by
  intro n _ s₀ cnt
  apply M.triple_of_run
  rintro s rs s' rfl hrun
  obtain ⟨F, hF0, hcl⟩ := checkerProg_biW
  obtain ⟨hfr, hby⟩ := M.of_run (P := fun x => x = s) rfl hrun (invoke_memFrame hcl n hF0 [cnt] s)
  obtain ⟨hl, -⟩ := M.of_run (P := fun x => x = s) rfl hrun (callW_spec checkerProg n "build_index" [cnt] s)
  refine ⟨hl, fun hQ hc => ?_⟩
  have hD : s'.mem.arr64 L.Front.DECL = s.mem.arr64 L.Front.DECL :=
    hfr.arr _ (fun h => by simp [biA] at h) (by decide)
  refine ⟨?_, hD⟩
  obtain ⟨sA, pre, sB, rC, sC, rS, sC', dsS, sD, pins, ipins, sE, hpx, hE, h7, hst, hk6⟩ := hQ
  have hctl : 220 ≤ (s.mem.arr64 CTL).size := by
    have := h7.since.caps.2.1
    rw [h7.since.frame.size]; simp only [ctlMin] at this; omega
  have hD0 : 0 < (s.mem.arr64 L.Front.DECL).size := by
    have := h7.since.caps.2.2.1; rw [h7.since.frame.size]; exact this
  have hcnt : cnt.toNat = dsS.size := by
    rw [hc hD0]; have := h7.decls.count; simpa [hD0] using this
  have hPB : s.mem.arr8 L.Rom.PB = pb.data.toList.toArray := by
    rw [h7.since.keep.arr8]; exact loadMem_pb bS pb sz
  rw [← L.Rom.invoke_subPB (bs := pb.data.toList) checkerProg_noSt8PB n _ _ hPB] at hrun
  obtain ⟨I, a', hI, hR', hFz, hsz', hG⟩ := (M.of_run (P := fun x => x = s) rfl hrun
    (buildIndex_refines (checkerProg_idxProgPB pb.data.toList
      (by simpa [RomOK] using hpb) h7.since.pbpre) cnt hcnt n s sE h7.pinsFull (by omega)
      (fun _ hf hl => buildR_of_out hsz (StagesOut.cmp hpx hE) h7 hf hl))).2
  exact ⟨⟨pins, sA, pre, sB, rC, sC, rS, sC', dsS, sD, ipins, sE, I, a', hpx, hE, hI⟩, s.mem,
    ⟨h7, hR', hFz, hsz', hG, hfr, hby⟩, hst.frame hfr (by simp [biA]) (by simp [biA]),
    hk6.frame hfr (by simp [biA]) (by simp [biA]) (not_mem_biC (by decide)) (not_mem_biC (by decide)) (not_mem_biC (by decide))⟩

/-! ## `check` in mode `5` -/

set_option experimental.vcgen true in
/-- **`check`'s dispatch to mode `5`**: with the mode word `5`, `check` is `check_c2()`. -/
theorem check_dispatch5 {p : Prog} (hp : p.lookup "check" = some checkL) (n : Nat) (s₀ : St)
    (P : Word → Mem → Prop)
    (hC : ∀ s₁ : St, ⦃fun s => s = s₁⦄ invoke p (exec p n) "check_c2" []
      ⦃fun r s' => s₁.mem = s₀.mem → P (r.headD 0) s'.mem; ⊤⦄) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check" []
    ⦃fun r s' => s₀.mem.glob MODE = 5 → P (r.headD 0) s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (hC ·),
    (L.invoke_loc p (exec p n) "check_a" [·] ·), (L.invoke_loc p (exec p n) "check_b" [] ·),
    (L.invoke_loc p (exec p n) "check_c1" [] ·), (L.invoke_loc p (exec p n) "check_c3" [] ·)]
  all_goals (try simp only [Sig.retVal, Sig.retOr, L.St.setLoc_mem, List.headD_cons,
    St.setLocs_cons, St.setLocs_nil, St.setLoc_loc] at *)
  all_goals grind [lang_grind]

set_option experimental.vcgen true in
/-- **`check_c2()` from its stages**: the solution's `front_run`, `prepare_prelude`,
`intern_all_pins`, the index build (with its count `DECL[0]`, keeping `DECL`) and
`par_compact(1)`; on a result other than `1` the final memory is the frozen buffer's after an
index build that ended in `F`, and the result is `2^63 + DECL[0]`. -/
theorem checkC2_of_stages {p : Prog} (hp : p.lookup "check_c2" = some checkC2L)
    (hpc : p.lookup "par_compact" = some parCompactL)
    (hfz : ∀ i < frozen.length, p.lookup (fzName i) = some (fzF i))
    {Q4 Q5 Q6 Q7 : Mem → Prop} {F : Mem → Prop}
    (h5 : StageSpec p "front_run" Q4 fun r m => r.headD 0 = 0 → Q5 m)
    (h6 : StageSpec p "prepare_prelude" Q5 fun _ => Q6)
    (h7 : StageSpec p "intern_all_pins" Q6 fun _ => Q7)
    (h8 : ∀ n, n ≤ 2 ^ 62 → ∀ (s₀ : St) (cnt : Word),
      ⦃fun s => s = s₀⦄ invoke p (exec p n) "build_index" [cnt]
      ⦃fun _ s' => LocEq s' s₀ ∧ (Q7 s₀.mem →
        (∀ h : 0 < (s₀.mem.arr64 L.Front.DECL).size, cnt = (s₀.mem.arr64 L.Front.DECL)[0]) →
        F s'.mem ∧ s'.mem.arr64 L.Front.DECL = s₀.mem.arr64 L.Front.DECL); ⊤⦄)
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_c2" []
    ⦃fun r s' => Q4 s₀.mem → r.headD 0 ≠ 1 → PostPC 1 F s'.mem ∧
      ∀ h : 0 < (s'.mem.arr64 L.Front.DECL).size,
        r.headD 0 = (9223372036854775808 : Word) + (s'.mem.arr64 L.Front.DECL)[0];
      ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkC2L]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hn' : n ≤ 2 ^ 62 := by omega
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      (h5 n hn' ·), (h6 n hn' ·), (h7 n hn' ·), (h8 n hn' · ·), (parCompact_stage hpc hfz · F n ·)]
    all_goals (try simp only [Sig.retVal, Sig.retOr, L.St.setLoc_mem, List.headD_cons,
      St.setLocs_cons, St.setLocs_nil, St.setLoc_loc, Cmp.eval, BinOp.eval, ite_true, ite_false, Nat.reduceEqDiff,
      UInt64.toNat_zero, bne_iff_ne, ne_eq, Decidable.not_not] at *)
    all_goals clear h5 h6 h7 h8 hfz hp hpc
    -- gen/ematch raised as in `checkA_of_stages`
    all_goals grind (gen := 30) (ematch := 40) [lang_grind, Locals.init_cons_zero]

/-- **Mode `5`'s end** at its final memory `m'`: the frozen buffer's memory of a memory `m` after
the solution's index build (`FS`: the compared run's twin up to the solution's index, `FoldOn`, the
challenge's records in `CDECL`). -/
def CmpAt5 (bC bS pb : ByteArray) (sz : TieredArray → Nat) (m' : Mem) : Prop :=
  PostPC 1 (FS bC bS pb sz) m'

/-- **Mode `5` in L**: from mode `4`'s end (`CmpAt4`, at its memory `m4`), a run of `check` from
`m4` with the input replaced by the solution's bytes `bS` and the mode word `5` that returns
anything but `1` (a line that did not scan) ends in mode `5`'s end (`CmpAt5`) and returns
`2^63 + |dsS|`, the solution's prepared records' count. -/
theorem checkC2_run (bC bS pb : ByteArray) (sz : TieredArray → Nat) (hin : InputsOK bS pb sz)
    (N : Nat) (hN : N < 2 ^ 62) (m4 : Mem) (h4 : CmpAt4 bC bS pb sz m4) (rs : List Word) (m' : Mem)
    (hrun : L.run checkerProg N "check" [] ((m4.setIn bS.data).setG MODE 5) = .ok (rs, m'))
    (hr : rs.headD 0 ≠ 1) :
    ∃ (PS : PhaseS bC bS) (m₇ m : Mem), FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m ∧
      Stash m PS.pre PS.rC ∧ Keep6 m PS.pre ∧ parCompactOK m 1 = true ∧ m' = parCompactMem m 1 ∧
      rs.headD 0 = 9223372036854775808 + UInt64.ofNat PS.dsS.size := by
  have s5 := frontStageC_checker bC bS pb sz hin.1 hin.2.1
  have s6 := prepareStageC_checker bC bS pb sz
  have s7 := pinsStageC_checker bC bS pb sz hin.2.2.1
  have s8 := buildStageC_checker bC bS pb sz hin.2.2.1 hin.2.2.2
  have hc2 : checkerProg.lookup "check_c2" = some checkC2L := by chk_lk
  have hlc : checkerProg.lookup "check" = some checkL := by chk_lk
  have hpc : checkerProg.lookup "par_compact" = some parCompactL := by chk_lk
  let M5 := (m4.setIn bS.data).setG MODE 5
  have hmode : M5.glob MODE = 5 := by simp [M5, Mem.setG]
  have hQ4 : QS4 bC bS pb sz M5 := by
    obtain ⟨sA, pre, sB, rC, sC, hpx, hR4, hst⟩ := h4
    exact ⟨sA, pre, sB, rC, sC, hpx, hR4.frame0 (memFrame_setG _ _ _) rfl, ⟨hst.decls, hst.rok⟩⟩
  let P : Word → Mem → Prop := fun x m'' => x ≠ 1 → PostPC 1 (FS bC bS pb sz) m'' ∧
    ∀ h : 0 < (m''.arr64 L.Front.DECL).size, x = (9223372036854775808 : Word) + (m''.arr64 L.Front.DECL)[0]
  cases N with
  | zero =>
    exfalso
    refine run_post (Q := fun _ _ => False) hrun ?_
    rw [invoke_eq _ hlc]
    simp only [callFn]
    vcgen [exec] <;> grind
  | succ n =>
    have hn : n ≤ 2 ^ 62 := by omega
    let s₀ : St := { mem := M5, loc := Locals.init [] }
    have hC : ∀ s₁ : St, ⦃fun s => s = s₁⦄ invoke checkerProg (exec checkerProg n) "check_c2" []
        ⦃fun r s' => s₁.mem = s₀.mem → P (r.headD 0) s'.mem; ⊤⦄ := fun s₁ =>
      triple_post (checkC2_of_stages hc2 hpc checkerProg_fz s5 s6 s7 s8 n hn s₁)
        fun _ _ h e => h (by rw [e]; exact hQ4)
    have H := run_post (Q := fun x m'' => s₀.mem.glob MODE = 5 → P (x.headD 0) m'') hrun
      (check_dispatch5 hlc n s₀ P hC)
    obtain ⟨⟨m, ⟨PS, m₇, hF, hst, hk6⟩, hok, rfl⟩, hval⟩ := H hmode hr
    refine ⟨PS, m₇, m, hF, hst, hk6, hok, rfl, ?_⟩
    have hFo := parCompactMem_out m 1
    have hD0 : 0 < (m.arr64 L.Front.DECL).size := by have := hF.build.decls.room; omega
    have eD : (parCompactMem m 1).arr64 L.Front.DECL = m.arr64 L.Front.DECL := hFo.arr _ (by decide)
    have hD0' : 0 < ((parCompactMem m 1).arr64 L.Front.DECL).size := by rw [eD]; exact hD0
    have hc := hF.build.decls.count
    rw [Array.getElem?_eq_getElem hD0, Option.getD_some] at hc
    have key : ∀ (A B : Array Word) (e : A = B) (h1 : 0 < A.size) (h2 : 0 < B.size), A[0] = B[0] := by
      intro A B e _ _; subst e; rfl
    rw [hval hD0', key _ _ eD hD0' hD0, ← hc, UInt64.ofNat_toNat]

end L.Checker
