module

public import ConAgua.Checker.JobsClosed
meta import ConAgua.Checker.JobsClosed
import all ConAgua.Arena.Abs1
import all ConAgua.Arena.BasisL
import all ConAgua.Arena.IndDeclConsts
import all ConAgua.Arena.IndStream
import all ConAgua.Arena.AppStore
import all ConAgua.Arena.ArRange
import all ConAgua.Arena.ArRangeSpec
import all ConAgua.Arena.BVarStore
import all ConAgua.Arena.BvarB
import all ConAgua.Arena.CheckerL
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.ConsPresize
import all ConAgua.Arena.ConstStore
import all ConAgua.Arena.ConstsResolveF
import all ConAgua.Arena.CoreCaches
import all ConAgua.Arena.CoreLevels
import all ConAgua.Arena.CoreWalks
import all ConAgua.Arena.DeclAndPin
import all ConAgua.Arena.DeclApd
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.DeclArmsCanon
import all ConAgua.Arena.DeclArmsNat
import all ConAgua.Arena.DeclStep
import all ConAgua.Arena.DefEq
import all ConAgua.Arena.Env
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.FVarRange
import all ConAgua.Arena.FVarStore
import all ConAgua.Arena.ForallStore
import all ConAgua.Arena.Freeze
import all ConAgua.Arena.HasFvar
import all ConAgua.Arena.ImaxStore
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.IndParts
import all ConAgua.Arena.IotaFrame
import all ConAgua.Arena.IotaRel
import all ConAgua.Arena.JustifyIface
import all ConAgua.Arena.Needs
import all ConAgua.Arena.Justify
import all ConAgua.Arena.JustifySide
import all ConAgua.Checker.CompareEntry
import all ConAgua.Arena.FreezeCmp
import all ConAgua.Checker.CmpSeqEntry
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos2
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.Infer
import all ConAgua.Arena.InferFieldSort
import all ConAgua.Arena.Inst1
import all ConAgua.Arena.Inst1Spec
import all ConAgua.Arena.InstLP
import all ConAgua.Arena.InstList
import all ConAgua.Arena.InstListSpec
import all ConAgua.Arena.Knot
import all ConAgua.Arena.LamStore
import all ConAgua.Arena.LetStore
import all ConAgua.Arena.LevelApd
import all ConAgua.Arena.LevelEquiv
import all ConAgua.Arena.LevelHeap
import all ConAgua.Arena.LevelIntern
import all ConAgua.Arena.LevelLeq
import all ConAgua.Arena.LevelSimp
import all ConAgua.Arena.LevelStore
import all ConAgua.Arena.LevelSubst
import all ConAgua.Arena.LevelSubstL
import all ConAgua.Arena.LevelSubstLP
import all ConAgua.Arena.LevelZero
import all ConAgua.Arena.LiftL
import all ConAgua.Arena.LsStore
import all ConAgua.Arena.MaxStore
import all ConAgua.Arena.MemoLib
import all ConAgua.Arena.NAnonStore
import all ConAgua.Arena.NNumStore
import all ConAgua.Arena.NStrStore
import all ConAgua.Arena.NatAdd
import all ConAgua.Arena.NatLeaf
import all ConAgua.Arena.NatArms
import all ConAgua.Arena.NatBits
import all ConAgua.Arena.NatCmp
import all ConAgua.Arena.NatDiv
import all ConAgua.Arena.NatDivKstep
import all ConAgua.Arena.NatDivSubmul
import all ConAgua.Arena.NatDivWord
import all ConAgua.Arena.NatGcd
import all ConAgua.Arena.NatMul
import all ConAgua.Arena.NatPow
import all ConAgua.Arena.NatShl
import all ConAgua.Arena.NatShr
import all ConAgua.Arena.NatSub
import all ConAgua.Arena.ParamStore
import all ConAgua.Arena.Pins
import all ConAgua.Arena.Prelude
import all ConAgua.Arena.ProjStore
import all ConAgua.Arena.PropRead
import all ConAgua.Arena.RecCheck
import all ConAgua.Arena.RecClass
import all ConAgua.Arena.RecGen
import all ConAgua.Arena.Refine
import all ConAgua.Arena.Rom
import all ConAgua.Arena.RomCI
import all ConAgua.Arena.RomExpr
import all ConAgua.Arena.RomItems
import all ConAgua.Arena.RomLevel
import all ConAgua.Arena.RomLevels
import all ConAgua.Arena.RomPins
import all ConAgua.Arena.Scratch
import all ConAgua.Arena.SortStore
import all ConAgua.Arena.Store
import all ConAgua.Arena.StrLit
import all ConAgua.Arena.StripTele
import all ConAgua.Arena.StubInd
import all ConAgua.Arena.StubNames
import all ConAgua.Arena.TeleLift
import all ConAgua.Arena.Walk
import all ConAgua.Arena.WalkLeaves
import all ConAgua.Arena.WalkLift
import all ConAgua.Arena.WalkScope
import all ConAgua.Arena.WhnfCore
import all ConAgua.Arena.WhnfCoreApp
import all ConAgua.Arena.WhnfDelta
import all ConAgua.Arena.WhnfEntry
import all ConAgua.Arena.WhnfIota
import all ConAgua.Arena.WhnfIotaRec
import all ConAgua.Arena.WhnfM2C
import all ConAgua.Arena.WhnfProj
import all ConAgua.Arena.WhnfSpineArgs
import all ConAgua.Arena.WhnfSpineRefine
import all ConAgua.Arena.ZeroStore
import all ConAgua.Checker.Entry
import all ConAgua.Checker.Hoist
import all ConAgua.Checker.Prelude
import all ConAgua.Checker.Presize
import all ConAgua.Front.Apply
import all ConAgua.Front.ApplyDecl
import all ConAgua.Front.ApplyExpr
import all ConAgua.Front.Driver
import all ConAgua.Front.Fields
import all ConAgua.Front.FieldsDecl
import all ConAgua.Front.IdTable
import all ConAgua.Front.IndApply
import all ConAgua.Front.IndFields
import all ConAgua.Front.Line
import all ConAgua.Front.LineRec
import all ConAgua.Front.NatDec
import all ConAgua.Front.Unescape
import all ConAgua.L.Examples
import all ConAgua.Rom.CIConst
import all ConAgua.Rom.CIRead
import all ConAgua.Rom.PinRead
import all ConAgua.Rom.PinReadSpec
import all ConAgua.Scan.Key
import all ConAgua.Scan.Leaves
import all ConAgua.Scan.Line
import all ConAgua.Scan.Lit
import all ConAgua.Scan.Member
import all ConAgua.Scan.Records
import all ConAgua.Scan.Str
import all ConAgua.Scan.Utf8
import all ConAgua.Scan.Values
import all ConAgua.Arena.NatSized

@[expose] public section

/-!
# The jobs' write set at the checker's program (lane compare2, the in-place sequential run)

`check_jobs` with its call closure (`check_decl`'s and `check_record_sol`'s, `cdFns`, and the
jobs' loop, the bracket, the `And` pin: `cqJobFns`) stores only where `cdA`/`cdC` allow
(`checkerProg_jobsW`, as `checkerProg_cdW`). So a run of the solution's jobs in place leaves the
stream index's rows (`EIX*`, `TIX*`, `FIRSTS`), the solution's rows (`SIX*`, `STX*`, `MAT*`), the
pin table and the `CTL` words `128`, `162‥173`, `224‥226` alone (`cq_jobs_keep`): what the
challenge's view reads of the frozen image after the solution's phase.
-/

namespace L.Checker

open L L.Arena L.Compiler

/-- `check_jobs`' call closure in the checker's program: `cdFns` and the jobs' own functions. -/
def cqJobFns : List FnName :=
  ["check_jobs", "record_job", "scratch_enter", "scratch_drop", "scratch_reset", "iw_reset",
   "and_pin_ok", "rom_and_pin", "and_block_named", "from_le", "canon_rules_eq", "ci_canon_rec",
   "canon_level_list_eq", "canon_levels_eq", "canon_level_eq", "canon_expr_eq", "canon_names_go",
   "canon_names", "canon_ctx", "cv_canon_eq", "ci_canon_defn", "ci_canon_eq", "canon_eq_list"] ++
  cdFns

names_tree cqJobTree : cqJobFns

/-- Every function of the checker passes the jobs' per-function check. -/
prog_all checkerProg_cqJobChk : checkerProg (wsChk CTL cdPa cdPc cqJobTree)

/-- **`check_jobs`' write set**: `check_decl`'s. -/
theorem checkerProg_jobsW : ∃ F, "check_jobs" ∈ F ∧ "record_job" ∈ F ∧
    closedA checkerProg cdA cdC F = true :=
  ⟨cqJobFns, List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self,
    closedW_of_all cqJobTree.eq cdPa_mem cdPc_mem checkerProg_cqJobChk⟩

/-- The arrays a job never stores to: the stream index's rows and `FIRSTS`, the pin table, the
solution's rows. -/
theorem cq_not_cdA {b : TieredArray} (h : IdxArr b = true ∨ b = PINS ∨ SolArr b = true) : b ∉ cdA :=
  fun hm => by
    have := (List.mem_filter.mp hm).2
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
    rcases h with h | h | h
    · rw [this.1.1] at h; cases h
    · exact this.1.2 h
    · rw [this.2] at h; cases h

/-- The `CTL` words a job never stores to: the index's counter, the frozen index's words, the
solution's words. -/
theorem cq_not_cdC {x : Word} (h : x.toNat = 128 ∨ (162 ≤ x.toNat ∧ x.toNat ≤ 173) ∨
    (224 ≤ x.toNat ∧ x.toNat ≤ 226)) : x ∉ cdC := fun hm => by
  simp only [cdC, List.mem_map, List.mem_filter, List.mem_range] at hm
  obtain ⟨y, ⟨hy0, h1⟩, e⟩ := hm
  have hy : x.toNat = y := by rw [← e]; simp; omega
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h1
  omega

/-! ## With the flag off: the walks' memos kept

`record_job` dispatches on the flag `CTL[224]`: with the flag `0` it calls `check_decl`, never
`check_record_sol`, whose closure alone stores to the walks' memos (`NDM`, `CSM`, `CTL[220‥223]`).
So the solution's jobs (`J = none`) keep them (`cq_checkJobsE_frame0`): what the challenge's jobs,
run after them in place, need of the memos (`WalkMem`). -/

/-- The callees of `record_job` on the flag-`0` path and their closures: `cqJobFns` without the
jobs' loop, `record_job` and `check_record_sol`'s own closure. -/
def cqCrsOnly : List FnName :=
  ["check_jobs", "record_job", "check_record_sol", "builtin_axiom_name", "check_justified",
   "cone_entry", "cone_go", "cone_push", "copy_b", "cs_clear", "cs_find", "cs_put", "entry_needs",
   "is_stmt_kind", "justifiable", "justify_why", "levels_renaming", "lit_needs", "mates_get",
   "nd_clear", "nd_find", "nd_put", "needs_const", "needs_expr", "needs_exprs", "needs_go",
   "needs_name", "needs_names", "needs_names_iw", "needs_reset", "needs_rule", "needs_rules",
   "needs_table", "pin_footprint", "pin_footprint_nat", "pin_footprint_reduce", "rec_names",
   "refines_b", "same_cv_up_to_levels", "sol_find", "sol_find_table", "sol_row_get", "sol_tbl_get",
   "tbl_beq_p", "tbl_eq"]

/-- `record_job`'s callees on the flag-`0` path (first) and their closures. -/
def cqF0 : List FnName :=
  ["scratch_enter", "iw_reset", "from_le", "and_pin_ok", "check_decl", "scratch_drop"] ++
    cqJobFns.filter fun f => !cqCrsOnly.contains f

names_tree cqF0Tree : cqF0

/-- The compared run's stash arrays (`223‥230`: the first parse's records, the solution's and the
challenge's copies), which no job stores to. -/
def cqStash (b : TieredArray) : Bool := decide (223 ≤ b.arr) && decide (b.arr ≤ 230)

/-- The flag-`0` jobs' arrays: `cdA` but the walks' memos and the stash arrays. -/
def cqA : List TieredArray := cdA.filter fun b => b != (NDM : TieredArray) && b != (CSM : TieredArray) &&
  !cqStash b

/-- The flag-`0` jobs' `CTL` words: `cdC` but the walks' memos' words `220‥223`. -/
def cqC : List Word := cdC.filter fun x => decide (x.toNat < 220) || decide (223 < x.toNat)

def cqPa (b : TieredArray) : Bool := cdPa b && b != (NDM : TieredArray) && b != (CSM : TieredArray) &&
  !cqStash b
def cqPc (x : Word) : Bool := cdPc x && (decide (x.toNat < 220) || decide (223 < x.toNat))

theorem cqPa_mem (b : TieredArray) (h : cqPa b = true) : b ∈ cqA := by
  simp only [cqPa, Bool.and_eq_true] at h
  exact List.mem_filter.mpr ⟨cdPa_mem b h.1.1.1, by simp only [Bool.and_eq_true]; exact ⟨⟨h.1.1.2, h.1.2⟩, h.2⟩⟩

theorem cqPc_mem (x : Word) (h : cqPc x = true) : x ∈ cqC := by
  simp only [cqPc, Bool.and_eq_true] at h
  exact List.mem_filter.mpr ⟨cdPc_mem x h.1, h.2⟩

/-- Every function of the checker passes the flag-`0` jobs' per-function check. -/
prog_all checkerProg_cqF0Chk : checkerProg (wsChk CTL cqPa cqPc cqF0Tree)

/-- **The flag-`0` jobs' callees' write set.** -/
theorem checkerProg_cqF0W : closedA checkerProg cqA cqC cqF0 = true :=
  closedW_of_all cqF0Tree.eq cqPa_mem cqPc_mem checkerProg_cqF0Chk

theorem cq_not_cqC {x : Word} (h : x ∉ cdC ∨ (220 ≤ x.toNat ∧ x.toNat ≤ 223)) : x ∉ cqC := fun hm => by
  have := List.mem_filter.mp hm
  rcases h with h | h
  · exact h this.1
  · have h2 := this.2; simp only [Bool.or_eq_true, decide_eq_true_eq] at h2; omega

theorem cq_not_cqA {b : TieredArray} (h : b ∉ cdA ∨ b = (NDM : TieredArray) ∨ b = (CSM : TieredArray) ∨
    cqStash b = true) : b ∉ cqA := fun hm => by
  have := List.mem_filter.mp hm
  rcases h with h | rfl | rfl | h
  · exact h this.1
  · simp at this
  · simp at this
  · have h2 := this.2; rw [h] at h2; simp at h2

theorem cq_ctl_mem {x : Word} (h : cqPc x = true) : x ∈ cqC := cqPc_mem x h

/-- A call of a function of a closed set is a frame of the set's write set. -/
theorem cq_callE_frame {p : Prog} {A : List TieredArray} {C : List Word} {F : List FnName}
    (hcl : closedA p A C F = true) {f : FnName} (hf : f ∈ F) {n : Nat} {vs : List Word}
    {m m' : Mem} {r : List Word} (h : callE p n f vs m = .ok (r, m')) : MemFrame A C m m' := by
  obtain ⟨s, hs, hfr, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (invoke_memFrame hcl n hf vs ⟨m, Locals.init []⟩) (callW_of_callE h)
  rw [hs] at hfr; exact hfr

theorem cq_setCtl_frame {x : Word} (hx : cqPc x = true) (m : Mem) (v : Word) :
    MemFrame cqA cqC m (m.set64 CTL x v) :=
  (MemFrame.setCtl m x v).mono (by simp) (fun y hy => by
    simp only [List.mem_singleton] at hy; subst hy; exact cqPc_mem _ hx)

/-- **`record_job` with the flag off stores only to the flag-`0` write set.** -/
theorem cq_recordJobE_frame0 {p : Prog} (hcl : closedA p cqA cqC cqF0 = true) {n : Nat} {m m' : Mem}
    {k r : Word} (h : recordJobE p n m k = .ok (r, m')) (h224 : rdW (m.arr64 CTL) 224 = 0) :
    MemFrame cqA cqC m m' := by
  have n224 : (224 : Word) ∉ cqC := cq_not_cqC (.inl (cq_not_cdC (by decide)))
  have mem : ∀ f, f ∈ ["scratch_enter", "iw_reset", "from_le", "and_pin_ok", "check_decl",
      "scratch_drop"] → f ∈ cqF0 := fun f hf => List.mem_append_left _ hf
  rcases n with _ | n
  · simp [recordJobE] at h
  simp only [recordJobE] at h
  rcases c1 : callE p n "scratch_enter" [] m with e | ⟨r1, m1⟩
  · rw [c1] at h; simp [recordJobE.k_scratch_enter] at h
  rw [c1] at h; simp only [recordJobE.k_scratch_enter] at h
  have f1 := (cq_callE_frame hcl (mem _ (by simp)) c1).trans (cq_setCtl_frame (x := 130) (by decide) m1 0)
  generalize m1.set64 CTL 130 0 = m1' at h f1
  rcases c2 : callE p n "iw_reset" [] m1' with e | ⟨r2, m2⟩
  · rw [c2] at h; simp [recordJobE.k_iw_reset] at h
  rw [c2] at h; simp only [recordJobE.k_iw_reset] at h
  have f2 := f1.trans (cq_callE_frame hcl (mem _ (by simp)) c2)
  split at h; · cases h
  split at h; · cases h
  have f3 : MemFrame cqA cqC m (((m2.set64 CTL 133 (rdW (m2.arr64 CTL) 133 + 1)).set64 CTL 134
      (rdW ((m2.set64 CTL 133 (rdW (m2.arr64 CTL) 133 + 1)).arr64 FIRSTS) k)).set64 CTL 135 k) :=
    ((f2.trans (cq_setCtl_frame (x := 133) (by decide) _ _)).trans
      (cq_setCtl_frame (x := 134) (by decide) _ _)).trans (cq_setCtl_frame (x := 135) (by decide) _ _)
  generalize (((m2.set64 CTL 133 (rdW (m2.arr64 CTL) 133 + 1)).set64 CTL 134
    (rdW ((m2.set64 CTL 133 (rdW (m2.arr64 CTL) 133 + 1)).arr64 FIRSTS) k)).set64 CTL 135 k) = m3 at h f3
  generalize rdW ((m2.set64 CTL 133 (rdW (m2.arr64 CTL) 133 + 1)).arr64 FIRSTS) k = c at h
  rcases c4 : callE p n "from_le" [rdW (m3.arr64 CTL) 172, c] m3 with e | ⟨r4, m4⟩
  · rw [c4] at h; simp [recordJobE.k_from_le] at h
  rw [c4] at h; simp only [recordJobE.k_from_le] at h
  have f4 := (f3.trans (cq_callE_frame hcl (mem _ (by simp)) c4)).trans (cq_setCtl_frame (x := 160) (by decide) m4 (r4.headD 0))
  generalize m4.set64 CTL 160 (r4.headD 0) = m4' at h f4
  rcases c5 : callE p n "from_le" [rdW (m4'.arr64 CTL) 173, c] m4' with e | ⟨r5, m5⟩
  · rw [c5] at h; simp [recordJobE.k_from_le_2] at h
  rw [c5] at h; simp only [recordJobE.k_from_le_2] at h
  have f5 := (f4.trans (cq_callE_frame hcl (mem _ (by simp)) c5)).trans (cq_setCtl_frame (x := 161) (by decide) m5 (r5.headD 0))
  generalize m5.set64 CTL 161 (r5.headD 0) = m5' at h f5
  rcases c6 : callE p n "and_pin_ok" [k] m5' with e | ⟨r6, m6⟩
  · rw [c6] at h; simp [recordJobE.k_and_pin_ok] at h
  rw [c6] at h; simp only [recordJobE.k_and_pin_ok] at h
  have f6 := f5.trans (cq_callE_frame hcl (mem _ (by simp)) c6)
  split at h; · cases h
  have e224 : rdW (m6.arr64 CTL) 224 = 0 := by rw [f6.ctl 224 n224]; exact h224
  rw [ite_eq_right_of_eq_false _ _ (by simp [e224])] at h
  rcases c7 : callE p n "check_decl" [k, 0] m6 with e | ⟨r7, m7⟩
  · rw [c7] at h; simp [recordJobE.k_check_record_sol] at h
  rw [c7] at h; simp only [recordJobE.k_check_record_sol, recordJobE.j1] at h
  have f7 := f6.trans (cq_callE_frame hcl (mem _ (by simp)) c7)
  rcases c8 : callE p n "scratch_drop" [] m7 with e | ⟨r8, m8⟩
  · rw [c8] at h; simp [recordJobE.k_scratch_drop] at h
  rw [c8] at h; simp only [recordJobE.k_scratch_drop, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact (f7.trans (cq_callE_frame hcl (mem _ (by simp)) c8)).trans (cq_setCtl_frame (x := 130) (by decide) m8 0)

/-- **`check_jobs`' loop with the flag off stores only to the flag-`0` write set** (the flag is
not in it, so every job of the loop runs with it off). -/
theorem cq_checkJobsLoop_frame0 {p : Prog} (hcl : closedA p cqA cqC cqF0 = true)
    (hrj : p.lookup "record_job" = some recordJobL) :
    ∀ (n : Nat) (m : Mem) (j hi : Word) (m' : Mem), checkJobsE.loop1 p n m j hi = .ok m' →
      rdW (m.arr64 CTL) 224 = 0 → MemFrame cqA cqC m m' := by
  have n224 : (224 : Word) ∉ cqC := cq_not_cqC (.inl (cq_not_cdC (by decide)))
  intro n
  induction n with
  | zero => intro m j hi m' h; rw [checkJobsE.loop1.eq_1] at h; cases h
  | succ n ih =>
    intro m j hi m' h h224
    by_cases g : j < hi
    · rw [checkJobsE.loop1.arm1 _ _ _ _ _ g] at h
      rcases c : callE p n "record_job" [j] m with e | ⟨r, m1⟩
      · rw [c, checkJobsE.k_record_job.none] at h; cases h
      rw [c, checkJobsE.k_record_job.arm1] at h
      obtain ⟨s', hs', -, hE⟩ := triple_of_callE (recordJob_specE p hrj n ⟨m, Locals.init []⟩ j) c
      rw [hs'] at hE
      have f1 := cq_recordJobE_frame0 hcl hE h224
      exact f1.trans (ih m1 (j + 1) hi m' h (by rw [f1.ctl 224 n224]; exact h224))
    · rw [checkJobsE.loop1.arm2 _ _ _ _ _ g] at h; cases h; exact MemFrame.refl _ _ _

/-- **A run of `check_jobs` with the flag off stores only to the flag-`0` write set**: it keeps
the walks' memos (`NDM`, `CSM`, `CTL[220‥223]`) besides what `cq_jobs_keep` keeps. -/
theorem cq_checkJobs_frame0 {p : Prog} (hcl : closedA p cqA cqC cqF0 = true)
    (hrj : p.lookup "record_job" = some recordJobL) (hcj : p.lookup "check_jobs" = some checkJobsL)
    {n : Nat} {j hi : Word} {m m' : Mem} {r : List Word}
    (h : callE p n "check_jobs" [j, hi] m = .ok (r, m')) (h224 : rdW (m.arr64 CTL) 224 = 0) :
    MemFrame cqA cqC m m' := by
  obtain ⟨s', hs', -, hE⟩ := triple_of_callE (checkJobs_specE p hcj n ⟨m, Locals.init []⟩ j hi) h
  rw [hs'] at hE
  rcases n with _ | n
  · simp [checkJobsE] at hE
  simp only [checkJobsE] at hE
  rcases c : checkJobsE.loop1 p (n + 1) m j hi with e | m1
  · rw [c] at hE; simp [checkJobsE.k_loop1] at hE
  rw [c] at hE; simp only [checkJobsE.k_loop1, Except.ok.injEq, Prod.mk.injEq] at hE
  rw [← hE.2]
  exact cq_checkJobsLoop_frame0 hcl hrj _ _ _ _ _ c h224

end L.Checker
