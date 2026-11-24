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

/-- **A run of `check_jobs` keeps** the stream index's rows and `FIRSTS`, the pin table, the
solution's rows, and the index's, frozen and solution's `CTL` words. -/
theorem cq_jobs_keep {n : Nat} {vs : List Word} {m m' : Mem} {rs : List Word}
    (h : run checkerProg n "check_jobs" vs m = .ok (rs, m')) :
    MemFrame cdA cdC m m' ∧ m'.bytes = m.bytes :=
  have ⟨_, hF, _, hc⟩ := checkerProg_jobsW
  run_memFrame hc hF h

end L.Checker
