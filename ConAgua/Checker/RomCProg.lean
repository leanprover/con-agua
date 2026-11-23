module

public import ConAgua.Checker.LoopProgTac
public meta import ConAgua.Checker.LoopProgTac
public import ConAgua.Rom.CIReadSpec
import all ConAgua.Rom.CIConst
import all ConAgua.Rom.CIReadSpec
import all ConAgua.Arena.Abs1
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
import ConAgua.Compiler.Main

@[expose] public section

/-!
# The ROM readers over the constant data at the checker's program (lane `ronsync2`)

`RomCIProg`'s two program facts at `Prog.subPB bs checkerProg`: the generic readers' lookups in
`Prog.viaC romDataLit` of it (`checkerProg_romCVia`) and the renaming (`checkerProg_romCRen`,
by `RenameOK.of_tab`): the readers' callees `romCTabO` are bound in the checker's program, call
none of the readers, and every body of `romCTabR romDataLit ++ romCTabO` calls names of `romCN`
only.
-/

namespace L.Checker

open L L.Rom L.Arena

/-- The functions the ROM readers call (none of them a reader), with their bodies. -/
def romCTabO : Prog :=
  [("intern_nanon", L.Arena.internNAnon),
   ("nanon_find", L.Arena.nanonFind),
   ("nanon_push", L.Arena.nanonPush),
   ("intern_nstr", L.Arena.internNStr),
   ("lit_hash", L.Arena.litHash),
   ("nstr_find", L.Arena.nsFind),
   ("nstr_match", L.Arena.nsMatch),
   ("limbs_eq", L.Arena.limbsEq),
   ("nstr_push", L.Arena.nsPush),
   ("intern_nnum", L.Arena.internNNum),
   ("nnum_find", L.Arena.nnumFind),
   ("nnum_push", L.Arena.nnumPush),
   ("intern_zero", L.Arena.internZero),
   ("zero_find", L.Arena.zeroFind),
   ("zero_push", L.Arena.zeroPush),
   ("intern_param", L.Arena.internParam),
   ("param_find", L.Arena.paramFind),
   ("param_push", L.Arena.paramPush),
   ("intern_succ", L.Arena.internSucc),
   ("succ_find", L.Arena.succFind),
   ("succ_push", L.Arena.succPush),
   ("intern_max", L.Arena.internMax),
   ("max_find", L.Arena.maxFind),
   ("max_push", L.Arena.maxPush),
   ("intern_imax", L.Arena.internImax),
   ("imax_find", L.Arena.imaxFind),
   ("imax_push", L.Arena.imaxPush),
   ("stk_push", L.Rom.stkPush),
   ("stk_pool", L.Rom.stkPool),
   ("intern_ls", L.Arena.internLs),
   ("ls_find", L.Arena.lsFind),
   ("ls_match", L.Arena.lsMatch),
   ("ls_push", L.Arena.lsPush),
   ("memo_get", L.Rom.memoGet),
   ("intern_bvar", L.Arena.internBVar),
   ("bvar_find", L.Arena.bvarFind),
   ("bvar_push", L.Arena.bvarPush),
   ("intern_sort", L.Arena.internSort),
   ("sort_find", L.Arena.sortFind),
   ("sort_push", L.Arena.sortPush),
   ("rom_lit", L.Rom.romLit),
   ("intern_lit", L.Arena.internLit),
   ("lit_find", L.Arena.litFind),
   ("lit_match", L.Arena.litMatch),
   ("lit_push", L.Arena.litPush),
   ("intern_const", L.Arena.internConst),
   ("const_find", L.Arena.constFind),
   ("const_push", L.Arena.constPush),
   ("intern_fvar", L.Arena.internFVar),
   ("fvar_find", L.Arena.fvarFind),
   ("fvar_push", L.Arena.fvarPush),
   ("memo_push", L.Rom.memoPush),
   ("rset_find", L.Arena.memoFindG L.Rom.rsetSch),
   ("rset_put", L.Arena.memoPutG L.Rom.rsetSch),
   ("mk_proj", L.Arena.mkProj),
   ("der_b", L.Arena.derB),
   ("intern_proj", L.Arena.internProj),
   ("proj_find", L.Arena.projFind),
   ("proj_push", L.Arena.projPush),
   ("mk_app", L.Arena.mkApp),
   ("intern_app", L.Arena.internApp),
   ("app_find", L.Arena.appFind),
   ("app_push", L.Arena.appPush),
   ("mk_lam", L.Arena.mkLam),
   ("intern_lam", L.Arena.internLamL),
   ("lam_find", L.Arena.lamFind),
   ("lam_push", L.Arena.lamPush),
   ("mk_forall", L.Arena.mkForall),
   ("intern_forall", L.Arena.internForallL),
   ("forall_find", L.Arena.forallFind),
   ("forall_push", L.Arena.forallPush),
   ("mk_let", L.Arena.mkLet),
   ("intern_letE", L.Arena.internLet),
   ("letE_find", L.Arena.letFind),
   ("letE_push", L.Arena.letPush),
   ("erec_put", L.Ind.erecPut)]

theorem romCTabO_fixed :
    romCTabO.all (fun x => romC x.1 == x.1 && x.2.body.calls.all (fun h => romC h == h)) = true := by
  decide +kernel

theorem romCTab_calls :
    (romCTabR romDataLit ++ romCTabO).all (fun x => x.2.body.calls.all (· ∈ romCN)) = true := by
  decide +kernel

theorem romCTab_keys :
    romCN.all (fun g => ((romCTabR romDataLit ++ romCTabO).lookup g).isSome) = true := by
  decide +kernel

theorem romConst_eq :
    (romCTabR romDataLit).map (fun x => (romC x.1, x.2.renameCalls romC)) = romConstProg := by
  simp only [romCTabR, romConstProg, List.map_cons, List.map_nil, romU64C, romPutC, romNameC, romLevelC,
    romLevelsC, romLvlsGoC, romExprC, romExRefC, romExLeafC, romExOneC, romExTwoC, romExprsToC,
    List.cons.injEq, Prod.mk.injEq, and_true]
  decide

theorem checkerProg_romCOther (bs : List UInt8) : ProgHas (Prog.subPB bs checkerProg) romCTabO := by
  prog_bundle []

theorem checkerProg_romConst (bs : List UInt8) : ProgHas (Prog.subPB bs checkerProg) romConstProg := by
  prog_bundle []

theorem romConstProg_nodup : (romConstProg.map (·.1)).Nodup := by decide

/-- **The renaming of the ROM readers at the checker's program.** -/
theorem checkerProg_romCRen (bs : List UInt8) :
    RenameOK romC (Prog.subPB bs checkerProg) (Prog.viaC romDataLit (Prog.subPB bs checkerProg))
      romCN := by
  have hO := checkerProg_romCOther bs
  have hC := checkerProg_romConst bs
  refine RenameOK.of_tab (romCTabR romDataLit ++ romCTabO)
    (fun g hg => List.all_eq_true.mp romCTab_keys g hg) (fun g B hB => ?_) (fun g _ B hB => ?_)
    (fun g _ B hB => ?_)
  · rw [List.lookup_append] at hB
    simp only [Prog.viaC, List.lookup_append]
    cases h : (romCTabR romDataLit).lookup g with
    | some v => rw [h] at hB; exact hB
    | none => rw [h] at hB; simp only [Option.none_or] at hB ⊢; exact hO g B hB
  · have := List.all_eq_true.mp romCTab_calls _ (L.Compiler.mem_of_lookup hB)
    simpa using this
  · rw [List.lookup_append] at hB
    cases h : (romCTabR romDataLit).lookup g with
    | some v =>
      rw [h] at hB; simp only [Option.some_or, Option.some.injEq] at hB; subst hB
      have hm : (romC g, v.renameCalls romC) ∈ romConstProg := by
        rw [← romConst_eq]
        exact List.mem_map.mpr ⟨(g, v), L.Compiler.mem_of_lookup h, rfl⟩
      exact hC _ _ (lookup_of_mem romConstProg_nodup hm)
    | none =>
      rw [h] at hB; simp only [Option.none_or] at hB
      have hx := List.all_eq_true.mp romCTabO_fixed _ (L.Compiler.mem_of_lookup hB)
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hx
      rw [hx.1, show B.renameCalls romC = B from by
        cases B; simp only [FunDecl.renameCalls, FunDecl.mk.injEq, true_and]
        exact Stmt.renameCalls_of_calls _ hx.2]
      exact hO g B hB

theorem viaC_lookup_of {rom : List UInt8} {p : Prog} {g : FnName} (h : (romCTabR rom).lookup g = none) :
    (Prog.viaC rom p).lookup g = p.lookup g := by
  simp only [Prog.viaC, List.lookup_append, h, Option.none_or]

theorem romCTabR_noSt8 : (romCTabR romDataLit).all (fun f => f.2.body.noSt8) = true := by decide +kernel

/-- **The generic readers' lookups in `Prog.viaC` at the checker's program.** -/
theorem checkerProg_romCVia (bs : List UInt8) :
    ExprProg romDataLit (Prog.viaC romDataLit (Prog.subPB bs checkerProg)) := by
  have hns : Prog.noSt8 (Prog.subPB bs checkerProg) = true := by
    rw [Prog.noSt8_subPB]; exact checkerProg_noSt8
  repeat' first
    | apply L.Rom.ExprProg.mk
    | apply L.Rom.LevelsProg.mk
    | apply L.Rom.LevelProg.mk
    | apply L.Rom.NameProg.mk
  all_goals first
    | (rw [Prog.viaC, L.Prog.noSt8, List.all_append, Bool.and_eq_true]
       exact ⟨romCTabR_noSt8, hns⟩)
    | (rw [viaC_lookup_of rfl]; chk_lk)
    | rfl

end L.Checker
