import ConAgua.Compiler.WF
import ConAgua.Arena.AppStore
import ConAgua.Arena.BVarStore
import ConAgua.Arena.ConstStore
import ConAgua.Arena.CoreCaches
import ConAgua.Arena.Env
import ConAgua.Arena.FVarRange
import ConAgua.Arena.FVarStore
import ConAgua.Arena.ForallStore
import ConAgua.Arena.ImaxStore
import ConAgua.Arena.Inst1Spec
import ConAgua.Arena.LamStore
import ConAgua.Arena.LetStore
import ConAgua.Arena.LevelEquiv
import ConAgua.Arena.LevelStore
import ConAgua.Arena.LiftSpec
import ConAgua.Arena.LitRefine
import ConAgua.Arena.LsStore
import ConAgua.Arena.MaxStore
import ConAgua.Arena.MemoBank
import ConAgua.Arena.NAnonStore
import ConAgua.Arena.NNumStore
import ConAgua.Arena.NStrStore
import ConAgua.Arena.NatAdd
import ConAgua.Arena.NatArms
import ConAgua.Arena.NatBits
import ConAgua.Arena.NatCmp
import ConAgua.Arena.NatDiv
import ConAgua.Arena.NatGcd
import ConAgua.Arena.NatMul
import ConAgua.Arena.NatPow
import ConAgua.Arena.NatShl
import ConAgua.Arena.NatShr
import ConAgua.Arena.NatSub
import ConAgua.Arena.ParamStore
import ConAgua.Arena.ProjStore
import ConAgua.Arena.Scratch
import ConAgua.Arena.SortStore
import ConAgua.Arena.Store
import ConAgua.Arena.Walk
import ConAgua.Arena.WalkBench
import ConAgua.Arena.ZeroStore
import ConAgua.Compiler.Tests
import ConAgua.Final.Statement
import ConAgua.Front.Apply
import ConAgua.Front.ApplyDecl
import ConAgua.Front.ApplyExpr
import ConAgua.Front.FrontRun
import ConAgua.Front.NatDec
import ConAgua.Front.Unescape
import ConAgua.L.Examples
import ConAgua.Scan.Key
import ConAgua.Scan.Lit
import ConAgua.Scan.Str
import ConAgua.Scan.Utf8
import ConAgua.Scan.Validator
import ConAgua.Scan.Values

/-!
# Every program passes the compiler's static check

One `#guard` per program defined on master (lane `cresults`): `Prog.wfAuto p` is `Prog.wf` for the
smallest table that has every array `p` names, so `compile_correct` applies to `p` in any layout
with those arrays (a layout with more arrays only moves the table offsets). Add a line for every new
program (except the compiler's own test programs, checked in `Tests.lean`). The benchmark programs (whose modules clash with `NatBits` on import) are in
`WFAllBench.lean`.
-/

open L.Compiler

#guard Prog.wfAuto L.Arena.appProg
#guard Prog.wfAuto L.Arena.bvarProg
#guard Prog.wfAuto L.Arena.constProg
#guard Prog.wfAuto L.Arena.cacheProg
#guard Prog.wfAuto L.Arena.envProg
#guard Prog.wfAuto L.Arena.fvarRangeProg
#guard Prog.wfAuto L.Arena.fvarProg
#guard Prog.wfAuto L.Arena.forallProg
#guard Prog.wfAuto L.Arena.imaxProg
#guard Prog.wfAuto L.Arena.instProg
#guard Prog.wfAuto L.Arena.lamProg
#guard Prog.wfAuto L.Arena.letProg
#guard Prog.wfAuto L.Arena.levelProg
#guard Prog.wfAuto L.Arena.succProg
#guard Prog.wfAuto L.Arena.liftProg
#guard Prog.wfAuto L.Arena.storeProg
#guard Prog.wfAuto L.Arena.lsProg
#guard Prog.wfAuto L.Arena.maxProg
#guard Prog.wfAuto L.Arena.tbProg
#guard Prog.wfAuto L.Arena.nanonProg
#guard Prog.wfAuto L.Arena.nnumProg
#guard Prog.wfAuto L.Arena.nstrProg
#guard Prog.wfAuto L.Arena.natProg
#guard Prog.wfAuto L.Arena.natArmProg
#guard Prog.wfAuto L.Arena.natBitsProg
#guard Prog.wfAuto L.Arena.natCmpProg
#guard Prog.wfAuto L.Arena.natDivProg
#guard Prog.wfAuto L.Arena.natGcdProg
#guard Prog.wfAuto L.Arena.natMulProg
#guard Prog.wfAuto L.Arena.natPowProg
#guard Prog.wfAuto L.Arena.natShlProg
#guard Prog.wfAuto L.Arena.natShrProg
#guard Prog.wfAuto L.Arena.natSubProg
#guard Prog.wfAuto L.Arena.paramProg
#guard Prog.wfAuto L.Arena.projProg
#guard Prog.wfAuto L.Arena.scratchProg
#guard Prog.wfAuto L.Arena.sortProg
#guard Prog.wfAuto L.Arena.litProg
#guard Prog.wfAuto L.Arena.walkProg
#guard Prog.wfAuto L.Arena.benchProg
#guard Prog.wfAuto L.Arena.zeroProg
#guard Prog.wfAuto ConAgua.Final.rejectProg
#guard Prog.wfAuto L.Front.frontProg
#guard Prog.wfAuto L.Front.declProg
#guard Prog.wfAuto L.Front.exprProg
#guard Prog.wfAuto L.Front.frontAllProg
#guard Prog.wfAuto L.Front.natDecProg
#guard Prog.wfAuto L.Front.Unescape.escProg
#guard Prog.wfAuto L.Examples.findProg
#guard Prog.wfAuto L.Examples.scanProg
#guard Prog.wfAuto L.Scan.Key.keyProg
#guard Prog.wfAuto L.Scan.Lit.litProg
#guard Prog.wfAuto L.Scan.Str.strProg
#guard Prog.wfAuto L.Scan.Utf8.utf8Prog
#guard Prog.wfAuto L.Scan.Validator.valProg
-- `hintsProg` is a test fragment: it calls `skip_ws`/`hints_obj`, which it does not contain.
#guard !Prog.wfAuto L.Scan.Values.hintsProg
