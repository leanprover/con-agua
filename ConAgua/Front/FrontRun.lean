module

public import ConAgua.Front.LineRef
public import ConAgua.Front.Driver
public import ConAgua.Scan.Validator
import ConRon.Bridge.Frontend.Chunks
meta import ConAgua.Front.LineRef
meta import ConAgua.Front.Driver
meta import ConAgua.Scan.Validator
meta import ConRon.Bridge.Frontend.Chunks
import all ConRon.Bridge.Frontend.Lines
import all ConAgua.Arena.AppStore
import all ConAgua.Arena.BVarStore
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.ConstStore
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.ForallStore
import all ConAgua.Arena.ImaxStore
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.LamStore
import all ConAgua.Arena.LetStore
import all ConAgua.Arena.LevelEquiv
import all ConAgua.Arena.LevelHeap
import all ConAgua.Arena.LevelLeq
import all ConAgua.Arena.LevelSimp
import all ConAgua.Arena.LevelStore
import all ConAgua.Arena.LevelSubst
import all ConAgua.Arena.LsStore
import all ConAgua.Arena.MaxStore
import all ConAgua.Arena.MemoLib
import all ConAgua.Arena.NAnonStore
import all ConAgua.Arena.NNumStore
import all ConAgua.Arena.NStrStore
import all ConAgua.Arena.ParamStore
import all ConAgua.Arena.ProjStore
import all ConAgua.Arena.SortStore
import all ConAgua.Arena.Store
import all ConAgua.Arena.ZeroStore
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
import all ConAgua.Scan.Key
import all ConAgua.Scan.Leaves
import all ConAgua.Scan.Line
import all ConAgua.Scan.Lit
import all ConAgua.Scan.Member
import all ConAgua.Scan.Records
import all ConAgua.Scan.Str
import all ConAgua.Scan.Utf8
import all ConAgua.Scan.Values

@[expose] public section

/-!
# The frontend's driver: the twin's invariant, `front_init`, the whole program

What `front_run()`'s refinement (`frontRun_ref`, `FrontRunRef.lean`) iterates: con-ron's bridge
invariant across the lines (`TwinOK`), `front_init`'s model with the input bytes unchanged
(`initKW`, `Keep`: a property of every L run of a program without byte stores), and the whole
frontend program `frontAllProg` with its lookup bundles (`frontAllProg_line`).
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Front.Fields
open ConLeche.Frontend hiding StateD RecordVerdict applyLine parseBytes ParseResultD
open ConRon.Arena ConRon.Arena.Frontend

namespace L.Front

/-- `front_init`'s model, with the input unchanged. -/
def initKW (m : Mem) : Option Mem :=
  match frontInitW m with
  | none => none
  | some m' => if m'.arr8 IN = m.arr8 IN then some m' else none

/-- What con-ron's own bridge keeps of the arena and parse states across the lines
(`ConRon.Bridge.Frontend.applyLine_run`): the store is well formed (`StateOK`, which the apply step
of an `inductive` line reads), the scratch tier is off, the pins hold, and the parse state is
persistent and related to con-leche's. -/
def TwinOK (a : AState) (st : StateD) : Prop :=
  ConRon.Bridge.StateOK a ∧ a.store.scratchOn = false ∧ ConRon.Bridge.PinsOK a ∧
    ConRon.Bridge.Frontend.PersStateD st ∧ ∃ sc, ConRon.Bridge.Frontend.StateDRel a.store st sc

/-- A line con-ron applies keeps `TwinOK`. -/
theorem TwinOK.line {a : AState} {st : StateD} (h : TwinOK a st) {r : LineRec} {st' : StateD}
    (h1 : AM.ok (applyRecord st r) a) (h2 : AM.res (applyRecord st r) a = .inl st') :
    TwinOK (AM.st (applyRecord st r) a) st' := by
  obtain ⟨hok, hoff, hpins, hp, sc, hrel⟩ := h
  cases hr : (applyRecord st r).run a with
  | error e => simp [AM.ok, hr] at h1
  | ok q =>
    obtain ⟨x, a'⟩ := q
    have hx : x = .inl st' := by simpa [AM.res, hr] using h2
    have ha : AM.st (applyRecord st r) a = a' := by simp [AM.st, hr]
    rw [ha]
    subst hx
    obtain ⟨hstep, hpers, y, -, hsum⟩ := ConRon.Bridge.Frontend.applyRecord_run hok hoff hpins hrel hp hr
    refine ⟨hstep.ok, by rw [hstep.scratch]; exact hoff, hpins.mono hstep.ext hstep.pins, hpers st' rfl, ?_⟩
    cases y with
    | inl sc' => exact ⟨sc', hsum⟩
    | inr w => exact hsum.elim

/-- `StateD.init` establishes `TwinOK`. -/
theorem TwinOK.init {a a₁ : AState} {st₀ : StateD} (hok : ConRon.Bridge.StateOK a)
    (hoff : a.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a)
    (h : StateD.init.run a = .ok (st₀, a₁)) : TwinOK a₁ st₀ := by
  obtain ⟨hstep, hp, hrel⟩ := ConRon.Bridge.Frontend.StateD_init_run hok hoff h
  exact ⟨hstep.ok, by rw [hstep.scratch]; exact hoff, hpins.mono hstep.ext hstep.pins, hp, _, hrel⟩

/-- `front_init`'s model keeps the mode (it interns the anonymous name and `zero`). -/
theorem frontInitW_mode (m m' : Mem) (hW : frontInitW m = some m') (hmo : ModeOK m) : ModeOK m' := by
  simp only [frontInitW] at hW
  cases h1 : putK NID 0 (nainternW m) with
  | none => rw [h1] at hW; simp [initK] at hW
  | some m₁ =>
    rw [h1, initK_some] at hW
    obtain ⟨w, m₃, hI, -, hp⟩ := putK_eq h1
    obtain ⟨w', m₄, hI', -, hp'⟩ := putK_eq hW
    have e1 := MemFrame.modeOK (tblPutW_frame (.inl rfl) hp)
      (h := MemFrame.modeOK (consInternM_frame nanonCS_wf hI) (by decide) (by decide) hmo)
    exact MemFrame.modeOK (tblPutW_frame (.inr (.inl rfl)) hp')
      (h := MemFrame.modeOK (consInternM_frame zeroCS_wf hI') (by decide) (by decide) e1)

/-- `front_init`'s run, with the input unchanged. -/
theorem frontInitK_spec (p : Prog) (hL : FrontLookups p) (hE : ExprLookups p)
    (hpi : p.lookup "front_init" = some frontInit) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "front_init" []
    ⦃fun _ s' => initKW s₀.mem = some s'.mem ∧ Keep s₀.mem s'.mem ∧ LocEq s' s₀; ⊤⦄ := by
  have h := Triple.keep hE.no_st8 (frontInit_spec p hL hpi n s₀)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨⟨-, hW⟩, hk, hl⟩ := M.of_run (P := fun s => s = s₀) hs hrun h
  refine ⟨?_, hk, hl⟩
  unfold initKW
  rw [hW]
  simp [Keep.arr8 hk]

/-! ## The whole program -/

/-- Every function of the frontend: the validator, the single pass, the stores, the apply
steps, the line and the driver. -/
def frontAllProg : Prog := L.Scan.Validator.valProg ++
  [("rec_nat_list", recNatList), ("sub_bit", L.Front.LineRec.subBitF),
   ("sub_val", L.Front.LineRec.subValF), ("sub_rec", L.Front.LineRec.subRec),
   ("line_rec", L.Front.LineRec.lineRec)] ++
  exprProg.filter (fun f => f.1 != "skip_digits" && f.1 != "num_end" && f.1 != "byte_in" &&
    f.1 != "hex_val" && f.1 != "hex4" && f.1 != "hex3") ++
  [("front_line", frontLine), ("apply_rec", applyRec), ("apply_str", applyStr),
   ("front_run", frontRun),
   ("match_dlit", matchDlit), ("str_code", strCode), ("hints_val", hintsVal),
   ("d_member", dMember), ("decl_val", declVal), ("decl_code", declCodeF),
   ("rec_decl_obj", recDeclObj), ("rec_decl_line", recDeclLine),
   ("lp_put", lpPut), ("decl_kind", declKind), ("decl_push", declPush), ("decl_cv", declCv),
   ("apply_decl", applyDecl), ("apply_dline", applyDLine)] ++
  L.Front.Ind.indFieldsFns ++ L.Front.Ind.indApplyFns ++ L.Arena.levelProg ++ [("e_view", L.Ind.eView)]

set_option maxRecDepth 100000

theorem frontAllProg_noSt8 : frontAllProg.noSt8 = true := by decide +kernel

theorem frontAllProg_scan : ScanLookups frontAllProg := by
  unfold ScanLookups scanLookupsFns; repeat (first | exact ProgHas.nil | refine ProgHas.cons rfl ?_)

theorem frontAllProg_front : FrontLookups frontAllProg := by constructor <;> rfl

theorem frontAllProg_expr : ExprLookups frontAllProg := by
  refine ⟨frontAllProg_front, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    frontAllProg_noSt8⟩ <;> rfl

theorem frontAllProg_dfields : DeclFieldLookups frontAllProg := by
  unfold DeclFieldLookups declFieldLookupsFns; repeat (first | exact ProgHas.nil | refine ProgHas.cons rfl ?_)

theorem frontAllProg_decl : DeclLookups frontAllProg :=
  ⟨frontAllProg_expr, rfl, rfl, rfl, rfl, rfl⟩

theorem frontAllProg_indFields : L.Front.Ind.IndFieldLookups frontAllProg := by
  constructor <;> first | rfl | exact frontAllProg_noSt8

theorem frontAllProg_indApply : L.Front.Ind.IndApplyLookups frontAllProg := by
  constructor
  · exact frontAllProg_decl
  · constructor <;> rfl
  all_goals rfl

theorem frontAllProg_indInstall : L.Front.Ind.IndInstallLookups frontAllProg := by
  constructor <;> rfl

theorem frontAllProg_dline : DLineLookups frontAllProg :=
  { apply_ind := rfl, apply_ind_line := rfl, apply_dline := rfl, dfields := frontAllProg_dfields }

theorem frontAllProg_line : LineLookups frontAllProg :=
  { frontAllProg_dline with
    scan := frontAllProg_scan, apply := frontAllProg_indApply, fields := frontAllProg_indFields,
    install := frontAllProg_indInstall, front_line := rfl, apply_nstr := rfl, apply_nnum := rfl,
    apply_level := rfl, apply_rec := rfl, apply_str := rfl }

/-- A memory with the tier-0 word arrays `0‥223` of 4096 words (as `initMem`, but one shared zero
array), every other word array empty, and the input `s` (the inductive lines' scratch arrays
`IFR`/`IFL` are 70, 71, the level heap 192). -/
def frontMemOf (s : String) : Mem :=
  let z : Array Word := Array.replicate 4096 0
  ({ words := fun b => if !b.hi && b.arr < 224 then z else #[] } : Mem).putBytes IN s.toUTF8.data

/- A header, a name, a level, and expression lines of six kinds (a 30-digit literal among them):
accepted. -/
#guard (run frontAllProg 100000 "front_run" [] (frontMemOf
  "{\"meta\":{\"x\":1}}\n{\"in\":1,\"str\":{\"pre\":0,\"str\":\"N\\u00e4t\\n\"}}\n{\"il\":1,\"succ\":0}\n\
  {\"ie\":0,\"sort\":1}\n{\"ie\":1,\"const\":{\"name\":1,\"us\":[0,1]}}\n\
  {\"ie\":2,\"app\":{\"fn\":1,\"arg\":0}}\n{\"ie\":3,\"natVal\":\"123456789012345678901234567890\"}\n\
  {\"ie\":4,\"lam\":{\"binderInfo\":\"default\",\"body\":0,\"name\":1,\"type\":2}}\n\
  {\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n\
  {\"def\":{\"hints\":{\"regular\":3},\"levelParams\":[1],\"name\":1,\"safety\":\"safe\",\"type\":0,\"value\":2}}")).toOption.map
  (·.1) == some [0]
/- A line that does not scan: its number (after the header, which must be line 0, #144). An unbound
id: the run aborts. -/
#guard (run frontAllProg 100000 "front_run" [] (frontMemOf
  "{\"meta\":{\"x\":1}}\n{\"il\":1,\"succ\":0}\n{\"il\":2,\"succ\":}\n")).toOption.map (·.1) == some [3]
#guard (run frontAllProg 100000 "front_run" [] (frontMemOf
  "{\"ie\":0,\"sort\":5}\n")).toOption.isNone

end L.Front
