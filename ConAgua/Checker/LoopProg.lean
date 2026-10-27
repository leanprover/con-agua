import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.LoopProgInd
import ConAgua.Checker.LoopDeclArm
import ConAgua.Checker.LoopDeclAgree
import ConAgua.Checker.IndCore
import ConAgua.Checker.CoreErec
import ConAgua.Checker.LeafAll
import ConAgua.Checker.LoopAll
import ConAgua.Checker.RomProgB
import ConAgua.Rom.CIReadRefs
import ConAgua.Arena.LoopStart
import ConAgua.Checker.IndMemoClosed

/-!
# The declaration loop's program hypotheses at the substituted checker program (lane `loopt3`)

The ROM readers' refinements (`RomRefs`) hold of a program whose readers read the ROM as constant
data (`romRefs_of`), not of `checkerProg`, whose readers read the buffer `PB`. As for the ROM
stages (`Rom/Stage.lean`), the loop is proved at `checkerProg.subPB bs` (`bs` the buffer
`pb_check` accepted) and carried to `checkerProg` by `triple_subPB`. Here its program hypotheses
at the substituted program: `LoopCallees` (`checkerProg_loopCalleesPB`) and `LoopTopProg`
(`checkerProg_loopTopPB`).

* Lookups: `prog_bundle` (`LoopProgTac.lean`): a function that reads no pin data is unchanged
  (`lkN`), the seven readers (`pbReadFns`) are their `subPB` (`lkR`).
* Write sets: `subPB` changes no store and no call (`Stmt.okW_subPB`), so `closedW` carries over
  (`closedW_subPB`, `StepIn.subPB`).
* Text agreements: on a name that is not a reader, the two programs agree
  (`checkerProg_subPB_lookup`, from the per-chunk check `checkerProg_pbFree`).
* `RomRefs`: `romRefs_of` from `RomCIProg bs` (`checkerProg_itemsProg` and the readers' lookups),
  for a buffer `bs` with `RomOK bs` starting with `romData` (what `pb_check` establishes).
-/

namespace L.Checker

open L L.Rom L.Arena L.Compiler

set_option maxRecDepth 100000

/-! ## Write sets under the substitution -/

theorem _root_.L.ctlIdx_subPB (bs : List UInt8) {e : Expr} {ws : List Word} (h : ctlIdx e = some ws) :
    ctlIdx (e.subPB bs) = some ws := by
  unfold ctlIdx at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h

theorem _root_.L.Stmt.okW_subPB (bs : List UInt8) {ctl : ArrId} {A : List ArrId} {C : List Word}
    {fs : List FnName} : ∀ {s : Stmt}, s.okW ctl A C fs = true → (s.subPB bs).okW ctl A C fs = true
  | .st64 a i e, h => by
    simp only [Stmt.okW, Stmt.subPB] at h ⊢
    split at h
    · rename_i hc
      simp only [hc, ite_true] at h ⊢
      split at h
      · rename_i ws hw; rw [ctlIdx_subPB bs hw]; exact h
      · cases h
    · rename_i hc; simp only [hc, ite_false] at h ⊢; exact h
  | .seq s t, h | .ite _ s t, h => by
    simp only [Stmt.okW, Stmt.subPB, Bool.and_eq_true] at h ⊢
    exact ⟨Stmt.okW_subPB bs h.1, Stmt.okW_subPB bs h.2⟩
  | .while _ s, h => by
    simp only [Stmt.okW, Stmt.subPB] at h ⊢; exact Stmt.okW_subPB bs h
  | .st8 .., h => by simp [Stmt.okW] at h
  | .call .., h => by simpa [Stmt.okW, Stmt.subPB] using h
  | .st64t .., h => by simpa [Stmt.okW, Stmt.subPB] using h
  | .copy64 d .., h | .copy8w d .., h => by cases d <;> simpa [Stmt.okW, Stmt.subPB, WArr.okW, WArr.subPB] using h
  | .scan8 .., _ => rfl
  | .skip, _ | .set .., _ | .brk, _ | .ret _, _ | .abort _, _ | .gset .., _ => rfl

theorem closedW_subPB (bs : List UInt8) {ctl : ArrId} {p : Prog} {A : List ArrId} {C : List Word}
    {fs : List FnName} (h : closedW ctl p A C fs = true) :
    closedW ctl (Prog.subPB bs p) A C fs = true := by
  simp only [closedW, List.all_eq_true] at h ⊢
  intro f hf
  have := h f hf
  rw [lookup_subPB]
  cases e : p.lookup f with
  | none => rfl
  | some fd =>
    simp only [e] at this
    exact Stmt.okW_subPB bs this

theorem closedWL_subPB (bs : List UInt8) {ctl : ArrId} {p : Prog} {A : List ArrId} {C : List Word}
    {fs L : List FnName} (h : closedWL ctl p A C fs L = true) :
    closedWL ctl (Prog.subPB bs p) A C fs L = true := by
  simp only [closedWL, List.all_eq_true] at h ⊢
  intro f hf
  have := h f hf
  rw [lookup_subPB]
  cases e : p.lookup f with
  | none => rfl
  | some fd =>
    simp only [e] at this
    exact Stmt.okW_subPB bs this

theorem _root_.L.Arena.StepIn.subPB (bs : List UInt8) {p : Prog} {fs : List FnName} (h : StepIn p fs) :
    StepIn (Prog.subPB bs p) fs :=
  let ⟨F, hF, hc⟩ := h; ⟨F, hF, closedW_subPB bs hc⟩

/-! ## The functions that read no pin data -/

/-- The functions of `checkerProg` that read the pin-data buffer. -/
def pbReadFns : List FnName :=
  ["pb_check", "rom_expr", "rom_items", "rom_level", "rom_name", "rom_put", "rom_u64"]

names_tree pbReadTree : pbReadFns

/-- Every function of `checkerProg` but the readers reads no pin data. -/
prog_all checkerProg_pbFree : checkerProg
  (fun x => (pbReadTree.find (nameCode x.1)).isSome || x.2.body.noPB)

/-- **Off the readers the substituted program is `checkerProg`.** -/
theorem checkerProg_subPB_lookup (bs : List UInt8) {f : FnName}
    (hf : (pbReadTree.find (nameCode f)).isSome = false) :
    (Prog.subPB bs checkerProg).lookup f = checkerProg.lookup f := by
  cases e : checkerProg.lookup f with
  | none => rw [lookup_subPB, e]; rfl
  | some fd =>
    have h := checkerProg_pbFree _ (mem_of_lookup e)
    simp only [hf, Bool.false_or] at h
    exact lookup_subPB_noPB bs e h

/-- Agreement of the substituted program with a text, off the readers. -/
theorem agree_subPB (bs : List UInt8) {q : Prog} {fs : List FnName}
    (hn : fs.all (fun f => !(pbReadTree.find (nameCode f)).isSome) = true)
    (h : ∀ f ∈ fs, f ∉ openFns → checkerProg.lookup f = q.lookup f) :
    ∀ f ∈ fs, f ∉ openFns → (Prog.subPB bs checkerProg).lookup f = q.lookup f := by
  intro f hf ho
  have := List.all_eq_true.mp hn f hf
  rw [checkerProg_subPB_lookup bs (by simpa using this)]
  exact h f hf ho

theorem cvgFns_noPB : cvgFns.all (fun f => !(pbReadTree.find (nameCode f)).isSome) = true := by
  decide +kernel
theorem ivFns_noPB : ivFns.all (fun f => !(pbReadTree.find (nameCode f)).isSome) = true := by
  decide +kernel
theorem armFns_noPB : armFns.all (fun f => !(pbReadTree.find (nameCode f)).isSome) = true := by
  decide +kernel

theorem checkerProg_cvgAgreePB (bs : List UInt8) :
    ∀ f ∈ cvgFns, f ∉ openFns → (Prog.subPB bs checkerProg).lookup f = cvgProg.lookup f :=
  agree_subPB bs cvgFns_noPB checkerProg_cvgAgree

theorem checkerProg_ivAgreePB (bs : List UInt8) :
    ∀ f ∈ ivFns, f ∉ openFns → (Prog.subPB bs checkerProg).lookup f = ivProg.lookup f :=
  agree_subPB bs ivFns_noPB checkerProg_ivAgree

theorem checkerProg_armAgreePB (bs : List UInt8) :
    ∀ f ∈ armFns, f ∉ openFns → (Prog.subPB bs checkerProg).lookup f = armText.lookup f :=
  agree_subPB bs armFns_noPB checkerProg_armAgree

theorem lvlFns_cvg : ∀ f ∈ lvlFns, f ∈ cvgFns ∧ f ∉ openFns := by decide +kernel

theorem checkerProg_lvlTextPB (bs : List UInt8) :
    ∀ f ∈ lvlFns, (Prog.subPB bs checkerProg).lookup f = cvgProg.lookup f :=
  fun f hf => checkerProg_cvgAgreePB bs f (lvlFns_cvg f hf).1 (lvlFns_cvg f hf).2

theorem checkerProg_natArmPB (bs : List UInt8) :
    ProgHas (Prog.subPB bs checkerProg) natArmProg' := by prog_bundle []

theorem checkerProg_natAgreePB (bs : List UInt8) :
    ∀ f ∈ natFns, (Prog.subPB bs checkerProg).lookup f = natArmProg'.lookup f :=
  ProgHas.agreeNames (checkerProg_natArmPB bs)

/-! ## The ROM readers -/

theorem checkerProg_romCIProg (bs : List UInt8) : RomCIProg bs (Prog.subPB bs checkerProg) := by
  prog_bundle [checkerProg_itemsProg bs]

/-- **The ROM readers of the substituted program refine the twin**, for a buffer that
`pb_check` accepts. -/
theorem checkerProg_romRefsPB (bs : List UInt8) (hr : RomOK bs)
    (hpre : bs = romData ++ bs.drop romData.length) : RomRefs (Prog.subPB bs checkerProg) :=
  romRefs_of _ ⟨bs, _, hr, hpre, checkerProg_romCIProg bs⟩

/-! ## The loop's program hypotheses -/

/-- **The declaration loop's callees at the substituted checker program.** -/
theorem checkerProg_loopCalleesPB (bs : List UInt8) (hr : RomOK bs)
    (hpre : bs = romData ++ bs.drop romData.length) :
    ∀ dn, L.Ind.DnInj dn → IndArmSpec (Prog.subPB bs checkerProg) dn → QuotDn dn →
      LoopCallees dn (Prog.subPB bs checkerProg) := by
  intro dn hdn harm hq
  have hrom := checkerProg_romRefsPB bs hr hpre
  prog_bundle [checkerProg_cvgAgreePB bs, checkerProg_ivAgreePB bs, checkerProg_armAgreePB bs,
    checkerProg_cvgIn.subPB bs, checkerProg_ivIn.subPB bs, checkerProg_armIn.subPB bs,
    checkerProg_natGateIn.subPB bs, checkerProg_dgIn.subPB bs, checkerProg_indIn.subPB bs,
    (closedW_subPB bs checkerProg_leafClosed : LeafClosed (Prog.subPB bs checkerProg)),
    (closedW_subPB bs checkerProg_loopClosed : LoopClosed (Prog.subPB bs checkerProg)),
    (closedW_subPB bs checkerProg_coreStage : L.Ind.CoreStageClosed (Prog.subPB bs checkerProg)),
    closedW_subPB bs checkerProg_coreErec, checkerProg_natAgreePB bs, checkerProg_lvlTextPB bs,
    (closedWL_subPB bs checkerProg_indMemo : IndMemoClosed (Prog.subPB bs checkerProg)),
    (by prog_bundle [] : L.Ind.CrfF (Prog.subPB bs checkerProg)),
    hdn, harm, hq, hrom]

/-- **The loop's own program hypotheses at the substituted checker program.** -/
theorem checkerProg_loopTopPB (bs : List UInt8) : LoopTopProg (Prog.subPB bs checkerProg) := by
  prog_bundle []

end L.Checker
