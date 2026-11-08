module

public import ConAgua.Arena.Verdict
import ConAgua.Front.ApplyDeclRefine
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import ConLeche.Frontend.ExportC
public import ConLeche.Frontend.Scan.Types
import ConAgua.Front.ApplyExprRefine
public import ConAgua.Front.DeclIface
public import ConAgua.Front.StateDR

@[expose] public section

/-!
# The claim of a frontend step with a record verdict; `decl_kind`'s declines (lane `verdicts-b`,
helpers `c5`, `fr`)

`VerdictClaimR`/`VerdictClaimL`, the scanner's `safety` converse (`DeclSafeR`), the twin's runs at
`decl_kind`'s declines and `decl_cv`'s `parseCVD`: what the refinements of `decl_kind`,
`apply_decl`, `apply_dline` (`Front/ApplyDLineRef.lean`) and `apply_ind` read.
-/

open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend hiding StateD RecordVerdict applyLine parseBytes ParseResultD
open Std.WP
open scoped Lean.Order
open L.Arena
open ConAgua.Front.FieldsLink
open L.Front.Fields (DFld)

set_option experimental.vcgen true

/-! ## The claim for a frontend step that reports a record verdict -/

namespace L.Front

/-- **The claim about a twin step with a record verdict** (`AM (StateD ⊕ RecordVerdict)`): an L
error of class `c ≠ 0` means the step fails in the monad with an error of class `c`, or returns
the verdict `.inr v` whose error (`RecordVerdict.toError`, what the line driver turns it into)
has class `c`. -/
def VerdictClaimR {β : Type} (T : AM (β ⊕ RecordVerdict)) (a : AState) (e : Err) : Prop :=
  e.cls ≠ 0 → (∃ ce, T.run a = .error ce ∧ twinCls ce = e.cls) ∨
    ∃ v a', T.run a = .ok (.inr v, a') ∧ twinCls v.toError = e.cls

/-- The same for the other order, `AM (RecordVerdict ⊕ β)` (`validateIndD`). -/
def VerdictClaimL {β : Type} (T : AM (RecordVerdict ⊕ β)) (a : AState) (e : Err) : Prop :=
  e.cls ≠ 0 → (∃ ce, T.run a = .error ce ∧ twinCls ce = e.cls) ∨
    ∃ v a', T.run a = .ok (.inl v, a') ∧ twinCls v.toError = e.cls

/-- The common record of a declaration record (all but `inductive`). -/
def declCv? : DeclRec → Option CVRec
  | .ax cv _ | .defn cv .. | .thm cv _ | .opaq cv .. | .quot cv _ => some cv
  | .ind .. => none

/-- The scanner's `safety` word, the converse half `DeclR` does not state: a definition whose
`safety` string is `safe` does not have `flag = 0` (flag `0` is another string without an escape;
an escaped spelling of `safe` has flag `2`, where `decl_kind` aborts with class `0`). -/
def DeclSafeR (d : DeclRec) (f : DFld) : Prop :=
  ∀ cv v h s, d = .defn cv v h s → s = "safe" → f.flag ≠ 0

/-! ### The three decline sites of `decl_kind`: the twin's record verdicts -/

theorem axUnsafe_run (st : StateD) (a : AState) (cv : CVRec) (cvp : IConstantVal)
    (hpc : parseCVD st cv = pure cvp) :
    (applyRecord st (.decl (.ax cv true))).run a = .ok (.inr (.declined "unsafe axiom"), a) := by
  simp [applyLine, ConRon.Arena.Frontend.applyDeclD, ConRon.Arena.Frontend.processLineCoreD, hpc]; rfl

theorem defnSafety_run (st : StateD) (a : AState) (cv : CVRec) (cvp : IConstantVal)
    (hpc : parseCVD st cv = pure cvp) (v : Nat) (h : HintsRec) (s : String) (hs : s ≠ "safe") :
    ∃ w, (applyRecord st (.decl (.defn cv v h s))).run a = .ok (.inr (.declined w), a) := by
  refine ⟨s!"definition with safety {ConLeche.Display.str s}", ?_⟩
  simp [applyLine, ConRon.Arena.Frontend.applyDeclD, ConRon.Arena.Frontend.processLineCoreD, hpc]
  rfl

theorem opaqUnsafe_run (st : StateD) (a : AState) (cv : CVRec) (cvp : IConstantVal)
    (hpc : parseCVD st cv = pure cvp) (v : Nat) :
    (applyRecord st (.decl (.opaq cv v true))).run a =
      .ok (.inr (.declined "unsafe opaque declaration"), a) := by
  simp [applyLine, ConRon.Arena.Frontend.applyDeclD, ConRon.Arena.Frontend.processLineCoreD, hpc]; rfl

/-! ## `apply_decl`: the declines after the common data (con-ron's `parseCVD` first) -/

/-- `decl_cv` ran (`cvW`): con-ron's `parseCVD` of the record's common data succeeds. -/
theorem cvW_parse (b : ByteArray) (m m₁ : Mem) (st : StateD) (hD : StateDR m st) (f : DFld)
    (cv : CVRec) (hcv : CVR b cv f) (h : cvW b.data m f.name f.lps f.type = some m₁) :
    ∃ cvp, parseCVD st cv = pure cvp := by
  obtain ⟨hcn, hcl, hct⟩ := hcv
  unfold cvW at h
  have hok : tblOK m NID f.name = true ∧ tblOK m EID f.type = true :=
    Classical.byContradiction fun hok => by simp [hok] at h
  simp only [hok, and_self, ↓reduceIte] at h
  obtain ⟨hgn, -, hnn⟩ := tbl_read hD.names _ hok.1
  obtain ⟨hgt, -, hnt⟩ := tbl_read hD.exprs _ hok.2
  have hDR := hD.decls
  unfold lpPutW at h
  split at h
  · cases h
  rename_i hz
  have hps := hDR.psize
  have hptop := hDR.ptop
  have hrd : rdW (m.arr64 DLP) 0 = (m.arr64 DLP)[0]?.getD 0 := rfl
  obtain ⟨-, -, -, -, -, F6, -⟩ := lpLoopM_facts b.data (rdW (m.arr64 DLP) 0) m (f.lps + 1) 0 m₁
    h (by rw [hrd]; simp; omega) hps
  have hxs : Fields.itemsN b.data (f.lps + 1) = Fields.listN b.data f.lps := rfl
  rw [hxs] at F6
  have hmap := mapM_name m st hD.names _ _ hcl F6
  refine ⟨⟨decI (tblW m NID f.name), (Fields.listN b.data f.lps).map fun x => decI (tblW m NID x),
    decI (tblW m EID f.type)⟩, ?_⟩
  simp [parseCVD, ConRon.Arena.Frontend.StateD.name, getDeclD, ConRon.Arena.Frontend.StateD.expr,
    itemR_eq hcn hnn, itemR_eq hct hnt, hgn, hgt, hmap]

theorem cvW_parse' (b : ByteArray) (m m₁ : Mem) (st : StateD) (hD : StateDR m st) (f : DFld)
    (d : DeclRec) (hR : DeclR b d f) (h : cvW b.data m f.name f.lps f.type = some m₁) :
    ∀ cv, declCv? d = some cv → ∃ cvp, parseCVD st cv = pure cvp := by
  intro cv hcv
  cases d <;> simp only [declCv?, Option.some.injEq, reduceCtorEq] at hcv <;> subst hcv
  all_goals exact cvW_parse b m m₁ st hD f _ hR.2.1 h

end L.Front
