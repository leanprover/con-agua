import ConAgua.Front.ApplyDeclRefine
import ConAgua.Front.IndApplyRefine9
import ConAgua.Arena.Verdict

/-!
# Error refinements of `decl_kind`, `vi_unsafe` (lane `verdicts-b`, helper `c5`)
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
`safety` string is `safe` has `flag = 1` (flag `0` is another string, `2` an escaped one). -/
def DeclSafeR (d : DeclRec) (f : DFld) : Prop :=
  ∀ cv v h s, d = .defn cv v h s → s = "safe" → f.flag = 1

open L.Arena in
l_model declKind_specE (p : Prog) (hf : p.lookup "decl_kind" = some declKind)
  fns [hf ↦ declKindE] grind [arena_grind] errors

/-! ### The three decline sites of `decl_kind`: the twin's record verdicts -/

theorem axUnsafe_run (st : StateD) (a : AState) (cv : CVRec) (cvp : IConstantVal)
    (hpc : parseCVD st cv = pure cvp) :
    (applyLine st (.decl (.ax cv true))).run a = .ok (.inr (.declined "unsafe axiom"), a) := by
  simp [applyLine, ConRon.Arena.Frontend.applyDeclD, ConRon.Arena.Frontend.processLineCoreD, hpc]; rfl

theorem defnSafety_run (st : StateD) (a : AState) (cv : CVRec) (cvp : IConstantVal)
    (hpc : parseCVD st cv = pure cvp) (v : Nat) (h : HintsRec) (s : String) (hs : s ≠ "safe") :
    ∃ w, (applyLine st (.decl (.defn cv v h s))).run a = .ok (.inr (.declined w), a) := by
  refine ⟨s!"definition with safety {ConLeche.Display.str s}", ?_⟩
  simp [applyLine, ConRon.Arena.Frontend.applyDeclD, ConRon.Arena.Frontend.processLineCoreD, hpc]
  rfl

theorem opaqUnsafe_run (st : StateD) (a : AState) (cv : CVRec) (cvp : IConstantVal)
    (hpc : parseCVD st cv = pure cvp) (v : Nat) :
    (applyLine st (.decl (.opaq cv v true))).run a =
      .ok (.inr (.declined "unsafe opaque declaration"), a) := by
  simp [applyLine, ConRon.Arena.Frontend.applyDeclD, ConRon.Arena.Frontend.processLineCoreD, hpc]; rfl

theorem declKindE_claim (p : Prog) (m : Mem) (b : ByteArray) (st : StateD) (a : AState)
    (f : DFld) (d : DeclRec) (hR : DeclR b d f) (hS : DeclSafeR d f)
    (hP : ∀ cv, declCv? d = some cv → ∃ cvp, parseCVD st cv = pure cvp) :
    ∀ e, declKindE p m f.pl f.hk f.hn f.flag = .error e →
      VerdictClaimR (applyLine st (.decl d)) a e := by
  intro e he hk
  simp only [declKindE] at he
  repeat' split at he
  all_goals (try cases he)
  all_goals (try (rename_i he'; cases he'))
  all_goals (try (exfalso; exact hk (by decide)))
  · -- unsafe axiom
    rename_i h20 _ h1
    cases d with
    | ax cv u =>
      obtain ⟨-, -, hfl⟩ := hR
      have hu : u = true := by cases u <;> simp_all
      subst hu
      obtain ⟨cvp, hpc⟩ := hP cv rfl
      exact .inr ⟨_, a, axUnsafe_run st a cv cvp hpc, by decide⟩
    | _ => exact absurd (h20.symm.trans hR.1) (by decide)
  · -- definition with a safety other than `safe`
    rename_i h20 h21 h1 h2 h0
    cases d with
    | defn cv v h s =>
      have hs : s ≠ "safe" := fun hs => h1 (hS cv v h s rfl hs)
      obtain ⟨cvp, hpc⟩ := hP cv rfl
      obtain ⟨w, hw⟩ := defnSafety_run st a cv cvp hpc v h s hs
      exact .inr ⟨_, a, hw, by simp [ConRon.Arena.Frontend.RecordVerdict.toError, Err.cls, R_DEFINITION_WITH_SAFETY]⟩
    | _ => exact absurd (h21.symm.trans hR.1) (by decide)
  · -- unsafe opaque
    rename_i _ _ _ h23 _ h1
    cases d with
    | opaq cv v u =>
      obtain ⟨-, -, -, hfl⟩ := hR
      have hu : u = true := by cases u <;> simp_all
      subst hu
      obtain ⟨cvp, hpc⟩ := hP cv rfl
      exact .inr ⟨_, a, opaqUnsafe_run st a cv cvp hpc v, by decide⟩
    | _ => exact absurd (h23.symm.trans hR.1) (by decide)

/-- **`decl_kind`'s error refinement**: a failing call of class `1`/`2` claims the twin's record
verdict (or failure) for the line. Hypotheses: those of the ok refinement `applyDeclW_refines`
(`DeclR`), the scanner's `safety` converse (`DeclSafeR`), and that the twin's `parseCVD` of the
record succeeds (L reads the kind before the names; the twin parses first). -/
theorem declKind_refinesE (p : Prog) (hp : p.lookup "decl_kind" = some declKind) (n : Nat) (m : Mem)
    (b : ByteArray) (st : StateD) (a : AState) (f : DFld) (d : DeclRec) (hR : DeclR b d f)
    (hS : DeclSafeR d f) (hP : ∀ cv, declCv? d = some cv → ∃ cvp, parseCVD st cv = pure cvp)
    (e : Err) (hc : callE p (n + 1) "decl_kind" [f.pl, f.hk, f.hn, f.flag] m = .error e) :
    VerdictClaimR (applyLine st (.decl d)) a e := fun hk =>
  declKindE_claim p m b st a f d hR hS hP e
    (triple_of_callE_err (declKind_specE p hp (n + 1) ⟨m, Locals.init []⟩ f.pl f.hk f.hn f.flag) hc
      (Err.code_ne_of_cls hk)) hk

end L.Front
