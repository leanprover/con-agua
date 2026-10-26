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

namespace L.Front.Ind
open L.Front

l_model viUnsafe_specE (p : Prog) (hf : p.lookup "vi_unsafe" = some viUnsafe)
  fns [hf ↦ viUnsafeE] grind [arena_grind] errors

/-- **The error model of `vi_unsafe`**: an error of class `!= 0` (the decline) means some type
record from `j` on is unsafe. -/
theorem unsafeE_claim {b : ByteArray} {m : Mem} {tys : List IndTypeRec} {to tn : Word}
    (hL : ListF (TyF b m) m 11 to.toNat tys) (htn : tn.toNat = tys.length)
    (hto : to.toNat + 11 * tys.length < 2 ^ 63) (p : Prog) :
    ∀ n j e, viUnsafeE p n m to tn j = .error e → e.cls ≠ 0 →
      e = .abort R_UNSAFE_INDUCTIVE_DECLARATION ∧ ∃ k, ∃ _ : k < tys.length, tys[k].isUnsafe = true := by
  intro n
  induction n with
  | zero =>
    intro j e h hk
    exfalso; apply hk
    have : viUnsafeE p 0 m to tn j = .error .outOfFuel := by simp [viUnsafeE]
    rw [this] at h; cases h; simp
  | succ n ih =>
    intro j e h hk
    by_cases hle : tn ≤ j
    · rw [viUnsafeE.arm1 p n m to tn j hle] at h; cases h
    have hj := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
    have hix : (to + 11 * j + 7).toNat = to.toNat + 11 * j.toNat + 7 := widx _ _ _ _ (by simp; omega)
    by_cases h0 : rdW (m.arr64 IFR) (to + 11 * j + 7) = 0
    · rw [viUnsafeE.arm2 p n m to tn j hle h0] at h
      cases h1 : viUnsafeE p n m to tn (j + 1) with
      | error ε =>
        rw [h1, viUnsafeE.k_vi_unsafe.none] at h
        cases h
        exact ih _ _ h1 hk
      | ok q =>
        obtain ⟨u, m₁⟩ := q
        rw [h1, viUnsafeE.k_vi_unsafe.arm1] at h; cases h
    · rw [viUnsafeE.abort1 p n m to tn j hle h0] at h
      cases h
      refine ⟨rfl, j.toNat, by omega, ?_⟩
      have h0' := h0
      rw [wd_eq, hix] at h0'
      obtain ⟨-, -, -, h7, -, -⟩ := hL.2.2 j.toNat (by omega)
      cases hu : tys[j.toNat].isUnsafe
      · exfalso; rw [hu] at h7; simp [BoolW] at h7; exact h0' h7
      · rfl

/-- **`vi_unsafe`'s error refinement**: the decline is `validateIndD`'s first check
(`tys.any isUnsafe`, a record verdict). Hypotheses of the ok refinement `unsafeW_twin`. -/
theorem viUnsafe_refinesE (p : Prog) (hp : p.lookup "vi_unsafe" = some viUnsafe) (n : Nat) (m : Mem)
    {b : ByteArray} {tys : List IndTypeRec} {to tn : Word}
    (hL : ListF (TyF b m) m 11 to.toNat tys) (htn : tn.toNat = tys.length)
    (hto : to.toNat + 11 * tys.length < 2 ^ 63) (st : StateD) (cts : List IndCtorRec)
    (rcs : List IndRecRec) (a : AState)
    (e : Err) (hc : callE p (n + 1) "vi_unsafe" [to, tn, 0] m = .error e) :
    VerdictClaimL (ConRon.Arena.Frontend.validateIndD st tys cts rcs) a e := fun hk => by
  obtain ⟨he, k, hk', hu⟩ := unsafeE_claim hL htn hto p (n + 1) 0 e
    (triple_of_callE_err (viUnsafe_specE p hp (n + 1) ⟨m, Locals.init []⟩ to tn 0) hc
      (Err.code_ne_of_cls hk)) hk
  have hany : tys.any (·.isUnsafe) = true := List.any_eq_true.mpr ⟨_, List.getElem_mem hk', hu⟩
  refine .inr ⟨.declined "unsafe inductive declaration", a, ?_, ?_⟩
  · show (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = _
    simp [ConRon.Arena.Frontend.validateIndD, hany]
    rfl
  · subst he
    simp [ConRon.Arena.Frontend.RecordVerdict.toError, Err.cls, R_UNSAFE_INDUCTIVE_DECLARATION]

end L.Front.Ind
