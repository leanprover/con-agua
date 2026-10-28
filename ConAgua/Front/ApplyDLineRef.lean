import ConAgua.Front.FrontPreOK2
import ConAgua.Front.IndApplySpec3
import ConAgua.Front.FieldsDeclSpec

/-!
# A declaration line, both outcomes: `decl_kind`, `apply_decl`, `apply_dline`

One unified model and one refinement per function (`docs/design/unifiede.md`). The twin reports a
declined line as a value (`RecordVerdict`), so each refinement is a `RefC` whose error half is the
line's record verdict (`VerdictClaimR`), as `apply_ind`'s (`applyInd_ref`, `FrontPreOK2.lean`):

* `declKind_ref`: an ok `decl_kind` returns the record's kind and hint word (`DeclKindOk`); a
  failing one is con-ron's decline of the line (an unsafe axiom or opaque, a definition that is not
  `safe`).
* `applyDecl_ref`: an ok `apply_decl` is the twin's declaration step with the record appended
  (`ApplyDeclPost`: `declCvW_refines`, `declCvW_grow`, `declCvW_mode`); a failing one is
  `decl_kind`'s claim, the twin's `parseCVD` having run (`decl_cv` first, `cvW_parse'`).
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open ConRon.Arena ConRon.Arena.Frontend
open ConLeche.Frontend hiding StateD RecordVerdict applyLine parseBytes ParseResultD
open ConAgua.Front.FieldsLink
open L.Front.Fields (DFld NONE declLineN DeclFieldLookups recDeclLine_spec)

set_option experimental.vcgen true

namespace L.Front

/-! ## `decl_kind` -/

/-- **`decl_kind`'s unified model** (no callees). -/
l_model declKind_specE (p : Prog) (hf : p.lookup "decl_kind" = some declKind)
  fns [hf ↦ declKindE] grind [arena_grind] unified

/-- What `decl_kind`'s error arms assume: the record the fields stand for (`DeclR`), the scanner's
`safety` converse (`DeclSafeR`), and that the twin's `parseCVD` of the record succeeds
(`apply_decl` runs `decl_cv`, con-ron's `parseCVD`, first). -/
structure DeclKindG (b : ByteArray) (st : StateD) (d : DeclRec) (f : DFld) : Prop where
  dr : DeclR b d f
  safe : DeclSafeR d f
  parse : ∀ cv, declCv? d = some cv → ∃ cvp, parseCVD st cv = pure cvp

/-- **`decl_kind`, both outcomes**: an ok run returns the record's kind and hint word
(`DeclKindOk`) and keeps the memory; a failure of class `≠ 0` is the twin's decline of the line. -/
theorem declKind_ref (p : Prog) (m : Mem) (b : ByteArray) (st : StateD) (a : AState) (f : DFld)
    (d : DeclRec) :
    RefC (DeclKindG b st d f) (declKindE p m f.pl f.hk f.hn f.flag)
      (fun x => x.2 = m ∧ DeclKindOk f.pl f.hk f.hn f.flag (x.1.headD 0) (x.1.tail.headD 0))
      (VerdictClaimR (applyLine st (.decl d)) a) := by
  unfold declKindE
  repeat' split
  all_goals first
    | exact fun _ hk => absurd (by decide) hk
    | refine ⟨rfl, ?_⟩
    | skip
  · -- unsafe axiom
    rename_i h20 _ h1
    intro hG hk
    cases d with
    | ax cv u =>
      obtain ⟨-, -, hfl⟩ := hG.dr
      have hu : u = true := by cases u <;> simp_all
      subst hu
      obtain ⟨cvp, hpc⟩ := hG.parse cv rfl
      exact .inr ⟨_, a, axUnsafe_run st a cv cvp hpc, by decide⟩
    | _ => exact absurd (h20.symm.trans hG.dr.1) (by decide)
  · simp_all [DeclKindOk]
  · -- definition with a safety other than `safe`
    rename_i h20 h21 h1 h2 h0
    intro hG hk
    cases d with
    | defn cv v h s =>
      have hs : s ≠ "safe" := fun hs => hG.safe cv v h s rfl hs h0
      obtain ⟨cvp, hpc⟩ := hG.parse cv rfl
      obtain ⟨w, hw⟩ := defnSafety_run st a cv cvp hpc v h s hs
      exact .inr ⟨_, a, hw, by
        simp [ConRon.Arena.Frontend.RecordVerdict.toError, Err.cls, R_DEFINITION_WITH_SAFETY]⟩
    | _ => exact absurd (h21.symm.trans hG.dr.1) (by decide)
  · rename_i h20 h21 h1 h3 h3n
    refine .inr (.inl ⟨h21, Decidable.not_not.mp h1, rfl, rfl, fun h => h3 (.inl h),
      UInt64.not_lt.mp fun h => h3 (.inr h), by simpa [NONE] using h3n⟩)
  · simp_all [DeclKindOk]
  · -- unsafe opaque
    rename_i _ _ _ h23 _ h1
    intro hG hk
    cases d with
    | opaq cv v u =>
      obtain ⟨-, -, -, hfl⟩ := hG.dr
      have hu : u = true := by cases u <;> simp_all
      subst hu
      obtain ⟨cvp, hpc⟩ := hG.parse cv rfl
      exact .inr ⟨_, a, opaqUnsafe_run st a cv cvp hpc v, by decide⟩
    | _ => exact absurd (h23.symm.trans hG.dr.1) (by decide)
  · simp_all [DeclKindOk]
  · rename_i h24 h5 h04
    refine .inr (.inr (.inr (.inr ⟨h24, rfl, rfl, fun h => h04 (.inl h),
      UInt64.not_lt.mp fun h => h04 (.inr h)⟩)))

/-! ## `apply_decl` -/

/-- **`apply_decl`'s unified model**: `decl_cv`, `expr_get`, `decl_push` (outside the verdict
closure) lifted, `decl_kind` by its unified model. -/
l_model applyDecl_specE (p : Prog) (hf : p.lookup "apply_decl" = some applyDecl)
  (hk : p.lookup "decl_kind" = some declKind)
  fns [hf ↦ applyDeclE]
  specs [callW_spec p n "decl_cv", declKind_specE p hk n, callW_spec p n "expr_get",
    callW_spec p n "decl_push"]
  grind [arena_grind] simp [] unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `apply_decl`'s error arms assume: the no-verdict closure (the lifted callees) and the
scanner's `safety` converse for the line (`decl_kind`'s declines). -/
structure ApplyDeclG (p : Prog) (d : DeclRec) (f : DFld) : Prop where
  nv : closedNV p _root_.L.Checker.nvFns = true
  safe : DeclSafeR d f

/-- What a successful `apply_decl` from `m` gives at `m'`: the twin's declaration step accepts (the
state `a` unchanged) at a related state, the arena kept, the mode kept, one record appended. -/
structure ApplyDeclPost (st : StateD) (a : AState) (d : DeclRec) (m m' : Mem) : Prop where
  twin : ∃ st', (applyLine st (.decl d)).run a = .ok (.inl st', a) ∧ StateDR m' st'
  arena : ArenaD m' a
  mode : ModeOK m → ModeOK m'
  grow : DGrow m m'

/-- **`apply_decl` refines the declaration arms of `processLineCoreD`, both outcomes**: on fields
`f` that con-leche's scanner relates to the record `d` (`DeclR`), `decl_cv` is con-ron's
`parseCVD`, `decl_kind` its declines (`declKind_ref`), and the record pushed its declaration
(`declCvW_refines`); a failure of class `≠ 0` is the line's record verdict. -/
@[refines_part ConRon.Arena.Frontend.processLineCoreD "axiom, def, thm, opaque, quot"]
theorem applyDecl_ref {p : Prog} (hE : DeclLookups p) {b : ByteArray} (hb : b.data.size < 2 ^ 63)
    (n : Nat) {m : Mem} {a : AState} {st : StateD} (hm : m.arr8 IN = b.data) (hA : ArenaD m a)
    (hD : StateDR m st) {f : DFld} {d : DeclRec} (hR : DeclR b d f) :
    RefC (ApplyDeclG p d f) (applyDeclE p n m f.pl f.name f.lps f.type f.value f.hk f.hn f.flag)
      (fun x => ApplyDeclPost st a d m x.2) (VerdictClaimR (applyLine st (.decl d)) a) := by
  cases n with
  | zero => simp only [applyDeclE, RefC_error]; exact fun _ hk => absurd Err.cls_outOfFuel hk
  | succ n =>
  simp only [applyDeclE]
  -- `decl_cv`
  rcases h1 : callW p n "decl_cv" [f.name, f.lps, f.type] m with _ | ⟨r1, m₁⟩
  · rw [liftE_none, applyDeclE.k_decl_cv.none]; exact fun _ hk => absurd (by simp) hk
  rw [liftE_some, applyDeclE.k_decl_cv.arm1]
  obtain ⟨s1, rfl, -, rfl, hcw⟩ :=
    triple_of_callW (declCv_spec p hE b.data hb n ⟨m, Locals.init []⟩ hm f.name f.lps f.type) h1
  have hP := cvW_parse' b m s1.mem st hD f d hR hcw
  -- `decl_kind`
  have hK := declKind_ref p s1.mem b st a f d
  rcases h2 : declKindE p s1.mem f.pl f.hk f.hn f.flag with e2 | ⟨r2, m₂⟩
  · rw [applyDeclE.k_decl_kind.none]
    rw [h2] at hK
    exact fun hG => hK ⟨hR, hG.safe, hP⟩
  rw [h2] at hK
  obtain ⟨rfl, hks⟩ := hK
  dsimp only at hks hcw
  have hk5 := hks.k5
  have hcv := declCvW_of_cv hcw (r2.headD 0) (r2.tail.headD 0) f.value f.hn
  -- the value and the push: `declCvW`'s record
  have fin : ∀ m', declCvW b.data m (r2.headD 0) (r2.tail.headD 0) f.name f.lps f.type f.value f.hn =
      some m' → ApplyDeclPost st a d m m' := fun m' hW => by
    obtain ⟨st', hp, hA', hD'⟩ := declCvW_refines b m m' a st hA hD f d hR hks hW
    exact ⟨⟨st', by rw [hp]; rfl, hD'⟩, hA', declCvW_mode b.data m m' st hD _ _ _ _ _ _ _ hW,
      declCvW_grow b.data m m' st hD hk5 _ _ _ _ _ hW⟩
  by_cases hk234 : r2.headD 0 = 2 ∨ r2.headD 0 = 3 ∨ r2.headD 0 = 4
  · rw [applyDeclE.k_decl_kind.arm1 _ _ _ _ _ _ _ _ _ _ hk234]
    rcases h3 : callW p n "expr_get" [f.value] s1.mem with _ | ⟨r3, m₃⟩
    · rw [liftE_none, applyDeclE.k_expr_get.none]; exact fun _ hk => absurd (by simp) hk
    rw [liftE_some, applyDeclE.k_expr_get.arm1, applyDeclE.j1]
    obtain ⟨s3, rfl, rfl, hok3, rfl⟩ :=
      triple_of_callW (exprGet_spec p hE.expr n ⟨s1.mem, Locals.init []⟩ f.value) h3
    dsimp only at hok3 ⊢
    rcases h4 : callW p n "decl_push" _ s1.mem with _ | ⟨r4, m₄⟩
    · rw [liftE_none, applyDeclE.k_decl_push.none]; exact fun _ hk => absurd (by simp) hk
    rw [liftE_some, applyDeclE.k_decl_push.arm1]
    obtain ⟨s4, rfl, -, hp4⟩ :=
      triple_of_callW (declPush_spec p hE n ⟨s1.mem, Locals.init []⟩ _ _ _ _ _ _ _ _) h4
    exact fin _ (by rw [hcv, declK1_some, ite_eq_left hk234, ite_eq_left hok3]; exact hp4)
  · rw [applyDeclE.k_decl_kind.arm2 _ _ _ _ _ _ _ _ _ _ hk234, applyDeclE.j1]
    rcases h4 : callW p n "decl_push" _ s1.mem with _ | ⟨r4, m₄⟩
    · rw [liftE_none, applyDeclE.k_decl_push.none]; exact fun _ hk => absurd (by simp) hk
    rw [liftE_some, applyDeclE.k_decl_push.arm1]
    obtain ⟨s4, rfl, -, hp4⟩ :=
      triple_of_callW (declPush_spec p hE n ⟨s1.mem, Locals.init []⟩ _ _ _ _ _ _ _ _) h4
    exact fin _ (by rw [hcv, declK1_some, ite_eq_right hk234]; exact hp4)

/-! ## `apply_dline` -/

/-- The lookups of a declaration line's apply step: `apply_dline`, its record's fields, and the
`inductive` entries (the declaration functions are `IndApplyLookups.decl`). -/
structure DLineLookups (p : Prog) : Prop extends L.Front.Ind.IndLineLookups p where
  apply_dline : p.lookup "apply_dline" = some applyDLine
  dfields : DeclFieldLookups p

/-- **`apply_dline`'s unified model**: `rec_decl_line` (outside the verdict closure) lifted,
`apply_ind` and `apply_decl` by their unified models. -/
l_model applyDLine_specE (p : Prog) (hf : p.lookup "apply_dline" = some applyDLine)
  (hi : p.lookup "apply_ind" = some L.Front.Ind.applyInd)
  (hd : p.lookup "apply_decl" = some applyDecl) (hk : p.lookup "decl_kind" = some declKind)
  fns [hf ↦ applyDLineE]
  specs [callW_spec p n "rec_decl_line", L.Front.Ind.applyInd_specE p hi n, applyDecl_specE p hd hk n]
  grind [arena_grind] simp [] unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `apply_dline`'s error arms assume: `apply_ind`'s (`ApplyIndG`: the no-verdict closure,
the twin's name reads) and the scanner's `safety` converse for the line's record. -/
structure ApplyDLineG (p : Prog) (b : ByteArray) (st : StateD) (a : AState) (j : Word) (r : LineRec) :
    Prop where
  ind : L.Front.Ind.ApplyIndG p st a
  safe : (declLineN b.data j).pl ≠ 0 → ∀ d, r = .decl d → DeclSafeR d (declLineN b.data j)

/-- What a successful `apply_dline` from `m` gives at `m'`: con-ron's `applyLine` accepts the record
(the state `a` unchanged) at a related state, the arena kept, the mode kept, one record appended. -/
structure ApplyDLinePost (st : StateD) (a : AState) (r : LineRec) (m m' : Mem) : Prop where
  twin : ∃ st', (applyLine st r).run a = .ok (.inl st', a) ∧ StateDR m' st'
  arena : ArenaD m' a
  mode : ModeOK m → ModeOK m'
  grow : DGrow m m'

/-- **`apply_dline` refines con-ron's `applyLine` on a declaration line, both outcomes**: the
record is con-leche's (`declLine_link`); an inductive block is `apply_ind`'s (`applyInd_ref`), any
other declaration `apply_decl`'s (`applyDecl_ref`). -/
theorem applyDLine_ref {p : Prog} (hF : DeclFieldLookups p) (hDL : DeclLookups p)
    (hAL : L.Front.Ind.IndApplyLookups p) (hFI : L.Front.Ind.IndFieldLookups p)
    (hII : L.Front.Ind.IndInstallLookups p) {b : ByteArray} (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) {m : Mem} {a : AState} {st : StateD}
    (hm : m.arr8 IN = b.data) (hA : ArenaD m a) (hD : StateDR m st) (hok : ConRon.Bridge.StateOK a)
    {j : USize} {r : LineRec} {e' : USize} (hloop : scanLineLoop b j true 0 0 .absent = .ok r e') :
    RefC (ApplyDLineG p b st a j.toUInt64 r) (applyDLineE p n m j.toUInt64)
      (fun x => ApplyDLinePost st a r m x.2) (VerdictClaimR (applyLine st r) a) := by
  cases n with
  | zero => simp only [applyDLineE, RefC_error]; exact fun _ hk => absurd Err.cls_outOfFuel hk
  | succ n =>
  simp only [applyDLineE]
  rcases h1 : callW p n "rec_decl_line" [j.toUInt64] m with _ | ⟨r1, m₁⟩
  · rw [liftE_none, applyDLineE.k_rec_decl_line.none]; exact fun _ hk => absurd (by simp) hk
  rw [liftE_some]
  obtain ⟨s1, rfl, rfl, rfl⟩ :=
    triple_of_callW (recDeclLine_spec p hF b.data hsize n ⟨m, Locals.init []⟩ hm j.toUInt64) h1
  dsimp only
  generalize hf : declLineN b.data j.toUInt64 = f
  by_cases h0 : f.pl = 0
  · rw [applyDLineE.k_rec_decl_line.abort1 _ _ _ _ (by simpa [DFld.enc] using h0)]
    exact fun _ hk => absurd (by decide) hk
  have hX : DRecR b r f := by
    rw [← hf]; exact declLine_link b h64 hsize j true 0 0 .absent DFld.none r e' hloop trivial
      (by show (declLineN b.data j.toUInt64).pl ≠ 0; rw [hf]; exact h0)
  rcases r with _ | _ | _ | d | _ | _ <;> simp only [DRecR] at hX
  by_cases h25 : f.pl = 25
  · rw [applyDLineE.k_rec_decl_line.arm1 _ _ _ _ (by simpa [DFld.enc] using h0)
      (by simpa [DFld.enc] using h25)]
    cases d with
    | ind tys cts rcs =>
      obtain ⟨-, v, hv, e'', hscan⟩ := hX
      simp only [DFld.enc, List.headD_cons, List.tail_cons, hv]
      have hI := L.Front.Ind.applyInd_ref hAL hFI hII h64 hsize n hm hA hD hok hscan
      rcases h2 : L.Front.Ind.applyIndE p n m v.toUInt64 with e2 | ⟨z, m₂⟩
      · rw [h2] at hI; exact fun hG => hI hG.ind
      rw [h2] at hI
      exact ⟨hI.twin, hI.arena, hI.mode, hI.grow⟩
    | ax _ _ => exact absurd (hX.1.symm.trans h25) (by decide)
    | defn _ _ _ _ => exact absurd (hX.1.symm.trans h25) (by decide)
    | thm _ _ => exact absurd (hX.1.symm.trans h25) (by decide)
    | opaq _ _ _ => exact absurd (hX.1.symm.trans h25) (by decide)
    | quot _ _ => exact absurd (hX.1.symm.trans h25) (by decide)
  rw [applyDLineE.k_rec_decl_line.arm2 _ _ _ _ (by simpa [DFld.enc] using h0)
    (by simpa [DFld.enc] using h25)]
  simp only [DFld.enc, List.headD_cons, List.tail_cons]
  have hR := applyDecl_ref hDL hsize n hm hA hD hX (p := p) (a := a)
  rcases h2 : applyDeclE p n m f.pl f.name f.lps f.type f.value f.hk f.hn f.flag with e2 | ⟨z, m₂⟩
  · rw [h2] at hR
    exact fun hG => hR ⟨hG.ind.nv, by rw [← hf]; exact hG.safe (by rw [hf]; exact h0) d rfl⟩
  rw [h2] at hR
  exact ⟨hR.twin, hR.arena, hR.mode, hR.grow⟩

/-- **A run of `apply_dline` (`runF`, the front's line model's reading of it) is its
refinement's ok half.** -/
theorem applyDLine_runF {p : Prog} (hXI : DLineLookups p) (hAL : L.Front.Ind.IndApplyLookups p)
    (hFI : L.Front.Ind.IndFieldLookups p) (hII : L.Front.Ind.IndInstallLookups p) {b : ByteArray}
    (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63) {m m' : Mem} {a : AState}
    {st : StateD} (hm : m.arr8 IN = b.data) (hA : ArenaD m a) (hD : StateDR m st)
    (hok : ConRon.Bridge.StateOK a) {j : USize} {r : LineRec} {e' : USize}
    (hloop : scanLineLoop b j true 0 0 .absent = .ok r e')
    (h : runF p "apply_dline" [j.toUInt64] m = some m') : ApplyDLinePost st a r m m' := by
  obtain ⟨x, hx, hxm⟩ := runF_some h
  have hW := M.of_run' (P := fun s => s = ⟨m, Locals.init []⟩) rfl hx
    (applyDLine_specE p hXI.apply_dline hXI.apply_ind hAL.decl.apply_decl hAL.decl.decl_kind x.1 _
      j.toUInt64)
  have hP := applyDLine_ref hXI.dfields hAL.decl hAL hFI hII h64 hsize x.1 hm hA hD hok hloop
  rw [hW.2, hxm] at hP
  exact hP

end L.Front
