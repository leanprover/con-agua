import ConAgua.Arena.InferBodyIntern
import ConAgua.Arena.InferLeaves
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The `let` clause of `inferBody` and the chained binder clauses of `inferBodyIO` (lane `defeq`)

Each function has one unified model and one refinement for both outcomes (`RefE` with `CorePost`,
`InferG`): the slots and `ensure_sort` through their runs, the callees outside the verdict closure
lifted, threaded through the twin's `do` blocks by `RefE.bind_core`.

* `infer_let` refines `inferBody`'s `.letE` clause (`inferLetT`, `inferBody_let`; `ilet_ref`).
* `infer_lam_io` and `infer_forall_io` refine `inferBodyIO`'s `.lam` and `.forallE` clauses
  (`inferLamIOT`, `inferForallIOT`) at the io view of the knot (`ilam_ref`, `ifa_ref`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- What the body specs need of a program (beyond `InferLeafProg` and `KnotProg`). -/
structure InferBodyProg (p : Prog) : Prop where
  inferLet : p.lookup "infer_let" = some inferLetL
  inferLamIO : p.lookup "infer_lam_io" = some inferLamIOL
  inferForallIO : p.lookup "infer_forall_io" = some inferForallIOL
  fvf : p.lookup "fvar_find" = some fvarFind
  fvp : p.lookup "fvar_push" = some fvarPush
  fvi : p.lookup "intern_fvar" = some internFVar
  sof : p.lookup "sort_find" = some sortFind
  sop : p.lookup "sort_push" = some sortPush
  soi : p.lookup "intern_sort" = some internSort
  imf : p.lookup "imax_find" = some imaxFind
  imp : p.lookup "imax_push" = some imaxPush
  imi : p.lookup "intern_imax" = some internImax
  suf : p.lookup "succ_find" = some succFind
  sup : p.lookup "succ_push" = some succPush
  sui : p.lookup "intern_succ" = some internSucc

/-- **`intern_fvar` refines `internE (.fvar …)` under `CoreS`, as its `CoreSpec`** (for
`RefE.bind_callW`). -/
theorem internFVar_coreSpec {p : Prog} (hb : InferBodyProg p) (n : Nat) (s₀ : St) {a : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn s₀.mem a vis fe M eb) (u ty : Word) (hty : HW ty) :
    CoreSpec p n "intern_fvar" [u, ty] (internE (.fvar u.toNat (decE ty))) decH s₀ a dn vis fe M eb :=
  L.M.triple_of_run fun _ _ _ hp hr => by
    subst hp
    obtain ⟨hl, hfv⟩ := L.M.of_run (P := fun s => s = _) rfl hr
      (internFVar_spec p hb.fvf hb.fvp hb.fvi n _ u ty)
    exact ⟨hl, internFVar_core hS u ty hty _ hfv⟩

/-! ## Sequencing -/

/-- **A core run, then a core run at its result**: the refinement of a `>>=`. -/
theorem coreRef_bind {α β : Type} [Inhabited α] [Inhabited β] {T₁ : AM α} {T₂ : α → AM β}
    {a₀ : AState} {dec₁ : List Word → α} {dec : List Word → β} {dn : NIdx → Option ConLeche.Name}
    {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r₁ r : List Word}
    {ok₁ ok : List Word → Prop}
    (h₁ : CoreRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb →
      CoreRef (T₂ (dec₁ r₁)) (AM.st T₁ a₀) dec dn m₁ vis fe M' eb r m ok) :
    CoreRef (T₁ >>= T₂) a₀ dec dn m₀ vis fe M eb r m ok :=
  coreRef_then h₁ h₂ (by
    rw [StateT.run_bind, AM.run_of_ok _ _ h₁.run, h₁.res]; rfl)

/-- `ensure_sort` at every L fuel up to `n + 1` from the knot up to `n`. -/
theorem ensureSortSpec_of_knot (p : Prog) (hp : InferLeafProg p) :
    ∀ n, KnotUpTo p n → EnsureSortSpec p n
  | 0, _ => fun F s₀ a₀ dn vis fe M eb mode d e _ _ _ _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk => ensureSort_refines p hp n (hk.mono (by omega))

/-! ## `infer_let`: the `.letE` clause -/

/-- **The `.letE` clause of `inferBody`**, copied: the twin fragment `infer_let` refines. -/
def inferLetT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (ty v b : EIdx) : AM EIdx := do
  let tty ← r.infer depth ty
  let _ ← ensureSort r fe depth tty
  let tv ← r.infer depth v
  if !(← r.defeq depth tv ty) then
    fail (.invalid "let value type mismatch")
  else do
    let ob ← instantiate1Fast coreWalkFuel b v 0
    r.infer depth ob

/-- `inferBody`'s `.letE` arm is `inferLetT`. -/
@[refines_part ConRon.Arena.inferBody "letE"]
theorem inferBody_let (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)
    (ty v b : EIdx) (hv : a.store.view e = some (.letE ty v b)) :
    (inferBody r fe d e).run a = (inferLetT r fe d ty v b).run a := by
  simp only [inferBody, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  rfl

/-- **`infer_let`'s unified model**: the slots and `ensure_sort` through their runs, `inst1` lifted. -/
l_model iletE_spec (p : Prog) (hf : p.lookup "infer_let" = some inferLetL)
  fns [hf ↦ iletE list]
  specs [callW_spec p n "inst1"]
  grind [arena_grind] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- Peel one call off a model: the run exists, and the model is the continuation's. -/
theorem callW_cases {f : FnName} {p : Prog} {n : Nat} {vs : List Word} {m : Mem}
    {K : Option (List Word × Mem) → Option (Word × Mem)} {x : Word × Mem}
    (hK : K none = none) (h : K (callW p n f vs m) = some x) :
    ∃ r₁ m₁, callW p n f vs m = some (r₁, m₁) ∧ K (some (r₁, m₁)) = some x := by
  cases hc : callW p n f vs m with
  | none => rw [hc, hK] at h; cases h
  | some q => exact ⟨q.1, q.2, rfl, by rw [hc] at h; exact h⟩

/-- **`infer_let` refines the `.letE` clause** (`inferLetT`) at the knot, both outcomes: the
slots' (`infer`, `defeq`) and `ensure_sort`'s errors, a value of another type rejects; `inst1`
claims nothing. -/
theorem ilet_ref (p : Prog) (hp : InferLeafProg p) (hi1 : Inst1OK p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d ty v b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hv : HW v) (hbb : HW b) :
    RefE (InferG p n) (iletE p (n + 1) s₀.mem mode vis d ty v b)
      (inferLetT (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) (decE v) (decE b)) a₀
      (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  simp only [iletE, inferLetT]
  refine RefE.bind_callE (fun _ => rfl) (hK.infer F s₀ a₀ dn vis fe M eb mode d ty hF hn hs hty)
    (fun (hG : InferG p n) => (hG.knot n (Nat.le_refl _)).infer F s₀ a₀ dn vis fe M eb mode d ty hF hn hs hty)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [iletE.k_infer]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (ensureSortSpec_of_knot p hp n hk F _ _ dn vis fe M₁ eb mode d
      (r₁.headD 0) hF hn hs₁ h₁.resOk)
    (fun (hG : InferG p n) => ensureSortSpecE_of_knot p hp n hk hG.knot F _ _ dn vis fe M₁ eb mode d
      (r₁.headD 0) hF hn hs₁ h₁.resOk) fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  dsimp only [iletE.k_ensure_sort]
  have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.infer F _ _ dn vis fe M₂ eb mode d v hF hn hs₂ hv)
    (fun (hG : InferG p n) => (hG.knot n (Nat.le_refl _)).infer F _ _ dn vis fe M₂ eb mode d v hF hn hs₂ hv)
    fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ _ => ?_
  dsimp only [iletE.k_infer_2]
  have hs₃ : SlotPre ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode := ⟨hS₃, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.defeq F _ _ dn vis fe M₃ eb mode d (r₃.headD 0) ty hF hn hs₃
      h₃.resOk hty)
    (fun (hG : InferG p n) => (hG.knot n (Nat.le_refl _)).defeq F _ _ dn vis fe M₃ eb mode d (r₃.headD 0) ty
      hF hn hs₃ h₃.resOk hty) fun r₄ m₄ _ h₄ => RefE.after_core (w := id) h₄ fun M₄ hS₄ _ => ?_
  dsimp only [iletE.k_defeq]
  refine RefE.guardThen (by rfl) (fun h0 => by simp only [decBool, h0]; rfl)
    (fun hb => by simpa [decBool] using hb) fun _ _ => ?_
  refine RefE.bind_callW (fun _ => rfl) (hi1 n ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb b v 0 hS₄ hbb hv)
    fun r₅ m₅ _ h₅ => RefE.after_core (w := id) h₅ fun M₅ hS₅ _ => ?_
  dsimp only [iletE.k_inst1]
  rcases c6 : callE p n "infer" [mode, vis, d, r₅.headD 0] m₅ with e6 | ⟨r₆, m₆⟩
  · exact fun hG => CoreSpecE.of_callE (s₀ := ⟨m₅, Locals.init []⟩)
      ((hG.knot n (Nat.le_refl _)).infer F _ _ dn vis fe M₅ eb mode d (r₅.headD 0) hF hn
        ⟨hS₅, hs.mode4, hs.eb_mode⟩ h₅.resOk) c6
  obtain ⟨hrun, hP⟩ := (CoreSpec.of_callW (hK.infer F ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb mode d
    (r₅.headD 0) hF hn ⟨hS₅, hs.mode4, hs.eb_mode⟩ h₅.resOk) (callW_of_callE c6)).post
  exact RefE.ret hrun ⟨hP.after, hP.res, hP.valid⟩

/-- **`infer_let` refines the `.letE` clause** (`inferLetT`) at the knot (`ilet_ref`'s ok half). -/
@[refines_part ConRon.Arena.inferBody "letE (inferLetT)"]
theorem inferLet_refines (p : Prog) (hp : InferLeafProg p) (hb : InferBodyProg p)
    (hi1 : Inst1OK p) (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty v b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (hty : HW ty) (hv : HW v) (hbb : HW b) :
    CoreSpec p (n + 1) "infer_let" [mode, vis, d, ty, v, b]
      (inferLetT (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) (decE v) (decE b)) decH
      s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (iletE_spec p hb.inferLet (n + 1) s₀ mode vis d ty v b)
    (ilet_ref p hp hi1 n hk F s₀ a₀ dn vis fe M eb mode d ty v b hF hn hs hty hv hbb)

/-! ## `infer_lam_io`: the io body's `.lam` clause -/

/-- **The `.lam` clause of `inferBodyIO`**, copied. -/
def inferLamIOT (r : CoreFnsA) (depth : Nat) (ty body : EIdx) : AM EIdx := do
  let fv ← internE (.fvar depth ty)
  let ob ← instantiate1Fast coreWalkFuel body fv 0
  let bt ← r.infer (depth + 1) ob
  inferLamResult ty bt depth

/-- `inferBodyIO`'s `.lam` arm is `inferLamIOT`. -/
@[refines_part ConRon.Arena.inferBodyIO "lam"]
theorem inferBodyIO_lam (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)
    (ty body : EIdx) (hv : a.store.view e = some (.lam ty body)) :
    (inferBodyIO r fe d e).run a = (inferLamIOT r d ty body).run a := by
  simp only [inferBodyIO, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  rfl

/-- **`infer_lam_io`'s unified model**: the `infer_io` slot through its run, the rest lifted. -/
l_model ilamE_spec (p : Prog) (hf : p.lookup "infer_lam_io" = some inferLamIOL)
  fns [hf ↦ ilamE list]
  specs [callW_spec p n "intern_fvar", callW_spec p n "inst1", callW_spec p n "infer_lam_result"]
  grind [arena_grind] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `infer_lam_result` at every L fuel. -/
theorem inferLamResult_any (p : Prog) (hp : InferLeafProg p) (ha : Abstract1OK p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb ty bt d : Word) (hS : CoreS dn s₀.mem a₀ vis fe M eb) (hbt : HW bt) :
    CoreSpec p n "infer_lam_result" [ty, bt, d]
      (inferLamResult (decE ty) (decE bt) d.toNat) decH s₀ a₀ dn vis fe M eb := by
  cases n with
  | zero => exact CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | succ n => exact inferLamResult_refines p hp n ha s₀ a₀ dn vis fe M eb ty bt d hS hbt

theorem toNat_succ_of_ne {d : Word} (h : ¬ d + 1 = 0) : (d + 1).toNat = d.toNat + 1 := by
  rw [UInt64.toNat_add]
  have : d.toNat + 1 < 2 ^ 64 := by
    rcases Nat.lt_or_ge (d.toNat + 1) (2 ^ 64) with h' | h'
    · exact h'
    · exfalso; apply h
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add]; have := d.toNat_lt; simp; omega
  simp; omega

/-- **`infer_lam_io` refines the io body's `.lam` clause** (`inferLamIOT`) at the io view of the
knot, both outcomes: the body's type (the `infer_io` slot at `d + 1`); the rest claims nothing. -/
theorem ilam_ref (p : Prog) (hp : InferLeafProg p) (hb : InferBodyProg p)
    (hi1 : Inst1OK p) (ha1 : Abstract1OK p) (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    RefE (InferG p n) (ilamE p (n + 1) s₀.mem mode vis d ty body)
      (inferLamIOT (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) d.toNat (decE ty) (decE body))
      a₀ (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  simp only [ilamE, inferLamIOT]
  refine RefE.abort0 (by rfl) fun hd => ?_
  rw [← toNat_succ_of_ne hd]
  refine RefE.bind_callW (fun _ => rfl) (internFVar_coreSpec hb n s₀ hs.rel d ty hty)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [ilamE.k_intern_fvar]
  refine RefE.bind_callW (fun _ => rfl) (hi1 n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb body (r₁.headD 0) 0 hS₁
    hbody h₁.resOk) fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  dsimp only [ilamE.k_inst1]
  have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.inferIO F _ _ dn vis fe M₂ eb mode (d + 1) (r₂.headD 0) hF hn hs₂
      h₂.resOk)
    (fun (hG : InferG p n) => (hG.knot n (Nat.le_refl _)).inferIO F _ _ dn vis fe M₂ eb mode (d + 1)
      (r₂.headD 0) hF hn hs₂ h₂.resOk) fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ _ => ?_
  dsimp only [ilamE.k_infer_io]
  rcases c4 : callW p n "infer_lam_result" [ty, r₃.headD 0, d] m₃ with _ | ⟨r₄, m₄⟩
  · rw [liftE_none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hrun, hP⟩ := (CoreSpec.of_callW (inferLamResult_any p hp ha1 n ⟨m₃, Locals.init []⟩ _ dn vis
    fe M₃ eb ty (r₃.headD 0) d hS₃ h₃.resOk) c4).post
  exact RefE.ret hrun ⟨hP.after, hP.res, hP.valid⟩

/-- **`infer_lam_io` refines the io body's `.lam` clause** (`inferLamIOT`) at the io view of the
knot (`ilam_ref`'s ok half). -/
@[refines_part ConRon.Arena.inferBodyIO "lam (inferLamIOT)"]
theorem inferLamIO_refines (p : Prog) (hp : InferLeafProg p) (hb : InferBodyProg p)
    (hi1 : Inst1OK p) (ha1 : Abstract1OK p) (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    CoreSpec p (n + 1) "infer_lam_io" [mode, vis, d, ty, body]
      (inferLamIOT (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) d.toNat (decE ty) (decE body))
      decH s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (ilamE_spec p hb.inferLamIO (n + 1) s₀ mode vis d ty body)
    (ilam_ref p hp hb hi1 ha1 n hk F s₀ a₀ dn vis fe M eb mode d ty body hF hn hs hty hbody)

/-! ## `infer_forall_io`: the io body's `.forallE` clause -/

/-- **The `.forallE` clause of `inferBodyIO`**, copied. -/
def inferForallIOT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (ty body : EIdx) : AM EIdx := do
  let hh ← r.whnf depth (← r.infer depth ty)
  if hh.tag == ETag.sort then
    match ← view hh with
    | .sort u => do
      let fv ← internE (.fvar depth ty)
      let ob ← instantiate1Fast coreWalkFuel body fv 0
      let v ← ensureSort r fe (depth + 1) (← r.infer (depth + 1) ob)
      let iu ← internLNode (.imax u v)
      internE (.sort iu)
    | _ => fail (.invalid "expected a sort")
  else fail (.invalid "expected a sort")

/-- `inferBodyIO`'s `.forallE` arm is `inferForallIOT`. -/
@[refines_part ConRon.Arena.inferBodyIO "forallE"]
theorem inferBodyIO_forall (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)
    (ty body : EIdx) (hv : a.store.view e = some (.forallE ty body)) :
    (inferBodyIO r fe d e).run a = (inferForallIOT r fe d ty body).run a := by
  simp only [inferBodyIO, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  rfl

/-- **`infer_forall_io`'s unified model**: the slots and `ensure_sort` through their runs, the
interning and `inst1` lifted. -/
l_model ifaE_spec (p : Prog) (hf : p.lookup "infer_forall_io" = some inferForallIOL)
  fns [hf ↦ ifaE list]
  specs [callW_spec p n "intern_fvar", callW_spec p n "inst1", callW_spec p n "intern_imax",
    callW_spec p n "intern_sort"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_tagE]
  unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **A forwarded run meets its callee's spec.** -/
theorem of_call1W {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {m m' : Mem} {w : Word}
    {X : Mem → Word → Mem → Prop}
    (h : ∀ s₀ : St, ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs
      ⦃fun r s' => LocEq s' s₀ ∧ X s₀.mem (r.headD 0) s'.mem; ⊤⦄)
    (hc : call1W p n f vs m = some (w, m')) : X m w m' := by
  rcases hcall : callW p n f vs m with _ | ⟨r₁, m₁⟩ <;> simp only [hcall, call1W, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨s', hs', -, hX⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (h _) hcall
  rw [hs'] at hX; exact hX

/-- **`infer_forall_io` refines the io body's `.forallE` clause** (`inferForallIOT`) at the io
view of the knot, both outcomes: the slots' (`infer_io` twice, `whnf`) and `ensure_sort`'s errors,
a domain type that is no sort rejects; the interning and `inst1` claim nothing. -/
theorem ifa_ref (p : Prog) (hp : InferLeafProg p) (hb : InferBodyProg p)
    (hi1 : Inst1OK p) (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    RefE (InferG p n) (ifaE p (n + 1) s₀.mem mode vis d ty body)
      (inferForallIOT (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE ty)
        (decE body)) a₀ (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  simp only [ifaE, inferForallIOT]
  refine RefE.abort0 (by rfl) fun hd => ?_
  rw [← toNat_succ_of_ne hd]
  refine RefE.bind_callE (fun _ => rfl) (hK.inferIO F s₀ a₀ dn vis fe M eb mode d ty hF hn hs hty)
    (fun (hG : InferG p n) => (hG.knot n (Nat.le_refl _)).inferIO F s₀ a₀ dn vis fe M eb mode d ty hF hn hs hty)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [ifaE.k_infer_io]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.whnf F _ _ dn vis fe M₁ eb mode d (r₁.headD 0) hF hn hs₁ h₁.resOk)
    (fun (hG : InferG p n) => (hG.knot n (Nat.le_refl _)).whnf F _ _ dn vis fe M₁ eb mode d (r₁.headD 0) hF hn
      hs₁ h₁.resOk) fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  dsimp only [ifaE.k_whnf]
  refine RefE.guardIf (by rfl) (tag_sort_ne _ h₂.resOk)
    (fun hb g => Bool.noConfusion ((tag_sort_beq _ h₂.resOk g).symm.trans hb)) fun g1 _ => ?_
  refine RefE.abort0 (by rfl) fun g2 => ?_
  refine RefE.abort0 (by rfl) fun g3 => ?_
  have hg : tagW (r₂.headD 0) = 2 := by simpa using g1
  obtain ⟨hv, hu⟩ := L.Ind.view_sort_f m₂ _ hS₂.arena.base (r₂.headD 0) h₂.resOk ⟨g2, by simpa using g3⟩ hg
  refine RefE.bind_right (view_run _ _ _ hv) ?_
  refine RefE.bind_callW (fun _ => rfl) (internFVar_coreSpec hb n ⟨m₂, Locals.init []⟩ hS₂ d ty hty)
    fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ hT₃ => ?_
  dsimp only [ifaE.k_intern_fvar]
  refine RefE.bind_callW (fun _ => rfl) (hi1 n ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb body (r₃.headD 0) 0 hS₃
    hbody h₃.resOk) fun r₄ m₄ _ h₄ => RefE.after_core (w := id) h₄ fun M₄ hS₄ hT₄ => ?_
  dsimp only [ifaE.k_inst1]
  have hs₄ : SlotPre ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode := ⟨hS₄, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.inferIO F _ _ dn vis fe M₄ eb mode (d + 1) (r₄.headD 0) hF hn hs₄
      h₄.resOk)
    (fun (hG : InferG p n) => (hG.knot n (Nat.le_refl _)).inferIO F _ _ dn vis fe M₄ eb mode (d + 1)
      (r₄.headD 0) hF hn hs₄ h₄.resOk) fun r₅ m₅ _ h₅ => RefE.after_core (w := id) h₅ fun M₅ hS₅ hT₅ => ?_
  dsimp only [ifaE.k_infer_io_2]
  have hs₅ : SlotPre ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb mode := ⟨hS₅, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (ensureSortSpec_of_knot p hp n hk F _ _ dn vis fe M₅ eb mode (d + 1)
      (r₅.headD 0) hF hn hs₅ h₅.resOk)
    (fun (hG : InferG p n) => ensureSortSpecE_of_knot p hp n hk hG.knot F _ _ dn vis fe M₅ eb mode (d + 1)
      (r₅.headD 0) hF hn hs₅ h₅.resOk) fun r₆ m₆ _ h₆ => RefE.after_core (w := id) h₆ fun M₆ hS₆ hT₆ => ?_
  dsimp only [ifaE.k_ensure_sort]
  obtain ⟨x₆, hx₆⟩ := ensureSort_view (AM.run_of_ok _ _ h₆.run)
  rw [h₆.res] at hx₆
  have hdu := lvl_den_later hS₂.arena.base hS₆.arena.base hS₆.den
    (hT₃.trans (hT₄.trans (hT₅.trans hT₆))).pool.lvl hu (hS₂.den.sort _ _ hv)
  have hdv := hS₆.den.sort _ _ hx₆
  rcases c7 : callW p n "intern_imax" [_, r₆.headD 0] m₆ with _ | ⟨r₇, m₇⟩
  · rw [liftE_none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s₇, hs₇, -, him⟩ := triple_of_callW
    (internImax_spec p hb.imf hb.imp hb.imi n ⟨m₆, Locals.init []⟩ _ (r₆.headD 0)) c7
  rw [hs₇] at him
  have h₇ := internImax_core hS₆ _ _ hu h₆.resOk r₇ him hdu hdv
  have hd7 := internLNode_res_den hS₆
    (fun c hc => by
      simp only [LNodeView.lchildren, List.mem_cons, List.mem_nil_iff, or_false] at hc; rcases hc with rfl | rfl
      · exact hdu
      · exact hdv)
    (fun n hn => by simp [LNodeView.nchildren] at hn) h₇.run
  rw [h₇.res] at hd7
  refine RefE.bind_core (w := id) h₇ (fun M₇ hS₇ _ => ?_)
  simp only [ifaE.k_intern_imax]
  rcases c8 : callW p n "intern_sort" [r₇.headD 0] m₇ with _ | ⟨r₈, m₈⟩
  · rw [liftE_none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s₈, hs₈, -, hso⟩ := triple_of_callW
    (internSort_spec p hb.sof hb.sop hb.soi n ⟨m₇, Locals.init []⟩ (r₇.headD 0)) c8
  rw [hs₈] at hso
  obtain ⟨hrun, hP⟩ := (internSort_core hS₇ (r₇.headD 0) h₇.resOk r₈ hso hd7).post
  exact RefE.ret hrun ⟨hP.after, hP.res, hP.valid⟩

/-- **`infer_forall_io` refines the io body's `.forallE` clause** (`inferForallIOT`) at the io
view of the knot (`ifa_ref`'s ok half). -/
@[refines_part ConRon.Arena.inferBodyIO "forallE (inferForallIOT)"]
theorem inferForallIO_refines (p : Prog) (hp : InferLeafProg p) (hb : InferBodyProg p)
    (hi1 : Inst1OK p) (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    CoreSpec p (n + 1) "infer_forall_io" [mode, vis, d, ty, body]
      (inferForallIOT (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE ty)
        (decE body)) decH s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (ifaE_spec p hb.inferForallIO (n + 1) s₀ mode vis d ty body)
    (ifa_ref p hp hb hi1 n hk F s₀ a₀ dn vis fe M eb mode d ty body hF hn hs hty hbody)

end L.Arena
