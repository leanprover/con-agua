import ConAgua.Arena.InferBodyIntern
import ConAgua.Arena.InferLeaves
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The `let` clause of `inferBody` and the chained binder clauses of `inferBodyIO` (lane `defeq`)

The callW pattern (`InferLeaves.lean`): a word model of each function with its callees through
their runs (`callW`), the L spec by `vcgen` + `finish`, the refinement from the callees' specs,
threaded through the twin's `do` blocks by `coreRef_bind`.

* `infer_let` refines `inferBody`'s `.letE` clause (`inferLetT`, `inferBody_let`).
* `infer_lam_io` and `infer_forall_io` refine `inferBodyIO`'s `.lam` and `.forallE` clauses
  (`inferLamIOT`, `inferForallIOT`) at the io view of the knot.
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
    rw [StateT.run_bind, AM.run_of_ok _ _ h₁.1, h₁.2.2.1]; rfl)

/-- **Every spec holds at L fuel `0`** (the run fails). -/
theorem CoreSpec.zeroLet {α : Type} [Inhabited α] (p : Prog) (f : FnName) (args : List Word)
    (T : AM α) (dec : List Word → α) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word) (ok : List Word → Prop) :
    CoreSpec p 0 f args T dec s₀ a₀ dn vis fe M eb ok := by
  apply L.M.triple_of_run
  intro s r s' _ hrun
  rw [invoke_run_loc] at hrun
  obtain ⟨e, he⟩ : ∃ e, (invoke p (exec p 0) f args).run ⟨s.mem, Locals.init []⟩ = .error e := by
    simp only [invoke, lookupFn]
    cases p.lookup f with
    | none | some fd => exact ⟨_, rfl⟩
  rw [he] at hrun; cases hrun

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

section letK
variable (p : Prog) (n : Nat) (mode vis d ty v b : Word)

/-- After `defeq`'s run: the verdict, `inst1`, the body's `infer`. -/
def letK5 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => call1W p n "infer" [mode, vis, d, r.headD 0] m

def letK4 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else letK5 p n mode vis d (callW p n "inst1" [b, v, 0] m)

def letK3 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => letK4 p n mode vis d v b (callW p n "defeq" [mode, vis, d, r.headD 0, ty] m)

def letK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (_, m) => letK3 p n mode vis d ty v b (callW p n "infer" [mode, vis, d, v] m)

/-- **The model of `infer_let`** past the type's `infer` run `res`. -/
def letK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => letK2 p n mode vis d ty v b (callW p n "ensure_sort" [mode, vis, d, r.headD 0] m)

variable (r : List Word) (m : Mem)

theorem letK5_some : letK5 p n mode vis d (some (r, m)) = call1W p n "infer" [mode, vis, d, r.headD 0] m := rfl
theorem letK4_ok (h : r.headD 0 ≠ 0) :
    letK4 p n mode vis d v b (some (r, m)) = letK5 p n mode vis d (callW p n "inst1" [b, v, 0] m) := by
  simp only [letK4, h, ↓reduceIte]
theorem letK3_some :
    letK3 p n mode vis d ty v b (some (r, m)) =
      letK4 p n mode vis d v b (callW p n "defeq" [mode, vis, d, r.headD 0, ty] m) := rfl
theorem letK2_some :
    letK2 p n mode vis d ty v b (some (r, m)) = letK3 p n mode vis d ty v b (callW p n "infer" [mode, vis, d, v] m) := rfl
theorem letK1_some :
    letK1 p n mode vis d ty v b (some (r, m)) =
      letK2 p n mode vis d ty v b (callW p n "ensure_sort" [mode, vis, d, r.headD 0] m) := rfl

end letK

section ilet
variable (p : Prog) (hb : InferBodyProg p)

include hb in
theorem inferLet_spec (n : Nat) (s₀ : St) (mode vis d ty v b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_let" [mode, vis, d, ty, v, b]
    ⦃fun r s' => LocEq s' s₀ ∧ letK1 p n mode vis d ty v b
      (callW p n "infer" [mode, vis, d, ty] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hb.inferLet]
  simp only [callFn, inferLetL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "infer",
      callW_spec p n "ensure_sort", callW_spec p n "defeq", callW_spec p n "inst1"] <;>
  simp_all [letK1_some, letK2_some, letK3_some, letK4, letK5_some, call1W, Cmp.eval, LocEq,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr]

end ilet

/-- Peel one call off a model: the run exists, and the model is the continuation's. -/
theorem callW_cases {f : FnName} {p : Prog} {n : Nat} {vs : List Word} {m : Mem}
    {K : Option (List Word × Mem) → Option (Word × Mem)} {x : Word × Mem}
    (hK : K none = none) (h : K (callW p n f vs m) = some x) :
    ∃ r₁ m₁, callW p n f vs m = some (r₁, m₁) ∧ K (some (r₁, m₁)) = some x := by
  cases hc : callW p n f vs m with
  | none => rw [hc, hK] at h; cases h
  | some q => exact ⟨q.1, q.2, rfl, by rw [hc] at h; exact h⟩

/-- **`infer_let` refines the `.letE` clause** (`inferLetT`) at the knot, from the knot's slots,
`ensure_sort` and `inst1`'s spec. -/
@[refines_part ConRon.Arena.inferBody "letE (inferLetT)"]
theorem inferLet_refines (p : Prog) (hp : InferLeafProg p) (hb : InferBodyProg p)
    (hi1 : Inst1OK p) (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty v b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (hty : HW ty) (hv : HW v) (hbb : HW b) :
    CoreSpec p (n + 1) "infer_let" [mode, vis, d, ty, v, b]
      (inferLetT (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) (decE v) (decE b)) decH
      s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferLet_spec p hb n s₀ mode vis d ty v b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hK := hk n (Nat.le_refl _)
  have hes := ensureSortSpec_of_knot p hp n hk
  obtain ⟨r₁, m₁, hc1, hW⟩ := callW_cases rfl hW
  rw [letK1_some] at hW
  obtain ⟨r₂, m₂, hc2, hW⟩ := callW_cases rfl hW
  rw [letK2_some] at hW
  obtain ⟨r₃, m₃, hc3, hW⟩ := callW_cases rfl hW
  rw [letK3_some] at hW
  obtain ⟨r₄, m₄, hc4, hW⟩ := callW_cases rfl hW
  have h0 : ¬ r₄.headD 0 = 0 := fun h0 => by simp only [letK4, h0, ↓reduceIte] at hW; cases hW
  rw [letK4_ok (h := h0)] at hW
  obtain ⟨r₅, m₅, hc5, hW⟩ := callW_cases rfl hW
  rw [letK5_some] at hW
  have h₁ := CoreSpec.of_callW (hK.infer F s a₀ dn vis fe M eb mode d ty hF hn hs hty) hc1
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  have h₂ := CoreSpec.of_callW (hes F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0) hF hn
    ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  have h₃ := CoreSpec.of_callW (hK.infer F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d v hF hn
    ⟨hS₂, hs.mode4, hs.eb_mode⟩ hv) hc3
  refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
  have h₄ := CoreSpec.of_callW (hK.defeq F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode d (r₃.headD 0) ty
    hF hn ⟨hS₃, hs.mode4, hs.eb_mode⟩ h₃.2.2.2 hty) hc4
  refine coreRef_bind h₄ (fun M₄ hS₄ => ?_)
  have hbt : decBool r₄ = true := by simp only [decBool, bne_iff_ne]; exact h0
  rw [hbt]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have h₅ := CoreSpec.of_callW (hi1 n ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb b v 0 hS₄ hbb hv) hc5
  refine coreRef_bind h₅ (fun M₅ hS₅ => ?_)
  exact CoreSpec.of_call1W (s₀ := ⟨m₅, Locals.init []⟩)
    (hK.infer F _ _ dn vis fe M₅ eb mode d (r₅.headD 0) hF hn ⟨hS₅, hs.mode4, hs.eb_mode⟩ h₅.2.2.2)
    (fun r r' h => by simp only [decH, h]) hW

/-! ## `infer_lam_io`: the io body's `.lam` clause -/

/-- A `view` read, then a run at the node it reads. -/
theorem coreRef_view {β : Type} [Inhabited β] {h : EIdx} {v : ENodeView} {k : ENodeView → AM β}
    {a₀ : AState} {dec : List Word → β} {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word} {ok : List Word → Prop}
    (hv : a₀.store.view h = some v) (h' : CoreRef (k v) a₀ dec dn m₀ vis fe M eb r m ok) :
    CoreRef (view h >>= k) a₀ dec dn m₀ vis fe M eb r m ok :=
  coreRef_congr (by rw [StateT.run_bind, view_run _ _ _ hv]; rfl) h'

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

section lamK
variable (p : Prog) (n : Nat) (mode vis d ty body : Word)

def lamIOK3 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => call1W p n "infer_lam_result" [ty, r.headD 0, d] m

def lamIOK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => lamIOK3 p n d ty (callW p n "infer_io" [mode, vis, d + 1, r.headD 0] m)

def lamIOK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => lamIOK2 p n mode vis d ty (callW p n "inst1" [body, r.headD 0, 0] m)

/-- **The model of `infer_lam_io`.** -/
def lamIOK (m : Mem) : Option (Word × Mem) :=
  if d + 1 = 0 then none else lamIOK1 p n mode vis d ty body (callW p n "intern_fvar" [d, ty] m)

variable (r : List Word) (m : Mem)

theorem lamIOK3_some : lamIOK3 p n d ty (some (r, m)) =
    call1W p n "infer_lam_result" [ty, r.headD 0, d] m := rfl
theorem lamIOK2_some : lamIOK2 p n mode vis d ty (some (r, m)) =
    lamIOK3 p n d ty (callW p n "infer_io" [mode, vis, d + 1, r.headD 0] m) := rfl
theorem lamIOK1_some : lamIOK1 p n mode vis d ty body (some (r, m)) =
    lamIOK2 p n mode vis d ty (callW p n "inst1" [body, r.headD 0, 0] m) := rfl
theorem lamIOK_ok (h : ¬ d + 1 = 0) :
    lamIOK p n mode vis d ty body m = lamIOK1 p n mode vis d ty body (callW p n "intern_fvar" [d, ty] m) := by
  simp only [lamIOK, h, ↓reduceIte]

end lamK

section ilam
variable (p : Prog) (hb : InferBodyProg p)

include hb in
theorem inferLamIO_spec (n : Nat) (s₀ : St) (mode vis d ty body : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_lam_io" [mode, vis, d, ty, body]
    ⦃fun r s' => LocEq s' s₀ ∧ lamIOK p n mode vis d ty body s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hb.inferLamIO]
  simp only [callFn, inferLamIOL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "intern_fvar",
      callW_spec p n "inst1", callW_spec p n "infer_io", callW_spec p n "infer_lam_result"] <;>
  simp_all [lamIOK, lamIOK1_some, lamIOK2_some, lamIOK3_some, call1W, Cmp.eval, LocEq, BinOp.eval,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr]

end ilam

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
knot, from the `infer_io` slot, `inst1` and `abstract1`. -/
@[refines_part ConRon.Arena.inferBodyIO "lam (inferLamIOT)"]
theorem inferLamIO_refines (p : Prog) (hp : InferLeafProg p) (hb : InferBodyProg p)
    (hi1 : Inst1OK p) (ha1 : Abstract1OK p) (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    CoreSpec p (n + 1) "infer_lam_io" [mode, vis, d, ty, body]
      (inferLamIOT (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) d.toNat (decE ty) (decE body))
      decH s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferLamIO_spec p hb n s₀ mode vis d ty body)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hK := hk n (Nat.le_refl _)
  have hd : ¬ d + 1 = 0 := fun hd => by simp only [lamIOK, hd, ↓reduceIte] at hW; cases hW
  rw [lamIOK_ok (h := hd)] at hW
  have hd1 := toNat_succ_of_ne hd
  obtain ⟨r₁, m₁, hc1, hW⟩ := callW_cases rfl hW
  rw [lamIOK1_some] at hW
  obtain ⟨r₂, m₂, hc2, hW⟩ := callW_cases rfl hW
  rw [lamIOK2_some] at hW
  obtain ⟨r₃, m₃, hc3, hW⟩ := callW_cases rfl hW
  rw [lamIOK3_some] at hW
  obtain ⟨s₁, hs₁, -, hfv⟩ := triple_of_callW (internFVar_spec p hb.fvf hb.fvp hb.fvi n s d ty) hc1
  rw [hs₁] at hfv
  have h₁ := internFVar_core hs.rel d ty hty r₁ hfv
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  have h₂ := CoreSpec.of_callW (hi1 n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb body (r₁.headD 0) 0 hS₁
    hbody h₁.2.2.2) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  have h₃ := CoreSpec.of_callW (hK.inferIO F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode (d + 1)
    (r₂.headD 0) hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ h₂.2.2.2) hc3
  rw [hd1] at h₃
  refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
  exact CoreSpec.of_call1W (s₀ := ⟨m₃, Locals.init []⟩)
    (inferLamResult_any p hp ha1 n _ _ dn vis fe M₃ eb ty (r₃.headD 0) d hS₃ h₃.2.2.2)
    (fun r r' h => by simp only [decH, h]) hW

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

section faK
variable (p : Prog) (n : Nat) (mode vis d ty body u : Word)

def faK8 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => call1W p n "intern_sort" [r.headD 0] m

def faK7 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => faK8 p n (callW p n "intern_imax" [u, r.headD 0] m)

def faK6 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => faK7 p n u (callW p n "ensure_sort" [mode, vis, d + 1, r.headD 0] m)

def faK5 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => faK6 p n mode vis d u (callW p n "infer_io" [mode, vis, d + 1, r.headD 0] m)

def faK4 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => faK5 p n mode vis d u (callW p n "inst1" [body, r.headD 0, 0] m)

/-- After `whnf`'s run: the sort's level read off its record, then the binder's `fvar`. -/
def faK3 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 >>> 28 ≠ 2 then none
    else if tierW (r.headD 0) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m SORT (tierW (r.headD 0)) ≤ idxW (r.headD 0) then none
    else faK4 p n mode vis d body (tfld m SORT (tierW (r.headD 0)) (idxW (r.headD 0)) 0)
      (callW p n "intern_fvar" [d, ty] m)

def faK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => faK3 p n mode vis d ty body (callW p n "whnf" [mode, vis, d, r.headD 0] m)

/-- **The model of `infer_forall_io`.** -/
def faK (m : Mem) : Option (Word × Mem) :=
  if d + 1 = 0 then none else faK2 p n mode vis d ty body (callW p n "infer_io" [mode, vis, d, ty] m)

variable (r : List Word) (m : Mem)

theorem faK8_some : faK8 p n (some (r, m)) = call1W p n "intern_sort" [r.headD 0] m := rfl
theorem faK7_some : faK7 p n u (some (r, m)) = faK8 p n (callW p n "intern_imax" [u, r.headD 0] m) := rfl
theorem faK6_some : faK6 p n mode vis d u (some (r, m)) =
    faK7 p n u (callW p n "ensure_sort" [mode, vis, d + 1, r.headD 0] m) := rfl
theorem faK5_some : faK5 p n mode vis d u (some (r, m)) =
    faK6 p n mode vis d u (callW p n "infer_io" [mode, vis, d + 1, r.headD 0] m) := rfl
theorem faK4_some : faK4 p n mode vis d body u (some (r, m)) =
    faK5 p n mode vis d u (callW p n "inst1" [body, r.headD 0, 0] m) := rfl
theorem faK2_some : faK2 p n mode vis d ty body (some (r, m)) =
    faK3 p n mode vis d ty body (callW p n "whnf" [mode, vis, d, r.headD 0] m) := rfl

end faK

section ifa
variable (p : Prog) (hb : InferBodyProg p)

include hb in
theorem inferForallIO_spec (n : Nat) (s₀ : St) (mode vis d ty body : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_forall_io" [mode, vis, d, ty, body]
    ⦃fun r s' => LocEq s' s₀ ∧ faK p n mode vis d ty body s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hb.inferForallIO]
  simp only [callFn, inferForallIOL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, callW_spec p n "infer_io",
      callW_spec p n "whnf", callW_spec p n "intern_fvar", callW_spec p n "inst1",
      callW_spec p n "ensure_sort", callW_spec p n "intern_imax", callW_spec p n "intern_sort",
        evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
  simp_all [faK, faK2_some, faK3, faK4_some, faK5_some, faK6_some, faK7_some, faK8_some, call1W,
    Cmp.eval, LocEq, BinOp.eval, tierW, idxW, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr, tfld]

end ifa

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
view of the knot, from the `infer_io` and `whnf` slots, `ensure_sort` and `inst1`. -/
@[refines_part ConRon.Arena.inferBodyIO "forallE (inferForallIOT)"]
theorem inferForallIO_refines (p : Prog) (hp : InferLeafProg p) (hb : InferBodyProg p)
    (hi1 : Inst1OK p) (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    CoreSpec p (n + 1) "infer_forall_io" [mode, vis, d, ty, body]
      (inferForallIOT (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE ty)
        (decE body)) decH s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferForallIO_spec p hb n s₀ mode vis d ty body)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hK := hk n (Nat.le_refl _)
  have hes := ensureSortSpec_of_knot p hp n hk
  have hd : ¬ d + 1 = 0 := fun hd => by simp only [faK, hd, ↓reduceIte] at hW; cases hW
  simp only [faK, hd, ↓reduceIte] at hW
  have hd1 := toNat_succ_of_ne hd
  obtain ⟨r₁, m₁, hc1, hW⟩ := callW_cases rfl hW
  rw [faK2_some] at hW
  obtain ⟨r₂, m₂, hc2, hW⟩ := callW_cases rfl hW
  have h₁ := CoreSpec.of_callW (hK.inferIO F s a₀ dn vis fe M eb mode d ty hF hn hs hty) hc1
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  have h₂ := CoreSpec.of_callW (hK.whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0)
    hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  simp only [faK3] at hW
  obtain ⟨g1, hW⟩ := of_ite_none hW
  obtain ⟨g2, hW⟩ := of_ite_none hW
  obtain ⟨g3, hW⟩ := of_ite_none hW
  have hg : r₂.headD 0 >>> 28 = 2 := by simpa using g1
  obtain ⟨hv, hu⟩ := L.Ind.view_sort_f m₂ _ hS₂.arena.1 (r₂.headD 0) h₂.2.2.2 ⟨g2, by simpa using g3⟩ hg
  have htag : ((decH r₂).tag == ETag.sort) = true := tag_sort_beq _ h₂.2.2.2 hg
  simp only [htag, ↓reduceIte]
  refine coreRef_view hv ?_
  obtain ⟨r₃, m₃, hc3, hW⟩ := callW_cases rfl hW
  rw [faK4_some] at hW
  obtain ⟨r₄, m₄, hc4, hW⟩ := callW_cases rfl hW
  rw [faK5_some] at hW
  obtain ⟨r₅, m₅, hc5, hW⟩ := callW_cases rfl hW
  rw [faK6_some] at hW
  obtain ⟨r₆, m₆, hc6, hW⟩ := callW_cases rfl hW
  rw [faK7_some] at hW
  obtain ⟨r₇, m₇, hc7, hW⟩ := callW_cases rfl hW
  rw [faK8_some] at hW
  obtain ⟨s₃, hs₃, -, hfv⟩ := triple_of_callW
    (internFVar_spec p hb.fvf hb.fvp hb.fvi n ⟨m₂, Locals.init []⟩ d ty) hc3
  rw [hs₃] at hfv
  have h₃ := internFVar_core hS₂ d ty hty r₃ hfv
  refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
  have h₄ := CoreSpec.of_callW (hi1 n ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb body (r₃.headD 0) 0 hS₃
    hbody h₃.2.2.2) hc4
  refine coreRef_bind h₄ (fun M₄ hS₄ => ?_)
  have h₅ := CoreSpec.of_callW (hK.inferIO F ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode (d + 1)
    (r₄.headD 0) hF hn ⟨hS₄, hs.mode4, hs.eb_mode⟩ h₄.2.2.2) hc5
  rw [hd1] at h₅
  refine coreRef_bind h₅ (fun M₅ hS₅ => ?_)
  have h₆ := CoreSpec.of_callW (hes F ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb mode (d + 1) (r₅.headD 0)
    hF hn ⟨hS₅, hs.mode4, hs.eb_mode⟩ h₅.2.2.2) hc6
  rw [hd1] at h₆
  refine coreRef_bind h₆ (fun M₆ hS₆ => ?_)
  obtain ⟨_, _, _, hT₃⟩ := h₃.2.1
  obtain ⟨_, _, _, hT₄⟩ := h₄.2.1
  obtain ⟨_, _, _, hT₅⟩ := h₅.2.1
  obtain ⟨_, _, _, hT₆⟩ := h₆.2.1
  have hdu := lvl_den_later hS₂.arena.1 hS₆.arena.1 hS₆.den
    (hT₃.trans (hT₄.trans (hT₅.trans hT₆))).pool.lvl hu (hS₂.den.sort _ _ hv)
  obtain ⟨x₆, hx₆⟩ := ensureSort_view (AM.run_of_ok _ _ h₆.1)
  rw [h₆.2.2.1] at hx₆
  have hdv := hS₆.den.sort _ _ hx₆
  obtain ⟨s₇, hs₇, -, him⟩ := triple_of_callW
    (internImax_spec p hb.imf hb.imp hb.imi n ⟨m₆, Locals.init []⟩ _ (r₆.headD 0)) hc7
  rw [hs₇] at him
  have h₇ := internImax_core hS₆ _ _ hu h₆.2.2.2 r₇ him hdu hdv
  refine coreRef_bind h₇ (fun M₇ hS₇ => ?_)
  have hso := of_call1W (X := fun m w m' => sointernW m (r₇.headD 0) = some (w, m'))
    (fun s₀ => internSort_spec p hb.sof hb.sop hb.soi n s₀ (r₇.headD 0)) hW
  exact internSort_core hS₇ (r₇.headD 0) h₇.2.2.2 r hso (by
    have hd := internLNode_res_den hS₆
      (fun c hc => by
        simp only [LNodeView.lchildren, List.mem_cons, List.mem_nil_iff, or_false] at hc; rcases hc with rfl | rfl
        · exact hdu
        · exact hdv)
      (fun n hn => by simp [LNodeView.nchildren] at hn) h₇.1
    rw [h₇.2.2.1] at hd; exact hd)

end L.Arena
