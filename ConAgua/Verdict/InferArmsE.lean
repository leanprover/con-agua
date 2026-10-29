import ConAgua.Verdict.InferLeavesE
import ConAgua.Arena.IndTwin
/-!
# Error claims of the inference arms

The error halves of the unified refinements of `ensure_sort` (`es_ref`), the stage entries
`infer_type_core` and `ensure_sort_core` (`itc_ref`, `esc_ref`, in `CoreStubsE`'s shape) and the
straight-line arms of the inference bodies `infer_lit`, `infer_let`, `infer_lam_io`,
`infer_forall_io` (`il_ref`, `ilet_ref`, `ilam_ref`, `ifa_ref`), as the
error claims (`CoreSpecE`) their non-migrated readers take.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The kit for core runs -/

/-- **A core run that succeeded, then the claim of the rest** (`coreRef_bind`'s error half). -/
theorem ErrClaim.bind_ref {α β : Type} [Inhabited α] {T₁ : AM α} {T₂ : α → AM β} {a₀ : AState}
    {dec₁ : List Word → α} {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {r₁ : List Word} {ok₁ : List Word → Prop} {e : Err}
    (h₁ : CoreRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ErrClaim (T₂ (dec₁ r₁)) (AM.st T₁ a₀) e) : ErrClaim (T₁ >>= T₂) a₀ e :=
  ErrClaim.bind_right (by rw [AM.run_of_ok _ _ h₁.1, h₁.2.2.1]) h₂

/-! ## The stage entries `infer_type_core`, `ensure_sort_core` (`CoreStubsE`'s shape) -/

local notation "V" => ConLeche.CheckMode.verified

/-- **`infer_type_core`'s verdicts under `StageT`** (`CoreStubsE.inferTypeCore`): the `infer`
slot's at the verified mode (`itc_ref`'s error half). -/
theorem inferTypeCore_refinesE (p : Prog) (hp : KnotEntryProg p) (hK : ∀ n, KnotOK p n)
    (hKE : ∀ n, KnotOKE p n) :
    ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState}, L.Ind.StageT dn vis fe m a → ∀ (dep t : Word), L.Ind.H t →
    ∀ e, callE p n "infer_type_core" [vis, dep, t] m = .error e →
      ErrClaim (inferTypeCore V fe checkFuel dep.toNat (decI t)) a e := by
  intro n hn dn vis fe m a hS dep t ht er hc
  obtain _ | k := n
  · obtain ⟨e', he', h0⟩ := callE_zero p _ _ m
    rw [hc] at he'; cases he'; exact ErrClaim.of_cls0 h0
  obtain ⟨M, hC⟩ := hS.core
  exact RefE.run_err (itcE_spec p hp.inferTypeCore (k + 1) ⟨m, Locals.init []⟩ vis dep t) trivial
    (hKE k).infer (itc_ref p k (hK k).infer checkFuel ⟨m, Locals.init []⟩ a dn vis fe M dep t
      (L.Ind.stage_fuel hn) (by omega) hC (L.Ind.hw_of_h ht)) hc

/-- **`ensure_sort_core`'s verdicts under `StageT`** (`CoreStubsE.ensureSortCore`):
`ensure_sort`'s at the verified mode (`esc_ref`'s error half). -/
theorem ensureSortCore_refinesE (p : Prog) (hp : KnotEntryProg p) (hl : InferLeafProg p)
    (hK : ∀ n, KnotOK p n) (hKE : ∀ n, KnotOKE p n) :
    ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState}, L.Ind.StageT dn vis fe m a → ∀ (dep t : Word), L.Ind.H t →
    ∀ e, callE p n "ensure_sort_core" [vis, dep, t] m = .error e →
      ErrClaim (ensureSortCore V fe checkFuel dep.toNat (decI t)) a e := by
  intro n hn dn vis fe m a hS dep t ht er hc
  obtain _ | k := n
  · obtain ⟨e', he', h0⟩ := callE_zero p _ _ m
    rw [hc] at he'; cases he'; exact ErrClaim.of_cls0 h0
  obtain ⟨M, hC⟩ := hS.core
  exact RefE.run_err (escE_spec p hp.ensureSortCore (k + 1) ⟨m, Locals.init []⟩ vis dep t) trivial
    (ensureSortSpecE_of_knot p hl k (fun j _ => hK j) (fun j _ => hKE j))
    (esc_ref p k (ensureSortSpec_of_knot p hl k (fun j _ => hK j)) checkFuel ⟨m, Locals.init []⟩ a dn
      vis fe M dep t (L.Ind.stage_fuel hn) (by omega) hC (L.Ind.hw_of_h ht)) hc

/-! ## The callees' error claims -/

/-- The callees of the inference functions outside the verdict closure. -/
theorem inferArmsE_nv : ∀ f ∈ ["nat_lit_supported", "str_lit_supported", "pin_at", "const_e",
    "intern_fvar", "inst1", "inst_list", "infer_lam_result", "intern_imax", "intern_sort",
    "intern_succ", "e_view", "head_and_args", "ar_entry", "mk_forall", "in_find", "in_put",
    "io_find", "io_put"], f ∈ L.Checker.nvFns :=
  _root_.L.Checker.nv_sub (by decide +kernel)

/-- **The callees' error claims the inference bodies take** (the error half of `InferCallees`):
every callee outside the verdict closure claims nothing (`nv`), `infer_proj`'s
(`inferProj_refinesE'`, `InferLeavesE.lean`). -/
structure InferCalleesE (p : Prog) : Prop where
  nv : closedNV p L.Checker.nvFns = true
  proj : InferProjOKE p

/-! ## The arms -/

/-- **`infer_lit`'s verdicts** (`il_ref`'s error half). -/
theorem inferLit_refinesE (p : Prog) (hp : InferLeafProg p) (hc : InferLitCallees p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb e : Word) (l : ConLeche.Literal) (hS : CoreS dn s₀.mem a₀ vis fe M eb)
    (he : HW e) (hg : e >>> 28 = 8) (hv : a₀.store.view (decE e) = some (.lit l)) :
    CoreSpecE p (n + 1) "infer_lit" [vis, e] (inferLitT fe l) s₀ a₀ :=
  RefE.coreSpecE (ilE_spec p hp.inferLit (n + 1) s₀ vis e) hnv hnv
    (il_ref p hp hc n s₀ a₀ dn vis fe M eb e l hS he hg hv)

/-- **`infer_lam_io`'s verdicts** (`ilam_ref`'s error half). -/
theorem inferLamIO_refinesE (p : Prog) (hp : InferLeafProg p) (hb : InferBodyProg p)
    (hnv : closedNV p L.Checker.nvFns = true) (hi1 : Inst1OK p) (ha1 : Abstract1OK p) (n : Nat)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    CoreSpecE p (n + 1) "infer_lam_io" [mode, vis, d, ty, body]
      (inferLamIOT (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) d.toNat (decE ty) (decE body))
      s₀ a₀ :=
  RefE.coreSpecE (ilamE_spec p hb.inferLamIO (n + 1) s₀ mode vis d ty body) hnv ⟨hkE, hnv⟩
    (ilam_ref p hp hb hi1 ha1 n hk F s₀ a₀ dn vis fe M eb mode d ty body hF hn hs hty hbody)

/-- **`infer_let`'s verdicts** (`ilet_ref`'s error half). -/
theorem inferLet_refinesE (p : Prog) (hp : InferLeafProg p) (hb : InferBodyProg p)
    (hnv : closedNV p L.Checker.nvFns = true) (hi1 : Inst1OK p) (n : Nat) (hk : KnotUpTo p n)
    (hkE : KnotUpToE p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty v b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (hty : HW ty) (hv : HW v) (hbb : HW b) :
    CoreSpecE p (n + 1) "infer_let" [mode, vis, d, ty, v, b]
      (inferLetT (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) (decE v) (decE b)) s₀ a₀ :=
  RefE.coreSpecE (iletE_spec p hb.inferLet (n + 1) s₀ mode vis d ty v b) hnv ⟨hkE, hnv⟩
    (ilet_ref p hp hi1 n hk F s₀ a₀ dn vis fe M eb mode d ty v b hF hn hs hty hv hbb)

/-- **`infer_forall_io`'s verdicts** (`ifa_ref`'s error half). -/
theorem inferForallIO_refinesE (p : Prog) (hp : InferLeafProg p) (hb : InferBodyProg p)
    (hnv : closedNV p L.Checker.nvFns = true) (hi1 : Inst1OK p) (n : Nat) (hk : KnotUpTo p n)
    (hkE : KnotUpToE p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    CoreSpecE p (n + 1) "infer_forall_io" [mode, vis, d, ty, body]
      (inferForallIOT (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE ty)
        (decE body)) s₀ a₀ :=
  RefE.coreSpecE (ifaE_spec p hb.inferForallIO (n + 1) s₀ mode vis d ty body) hnv ⟨hkE, hnv⟩
    (ifa_ref p hp hb hi1 n hk F s₀ a₀ dn vis fe M eb mode d ty body hF hn hs hty hbody)

end L.Arena
