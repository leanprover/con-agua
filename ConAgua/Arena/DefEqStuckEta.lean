import ConAgua.Arena.DefEqStuck
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr

/-!
# `eta_cert` refines `etaCert` (lane `defeq`, helper `defeq-top`)

The callW pattern (`DefEqStuck.lean`). `mk_app` under `CoreS` (`mkApp_core`, from lane `whnf`'s
`callW_mkApp`). The twin's body after the `∀` view is `etaInnerT` (`etaCert_eq`, by `rfl`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Leaves at any fuel -/

/-- `io_neutral` at every L fuel. -/
theorem ioNeutral_at (p : Prog) (hp : DefEqLeafProg p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
      (fe : IFEnv) (MM : ModeMaps) (eb e : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW e →
      CoreSpec p n "io_neutral" [e] (ioNeutral (decE e)) decBool s₀ a₀ dn vis fe MM eb
  | 0, s₀, a₀, dn, vis, fe, MM, eb, _, _, _ => CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe MM eb _
  | n + 1, s₀, a₀, dn, vis, fe, MM, eb, e, hS, he => ioNeutral_refines p hp n s₀ a₀ dn vis fe MM eb e hS he

/-- **`mk_app` refines `internE (.app …)` under `CoreS`** (a run). -/
theorem mkApp_core {p : Prog} (hp : SpineProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn m a vis fe M eb) (f x : Word) (rs : List Word)
    (hc : callW p n "mk_app" [f, x] m = some (rs, m')) :
    CoreRef (internE (.app (decE f) (decE x))) a decH dn m vis fe M eb rs m' := by
  obtain ⟨hok, hD, hres, hf, hw⟩ := callW_mkApp p hp n ⟨m, Locals.init []⟩ a hS.arena f x rs m' hc
  have hS' : CoreS dn m' _ vis fe M eb := hS.arena_frame hD
    (Keeps.run (keeps_cpl_internApp _ _) (AM.run_of_ok _ _ hok)) hf
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp [AREC, ASLOT, ADER])
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
  have hst := StackKept.of_frame hf
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, hst⟩, by rw [hres]; rfl, hw⟩

/-- The mode test of `eta_cert_body` is `verifiedChecks`. -/
theorem decMode_vc (mode : Word) (h : mode < 4) :
    (decMode mode).verifiedChecks = decide (mode &&& 1 = 0) := by
  rcases mode_cases mode h with rfl | rfl | rfl | rfl <;> decide

/-! ## The twin, in the L code's pieces -/

/-- `etaCert`'s verified-mode check, copied (`eta_cert_ty`). -/
def etaTyT (r : CoreFnsA) (depth : Nat) (lhs cod₂ fv : EIdx) : AM Bool := do
  let t₁ ← r.infer (depth + 1) lhs
  let t₂ ← instantiate1Fast coreWalkFuel cod₂ fv 0
  r.defeq (depth + 1) t₁ t₂

/-- `etaCert` once the domains agree, copied (`eta_cert_body`). -/
def etaBodyT (mode : ConLeche.CheckMode) (r : CoreFnsA) (depth : Nat) (ty₁ body₁ b cod₂ : EIdx) :
    AM Bool := do
  let fv ← internE (.fvar depth ty₁)
  let lhs ← instantiate1Fast coreWalkFuel body₁ fv 0
  let rhs ← internE (.app b fv)
  if !(← r.defeq (depth + 1) lhs rhs) then pure false
  else if mode.verifiedChecks then etaTyT r depth lhs cod₂ fv
  else pure true

theorem etaCert_eq (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (ty₁ body₁ b : EIdx) :
    etaCert mode r fe depth ty₁ body₁ b = (do
      let x ← ioNeutral b
      if !x then pure false else do
      let tb ← r.inferIO depth b
      let hh ← r.whnf depth tb
      if hh.tag == ETag.forallE then
        view hh >>= fun v => match v with
          | .forallE ty₂ cod₂ => do
            if ← r.defeq depth ty₂ ty₁ then etaBodyT mode r depth ty₁ body₁ b cod₂
            else pure false
          | _ => pure false
      else pure false) := rfl

/-! ## The models -/

section ecK
variable (p : Prog) (n : Nat) (mode vis d ty1 body1 b cod2 : Word)

/-- `eta_cert_ty` past `infer`'s run. -/
def ectK2 (t1 : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => call1W p n "defeq" [mode, vis, d + 1, t1, r.headD 0] m

def ectK1 (fv : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => ectK2 p n mode vis d (r.headD 0) (callW p n "inst1" [cod2, fv, 0] m)

/-- `eta_cert_body` past the bodies' comparison. -/
def ecbK4 (fv lhs : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, m)
    else if mode &&& 1 = 0 then call1W p n "eta_cert_ty" [mode, vis, d, lhs, cod2, fv] m
    else some (1, m)

def ecbK3 (fv lhs : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => ecbK4 p n mode vis d cod2 fv lhs (callW p n "defeq" [mode, vis, d + 1, lhs, r.headD 0] m)

def ecbK2 (fv : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => ecbK3 p n mode vis d cod2 fv (r.headD 0) (callW p n "mk_app" [b, fv] m)

def ecbK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => ecbK2 p n mode vis d b cod2 (r.headD 0) (callW p n "inst1" [body1, r.headD 0, 0] m)

/-- **The model of `eta_cert_body`.** -/
def ecbK (m : Mem) : Option (Word × Mem) :=
  if d + 1 = 0 then none else ecbK1 p n mode vis d body1 b cod2 (callW p n "intern_fvar" [d, ty1] m)

/-- `eta_cert` past the domains' comparison. -/
def ecK4 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, m)
    else call1W p n "eta_cert_body" [mode, vis, d, ty1, body1, b, cod2] m

/-- `eta_cert` past `whnf`: the `∀` view. -/
def ecK3 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 >>> 28 ≠ 6 then some (0, m)
    else if tierW (r.headD 0) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m FORALL (tierW (r.headD 0)) ≤ idxW (r.headD 0) then none
    else ecK4 p n mode vis d ty1 body1 b
      (tfld m FORALL (tierW (r.headD 0)) (idxW (r.headD 0)) 1)
      (callW p n "defeq" [mode, vis, d,
        tfld m FORALL (tierW (r.headD 0)) (idxW (r.headD 0)) 0, ty1] m)

def ecK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => ecK3 p n mode vis d ty1 body1 b (callW p n "whnf" [mode, vis, d, r.headD 0] m)

/-- **The model of `eta_cert`** past `io_neutral`'s run. -/
def ecK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, m)
    else ecK2 p n mode vis d ty1 body1 b (callW p n "infer_io" [mode, vis, d, b] m)

variable (r : List Word) (m : Mem) (t1 fv lhs : Word)

theorem ectK2_some : ectK2 p n mode vis d t1 (some (r, m)) =
    call1W p n "defeq" [mode, vis, d + 1, t1, r.headD 0] m := rfl
theorem ectK1_some : ectK1 p n mode vis d cod2 fv (some (r, m)) =
    ectK2 p n mode vis d (r.headD 0) (callW p n "inst1" [cod2, fv, 0] m) := rfl
theorem ecbK4_no (h : r.headD 0 = 0) : ecbK4 p n mode vis d cod2 fv lhs (some (r, m)) = some (0, m) := by
  simp only [ecbK4, h, ↓reduceIte]
theorem ecbK4_vc (h : r.headD 0 ≠ 0) (hm : mode &&& 1 = 0) : ecbK4 p n mode vis d cod2 fv lhs (some (r, m)) =
    call1W p n "eta_cert_ty" [mode, vis, d, lhs, cod2, fv] m := by
  simp only [ecbK4, h, hm, ↓reduceIte]
theorem ecbK4_tr (h : r.headD 0 ≠ 0) (hm : ¬ mode &&& 1 = 0) :
    ecbK4 p n mode vis d cod2 fv lhs (some (r, m)) = some (1, m) := by
  simp only [ecbK4, h, hm, ↓reduceIte]
theorem ecbK3_some : ecbK3 p n mode vis d cod2 fv lhs (some (r, m)) =
    ecbK4 p n mode vis d cod2 fv lhs (callW p n "defeq" [mode, vis, d + 1, lhs, r.headD 0] m) := rfl
theorem ecbK2_some : ecbK2 p n mode vis d b cod2 fv (some (r, m)) =
    ecbK3 p n mode vis d cod2 fv (r.headD 0) (callW p n "mk_app" [b, fv] m) := rfl
theorem ecbK1_some : ecbK1 p n mode vis d body1 b cod2 (some (r, m)) =
    ecbK2 p n mode vis d b cod2 (r.headD 0) (callW p n "inst1" [body1, r.headD 0, 0] m) := rfl
theorem ecbK_ok (h : ¬ d + 1 = 0) : ecbK p n mode vis d ty1 body1 b cod2 m =
    ecbK1 p n mode vis d body1 b cod2 (callW p n "intern_fvar" [d, ty1] m) := by
  simp only [ecbK, h, ↓reduceIte]
theorem ecK4_no (h : r.headD 0 = 0) : ecK4 p n mode vis d ty1 body1 b cod2 (some (r, m)) = some (0, m) := by
  simp only [ecK4, h, ↓reduceIte]
theorem ecK4_yes (h : r.headD 0 ≠ 0) : ecK4 p n mode vis d ty1 body1 b cod2 (some (r, m)) =
    call1W p n "eta_cert_body" [mode, vis, d, ty1, body1, b, cod2] m := by
  simp only [ecK4, h, ↓reduceIte]
theorem ecK3_no (h : r.headD 0 >>> 28 ≠ 6) : ecK3 p n mode vis d ty1 body1 b (some (r, m)) = some (0, m) := by
  simp only [ecK3, h, ne_eq, not_false_eq_true, ↓reduceIte]
theorem ecK3_ok (h1 : r.headD 0 >>> 28 = 6) (h2 : ¬ (tierW (r.headD 0) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (h3 : idxW (r.headD 0) < tcnt m FORALL (tierW (r.headD 0))) :
    ecK3 p n mode vis d ty1 body1 b (some (r, m)) = ecK4 p n mode vis d ty1 body1 b
      (tfld m FORALL (tierW (r.headD 0)) (idxW (r.headD 0)) 1)
      (callW p n "defeq" [mode, vis, d,
        tfld m FORALL (tierW (r.headD 0)) (idxW (r.headD 0)) 0, ty1] m) := by
  have h3' : ¬ tcnt m FORALL (tierW (r.headD 0)) ≤ idxW (r.headD 0) := by simpa using h3
  simp only [ecK3, h1, h2, h3', ne_eq, not_true_eq_false, ↓reduceIte]
theorem ecK2_some : ecK2 p n mode vis d ty1 body1 b (some (r, m)) =
    ecK3 p n mode vis d ty1 body1 b (callW p n "whnf" [mode, vis, d, r.headD 0] m) := rfl
theorem ecK1_no (h : r.headD 0 = 0) : ecK1 p n mode vis d ty1 body1 b (some (r, m)) = some (0, m) := by
  simp only [ecK1, h, ↓reduceIte]
theorem ecK1_yes (h : r.headD 0 ≠ 0) : ecK1 p n mode vis d ty1 body1 b (some (r, m)) =
    ecK2 p n mode vis d ty1 body1 b (callW p n "infer_io" [mode, vis, d, b] m) := by
  simp only [ecK1, h, ↓reduceIte]

end ecK

/-! ## The L specs -/

section ecspec
variable (p : Prog) (hq : StuckProg p)

include hq in
theorem etaCertTy_spec (n : Nat) (s₀ : St) (mode vis d lhs cod2 fv : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "eta_cert_ty" [mode, vis, d, lhs, cod2, fv]
    ⦃fun r s' => LocEq s' s₀ ∧ ectK1 p n mode vis d cod2 fv
      (callW p n "infer" [mode, vis, d + 1, lhs] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.etaCertTy]
  simp only [callFn, etaCertTyL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "infer",
      callW_spec p n "inst1", callW_spec p n "defeq"] <;>
    finish (gen := 20) [ectK1_some, ectK2_some, call1W_some]

include hq in
theorem etaCertBody_spec (n : Nat) (s₀ : St) (mode vis d ty1 body1 b cod2 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "eta_cert_body" [mode, vis, d, ty1, body1, b, cod2]
    ⦃fun r s' => LocEq s' s₀ ∧ ecbK p n mode vis d ty1 body1 b cod2 s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.etaCertBody]
  simp only [callFn, etaCertBodyL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "intern_fvar",
      callW_spec p n "inst1", callW_spec p n "mk_app", callW_spec p n "defeq",
      callW_spec p n "eta_cert_ty"] <;>
  simp_all [ecbK, ecbK1, ecbK2, ecbK3, ecbK4, call1W, Cmp.eval, BinOp.eval, LocEq,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr]

include hq in
theorem etaCert_spec (n : Nat) (s₀ : St) (mode vis d ty1 body1 b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "eta_cert" [mode, vis, d, ty1, body1, b]
    ⦃fun r s' => LocEq s' s₀ ∧ ecK1 p n mode vis d ty1 body1 b
      (callW p n "io_neutral" [b] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.etaCert]
  simp only [callFn, etaCertL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, evalE_tld, tld,
    evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "io_neutral", callW_spec p n "infer_io", callW_spec p n "whnf",
      callW_spec p n "defeq", callW_spec p n "eta_cert_body"] <;>
  simp_all [ecK1, ecK2, ecK3, ecK4, call1W, tierW, idxW, LocEq, BinOp.eval,
    St.setLocs_cons, CTL,
    Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

end ecspec

/-! ## The refinements -/

/-- **`eta_cert_ty` refines `etaTyT`** at the knot. -/
@[refines_part ConRon.Arena.etaCert "the verified-mode check (etaTyT)"]
theorem etaCertTy_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d lhs cod2 fv : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hd : ¬ d + 1 = 0) (hl : HW lhs)
    (hcod : HW cod2) (hfv : HW fv) :
    CoreSpec p (n + 1) "eta_cert_ty" [mode, vis, d, lhs, cod2, fv]
      (etaTyT (coreKnot (decMode mode) fe id F) d.toNat (decE lhs) (decE cod2) (decE fv)) decBool
      s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (etaCertTy_spec p hq n s₀ mode vis d lhs cod2 fv)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hK := hk n (Nat.le_refl _)
  have hd1 := toNat_succ_of_ne hd
  obtain ⟨r₁, m₁, hc1, hW⟩ := callW_cases rfl hW
  rw [ectK1_some] at hW
  obtain ⟨r₂, m₂, hc2, hW⟩ := callW_cases rfl hW
  rw [ectK2_some] at hW
  have h₁ := CoreSpec.of_callW (hK.infer F s a₀ dn vis fe M eb mode (d + 1) lhs hF hn hs hl) hc1
  rw [hd1] at h₁
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  have h₂ := CoreSpec.of_callW (hc.inst1 n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb cod2 fv 0 hS₁
    hcod hfv) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  have h₃ := CoreSpec.of_call1W (s₀ := ⟨m₂, Locals.init []⟩)
    (hK.defeq F _ _ dn vis fe M₂ eb mode (d + 1) (r₁.headD 0) (r₂.headD 0) hF hn
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ h₁.2.2.2 h₂.2.2.2)
    (fun r r' h => by simp only [decBool, h]) hW
  rw [hd1] at h₃
  exact h₃

/-- `eta_cert_ty` at every L fuel up to `n + 1`. -/
theorem etaCertTy_at (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d lhs cod2 fv : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
      ¬ d + 1 = 0 → HW lhs → HW cod2 → HW fv →
      CoreSpec p n "eta_cert_ty" [mode, vis, d, lhs, cod2, fv]
        (etaTyT (coreKnot (decMode mode) fe id F) d.toNat (decE lhs) (decE cod2) (decE fv)) decBool
        s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, lhs, cod2, fv, hF, hn, hs, hd, hl, hcod, hfv =>
      etaCertTy_refines p hq hc n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d lhs cod2 fv
        (by omega) (by omega) hs hd hl hcod hfv

theorem decBool_true_of {r : List Word} (h : r.headD 0 ≠ 0) : decBool r = true := by
  simp only [decBool, bne_iff_ne]; exact h

theorem decBool_false_of {r : List Word} (h : r.headD 0 = 0) : decBool r = false := by
  simp only [decBool, bne_eq_false_iff_eq]; exact h

/-- **`eta_cert_body` refines `etaBodyT`** at the knot. -/
@[refines_part ConRon.Arena.etaCert "the bodies at a fresh variable (etaBodyT)"]
theorem etaCertBody_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d ty1 body1 b cod2 : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty1) (hbody : HW body1)
    (_hb : HW b) (hcod : HW cod2) :
    CoreSpec p (n + 1) "eta_cert_body" [mode, vis, d, ty1, body1, b, cod2]
      (etaBodyT (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE ty1) (decE body1)
        (decE b) (decE cod2)) decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (etaCertBody_spec p hq n s₀ mode vis d ty1 body1 b cod2)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hK := hk n (Nat.le_refl _)
  have hd : ¬ d + 1 = 0 := fun hd => by simp only [ecbK, hd, ↓reduceIte] at hW; cases hW
  rw [ecbK_ok (h := hd)] at hW
  have hd1 := toNat_succ_of_ne hd
  obtain ⟨r₁, m₁, hc1, hW⟩ := callW_cases rfl hW
  rw [ecbK1_some] at hW
  obtain ⟨r₂, m₂, hc2, hW⟩ := callW_cases rfl hW
  rw [ecbK2_some] at hW
  obtain ⟨r₃, m₃, hc3, hW⟩ := callW_cases rfl hW
  rw [ecbK3_some] at hW
  obtain ⟨r₄, m₄, hc4, hW⟩ := callW_cases rfl hW
  obtain ⟨s₁, hs₁, -, hfv⟩ := triple_of_callW
    (internFVar_spec p hq.body.fvf hq.body.fvp hq.body.fvi n s d ty1) hc1
  rw [hs₁] at hfv
  have h₁ := internFVar_core hs.rel d ty1 hty r₁ hfv
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  have h₂ := CoreSpec.of_callW (hc.inst1 n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb body1 (r₁.headD 0) 0
    hS₁ hbody h₁.2.2.2) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  have h₃ := mkApp_core hq.leaf.core.spine hS₂ b (r₁.headD 0) r₃ hc3
  refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
  have h₄ := CoreSpec.of_callW (hK.defeq F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode (d + 1)
    (r₂.headD 0) (r₃.headD 0) hF hn ⟨hS₃, hs.mode4, hs.eb_mode⟩ h₂.2.2.2 h₃.2.2.2) hc4
  rw [hd1] at h₄
  refine coreRef_bind h₄ (fun M₄ hS₄ => ?_)
  by_cases h0 : r₄.headD 0 = 0
  · rw [ecbK4_no (h := h0)] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [decBool_false_of h0]
    exact coreRef_pure hS₄ rfl (decBool_false_of hr.symm).symm (by unfold ResH; rw [← hr]; exact hw0)
  rw [decBool_true_of h0, decMode_vc mode hs.mode4]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hm : mode &&& 1 = 0
  · rw [ecbK4_vc (h := h0) (hm := hm)] at hW
    simp only [hm, decide_true, ↓reduceIte]
    exact CoreSpec.of_call1W (s₀ := ⟨m₄, Locals.init []⟩)
      (etaCertTy_at p hq hc n hk F _ _ dn vis fe M₄ eb mode d (r₂.headD 0) cod2 (r₁.headD 0) hF hn
        ⟨hS₄, hs.mode4, hs.eb_mode⟩ hd h₂.2.2.2 hcod h₁.2.2.2)
      (fun r r' h => by simp only [decBool, h]) hW
  · rw [ecbK4_tr (h := h0) (hm := hm)] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact coreRef_pure hS₄ rfl (decBool_true_of (by rw [← hr]; decide)).symm
      (by unfold ResH; rw [← hr]; exact hw1)

/-- `eta_cert_body` at every L fuel up to `n + 1`. -/
theorem etaCertBody_at (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
      (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
      (eb mode d ty1 body1 b cod2 : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
      HW ty1 → HW body1 → HW b → HW cod2 →
      CoreSpec p n "eta_cert_body" [mode, vis, d, ty1, body1, b, cod2]
        (etaBodyT (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE ty1) (decE body1)
          (decE b) (decE cod2)) decBool s₀ a₀ dn vis fe M eb
  | 0, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, s₀, a₀, dn, vis, fe, M, eb, mode, d, ty1, body1, b, cod2, hF, hn, hs, h1, h2, h3, h4 =>
      etaCertBody_refines p hq hc n (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d ty1 body1 b
        cod2 (by omega) (by omega) hs h1 h2 h3 h4

/-- **`eta_cert` refines `etaCert`** at the knot, from the knot's slots, `io_neutral`, `inst1`
and `mk_app`. -/
@[refines ConRon.Arena.etaCert]
theorem etaCert_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d ty1 body1 b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty1) (hbody : HW body1)
    (hb : HW b) :
    CoreSpec p (n + 1) "eta_cert" [mode, vis, d, ty1, body1, b]
      (etaCert (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty1) (decE body1)
        (decE b)) decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (etaCert_spec p hq n s₀ mode vis d ty1 body1 b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hK := hk n (Nat.le_refl _)
  rw [etaCert_eq]
  obtain ⟨r₁, m₁, hc1, hW⟩ := callW_cases rfl hW
  have h₁ := CoreSpec.of_callW (ioNeutral_at p hq.leaf n s a₀ dn vis fe M eb b hs.rel hb) hc1
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  by_cases h0 : r₁.headD 0 = 0
  · rw [ecK1_no (h := h0)] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [decBool_false_of h0]
    exact coreRef_pure hS₁ rfl (decBool_false_of hr.symm).symm (by unfold ResH; rw [← hr]; exact hw0)
  rw [ecK1_yes (h := h0)] at hW
  rw [decBool_true_of h0]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨r₂, m₂, hc2, hW⟩ := callW_cases rfl hW
  rw [ecK2_some] at hW
  obtain ⟨r₃, m₃, hc3, hW⟩ := callW_cases rfl hW
  have h₂ := CoreSpec.of_callW (hK.inferIO F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d b hF hn
    ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  have h₃ := CoreSpec.of_callW (hK.whnf F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d (r₂.headD 0)
    hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ h₂.2.2.2) hc3
  refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
  have hh3 : HW (r₃.headD 0) := h₃.2.2.2
  simp only [decH]
  simp only [tag_beq_w _ hh3 6 (by decide) ETag.forallE rfl 6 rfl]
  by_cases h6 : r₃.headD 0 >>> 28 ≠ 6
  · rw [ecK3_no (h := h6)] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    simp only [h6, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact coreRef_pure hS₃ rfl (decBool_false_of hr.symm).symm (by unfold ResH; rw [← hr]; exact hw0)
  have h6' : r₃.headD 0 >>> 28 = 6 := by simpa using h6
  by_cases ht : tierW (r₃.headD 0) ≠ 0 ∧ rdW (m₃.arr64 CTL) 1 = 0
  · simp only [ecK3, h6', ht, ne_eq, not_true_eq_false, ↓reduceIte] at hW; cases hW
  by_cases hi : tcnt m₃ FORALL (tierW (r₃.headD 0)) ≤ idxW (r₃.headD 0)
  · simp only [ecK3, h6', ht, hi, ne_eq, not_true_eq_false, ↓reduceIte] at hW; cases hW
  have hi' : idxW (r₃.headD 0) < tcnt m₃ FORALL (tierW (r₃.headD 0)) := by simpa using hi
  rw [ecK3_ok (h1 := h6') (h2 := ht) (h3 := hi')] at hW
  simp only [h6', decide_true, ↓reduceIte]
  obtain ⟨hv, hty2, hcod2⟩ := view_forall m₃ _ hS₃.arena.1 (r₃.headD 0) hh3 ⟨ht, hi'⟩ h6'
  refine coreRef_view hv ?_
  simp only
  obtain ⟨r₄, m₄, hc4, hW⟩ := callW_cases rfl hW
  have h₄ := CoreSpec.of_callW (hK.defeq F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode d _ ty1 hF hn
    ⟨hS₃, hs.mode4, hs.eb_mode⟩ hty2 hty) hc4
  refine coreRef_bind h₄ (fun M₄ hS₄ => ?_)
  by_cases h40 : r₄.headD 0 = 0
  · rw [ecK4_no (h := h40)] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [decBool_false_of h40]
    exact coreRef_pure hS₄ rfl (decBool_false_of hr.symm).symm (by unfold ResH; rw [← hr]; exact hw0)
  rw [ecK4_yes (h := h40)] at hW
  rw [decBool_true_of h40]
  simp only [↓reduceIte]
  exact CoreSpec.of_call1W (s₀ := ⟨m₄, Locals.init []⟩)
    (etaCertBody_at p hq hc n hk F _ _ dn vis fe M₄ eb mode d ty1 body1 b _ hF hn
      ⟨hS₄, hs.mode4, hs.eb_mode⟩ hty hbody hb hcod2)
    (fun r r' h => by simp only [decBool, h]) hW

end L.Arena
