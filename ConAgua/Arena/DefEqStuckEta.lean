import ConAgua.Arena.DefEqStuck
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.LdRd

/-!
# `eta_cert` refines `etaCert` (lane `defeq`, helper `defeq-top`)

One refinement per piece for both outcomes (`RefE` over its unified model,
`Verdict/WhnfModels7E.lean`; the errors are the knot's slots'). `mk_app` under `CoreS`
(`mkApp_core`, from lane `whnf`'s `callW_mkApp`). The twin's body after the `∀` view is
`etaBodyT` (`etaCert_eq`, by `rfl`).
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
    (by decide)
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

/-! ## The refinements -/

/-- **`eta_cert_ty` refines `etaTyT`, both outcomes**: the errors are the `infer` and `defeq`
slots'. -/
@[refines_part ConRon.Arena.etaCert "the verified-mode check (etaTyT)"]
theorem ect_ref (p : Prog) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d lhs cod2 fv : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hd : ¬ d + 1 = 0) (hl : HW lhs)
    (hcod : HW cod2) (hfv : HW fv) :
    RefE (KnotUpToE p n) (ectE p (n + 1) s₀.mem mode vis d lhs cod2 fv)
      (etaTyT (coreKnot (decMode mode) fe id F) d.toNat (decE lhs) (decE cod2) (decE fv)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  have hd1 := toNat_succ_of_ne hd
  simp only [ectE]
  unfold etaTyT
  rcases c1 : callE p n "infer" [mode, vis, d + 1, lhs] s₀.mem with e1 | ⟨r₁, m₁⟩
  · intro hkE
    have h := CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).infer F s₀ a₀ dn vis fe M eb mode (d + 1)
      lhs hF hn hs hl) c1
    rw [hd1] at h
    exact ErrClaim.bind_left h
  have h₁ := CoreSpec.of_callW (hK.infer F s₀ a₀ dn vis fe M eb mode (d + 1) lhs hF hn hs hl)
    (callW_of_callE c1)
  rw [hd1] at h₁
  refine RefE.bind_core (w := id) h₁ (fun M₁ hS₁ _ => ?_)
  simp only [ectE.k_infer]
  rcases c2 : callW p n "inst1" [cod2, fv, 0] m₁ with _ | ⟨r₂, m₂⟩
  · rw [liftE_none, ectE.k_inst1.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have h₂ := CoreSpec.of_callW (hc.inst1 n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb cod2 fv 0 hS₁
    hcod hfv) c2
  refine RefE.bind_core (w := id) h₂ (fun M₂ hS₂ _ => ?_)
  simp only [ectE.k_inst1]
  have hD := hK.defeq F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode (d + 1) (r₁.headD 0) (r₂.headD 0)
    hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ h₁.2.2.2 h₂.2.2.2
  rw [hd1] at hD
  rcases c3 : callE p n "defeq" [mode, vis, d + 1, r₁.headD 0, r₂.headD 0] m₂ with e3 | ⟨r₃, m₃⟩
  · intro hkE
    have h := CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).defeq F ⟨m₂, Locals.init []⟩ _ dn vis fe
      M₂ eb mode (d + 1) _ _ hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ h₁.2.2.2 h₂.2.2.2) c3
    rw [hd1] at h
    exact h
  obtain ⟨hrun, hP⟩ := (CoreSpec.of_callW hD (callW_of_callE c3)).post
  exact RefE.ret hrun ⟨hP.after, hP.res, hP.valid⟩

theorem decBool_true_of {r : List Word} (h : r.headD 0 ≠ 0) : decBool r = true := by
  simp only [decBool, bne_iff_ne]; exact h

theorem decBool_false_of {r : List Word} (h : r.headD 0 = 0) : decBool r = false := by
  simp only [decBool, bne_eq_false_iff_eq]; exact h

/-- **`eta_cert_body` refines `etaBodyT`, both outcomes**: the errors are the `defeq` slot's and
`eta_cert_ty`'s. -/
@[refines_part ConRon.Arena.etaCert "the bodies at a fresh variable (etaBodyT)"]
theorem ecb_ref (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d ty1 body1 b cod2 : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty1) (hbody : HW body1)
    (hcod : HW cod2) :
    RefE (KnotUpToE p n) (ecbE p (n + 1) s₀.mem mode vis d ty1 body1 b cod2)
      (etaBodyT (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE ty1) (decE body1)
        (decE b) (decE cod2)) a₀ (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  simp only [ecbE]
  unfold etaBodyT
  by_cases hd : d + 1 = 0
  · rw [ite_eq_left hd]; exact RefE.of_cls0 (by decide)
  rw [ite_eq_right hd]
  have hd1 := toNat_succ_of_ne hd
  rcases c1 : callW p n "intern_fvar" [d, ty1] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, ecbE.k_intern_fvar.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s₁, hs₁, -, hfv⟩ := triple_of_callW
    (internFVar_spec p hq.body.fvf hq.body.fvp hq.body.fvi n s₀ d ty1) c1
  rw [hs₁] at hfv
  have h₁ := internFVar_core hs.rel d ty1 hty r₁ hfv
  refine RefE.bind_core (w := id) h₁ (fun M₁ hS₁ _ => ?_)
  simp only [ecbE.k_intern_fvar]
  rcases c2 : callW p n "inst1" [body1, r₁.headD 0, 0] m₁ with _ | ⟨r₂, m₂⟩
  · rw [liftE_none, ecbE.k_inst1.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have h₂ := CoreSpec.of_callW (hc.inst1 n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb body1 (r₁.headD 0) 0
    hS₁ hbody h₁.2.2.2) c2
  refine RefE.bind_core (w := id) h₂ (fun M₂ hS₂ _ => ?_)
  simp only [ecbE.k_inst1]
  rcases c3 : callW p n "mk_app" [b, r₁.headD 0] m₂ with _ | ⟨r₃, m₃⟩
  · rw [liftE_none, ecbE.k_mk_app.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have h₃ := mkApp_core hq.leaf.core.spine hS₂ b (r₁.headD 0) r₃ c3
  refine RefE.bind_core (w := id) h₃ (fun M₃ hS₃ _ => ?_)
  simp only [ecbE.k_mk_app]
  have hD := hK.defeq F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode (d + 1) (r₂.headD 0) (r₃.headD 0)
    hF hn ⟨hS₃, hs.mode4, hs.eb_mode⟩ h₂.2.2.2 h₃.2.2.2
  rw [hd1] at hD
  rcases c4 : callE p n "defeq" [mode, vis, d + 1, r₂.headD 0, r₃.headD 0] m₃ with e4 | ⟨r₄, m₄⟩
  · intro hkE
    have h := CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).defeq F ⟨m₃, Locals.init []⟩ _ dn vis fe
      M₃ eb mode (d + 1) _ _ hF hn ⟨hS₃, hs.mode4, hs.eb_mode⟩ h₂.2.2.2 h₃.2.2.2) c4
    rw [hd1] at h
    exact ErrClaim.bind_left h
  have h₄ := CoreSpec.of_callW hD (callW_of_callE c4)
  refine RefE.bind_core (w := id) h₄ (fun M₄ hS₄ _ => ?_)
  simp only [ecbE.k_defeq]
  by_cases h0 : r₄.headD 0 = 0
  · rw [ite_eq_left h0, decBool_false_of h0]
    exact RefE.ret rfl (CorePost.ret hS₄ rfl hw0)
  rw [ite_eq_right h0, decBool_true_of h0, decMode_vc mode hs.mode4]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hm : mode &&& 1 = 0
  · rw [ite_eq_left hm]
    simp only [hm, decide_true, ↓reduceIte]
    cases n with
    | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
    | succ N =>
    exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hkE => hkE.mono (Nat.le_succ N)) rfl
      (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
      (ect_ref p hc N (hk.mono (Nat.le_succ N)) F ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode d
        (r₂.headD 0) cod2 (r₁.headD 0) (by omega) (by omega) ⟨hS₄, hs.mode4, hs.eb_mode⟩ hd h₂.2.2.2
        hcod h₁.2.2.2)
  · rw [ite_eq_right hm]
    simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS₄ rfl hw1)

/-- **`eta_cert` refines `etaCert`, both outcomes**: the errors are the `infer_io`, `whnf`,
`defeq` slots' and `eta_cert_body`'s. -/
theorem ec_ref (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d ty1 body1 b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty1) (hbody : HW body1)
    (hb : HW b) :
    RefE (KnotUpToE p n) (ecE p (n + 1) s₀.mem mode vis d ty1 body1 b)
      (etaCert (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty1) (decE body1)
        (decE b)) a₀ (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  simp only [ecE]
  rw [etaCert_eq]
  rcases c1 : callW p n "io_neutral" [b] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, ecE.k_io_neutral.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have h₁ := CoreSpec.of_callW (ioNeutral_at p hq.leaf n s₀ a₀ dn vis fe M eb b hs.rel hb) c1
  refine RefE.bind_core (w := id) h₁ (fun M₁ hS₁ _ => ?_)
  simp only [ecE.k_io_neutral]
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0, decBool_false_of h0]
    exact RefE.ret rfl (CorePost.ret hS₁ rfl hw0)
  rw [ite_eq_right h0, decBool_true_of h0]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rcases c2 : callE p n "infer_io" [mode, vis, d, b] m₁ with e2 | ⟨r₂, m₂⟩
  · exact fun hkE => ErrClaim.bind_left (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).inferIO F
      ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d b hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb) c2)
  have h₂ := CoreSpec.of_callW (hK.inferIO F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d b hF hn
    ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb) (callW_of_callE c2)
  refine RefE.bind_core (w := id) h₂ (fun M₂ hS₂ _ => ?_)
  simp only [ecE.k_infer_io]
  rcases c3 : callE p n "whnf" [mode, vis, d, r₂.headD 0] m₂ with e3 | ⟨r₃, m₃⟩
  · exact fun hkE => ErrClaim.bind_left (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).whnf F
      ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d (r₂.headD 0) hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩
      h₂.2.2.2) c3)
  have h₃ := CoreSpec.of_callW (hK.whnf F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d (r₂.headD 0)
    hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ h₂.2.2.2) (callW_of_callE c3)
  refine RefE.bind_core (w := id) h₃ (fun M₃ hS₃ _ => ?_)
  have hh3 : HW (r₃.headD 0) := h₃.2.2.2
  simp only [ecE.k_whnf, decH, tag_beq_w _ hh3 6 (by decide) ETag.forallE rfl 6 rfl]
  by_cases h6 : r₃.headD 0 >>> 28 ≠ 6
  · rw [ite_eq_left h6]
    simp only [h6, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS₃ rfl hw0)
  rw [ite_eq_right h6]
  have h6' : r₃.headD 0 >>> 28 = 6 := by simpa using h6
  by_cases ht : tierW (r₃.headD 0) ≠ 0 ∧ rdW (m₃.arr64 CTL) 1 = 0
  · rw [ite_eq_left ht]; exact RefE.of_cls0 (by decide)
  rw [ite_eq_right ht]
  by_cases hi : tcnt m₃ FORALL (tierW (r₃.headD 0)) ≤ idxW (r₃.headD 0)
  · rw [ite_eq_left hi]; exact RefE.of_cls0 (by decide)
  rw [ite_eq_right hi]
  have hi' : idxW (r₃.headD 0) < tcnt m₃ FORALL (tierW (r₃.headD 0)) := by simpa using hi
  simp only [h6', decide_true, ↓reduceIte]
  obtain ⟨hv, hty2, hcod2⟩ := view_forall m₃ _ hS₃.arena.base (r₃.headD 0) hh3 ⟨ht, hi'⟩ h6'
  refine RefE.bind_right (view_run _ _ _ hv) ?_
  simp only
  rcases c4 : callE p n "defeq" [mode, vis, d, tfld m₃ FORALL (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0,
      ty1] m₃ with e4 | ⟨r₄, m₄⟩
  · exact fun hkE => ErrClaim.bind_left (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).defeq F
      ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode d _ ty1 hF hn ⟨hS₃, hs.mode4, hs.eb_mode⟩ hty2 hty) c4)
  have h₄ := CoreSpec.of_callW (hK.defeq F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode d _ ty1 hF hn
    ⟨hS₃, hs.mode4, hs.eb_mode⟩ hty2 hty) (callW_of_callE c4)
  refine RefE.bind_core (w := id) h₄ (fun M₄ hS₄ _ => ?_)
  simp only [ecE.k_defeq]
  by_cases h40 : r₄.headD 0 = 0
  · rw [ite_eq_left h40, decBool_false_of h40]
    exact RefE.ret rfl (CorePost.ret hS₄ rfl hw0)
  rw [ite_eq_right h40, decBool_true_of h40]
  simp only [↓reduceIte]
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ N =>
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hkE => hkE.mono (Nat.le_succ N)) rfl
    (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
    (ecb_ref p hq hc N (hk.mono (Nat.le_succ N)) F ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode d ty1
      body1 b _ (by omega) (by omega) ⟨hS₄, hs.mode4, hs.eb_mode⟩ hty hbody hcod2)

/-- **`eta_cert` refines `etaCert`** at the knot, from the knot's slots, `io_neutral`, `inst1`
and `mk_app` (`ec_ref`'s ok half). -/
@[refines ConRon.Arena.etaCert]
theorem etaCert_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d ty1 body1 b : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty1) (hbody : HW body1)
    (hb : HW b) :
    CoreSpec p (n + 1) "eta_cert" [mode, vis, d, ty1, body1, b]
      (etaCert (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty1) (decE body1)
        (decE b)) decBool s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (ecE_spec p hq.etaCert hq.etaCertBody hq.etaCertTy (n + 1) s₀ mode vis d ty1 body1 b)
    (ec_ref p hq hc n hk F s₀ a₀ dn vis fe M eb mode d ty1 body1 b hF hn hs hty hbody hb)

end L.Arena
