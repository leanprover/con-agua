import ConAgua.Verdict.InferBindE
import ConAgua.Arena.InferBodyDisp
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# Error refinements of the inference bodies and the knot's `infer`, `infer_io` slots
(lane `verdicts-b`, helper `k1`)

`infer_body`, `infer_body_io` (the dispatchers: `e_view` claims nothing, each clause's claim is
its arm's: `InferArmsE.lean`, `InferSpineE.lean`, `InferBindE.lean`, `InferLeavesE.lean`; a free
variable out of scope rejects, a loose bound variable declines) and the two memo slots `infer`,
`infer_io` (the memo's callees claim nothing; on a miss the body's failure is the slot's). The
goal: the error halves of the knot's `infer` and `infer_io` steps,
`inferSlot_stepE`/`inferIOSlot_stepE`: `KnotUpTo p n → KnotUpToE p n → InferSlotE p (n + 1)`
(resp. `InferIOSlotE`), under the ok step's program hypotheses (`InferAllProg`), its callees'
ok specs (`InferCallees`) and their error claims (`InferCalleesE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The bodies' error specs -/

/-- `infer_body`'s error claim (the error half of `InferBodySpec`). -/
def InferBodySpecE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW e → KnotUpTo p n → KnotUpToE p n →
    CoreSpecE p n "infer_body" [mode, vis, d, e]
      (inferBody (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) s₀ a₀

/-- `infer_body_io`'s error claim (the error half of `InferIOBodySpec`). -/
def InferIOBodySpecE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW e → KnotUpTo p n → KnotUpToE p n →
    CoreSpecE p n "infer_body_io" [mode, vis, d, e]
      (inferBodyIO (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE e)) s₀ a₀

l_model inferBody_specE (p : Prog) (hf : p.lookup "infer_body" = some inferBodyL)
  fns [hf ↦ inferBodyE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [tierW, idxW] errors

l_model inferBodyIO_specE (p : Prog) (hf : p.lookup "infer_body_io" = some inferBodyIOL)
  fns [hf ↦ inferBodyIOE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [tierW, idxW] errors

/-! ## The twin's arms that fail at the dispatcher -/

section arms
variable (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)

theorem inferBody_bvarE (i : Nat) (hv : a.store.view e = some (.bvar i)) :
    (inferBody r fe d e).run a = .error (.notImplemented "inferType beyond the supported fragment") := by
  simp only [inferBody, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; rfl

theorem inferBodyIO_bvarE (i : Nat) (hv : a.store.view e = some (.bvar i)) :
    (inferBodyIO r fe d e).run a =
      .error (.notImplemented "inferType beyond the supported fragment") := by
  simp only [inferBodyIO, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; rfl

theorem inferBody_fvarE (i : Nat) (ty : EIdx) (hv : a.store.view e = some (.fvar i ty)) (hi : ¬ i < d) :
    (inferBody r fe d e).run a = .error (.invalid "free variable out of scope") := by
  simp only [inferBody, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hi, ↓reduceIte]; rfl

theorem inferBodyIO_fvarE (i : Nat) (ty : EIdx) (hv : a.store.view e = some (.fvar i ty))
    (hi : ¬ i < d) :
    (inferBodyIO r fe d e).run a = .error (.invalid "free variable out of scope") := by
  simp only [inferBodyIO, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hi, ↓reduceIte]; rfl

end arms

/-- **The io `.const` clause fails where the full one does** (with a class other than `0`: the
two differ only in how a dangling level list fails). -/
theorem inferConstIOT_err (fe : IFEnv) (n : NIdx) (us : LsIdx) (a : AState) (ce : CheckError)
    (h : (inferConstT fe n us).run a = .error ce) (hc : twinCls ce ≠ 0) :
    (inferConstIOT fe n us).run a = .error ce := by
  unfold inferConstT at h; unfold inferConstIOT
  cases hf : fe.find? n with
  | none => rw [hf] at h; exact h
  | some ci =>
  rw [hf] at h
  simp only [StateT.run_bind] at h ⊢
  generalize ci.toConstantVal = cv at h ⊢
  cases hv : a.store.lss.view us with
  | none =>
    have e1 : (viewLs us).run a = .error (.internal "arena: dangling level-list handle") := by
      simp only [viewLs, StateT.run_bind, StateT.run_get, pure_bind, hv]; rfl
    rw [e1] at h
    have h' : (Except.error (CheckError.internal "arena: dangling level-list handle") :
        Except CheckError (EIdx × AState)) = .error ce := h
    cases h'; exact absurd rfl hc
  | some ids =>
  have hl := LsStore.viewLen_of_view _ _ _ hv
  have e1 : (viewLs us).run a = .ok (ids, a) := viewLs_run us a ids hv
  have e2 : (viewLsLen us).run a = .ok (some ids.length, a) := by
    simp [viewLsLen, hl, StateT.run_get]; rfl
  rw [e1] at h; rw [e2]
  simp only [except_ok_bind] at h ⊢
  exact h

/-- An io `.const` claim from the full one. -/
theorem ErrClaim.constIO {fe : IFEnv} {n : NIdx} {us : LsIdx} {a : AState} {e : Err}
    (h : ErrClaim (inferConstT fe n us) a e) : ErrClaim (inferConstIOT fe n us) a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h hk
  exact ⟨ce, inferConstIOT_err fe n us a ce hce (by rw [hc]; exact hk), hc⟩

theorem kisE_err {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {m : Mem} {er : Err}
    (hW : inferBodyE.k_intern_sort p (callE p n f vs m) = .error er) : callE p n f vs m = .error er := by
  cases h : callE p n f vs m with
  | error e => rw [h, inferBodyE.k_intern_sort.none] at hW; cases hW; rfl
  | ok q => obtain ⟨r, m'⟩ := q; rw [h, inferBodyE.k_intern_sort.arm1] at hW; cases hW

theorem kisIOE_err {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {m : Mem} {er : Err}
    (hW : inferBodyIOE.k_intern_sort p (callE p n f vs m) = .error er) :
    callE p n f vs m = .error er := by
  cases h : callE p n f vs m with
  | error e => rw [h, inferBodyIOE.k_intern_sort.none] at hW; cases hW; rfl
  | ok q => obtain ⟨r, m'⟩ := q; rw [h, inferBodyIOE.k_intern_sort.arm1] at hW; cases hW

/-! ## `infer_body` -/

/-- **`infer_body`'s verdicts** (the error half of `inferBody_refines`): `InferBodySpecE p n`
for every `n`. -/
theorem inferBody_refinesE (p : Prog) (hq : InferAllProg p) (hc : InferCallees p)
    (hcE : InferCalleesE p) : ∀ n, InferBodySpecE p n := by
  intro n F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he hk hkE
  cases n with
  | zero => exact CoreSpecE.zero p _ _ _ s₀ a₀
  | succ n =>
  refine CoreSpecE.of_runs fun er hc00 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferBody_specE p hq.inferBody (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d e) hc00 (Err.code_ne_of_cls hk0)
  rw [inferBodyE.eq_2] at hW
  have hS := hs.rel
  have hnv := hcE.nv
  cases hc0 : callE p n "e_view" [e] s₀.mem with
  | error e0 =>
    rw [hc0, inferBodyE.k_e_view.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "e_view" (by simp)) hc0
  | ok q =>
  obtain ⟨r₀, m₀⟩ := q
  rw [hc0] at hW
  obtain ⟨t₀, ht₀, hts, hne, hr0⟩ := triple_of_callE
    (L.Ind.eView_spec p hq.eview n ⟨s₀.mem, Locals.init []⟩ e) hc0
  have hm₀ : m₀ = s₀.mem := by rw [← ht₀, hts]
  subst hm₀
  subst hr0
  obtain ⟨v, hv, hvr⟩ := L.Ind.eViewW_ok s₀.mem a₀ hS.arena.1 e hne
  have hhd := eViewW_head s₀.mem e hne
  have hsl : SlotPre ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode := ⟨hS, hs.mode4, hs.eb_mode⟩
  cases v with
  | bvar i =>
    obtain ⟨hg, -⟩ := hvr
    simp (config := { decide := true }) only [inferBodyE.k_e_view, hg, ↓reduceIte] at hW
    cases hW
    exact ErrClaim.of_error (inferBody_bvarE _ fe d.toNat (decE e) a₀ i hv) rfl
  | fvar idx ty =>
    obtain ⟨hg, hi, hty, hdec⟩ := hvr
    simp (config := { decide := true }) only [inferBodyE.k_e_view, hg, ↓reduceIte] at hW
    rw [getD1] at hi
    by_cases hlt : (L.Ind.eViewW s₀.mem e).tail.headD 0 < d
    · simp only [hlt, ↓reduceIte] at hW; cases hW
    · simp only [hlt, ↓reduceIte] at hW; cases hW
      have hi' : ¬ idx < d.toNat := fun h => hlt (by
        rw [UInt64.lt_iff_toNat_lt, hi]; exact h)
      exact ErrClaim.of_error (inferBody_fvarE _ fe d.toNat (decE e) a₀ idx ty hv hi') rfl
  | sort u =>
    obtain ⟨hg, hu, hdec⟩ := hvr
    simp (config := { decide := true }) only [inferBodyE.k_e_view, hg, ↓reduceIte] at hW
    cases h1 : callE p n "intern_succ" [(L.Ind.eViewW s₀.mem e).tail.headD 0] s₀.mem with
    | error e1 =>
      rw [h1, inferBodyE.k_intern_succ.none] at hW; cases hW
      exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "intern_succ" (by simp)) h1
    | ok q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [h1, inferBodyE.k_intern_succ.arm1] at hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "intern_sort" (by simp)) (kisE_err hW)
  | const nm us =>
    obtain ⟨hg, hn1, hdn, hu2, hdu⟩ := hvr
    rw [getD1] at hn1 hdn; rw [getD2] at hu2 hdu
    simp (config := { decide := true }) only [inferBodyE.k_e_view, hg, ↓reduceIte] at hW
    have h1 := kisE_err hW
    cases n with
    | zero => exact absurd (callE_zero_cls h1) hk0
    | succ k =>
    rw [← hdn, ← hdu] at hv
    exact ErrClaim.of_run_eq' (fun ce h => (inferBody_const _ fe d.toNat (decE e) a₀ _ _ hv).trans h)
      (CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
        (inferConst_refinesE p hq.leaf hnv k _ a₀ dn vis fe MM eb _ _ hS hn1 hu2) h1)
  | lit l =>
    have hg : (L.Ind.eViewW s₀.mem e).headD 0 = 8 := hvr
    simp (config := { decide := true }) only [inferBodyE.k_e_view, hg, ↓reduceIte] at hW
    have h1 := kisE_err hW
    cases n with
    | zero => exact absurd (callE_zero_cls h1) hk0
    | succ k =>
    have h8 : e >>> 28 = 8 := by rw [← hhd, hg]
    exact ErrClaim.of_run_eq' (fun ce h => (inferBody_lit _ fe d.toNat (decE e) a₀ l hv).trans h)
      (CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
        (inferLit_refinesE p hq.leaf hc.lit hnv k _ a₀ dn vis fe MM eb e l hS he h8 hv) h1)
  | forallE ty b =>
    obtain ⟨hg, h1', hd1, h2', hd2⟩ := hvr
    rw [getD1] at h1' hd1; rw [getD2] at h2' hd2
    simp (config := { decide := true }) only [inferBodyE.k_e_view, hg, ↓reduceIte] at hW
    have h1 := kisE_err hW
    cases n with
    | zero => exact absurd (callE_zero_cls h1) hk0
    | succ k =>
    rw [← hd1, ← hd2] at hv
    exact ErrClaim.of_run_eq' (fun ce h => (inferBody_forall _ fe d.toNat (decE e) a₀ _ _ hv).trans h)
      (CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
        (inferForall_refinesE p hq.leaf hq.bind hq.body hc.instList hnv hc.bcap k (hk.mono (by omega))
          (hkE.mono (by omega)) F (by omega) (by omega) _ a₀ dn vis fe MM eb mode d _ _ hsl h1' h2') h1)
  | lam ty b =>
    obtain ⟨hg, h1', hd1, h2', hd2⟩ := hvr
    rw [getD1] at h1' hd1; rw [getD2] at h2' hd2
    simp (config := { decide := true }) only [inferBodyE.k_e_view, hg, ↓reduceIte] at hW
    have h1 := kisE_err hW
    cases n with
    | zero => exact absurd (callE_zero_cls h1) hk0
    | succ k =>
    rw [← hd1, ← hd2] at hv
    exact ErrClaim.of_run_eq' (fun ce h => (inferBody_lam _ fe d.toNat (decE e) a₀ _ _ hv).trans h)
      (CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
        (inferLam_refinesE p hq.leaf hq.bind hq.body hc.instList hnv hc.bcap k (hk.mono (by omega))
          (hkE.mono (by omega)) F (by omega) (by omega) _ a₀ dn vis fe MM eb mode d _ _ hsl h1' h2') h1)
  | app f x =>
    obtain ⟨hg, -⟩ := hvr
    simp (config := { decide := true }) only [inferBodyE.k_e_view, hg, ↓reduceIte] at hW
    have h1 := kisE_err hW
    cases n with
    | zero => exact absurd (callE_zero_cls h1) hk0
    | succ k =>
    have h4 : e >>> 28 = 4 := by rw [← hhd, hg]
    exact ErrClaim.of_run_eq' (fun ce h => (inferBody_app _ fe d.toNat (decE e) a₀ f x hv).trans h)
      (CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
        (inferApp_refinesE p hq.leaf hq.knot hq.spf hq.spine hc.eager hcE.defeqArg hc.instList hnv k
          (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega) _ a₀ dn vis fe MM eb mode
          d e hsl he h4) h1)
  | letE ty v b =>
    obtain ⟨hg, h1', hd1, h2', hd2, h3', hd3⟩ := hvr
    rw [getD1] at h1' hd1; rw [getD2] at h2' hd2; rw [getD3] at h3' hd3
    simp (config := { decide := true }) only [inferBodyE.k_e_view, hg, ↓reduceIte] at hW
    have h1 := kisE_err hW
    cases n with
    | zero => exact absurd (callE_zero_cls h1) hk0
    | succ k =>
    rw [← hd1, ← hd2, ← hd3] at hv
    exact ErrClaim.of_run_eq' (fun ce h => (inferBody_let _ fe d.toNat (decE e) a₀ _ _ _ hv).trans h)
      (CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
        (inferLet_refinesE p hq.leaf hq.body hnv hc.inst1 k (hk.mono (by omega)) (hkE.mono (by omega)) F
          _ a₀ dn vis fe MM eb mode d _ _ _ (by omega) (by omega) hsl h1' h2' h3') h1)
  | proj sn i pe =>
    obtain ⟨hg, h1', hd1, h2', h3', hd3⟩ := hvr
    rw [getD1] at h1' hd1; rw [getD2] at h2'; rw [getD3] at h3' hd3
    simp (config := { decide := true }) only [inferBodyE.k_e_view, hg, ↓reduceIte] at hW
    have h1 := kisE_err hW
    cases n with
    | zero => exact absurd (callE_zero_cls h1) hk0
    | succ k =>
    rw [← hd1, ← h2', ← hd3] at hv
    exact ErrClaim.of_run_eq' (fun ce h => (inferBody_proj _ fe d.toNat (decE e) a₀ _ _ _ hv).trans h)
      (CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
        (hcE.proj k (hk.mono (by omega)) (hkE.mono (by omega)) F _ a₀ dn vis fe MM eb mode d _ _ _
          (by omega) (by omega) hsl h1' h3').1 h1)

/-! ## `infer_body_io` -/

/-- **`infer_body_io`'s verdicts** (the error half of `inferBodyIO_refines`): `InferIOBodySpecE p n`
for every `n`. -/
theorem inferBodyIO_refinesE (p : Prog) (hq : InferAllProg p) (hc : InferCallees p)
    (hcE : InferCalleesE p) : ∀ n, InferIOBodySpecE p n := by
  intro n F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he hk hkE
  cases n with
  | zero => exact CoreSpecE.zero p _ _ _ s₀ a₀
  | succ n =>
  refine CoreSpecE.of_runs fun er hc00 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferBodyIO_specE p hq.inferBodyIO (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d e) hc00 (Err.code_ne_of_cls hk0)
  rw [inferBodyIOE.eq_2] at hW
  have hS := hs.rel
  have hnv := hcE.nv
  cases hc0 : callE p n "e_view" [e] s₀.mem with
  | error e0 =>
    rw [hc0, inferBodyIOE.k_e_view.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "e_view" (by simp)) hc0
  | ok q =>
  obtain ⟨r₀, m₀⟩ := q
  rw [hc0] at hW
  obtain ⟨t₀, ht₀, hts, hne, hr0⟩ := triple_of_callE
    (L.Ind.eView_spec p hq.eview n ⟨s₀.mem, Locals.init []⟩ e) hc0
  have hm₀ : m₀ = s₀.mem := by rw [← ht₀, hts]
  subst hm₀
  subst hr0
  obtain ⟨v, hv, hvr⟩ := L.Ind.eViewW_ok s₀.mem a₀ hS.arena.1 e hne
  have hhd := eViewW_head s₀.mem e hne
  have hsl : SlotPre ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode := ⟨hS, hs.mode4, hs.eb_mode⟩
  cases v with
  | bvar i =>
    obtain ⟨hg, -⟩ := hvr
    simp (config := { decide := true }) only [inferBodyIOE.k_e_view, hg, ↓reduceIte] at hW
    cases hW
    exact ErrClaim.of_error (inferBodyIO_bvarE _ fe d.toNat (decE e) a₀ i hv) rfl
  | fvar idx ty =>
    obtain ⟨hg, hi, hty, hdec⟩ := hvr
    simp (config := { decide := true }) only [inferBodyIOE.k_e_view, hg, ↓reduceIte] at hW
    rw [getD1] at hi
    by_cases hlt : (L.Ind.eViewW s₀.mem e).tail.headD 0 < d
    · simp only [hlt, ↓reduceIte] at hW; cases hW
    · simp only [hlt, ↓reduceIte] at hW; cases hW
      have hi' : ¬ idx < d.toNat := fun h => hlt (by
        rw [UInt64.lt_iff_toNat_lt, hi]; exact h)
      exact ErrClaim.of_error (inferBodyIO_fvarE _ fe d.toNat (decE e) a₀ idx ty hv hi') rfl
  | sort u =>
    obtain ⟨hg, hu, hdec⟩ := hvr
    simp (config := { decide := true }) only [inferBodyIOE.k_e_view, hg, ↓reduceIte] at hW
    cases h1 : callE p n "intern_succ" [(L.Ind.eViewW s₀.mem e).tail.headD 0] s₀.mem with
    | error e1 =>
      rw [h1, inferBodyIOE.k_intern_succ.none] at hW; cases hW
      exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "intern_succ" (by simp)) h1
    | ok q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [h1, inferBodyIOE.k_intern_succ.arm1] at hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "intern_sort" (by simp)) (kisIOE_err hW)
  | const nm us =>
    obtain ⟨hg, hn1, hdn, hu2, hdu⟩ := hvr
    rw [getD1] at hn1 hdn; rw [getD2] at hu2 hdu
    simp (config := { decide := true }) only [inferBodyIOE.k_e_view, hg, ↓reduceIte] at hW
    have h1 := kisIOE_err hW
    cases n with
    | zero => exact absurd (callE_zero_cls h1) hk0
    | succ k =>
    rw [← hdn, ← hdu] at hv
    exact ErrClaim.of_run_eq' (fun ce h => (inferBodyIO_const _ fe d.toNat (decE e) a₀ _ _ hv).trans h)
      (ErrClaim.constIO (CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
        (inferConst_refinesE p hq.leaf hnv k _ a₀ dn vis fe MM eb _ _ hS hn1 hu2) h1))
  | lit l =>
    have hg : (L.Ind.eViewW s₀.mem e).headD 0 = 8 := hvr
    simp (config := { decide := true }) only [inferBodyIOE.k_e_view, hg, ↓reduceIte] at hW
    have h1 := kisIOE_err hW
    cases n with
    | zero => exact absurd (callE_zero_cls h1) hk0
    | succ k =>
    have h8 : e >>> 28 = 8 := by rw [← hhd, hg]
    exact ErrClaim.of_run_eq' (fun ce h => (inferBodyIO_lit _ fe d.toNat (decE e) a₀ l hv).trans h)
      (CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
        (inferLit_refinesE p hq.leaf hc.lit hnv k _ a₀ dn vis fe MM eb e l hS he h8 hv) h1)
  | forallE ty b =>
    obtain ⟨hg, h1', hd1, h2', hd2⟩ := hvr
    rw [getD1] at h1' hd1; rw [getD2] at h2' hd2
    simp (config := { decide := true }) only [inferBodyIOE.k_e_view, hg, ↓reduceIte] at hW
    have h1 := kisIOE_err hW
    cases n with
    | zero => exact absurd (callE_zero_cls h1) hk0
    | succ k =>
    rw [← hd1, ← hd2] at hv
    exact ErrClaim.of_run_eq' (fun ce h => (inferBodyIO_forall _ fe d.toNat (decE e) a₀ _ _ hv).trans h)
      (CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
        (inferForallIO_refinesE p hq.leaf hq.body hnv hc.inst1 k (hk.mono (by omega)) (hkE.mono (by omega))
          F _ a₀ dn vis fe MM eb mode d _ _ (by omega) (by omega) hsl h1' h2') h1)
  | lam ty b =>
    obtain ⟨hg, h1', hd1, h2', hd2⟩ := hvr
    rw [getD1] at h1' hd1; rw [getD2] at h2' hd2
    simp (config := { decide := true }) only [inferBodyIOE.k_e_view, hg, ↓reduceIte] at hW
    have h1 := kisIOE_err hW
    cases n with
    | zero => exact absurd (callE_zero_cls h1) hk0
    | succ k =>
    rw [← hd1, ← hd2] at hv
    exact ErrClaim.of_run_eq' (fun ce h => (inferBodyIO_lam _ fe d.toNat (decE e) a₀ _ _ hv).trans h)
      (CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
        (inferLamIO_refinesE p hq.body hnv hc.inst1 k (hkE.mono (by omega)) F _ a₀ dn vis fe MM eb mode d
          _ _ (by omega) (by omega) hsl h1' h2') h1)
  | app f x =>
    obtain ⟨hg, -⟩ := hvr
    simp (config := { decide := true }) only [inferBodyIOE.k_e_view, hg, ↓reduceIte] at hW
    have h1 := kisIOE_err hW
    cases n with
    | zero => exact absurd (callE_zero_cls h1) hk0
    | succ k =>
    have h4 : e >>> 28 = 4 := by rw [← hhd, hg]
    exact ErrClaim.of_run_eq' (fun ce h => (inferBodyIO_app _ fe d.toNat (decE e) a₀ f x hv).trans h)
      (CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
        (inferAppIO_refinesE p hq.spio hq.spine hc.instList hnv k (hk.mono (by omega))
          (hkE.mono (by omega)) F (by omega) (by omega) _ a₀ dn vis fe MM eb mode d e hsl he h4) h1)
  | letE ty v b =>
    obtain ⟨hg, h1', hd1, h2', hd2, h3', hd3⟩ := hvr
    rw [getD1] at h1' hd1; rw [getD2] at h2' hd2; rw [getD3] at h3' hd3
    simp (config := { decide := true }) only [inferBodyIOE.k_e_view, hg, ↓reduceIte] at hW
    rw [← hd1, ← hd2, ← hd3] at hv
    refine ErrClaim.of_run_eq' (fun ce h => (inferBodyIO_let _ fe d.toNat (decE e) a₀ _ _ _ hv).trans h) ?_
    cases hi : callE p n "inst1" [(L.Ind.eViewW s₀.mem e).tail.tail.tail.headD 0,
        (L.Ind.eViewW s₀.mem e).tail.tail.headD 0, 0] s₀.mem with
    | error e1 =>
      rw [hi, inferBodyIOE.k_inst1.none] at hW; cases hW
      exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "inst1" (by simp)) hi
    | ok q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hi, inferBodyIOE.k_inst1.arm1] at hW
    have h₁ := CoreSpec.of_callW (hc.inst1 n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb _ _ 0 hS h3' h2')
      (callW_of_callE hi)
    obtain ⟨M₁, hS₁, -, -⟩ := h₁.2.1
    refine ErrClaim.bind_ref h₁ ?_
    exact CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      ((hkE n (by omega)).inferIO F _ _ dn vis fe M₁ eb mode d (r₁.headD 0) (by omega) (by omega)
        ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) (kisIOE_err hW)
  | proj sn i pe =>
    obtain ⟨hg, h1', hd1, h2', h3', hd3⟩ := hvr
    rw [getD1] at h1' hd1; rw [getD2] at h2'; rw [getD3] at h3' hd3
    simp (config := { decide := true }) only [inferBodyIOE.k_e_view, hg, ↓reduceIte] at hW
    have h1 := kisIOE_err hW
    cases n with
    | zero => exact absurd (callE_zero_cls h1) hk0
    | succ k =>
    rw [← hd1, ← h2', ← hd3] at hv
    exact ErrClaim.of_run_eq' (fun ce h => (inferBodyIO_proj _ fe d.toNat (decE e) a₀ _ _ _ hv).trans h)
      (CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
        (hcE.proj k (hk.mono (by omega)) (hkE.mono (by omega)) F _ a₀ dn vis fe MM eb mode d _ _ _
          (by omega) (by omega) hsl h1' h3').2 h1)

/-! ## The slots `infer`, `infer_io` -/

l_model infer_specE (p : Prog) (hf : p.lookup "infer" = some inferSlotL)
  fns [hf ↦ inferE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] heartbeats 400000 errors

l_model inferIO_specE (p : Prog) (hf : p.lookup "infer_io" = some inferIOSlotL)
  fns [hf ↦ inferIOE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] heartbeats 400000 errors

theorem knot_infer_missE (mode : ConLeche.CheckMode) (fe : IFEnv) (F d : Nat) (e : EIdx) (a : AState)
    (hm : a.caches.inferC[e]? = none) (ce : CheckError)
    (hb : (inferBody (coreKnot mode fe id F) fe d e).run a = .error ce) :
    ((coreKnot mode fe id (F + 1)).infer d e).run a = .error ce := by
  simp [coreKnot, hm, StateT.run_bind, hb]; rfl

theorem knot_inferIO_missE (mode : ConLeche.CheckMode) (fe : IFEnv) (F d : Nat) (e : EIdx)
    (a : AState) (hm : a.caches.inferIOC[e]? = none) (ce : CheckError)
    (hb : (inferBodyIO (CoreFnsA.ioView (coreKnot mode fe id F)) fe d e).run a = .error ce) :
    ((coreKnot mode fe id (F + 1)).inferIO d e).run a = .error ce := by
  simp [coreKnot, hm, StateT.run_bind, hb]; rfl

/-- **`infer`'s verdicts** (the error half of `infer_refines`): a hit succeeds, a miss fails as
the body; the memo's `in_find`/`in_put` claim nothing. -/
theorem infer_refinesE (p : Prog) (hp : KnotProg p) (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (hb : InferBodySpecE p n) : InferSlotE p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hs he
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (infer_specE p hp.infer (n + 1) ⟨s₀.mem, Locals.init []⟩ mode vis d e)
    hc0 (Err.code_ne_of_cls hk0)
  rw [inferE.eq_2] at hW
  have hS := hs.rel
  have hkey : ((mode >>> 1) &&& 1) <<< 32 = genW 0 eb := ebKey_eq mode eb hs.eb_mode
  rw [hkey] at hW
  cases h1 : callE p n "in_find" [e, genW 0 eb] s₀.mem with
  | error e1 =>
    rw [h1, inferE.k_in_find.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "in_find" (by simp)) h1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1] at hW
  obtain ⟨t₁, ht₁, hst, hne, hr⟩ := triple_of_callE
    (memoFindG_spec inSch p "in_find" hp.inFind n ⟨s₀.mem, Locals.init []⟩ e (genW 0 eb)) h1
  have hm₁ : m₁ = s₀.mem := by rw [← ht₁, hst]
  subst hm₁
  subst hr
  by_cases h1' : (mfindG inSch s₀.mem e (genW 0 eb)).headD 0 ≠ 0
  · simp only [inferE.k_in_find] at hW; rw [ite_eq_left h1'] at hW; cases hW
  have hmiss := (hS.core.inf.findE hS.core.eb1 e he hne).2 (by simpa using h1')
  simp only [inferE.k_in_find] at hW; rw [ite_eq_right h1'] at hW
  cases h2 : callE p n "infer_body" [mode, vis, d, e] s₀.mem with
  | error e2 =>
    rw [h2, inferE.k_infer_body.none] at hW; cases hW
    have hcl := CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩) (hb F' _ a₀ dn vis fe MM eb mode d e
      (by omega) (by omega) ⟨hS, hs.mode4, hs.eb_mode⟩ he hk hkE) h2
    exact ErrClaim.of_run_eq' (fun ce h => knot_infer_missE _ fe F' d.toNat _ a₀ hmiss ce h) hcl
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2, inferE.k_infer_body.arm1] at hW
  cases h3 : callE p n "in_find" [e, genW 0 eb] m₂ with
  | error e3 =>
    rw [h3, inferE.k_in_find_2.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "in_find" (by simp)) h3
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [h3] at hW; simp only [inferE.k_in_find_2] at hW
  cases h4 : callE p n "in_put" [e, genW 0 eb, r₂.headD 0, r₃.headD 0, r₃.tail.headD 0] m₃ with
  | error e4 =>
    rw [h4, inferE.k_in_put.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "in_put" (by simp)) h4
  | ok q => rw [h4] at hW; simp [inferE.k_in_put] at hW

/-- **`infer_io`'s verdicts** (the error half of `inferIO_refines`). -/
theorem inferIO_refinesE (p : Prog) (hp : KnotProg p) (hnv : closedNV p L.Checker.nvFns = true)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (hb : InferIOBodySpecE p n) :
    InferIOSlotE p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hs he
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferIO_specE p hp.inferIO (n + 1) ⟨s₀.mem, Locals.init []⟩ mode vis
    d e) hc0 (Err.code_ne_of_cls hk0)
  rw [inferIOE.eq_2] at hW
  have hS := hs.rel
  have hkey : ((mode >>> 1) &&& 1) <<< 32 = genW 0 eb := ebKey_eq mode eb hs.eb_mode
  rw [hkey] at hW
  cases h1 : callE p n "io_find" [e, genW 0 eb] s₀.mem with
  | error e1 =>
    rw [h1, inferIOE.k_io_find.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "io_find" (by simp)) h1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1] at hW
  obtain ⟨t₁, ht₁, hst, hne, hr⟩ := triple_of_callE
    (memoFindG_spec ioSch p "io_find" hp.ioFind n ⟨s₀.mem, Locals.init []⟩ e (genW 0 eb)) h1
  have hm₁ : m₁ = s₀.mem := by rw [← ht₁, hst]
  subst hm₁
  subst hr
  by_cases h1' : (mfindG ioSch s₀.mem e (genW 0 eb)).headD 0 ≠ 0
  · simp only [inferIOE.k_io_find] at hW; rw [ite_eq_left h1'] at hW; cases hW
  have hmiss := (hS.core.io.findE hS.core.eb1 e he hne).2 (by simpa using h1')
  simp only [inferIOE.k_io_find] at hW; rw [ite_eq_right h1'] at hW
  cases h2 : callE p n "infer_body_io" [mode, vis, d, e] s₀.mem with
  | error e2 =>
    rw [h2, inferIOE.k_infer_body_io.none] at hW; cases hW
    have hcl := CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩) (hb F' _ a₀ dn vis fe MM eb mode d e
      (by omega) (by omega) ⟨hS, hs.mode4, hs.eb_mode⟩ he hk hkE) h2
    exact ErrClaim.of_run_eq' (fun ce h => knot_inferIO_missE _ fe F' d.toNat _ a₀ hmiss ce h) hcl
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2, inferIOE.k_infer_body_io.arm1] at hW
  cases h3 : callE p n "io_find" [e, genW 0 eb] m₂ with
  | error e3 =>
    rw [h3, inferIOE.k_io_find_2.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "io_find" (by simp)) h3
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [h3] at hW; simp only [inferIOE.k_io_find_2] at hW
  cases h4 : callE p n "io_put" [e, genW 0 eb, r₂.headD 0, r₃.headD 0, r₃.tail.headD 0] m₃ with
  | error e4 =>
    rw [h4, inferIOE.k_io_put.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "io_put" (by simp)) h4
  | ok q => rw [h4] at hW; simp [inferIOE.k_io_put] at hW

/-! ## The goal: the knot's `infer`, `infer_io` steps, error halves -/

/-- **The knot's `infer` slot one level up, error half** (`inferSlot_step`'s): from the knot and
its error half up to `n`. -/
@[refines_part ConRon.Arena.coreKnot "infer (step, verdicts)"]
theorem inferSlot_stepE (p : Prog) (hq : InferAllProg p) (hc : InferCallees p) (hcE : InferCalleesE p)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) : InferSlotE p (n + 1) :=
  infer_refinesE p hq.knot hcE.nv n hk hkE (inferBody_refinesE p hq hc hcE n)

/-- **The knot's `inferIO` slot one level up, error half** (`inferIOSlot_step`'s). -/
@[refines_part ConRon.Arena.coreKnot "inferIO (step, verdicts)"]
theorem inferIOSlot_stepE (p : Prog) (hq : InferAllProg p) (hc : InferCallees p)
    (hcE : InferCalleesE p) (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) :
    InferIOSlotE p (n + 1) :=
  inferIO_refinesE p hq.knot hcE.nv n hk hkE (inferBodyIO_refinesE p hq hc hcE n)

/-- **Both inference slots one level up, error halves.** -/
theorem inferSlots_stepE (p : Prog) (hq : InferAllProg p) (hc : InferCallees p)
    (hcE : InferCalleesE p) :
    ∀ n, KnotUpTo p n → KnotUpToE p n → InferSlotE p (n + 1) ∧ InferIOSlotE p (n + 1) :=
  fun n hk hkE => ⟨inferSlot_stepE p hq hc hcE n hk hkE, inferIOSlot_stepE p hq hc hcE n hk hkE⟩

end L.Arena
