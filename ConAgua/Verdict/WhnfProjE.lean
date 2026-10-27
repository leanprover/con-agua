import ConAgua.Verdict.WhnfModels2E
import ConAgua.Verdict.WhnfSlotE
import ConAgua.Arena.Checker

/-!
# The `proj` arm's verdict claims (lane `verdicts-b`, helper `k2`)

`whnf_core_step_proj`, `reduce_proj_core`, `proj_lit_to_ctor` have no verdict site of their own:
their claims are the knot's slots' (`KnotUpToE`), propagated (`stepProjE_of`: `StepProjE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem whnfProjE_nv : ∀ f ∈ ["str_lit_supported", "str_lit_ctor", "find_proj",
    "reduce_proj_head"], f ∈ L.Checker.nvFns := by
  decide +kernel

theorem projLitToCtor_err_ctor (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (h : Word) (hh : HW h)
    (hg : h >>> 28 = 8) (a a' a₁ : AState) (s : String)
    (hv : a.store.view (decE h) = some (.lit (.strVal s)))
    (hsup : (strLitSupported fe).run a = .ok (true, a')) (c : EIdx)
    (hc : (strLitToConstructor s).run a' = .ok (c, a₁)) (ce : CheckError)
    (hres : (r.whnf depth c).run a₁ = .error ce) :
    (projLitToCtor r fe depth (decE h)).run a = .error ce := by
  have ht : ((decE h).tag == ETag.lit) = true := by rw [decE_lit_tag h hh]; simp [hg]
  simp [projLitToCtor, ht, StateT.run_bind, view_run _ _ _ hv, hsup, hc, hres]

/-- **`proj_lit_to_ctor`'s verdicts** are the `whnf` slot's (on a supported string literal). -/
theorem projLitToCtor_refinesE (p : Prog) (hp : WhnfCoreProg p) (hStrSup : StrLitSupportedOK p)
    (hStrCtor : StrLitCtorOK p) (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d h : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hh : HW h)
    (hsupKeep : SupKeep fe) :
    CoreSpecE p (n + 1) "proj_lit_to_ctor" [mode, vis, d, h]
      (projLitToCtor (coreKnot (decMode mode) fe id F) fe d.toNat (decE h)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (projLitToCtor_specE p hp.plit (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d h) hc (Err.code_ne_of_cls hk0)
  simp only [projLitToCtorE] at hW
  have hS := hs.rel
  by_cases htag : h >>> 28 ≠ 8
  · rw [ite_eq_left htag] at hW; cases hW
  rw [ite_eq_right htag] at hW
  have htag8 : h >>> 28 = 8 := by simpa using htag
  by_cases hsc : tierW h ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [ite_eq_left hsc] at hW; cases hW; exact absurd rfl hk0
  rw [ite_eq_right hsc] at hW
  by_cases hbd : tcnt s₀.mem LIT (tierW h) ≤ idxW h
  · rw [ite_eq_left hbd] at hW; cases hW; exact absurd rfl hk0
  rw [ite_eq_right hbd] at hW
  have hvOK : viewOK s₀.mem h LIT := ⟨hsc, by simpa using hbd⟩
  obtain ⟨hviewS, -⟩ := view_lit_kind s₀.mem a₀ hS.arena.1 h hh hvOK htag8
  by_cases hkind : tfld s₀.mem LIT (tierW h) (idxW h) 0 ≠ 1
  · rw [ite_eq_left hkind] at hW; cases hW
  rw [ite_eq_right hkind] at hW
  obtain ⟨s', hv⟩ := hviewS (by simpa using hkind)
  cases hcall1 : callE p n "str_lit_supported" [vis] s₀.mem with
  | error e1 =>
    rw [hcall1, projLitToCtorE.k_str_lit_supported.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfProjE_nv "str_lit_supported" (by simp)) hcall1
  | ok q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [hcall1] at hW
  simp only [projLitToCtorE.k_str_lit_supported] at hW
  obtain ⟨hok1, ⟨M₁, hS₁, -, -⟩, hres1, -⟩ :=
    CoreSpec.of_callW (hStrSup n s₀ a₀ dn vis fe MM eb hS) (callW_of_callE hcall1)
  by_cases hsup0 : r₁.headD 0 = 0
  · rw [ite_eq_left hsup0] at hW; cases hW
  rw [ite_eq_right hsup0] at hW
  have hsupT : (strLitSupported fe).run a₀ = .ok (true, AM.st (strLitSupported fe) a₀) := by
    have hrr := AM.run_of_ok _ _ hok1
    rw [hres1] at hrr
    have hdb : decBool r₁ = true := by
      show (r₁.headD 0 != 0) = true
      rw [bne_iff_ne]
      exact hsup0
    rwa [hdb] at hrr
  let a₁ : AState := AM.st (strLitSupported fe) a₀
  have hv₁ : a₁.store.view (decE h) = some (.lit (.strVal s')) := hsupKeep a₀ _ _ hv
  cases hcall2 : callE p n "str_lit_ctor" [h] m₁ with
  | error e2 =>
    rw [hcall2, projLitToCtorE.k_str_lit_ctor.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfProjE_nv "str_lit_ctor" (by simp)) hcall2
  | ok q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [hcall2] at hW
  simp only [projLitToCtorE.k_str_lit_ctor] at hW
  obtain ⟨hok2, ⟨M₂, hS₂, -, -⟩, hres2, hrw2⟩ :=
    CoreSpec.of_callW (hStrCtor n ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb h s' hS₁ hh hv₁)
      (callW_of_callE hcall2)
  have hc2run := AM.run_of_ok _ _ hok2
  rw [hres2] at hc2run
  have herr := err_of_k (k := projLitToCtorE.k_whnf p) (by intro q e; simp [projLitToCtorE.k_whnf])
    (fun _ => rfl) hW
  exact ErrClaim.of_run_err (fun ce h' => projLitToCtor_err_ctor _ fe d.toNat h hh htag8 a₀ a₁ _ s' hv
      hsupT _ hc2run ce h')
    (CoreSpecE.of_callE ((hkE n (Nat.le_refl n)).whnf F ⟨m₂, Locals.init []⟩
      (AM.st (strLitToConstructor s') a₁) dn vis fe M₂ eb mode d (r₂.headD 0) hF hn
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ hrw2) herr)

theorem reduceProjCore_err (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (sn : NIdx) (i : Nat) (c : EIdx) (a : AState) (ce : CheckError)
    (h : (projLitToCtor r fe depth c).run a = .error ce) :
    (reduceProjCore mode r fe depth sn i c).run a = .error ce := by
  simp only [reduceProjCore, StateT.run_bind, h]; rfl

/-- **`reduce_proj_core`'s verdicts** are `proj_lit_to_ctor`'s. -/
theorem reduceProjCore_refinesE (p : Prog) (hp : WhnfCoreProg p) (hStrSup : StrLitSupportedOK p)
    (hStrCtor : StrLitCtorOK p) (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d sn i c : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hc' : HW c)
    (hsup : SupKeep fe) :
    CoreSpecE p (n + 1) "reduce_proj_core" [mode, vis, d, sn, i, c]
      (reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE c)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (reduceProjCore_specE p hp.rproj (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d sn i c) hc (Err.code_ne_of_cls hk0)
  simp only [reduceProjCoreE] at hW
  cases hc1 : callE p n "proj_lit_to_ctor" [mode, vis, d, c] s₀.mem with
  | error e1 =>
    rw [hc1, reduceProjCoreE.k_proj_lit_to_ctor.none] at hW; cases hW
    refine ErrClaim.of_run_err (fun ce h' => reduceProjCore_err _ _ _ _ _ _ _ a₀ ce h') ?_
    cases n with
    | zero => exact ErrClaim.of_callE_zeroW hc1
    | succ N =>
    exact CoreSpecE.of_callE (projLitToCtor_refinesE p hp hStrSup hStrCtor hnv N
      (hkE.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe MM eb mode d c hs hc' hsup) hc1
  | ok q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [hc1] at hW
  simp only [reduceProjCoreE.k_proj_lit_to_ctor] at hW
  cases hc2 : callE p n "find_proj" [vis, sn, i] m₁ with
  | error e2 =>
    rw [hc2, reduceProjCoreE.k_find_proj.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfProjE_nv "find_proj" (by simp)) hc2
  | ok q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [hc2] at hW
  simp only [reduceProjCoreE.k_find_proj] at hW
  split at hW
  · cases hW
  exact ErrClaim.of_callE_nv hnv (whnfProjE_nv "reduce_proj_head" (by simp))
    (err_of_k (by intro q e; simp [reduceProjCoreE.k_reduce_proj_head]) (fun _ => rfl) hW)

theorem stepProj_err1 (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool)
    (depth : Nat) (e : EIdx) (sn : NIdx) (i : Nat) (pe : EIdx) (a : AState) (ce : CheckError)
    (h : (if cheap then r.whnfCore true depth pe else r.whnf depth pe).run a = .error ce) :
    (whnfCoreStepProj mode r fe cheap depth e sn i pe).run a = .error ce := by
  cases cheap <;> simp_all [whnfCoreStepProj, StateT.run_bind] <;> rfl

theorem stepProj_err2 (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool)
    (depth : Nat) (e : EIdx) (sn : NIdx) (i : Nat) (pe : EIdx) (a a₁ : AState) (c : EIdx)
    (h₁ : (if cheap then r.whnfCore true depth pe else r.whnf depth pe).run a = .ok (c, a₁))
    (ce : CheckError) (h₂ : (reduceProjCore mode r fe depth sn i c).run a₁ = .error ce) :
    (whnfCoreStepProj mode r fe cheap depth e sn i pe).run a = .error ce := by
  cases cheap <;> simp_all [whnfCoreStepProj, StateT.run_bind] <;> rfl

/-- **`whnf_core_step_proj`'s verdicts** are the scrutinee's head normalization's (a slot's) and
`reduce_proj_core`'s. -/
theorem stepProj_refinesE (p : Prog) (hp : WhnfCoreProg p) (hStrSup : StrLitSupportedOK p)
    (hStrCtor : StrLitCtorOK p) (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode cheap d e sn i pe : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hpe : HW pe)
    (hsup : SupKeep fe) :
    CoreSpecE p (n + 1) "whnf_core_step_proj" [mode, cheap, vis, d, e, sn, i, pe]
      (whnfCoreStepProj (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e) (decI sn) i.toNat (decE pe)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (coreStepProj_specE p hp.sproj (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode cheap vis d e sn i pe) hc (Err.code_ne_of_cls hk0)
  simp only [coreStepProjE] at hW
  -- the scrutinee's normalization, a slot
  have key : ∀ (c : Except Err (List Word × Mem)),
      c = (if cheap ≠ 0 then callE p n "whnf_core" [mode, 1, vis, d, pe] s₀.mem
        else callE p n "whnf" [mode, vis, d, pe] s₀.mem) →
      (∀ er', c = .error er' → ErrClaim (if (cheap != 0) = true then
          (coreKnot (decMode mode) fe id F).whnfCore true d.toNat (decE pe)
          else (coreKnot (decMode mode) fe id F).whnf d.toNat (decE pe)) a₀ er') ∧
      (∀ r₁ m₁, c = .ok (r₁, m₁) → ∃ M₁ a₁, CoreS dn m₁ a₁ vis fe M₁ eb ∧ HW (r₁.headD 0) ∧
        (if (cheap != 0) = true then (coreKnot (decMode mode) fe id F).whnfCore true d.toNat (decE pe)
          else (coreKnot (decMode mode) fe id F).whnf d.toNat (decE pe)).run a₀ =
          .ok (decE (r₁.headD 0), a₁)) := by
    intro c hcdef
    by_cases hch : cheap = 0
    · rw [ite_eq_right (by simpa using hch)] at hcdef
      have hb : (cheap != 0) = false := by simp [hch]
      rw [hb]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨fun er' he => ?_, fun r₁ m₁ he => ?_⟩
      · subst hcdef
        exact CoreSpecE.of_callE ((hkE n (Nat.le_refl n)).whnf F s₀ a₀ dn vis fe MM eb mode d pe hF hn
          hs hpe) he
      · subst hcdef
        obtain ⟨hok, ⟨M₁, hS₁, -, -⟩, hres, hrw⟩ := CoreSpec.of_callW
          ((hk n (Nat.le_refl n)).whnf F s₀ a₀ dn vis fe MM eb mode d pe hF hn hs hpe) (callW_of_callE he)
        refine ⟨M₁, _, hS₁, hrw, ?_⟩
        have := AM.run_of_ok _ _ hok
        rw [hres] at this; exact this
    · rw [ite_eq_left hch] at hcdef
      have hb : (cheap != 0) = true := by simpa using hch
      rw [hb]
      simp only [↓reduceIte]
      refine ⟨fun er' he => ?_, fun r₁ m₁ he => ?_⟩
      · subst hcdef
        exact CoreSpecE.of_callE ((hkE n (Nat.le_refl n)).whnfCore F s₀ a₀ dn vis fe MM eb mode 1 d pe hF
          hn hs hpe) he
      · subst hcdef
        obtain ⟨hok, ⟨M₁, hS₁, -, -⟩, hres, hrw⟩ := CoreSpec.of_callW
          ((hk n (Nat.le_refl n)).whnfCore F s₀ a₀ dn vis fe MM eb mode 1 d pe hF hn hs hpe)
          (callW_of_callE he)
        refine ⟨M₁, _, hS₁, hrw, ?_⟩
        have := AM.run_of_ok _ _ hok
        rw [hres] at this; exact this
  have hW' : coreStepProjE.k_whnf_core p n mode vis d e sn i (if cheap ≠ 0 then
      callE p n "whnf_core" [mode, 1, vis, d, pe] s₀.mem else callE p n "whnf" [mode, vis, d, pe] s₀.mem) =
      .error er := by
    by_cases hch : cheap ≠ 0
    · rw [ite_eq_left hch] at hW ⊢; exact hW
    · rw [ite_eq_right hch] at hW ⊢; exact hW
  obtain ⟨kE, kO⟩ := key _ rfl
  cases hc1 : (if cheap ≠ 0 then callE p n "whnf_core" [mode, 1, vis, d, pe] s₀.mem
    else callE p n "whnf" [mode, vis, d, pe] s₀.mem) with
  | error e1 =>
    rw [hc1, coreStepProjE.k_whnf_core.none] at hW'; cases hW'
    exact ErrClaim.of_run_err (fun ce h' => stepProj_err1 _ _ _ _ _ _ _ _ _ a₀ ce h') (kE _ hc1)
  | ok q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [hc1] at hW'
  simp only [coreStepProjE.k_whnf_core, coreStepProjE.j1] at hW'
  obtain ⟨M₁, a₁, hS₁, hr₁, hrun₁⟩ := kO r₁ m₁ hc1
  have herr := err_of_k (k := coreStepProjE.k_reduce_proj_core p e)
    (by intro q e'; simp only [coreStepProjE.k_reduce_proj_core]; split <;> simp) (fun _ => rfl) hW'
  refine ErrClaim.of_run_err (fun ce h' => stepProj_err2 _ _ _ _ _ _ _ _ _ a₀ a₁ _ hrun₁ ce h') ?_
  cases n with
  | zero => exact ErrClaim.of_callE_zeroW herr
  | succ N =>
  exact CoreSpecE.of_callE (reduceProjCore_refinesE p hp hStrSup hStrCtor hnv N (hk.mono (by omega))
    (hkE.mono (by omega)) F (by omega) (by omega) ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode d sn i
    (r₁.headD 0) ⟨hS₁, hs.mode4, hs.eb_mode⟩ hr₁ hsup) herr

/-- **`StepProjE`**: the `proj` arm's error claim, from the ok knot's bundles. -/
theorem stepProjE_of (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p)
    (hsup : ∀ fe : IFEnv, SupKeep fe) (hnv : closedNV p L.Checker.nvFns = true) : StepProjE p :=
  fun N hk hkE F s₀ a₀ dn vis fe MM eb mode cheap d e sn i pe hF hn hs _ _ hpe =>
    stepProj_refinesE p hp hwc.strLitSupported hwc.strLitCtor hnv N hk hkE F hF hn s₀ a₀ dn vis fe MM
      eb mode cheap d e sn i pe hs hpe (hsup fe)

end L.Arena
