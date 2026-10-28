import ConAgua.Arena.IndT.Install6

/-!
# The error claim of `check_abs_ctor_sorts_all` (lane `verdicts-b`, helper `ia2`, fork `top`)

`iaaW_simC`'s proof (`Install6.lean`) on the model `iaaE`: `check_abs_ctor_sorts`' error half from
its run (`iac_ref`, under `check_struct_field_sorts_i`'s claim `CheckStructFieldSortsIE`); the
aborts are of class `0`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (eCsf : CheckStructFieldSortsIE p)

include hq henv hOpf hLC hLT hnv eCsf in
/-- **`check_abs_ctor_sorts_all`'s error claim** (`iaaW_simC`'s hypotheses; induction on the
fuel). -/
theorem iaaE_claim (hApd : ApdF p) (hP : AbsProg p) (ctx isP : Word) (c : NestCtx) (b : Bool)
    (hb : (isP != 0) = b) (hhi : c.hiAt 0 < 2 ^ 64) {ctxP : ConLeche.NestCtx} (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (so sl oo ol : Word) (css : List (List (IConstantVal × Nat)))
      (oss : List (List (List NestFieldKind × EIdx))) (cssP : List (List (ConLeche.ConstantVal × Nat)))
      (ossP : List (List (List ConLeche.NestFieldKind × ConLeche.Expr))),
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decCtx m ctx.toNat) m c →
    PSlR0 decCNS css so sl m → PSlR0 decKES oss oo ol m →
    ConRon.Bridge.Inductives.dCtx a.store ctxP.find? c = some ctxP →
    css.mapM (ConRon.Bridge.Inductives.dCtors a.store) = some cssP →
    ConRon.Bridge.Inductives.dOutss a.store oss = some ossP →
    (∀ os ∈ ossP, ∀ o ∈ os, ConLeche.Expr.WScoped (ctxP.hiAt 0) o.2) →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    ∀ e, iaaE p n m vis ctx isP so sl oo ol = .error e →
      ErrClaim (ConRon.Arena.checkAbsCtorSortsAll V fe c b css oss) a e := by
  induction n with
  | zero => intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he; rw [iaaE.eq_1] at he; cases he; exact ErrClaim.of_cls0 rfl
  | succ n ih =>
  intro m a so sl oo ol css oss cssP ossP hC hA hc hcss hoss hctxP hcssP hossP hws hfe e he
  have hS := hC.stage
  by_cases hsl : sl = 0
  · rw [iaaE.arm1 p n m vis ctx isP so sl oo ol hsl] at he; cases he
  by_cases hol : ol = 0
  · rw [iaaE.arm2 p n m vis ctx isP so sl oo ol hsl hol] at he; cases he
  obtain ⟨qc, cs, css', rfl, hwc, hqcb, hdc, hcss'⟩ := partsPSl_cons (hcss.pslr hsl) hsl
  obtain ⟨qo, os, oss', rfl, hwo, hqob, hdo, hoss'⟩ := partsPSl_cons (hoss.pslr hol) hol
  obtain ⟨csP, cssP', rfl, hcP, hcssP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcssP
  simp only [ConRon.Bridge.Inductives.dOutss] at hossP
  obtain ⟨osP, ossP', rfl, hoP, hossP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hossP
  have hqc' : (UInt64.ofNat qc : Word).toNat = qc := UInt64.toNat_ofNat_of_lt' hqcb
  have hqo' : (UInt64.ofNat qo : Word).toNat = qo := UInt64.toNat_ofNat_of_lt' hqob
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨co, cl, hco, hcl, hcd, hcb⟩ := partsAt decCN_mono (show decAt (truncM m)
    (decPL (truncM m) (decCN (truncM m))) qc = some cs from hdc)
  obtain ⟨oo2, ol2, hoo, hol2, hod, hob⟩ := partsAt decKE_mono (show decAt (truncM m)
    (decPL (truncM m) (decKE (truncM m))) qo = some os from hdo)
  have l1 := partsIwLt hcl; have l2 := partsIwLt hol2
  obtain ⟨w1, -, -⟩ := partsIwRd hco (w := UInt64.ofNat qc) hqc'
  obtain ⟨w2, -, -⟩ := partsIwRd hcl (w := UInt64.ofNat qc + 1) (by rw [UInt64.toNat_add, hqc']; simp; omega)
  obtain ⟨w3, -, -⟩ := partsIwRd hoo (w := UInt64.ofNat qo) hqo'
  obtain ⟨w4, -, -⟩ := partsIwRd hol2 (w := UInt64.ofNat qo + 1) (by rw [UInt64.toNat_add, hqo']; simp; omega)
  rw [UInt64.ofNat_toNat] at w1 w2 w3 w4
  rw [iaaE.arm3 p n m vis ctx isP so sl oo ol hsl hol, hwc, hwo, w1, w2, w3, w4] at he
  simp only [ConRon.Arena.checkAbsCtorSortsAll]
  cases h1 : callE p n "check_abs_ctor_sorts" [vis, ctx, isP, co, cl, oo2, ol2] m with
  | error e1 =>
    rw [h1, iaaE.k_check_abs_ctor_sorts.none] at he; cases he
    exact ErrClaim.bind_left (RefE.run_err (iacE_spec p hP.one hP.abs n ⟨m, Locals.init []⟩ vis ctx isP co cl oo2 ol2)
      hnv eCsf (iac_ref hq henv hOpf hLC hLT hApd hP ctx isP c b hb hhi n (by omega) m a co cl oo2 ol2 cs os csP osP
        hC hA hc ⟨hcd, hcb⟩ ⟨hod, hob⟩ hctxP hcP hoP (hws osP List.mem_cons_self) hfe) h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨s', rfl, -, u1, a1, hrun1, hC1, hg1, hA1, c1⟩ := RefE.run_ok
    (iacE_spec p hP.one hP.abs n ⟨m, Locals.init []⟩ vis ctx isP co cl oo2 ol2)
    (iac_ref hq henv hOpf hLC hLT hApd hP ctx isP c b hb hhi n (by omega) m a co cl oo2 ol2 cs os csP osP hC hA hc
      ⟨hcd, hcb⟩ ⟨hod, hob⟩ hctxP hcP hoP (hws osP List.mem_cons_self) hfe) h1
  refine ErrClaim.bind_right hrun1 ?_
  rw [h1, iaaE.k_check_abs_ctor_sorts.arm1] at he
  cases hx : iaaE p n s'.mem vis ctx isP (so + 1) (sl - 1) (oo + 1) (ol - 1) with
  | ok q => obtain ⟨r0, m0⟩ := q; rw [hx, iaaE.k_check_abs_ctor_sorts_all.arm1] at he; cases he
  | error ε =>
  rw [hx, iaaE.k_check_abs_ctor_sorts_all.none] at he; cases he
  exact ih (by omega) s'.mem a1 (so + 1) (sl - 1) (oo + 1) (ol - 1) css' oss' cssP' ossP' hC1 hA1
    (hc.grow (decCtx_mono _) hg1)
    (PSlR0.grow decCNS_mono (⟨hcss'.1, Or.inr hcss'.2⟩ : PSlR0 decCNS css' (so + 1) (sl - 1) m) hg1)
    (PSlR0.grow (fun q => OMono.decAt (fun o l => OMono.decPL decKE_mono o l) q)
      (⟨hoss'.1, Or.inr hoss'.2⟩ : PSlR0 decKES oss' (oo + 1) (ol - 1) m) hg1)
    (ConRon.Bridge.Inductives.dCtx_ext _ c1.ext _ _ hctxP)
    (ConRon.Bridge.Inductives.dCtors_ext.list c1.ext _ _ hcssP')
    (ConRon.Bridge.Inductives.dOutss_ext c1.ext _ _ hossP')
    (fun y hy => hws y (List.mem_cons_of_mem _ hy)) (ConRon.Bridge.denoteFEnv_mono c1.ext hfe) _ hx

end sims

end L.Ind
