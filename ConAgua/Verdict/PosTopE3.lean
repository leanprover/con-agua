import ConAgua.Checker.NoVerdictFns
import ConAgua.Verdict.IndBE
import ConAgua.Verdict.PosTopE1
import ConAgua.Arena.IndT.Install6

/-!
# The error claims of `check_abs_ctor_sorts_one`, `check_abs_ctor_sorts`,
`check_abs_ctor_sorts_all` (lane `verdicts-b`, helper `ia2`, fork `top`)

`iaoW_simC`'s, `iacW_simC`'s, `iaaW_simC`'s proofs (`Install6.lean`) on the models `iaoE`, `iacE`,
`iaaE`: `check_struct_field_sorts_i`'s claim (`CheckStructFieldSortsIE`) at the leaf; the other
callees claim nothing (`nvFns`); the aborts are of class `0`.
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
/-- **`check_abs_ctor_sorts_one`'s error claim** (`iaoW_simC`'s hypotheses). -/
theorem iaoE_claim (hsum : SumProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {ctx isP nF tyN hi : Word} {c : NestCtx} {b : Bool}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hc : DecB (fun m => decCtx m ctx.toNat) m c)
    (hty : H tyN) (hhi : hi.toNat = c.hiAt 0) (hb : (isP != 0) = b)
    {tyNP : ConLeche.Expr} {sortP : ConLeche.Level}
    (htyP : denoteE a.store (decI tyN) = some tyNP) (hW : ConLeche.Expr.WScoped (c.hiAt 0) tyNP)
    (hsP : denoteL a.store.ls c.sort = some sortP) :
    ∀ e, iaoE p (n + 1) m vis ctx isP nF tyN hi = .error e →
      ErrClaim (absOneAM fe c b nF.toNat (decI tyN)) a e := by
  intro e he
  have hS := hC.stage
  obtain ⟨hs32, hse⟩ := installCtxWord9 hc hS.2.2.2.1
  by_cases hov : hi + nF < hi
  · rw [iaoE.abort1 p n m vis ctx isP nF tyN hi hov] at he; cases he; exact ErrClaim.of_cls0 rfl
  rw [iaoE.arm1 p n m vis ctx isP nF tyN hi hov] at he
  unfold absOneAM
  cases h1 : callE p n "open_pis_at_fvars_f" [nF, tyN, hi] m with
  | error e1 =>
    rw [h1, iaoE.k_open_pis_at_fvars_f.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q =>
  obtain ⟨r1, m1⟩ := q
  have hsim := opfSimRA (p := p) (n := n) (k := nF) (i := hi) hOpf hty hS hA
  rw [hhi] at hsim
  obtain ⟨x1, a1, hrun1, ⟨⟨hS1, hg1, hd1⟩, hr1⟩, hA1⟩ := hsim r1 m1 (callW_of_callE h1)
  refine ErrClaim.bind_right hrun1 ?_
  obtain ⟨p1, ho1⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC.check.state htyP hr1
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
  by_cases h0 : r1.headD 0 = 0
  · rw [h1, iaoE.k_open_pis_at_fvars_f.abort1 p n vis isP nF hi _ r1 m1 h0] at he; cases he
    exact ErrClaim.of_cls0 rfl
  rw [h1, iaoE.k_open_pis_at_fvars_f.arm1 p n vis isP nF hi _ r1 m1 h0] at he
  cases x1 with
  | none => exact absurd (show r1.headD 0 = 0 from hd1) h0
  | some fb =>
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨xsP, xP, hxq, hxs, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho1
  obtain ⟨h1', hfv, -⟩ := hd1
  obtain ⟨hfd, hfb⟩ := hfv
  have g1 : r1.getD 1 0 = r1.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r1.getD (1 + 1) 0 = r1.tail.tail.headD 0 := by
    rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  show ErrClaim (checkStructFieldSortsI V fe b false c.sort (c.hiAt 0) fvs [] nF.toNat >>= fun _ => pure ()) a1 e
  have hfvsc := ConRon.Bridge.Inductives.openers_typeD_WScoped hxq hW
  cases h2 : callE p n "check_struct_field_sorts_i" [vis, isP, 0, rdW (m.arr64 IW) (ctx + 9), hi,
      r1.tail.headD 0, r1.tail.tail.headD 0, 0, 0, nF] m1 with
  | ok q2 => obtain ⟨r2, m2⟩ := q2; rw [h2, iaoE.k_check_struct_field_sorts_i.arm1] at he; cases he
  | error e2 =>
  rw [h2, iaoE.k_check_struct_field_sorts_i.none] at he; cases he
  refine ErrClaim.bind_left ?_
  have h := eCsf hq henv hLC hLT hsum.hg hsum.hpw hsum.het hsum.hcn hsum.hfsb hsum.hcfg hsum.ha hsum.hcfs
    hsum.ad.ftd ⟨m1, Locals.init []⟩ a1 isP 0 (rdW (m.arr64 IW) (ctx + 9)) hi _ _ 0 0 nF fvs [] hC1 hA1 hfd hfb
    (by simp [decHL, hslice?]) (by simp) hs32
    (by rw [hse]; exact ConRon.Bridge.denoteL_ext hsP p1.ext)
    (by rw [← partsAddNoOv hov]; exact UInt64.toNat_lt _) hxs
    (fun i _ x hx => by rw [hhi]; exact hfvsc i x hx) n hn _ h2
  rw [hse, hhi, hb, show ((0 : Word) != 0) = false from rfl] at h
  exact h

include hq henv hOpf hLC hLT hnv eCsf in
/-- **`check_abs_ctor_sorts`'s error claim** (`iacW_simC`'s hypotheses; induction on the fuel). -/
theorem iacE_claim (hApd : ApdF p) (hP : AbsProg p) (ctx isP : Word) (c : NestCtx) (b : Bool)
    (hb : (isP != 0) = b) (hhi : c.hiAt 0 < 2 ^ 64) {ctxP : ConLeche.NestCtx} (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (co cl oo ol : Word) (cs : List (IConstantVal × Nat))
      (os : List (List NestFieldKind × EIdx)) (csP : List (ConLeche.ConstantVal × Nat))
      (osP : List (List ConLeche.NestFieldKind × ConLeche.Expr)),
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decCtx m ctx.toNat) m c →
    PSlR0 decCN cs co cl m → PSlR0 decKE os oo ol m →
    ConRon.Bridge.Inductives.dCtx a.store ctxP.find? c = some ctxP →
    ConRon.Bridge.Inductives.dCtors a.store cs = some csP →
    os.mapM (ConRon.Bridge.Inductives.dOut a.store) = some osP →
    (∀ o ∈ osP, ConLeche.Expr.WScoped (ctxP.hiAt 0) o.2) →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    ∀ e, iacE p n m vis ctx isP co cl oo ol = .error e →
      ErrClaim (ConRon.Arena.checkAbsCtorSorts V fe c b cs os) a e := by
  induction n with
  | zero => intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he; rw [iacE.eq_1] at he; cases he; exact ErrClaim.of_cls0 rfl
  | succ n ih =>
  intro m a co cl oo ol cs os csP osP hC hA hc hcs hos hctxP hcsP hosP hws hfe e he
  have hS := hC.stage
  by_cases hcl : cl = 0
  · rw [iacE.arm1 p n m vis ctx isP co cl oo ol hcl] at he; cases he
  by_cases hol : ol = 0
  · rw [iacE.arm2 p n m vis ctx isP co cl oo ol hcl hol] at he; cases he
  obtain ⟨qc, ⟨cv, nF⟩, cs', rfl, hwc, hqcb, hdc, hcs'⟩ := partsPSl_cons (hcs.pslr hcl) hcl
  obtain ⟨qo, ⟨ks, e0⟩, os', rfl, hwo, hqob, hdo, hos'⟩ := partsPSl_cons (hos.pslr hol) hol
  obtain ⟨cP, csP', rfl, hcP, hcsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcsP
  obtain ⟨oP, osP', rfl, hoP, hosP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hosP
  obtain ⟨tyNP, htyNP, rfl⟩ : ∃ tyN, denoteE a.store e0 = some tyN ∧ oP = (ks.map ConRon.Bridge.Inductives.kindOf, tyN) := by
    simp only [ConRon.Bridge.Inductives.dOut, Option.map_eq_some_iff] at hoP
    obtain ⟨x, hx, rfl⟩ := hoP
    exact ⟨x, hx, rfl⟩
  have hWP : ConLeche.Expr.WScoped (ctxP.hiAt 0) tyNP := hws _ List.mem_cons_self
  obtain ⟨namesP, lpsP, paramsP, sortP, hceq, hnm, hlp, -, hsort, -⟩ := ConRon.Bridge.Inductives.dCtx_inv hctxP
  have hhiP : c.hiAt 0 = ctxP.hiAt 0 := by
    rw [hceq]
    simp [ConRon.Arena.NestCtx.hiAt, ConLeche.NestCtx.hiAt, ConRon.Bridge.denoteNList_length _ _ hnm]
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hqc' : (UInt64.ofNat qc : Word).toNat = qc := UInt64.toNat_ofNat_of_lt' hqcb
  have hqo' : (UInt64.ofNat qo : Word).toNat = qo := UInt64.toNat_ofNat_of_lt' hqob
  have hcT : decCtx (truncM m) ctx.toNat = some c := hc
  obtain ⟨-, hlps, hnP, -, -, -, -⟩ := decCtx_some hcT
  obtain ⟨lo, ll, hlo, hll, hlpsd⟩ := decAt_some hlps
  have hlolt := partsIwLt hll
  obtain ⟨hwlo, hlob, -⟩ := partsIwRd hlo (w := ctx + 2) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨hwll, hllb, -⟩ := partsIwRd hll (w := ctx + 3) (by rw [UInt64.toNat_add]; simp; omega)
  have hdoT : decKE (truncM m) qo = some (ks, e0) := hdo
  simp only [decKE, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hdoT
  obtain ⟨-, -, ee, hee, -, rfl⟩ := hdoT
  obtain ⟨heelt, hee'⟩ := rec2IwH_trunc hee
  obtain ⟨ew, hew, hew32, hewe⟩ := iwH_rdW_at (w := UInt64.ofNat qo) (k := 2) (by rw [hqo']; exact hee')
    hS.2.2.2.1
  rw [show (UInt64.ofNat 2 : Word) = 2 from rfl] at hew
  rw [iacE.arm3 p n m vis ctx isP co cl oo ol hcl hol, hwc, hwo, hwlo, hwll, hew] at he
  simp only [ConRon.Arena.checkAbsCtorSorts]
  have hlpsm : decHL m (UInt64.ofNat lo : Word).toNat (UInt64.ofNat ll : Word).toNat = some c.lps := by
    rw [UInt64.toNat_ofNat_of_lt' hlob, UInt64.toNat_ofNat_of_lt' hllb]
    exact DecB.get (f := fun m => (decHL m lo ll : Option (List NIdx))) (OMono.decHL _ _) hlpsd
  have hl' : Frontend.denoteNList a.store.ns c.lps = some ctxP.lps := by rw [hceq]; exact hlp
  have hsort' : denoteL a.store.ls c.sort = some ctxP.sort := by rw [hceq]; exact hsort
  cases h1 : callE p n "all_level_params_defined" [UInt64.ofNat lo, UInt64.ofNat ll, ew] m with
  | error e1 =>
    rw [h1, iacE.k_all_level_params_defined.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  have h := apdCall_simR hApd n (UInt64.ofNat lo) (UInt64.ofNat ll) ew hew32 c.lps hS hA
    hC.check.state hlpsm ⟨_, denoteNList_mapM hl'⟩
  rw [hewe] at h
  obtain ⟨ok, a1, hr1, hS1, hg1, ⟨hok1, -⟩, hA1, -⟩ := h r1 m1 (callW_of_callE h1)
  obtain ⟨h1s, h1c, h1p, -⟩ := ConRon.Bridge.allLevelParamsDefined_run hC.check.state hl' htyNP hr1
  have c1 := ConRon.Bridge.Inductives.BI.coreStep_of_store hC.check h1s h1c h1p
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_check hS1 hA1 c1.ok c1.ext
  refine ErrClaim.bind_right hr1 ?_
  by_cases h0 : r1.headD 0 = 0
  · rw [h1, iacE.k_all_level_params_defined.abort1 p n vis ctx isP co cl oo ol _ _ r1 m1 h0] at he; cases he
    exact ErrClaim.of_cls0 rfl
  have hokt : ok = true := by rw [← hok1]; simp only [bne_iff_ne, ne_eq, h0, not_false_eq_true]
  subst hokt
  rw [h1, iacE.k_all_level_params_defined.arm1 p n vis ctx isP co cl oo ol _ _ r1 m1 h0] at he
  have hc1 : decCtx m1 ctx.toNat = some c := hc.stab (decCtx_mono _) m1 hg1
  have hnPlt := partsIwLt hnP
  cases h2 : callE p n "nest_ctx_hi_at" [ctx, 0] m1 with
  | error e2 =>
    rw [h2, iacE.k_nest_ctx_hi_at.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, hpost2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (nestCtxHiAt_refines p hP.hiAt n _ ctx 0 c hc1 (by omega) (by omega)) (callW_of_callE h2)
  obtain ⟨rfl, hr2⟩ := hpost2
  simp only at hs2; subst hs2
  rw [h2, iacE.k_nest_ctx_hi_at.arm1, hr2, show (UInt64.toNat 0 : Nat) = 0 from rfl] at he
  have hdcT : decCN (truncM m) qc = some (cv, nF) := hdc
  obtain ⟨-, hnF⟩ := decCN_some hdcT
  have hnFlt := partsIwLt hnF
  obtain ⟨hwnF, hnFb, -⟩ := partsIwRd hnF (w := UInt64.ofNat qc + 1) (by rw [UInt64.toNat_add, hqc']; simp; omega)
  have hwnF1 : rdW (m1.arr64 IW) (UInt64.ofNat qc + 1) = UInt64.ofNat nF := by
    rw [← hwnF]; simp only [rdW]; rw [show (UInt64.ofNat qc + 1 : Word).toNat = qc + 1 by
      rw [UInt64.toNat_add, hqc']; simp; omega, hg1.2.2.1 _ hnFlt]
  have hwe1 : rdW (m1.arr64 IW) (UInt64.ofNat qo + 2) = ew := by
    rw [← hew]; simp only [rdW]; rw [show (UInt64.ofNat qo + 2 : Word).toNat = qo + 2 by
      rw [UInt64.toNat_add, hqo']; simp; omega, hg1.2.2.1 _ heelt]
  rw [hwnF1, hwe1] at he
  refine ErrClaim.congr (T' := absOneAM fe c b nF ee >>= fun _ => ConRon.Arena.checkAbsCtorSorts V fe c b cs' os')
    (by simp only [absOneAM, bind_assoc, pure_bind]; rfl) ?_
  have hhiw : (UInt64.ofNat (c.hiAt 0) : Word).toNat = c.hiAt 0 := UInt64.toNat_ofNat_of_lt' hhi
  have htyP1 : denoteE a1.store (decI ew) = some tyNP := by
    rw [hewe]; exact ConRon.Bridge.denote_ext htyNP c1.ext
  cases h3 : callE p n "check_abs_ctor_sorts_one"
      [vis, ctx, isP, UInt64.ofNat nF, ew, UInt64.ofNat (c.hiAt 0)] m1 with
  | error e3 =>
    rw [h3, iacE.k_check_abs_ctor_sorts_one.none] at he; cases he
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    have hW3 := triple_of_callE_err (iaoE_spec p hP.one n ⟨m1, Locals.init []⟩ vis ctx isP (UInt64.ofNat nF) ew
      (UInt64.ofNat (c.hiAt 0))) h3 (Err.code_ne_of_cls hk0)
    simp only at hW3
    rcases n with _ | k
    · rw [iaoE.eq_1] at hW3; cases hW3; exact absurd rfl hk0
    refine ErrClaim.bind_left ?_
    have := iaoE_claim hq henv hOpf hLC hLT hnv eCsf hP.sum k (by omega) hC1 hA1 (hc.grow (decCtx_mono _) hg1)
      hew32 hhiw hb htyP1 (by rw [hhiP]; exact hWP) (ConRon.Bridge.denoteL_ext hsort' c1.ext) _ hW3
    rw [UInt64.toNat_ofNat_of_lt' hnFb, hewe] at this
    exact this
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rcases n with _ | k
  · obtain ⟨z, hz, -⟩ := callE_zero p "check_abs_ctor_sorts_one"
      [vis, ctx, isP, UInt64.ofNat nF, ew, UInt64.ofNat (c.hiAt 0)] m1
    rw [hz] at h3; cases h3
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (iao_spec p hP.one k _ vis ctx isP (UInt64.ofNat nF) ew (UInt64.ofNat (c.hiAt 0))) (callW_of_callE h3)
  have hsim := iaoW_simC (p := p) hq henv hOpf hLC hLT hP.sum k (by omega) hC1 hA1 (hc.grow (decCtx_mono _) hg1) hew32
    hhiw hb htyP1 (by rw [hhiP]; exact hWP) (ConRon.Bridge.denoteL_ext hsort' c1.ext)
    (ConRon.Bridge.denoteFEnv_mono c1.ext hfe) r3 s'.mem hW
  rw [UInt64.toNat_ofNat_of_lt' hnFb, hewe] at hsim
  obtain ⟨u3, a3, hrun3, hC3, hg3, hA3, c3⟩ := hsim
  subst hs'
  refine ErrClaim.bind_right hrun3 ?_
  rw [h3, iacE.k_check_abs_ctor_sorts_one.arm1] at he
  have hg13 := hg1.trans hg3
  have c13 := c1.trans c3
  have hcP' : ConRon.Bridge.Inductives.dCtors a3.store cs' = some csP' :=
    ConRon.Bridge.Inductives.dCtors_ext c13.ext _ _ hcsP'
  cases hx : iacE p (k + 1) s'.mem vis ctx isP (co + 1) (cl - 1) (oo + 1) (ol - 1) with
  | ok q => obtain ⟨r0, m0⟩ := q; rw [hx, iacE.k_check_abs_ctor_sorts.arm1] at he; cases he
  | error ε =>
  rw [hx, iacE.k_check_abs_ctor_sorts.none] at he; cases he
  exact ih (by omega) s'.mem a3 (co + 1) (cl - 1) (oo + 1) (ol - 1) cs' os' csP' osP' hC3 hA3
    (hc.grow (decCtx_mono _) hg13)
    (PSlR0.grow decCN_mono (⟨hcs'.1, Or.inr hcs'.2⟩ : PSlR0 decCN cs' (co + 1) (cl - 1) m) hg13)
    (PSlR0.grow decKE_mono (⟨hos'.1, Or.inr hos'.2⟩ : PSlR0 decKE os' (oo + 1) (ol - 1) m) hg13)
    (ConRon.Bridge.Inductives.dCtx_ext _ c13.ext _ _ hctxP) hcP'
    (ConRon.Bridge.Inductives.dOut_ext.list c13.ext _ _ hosP')
    (fun y hy => hws y (List.mem_cons_of_mem _ hy)) (ConRon.Bridge.denoteFEnv_mono c13.ext hfe) _ hx

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
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    have hW1 := triple_of_callE_err (iacE_spec p hP.abs n ⟨m, Locals.init []⟩ vis ctx isP co cl oo2 ol2) h1
      (Err.code_ne_of_cls hk0)
    simp only at hW1
    exact ErrClaim.bind_left (iacE_claim hq henv hOpf hLC hLT hnv eCsf hApd hP ctx isP c b hb hhi n (by omega)
      m a co cl oo2 ol2 cs os csP osP hC hA hc ⟨hcd, hcb⟩ ⟨hod, hob⟩ hctxP hcP hoP (hws osP List.mem_cons_self)
      hfe _ hW1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iac_spec p hP.abs n _ vis ctx isP co cl oo2 ol2) (callW_of_callE h1)
  subst hs'
  obtain ⟨u1, a1, hrun1, hC1, hg1, hA1, c1⟩ := iacW_simC hq henv hOpf hLC hLT hApd hP ctx isP c b hb hhi n (by omega)
    m a co cl oo2 ol2 cs os csP osP hC hA hc ⟨hcd, hcb⟩ ⟨hod, hob⟩ hctxP hcP hoP (hws osP List.mem_cons_self) hfe
    r1 s'.mem hW
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
