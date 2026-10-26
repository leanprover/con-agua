import ConAgua.Verdict.PosTopE3

/-!
# The error claims of `nest_root` and `nest_seeds` (lane `verdicts-b`, helper `ia2`, fork `top`)

`p2rtW_okC`'s and `p2sdW_okC`'s proofs (`PosRoot.lean`) on the models `nrtE`, `nsdE`: the walk's
callees by their claims (`CtorsOKE`, `KeyOKEc` of `NbOKE`, `NitE`), the others claim nothing
(`nvFns`); their ok runs through the block's specs (`nbSpec_all`) and `StageC` facts
(`nbOKC_all`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dCtors dOut dOutss kindOf)

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section root
variable {p : Prog} (L : RsLook p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
  (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hCtE : ∀ n, n ≤ 2 ^ 62 → CtorsOKE p dn vis fe env n)
  (ctx hO hL : Word) (c : NestCtx) (holes : List EIdx)
  {ctxP : ConLeche.NestCtx} (hc : ConLeche.NestCtxOk ctxP) {holesP : List ConLeche.Expr}
  (hholes : ∀ x ∈ holesP, ConLeche.Expr.WScoped (ctxP.hiAt 0) x)
  (hlen : ctxP.names.length ≤ holesP.length)
  (hpar : ∀ x ∈ ctxP.params, ConLeche.Expr.WScoped (ctxP.hiAt 0) x)

include L hnv hq hIlpf hLC henv hCtE hc hholes hlen hpar in
/-- **`nest_root`'s error claim** (`p2rtW_okC`'s hypotheses). -/
theorem nrtE_claim : ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (cO cL ns oO oL : Word)
    (css : List (List (IConstantVal × Nat))) (NS : NestState) (outss : List (List (List NestFieldKind × EIdx)))
    (cssP : List (List (ConLeche.ConstantVal × Nat))) (nsP : ConLeche.NestState)
    (outssP : List (List (List ConLeche.NestFieldKind × ConLeche.Expr))) (e : Err),
    nrtE p n m vis ctx hO hL cO cL ns oO oL = .error e → StageC dn vis fe env m a →
    UCtx dn vis fe m ctx c →
    c.hiAt 0 < 2 ^ 64 → c.params.length + c.names.length < 2 ^ 64 →
    decHL m hO.toNat hL.toNat = some holes → hO.toNat + hL.toNat ≤ iwTop m →
    cL.toNat = css.length → cO.toNat + css.length ≤ iwTop m → CssAt m cO.toNat css → NSB m ns NS →
    RootOutsB m oO.toNat oL.toNat outss → oO.toNat + oL.toNat ≤ iwTop m → PosMR m → AbsOK m →
    dCtx a.store env.find? c = some ctxP → Frontend.denoteEList a.store holes = some holesP →
    css.mapM (dCtors a.store) = some cssP → dState a.store NS = some nsP → dOutss a.store outss = some outssP →
    (∀ cs ∈ cssP, ∀ x ∈ cs, x.1.type.hasFvar = false) →
    ErrClaim (nestRoot V fe c holes css NS outss) a e
  | 0, _, m, a, cO, cL, ns, oO, oL, css, NS, outss, _, _, _, e, he, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _ => by
    rw [nrtE.eq_1] at he; cases he; exact ErrClaim.of_cls0 rfl
  | n + 1, hn, m, a, cO, cL, ns, oO, oL, css, NS, outss, cssP, nsP, outssP, e, he, hC, hU, hhi, hpn, hho, hhob,
      hcl, hcb, hcss, hns, hout, houtb, hP, hA, hctx, hholesP, hcssP, hnsP, houtsP, hcF => by
    have hS := hC.stage
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    have R := L.nb.ct.cr.rx
    by_cases h0 : cL = 0
    · rw [nrtE.arm1 p n m vis ctx hO hL cO cL ns oO oL h0] at he; cases he
    rw [nrtE.arm2 p n m vis ctx hO hL cO cL ns oO oL h0] at he
    obtain ⟨cs, css', rfl⟩ : ∃ x css', css = x :: css' := by
      cases css with
      | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hcl)) h0
      | cons x css' => exact ⟨x, css', rfl⟩
    simp only [List.length_cons] at hcl hcb
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hcssP
    rcases hc1 : dCtors a.store cs with _ | csP; · rw [hc1] at hcssP; simp at hcssP
    cases hcs1 : css'.mapM (dCtors a.store) with
    | none => rw [hc1, hcs1] at hcssP; simp at hcssP
    | some cssP' =>
    simp only [hc1, hcs1, Option.bind_some, Option.some.injEq] at hcssP
    subst hcssP
    obtain ⟨hcn, -, -, hpar', hlv, -⟩ := ConRon.Bridge.Inductives.dCtx_fields hctx
    have hhiP : c.hiAt 0 = ctxP.hiAt 0 := ConRon.Bridge.Inductives.hiAt_eq hctx 0
    obtain ⟨hdr, cO', cL', h0w, h1w, h2w, -, hhdr, hcl', hcb', hcsAt⟩ := hcss 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0w hcl' hcb' hcsAt
    rw [hcl'] at hcb'
    have rd0 : rdW (m.arr64 IW) cO = hdr := by simp [rdW, h0w]
    have rd1 : rdW (m.arr64 IW) hdr = cO' := by simp [rdW, h1w]
    have hdr1 : (hdr + 1).toNat = hdr.toNat + 1 := word_add_toNat (by simp; omega)
    have rd2 : rdW (m.arr64 IW) (hdr + 1) = cL' := by simp [rdW, hdr1, h2w]
    -- the context's words
    obtain ⟨hn0, -, hpa0, -, -, hus0, husd0, -, -, -⟩ := ctx_fields hU.dec hU.inn htop
    have hne0 := ctx_names_end hU.dec hU.inn hU.sl htop
    have hpe0 := ctx_params_end hU.dec hU.inn hU.sl htop
    have hW : WCtx dn vis fe m ctx 0 0 c [] := ⟨hU, by simp [HSl, HolesAt], by simpa using hhi⟩
    have hhi0 : (nhiW m ctx 0).toNat = c.hiAt 0 := by simpa using hW.hi htop
    have hpl : (rdW (m.arr64 IW) (ctx + 8)).toNat = c.params.length := (pos2_hslice_get hpa0).1.symm
    have hCc : CtorsCtx m (rdW (m.arr64 IW) (ctx + 10)) (rdW (m.arr64 IW) (ctx + 7)) (rdW (m.arr64 IW) (ctx + 8))
        (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) hO hL c.params c.names holes :=
      ⟨hus0, by show decHL (truncM m) _ _ = _; rw [decHL_truncM hpe0]; exact hpa0, hpe0, hn0, hne0,
        by rw [hpl]; exact hpn, hho, hhob⟩
    have hpre : CtorsPre a.store (decI (rdW (m.arr64 IW) (ctx + 10))) c.params c.names holes (nhiW m ctx 0).toNat
        (ctxP.lps.map .param) ctxP.params ctxP.names holesP :=
      ⟨by rw [husd0]; exact hlv, hpar', hcn, hholesP, by rw [hhi0, hhiP]; exact hpar,
        by rw [hhi0, hhiP]; exact hholes, hlen⟩
    rw [ConRon.Arena.nestRoot]
    -- `nest_ctx_hi_at`
    cases h1 : callE p n "nest_ctx_hi_at" [ctx, 0] m with
    | error e1 =>
      rw [h1, nrtE.k_nest_ctx_hi_at.none] at he; cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
    | ok q1 =>
    obtain ⟨rh, mh⟩ := q1
    obtain ⟨sh, hsh, -, hmh, hrh⟩ := triple_of_callW (nestCtxHiAt_specE p R.hi n ⟨m, Locals.init []⟩ ctx 0)
      (callW_of_callE h1)
    simp only at hmh hrh
    rw [hsh] at hmh; subst hmh
    rw [h1, nrtE.k_nest_ctx_hi_at.arm1, hrh, rd0, rd1, rd2] at he
    -- `nest_ctors`
    cases h2 : callE p n "nest_ctors" [vis, ctx, 1, 0, 0, 0, nhiW mh ctx 0, rdW (mh.arr64 IW) (ctx + 10),
        rdW (mh.arr64 IW) (ctx + 7), rdW (mh.arr64 IW) (ctx + 8), rdW (mh.arr64 IW) ctx,
        rdW (mh.arr64 IW) (ctx + 1), hO, hL, cO', cL', ns, 0, 0] mh with
    | error e2 =>
      rw [h2, nrtE.k_nest_ctors.none] at he; cases he
      refine ErrClaim.bind_left ?_
      have hE := hCtE n (by omega) mh a ctx 1 0 0 0 (nhiW mh ctx 0) _ _ _ _ _ hO hL cO' cL' ns 0 0 c [] c.params
        c.names holes cs NS [] ctxP [] _ _ _ _ csP nsP [] hC hW hCc hcl' hcb' hcsAt hns
        (by simpa using OutsB.nil mh 0) (by simp) hP hA hc hctx rfl hpre hc1 (hcF csP List.mem_cons_self) hnsP rfl
        _ h2
      rw [hhi0, husd0] at hE
      simpa using hE
    | ok q2 =>
    obtain ⟨r1', m1⟩ := q2
    have hCt := (nbOKC_all (dn := dn) (vis := vis) (fe := fe) hq hIlpf hLC henv n (by omega)).2.2.2.2.2.2.2.1
    obtain ⟨s2, hs2, -, hct⟩ := triple_of_callW
      ((nbSpec_all L.nb (realCall p) (realCall_spec p) n).2.2.2.2.2.2.2.1 ⟨mh, Locals.init []⟩ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _) (callW_of_callE h2)
    simp only at hct hs2
    rw [hs2] at hct
    rw [h2, nrtE.k_nest_ctors.arm1] at he
    obtain ⟨x1, a1, hrun1, hC1, hg1, hO1, hOb1, hns1, hP1, hA1, c1⟩ := hCt mh m1 a ctx 1 0 0 0 (nhiW mh ctx 0) _ _ _ _ _
      hO hL cO' cL' ns 0 0 c [] c.params c.names holes cs NS [] _ ctxP [] _ _ _ _ csP nsP [] hct hC hW hCc hcl'
      hcb' hcsAt hns (by simpa using OutsB.nil mh 0) (by simp) hP hA hc hctx rfl hpre hc1
      (hcF csP List.mem_cons_self) hnsP rfl
    simp only [List.headD_cons, List.tail_cons] at hO1 hOb1 hns1
    have hS1 := hC1.stage
    rw [hhi0, husd0] at hrun1
    have hrun1' : (nestCtors V fe c true 0 [] (c.hiAt 0) c.lvls c.params c.names holes cs NS []).run a =
        .ok (x1, a1) := by simpa using hrun1
    have hrun1P : (nestCtors V fe c true 0 [] (ctxP.hiAt 0) c.lvls c.params c.names holes cs NS []) a =
        .ok (x1, a1) := by rw [← hhiP]; exact hrun1'
    obtain ⟨-, v1, ⟨hv1, hns1P, -⟩, -⟩ := ConRon.Bridge.Inductives.nestCtors_spec coreSpecV henv true 0
      (fun crestP => ConLeche.nestPos (ConLeche.fueledOpsM V) env ctxP (ConLeche.whnfWalkFuel crestP))
      (fun _ => by simp) (fun crestP => by simpa using ConRon.Bridge.Inductives.nestPos_spec coreSpecV henv hc _)
      [] [] (ctxP.hiAt 0) c.lvls _ c.params ctxP.params c.names ctxP.names holes holesP
      hpar hholes hlen cs csP NS nsP [] [] (hcF csP List.mem_cons_self) a a1 x1 hC.check
      ⟨hctx, rfl, hlv, hpar', hcn, hholesP, hc1, hnsP, rfl⟩ hrun1P
    simp only [List.nil_append] at hv1
    refine ErrClaim.bind_right hrun1' ?_
    have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
    -- its record
    cases h3 : callE p n "rec2" [r1'.headD 0, r1'.tail.headD 0] m1 with
    | error e3 =>
      rw [h3, nrtE.k_rec2.none] at he; cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
    | ok q3 =>
    obtain ⟨rq, m2⟩ := q3
    obtain ⟨s3, hs3, -, hr2⟩ := triple_of_callW (posRec2_specW p R.ha R.h2 n ⟨m1, Locals.init []⟩ _ _) (callW_of_callE h3)
    simp only at hr2 hs3
    rw [hs3] at hr2
    rw [h3, nrtE.k_rec2.arm1] at he
    obtain ⟨hS2, hg2, hq2, ht2, hget2⟩ := posRecW_stage hr2 hS1 (by simp)
    simp only [List.length_cons, List.length_nil] at ht2
    have hrec := pos2_outs_rec (q := rq.headD 0) (by omega) hget2 (hO1.grow hg2)
    have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
    cases h4 : callE p n "sl_snoc" [oO, oL, rq.headD 0] m2 with
    | error e4 =>
      rw [h4, nrtE.k_sl_snoc.none] at he; cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
    | ok q4 =>
    obtain ⟨ro, m3⟩ := q4
    obtain ⟨s4, hs4, -, hsn⟩ := triple_of_callW (slSnoc_specW p R.ha L.nb.nit.hc2 L.nb.nag.hsn n
      ⟨m2, Locals.init []⟩ _ _ _) (callW_of_callE h4)
    simp only at hsn hs4
    rw [hs4] at hsn
    rw [h4, nrtE.k_sl_snoc.arm1] at he
    have hg12 := hg1.trans hg2
    obtain ⟨hS3, hg3, h30, h31, ht3, hw3, hx3⟩ := snocW_words hsn hS2 (by have := hg12.1; omega)
    have hout3 : RootOutsB m3 (ro.headD 0).toNat (ro.tail.headD 0).toNat (outss ++ [x1.1]) := by
      rw [h30, h31]
      exact pos2_decB_snoc pos2_rootOuts_mono (hout.grow hg12) hg3 (by omega) hw3 hx3
        (DecB.grow (pos2_rootOuts_mono _) hg3 hrec)
    have hg13 := hg12.trans hg3
    have hcO1 : (cO + 1).toNat = cO.toNat + 1 := word_add_toNat (by simp; omega)
    have hcL1 : (cL - 1).toNat = css'.length := by rw [pos2_word_pred h0]; omega
    have hA3 : AbsOK m3 := snocW_afr hsn (posRecW_afr hr2 hA1)
    have hC3 : StageC dn vis fe env m3 a1 := hC1.of_pstep hS3 hA3 (PStep.refl hC1.check.state)
    cases hx : nrtE p n m3 vis ctx hO hL (cO + 1) (cL - 1) (r1'.tail.tail.headD 0) (ro.headD 0) (ro.tail.headD 0) with
    | ok q => obtain ⟨r0, m0⟩ := q; rw [hx, nrtE.k_nest_root.arm1] at he; cases he
    | error ε =>
    rw [hx, nrtE.k_nest_root.none] at he; cases he
    exact nrtE_claim n (by omega) m3 a1 (cO + 1) (cL - 1)
      (r1'.tail.tail.headD 0) (ro.headD 0) (ro.tail.headD 0) css' x1.2 (outss ++ [x1.1]) cssP' v1.2
      (outssP ++ [v1.1]) _ hx hC3 (hU.grow hg13) hhi hpn
      (by rw [decHL_agree (RdS.of_grow hg13) (fun j hj => by omega)]; exact hho)
      (by have := hg13.1; omega) hcL1 (by rw [hcO1]; have := hg13.1; omega)
      (by rw [hcO1]; exact (hcss.grow hg13).tail)
      ((hns1.grow hg2 htop1).grow hg3 htop2) hout3 (by rw [h30, h31]; omega)
      ((hP1.fr (posRecW_mfr hr2)).fr (snocW_mfr hsn)) hA3
      (dCtx_ext _ c1.ext _ _ hctx) (ConRon.Bridge.denoteEList_ext c1.ext _ _ hholesP)
      (ConRon.Bridge.Inductives.dCtors_ext.list c1.ext _ _ hcs1) hns1P
      (ConRon.Bridge.Inductives.mapM_option_append (ConRon.Bridge.Inductives.dOutss_ext c1.ext _ _ houtsP)
        (by simp [hv1]))
      (fun cs hcs => hcF cs (List.mem_cons_of_mem _ hcs))

end root

end L.Ind
