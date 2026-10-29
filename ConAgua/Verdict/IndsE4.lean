import ConAgua.Arena.IndT.Install1
import ConAgua.Verdict.LefRef
import ConAgua.Arena.IndInstallSpec.IagW
import ConAgua.Arena.Checker
/-!
# `check_block_agree_one`: one model and one refinement for both outcomes

`cbaoE` (`l_model … unified`): `open_pis_at_fvars_f` and `fvar_type_ds` (outside the verdict
closure) through their `Option` models, `check_block_doms_at` through its run, `lvl_eq_fueled`
through its unified model `lefE`. `cbao_ref` refines `agreeBodyAM` for both outcomes: the
unopened member telescope and a length mismatch are the twin's rejects, `check_block_doms_at`'s
errors by `cbda_ref`, `lvl_eq_fueled`'s by `lef_ref`, a `false` universe comparison the twin's
reject.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_block_agree_one`'s model, both outcomes**: `open_pis_at_fvars_f` and `fvar_type_ds`
(outside the verdict closure) through their `Option` models, `check_block_doms_at` through its
run, `lvl_eq_fueled` through `lefE`. -/
l_model cbaoE_spec (p : Prog) (hf : p.lookup "check_block_agree_one" = some checkBlockAgreeOne)
  (hl : p.lookup "lvl_eq_fueled" = some lvlEqFueled)
  fns [hf ↦ cbaoE]
  specs [callW_spec p n "open_pis_at_fvars_f", callW_spec p n "fvar_type_ds", lefE_spec p hl n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What the agreements leave: the stage relation, the growth, the absence of stale records, the
twin's frame. -/
structure AgreePost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p)

include hq henv hOpf hLC in
/-- **`check_block_agree_one` refines `agreeBodyAM`**, both outcomes (member 0's telescope opened
by the caller; the denotations as con-ron's `checkBlockAgree_specF`'s proof has them at a member). -/
theorem cbao_ref (hP : AgreeProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {nP fvs0O fvs0L s0 cvTa s : Word} {cv : IConstantVal} {fvs0 : List EIdx}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hty : (rdW (m.arr64 EREC) (cvTa + 3)).toNat < 2 ^ 32 ∧ decI (rdW (m.arr64 EREC) (cvTa + 3)) = cv.type)
    (hfvs0 : decHL m fvs0O.toNat fvs0L.toNat = some fvs0)
    (hfot : fvs0O.toNat + fvs0L.toNat ≤ iwTop m) (hs : H s) (hs0 : H s0)
    {tyP : ConLeche.Expr} {xs0 : List ConLeche.Expr} {sP s0P : ConLeche.Level}
    (htyP : denoteE a.store cv.type = some tyP) (hwx : ConLeche.Expr.WScoped 0 tyP)
    (hxs0 : Frontend.denoteEList a.store fvs0 = some xs0)
    (hsc0 : ∀ (i : Nat) (x : ConLeche.Expr), xs0[i]? = some x →
      ConLeche.Expr.WScoped (0 + i) x.fvarTypeD)
    (hsP : denoteL a.store.ls (decI s) = some sP) (hs0P : denoteL a.store.ls (decI s0) = some s0P) :
    RefE (VerdictCtx p) (cbaoE p n m vis nP fvs0O fvs0L s0 cvTa s)
      (agreeBodyAM fe nP.toNat fvs0 cv (decI s) (decI s0)) a
      (fun v _ a' => AgreePost dn vis fe env m a v.2 a') := by
  cases n with
  | zero => rw [cbaoE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n =>
  have hStage := hC.stage
  have hz : UInt64.toNat 0 = 0 := rfl
  have hty' : cv.type = decI (rdW (m.arr64 EREC) (cvTa + 3)) := hty.2.symm
  rw [cbaoE.arm1]
  -- `open_pis_at_fvars_f`
  rcases h1 : callW p n "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (cvTa + 3), 0] m with _ | ⟨ra, m1⟩
  · rw [liftE_none, cbaoE.k_open_pis_at_fvars_f.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨x1, a1, hrun1, hSt1, hg1, hdec1, hA1⟩ := opfF_okRA hty.1 (callW_opfF hOpf h1) hStage hA
  have hdty : denoteE a.store (decI (rdW (m.arr64 EREC) (cvTa + 3))) = some tyP := by
    rw [hty.2]; exact htyP
  obtain ⟨p1, ho1⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC.check.state hdty hrun1
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hSt1 hA1 p1
  rw [hz] at hrun1
  by_cases h0 : ra.headD 0 = 0
  · rw [cbaoE.k_open_pis_at_fvars_f.abort1 p n vis nP fvs0O fvs0L s0 s ra m1 h0, RefE_error]
    cases x1 with
    | some fb => exact absurd hdec1.1 (by rw [h0]; decide)
    | none =>
    intro _ _
    refine ⟨.invalid "parameters of all inductive datatypes must match", ?_, rfl⟩
    simp only [agreeBodyAM, unwrapOr, hty', StateT.run_bind, hrun1]
    rfl
  cases x1 with
  | none => exact absurd hdec1 h0
  | some fb =>
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨xs1, b1, hq1, hxs1, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho1
  rw [hz] at hq1
  obtain ⟨-, hrl1, -⟩ := hdec1
  simp only [decRL, show (1:Nat) + 1 = 2 from rfl, agGetD1, agGetD2] at hrl1
  obtain ⟨hfv1, hfvb1⟩ := hrl1
  have hlen1 := decHL_length m1 hfv1
  have hlen0 := decHL_length m hfvs0
  by_cases hL : ra.tail.tail.headD 0 = fvs0L
  case neg =>
    rw [cbaoE.k_open_pis_at_fvars_f.abort2 p n vis nP fvs0O fvs0L s0 s ra m1 h0 hL, RefE_error]
    have hne : fvs.length ≠ fvs0.length := by
      intro hc; apply hL; apply UInt64.toNat_inj.mp; omega
    intro _ _
    refine ⟨.invalid "parameters of all inductive datatypes must match", ?_, rfl⟩
    simp [agreeBodyAM, unwrapOr, hty', StateT.run_bind, hrun1, hne] <;> rfl
  rw [cbaoE.k_open_pis_at_fvars_f.arm1 p n vis nP fvs0O fvs0L s0 s ra m1 h0 hL]
  rw [hL] at hlen1
  have heq : fvs.length = fvs0.length := by omega
  -- `fvar_type_ds`
  rcases h2 : callW p n "fvar_type_ds" [fvs0O, fvs0L] m1 with _ | ⟨rd, m2⟩
  · rw [liftE_none, cbaoE.k_fvar_type_ds.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, cbaoE.k_fvar_type_ds.arm1]
  have hrb : ftdsF m1 [fvs0O, fvs0L] = some (rd, m2) := by
    obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩) (ftdsF_spec p hP.ad n _ _) h2
    rw [← hs']; exact hW
  have hbound1 : fvs0O.toNat + fvs0L.toNat ≤ iwTop m1 := by have := hg1.1; omega
  obtain ⟨x2, a2, hrun2, hSt2, hg2, hdec2⟩ :=
    ftdsF_ok dn vis fe fvs0O fvs0L fvs0 m1 m2 a1 rd hrb
      ⟨hSt1, by rw [decHL_grow hg1 (by omega)]; exact hfvs0, fun _ => hbound1⟩
  obtain ⟨p2, hdoms⟩ := ConRon.Bridge.Inductives.fvarTypeDs_run fvs0 xs0 hC1.check.state
    (ConRon.Bridge.denoteEList_ext p1.ext _ _ hxs0) hrun2
  have hA2 := ftdsF_afr hrb hA1
  have hC2 : StageC dn vis fe env m2 a2 := hC1.of_pstep hSt2 hA2 p2
  simp only [decRL, show (0:Nat) + 1 = 1 from rfl, agGetD0, agGetD1] at hdec2
  obtain ⟨hdm2, hdb2⟩ := hdec2
  have hlt1 := UInt64.toNat_lt (ra.tail.headD 0)
  have hlt2 := UInt64.toNat_lt (ra.tail.tail.headD 0)
  have hlt3 := UInt64.toNat_lt (rd.headD 0)
  have hlt4 := UInt64.toNat_lt (rd.tail.headD 0)
  have hltt : iwTop m2 < 2 ^ 64 := UInt64.toNat_lt _
  have hltt1 : iwTop m1 < 2 ^ 64 := UInt64.toNat_lt _
  have hc : ∀ (i : Nat) (x : ConLeche.Expr), xs1[i]? = some x →
      ConLeche.Expr.WScoped (0 + i) x.fvarTypeD :=
    ConRon.Bridge.Inductives.openers_typeD_WScoped hq1 hwx
  have ht : ∀ (i : Nat) (y : ConLeche.Expr), (xs0.map ConLeche.Expr.fvarTypeD)[i]? = some y →
      ConLeche.Expr.WScoped (0 + i) y := fun i y hy => by
    rw [List.getElem?_map] at hy
    obtain ⟨z, hz', rfl⟩ := Option.map_eq_some_iff.mp hy
    exact hsc0 i z hz'
  have hxs1' := ConRon.Bridge.denoteEList_ext p2.ext _ _ hxs1
  have hfv2 : decHL m2 (ra.tail.headD 0).toNat (ra.tail.tail.headD 0).toNat = some fvs := by
    rw [decHL_grow hg2 hfvb1]; exact hfv1
  -- the twin's prefix up to the domains' comparison
  have hpre :
      (agreeBodyAM fe nP.toNat fvs0 cv (decI s) (decI s0)).run a =
        (ConRon.Arena.checkBlockDomsAt V fe 0 fvs x2 nP.toNat >>= fun _ =>
          lvlEq? (decI s) (decI s0) >>= fun x => liftFueled "level comparison" x >>= fun b =>
            if b = true then (pure () : AM Unit) else
              ConRon.Arena.fail (.invalid "mutually inductive types must live in the same universe")).run a2 := by
    simp [agreeBodyAM, unwrapOr, hty', StateT.run_bind, hrun1, heq, hrun2]
  -- `check_block_doms_at`
  have hR3 := cbda_ref hq henv hP.ad.ftd n (by omega) m2 a2 0 (ra.tail.headD 0) (ra.tail.tail.headD 0)
    (rd.headD 0) (rd.tail.headD 0) nP fvs x2 xs1 (xs0.map ConLeche.Expr.fvarTypeD)
    hC2 hA2 hfv2 hdm2 (by omega) (by omega) (by have := hg2.1; omega) (by omega)
    (by simp only [UInt64.toNat_zero, Nat.zero_add]; exact hlt2)
    hxs1' hdoms (fun i _ x y hx hy => ⟨hc i x hx, ht i y hy⟩)
  have hs3 := cbdaE_spec p hP.doms n ⟨m2, Locals.init []⟩ vis 0 (ra.tail.headD 0) (ra.tail.tail.headD 0)
    (rd.headD 0) (rd.tail.headD 0) nP
  rcases h3 : callE p n "check_block_doms_at" [vis, 0, ra.tail.headD 0, ra.tail.tail.headD 0, rd.headD 0,
      rd.tail.headD 0, nP] m2 with e3 | ⟨r3, m3⟩
  · rw [cbaoE.k_check_block_doms_at.none, RefE_error]
    refine fun hG => ErrClaim.of_run_err (T' := ConRon.Arena.checkBlockDomsAt V fe 0 fvs x2 nP.toNat)
      (a' := a2) (fun ce hce => by rw [hpre, StateT.run_bind, hce]; rfl) ?_
    have hcl := RefE.run_err hs3 hG.nv hG.core hR3 h3
    rwa [hz] at hcl
  rw [cbaoE.k_check_block_doms_at.arm1]
  obtain ⟨s3, rfl, -, u3, a3, hrun3, hC3, hg3, hA3⟩ := RefE.run_ok hs3 hR3 h3
  dsimp only at hC3 hg3 hA3
  rw [hz] at hrun3
  obtain ⟨c3, -⟩ := ConRon.Bridge.Inductives.checkBlockDomsAt_specF fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv 0 fvs x2 xs1 (xs0.map ConLeche.Expr.fvarTypeD) hc ht
    nP.toNat a2 a3 u3 hC2.check ⟨hxs1', hdoms⟩ hrun3
  have hx03 := p1.ext.trans (p2.ext.trans c3.ext)
  have hpre3 : (agreeBodyAM fe nP.toNat fvs0 cv (decI s) (decI s0)).run a =
      (lvlEq? (decI s) (decI s0) >>= fun x => liftFueled "level comparison" x >>= fun b =>
        if b = true then (pure () : AM Unit) else
          ConRon.Arena.fail (.invalid "mutually inductive types must live in the same universe")).run a3 := by
    rw [hpre, StateT.run_bind, hrun3]; rfl
  refine RefE.of_run_eq hpre3 ?_
  -- `lvl_eq_fueled`
  rw [lefT_bind]
  have hR4 := lef_ref (p := p) hq.closed hLC n hC3.stageT hs hs0 (ConRon.Bridge.denoteL_ext hsP hx03)
    (ConRon.Bridge.denoteL_ext hs0P hx03)
  rcases h4 : lefE p n s3.mem s s0 with e4 | ⟨w, m4⟩
  · rw [h4] at hR4
    rw [cbaoE.k_lvl_eq_fueled.none]
    exact RefE.bind_left fun hG =>
      hR4 fun n args m e h => callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) n args m h
  rw [h4] at hR4
  obtain ⟨b, a4, hrun4, hL⟩ := hR4
  refine RefE.bind_right hrun4 ?_
  obtain ⟨hC4, hA4, -⟩ := hL.stageC env hC3 hA3
  have hbre : w = if b then 1 else 0 := hL.res
  by_cases hre : w = 0
  · rw [cbaoE.k_lvl_eq_fueled.abort1 p w m4 hre, RefE_error]
    obtain rfl : b = false := by cases b <;> simp_all
    intro _ _
    exact ⟨.invalid "mutually inductive types must live in the same universe", rfl, rfl⟩
  rw [cbaoE.k_lvl_eq_fueled.arm1 p w m4 hre]
  obtain rfl : b = true := by cases b <;> simp_all
  obtain ⟨c4, -⟩ := ConRon.Bridge.Inductives.lvlEq?_crun hC3.check
    (ConRon.Bridge.denoteL_ext hsP hx03) (ConRon.Bridge.denoteL_ext hs0P hx03) hL.run
  exact RefE.ret rfl
    ⟨hC4, (hg1.trans hg2).trans (hg3.trans hL.grow), hA4, ((p1.trans p2).toCore hC.check).trans (c3.trans c4)⟩

end sims

end L.Ind
