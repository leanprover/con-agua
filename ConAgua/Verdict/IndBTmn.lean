import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.IndSumSpec.SoaW
import ConAgua.Arena.RecCheckSpec.CnfW
import ConAgua.Arena.RecCheckSpec.TargetMajorDefault
import ConAgua.Arena.RecCheckSpec.Tmn
import ConAgua.Verdict.IndBTcm
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
/-!
# `target_major_nfs`: one model and one refinement for both outcomes

`tmnE` (`l_model … unified`): the recursive call through the model itself, `target_class_match`
through its unified model (`tcmE`), `ctors_have_name` and `sl_cons` (outside the verdict closure)
through their `Option` models. `tmn_ref` refines `targetMajorNfs` for both outcomes; its ok half
is `targetMajorNfs_refinesC` and `classes_nfs`' refinement (`RecGen28`), its error half
`classes_nfs`' error claim (`IndBNfs`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs dShape dCtors dCtorNf)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tmnE_spec (p : Prog) (hL : TmnLook p)
  fns [hL.tmn ↦ tmnE]
  specs [ctorsHaveName_spec p hL.chn n, tcmE_spec p hL.tcm n,
    slCons_specW p hL.tcm.ha hL.tcm.ic hL.tcm.sc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `target_major_nfs` gives besides the twin's result `ys` (from `m`, the table `nfs` at
`nfo`, `nfl`): the kept entries' slice, the stage invariant, the growth; and, when the table's
pointers are those of `mb`, where the kept slice lies and that its pointers are `mb`'s too. -/
structure TmnPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (nfo nfl : Word) (nfs : List NestCtorNf) (r : List Word) (m' : Mem)
    (ys : List NestCtorNf) (a' : AState) : Prop where
  slice : PSlR decNCN ys (r.headD 0) (r.tail.headD 0) m'
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  rc : RcMR m'
  abs : AbsOK m'
  ptrs : ∀ mb ps, decNL m nfo.toNat nfl.toNat = some ps → PtrsB mb ps nfs →
    (r.tail.headD 0 = 0 ∨ iwTop m ≤ (r.headD 0).toNat) ∧
    ∃ ps', decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some ps' ∧ PtrsB mb ps' ys

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`target_major_nfs` refines `targetMajorNfs`, both outcomes** (twin side: con-ron's
`targetMajorNfs_spec`'s list induction): the tail first (its `CoreStep` from con-ron's spec on the
tail's run), the name test (L only, `chnW_ok`), `targetClassMatch` (`tcm_ref`), the kept entry
consed (L only). -/
theorem tmn_ref (hL : TmnLook p) (n : Nat) (hn : n ≤ 2 ^ 62) : ∀ {m : Mem} {a : AState}
    {q fto ftl pfo pfl us dso dsl cto ctl nfo nfl : Word}
    {bs : BlockShape} {formerTys pfvs ds : List EIdx} {ctors : List (IConstantVal × Nat)}
    {nfs : List NestCtorNf} {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP : List ConLeche.Expr}
    {usP : List ConLeche.Level} {ctorsP : List (ConLeche.ConstantVal × Nat)}
    {nfsP : List ConLeche.NestCtorNf},
    StageC dn vis fe env m a → AbsOK m → BSOK m q.toNat bs → H us →
    decHL m fto.toNat ftl.toNat = some formerTys → fto.toNat + ftl.toNat ≤ iwTop m →
    HSl0 m pfo pfl pfvs → HSl0 m dso dsl ds →
    DecB (fun m => decPL m (decCN m) cto.toNat ctl.toNat) m ctors → cto.toNat + ctl.toNat < 2 ^ 64 →
    PSlR decNCN nfs nfo nfl m → RcMR m →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    Frontend.denoteEList a.store pfvs = some pfvsP → denoteLs a.store.lss (decI us) = some usP →
    Frontend.denoteEList a.store ds = some dsP → dCtors a.store ctors = some ctorsP →
    nfs.mapM (dCtorNf a.store) = some nfsP →
    (∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t) →
    (∀ x ∈ pfvsP, ConLeche.Expr.WScoped pfvsP.length x) →
    RefE (VerdictCtx p) (tmnE p n m vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl)
      (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a
      (fun v ys a' => TmnPost dn vis fe env m nfo nfl nfs v.1 v.2 ys a') := by
  induction n with
  | zero =>
    intros; rw [tmnE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n ih =>
  intro m a q fto ftl pfo pfl us dso dsl cto ctl nfo nfl bs formerTys pfvs ds ctors nfs pP
    formerTysP pfvsP dsP usP ctorsP nfsP hC hA hbs hus hft hftb hpf hds hct hctb hnf hP hsh hftP
    hpfP husP hdsP hctP hnfP hformer hpw
  have hS := hC.stage
  by_cases hl : nfl = 0
  · rw [tmnE.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl]
    subst hl
    have : nfs = [] := by
      have := decPL_length _ (hnf.1.get (OMono.decPL decNCN_mono _ _)); simpa using this
    subst this
    exact RefE.ret rfl ⟨PSlR.nil _ _, hC, IWGrow.refl _, hP, hA,
      fun _ _ _ _ => ⟨.inl rfl, [], by simp [decNL], FA2.nil⟩⟩
  rw [tmnE.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl]
  have hsz := hS.2.2.2.1
  obtain ⟨nf, nfs', rfl, hnf0, hnf'⟩ := hnf.uncons hl hsz
  obtain ⟨nfP, nfsP', rfl, hnfP1, hnfsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hnfP
  have hb64 := hS.lt64 hnf.2
  obtain ⟨e1, e2, hl0⟩ := slice_step hl hb64
  have ih' := ih (by omega) hC hA hbs hus hft hftb hpf hds hct hctb hnf' hP hsh hftP hpfP husP hdsP hctP
    hnfsP' hformer hpw
  rw [ConRon.Arena.targetMajorNfs]
  rcases h1 : tmnE p n m vis q fto ftl pfo pfl us dso dsl cto ctl (nfo + 1) (nfl - 1) with e1' | ⟨rr, m1⟩
  · rw [h1] at ih'
    rw [tmnE.k_target_major_nfs.none]; exact RefE.bind_left ih'
  rw [h1] at ih'
  obtain ⟨ys, a1, run1, hR1⟩ := ih'
  obtain ⟨c1, -⟩ := ConRon.Bridge.Inductives.targetMajorNfs_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv bs pP formerTys pfvs formerTysP pfvsP (decI us) usP ds dsP ctors ctorsP hformer hpw nfs'
    nfsP' a a1 ys hC.check ⟨hsh, hftP, hpfP, husP, hdsP, hctP, hnfsP'⟩ run1
  refine RefE.bind_right run1 ?_
  rw [tmnE.k_target_major_nfs.arm1]
  have hC1 := hR1.stage
  have hg1 := hR1.grow
  have hS1 := hC1.stage
  have hnfo : nfo.toNat < iwTop m := by have := hnf.2; omega
  have he : rdW (m1.arr64 IW) nfo = rdW (m.arr64 IW) nfo := by
    simp only [rdW]; rw [hg1.2.2.1 _ hnfo]
  rw [he]
  -- the table's head pointer: the entry `nf`, and its place in a pointer list
  have hptr0 : ∀ ps, decNL m nfo.toNat nfl.toNat = some ps → ∃ v ps', ps = v :: ps' ∧
      rdW (m.arr64 IW) nfo = UInt64.ofNat v ∧ v < 2 ^ 64 ∧
      decNL m (nfo + 1).toNat (nfl - 1).toNat = some ps' := by
    intro ps hps
    obtain ⟨LL, hLL⟩ : ∃ LL, nfl.toNat = LL + 1 := ⟨nfl.toNat - 1, by omega⟩
    rw [hLL, decNL_succ] at hps
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hps
    obtain ⟨v, hv, ps', hps', rfl⟩ := hps
    have := (iwN_rdW hv (by omega)).1; rw [UInt64.ofNat_toNat] at this
    exact ⟨v, ps', rfl, this, (iwN_rdW hv (by omega)).2, by rw [e1, e2, hLL]; simpa using hps'⟩
  generalize hE : rdW (m.arr64 IW) nfo = e at hnf0 hptr0 ⊢
  have hnf1 : DecB (fun m' => decNCN m' e.toNat) m1 nf := hnf0.grow (decNCN_mono _) hg1
  have hsz1 := hS1.2.2.2.1
  obtain ⟨hcH, hcD, hlH, hlD, hdsl⟩ := decNCN_fields hnf1 hsz1
  have hct1 := hct.grow (OMono.decPL decCN_mono _ _) hg1
  -- the tail's pointers, from the table's
  have hptr1 : ∀ mb ps, decNL m nfo.toNat nfl.toNat = some ps → PtrsB mb ps (nf :: nfs') →
      ∃ v, e.toNat = v ∧ DecB (fun m => decNCN m v) mb nf ∧ (rr.tail.headD 0 = 0 ∨ iwTop m ≤ (rr.headD 0).toNat) ∧
        ∃ pr, decNL m1 (rr.headD 0).toNat (rr.tail.headD 0).toNat = some pr ∧ PtrsB mb pr ys := by
    intro mb ps hps hpb
    obtain ⟨v, ps', rfl, hev, hvb, hps'⟩ := hptr0 ps hps
    cases hpb with
    | cons hpv hpb' =>
      obtain ⟨hfr, hrest⟩ := hR1.ptrs mb ps' hps' hpb'
      exact ⟨v, by rw [hev, UInt64.toNat_ofNat_of_lt' hvb], hpv, hfr, hrest⟩
  -- `ctors_have_name` (outside the verdict closure)
  rcases h2 : chnW n m1 cto ctl (rdW (m1.arr64 IW) e) with _ | hv
  · rw [liftE_none, tmnE.k_ctors_have_name.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hany, -⟩ := chnW_ok n m1 cto ctl _ hv ctors h2 (hct1.get (OMono.decPL decCN_mono _ _)) hcH hctb
  rw [hcD] at hany
  by_cases hh : hv = 0
  · rw [tmnE.k_ctors_have_name.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh]
    have hf : ctors.any (fun c => c.1.name == nf.ctor) = false := by rw [← hany, hh]; rfl
    simp only [hf, Bool.false_eq_true, ite_false]
    refine RefE.ret (y := ys) rfl ⟨hR1.slice, hC1, hg1, hR1.rc, hR1.abs, fun mb ps hps hpb => ?_⟩
    obtain ⟨v, -, -, hfr, pr, hpr, hprb⟩ := hptr1 mb ps hps hpb
    exact ⟨by simpa using hfr, pr, by simpa using hpr, hprb⟩
  rw [tmnE.k_ctors_have_name.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh]
  have ht : ctors.any (fun c => c.1.name == nf.ctor) = true := by rw [← hany]; simpa using hh
  simp only [ht, ite_true]
  obtain ⟨-, hlvP, hedP, -⟩ := ConRon.Bridge.Inductives.RC.dCtorNf_inv
    (ConRon.Bridge.Inductives.dCtorNf_ext c1.ext _ _ hnfP1)
  -- `target_class_match`
  have h3 := tcm_ref hq henv n (by omega) hC1 hR1.abs (hbs.grow hg1) hus hlH
    (by rw [decHL_grow hg1 hftb]; exact hft) (by have := hg1.1; omega)
    (hpf.grow hg1) (hds.grow hg1) hdsl hR1.rc
    (ConRon.Bridge.Inductives.dShape_ext c1.ext _ _ hsh) (denoteEList_ext c1.ext _ _ hftP)
    (denoteEList_ext c1.ext _ _ hpfP) (ConRon.Bridge.denoteLs_ext husP c1.ext)
    (denoteEList_ext c1.ext _ _ hdsP) (by rw [hlD]; exact hlvP) hedP hformer hpw
  rw [hlD] at h3
  rcases h3' : tcmE p n m1 vis q fto ftl pfo pfl us dso dsl (rdW (m1.arr64 IW) (e + 1))
      (rdW (m1.arr64 IW) (e + 2)) (rdW (m1.arr64 IW) (e + 3)) with e3 | ⟨rk, m2⟩
  · rw [h3'] at h3
    rw [tmnE.k_target_class_match.none]; exact RefE.bind_left h3
  rw [h3'] at h3
  obtain ⟨c, a2, run2, hR2⟩ := h3
  refine RefE.bind_right run2 ?_
  have hg2 : IWGrow m1 m2 := hR2.grow
  have hg12 := hg1.trans hg2
  have hys2 := hR1.slice.grow (fun q => decNCN_mono q) hg2
  by_cases hk : rk = 0
  · rw [tmnE.k_target_class_match.arm1 _ _ _ _ _ _ _ hk]
    have hc0 : c = false := by rw [← hR2.res, hk]; rfl
    subst hc0
    refine RefE.ret (y := ys) rfl ⟨hys2, hR2.stage, hg12, hR2.rc, hR2.abs, fun mb ps hps hpb => ?_⟩
    obtain ⟨v, -, -, hfr, pr, hpr, hprb⟩ := hptr1 mb ps hps hpb
    have hb := hR1.slice.2
    dsimp only at hb hpr ⊢
    exact ⟨by simpa using hfr, pr, by simp only [List.headD_cons, List.tail_cons]; rw [decNL_grow hg2 hb]; exact hpr, hprb⟩
  rw [tmnE.k_target_class_match.arm2 _ _ _ _ _ _ _ hk]
  have hc1 : c = true := by rw [← hR2.res]; simpa using hk
  subst hc1
  simp only [ite_true]
  -- `sl_cons` (outside the verdict closure)
  rcases h4 : consW n m2 e (rr.headD 0) (rr.tail.headD 0) with _ | ⟨rc, m3⟩
  · rw [liftE_none, tmnE.k_sl_cons.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, tmnE.k_sl_cons.arm1]
  obtain ⟨hS3, hg3, hps3, hf3⟩ := consW_pslr (fun q => decNCN_mono q) h4 hR2.stage.stage hys2
    (hnf1.grow (decNCN_mono _) hg2)
  have hA3 := consW_afr h4 hR2.abs
  refine RefE.ret (y := nf :: ys) rfl ⟨by simpa using hps3,
    hR2.stage.of_pstep hS3 hA3 (PStep.refl hR2.stage.check.state), hg12.trans hg3, hR2.rc.fr hf3, hA3,
    fun mb ps hps hpb => ?_⟩
  obtain ⟨v, heT, hpv, -, pr, hpr, hprb⟩ := hptr1 mb ps hps hpb
  obtain ⟨hr, hd, -, -, -, -⟩ := consW_decN h4 hR2.stage.stage.2.2.2.1 hR2.stage.stage.2.2.2.2.2 hys2.2
    (by rw [decNL_grow hg2 hR1.slice.2]; exact hpr)
  subst hr
  refine ⟨?_, e.toNat :: pr, by simpa using hd, ?_⟩
  · right; simp only [List.headD_cons]; exact hg12.1
  · rw [heT]; exact FA2.cons hpv hprb

include hq henv in
/-- **`target_major_nfs` refines `targetMajorNfs`** under `StageC` (`tmn_ref`'s ok half). -/
@[refines ConRon.Arena.targetMajorNfs]
theorem targetMajorNfs_refinesC (hL : TmnLook p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (q fto ftl pfo pfl us dso dsl cto ctl nfo nfl : Word)
    (bs : BlockShape) (formerTys pfvs ds : List EIdx) (ctors : List (IConstantVal × Nat))
    (nfs : List NestCtorNf) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hbs : BSOK s₀.mem q.toNat bs) (hus : H us)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hpf : HSl0 s₀.mem pfo pfl pfvs) (hds : HSl0 s₀.mem dso dsl ds)
    (hct : PSlR decCN ctors cto ctl s₀.mem) (hnf : PSlR decNCN nfs nfo nfl s₀.mem) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP : List ConLeche.Expr}
    {usP : List ConLeche.Level} {ctorsP : List (ConLeche.ConstantVal × Nat)}
    {nfsP : List ConLeche.NestCtorNf}
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hpfP : Frontend.denoteEList a₀.store pfvs = some pfvsP)
    (husP : denoteLs a₀.store.lss (decI us) = some usP)
    (hdsP : Frontend.denoteEList a₀.store ds = some dsP) (hctP : dCtors a₀.store ctors = some ctorsP)
    (hnfP : nfs.mapM (dCtorNf a₀.store) = some nfsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hpw : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped pfvsP.length x) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_major_nfs"
      [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo, nfl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a₀ ∧
      PSlR decNCN (AM.res (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a₀)
        (r.headD 0) (r.tail.headD 0) s'.mem ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (tmnE_spec p hL n s₀ vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl)
    (tmn_ref hq henv hL n hn hC hA hbs hus hft hftb hpf hds hct.1 (hC.stage.lt64 hct.2) hnf hP hsh hftP
      hpfP husP hdsP hctP hnfP hformer hpw)) ?_
  rintro r s' ⟨hl', ys, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hres]; exact hR.slice, by rw [hst]; exact hR.stage, hR.grow, hR.rc, hR.abs⟩

end sims

end L.Ind

end
