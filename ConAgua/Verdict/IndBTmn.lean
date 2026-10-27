import ConAgua.Arena.IndT.RecCheckTmn
import ConAgua.Verdict.IndBTcm
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

/-!
# Error refinement of `target_major_nfs` (lane `verdicts-b`, helper `ib`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs dShape dCtors dCtorNf)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tmnE_spec (p : Prog) (hf : p.lookup "target_major_nfs" = some targetMajorNfs)
  fns [hf ↦ tmnE]
  specs [callE_spec p n "target_major_nfs"] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors


/-- `target_class_match`'s error claim at every fuel (the claim at `n + 1`; at fuel `0` the call
fails with class `0`). -/
theorem tcm_claimA {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
    (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p) (L : TcmLook p)
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (q fto ftl pfo pfl us dso dsl lvls edso edsl : Word)
    (bs : BlockShape) (formerTys pfvs ds eds : List EIdx) (hC : StageC dn vis fe env s₀.mem a₀)
    (hA : AbsOK s₀.mem) (hbs : BSOK s₀.mem q.toNat bs) (hus : H us) (hlv : H lvls)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hpf : HSl0 s₀.mem pfo pfl pfvs) (hds : HSl0 s₀.mem dso dsl ds)
    (heds : HSl0 s₀.mem edso edsl eds) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP edsP : List ConLeche.Expr}
    {usP lvlsP : List ConLeche.Level}
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hpfP : Frontend.denoteEList a₀.store pfvs = some pfvsP)
    (husP : denoteLs a₀.store.lss (decI us) = some usP)
    (hdsP : Frontend.denoteEList a₀.store ds = some dsP)
    (hlvP : denoteLs a₀.store.lss (decI lvls) = some lvlsP)
    (hedsP : Frontend.denoteEList a₀.store eds = some edsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hpw : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped pfvsP.length x) :
    CoreSpecE p n "target_class_match" [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, lvls, edso, edsl]
      (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds) s₀ a₀ := by
  cases n with
  | zero => exact CoreSpecE.zero _ _ _ _ _ _
  | succ n =>
    exact tcm_claim hq henv hnv hcE L n (by omega) s₀ a₀ q fto ftl pfo pfl us dso dsl lvls edso edsl bs
      formerTys pfvs ds eds hC hA hbs hus hlv hft hftb hpf hds heds hP hsh hftP hpfP husP hdsP hlvP hedsP
      hformer hpw

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hq henv hnv hcE in
/-- **`target_major_nfs`' model error claim** (`tmnW_okC`'s hypotheses; the recursion is the
model's own). -/
theorem tmnE_claim (L : TmnLook p) (n : Nat) (hn : n ≤ 2 ^ 62) : ∀ {m : Mem} {a : AState}
    {q fto ftl pfo pfl us dso dsl cto ctl nfo nfl : Word}
    {bs : BlockShape} {formerTys pfvs ds : List EIdx} {ctors : List (IConstantVal × Nat)}
    {nfs : List NestCtorNf} {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP : List ConLeche.Expr}
    {usP : List ConLeche.Level} {ctorsP : List (ConLeche.ConstantVal × Nat)}
    {nfsP : List ConLeche.NestCtorNf},
    StageC dn vis fe env m a → AbsOK m → BSOK m q.toNat bs → H us →
    decHL m fto.toNat ftl.toNat = some formerTys → fto.toNat + ftl.toNat ≤ iwTop m →
    HSl0 m pfo pfl pfvs → HSl0 m dso dsl ds → PSlR decCN ctors cto ctl m → PSlR decNCN nfs nfo nfl m →
    RcMR m →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    Frontend.denoteEList a.store pfvs = some pfvsP → denoteLs a.store.lss (decI us) = some usP →
    Frontend.denoteEList a.store ds = some dsP → dCtors a.store ctors = some ctorsP →
    nfs.mapM (dCtorNf a.store) = some nfsP →
    (∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t) →
    (∀ x ∈ pfvsP, ConLeche.Expr.WScoped pfvsP.length x) →
    ∀ e, callE p n "target_major_nfs" [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo, nfl] m = .error e →
      ErrClaim (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a e := by
  induction n with
  | zero =>
    intro m a q fto ftl pfo pfl us dso dsl cto ctl nfo nfl bs formerTys pfvs ds ctors nfs pP
      formerTysP pfvsP dsP usP ctorsP nfsP hC hA hbs hus hft hftb hpf hds hct hnf hP hsh hftP hpfP
      husP hdsP hctP hnfP hformer hpw e hc'
    obtain ⟨e', he', h0⟩ := callE_zero p "target_major_nfs"
      [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo, nfl] m
    rw [hc'] at he'
    cases he'
    exact ErrClaim.of_cls0 h0
  | succ n ih =>
  intro m a q fto ftl pfo pfl us dso dsl cto ctl nfo nfl bs formerTys pfvs ds ctors nfs pP
    formerTysP pfvsP dsP usP ctorsP nfsP hC hA hbs hus hft hftb hpf hds hct hnf hP hsh hftP hpfP
    husP hdsP hctP hnfP hformer hpw e hc'
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have he := triple_of_callE_err (tmnE_spec p L.tmn (n + 1) ⟨m, Locals.init []⟩ vis q fto ftl pfo pfl us dso dsl
    cto ctl nfo nfl) hc' (Err.code_ne_of_cls hk0)
  have hS := hC.stage
  by_cases hl : nfl = 0
  · rw [tmnE.arm1 p n m vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl hl] at he
    cases he
  rw [tmnE.arm2 p n m vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl hl] at he
  have hsz := hS.2.2.2.1
  obtain ⟨nf, nfs', rfl, hnf0, hnf'⟩ := hnf.uncons hl hsz
  obtain ⟨nfP, nfsP', rfl, hnfP, hnfsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hnfP
  rw [ConRon.Arena.targetMajorNfs]
  cases h1 : callE p n "target_major_nfs" [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo + 1, nfl - 1] m with
  | error e1 =>
    rw [h1, tmnE.k_target_major_nfs.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    exact ih (by omega) hC hA hbs hus hft hftb hpf hds hct hnf' hP hsh hftP hpfP husP hdsP hctP hnfsP'
      hformer hpw _ h1
  | ok q1 =>
  obtain ⟨rr, m1⟩ := q1
  rw [h1, tmnE.k_target_major_nfs.arm1] at he
  obtain ⟨s1, hs1, -, h1m⟩ := triple_of_callW (tmn_spec p L (realCall p) (realCall_spec p) n
    ⟨m, Locals.init []⟩ vis q fto ftl pfo pfl us dso dsl cto ctl (nfo + 1) (nfl - 1)) (callW_of_callE h1)
  subst hs1
  dsimp only at h1m
  obtain ⟨ys, a1, run1, hys, hC1, hg1, hP1, hA1⟩ := tmnW_okC hq henv n (by omega) h1m hC hA hbs hus hft hftb hpf hds
    hct hnf' hP hsh hftP hpfP husP hdsP hctP hnfsP' hformer hpw
  obtain ⟨c1, -⟩ := ConRon.Bridge.Inductives.targetMajorNfs_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv bs pP formerTys pfvs formerTysP pfvsP (decI us) usP ds dsP ctors ctorsP hformer hpw nfs'
    nfsP' a a1 ys hC.check ⟨hsh, hftP, hpfP, husP, hdsP, hctP, hnfsP'⟩ run1
  refine ErrClaim.bind_right run1 ?_
  have hS1 := hC1.stage
  have hnfo : nfo.toNat < iwTop m := by
    have := hnf.2; have := (slice_step hl (hS.lt64 hnf.2)).2.2; omega
  have hE : rdW (s1.mem.arr64 IW) nfo = rdW (m.arr64 IW) nfo := by
    simp only [rdW]; rw [hg1.2.2.1 _ hnfo]
  generalize hEe : rdW (m.arr64 IW) nfo = ee at hE hnf0
  rw [hE] at he
  have hnf1 : DecB (fun m' => decNCN m' ee.toNat) s1.mem nf := hnf0.grow (decNCN_mono _) hg1
  have hsz1 := hS1.2.2.2.1
  obtain ⟨hcH, hcD, hlH, hlD, hdsl⟩ := decNCN_fields hnf1 hsz1
  have hct1 := hct.grow (fun q => decCN_mono q) hg1
  cases h2 : callE p n "ctors_have_name" [cto, ctl, rdW (s1.mem.arr64 IW) ee] s1.mem with
  | error e2 =>
    rw [h2, tmnE.k_ctors_have_name.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, h2m⟩ := triple_of_callW (ctorsHaveName_spec p L.chn n ⟨s1.mem, Locals.init []⟩ cto ctl
    (rdW (s1.mem.arr64 IW) ee)) (callW_of_callE h2)
  subst hs2
  dsimp only at h2m
  obtain ⟨hm2, h2m⟩ := h2m
  obtain ⟨hany, -⟩ := chnW_ok n s1.mem cto ctl _ (r2.headD 0) ctors h2m (hct1.1.get (OMono.decPL decCN_mono _ _)) hcH
    (hS1.lt64 hct1.2)
  rw [hcD] at hany
  by_cases hh : r2.headD 0 = 0
  · rw [h2, tmnE.k_ctors_have_name.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh] at he
    cases he
  rw [h2, tmnE.k_ctors_have_name.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh] at he
  rw [hm2] at he
  have ht : ctors.any (fun c => c.1.name == nf.ctor) = true := by rw [← hany]; simpa using hh
  refine ErrClaim.ite_pos (c := (ctors.any fun x => x.fst.name == nf.ctor) = true) ht ?_
  obtain ⟨-, hlvP, hedP, -⟩ := ConRon.Bridge.Inductives.RC.dCtorNf_inv
    (ConRon.Bridge.Inductives.dCtorNf_ext c1.ext _ _ hnfP)
  cases h3 : callE p n "target_class_match" [vis, q, fto, ftl, pfo, pfl, us, dso, dsl,
      rdW (s1.mem.arr64 IW) (ee + 1), rdW (s1.mem.arr64 IW) (ee + 2), rdW (s1.mem.arr64 IW) (ee + 3)] s1.mem with
  | error e3 =>
    rw [h3, tmnE.k_target_class_match.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    have := CoreSpecE.of_callE (tcm_claimA hq henv hnv hcE L.tcm n (by omega) ⟨s1.mem, Locals.init []⟩ a1 q fto ftl
      pfo pfl us dso dsl _ _ _ bs formerTys pfvs ds _ hC1 hA1 (hbs.grow hg1) hus hlH
      (by rw [decHL_grow hg1 hftb]; exact hft) (by dsimp only; have := hg1.1; omega)
      (hpf.grow hg1) (hds.grow hg1) hdsl hP1
      (ConRon.Bridge.Inductives.dShape_ext c1.ext _ _ hsh) (denoteEList_ext c1.ext _ _ hftP)
      (denoteEList_ext c1.ext _ _ hpfP) (ConRon.Bridge.denoteLs_ext husP c1.ext)
      (denoteEList_ext c1.ext _ _ hdsP) (by rw [hlD]; exact hlvP) hedP hformer hpw) h3
    rwa [hlD] at this
  | ok q3 =>
  obtain ⟨rk, m3⟩ := q3
  by_cases hk : rk.headD 0 = 0
  · rw [h3, tmnE.k_target_class_match.arm1 _ _ _ _ _ _ _ hk] at he
    cases he
  rw [h3, tmnE.k_target_class_match.arm2 _ _ _ _ _ _ _ hk] at he
  cases h4 : callE p n "sl_cons" [ee, rr.headD 0, rr.tail.headD 0] m3 with
  | error e4 =>
    rw [h4, tmnE.k_sl_cons.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h4)
  | ok q4 =>
    rw [h4, tmnE.k_sl_cons.arm1] at he
    cases he

include hq henv hnv hcE in
/-- **`target_major_nfs`' error claim** (all fuels; `tcm_claimA`'s and `tmn_spec`'s shapes). -/
theorem targetMajorNfs_claim (L : TmnLook p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
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
    CoreSpecE p n "target_major_nfs" [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo, nfl]
      (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) s₀ a₀ :=
  CoreSpecE.of_runs fun e hc =>
    tmnE_claim hq henv hnv hcE L n hn hC hA hbs hus hft hftb hpf hds hct hnf hP hsh hftP hpfP husP hdsP
      hctP hnfP hformer hpw e hc

end sims

end L.Ind
