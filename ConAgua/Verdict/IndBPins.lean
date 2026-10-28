import ConAgua.Arena.IndT.Lift
import ConRon.Bridge.Inductives.RecCheck
import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.Arena.RecClassSpec.ReadProg
import ConAgua.Arena.RecGenSpec.CkcW
import ConAgua.Arena.RecGenSpec.DecCIIndCv
import ConAgua.Verdict.DeclValE
import ConAgua.Verdict.VCtx
import ConAgua.Arena.RecCheckSpec.RcLook
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree

/-!
# `target_pin_tys` (one model and one refinement for both outcomes), `target_major_pins`' error claim

`tptE` (`l_model … unified`): `infer_type_core` through its run, the recursion through the model.
`tpt_ref` refines `targetPinTys` for both outcomes; its ok half is `targetPinTys_refinesC` and
`target_major_pins`' ok refinement (`tmpW_okC`, through the run), its error half
`target_major_pins`' error claim (`tmpE_claim`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tptE_spec (p : Prog) (hf : p.lookup "target_pin_tys" = some targetPinTys)
  fns [hf ↦ tptE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] unified

l_model tmpE_spec (p : Prog) (hf : p.lookup "target_major_pins" = some targetMajorPins)
  fns [hf ↦ tmpE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

/-- What `target_pin_tys` gives besides the twin's run (from `m`): the stage invariant, the growth,
the abstraction memos. -/
structure TptPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hq henv in
/-- **`target_pin_tys` refines `targetPinTys .verified`, both outcomes** (twin side: con-ron's
`targetPinTys_spec`'s proof): `inferTypeCore` (`inferC_rsim`, the core stubs' claim), then the
tail. -/
theorem tpt_ref (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ {m : Mem} {a : AState} {d xo xl : Word} {xs : List EIdx} {xsP : List ConLeche.Expr},
    StageC dn vis fe env m a → AbsOK m → HSl0 m xo xl xs →
    Frontend.denoteEList a.store xs = some xsP → (∀ x ∈ xsP, ConLeche.Expr.WScoped d.toNat x) →
    RefE (VerdictCtx p) (tptE p n m vis d xo xl) (ConRon.Arena.targetPinTys V fe d.toNat xs) a
      (fun v _ a' => TptPost dn vis fe env m v.2 a') := by
  induction n with
  | zero =>
    intro m a d xo xl xs xsP hC hA hxs hxsP hw
    rw [tptE.eq_def]
    exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a d xo xl xs xsP hC hA hxs hxsP hw
  by_cases hxl : xl = 0
  · rw [tptE.arm1 p n m vis d xo xl hxl]
    have : xs = [] := by have := hxs.len; rw [hxl] at this; simpa using this
    subst this
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, hA⟩
  rw [tptE.arm2 p n m vis d xo xl hxl]
  have hbt : xo.toNat + xl.toNat ≤ iwTop m := hxs.2.resolve_left hxl
  have hb : xo.toNat + xl.toNat < 2 ^ 64 := StageR.lt64 hC.stage hbt
  have hpos : 1 ≤ xl.toNat := by
    rcases Nat.eq_zero_or_pos xl.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hxl
    · omega
  obtain ⟨c1, hc1⟩ : ∃ c1, xl.toNat = c1 + 1 := ⟨xl.toNat - 1, by omega⟩
  have hxs0 := hxs.1
  rw [hc1] at hxs0
  obtain ⟨x, xs', rfl, hxs', hx⟩ := decHL_cons_r hxs0
  obtain ⟨w, hw1, hw2, hw3⟩ := iwH_rdW hx (by omega)
  rw [UInt64.ofNat_toNat] at hw1
  have hxl1 : (xl - 1).toNat = c1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp; omega
  have hxo1 : (xo + 1).toNat = xo.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [hw1]
  obtain ⟨xP, xsP', hxP, hxsP', rfl⟩ := ConRon.Bridge.denoteEList_cons_inv hxsP
  rw [ConRon.Arena.targetPinTys]
  subst hw3
  cases h1 : callE p n "infer_type_core" [vis, d, w] m with
  | error e1 =>
    rw [tptE.k_infer_type_core.none]
    exact RefE.bind_left fun hV => hV.core.inferTypeCore n (by omega) hC.stageT d w hw2 _ h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [tptE.k_infer_type_core.arm1]
  obtain ⟨t1, a1, hrun1, hC1, hg1, -, hA1, c1', -⟩ :=
    inferC_rsim hq henv n (by omega) hC hA d w hw2 hxP (hw xP List.mem_cons_self) (r1, m1)
      (callW_of_callE h1)
  dsimp only at hC1 hg1 hA1
  refine RefE.bind_right hrun1 ?_
  have hxs1 : HSl0 m1 (xo + 1) (xl - 1) xs' :=
    ⟨by rw [hxo1, hxl1, decHL_grow hg1 (by omega)]; exact hxs',
      .inr (by rw [hxo1, hxl1]; have := hg1.1; omega)⟩
  have hr := ih (by omega) hC1 hA1 hxs1 (ConRon.Bridge.denoteEList_ext c1'.ext _ _ hxsP')
    (fun y hy => hw y (List.mem_cons_of_mem _ hy))
  rcases h2 : tptE p n m1 vis d (xo + 1) (xl - 1) with e2 | ⟨v2, m2⟩ <;> rw [h2] at hr
  · rw [tptE.k_target_pin_tys.none]; exact hr
  rw [tptE.k_target_pin_tys.arm1]
  obtain ⟨y, a2, run2, hR⟩ := hr
  exact RefE.ret run2 ⟨hR.stage, hg1.trans hR.grow, hR.abs⟩

include hq henv in
/-- **`target_pin_tys` refines `targetPinTys .verified`** under `StageC` (`tpt_ref`'s ok half; the
knot's `infer_type_core`; the parameters' denotations and scoping as con-ron's `targetPinTys_spec`
asks). -/
@[refines ConRon.Arena.targetPinTys]
theorem targetPinTys_refinesC (hp : p.lookup "target_pin_tys" = some targetPinTys) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (d xo xl : Word) (xs : List EIdx)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hxs : decHL s₀.mem xo.toNat xl.toNat = some xs)
    (hbt : xo.toNat + xl.toNat ≤ iwTop s₀.mem) {xsP : List ConLeche.Expr}
    (hxsP : Frontend.denoteEList a₀.store xs = some xsP)
    (hw : ∀ x ∈ xsP, ConLeche.Expr.WScoped d.toNat x) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_pin_tys" [vis, d, xo, xl]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetPinTys V fe d.toNat xs) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.targetPinTys V fe d.toNat xs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (tptE_spec p hp n s₀ vis d xo xl)
    (tpt_ref hq henv n hn hC hA (HSl0.of hxs hbt) hxsP hw)) ?_
  rintro r s' ⟨hl, _, a', run, hR⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, hR.abs⟩

include hq henv hnv hcE in
/-- **`target_major_pins`' model error claim** (`tmpW_okC`'s hypotheses; `target_pin_tys` through
`tpt_ref`). -/
theorem tmpE_claim (hp : TmpProg p) (N : Nat) (hN : N ≤ 2 ^ 62) {m : Mem} {a : AState} {rP Mp : Word}
    {M : TargetMajor} (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hM : DecB (fun m => decTM m Mp.toNat) m M)
    {MP : ConLeche.TargetMajor} (hMP : dMajor a.store M = some MP)
    (hds : MP.member = none → ∀ x ∈ MP.ds, ConLeche.Expr.WScoped rP.toNat x) :
    ∀ e, tmpE p N m vis rP Mp = .error e →
      ErrClaim (ConRon.Arena.targetMajorPins V fe rP.toNat M) a e := by
  intro e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  obtain _ | N := N
  · simp only [tmpE] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  have hS := hC.stage
  have hsz := hS.2.2.2.1
  have hM0 := hM.get (decTM_mono _)
  obtain ⟨k, hk, hmem⟩ := decTM_member hM0
  obtain ⟨hind, hlv, hdsd, -, -, -, hmemP, -, -⟩ := ConRon.Bridge.Inductives.dMajor_inv hMP
  have hrk := iwN_rdW_at (w := Mp) (k := 8) hk hsz
  rw [show UInt64.ofNat 8 = (8 : Word) from rfl] at hrk
  by_cases hk8 : rdW (m.arr64 IW) (Mp + 8) ≠ 0
  · rw [tmpE.arm1 p N m vis rP Mp hk8] at he
    cases he
  rw [tmpE.arm2 p N m vis rP Mp (by simpa using hk8)] at he
  have hk00 : k = 0 := by
    have : rdW (m.arr64 IW) (Mp + 8) = 0 := by simpa using hk8
    rw [hrk.1] at this
    have := congrArg UInt64.toNat this
    rwa [UInt64.toNat_ofNat_of_lt' hrk.2] at this
  have hmem' : M.member = none := by rw [hmem, hk00]; rfl
  have hw := hds (by rw [← hmemP, hmem'])
  obtain ⟨o, l, hoT, hlT, hdT⟩ := decTM_ds (show decTM (truncM m) Mp.toNat = some M from hM)
  obtain ⟨hoi, ho⟩ := iwN_truncM_get hoT
  obtain ⟨hli, hl⟩ := iwN_truncM_get hlT
  have hdsm : decHL m o l = some M.ds := (OMono.decHL o l).mono _ _ _ (IWGrow.refl m).truncExt hdT
  have ro := iwN_rdW_at (w := Mp) (k := 2) ho hsz
  have rl := iwN_rdW_at (w := Mp) (k := 3) hl hsz
  rw [show UInt64.ofNat 2 = (2 : Word) from rfl] at ro
  rw [show UInt64.ofNat 3 = (3 : Word) from rfl] at rl
  rw [ro.1, rl.1] at he
  have hoo := UInt64.toNat_ofNat_of_lt' ro.2
  have hll := UInt64.toNat_ofNat_of_lt' rl.2
  rw [ConRon.Arena.targetMajorPins]
  simp only [hmem']
  -- the pins of the parameters
  have hds0 : HSl0 m (UInt64.ofNat o) (UInt64.ofNat l) M.ds := by
    refine ⟨by rw [hoo, hll]; exact hdsm, ?_⟩
    by_cases hl0 : l = 0
    · exact .inl (by rw [hl0]; rfl)
    · exact .inr (by rw [hoo, hll]; exact decHL_truncM_bound hdT hl0)
  have hR1 := tpt_ref hq henv N (by omega) hC hA hds0 hdsd hw
  cases h1 : callE p N "target_pin_tys" [vis, rP, UInt64.ofNat o, UInt64.ofNat l] m with
  | error e1 =>
    rw [h1, tmpE.k_target_pin_tys.none] at he
    cases he
    exact ErrClaim.bind_left (RefE.run_err (tptE_spec p hp.tpt N ⟨m, Locals.init []⟩ vis rP _ _) trivial
      ⟨hnv, hcE⟩ hR1 h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, tmpE.k_target_pin_tys.arm1] at he
  obtain ⟨s1, rfl, -, ⟨⟩, a1, hrun1, hR⟩ :=
    RefE.run_ok (tptE_spec p hp.tpt N ⟨m, Locals.init []⟩ vis rP _ _) hR1 h1
  dsimp only at hR
  have hC1 := hR.stage
  have hg1 := hR.grow
  have hA1 := hR.abs
  obtain ⟨c1, -⟩ := ConRon.Bridge.Inductives.targetPinTys_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv rP.toNat M.ds MP.ds hw a a1 () hC.check hdsd hrun1
  refine ErrClaim.bind_right hrun1 ?_
  have hS1 := hC1.stage
  have hM1 : decTM s1.mem Mp.toNat = some M := hM.stab (decTM_mono _) s1.mem hg1
  obtain ⟨wi, hwi, hwiH, hwiE⟩ := iwH_rdW_at (w := Mp) (k := 0) (by simpa using decTM_ind hM1) hS1.2.2.2.1
  obtain ⟨wu, hwu, hwuH, hwuE⟩ := iwH_rdW_at (w := Mp) (k := 1) (decTM_lvls' hM1) hS1.2.2.2.1
  rw [show Mp + UInt64.ofNat 0 = Mp by simp] at hwi
  rw [show UInt64.ofNat 1 = (1 : Word) from rfl] at hwu
  rw [hwi, hwu] at he
  cases h2 : callE p N "intern_const" [wi, wu] s1.mem with
  | error e2 =>
    rw [h2, tmpE.k_intern_const.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h2)
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, h2m⟩ := triple_of_callW (internConst_spec p hp.cf hp.cp hp.ic N ⟨s1.mem, Locals.init []⟩ wi wu)
    (callW_of_callE h2)
  subst hs2
  dsimp only at h2m
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internConst_stage hS1 wi wu hwiH hwuH h2m
  rw [hwiE, hwuE] at hrun2
  obtain ⟨p2, hhd⟩ := ConRon.Bridge.Inductives.internConstE_run c1.ok.state
    (ConRon.Bridge.denoteN_ext hind c1.ext) (ConRon.Bridge.denoteLs_ext hlv c1.ext) hrun2
  have hA2 := ceinternW_afr h2m hA1
  have hC2 : StageC dn vis fe env s2.mem a2 := hC1.of_pstep hS2 hA2 p2
  have c2 := c1.trans (p2.toCore c1.ok)
  refine ErrClaim.bind_right (x := ConRon.Arena.internConstE M.ind M.lvls) (by unfold ConRon.Arena.internConstE; exact hrun2) ?_
  by_cases hbig : 4294967296 ≤ r2.headD 0
  · rw [h2, tmpE.k_intern_const.abort1 p N vis rP Mp r2 s2.mem hbig] at he
    cases he
    exact absurd rfl hk0
  rw [h2, tmpE.k_intern_const.arm1 p N vis rP Mp r2 s2.mem hbig] at he
  have hdH : H (r2.headD 0) := by
    have : (r2.headD 0).toNat < (4294967296 : Word).toNat :=
      Nat.lt_of_not_le fun x => hbig (UInt64.le_iff_toNat_le.mpr x)
    simpa [H] using this
  have hg12 := hg1.trans hg2
  have hts : iwTop m ≤ (m.arr64 IW).size := hS.2.1
  have e2 : rdW (s2.mem.arr64 IW) (Mp + 2) = UInt64.ofNat o := by
    rw [← ro.1]; simp only [rdW]
    rw [show (Mp + 2).toNat = Mp.toNat + 2 by rw [UInt64.toNat_add]; simp; omega, hg12.2.2.1 _ hoi]
  have e3 : rdW (s2.mem.arr64 IW) (Mp + 3) = UInt64.ofNat l := by
    rw [← rl.1]; simp only [rdW]
    rw [show (Mp + 3).toNat = Mp.toNat + 3 by rw [UInt64.toNat_add]; simp; omega, hg12.2.2.1 _ hli]
  rw [e2, e3] at he
  cases h3 : callE p N "mk_app_n_f" [r2.headD 0, UInt64.ofNat o, UInt64.ofNat l] s2.mem with
  | error e3' =>
    rw [h3, tmpE.k_mk_app_n_f.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, tmpE.k_mk_app_n_f.arm1] at he
  obtain ⟨s3, hs3, -, h3m⟩ := triple_of_callW (mknF_spec p hp.ad N ⟨s2.mem, Locals.init []⟩
    [r2.headD 0, UInt64.ofNat o, UInt64.ofNat l]) (callW_of_callE h3)
  subst hs3
  dsimp only at h3m
  have hds2 : decHL s2.mem (UInt64.ofNat o).toNat (UInt64.ofNat l).toNat = some M.ds := by
    rw [hoo, hll]; exact (OMono.decHL o l).mono _ _ _ hg12.truncExt hdT
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ := mknF_ok dn vis fe (r2.headD 0) _ _ hdH M.ds s2.mem s3.mem a2 r3 h3m
    ⟨hS2, hds2⟩
  have hrun3' : (ConRon.Arena.mkAppN (decE (r2.headD 0)) M.ds) a2 = .ok (x3, a3) := hrun3
  obtain ⟨p3, happ⟩ := ConRon.Bridge.Inductives.mkAppN_run M.ds MP.ds c2.ok.state hhd
    (ConRon.Bridge.denoteEList_ext c2.ext _ _ hdsd) hrun3'
  have hrun3r : (ConRon.Arena.mkAppN (decE (r2.headD 0)) M.ds).run a2 = .ok (x3, a3) := hrun3
  have hA3 := mknF_afr h3m hA2
  have hC3 : StageC dn vis fe env s3.mem a3 := hC2.of_pstep hS3 hA3 p3
  refine ErrClaim.bind_right (x := ConRon.Arena.mkAppN (decE (r2.headD 0)) M.ds) hrun3r ?_
  cases h4 : callE p N "infer_type_core" [vis, rP, r3.headD 0] s3.mem with
  | error e4 =>
    rw [h4, tmpE.k_infer_type_core.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    have := hcE.inferTypeCore N (by omega) hC3.stageT rP (r3.headD 0) hx3.1 _ h4
    rw [← hx3.2]
    exact this
  | ok q4 =>
    rw [h4, tmpE.k_infer_type_core.arm1] at he
    cases he

include hq henv hnv hcE in
/-- **`target_major_pins`' error claim** (every fuel). -/
theorem targetMajorPins_claim (hp : TmpProg p) (N : Nat) (hN : N ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (rP Mp : Word) (M : TargetMajor) (hC : StageC dn vis fe env s₀.mem a₀)
    (hA : AbsOK s₀.mem) (hM : DecB (fun m => decTM m Mp.toNat) s₀.mem M)
    {MP : ConLeche.TargetMajor} (hMP : dMajor a₀.store M = some MP)
    (hds : MP.member = none → ∀ x ∈ MP.ds, ConLeche.Expr.WScoped rP.toNat x) :
    CoreSpecE p N "target_major_pins" [vis, rP, Mp] (ConRon.Arena.targetMajorPins V fe rP.toNat M) s₀ a₀ :=
  CoreSpecE.of_runs fun e hc => by
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    exact tmpE_claim hq henv hnv hcE hp N hN hC hA hM hMP hds e
      (triple_of_callE_err (tmpE_spec p hp.tmp N s₀ vis rP Mp) hc (Err.code_ne_of_cls hk0))

end sims

end L.Ind
