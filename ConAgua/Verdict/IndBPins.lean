import ConAgua.Arena.IndT.RecCheckPins
import ConAgua.Verdict.IndBStream

/-!
# Error refinement of `target_pin_tys`, `target_major_pins` (lane `verdicts-b`, helper `ib`)
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
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
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

l_model tmpE_spec (p : Prog) (hf : p.lookup "target_major_pins" = some targetMajorPins)
  fns [hf ↦ tmpE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hq henv hcE in
/-- **`target_pin_tys`' model error claim** (`tptW_okC`'s hypotheses). -/
theorem tptE_claim (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (d xo xl : Word) (xs : List EIdx) (xsP : List ConLeche.Expr),
    StageC dn vis fe env m a → AbsOK m →
    decHL m xo.toNat xl.toNat = some xs → xo.toNat + xl.toNat < 2 ^ 64 →
    xo.toNat + xl.toNat ≤ iwTop m → Frontend.denoteEList a.store xs = some xsP →
    (∀ x ∈ xsP, ConLeche.Expr.WScoped d.toNat x) →
    ∀ e, tptE p n m vis d xo xl = .error e →
      ErrClaim (ConRon.Arena.targetPinTys V fe d.toNat xs) a e := by
  induction n with
  | zero =>
    intro m a d xo xl xs xsP hC hA hxs hb hbt hxsP hw e he
    rw [tptE.eq_def] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a d xo xl xs xsP hC hA hxs hb hbt hxsP hw e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  by_cases hxl : xl = 0
  · rw [tptE.arm1 p n m vis d xo xl hxl] at he
    cases he
  rw [tptE.arm2 p n m vis d xo xl hxl] at he
  have hpos : 1 ≤ xl.toNat := by
    rcases Nat.eq_zero_or_pos xl.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hxl
    · omega
  obtain ⟨c1, hc1⟩ : ∃ c1, xl.toNat = c1 + 1 := ⟨xl.toNat - 1, by omega⟩
  rw [hc1] at hxs
  obtain ⟨x, xs', rfl, hxs', hx⟩ := decHL_cons_r hxs
  obtain ⟨w, hw1, hw2, hw3⟩ := iwH_rdW hx (by omega)
  rw [UInt64.ofNat_toNat] at hw1
  have hxl1 : (xl - 1).toNat = c1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp; omega
  have hxo1 : (xo + 1).toNat = xo.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [hw1] at he
  obtain ⟨xP, xsP', hxP, hxsP', rfl⟩ := ConRon.Bridge.denoteEList_cons_inv hxsP
  rw [ConRon.Arena.targetPinTys]
  subst hw3
  cases h1 : callE p n "infer_type_core" [vis, d, w] m with
  | error e1 =>
    rw [h1, tptE.k_infer_type_core.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    have := hcE.inferTypeCore n (by omega) hC.stageT d w hw2 _ h1
    exact this
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, tptE.k_infer_type_core.arm1] at he
  obtain ⟨t1, a1, hrun1, hC1, hg1, -, hA1, c1', -⟩ :=
    inferC_rsim hq henv n (by omega) hC hA d w hw2 hxP (hw xP List.mem_cons_self) (r1, m1)
      (callW_of_callE h1)
  dsimp only at hC1 hg1 hA1
  refine ErrClaim.bind_right hrun1 ?_
  cases h2 : tptE p n m1 vis d (xo + 1) (xl - 1) with
  | error e2 =>
    rw [h2, tptE.k_target_pin_tys.none] at he
    cases he
    have hxs1 : decHL m1 (xo + 1).toNat (xl - 1).toNat = some xs' := by
      rw [hxo1, hxl1, decHL_grow hg1 (by omega)]; exact hxs'
    exact ih (by omega) m1 a1 d (xo + 1) (xl - 1) xs' xsP' hC1 hA1 hxs1 (by rw [hxo1, hxl1]; omega)
      (by rw [hxo1, hxl1]; have := hg1.1; omega) (ConRon.Bridge.denoteEList_ext c1'.ext _ _ hxsP')
      (fun y hy => hw y (List.mem_cons_of_mem _ hy)) _ h2
  | ok q2 =>
    rw [h2, tptE.k_target_pin_tys.arm1] at he
    cases he

include hq henv hcE in
/-- **`target_pin_tys`' error claim** (every fuel). -/
theorem targetPinTys_claim (hp : p.lookup "target_pin_tys" = some targetPinTys) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (d xo xl : Word) (xs : List EIdx)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hxs : decHL s₀.mem xo.toNat xl.toNat = some xs) (hb : xo.toNat + xl.toNat < 2 ^ 64)
    (hbt : xo.toNat + xl.toNat ≤ iwTop s₀.mem) {xsP : List ConLeche.Expr}
    (hxsP : Frontend.denoteEList a₀.store xs = some xsP)
    (hw : ∀ x ∈ xsP, ConLeche.Expr.WScoped d.toNat x) :
    CoreSpecE p n "target_pin_tys" [vis, d, xo, xl] (ConRon.Arena.targetPinTys V fe d.toNat xs) s₀ a₀ :=
  CoreSpecE.of_runs fun e hc => by
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    exact tptE_claim hq henv hcE n hn s₀.mem a₀ d xo xl xs xsP hC hA hxs hb hbt hxsP hw e
      (triple_of_callE_err (tptE_spec p hp n s₀ vis d xo xl) hc (Err.code_ne_of_cls hk0))

include hq henv hnv hcE in
/-- **`target_major_pins`' model error claim** (`tmpW_okC`'s hypotheses). -/
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
  cases h1 : callE p N "target_pin_tys" [vis, rP, UInt64.ofNat o, UInt64.ofNat l] m with
  | error e1 =>
    rw [h1, tmpE.k_target_pin_tys.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    by_cases hl0 : l = 0
    · subst hl0
      have hnil : M.ds = [] := by simpa [decHL, hslice?] using hdsm.symm
      have h1' := triple_of_callE_err (tptE_spec p hp.tpt N ⟨m, Locals.init []⟩ vis rP (UInt64.ofNat o)
        (UInt64.ofNat 0)) h1 (Err.code_ne_of_cls hk0)
      dsimp only at h1'
      rw [show (UInt64.ofNat 0 : Word) = 0 from rfl] at h1'
      exfalso
      obtain _ | N' := N
      · rw [tptE.eq_def] at h1'
        cases h1'
        exact hk0 Err.cls_outOfFuel
      · rw [tptE.arm1 p N' m vis rP _ _ rfl] at h1'
        cases h1'
    have hbnd := decHL_truncM_bound hdT hl0
    exact CoreSpecE.of_callE (targetPinTys_claim hq henv hcE hp.tpt N (by omega) ⟨m, Locals.init []⟩ a rP
      (UInt64.ofNat o) (UInt64.ofNat l) M.ds hC hA (by rw [hoo, hll]; exact hdsm)
      (by rw [hoo, hll]; have := hS.2.1; omega) (by rw [hoo, hll]; exact hbnd) hdsd hw) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, tmpE.k_target_pin_tys.arm1] at he
  obtain ⟨s1, hs1, -, h1m⟩ := triple_of_callW (targetPinTys_spec p hp.tpt (realCall p) (realCall_spec p) N
    ⟨m, Locals.init []⟩ vis rP (UInt64.ofNat o) (UInt64.ofNat l)) (callW_of_callE h1)
  subst hs1
  dsimp only at h1m
  obtain ⟨a1, hrun1, hC1, hg1, hA1⟩ : ∃ a1, (ConRon.Arena.targetPinTys V fe rP.toNat M.ds).run a = .ok ((), a1) ∧
      StageC dn vis fe env s1.mem a1 ∧ IWGrow m s1.mem ∧ AbsOK s1.mem := by
    by_cases hl0 : l = 0
    · subst hl0
      have hnil : M.ds = [] := by simpa [decHL, hslice?] using hdsm.symm
      obtain _ | N' := N
      · simp [tptW] at h1m
      rw [tptW_nil (realCall p) N' m vis rP (UInt64.ofNat o) (UInt64.ofNat 0) rfl] at h1m
      obtain ⟨-, hmm⟩ := Prod.mk.inj (Option.some.inj h1m)
      rw [← hmm]
      exact ⟨a, by rw [hnil]; rfl, hC, IWGrow.refl m, hA⟩
    have hbnd := decHL_truncM_bound hdT hl0
    obtain ⟨a1, hrun1, hC1, hg1, hA1⟩ := tptW_okC hq henv N (by omega) m s1.mem a rP _ _ r1 M.ds MP.ds
      h1m hC hA (by rw [hoo, hll]; exact hdsm) (by rw [hoo, hll]; have := hS.2.1; omega)
      (by rw [hoo, hll]; exact hbnd) hdsd hw
    exact ⟨a1, hrun1, hC1, hg1, hA1⟩
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
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h2)
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
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
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
