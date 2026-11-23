module

public import ConAgua.Arena.IndT.Sum2
import ConAgua.Arena.IndT.Install1
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndInstallSpec.InstallSimCall
import ConAgua.Arena.IndInstallSpec.Cons
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.IndRealAbsSim
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.RecGenSpec.ClassFeR
import ConAgua.Arena.RefWalk
import ConAgua.Arena.StageC
import ConAgua.Checker.NoVerdictTree
import ConLeche.Verify.BridgeWfImp
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Inductives.SumInstall
public import ConAgua.Arena.IndInstallSpec.InstallRec2Tele
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndInstall
public import ConAgua.Verdict.DeclValsE
public import ConRon.Bridge.Checker.Hyp
public import ConRon.Bridge.Inductives.Records
import ConAgua.L.WordOff
import ConAgua.Arena.RecClassSpec.MjProg

@[expose] public section

/-!
# `checkBlockTele`, `checkBlockTeles` under `StageC` (lane `indstaget`)

`check_block_tele`'s model, from `StageC` and con-ron's preconditions of `checkBlockTele_specF`
(the member denotes, the environment denotes), its twin side transcribed from that spec's proof:
`checkConstantVal` (`ccv_ref` through its run, `checkConstantVal_bridge` on its run for the
`CoreStep` and the stored type's closure), `checkSumTele` (`ct_ref` through its run, con-ron's
`checkSumTele_spec` on its run for the answer's denotation), `stripPis` (`stripPis_pstep`), the
sort's intern (`internSortE_run`). `check_block_teles` walks the members (`dMember_ext`). Both have one model
(`cbtE`, `cbtsE`: `l_model … unified`) and one refinement (`cbt_ref`, `cbts_ref`: `RefE` under
`CtsG`, what `check_constant_val`'s and `check_sum_tele`'s refinements assume) for both outcomes,
walked by the rules of `RefWalk.lean` under the install family's package `InsAt`.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- `TeleOut` under `StageC`: the checked former below the tops, its result sort a handle. -/
def TeleOutC (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (r : List Word) (x : IConstantVal × LIdx) (m' : Mem) (a' : AState) : Prop :=
  StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ decCVp m' (r.headD 0).toNat = some x.1 ∧
    CVExt m' (r.headD 0).toNat ∧ H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = x.2

theorem TeleOutC.toR {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} {m : Mem} {r : List Word} {x : IConstantVal × LIdx} {m' : Mem}
    {a' : AState} (h : TeleOutC dn vis fe env m r x m' a') : TeleOut dn vis fe m r x m' a' :=
  ⟨h.1.stage, h.2⟩

/-- **`check_block_tele`'s unified model**: `check_constant_val` and `check_sum_tele` through their
runs, `strip_pis` and `intern_sort` (outside the verdict closure) lifted. -/
l_model cbtE_spec (p : Prog) (hf : p.lookup "check_block_tele" = some checkBlockTele)
  fns [hf ↦ cbtE] specs [callW_spec p n "strip_pis", callW_spec p n "intern_sort"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`check_block_teles`' unified model**: every member through `cbtE`, the `rec2`s and `sl_cons`es
(outside the verdict closure) lifted. -/
l_model cbtsE_spec (p : Prog) (h1 : p.lookup "check_block_tele" = some checkBlockTele)
  (hf : p.lookup "check_block_teles" = some checkBlockTeles)
  fns [hf ↦ cbtsE] specs [cbtE_spec p h1 n, callW_spec p n "rec2", callW_spec p n "sl_cons"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `check_sum_tele`'s lookups, as its model takes them. -/
theorem CstProg.ctProg {p : Prog} (hP : CstProg p) : CtProg p := ⟨hP.strip, hP.view, hP.tele⟩

/-- What `check_block_tele` gives besides the checked former and its sort `x` (from `m`, `a`): the
former's layout (`TeleOutC`), `AbsOK`, the core step. -/
structure TelePost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (r : List Word) (x : IConstantVal × LIdx) (m' : Mem) (a' : AState) : Prop where
  out : TeleOutC dn vis fe env m r x m' a'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep env fe a a'

/-- What `check_block_teles` gives besides the checked formers `x` (from `m`, `a`): the stage, the
growth, the formers' slice, `AbsOK`, the core step. -/
structure TelesPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (r : List Word) (x : List (IConstantVal × LIdx)) (m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  teles : PSlR decTele x (r.headD 0) (r.tail.headD 0) m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep env fe a a'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : CcvProg p) (hcr : CrfF p) (hCS : CcvSims p dn)
  (hApd : ApdF p) (hCrk : CrKeep p)

include hq henv hV hcr hCS hApd hCrk in
/-- **`check_block_tele` refines `checkBlockTele`, both outcomes** under `StageC` (twin side:
con-ron's `checkBlockTele_specF`'s proof): `check_constant_val` and `check_sum_tele` through their
runs (their refinements `ccv_ref`, `ct_ref`), `strip_pis` and `intern_sort` (outside the verdict closure)
lifted. -/
theorem cbt_ref (hP : CstProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {nP ms : Word} {msh : MemberShape}
    (hC : StageC dn vis fe env m a) (hms : MemOK m ms.toNat msh) (hA : AbsOK m)
    {msP : ConLeche.MemberShape} (hmsP : ConRon.Bridge.Inductives.dMember a.store msh = some msP) :
    RefE (VerdictCtxU p) (cbtE p (n + 1) m vis nP ms) (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a
      (fun v x a' => TelePost dn vis fe env m a v.1 x v.2 a') := by
  have hS := hC.stage
  obtain ⟨hcvP, -, -⟩ := ConRon.Bridge.Inductives.dMember_inv hmsP
  obtain ⟨hmsB, hcx⟩ := hms
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨⟨c, hc, hcv⟩, -, hni, -⟩ := decMS_some (m := truncM m) hmsB
  obtain ⟨hw0, hcb, hmsl⟩ := partsIwRd hc rfl
  obtain ⟨hw1, hnb, -⟩ := partsIwRd hni (w := ms + 1) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨-, hcN⟩ := L.Ind.iwN_truncM_some hc
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  have hcvx : CVExt m (UInt64.ofNat c : Word).toNat := by rw [hc']; exact hcx c hcN
  have hcvm : decCVp m (UInt64.ofNat c : Word).toNat = some msh.cvT := by
    rw [hc']; exact DecB.get (OMono.decCVp _) hcv
  by_cases hov : nP + UInt64.ofNat msh.nIdx < nP
  · rw [cbtE.abort1 p n m vis nP ms (by rw [hw1]; exact hov)]; exact RefE.of_cls0 rfl
  rw [cbtE.arm1 p n m vis nP ms (by rw [hw1]; exact hov), hw0, hw1]
  have hk : (nP + UInt64.ofNat msh.nIdx).toNat = nP.toNat + msh.nIdx := by
    rw [L.toNat_add_of_not_lt hov, UInt64.toNat_ofNat_of_lt' hnb]
  unfold ConRon.Arena.checkBlockTele
  -- `check_constant_val`
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => rfl) (checkConstantVal_specE p hV n _ vis _ 0 0 0)
    (fun hG => hG.nv) id (ccv_ref (allow := 0) (allowRd := 0) (allowSorry := 0) hV hq hApd hCrk hcr hCS hn hC.stageT
      (rec2DecCV_erecP hcvm hcvx) hcvP hA.cr.crOK)
    fun r1 s1 u1 a1 _ _ hr1 hP1 => ?_
  dsimp only [cbtE.k_check_constant_val]
  obtain ⟨c1, F₁, hF₁⟩ := ConRon.Bridge.checkConstantVal_bridge ConRon.Bridge.CoreSpec.of_core
    hC.check henv hcvP hr1
  have k1 : InsAt dn vis fe env m a s1.mem a1 := ⟨StageC.of_T hP1.stage c1.ok, hP1.abs hA, hP1.grow, c1⟩
  have hcA := ConRon.Bridge.denoteCV_ext hcvP c1.ext
  have hw1' : ConLeche.Expr.WScoped 0 msP.cvT.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar (ConLeche.checkConstantVal_typeWF hF₁).1
  have hcvm1 : decCVp s1.mem (UInt64.ofNat c : Word).toNat = some msh.cvT := by
    rw [hc']; exact DecB.stab (OMono.decCVp _) hcv s1.mem k1.grow
  -- `check_sum_tele`
  have hR2 := ct_ref (p := p) (dn := dn) (vis := vis) s1.mem a1 (nP + UInt64.ofNat msh.nIdx) _
    msh.cvT k1.stage hcvm1 k1.abs hcA
  rw [hk] at hR2
  refine RefE.bindRun (s₀ := ⟨s1.mem, Locals.init []⟩) (fun _ => rfl)
    (ctE_spec p hP.ctProg n _ _ _) (fun hG => hG.nv) (fun _ => trivial) hR2
    fun r2 s2 x2 a2 _ _ hr2 hP2 => ?_
  dsimp only [cbtE.k_check_sum_tele]
  obtain ⟨p2, sP, -, h2a, h2b⟩ := ConRon.Bridge.Inductives.checkSumTele_spec (nP.toNat + msh.nIdx)
    msh.cvT msP.cvT a1 a2 _ k1.stage.check.state hcA hr2
  have k2 : InsAt dn vis fe env s1.mem a1 s2.mem a2 :=
    ⟨hP2.stage, hP2.abs, hP2.grow, p2.toCore k1.stage.check⟩
  have hcv2 := installCvDecB hP2.cv (CVExt.of_dec hP2.cv)
  obtain ⟨htyl, htye⟩ := partsCVType hcv2 (w := r2.headD 0) rfl
  -- `strip_pis`
  refine RefE.bindLift (fun _ => rfl) fun r3 m3 h3 => ?_
  have hs3 := stripF_of_callW hP.strip h3
  obtain ⟨x3, a3, hr3, hS3, hg3, hd3⟩ :=
    stripF_pis_ok vis fe (nP + UInt64.ofNat msh.nIdx) _ htyl s2.mem m3 a2 r3 hs3 k2.stage.stage
  rw [hk, htye] at hr3
  obtain ⟨ha3, -⟩ := ConRon.Bridge.Inductives.stripPis_pstep k2.stage.check.state
    (ConRon.Bridge.denoteCV_type h2a) hr3
  subst ha3
  have k3 := InsAt.pstep k2.stage hS3 (stripF_afr hs3 k2.abs) hg3 (PStep.refl k2.stage.check.state)
  refine ⟨_, _, hr3, ?_⟩
  dsimp only [cbtE.k_strip_pis]
  cases x3 with
  | none => exact RefE.abort0 rfl fun h => absurd hd3 h
  | some bb =>
  obtain ⟨bs, body⟩ := bb
  obtain ⟨h1', -, hb32, hbe⟩ := hd3
  refine RefE.pass (by rw [h1']; decide) ?_
  rw [L.drop_three] at hb32 hbe
  -- `intern_sort`
  refine RefE.bindLift (fun _ => rfl) fun r4 m4 h4 => ?_
  obtain ⟨srt, a4, hr4, hS4, hg4, hsrt, hf4⟩ := installSortSim hP n hS3 hP2.sort32 r4 m4 h4
  rw [hP2.sort] at hr4
  obtain ⟨p4, -⟩ := ConRon.Bridge.Inductives.internSortE_run k3.stage.check.state h2b hr4
  have k4 := InsAt.pstep k3.stage hS4 (hf4 k3.abs) hg4 p4
  refine ⟨_, _, hr4, ?_⟩
  dsimp only [cbtE.k_intern_sort]
  split
  rotate_left
  · exact RefE.of_cls0 rfl
  rename_i h40
  have hb : (body == srt) = true := by rw [← hbe, ← hsrt, h40, decE_eq]; exact beq_self_eq_true _
  simp only [hb, ite_true]
  have k14 := ((k1.trans k2).trans k3).trans k4
  exact RefE.ret rfl ⟨⟨k4.stage, k14.grow, hcv2.stab (OMono.decCVp _) m4 (k3.trans k4).grow,
    CVExt_grow (k3.trans k4).grow (CVExt.of_dec hP2.cv), hP2.sort32, hP2.sort⟩, k4.abs, k14.core⟩

include hq henv hV hcr hCS hApd hCrk in
/-- **`check_block_tele` refines `checkBlockTele`** under `StageC` (the knot's core calls; the
member's denotation as con-ron's `checkBlockTele_specF` asks): the checked former below the tops,
its result sort a handle. -/
@[refines ConRon.Arena.checkBlockTele]
theorem checkBlockTele_refinesC (hP : CstProg p)
    (hp : p.lookup "check_block_tele" = some checkBlockTele) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (nP ms : Word) (msh : MemberShape)
    (hC : StageC dn vis fe env s₀.mem a₀) (hms : MemOK s₀.mem ms.toNat msh) (hA : AbsOK s₀.mem)
    {msP : ConLeche.MemberShape} (hmsP : ConRon.Bridge.Inductives.dMember a₀.store msh = some msP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_tele" [vis, nP, ms]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a₀ ∧
      TeleOutC dn vis fe env s₀.mem r (AM.res (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a₀) s'.mem
        (AM.st (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a₀) ∧ AbsOK s'.mem ∧
      ConRon.Bridge.CoreStep env fe a₀ (AM.st (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a₀);
      ⊤⦄ := by
  refine triple_post (RefE.triple (cbtE_spec p hp (n + 1) s₀ vis nP ms)
    (cbt_ref hq henv hV hcr hCS hApd hCrk hP n hn hC hms hA hmsP)) ?_
  rintro _r s' ⟨hl, x, a', hrun, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hR.out, hR.abs, by rw [hst]; exact hR.core⟩

include hq henv hV hcr hCS hApd hCrk in
/-- **`check_block_teles` refines `checkBlockTeles`, both outcomes** under `StageC` (twin side:
con-ron's `checkBlockTeles_specF`'s proof; induction on the fuel): every member by `cbt_ref`, the
`rec2`s and `sl_cons`es (outside the verdict closure) lifted. -/
theorem cbts_ref (hP : InstProg p) (nP : Word) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (o l : Word) (mss : List MemberShape)
      (mssP : List ConLeche.MemberShape),
    StageC dn vis fe env m a → MemsOK m o l mss → AbsOK m →
    mss.mapM (ConRon.Bridge.Inductives.dMember a.store) = some mssP →
    RefE (VerdictCtxU p) (cbtsE p n m vis nP o l) (ConRon.Arena.checkBlockTeles V fe nP.toNat mss) a
      (fun v x a' => TelesPost dn vis fe env m a v.1 x v.2 a') := by
  induction n with
  | zero => intros; rw [cbtsE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a o l mss mssP hC hms hA hmssP
  by_cases hl : l = 0
  · rw [cbtsE.arm1 p n m vis nP o l hl]
    have : mss = [] := by
      have h := hms.1.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, PSlR.nil decTele m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  obtain ⟨q, x, rest, rfl, hw, hqb, hmok, hrest⟩ := hms.cons hl
  obtain ⟨xP, restP, rfl, hxP, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmssP
  rw [cbtsE.arm2 p n m vis nP o l hl, hw]
  unfold ConRon.Arena.checkBlockTeles
  rcases n with _ | k
  · rw [cbtE.eq_1, cbtsE.k_check_block_tele.none]; exact RefE.of_cls0 Err.cls_outOfFuel
  -- the member's former
  refine RefE.bindE (fun _ => cbtsE.k_check_block_tele.none ..) id
    (cbt_ref hq henv hV hcr hCS hApd hCrk hP.toCstProg k (by omega) hC hmok hA hxP (nP := nP))
    fun ⟨r1, m1⟩ x1 a1 _ hT1 => ?_
  rw [cbtsE.k_check_block_tele.arm1]
  -- `rec2` (L only)
  refine RefE.onlySim (fun _ => cbtsE.k_rec2.none ..) (fun _ _ h => h) fun r2 m2 h2 => ?_
  rw [cbtsE.k_rec2.arm1]
  obtain ⟨hS2, hg2, hd2, -⟩ := installRec2Tele hP (k + 1) hT1.out.toR h2
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (rec2_specW p hP.alloc (k + 1) hP.rec2 _ _ _) h2
  have hA2 := recW_afr hW hT1.abs
  have k2 : InsAt dn vis fe env m a s'.mem a1 :=
    ⟨hT1.out.1.of_pstep hS2 hA2 (PStep.refl hT1.out.1.check.state), hA2, hg2, hT1.core⟩
  -- the other members' formers
  refine RefE.bindE (fun _ => cbtsE.k_check_block_teles.none ..) id
    (ih (by omega) s'.mem a1 (o + 1) (l - 1) rest restP k2.stage (hrest.grow hg2) hA2
      (ConRon.Bridge.Inductives.dMember_ext.list k2.core.ext _ _ hrestP))
    fun ⟨r3, m3⟩ xs a3 _ hT3 => ?_
  rw [cbtsE.k_check_block_teles.arm1]
  -- `sl_cons` (L only)
  refine RefE.onlySim (fun _ => cbtsE.k_sl_cons.none ..) (fun _ _ h => h) fun r4 m4 h4 => ?_
  rw [cbtsE.k_sl_cons.arm1]
  obtain ⟨s4, rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (slCons_specW p hP.alloc hP.copy hP.cons (k + 1) _ _ _ _) h4
  obtain ⟨hS4, hg4, hd4, htop4⟩ := partsConsPL decTele_mono hW hT3.stage.stage hT3.teles.2 hT3.teles.1
    (hd2.grow (decTele_mono _) hT3.grow)
  have hA4 := consW_afr hW hT3.abs
  exact RefE.ret rfl ⟨hT3.stage.of_pstep hS4 hA4 (PStep.refl hT3.stage.check.state),
    k2.grow.trans (hT3.grow.trans hg4), ⟨hd4, Nat.le_of_eq htop4⟩, hA4, k2.core.trans hT3.core⟩

include hq henv hV hcr hCS hApd hCrk in
/-- **`check_block_teles` refines `checkBlockTeles`** under `StageC` (the members' denotations as
con-ron's `checkBlockTeles_specF` asks): the checked formers a slice of `[cvTa, s]` records,
decoded below the tops. -/
@[refines ConRon.Arena.checkBlockTeles]
theorem checkBlockTeles_refinesC (hP : InstProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (nP o l : Word)
    (mss : List MemberShape) (hC : StageC dn vis fe env s₀.mem a₀) (hms : MemsOK s₀.mem o l mss)
    (hA : AbsOK s₀.mem) {mssP : List ConLeche.MemberShape}
    (hmssP : mss.mapM (ConRon.Bridge.Inductives.dMember a₀.store) = some mssP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_teles" [vis, nP, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockTeles V fe nP.toNat mss) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.checkBlockTeles V fe nP.toNat mss) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      PSlR decTele (AM.res (ConRon.Arena.checkBlockTeles V fe nP.toNat mss) a₀) (r.headD 0)
        (r.tail.headD 0) s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (cbtsE_spec p hP.bTele hP.bTeles n s₀ vis nP o l)
    (cbts_ref hq henv hV hcr hCS hApd hCrk hP nP n hn _ a₀ o l mss mssP hC hms hA hmssP)) ?_
  rintro _r s' ⟨hl, x, a', hrun, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.teles, hR.abs⟩

end sims

end L.Ind
