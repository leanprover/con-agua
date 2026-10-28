import ConAgua.Arena.IndT.Sum2
import ConAgua.Arena.IndInstallSpec.InstallSimCall
import ConAgua.Arena.IndInstallSpec.Cons
import ConAgua.Verdict.IndBE
import ConAgua.L.ModelGen

/-!
# `checkBlockTele`, `checkBlockTeles` under `StageC` (lane `indstaget`)

`check_block_tele`'s model, from `StageC` and con-ron's preconditions of `checkBlockTele_specF`
(the member denotes, the environment denotes), its twin side transcribed from that spec's proof:
`checkConstantVal` (the stub's `StageR` contract, `checkConstantVal_bridge` on its run for the
`CoreStep` and the stored type's closure), `checkSumTele` (`checkSumTele_refinesC`, con-ron's
`checkSumTele_spec` on its run for the answer's denotation), `stripPis` (`stripPis_pstep`), the
sort's intern (`internSortE_run`). `check_block_teles` walks the members (`dMember_ext`). Both have one model
(`cbtE`, `cbtsE`: `l_model … unified`) and one refinement (`cbt_ref`, `cbts_ref`: `RefE` under
`TeleG`, the claims of `check_constant_val` and `check_sum_tele`) for both outcomes.
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
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`check_block_teles`' unified model**: every member through `cbtE`, the `rec2`s and `sl_cons`es
(outside the verdict closure) lifted. -/
l_model cbtsE_spec (p : Prog) (h1 : p.lookup "check_block_tele" = some checkBlockTele)
  (hf : p.lookup "check_block_teles" = some checkBlockTeles)
  fns [hf ↦ cbtsE] specs [cbtE_spec p h1 n, callW_spec p n "rec2", callW_spec p n "sl_cons"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What the error arms of `check_block_tele`/`_teles` assume: the claims of `check_constant_val`
and `check_sum_tele` (read through their runs). -/
structure TeleG (p : Prog) : Prop where
  ccv : CheckConstantValE p
  sum : CheckSumTeleE p

/-- What `check_block_tele` gives besides the checked former and its sort `x` (from `m`, `a`): the
former's layout (`TeleOutC`), `AbsOK`, the core step. -/
structure TelePost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (r : List Word) (x : IConstantVal × LIdx) (m' : Mem) (a' : AState) : Prop where
  out : TeleOutC dn vis fe env m r x m' a'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'

/-- What `check_block_teles` gives besides the checked formers `x` (from `m`, `a`): the stage, the
growth, the formers' slice, `AbsOK`, the core step. -/
structure TelesPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (r : List Word) (x : List (IConstantVal × LIdx)) (m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  teles : PSlR decTele x (r.headD 0) (r.tail.headD 0) m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p)
  (hApd : ApdF p) (hCrk : CrKeep p)

include hq henv hV hApd hCrk in
/-- `check_sum_tele` under `StageC` as a `Sim` of its call (the constant and the start record the
same, below the tops). -/
theorem installCstSimC (hP : CstProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {cv k : Word} {cvv : IConstantVal} (hC : StageC dn vis fe env m a)
    (hcv : decCVp m cv.toNat = some cvv) (hx : CVExt m cv.toNat) (hA : AbsOK m)
    {cvP : ConLeche.ConstantVal} (hcvP : Frontend.denoteCV a.store cvv = some cvP)
    (hws : ConLeche.Expr.WScoped 0 cvP.type) (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    Sim (callW p n "check_sum_tele" [vis, cv, k, cv] m) (checkSumTele V fe cvv k.toNat cvv) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        decCVp m' (r.headD 0).toNat = some x.1 ∧ CVExt m' (r.headD 0).toNat ∧
        H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = x.2 ∧ AbsOK m') :=
  installSimCall (checkSumTele_refinesC hq henv hV hApd hCrk hP.alloc hP.copy hP.cons hP.view hP.fvarFind hP.fvarPush
    hP.internFVar hP.wt hP.sortFind hP.sortPush hP.internSort hP.derB hP.forallFind hP.forallPush
    hP.internForall hP.mkForall hP.closeTele hP.erAlloc hP.cvNew hP.slow hP.i1 hP.ab hP.tele hP.strip
    n hn _ a cv k cv cvv cvv hC hcv hx.1 hx.2 hcv hx.1 hx.2 hA hcvP hcvP hws hfe)
    fun _ _ ⟨_, hok, hC', hg, hd, h32, hs, hb, hsl, hA'⟩ => ⟨hok, hC', hg, hd, ⟨hb, hsl⟩, h32, hs, hA'⟩

include hq henv hV hApd hCrk in
/-- **`check_block_tele` refines `checkBlockTele`, both outcomes** under `StageC` (twin side:
con-ron's `checkBlockTele_specF`'s proof): `check_constant_val` and `check_sum_tele` through their
runs (their claims in `TeleG`), `strip_pis` and `intern_sort` (outside the verdict closure)
lifted. -/
theorem cbt_ref (hP : CstProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {nP ms : Word} {msh : MemberShape}
    (hC : StageC dn vis fe env m a) (hms : MemOK m ms.toNat msh) (hA : AbsOK m)
    {msP : ConLeche.MemberShape} (hmsP : ConRon.Bridge.Inductives.dMember a.store msh = some msP)
    (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    RefE (TeleG p) (cbtE p (n + 1) m vis nP ms) (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a
      (fun v x a' => TelePost dn vis fe env m a v.1 x v.2 a') := by
  have hS := hC.stage
  obtain ⟨hcvP, -, -⟩ := ConRon.Bridge.Inductives.dMember_inv hmsP
  obtain ⟨hmsB, hcx⟩ := hms
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨⟨c, hc, hcv⟩, hni, -⟩ := decMS_some (m := truncM m) hmsB
  obtain ⟨hw0, hcb, hmsl⟩ := partsIwRd hc rfl
  obtain ⟨hw1, hnb, -⟩ := partsIwRd hni (w := ms + 1) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨-, hcN⟩ := rec2IwN_trunc hc
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  have hcvx : CVExt m (UInt64.ofNat c : Word).toNat := by rw [hc']; exact hcx c hcN
  have hcvm : decCVp m (UInt64.ofNat c : Word).toNat = some msh.cvT := by
    rw [hc']; exact DecB.get (OMono.decCVp _) hcv
  by_cases hov : nP + UInt64.ofNat msh.nIdx < nP
  · rw [cbtE.abort1 p n m vis nP ms (by rw [hw1]; exact hov)]; exact RefE.of_cls0 rfl
  rw [cbtE.arm1 p n m vis nP ms (by rw [hw1]; exact hov), hw0, hw1]
  have hk : (nP + UInt64.ofNat msh.nIdx).toNat = nP.toNat + msh.nIdx := by
    rw [partsAddNoOv hov, UInt64.toNat_ofNat_of_lt' hnb]
  unfold ConRon.Arena.checkBlockTele
  -- `check_constant_val`
  cases h1 : callE p n "check_constant_val" [vis, UInt64.ofNat c] m with
  | error e1 =>
    rw [cbtE.k_check_constant_val.none]
    exact RefE.bind_left fun hG => hG.ccv hV hq hApd hCrk ⟨m, Locals.init []⟩ a dn fe vis _ msh.cvT hC.stageT
      (rec2DecCV_erecP hcvm hcvx) (rec3CVExt_lt hS hcvx) (denoteCV_lps hcvP) hA.crMemo.crOK n hn e1 h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [cbtE.k_check_constant_val.arm1]
  obtain ⟨s1, rfl, -, hok1, hT1, hg1, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (checkConstantVal_refinesT p hV hq hApd hCrk n hn _ a dn fe vis _ msh.cvT hC.stageT
      (rec2DecCV_erecP hcvm hcvx) (rec3CVExt_lt hS hcvx) (denoteCV_lps hcvP) hA.crMemo.crOK) (callW_of_callE h1)
  have hr1 := partsRunOfOk hok1
  have hA1 : AbsOK s1.mem := checkConstantVal_absOK p hV hq hApd hCrk hn hC.stageT
    (rec2DecCV_erecP hcvm hcvx) (rec3CVExt_lt hS hcvx) (denoteCV_lps hcvP) hA.crMemo.crOK (callW_of_callE h1) hA
  generalize AM.st (checkConstantVal V fe msh.cvT) a = a1 at hr1 hT1
  generalize AM.res (checkConstantVal V fe msh.cvT) a = u1 at hr1
  obtain ⟨c1, F₁, hF₁⟩ := ConRon.Bridge.checkConstantVal_bridge rfl (ConRon.Bridge.CoreSpec.of_core rfl)
    hC.check henv hcvP hr1
  have hC1 : StageC dn vis fe env s1.mem a1 := StageC.of_T hT1 c1.ok
  have hcA := ConRon.Bridge.denoteCV_ext hcvP c1.ext
  have hw1' : ConLeche.Expr.WScoped 0 msP.cvT.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar (ConLeche.checkConstantVal_typeWF hF₁).1
  have hcvm1 : decCVp s1.mem (UInt64.ofNat c : Word).toNat = some msh.cvT := by
    rw [hc']; exact DecB.stab (OMono.decCVp _) hcv s1.mem hg1
  have hx1 := CVExt_grow hg1 hcvx
  refine RefE.bind_right hr1 ?_
  -- `check_sum_tele`
  cases h2 : callE p n "check_sum_tele" [vis, UInt64.ofNat c, nP + UInt64.ofNat msh.nIdx, UInt64.ofNat c] s1.mem with
  | error e2 =>
    rw [cbtE.k_check_sum_tele.none]
    refine RefE.bind_left fun hG => ?_
    have hcl := hG.sum hq henv hV hApd hCrk hP.alloc hP.copy hP.cons hP.view hP.fvarFind hP.fvarPush
      hP.internFVar hP.wt hP.sortFind hP.sortPush hP.internSort hP.derB hP.forallFind hP.forallPush
      hP.internForall hP.mkForall hP.closeTele hP.erAlloc hP.cvNew hP.slow hP.i1 hP.ab hP.tele hP.strip
      ⟨s1.mem, Locals.init []⟩ a1 _ _ _ msh.cvT msh.cvT hC1 hcvm1 hx1.1 hx1.2 hcvm1 hx1.1 hx1.2 hA1 hcA hcA hw1'
      (ConRon.Bridge.denoteFEnv_mono c1.ext hfe) n hn e2 h2
    rw [hk] at hcl
    exact hcl
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [cbtE.k_check_sum_tele.arm1]
  have hsim := installCstSimC (k := nP + UInt64.ofNat msh.nIdx) hq henv hV hApd hCrk hP n hn hC1 hcvm1 hx1 hA1 hcA hw1'
    (ConRon.Bridge.denoteFEnv_mono c1.ext hfe) r2 m2 (callW_of_callE h2)
  rw [hk] at hsim
  obtain ⟨⟨cvTa, sx⟩, a2, hr2, hC2, hg2, hcvTa, hxTa, hs32, hsd, hA2⟩ := hsim
  obtain ⟨c2, F₂, cvTaP, sP, -, h2a, h2b⟩ := ConRon.Bridge.Inductives.checkSumTele_spec fe rfl
    (ConRon.Bridge.CoreSpec.of_core rfl) henv msh.cvT msP.cvT (nP.toNat + msh.nIdx) msh.cvT
    msP.cvT hw1' a1 a2 _ hC1.check ⟨hcA, hcA, ConRon.Bridge.denoteFEnv_mono c1.ext hfe⟩ hr2
  dsimp only at h2a h2b
  refine RefE.bind_right hr2 ?_
  have hS2 := hC2.stage
  obtain ⟨htyl, htye⟩ := partsCVType (installCvDecB hcvTa hxTa) (w := r2.headD 0) rfl
  -- `strip_pis`
  rcases h3 : callW p n "strip_pis" [nP + UInt64.ofNat msh.nIdx, rdW (m2.arr64 EREC) (r2.headD 0 + 3)] m2 with
    _ | ⟨r3, m3⟩
  · rw [liftE_none, cbtE.k_strip_pis.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have hs3 := stripF_of_callW hP.strip h3
  obtain ⟨x3, a3, hr3, hS3, hg3, hd3⟩ :=
    stripF_pis_ok dn vis fe (nP + UInt64.ofNat msh.nIdx) _ htyl m2 m3 a2 r3 hs3 hS2
  have hA3 := stripF_afr hs3 hA2
  rw [hk, htye] at hr3
  obtain ⟨ha3, -⟩ := ConRon.Bridge.Inductives.stripPis_pstep hC2.check.state
    (ConRon.Bridge.denoteCV_type h2a) hr3
  rw [ha3] at hS3 hr3
  refine RefE.bind_right hr3 ?_
  have hC3 : StageC dn vis fe env m3 a2 := hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state)
  cases x3 with
  | none =>
    have h0 : r3.headD 0 = 0 := hd3
    rw [cbtE.k_strip_pis.abort1 p n _ _ r3 m3 h0]; exact RefE.of_cls0 rfl
  | some bb =>
  obtain ⟨bs, body⟩ := bb
  obtain ⟨h1', -, hb32, hbe⟩ := hd3
  rw [cbtE.k_strip_pis.arm1 p n _ _ r3 m3 (by rw [h1']; decide)]
  have hd3' : (r3.drop 3).headD 0 = r3.tail.tail.tail.headD 0 := by
    rcases r3 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl
  rw [hd3'] at hb32 hbe
  -- `intern_sort`
  rcases h4 : callW p n "intern_sort" [r2.tail.headD 0] m3 with _ | ⟨r4, m4⟩
  · rw [liftE_none, cbtE.k_intern_sort.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have hsd' : decI (r2.tail.headD 0) = sx := hsd
  obtain ⟨srt, a4, hr4, hS4, hg4, hsrt, hf4⟩ := installSortSim hP n hS3 hs32 r4 m4 h4
  rw [hsd'] at hr4
  obtain ⟨p4, -⟩ := ConRon.Bridge.Inductives.internSortE_run hC3.check.state h2b hr4
  have hA4 := hf4 hA3
  have hC4 : StageC dn vis fe env m4 a4 := hC3.of_pstep hS4 hA4 p4
  refine RefE.bind_right hr4 ?_
  by_cases h40 : r3.tail.tail.tail.headD 0 = r4.headD 0
  · rw [cbtE.k_intern_sort.arm1 p _ _ _ r4 m4 h40]
    have hb : (body == srt) = true := by rw [← hbe, ← hsrt, h40, decE_eq]; exact beq_self_eq_true _
    simp only [hb, ite_true]
    refine RefE.ret rfl ⟨⟨hC4, ((hg1.trans hg2).trans hg3).trans hg4, ?_, ?_, hs32, hsd⟩, hA4,
      c1.trans (c2.trans (p4.toCore c2.ok))⟩
    · exact DecB.stab (OMono.decCVp _) (installCvDecB hcvTa hxTa) m4 (hg3.trans hg4)
    · exact CVExt_grow (hg3.trans hg4) hxTa
  · rw [cbtE.k_intern_sort.abort1 p _ _ _ r4 m4 h40]; exact RefE.of_cls0 rfl

include hq henv hV hApd hCrk in
/-- **`check_block_tele` refines `checkBlockTele`** under `StageC` (the knot's core calls; the
member's denotation as con-ron's `checkBlockTele_specF` asks): the checked former below the tops,
its result sort a handle. -/
@[refines ConRon.Arena.checkBlockTele]
theorem checkBlockTele_refinesC (hP : CstProg p)
    (hp : p.lookup "check_block_tele" = some checkBlockTele) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (nP ms : Word) (msh : MemberShape)
    (hC : StageC dn vis fe env s₀.mem a₀) (hms : MemOK s₀.mem ms.toNat msh) (hA : AbsOK s₀.mem)
    {msP : ConLeche.MemberShape} (hmsP : ConRon.Bridge.Inductives.dMember a₀.store msh = some msP)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_tele" [vis, nP, ms]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a₀ ∧
      TeleOutC dn vis fe env s₀.mem r (AM.res (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a₀) s'.mem
        (AM.st (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a₀) ∧ AbsOK s'.mem ∧
      ConRon.Bridge.CoreStep V env fe a₀ (AM.st (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a₀);
      ⊤⦄ := by
  refine triple_post (RefE.triple (cbtE_spec p hp (n + 1) s₀ vis nP ms)
    (cbt_ref hq henv hV hApd hCrk hP n hn hC hms hA hmsP hfe)) ?_
  rintro _r s' ⟨hl, x, a', hrun, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hR.out, hR.abs, by rw [hst]; exact hR.core⟩

include hq henv hV hApd hCrk in
/-- **`check_block_teles` refines `checkBlockTeles`, both outcomes** under `StageC` (twin side:
con-ron's `checkBlockTeles_specF`'s proof; induction on the fuel): every member by `cbt_ref`, the
`rec2`s and `sl_cons`es (outside the verdict closure) lifted. -/
theorem cbts_ref (hP : InstProg p) (nP : Word) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (o l : Word) (mss : List MemberShape)
      (mssP : List ConLeche.MemberShape),
    StageC dn vis fe env m a → MemsOK m o l mss → AbsOK m →
    mss.mapM (ConRon.Bridge.Inductives.dMember a.store) = some mssP →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    RefE (TeleG p) (cbtsE p n m vis nP o l) (ConRon.Arena.checkBlockTeles V fe nP.toNat mss) a
      (fun v x a' => TelesPost dn vis fe env m a v.1 x v.2 a') := by
  induction n with
  | zero => intros; rw [cbtsE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a o l mss mssP hC hms hA hmssP hfe
  have hS := hC.stage
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
  have h1 := cbt_ref hq henv hV hApd hCrk hP.toCstProg k (by omega) hC hmok hA hxP hfe (nP := nP)
  rcases h1' : cbtE p (k + 1) m vis nP (UInt64.ofNat q) with e1 | ⟨r1, m1⟩ <;> rw [h1'] at h1
  · rw [cbtsE.k_check_block_tele.none]; exact RefE.bind_left h1
  rw [cbtsE.k_check_block_tele.arm1]
  obtain ⟨x1, a1, hr1, hT1, hA1, c1⟩ := h1
  refine RefE.bind_right hr1 ?_
  rcases h2 : callW p (k + 1) "rec2" [r1.headD 0, r1.tail.headD 0] m1 with _ | ⟨r2, m2⟩
  · rw [liftE_none, cbtsE.k_rec2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, cbtsE.k_rec2.arm1]
  obtain ⟨hS2, hg2, hd2, hlt2⟩ := installRec2Tele hP (k + 1) hT1.toR h2
  have hA2 : AbsOK m2 := by
    obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (rec2_specW p hP.alloc (k + 1) hP.rec2 _ _ _) h2
    exact recW_afr hW hA1
  have hC2 : StageC dn vis fe env m2 a1 := hT1.1.of_pstep hS2 hA2 (PStep.refl hT1.1.check.state)
  have h3 := ih (by omega) m2 a1 (o + 1) (l - 1) rest restP hC2 (hrest.grow hg2) hA2
    (ConRon.Bridge.Inductives.dMember_ext.list c1.ext _ _ hrestP) (ConRon.Bridge.denoteFEnv_mono c1.ext hfe)
  rcases h3' : cbtsE p (k + 1) m2 vis nP (o + 1) (l - 1) with e3 | ⟨r3, m3⟩ <;> rw [h3'] at h3
  · rw [cbtsE.k_check_block_teles.none]; exact RefE.bind_left h3
  rw [cbtsE.k_check_block_teles.arm1]
  obtain ⟨xs, a3, hr3, hC3, hg3, hxs, hA3, c3⟩ := h3
  refine RefE.bind_right hr3 ?_
  rcases h4 : callW p (k + 1) "sl_cons" [r2.headD 0, r3.headD 0, r3.tail.headD 0] m3 with _ | ⟨r4, m4⟩
  · rw [liftE_none, cbtsE.k_sl_cons.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, cbtsE.k_sl_cons.arm1]
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (slCons_specW p hP.alloc hP.copy hP.cons (k + 1) _ _ _ _) h4
  obtain ⟨hS4, hg4, hd4, htop4⟩ := partsConsPL decTele_mono hW hC3.stage hxs.2 hxs.1
    (hd2.grow (decTele_mono _) hg3)
  have hA4 := consW_afr hW hA3
  exact RefE.ret rfl ⟨hC3.of_pstep hS4 hA4 (PStep.refl hC3.check.state), (hg2.trans hg3).trans hg4,
    ⟨hd4, Nat.le_of_eq htop4⟩, hA4, c1.trans c3⟩

include hq henv hV hApd hCrk in
/-- **`check_block_teles` refines `checkBlockTeles`** under `StageC` (the members' denotations as
con-ron's `checkBlockTeles_specF` asks): the checked formers a slice of `[cvTa, s]` records,
decoded below the tops. -/
@[refines ConRon.Arena.checkBlockTeles]
theorem checkBlockTeles_refinesC (hP : InstProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (nP o l : Word)
    (mss : List MemberShape) (hC : StageC dn vis fe env s₀.mem a₀) (hms : MemsOK s₀.mem o l mss)
    (hA : AbsOK s₀.mem) {mssP : List ConLeche.MemberShape}
    (hmssP : mss.mapM (ConRon.Bridge.Inductives.dMember a₀.store) = some mssP)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_teles" [vis, nP, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockTeles V fe nP.toNat mss) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.checkBlockTeles V fe nP.toNat mss) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      PSlR decTele (AM.res (ConRon.Arena.checkBlockTeles V fe nP.toNat mss) a₀) (r.headD 0)
        (r.tail.headD 0) s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (cbtsE_spec p hP.bTele hP.bTeles n s₀ vis nP o l)
    (cbts_ref hq henv hV hApd hCrk hP nP n hn _ a₀ o l mss mssP hC hms hA hmssP hfe)) ?_
  rintro _r s' ⟨hl, x, a', hrun, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.teles, hR.abs⟩

end sims

end L.Ind
