import ConAgua.Verdict.IndBSum4
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl
import ConAgua.Arena.IndInstallSpec.ConsBlockCtors
import ConAgua.Arena.IndInstallSpec.NestCtx
import ConAgua.L.ModelGen

/-!
# `checkBlockCtors` under `StageC` (lane `indstaget`)

The constructors of every member, from `StageC` and con-ron's preconditions of
`checkBlockCtors_specF` (the shape, the members and the formers denote, every stored former
closed, the environment denotes and its index spec holds — one environment, `vis0 = vis`, as
`check_block_pass` calls it), the twin side transcribed from that spec's proof: one member's
`checkSumCtors` (`checkSumCtors_refinesC`, con-ron's `checkSumCtors_spec` on its run for the
`CoreStep`), the records and conses (L only), the shape's level parameters (L only).

`check_block_ctors_one` and `check_block_ctors_go` have one model each for both outcomes
(`icboE`, `icbgE`: `l_model … unified`) and one refinement each (`icbo_ref`, `icbg_ref`: `RefE`
under `VerdictCtxU`, what `check_sum_ctors`' refinement `scts_ref` assumes).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_block_ctors_one`'s unified model**: `check_sum_ctors` through its run (not migrated),
the `rec2`s (outside the verdict closure) lifted. -/
l_model icboE_spec (p : Prog) (hP : CtorsProg p)
  fns [hP.one ↦ icboE]
  specs [rec2_specW p hP.alloc n hP.rec2]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`check_block_ctors_go`'s unified model**: the head through `icboE`, the `sl_cons` lifted. -/
l_model icbgE_spec (p : Prog) (hP : CtorsProg p)
  fns [hP.go ↦ icbgE]
  specs [icboE_spec p hP n, slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`check_block_ctors`' unified model**: `block_shape_lps` (outside the verdict closure) lifted,
`check_block_ctors_go` through `icbgE`. -/
l_model ictE_spec (p : Prog) (hP : CtorsProg p)
  fns [hP.ctors ↦ ictE]
  specs [blockShapeLps_spec p hP.alloc hP.erCopy hP.erToIw hP.lps n, icbgE_spec p hP n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


/-- What `check_block_ctors_one` gives besides the twin's constructors and their sorts `x` (from
`m`, `a`): the stage invariant, the growth, the two records `r₀` (constructors, also with the
slices' bounds) and `r₁` (sorts), `AbsOK`, the twin's step. -/
structure IcboPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (r : List Word) (m' : Mem)
    (x : List (IConstantVal × Nat) × List (List LIdx)) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  cns : DecB (fun m => decCNS m (r.headD 0).toNat) m' x.1
  iss : DecB (fun m => decISS m (r.tail.headD 0).toNat) m' x.2
  cnsB : DecB (fun m => decCNSB m (r.headD 0).toNat) m' x.1
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'

/-- What `check_block_ctors_go` gives besides the twin's constructors and sorts per member `x`:
the stage invariant, the growth, the two slices (the constructors also with their bounds),
`AbsOK`. -/
structure IcbgPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (r : List Word) (m' : Mem)
    (x : List (List (IConstantVal × Nat)) × List (List (List LIdx))) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  cns : PSlR decCNS x.1 (r.headD 0) (r.tail.headD 0) m'
  iss : PSlR decISS x.2 (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) m'
  cnsB : PSlR decCNSB x.1 (r.headD 0) (r.tail.headD 0) m'
  abs : AbsOK m'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p) (hOpf : OpfF p) (hLC : LvlCacheProg p)
  (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p)

include hq henv hV hOpf hLC hLT hApd hCrk in
/-- `check_sum_ctors` under `StageC` as a `Sim` of its call, at one environment. -/
theorem installSimSumCtorsC (hP : SumProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (T lo ll nP nIdx rs isP lg cvTa co cl : Word) (hT : H T) (hrs : H rs) (lps : List NIdx)
    (cvv : IConstantVal) (cs : List (IConstantVal × Nat))
    (hC : StageC dn vis fe env m a) (hl : decHL m lo.toNat ll.toNat = some lps)
    (hlb : lo.toNat + ll.toNat ≤ iwTop m) (hcv : DecB (fun m => decCVp m cvTa.toNat) m cvv)
    (hcs : DecB (fun m => decPL m (decCN m) co.toNat cl.toNat) m cs) (hA : AbsOK m)
    {TP : ConLeche.Name} {lpsP : List ConLeche.Name} {rsP : ConLeche.Level}
    {cvTaP : ConLeche.ConstantVal} {csP : List (ConLeche.ConstantVal × Nat)}
    (hTP : denoteN a.store.ns (decI T) = some TP)
    (hlpsP : Frontend.denoteNList a.store.ns lps = some lpsP)
    (hrsP : denoteL a.store.ls (decI rs) = some rsP)
    (hcvTaP : Frontend.denoteCV a.store cvv = some cvTaP) (hws : ConLeche.Expr.WScoped 0 cvTaP.type)
    (hcsP : ConRon.Bridge.Inductives.denoteCtors a.store cs = some csP)
    (hok₀ : ConRon.Bridge.Inductives.IFEnvOKS env fe a.store)
    (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    Sim (callW p n "check_sum_ctors" [vis, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvTa, co, cl] m)
      (checkSumCtors V fe fe (decI T) lps nP.toNat nIdx.toNat (decI rs) (isP != 0) (lg != 0) cvv cs) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        PSlR decCN x.1 (r.headD 0) (r.tail.headD 0) m' ∧
        PSlR decIS x.2 (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) m' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a') := by
  intro r m' e
  have hfev : fe.restrictTo vis.toNat = fe := by rw [← hC.stage.check.env.vis]; rfl
  have h := RefE.run_okW (sctsE_spec p hP hV n ⟨m, Locals.init []⟩ vis vis T lo ll nP nIdx rs isP lg cvTa co cl)
    (scts_ref (dn := dn) (vis := vis) (fe := fe) hq henv hOpf hLC hLT hApd hCrk hP vis T lo ll nP nIdx rs isP
      lg cvTa lps cvv hT hrs hws n hn m a co cl cs csP hC hl hlb hcv hcs hA hTP hlpsP hrsP hcvTaP hcsP
      (by rw [hfev]; exact hok₀) hfe) e
  rw [hfev] at h
  obtain ⟨s', rfl, -, x, a', h1, hR⟩ := h
  exact ⟨x, a', h1, hR.stage, hR.grow, ⟨hR.cns, hR.cnsB⟩, ⟨hR.sorts, hR.sortsB⟩, hR.abs, hR.core⟩

include hq henv hV hOpf hLC hLT hApd hCrk in
/-- **`check_block_ctors_one` refines `checkSumCtors`, both outcomes** (twin side: one member of
con-ron's `checkBlockCtors_specF`'s proof): `check_sum_ctors` through its run (`installSimSumCtorsC`,
`scts_ref`), the two `rec2`s (outside the verdict closure) claim nothing. -/
theorem icbo_ref (hP : CtorsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {pp lo ll ms cv : Word} {bs : BlockShape} {msh : MemberShape} {cvv : IConstantVal}
    (hC : StageC dn vis fe env m a) (hqd : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hlps : decHL m lo.toNat ll.toNat = some bs.lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hms : DecB (fun m => decMS m ms.toNat) m msh) (hcv : DecB (fun m => decCVp m cv.toNat) m cvv)
    (hA : AbsOK m) {bsP : ConLeche.BlockShape} {msP : ConLeche.MemberShape}
    {cvP : ConLeche.ConstantVal}
    (hbsP : ConRon.Bridge.Inductives.dShape a.store bs = some bsP)
    (hmsP : ConRon.Bridge.Inductives.dMember a.store msh = some msP)
    (hcvP : Frontend.denoteCV a.store cvv = some cvP) (hws : ConLeche.Expr.WScoped 0 cvP.type)
    (hok₀ : ConRon.Bridge.Inductives.IFEnvOKS env fe a.store)
    (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    RefE (VerdictCtxU p) (icboE p (n + 1) m vis vis pp lo ll ms cv)
      (checkSumCtors V fe fe msh.cvT.name bs.lps bs.nP msh.nIdx bs.resSort bs.isProp bs.large cvv msh.ctors) a
      (fun v x a' => IcboPost dn vis fe env m a v.1 v.2 x a') := by
  have hS := hC.stage
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hsz := hS.iw.iwSize
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hqd hsrc
  obtain ⟨hnpw, hnpb, hrs32, hrse⟩ := partsShapeWords (IWGrow.refl m) hqd hq9
  have hqt : decBS (truncM m) pp.toNat = some bs := hqd
  obtain ⟨-, -, -, -, -, hlg, hpr⟩ := decBS_some hqt
  have h8 := installIwB (w := pp) (k := 8) hpr hsz
  have h7 := installIwB (w := pp) (k := 7) hlg hsz
  rw [show (UInt64.ofNat 8 : Word) = 8 from rfl] at h8
  rw [show (UInt64.ofNat 7 : Word) = 7 from rfl] at h7
  have hmsT : decMS (truncM m) ms.toNat = some msh := hms
  obtain ⟨⟨cvp, hcvp, hcvT⟩, hni, hct⟩ := decMS_some hmsT
  obtain ⟨co, cl, hco, hcl, hcd, -⟩ := partsAt decCN_mono hct
  have l3 := partsIwLt hcl
  obtain ⟨hw0, hcvb, -⟩ := partsIwRd hcvp (w := ms) rfl
  obtain ⟨hw1, hnib, -⟩ := partsIwRd hni (w := ms + 1) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨hw2, -, -⟩ := partsIwRd hco (w := ms + 2) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨hw3, -, -⟩ := partsIwRd hcl (w := ms + 3) (by rw [UInt64.toNat_add]; simp; omega)
  rw [UInt64.ofNat_toNat] at hw2 hw3
  obtain ⟨hn32, hnm⟩ := partsCVName (IWGrow.refl m) hcvT hcvb
  obtain ⟨hcvTP, -, hcsP⟩ := ConRon.Bridge.Inductives.dMember_inv hmsP
  obtain ⟨-, -, -, -, hsP, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hbsP
  have hlpsP := ConRon.Bridge.Inductives.BlockShape.lps_spec hbsP
  have hcsP' : ConRon.Bridge.Inductives.denoteCtors a.store msh.ctors = some msP.ctors := by
    rw [← ConRon.Bridge.Inductives.dCtors_eq_denoteCtors]; exact hcsP
  have hTP : denoteN a.store.ns (decI (rdW (m.arr64 EREC) (UInt64.ofNat cvp))) = some msP.cvT.name := by
    rw [hnm]; exact ConRon.Bridge.denoteCV_name hcvTP
  have hfev : fe.restrictTo vis.toNat = fe := by rw [← hC.stage.check.env.vis]; rfl
  rw [icboE.arm1, hw0, hw1, hw2, hw3, hnpw]
  -- `check_sum_ctors`
  rcases h1 : callE p n "check_sum_ctors" [vis, vis, rdW (m.arr64 EREC) (UInt64.ofNat cvp), lo, ll,
      UInt64.ofNat bs.nP, UInt64.ofNat msh.nIdx, rdW (m.arr64 IW) (pp + 6), rdW (m.arr64 IW) (pp + 8),
      rdW (m.arr64 IW) (pp + 7), cv, co, cl] m with e1 | ⟨r1, m1⟩
  · rw [icboE.k_check_sum_ctors.none]
    intro hG
    have h := RefE.run_err (sctsE_spec p hP.sum hV n ⟨m, Locals.init []⟩ vis vis
      (rdW (m.arr64 EREC) (UInt64.ofNat cvp)) lo ll (UInt64.ofNat bs.nP) (UInt64.ofNat msh.nIdx)
      (rdW (m.arr64 IW) (pp + 6)) (rdW (m.arr64 IW) (pp + 8)) (rdW (m.arr64 IW) (pp + 7)) cv co cl) hG.nv hG
      (scts_ref hq henv hOpf hLC hLT hApd hCrk hP.sum vis (rdW (m.arr64 EREC) (UInt64.ofNat cvp)) lo ll
        (UInt64.ofNat bs.nP) (UInt64.ofNat msh.nIdx) (rdW (m.arr64 IW) (pp + 6)) (rdW (m.arr64 IW) (pp + 8))
        (rdW (m.arr64 IW) (pp + 7)) cv bs.lps cvv hn32 hrs32 hws n hn m a co cl msh.ctors _ hC hlps hlb hcv hcd hA
        hTP hlpsP (by rw [hrse]; exact hsP) hcvP hcsP' (by rw [hfev]; exact hok₀) hfe) h1
    rw [hfev, hnm, hrse, h8, h7, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib] at h
    exact h
  rw [icboE.k_check_sum_ctors.arm1]
  have hsim := installSimSumCtorsC (dn := dn) (fe := fe) hq henv hV hOpf hLC hLT hApd hCrk hP.sum n hn
    (rdW (m.arr64 EREC) (UInt64.ofNat cvp)) lo ll (UInt64.ofNat bs.nP) (UInt64.ofNat msh.nIdx)
    (rdW (m.arr64 IW) (pp + 6)) (rdW (m.arr64 IW) (pp + 8)) (rdW (m.arr64 IW) (pp + 7)) cv co cl
    hn32 hrs32 bs.lps cvv msh.ctors hC hlps hlb hcv hcd hA hTP hlpsP
    (by rw [hrse]; exact hsP) hcvP hws hcsP' hok₀ hfe
  rw [hnm, hrse, h8, h7, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib] at hsim
  obtain ⟨⟨cs, ss⟩, a1, hrun1, hC1, hg1, hcs1, hss1, hA1, c1⟩ := hsim r1 m1 (callW_of_callE h1)
  -- the two `rec2`s (L only)
  rcases h2 : recW m1 2 [r1.headD 0, r1.tail.headD 0] with _ | ⟨r2, m2⟩
  · rw [liftE_none, icboE.k_rec2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, icboE.k_rec2.arm1]
  obtain ⟨hS2, hg2, hd2⟩ := installRec2PSl decCN_mono h2 hC1.stage hcs1
  have hd2b := installRec2PSlB decCN_mono h2 hC1.stage hcs1
  have hA2 : AbsOK m2 := recW_afr h2 hA1
  rcases h3 : recW m2 2 [r1.tail.tail.headD 0, r1.tail.tail.tail.headD 0] with _ | ⟨r3, m3⟩
  · rw [liftE_none, icboE.k_rec2_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, icboE.k_rec2_2.arm1]
  obtain ⟨hS3, hg3, hd3⟩ := installRec2PSl decIS_mono h3 hS2 (hss1.grow decIS_mono hg2)
  have hA3 : AbsOK m3 := recW_afr h3 hA2
  exact RefE.ret hrun1 ⟨hC1.of_pstep hS3 hA3 (PStep.refl hC1.check.state), (hg1.trans hg2).trans hg3,
    hd2.grow (decCNS_mono _) hg3, hd3, hd2b.grow (decCNSB_mono _) hg3, hA3, c1⟩

include hq henv hV hOpf hLC hLT hApd hCrk in
/-- **`check_block_ctors_go` refines `checkBlockCtors`, both outcomes** (twin side: con-ron's
`checkBlockCtors_specF`'s proof): the head by `icbo_ref`, the rest by induction, the two
`sl_cons` (outside the verdict closure) claim nothing. -/
theorem icbg_ref (hP : CtorsProg p) (pp lo ll : Word) (bs : BlockShape) {bsP : ConLeche.BlockShape}
    (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (mo ml co cl : Word) (mss : List MemberShape) (cvs : List IConstantVal)
      (mssP : List ConLeche.MemberShape) (cvsP : List ConLeche.ConstantVal),
    StageC dn vis fe env m a → DecB (fun m => decBS m pp.toNat) m bs → ShapeSrc m pp →
    decHL m lo.toNat ll.toNat = some bs.lps → lo.toNat + ll.toNat ≤ iwTop m →
    PSlR decMS mss mo ml m → PSlR decCVp cvs co cl m → AbsOK m →
    ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    mss.mapM (ConRon.Bridge.Inductives.dMember a.store) = some mssP →
    cvs.mapM (Frontend.denoteCV a.store) = some cvsP → (∀ cv ∈ cvsP, ConLeche.Expr.WScoped 0 cv.type) →
    ConRon.Bridge.Inductives.IFEnvOKS env fe a.store →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    RefE (VerdictCtxU p) (icbgE p n m vis vis pp lo ll mo ml co cl) (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs) a
      (fun v x a' => IcbgPost dn vis fe env m v.1 v.2 x a') := by
  induction n with
  | zero => intros; rw [icbgE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n ih =>
  intro m a mo ml co cl mss cvs mssP cvsP hC hqd hsrc hlps hlb hmss hcvs hA hbsP hmssP hcvsP hws hok₀ hfe
  by_cases hml : ml = 0
  · rw [icbgE.arm1 p n m vis vis pp lo ll mo ml co cl hml]
    have : mss = [] := by
      have h := hmss.1; simp only [DecB, hml] at h
      simpa [decPL] using h.symm
    subst this
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, PSlR.nil decCNS m, PSlR.nil decISS m, PSlR.nil decCNSB m, hA⟩
  by_cases hcl : cl = 0
  · rw [icbgE.arm2 p n m vis vis pp lo ll mo ml co cl hml hcl]
    have : cvs = [] := by
      have h := hcvs.1; simp only [DecB, hcl] at h
      simpa [decPL] using h.symm
    subst this
    have : ConRon.Arena.checkBlockCtors V fe fe bs mss [] = pure ([], []) := by
      cases mss <;> simp [ConRon.Arena.checkBlockCtors]
    rw [this]
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, PSlR.nil decCNS m, PSlR.nil decISS m, PSlR.nil decCNSB m, hA⟩
  obtain ⟨q, msh, rest, rfl, hw, hqb, hdm, hrest⟩ := partsPSl_cons hmss hml
  obtain ⟨c, cvv, cvs', rfl, hwc, hcb, hdc, hcvs'⟩ := partsPSl_cons hcvs hcl
  obtain ⟨msP, restP, rfl, hmP, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmssP
  obtain ⟨cvP, cvsP', rfl, hcvP, hcvsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcvsP
  rw [icbgE.arm3 p n m vis vis pp lo ll mo ml co cl hml hcl, hw, hwc]
  simp only [ConRon.Arena.checkBlockCtors]
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  -- the head
  rcases n with _ | k
  · rw [icboE.eq_1, icbgE.k_check_block_ctors_one.none]; exact RefE.of_cls0 (by simp)
  have h1 := icbo_ref hq henv hV hOpf hLC hLT hApd hCrk hP k (by omega) hC hqd hsrc hlps hlb
    (by rw [hq']; exact hdm) (by rw [hc']; exact hdc) hA hbsP hmP hcvP (hws _ List.mem_cons_self) hok₀ hfe
  rcases h1' : icboE p (k + 1) m vis vis pp lo ll (UInt64.ofNat q) (UInt64.ofNat c) with e1 | ⟨r1, m1⟩
  · rw [h1'] at h1
    rw [icbgE.k_check_block_ctors_one.none]; exact RefE.bind_left h1
  rw [h1'] at h1
  obtain ⟨⟨cs, ss⟩, a1, hrun1, hR1⟩ := h1
  dsimp only at hR1
  rw [icbgE.k_check_block_ctors_one.arm1]
  refine RefE.bind_right hrun1 ?_
  dsimp only
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hqd hsrc
  have x1 := hR1.core.ext
  have hg1 := hR1.grow
  -- the rest
  have h2 := ih (by omega) m1 a1 (mo + 1) (ml - 1) (co + 1) (cl - 1) rest cvs' restP cvsP' hR1.stage
    (hqd.grow (decBS_mono _) hg1)
    (partsHsrc_grow hg1 hq9 hsrc) (by rw [decHL_grow3 hg1 hlb]; exact hlps) (Nat.le_trans hlb hg1.1)
    (hrest.grow decMS_mono hg1) (hcvs'.grow (fun q => OMono.decCVp q) hg1) hR1.abs
    (ConRon.Bridge.Inductives.dShape_ext x1 _ _ hbsP)
    (ConRon.Bridge.Inductives.dMember_ext.list x1 _ _ hrestP)
    (ConRon.Bridge.Inductives.dExt_denoteCV.list x1 _ _ hcvsP')
    (fun cv h => hws cv (List.mem_cons_of_mem _ h)) (hok₀.mono x1)
    (ConRon.Bridge.denoteFEnv_mono x1 hfe)
  rcases h2' : icbgE p (k + 1) m1 vis vis pp lo ll (mo + 1) (ml - 1) (co + 1) (cl - 1) with e2 | ⟨r2, m2⟩
  · rw [h2'] at h2
    rw [icbgE.k_check_block_ctors_go.none]; exact RefE.bind_left h2
  rw [h2'] at h2
  obtain ⟨⟨rc, rs⟩, a2, hrun2, hR2⟩ := h2
  dsimp only at hR2
  rw [icbgE.k_check_block_ctors_go.arm1]
  refine RefE.bind_right hrun2 ?_
  dsimp only
  have hS2 := hR2.stage.stage
  -- the two `sl_cons` (L only)
  rcases h3 : consW (k + 1) m2 (r1.headD 0) (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩
  · rw [liftE_none, icbgE.k_sl_cons.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, icbgE.k_sl_cons.arm1]
  obtain ⟨hS3, hg3, hd3, ht3⟩ := partsConsPL decCNS_mono h3 hS2 hR2.cns.bound hR2.cns.dec
    (hR1.cns.grow (decCNS_mono _) hR2.grow)
  obtain ⟨-, -, hb3, hbt3⟩ := partsConsPL decCNSB_mono h3 hS2 hR2.cnsB.bound hR2.cnsB.dec
    (hR1.cnsB.grow (decCNSB_mono _) hR2.grow)
  have hA3 := consW_afr h3 hR2.abs
  rcases h4 : consW (k + 1) m3 (r1.tail.headD 0) (r2.tail.tail.headD 0) (r2.tail.tail.tail.headD 0) with
    _ | ⟨r4, m4⟩
  · rw [liftE_none, icbgE.k_sl_cons_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, icbgE.k_sl_cons_2.arm1]
  obtain ⟨hS4, hg4, hd4, ht4⟩ := partsConsPL decISS_mono h4 hS3 (by have := hR2.iss.bound; have := hg3.1; omega)
    (hR2.iss.dec.grow (OMono.decPL decISS_mono _ _) hg3) (hR1.iss.grow (decISS_mono _) (hR2.grow.trans hg3))
  have hA4 := consW_afr h4 hA3
  exact RefE.ret rfl ⟨hR2.stage.of_pstep hS4 hA4 (PStep.refl hR2.stage.check.state),
    ((hg1.trans hR2.grow).trans hg3).trans hg4,
    by simpa using (show PSlR decCNS _ _ _ m3 from ⟨hd3, Nat.le_of_eq ht3⟩).grow decCNS_mono hg4,
    by simpa using (show PSlR decISS _ _ _ m4 from ⟨hd4, Nat.le_of_eq ht4⟩),
    by simpa using (show PSlR decCNSB _ _ _ m3 from ⟨hb3, Nat.le_of_eq hbt3⟩).grow decCNSB_mono hg4, hA4⟩

include hq henv hV hOpf hLC hLT hApd hCrk in
/-- **`check_block_ctors` refines `checkBlockCtors`, both outcomes** (at one environment,
`vis0 = vis`, as `check_block_pass` calls it): the shape's level parameters (L only, outside the
verdict closure), then `check_block_ctors_go` by `icbg_ref`; `check_block_ctors_go`'s post from
the memory before the call. -/
theorem ict_ref (hP : CtorsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (m : Mem) (a₀ : AState)
    (pp mo ml co cl : Word)
    (bs : BlockShape) (mss : List MemberShape) (cvs : List IConstantVal)
    (hC : StageC dn vis fe env m a₀) (hqd : DecB (fun m => decBS m pp.toNat) m bs)
    (hsrc : ShapeSrc m pp) (hmss : PSlR decMS mss mo ml m) (hcvs : PSlR decCVp cvs co cl m)
    (hA : AbsOK m) {bsP : ConLeche.BlockShape} {mssP : List ConLeche.MemberShape}
    {cvsP : List ConLeche.ConstantVal}
    (hbsP : ConRon.Bridge.Inductives.dShape a₀.store bs = some bsP)
    (hmssP : mss.mapM (ConRon.Bridge.Inductives.dMember a₀.store) = some mssP)
    (hcvsP : cvs.mapM (Frontend.denoteCV a₀.store) = some cvsP)
    (hws : ∀ cv ∈ cvsP, ConLeche.Expr.WScoped 0 cv.type)
    (hok₀ : ConRon.Bridge.Inductives.IFEnvOKS env fe a₀.store)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    RefE (VerdictCtxU p) (ictE p (n + 1) m vis vis pp mo ml co cl) (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs)
      a₀ (fun v x a' => IcbgPost dn vis fe env m v.1 v.2 x a') := by
  rw [ictE.arm1]
  rcases h1 : lpsW n m pp with _ | ⟨r1, m1⟩
  · rw [liftE_none, ictE.k_block_shape_lps.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, ictE.k_block_shape_lps.arm1]
  obtain ⟨hS1, hg1, hd1, hb1⟩ := lpsW_ok' h1 hC.stage hqd
  have hA1 : AbsOK m1 := lpsW_afr h1 hA
  have hC1 : StageC dn vis fe env m1 a₀ := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hqd hsrc
  have h2 := icbg_ref hq henv hV hOpf hLC hLT hApd hCrk hP pp _ _ bs n hn m1 a₀
    mo ml co cl mss cvs mssP cvsP hC1 (hqd.grow (decBS_mono _) hg1) (partsHsrc_grow hg1 hq9 hsrc) hd1 hb1
    (hmss.grow decMS_mono hg1) (hcvs.grow (fun q => OMono.decCVp q) hg1) hA1 hbsP hmssP hcvsP hws hok₀ hfe
  rcases h2' : icbgE p n m1 vis vis pp (r1.headD 0) (r1.tail.headD 0) mo ml co cl with e2 | ⟨r2, m2⟩
  · rw [h2'] at h2
    rw [ictE.k_check_block_ctors_go.none]; exact h2
  rw [h2'] at h2
  rw [ictE.k_check_block_ctors_go.arm1]
  obtain ⟨x, a2, hrun, hR⟩ := h2
  exact ⟨x, a2, hrun, { hR with grow := hg1.trans hR.grow }⟩

include hq henv hV hOpf hLC hLT hApd hCrk in
/-- **`check_block_ctors` refines `checkBlockCtors`** under `StageC` (at one environment,
`vis0 = vis`, as `check_block_pass` calls it; the denotations as con-ron's `checkBlockCtors_specF`
asks): the stored constructors and their fields' sorts, per member, two slices of `[off, len]`
pointers decoded below the tops; the constructors also with each member slice's bound. -/
@[refines ConRon.Arena.checkBlockCtors]
theorem checkBlockCtors_refinesC (hP : CtorsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (pp mo ml co cl : Word)
    (bs : BlockShape) (mss : List MemberShape) (cvs : List IConstantVal)
    (hC : StageC dn vis fe env s₀.mem a₀) (hqd : DecB (fun m => decBS m pp.toNat) s₀.mem bs)
    (hsrc : ShapeSrc s₀.mem pp) (hmss : PSlR decMS mss mo ml s₀.mem) (hcvs : PSlR decCVp cvs co cl s₀.mem)
    (hA : AbsOK s₀.mem) {bsP : ConLeche.BlockShape} {mssP : List ConLeche.MemberShape}
    {cvsP : List ConLeche.ConstantVal}
    (hbsP : ConRon.Bridge.Inductives.dShape a₀.store bs = some bsP)
    (hmssP : mss.mapM (ConRon.Bridge.Inductives.dMember a₀.store) = some mssP)
    (hcvsP : cvs.mapM (Frontend.denoteCV a₀.store) = some cvsP)
    (hws : ∀ cv ∈ cvsP, ConLeche.Expr.WScoped 0 cv.type)
    (hok₀ : ConRon.Bridge.Inductives.IFEnvOKS env fe a₀.store)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_ctors" [vis, vis, pp, mo, ml, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      PSlR decCNS (AM.res (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs) a₀).1 (r.headD 0)
        (r.tail.headD 0) s'.mem ∧
      PSlR decISS (AM.res (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs) a₀).2 (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) s'.mem ∧
      PSlR decCNSB (AM.res (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs) a₀).1 (r.headD 0)
        (r.tail.headD 0) s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (ictE_spec p hP (n + 1) s₀ vis vis pp mo ml co cl)
    (ict_ref hq henv hV hOpf hLC hLT hApd hCrk hP n hn s₀.mem a₀ pp mo ml co cl bs mss cvs hC hqd hsrc hmss
      hcvs hA hbsP hmssP hcvsP hws hok₀ hfe)) ?_
  rintro _r s' ⟨hl, _, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.cns, by rw [hres]; exact hR.iss,
    by rw [hres]; exact hR.cnsB, hR.abs⟩

end sims

end L.Ind
