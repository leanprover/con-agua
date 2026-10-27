import ConAgua.Verdict.IndA3
import ConAgua.Verdict.IndBE
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

/-!
# `check_block_ctors`' error claim (lane `verdicts-b`, helper `ia2`, fork `blk`)

`check_block_ctors_one` (`icboE_claim`: `check_sum_ctors`' claim `CheckSumCtorsE`, the `rec2`s
claim nothing), `check_block_ctors_go` (`icbgE_claim`, by induction on the fuel; the head's ok run
by `icboW_simC`), `check_block_ctors` (`checkBlockCtorsE_claim`: `CheckBlockCtorsE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model ictE_spec (p : Prog) (hf : p.lookup "check_block_ctors" = some checkBlockCtors)
  fns [hf ↦ ictE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model icbgE_spec (p : Prog) (hf : p.lookup "check_block_ctors_go" = some checkBlockCtorsGo)
  fns [hf ↦ icbgE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model icboE_spec (p : Prog) (hf : p.lookup "check_block_ctors_one" = some checkBlockCtorsOne)
  fns [hf ↦ icboE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

theorem blkE1_nv : ∀ f ∈ ["sl_cons", "rec2", "block_shape_lps"], f ∈ _root_.L.Checker.nvFns :=
  _root_.L.Checker.nv_sub (by decide +kernel)

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p) (hOpf : OpfF p) (hLC : LvlCacheProg p)
  (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
  (eSC : CheckSumCtorsE p)

include hq henv hV hOpf hLC hLT hApd hCrk hnv eSC in
/-- **`check_block_ctors_one`'s error claim** (the model at fuel `n + 1`; `icboW_simC`'s
hypotheses). -/
theorem icboE_claim (hP : CtorsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
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
    (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) (e : Err)
    (he : icboE p (n + 1) m vis vis pp lo ll ms cv = .error e) :
    ErrClaim (checkSumCtors V fe fe msh.cvT.name bs.lps bs.nP msh.nIdx bs.resSort bs.isProp bs.large cvv
      msh.ctors) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hsz := hS.2.2.2.1
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
  have hfev : fe.restrictTo vis.toNat = fe := by rw [← hC.stage.1.env.vis]; rfl
  rw [icboE.arm1, hw0, hw1, hw2, hw3, hnpw] at he
  cases h1 : callE p n "check_sum_ctors" [vis, vis, rdW (m.arr64 EREC) (UInt64.ofNat cvp), lo, ll,
      UInt64.ofNat bs.nP, UInt64.ofNat msh.nIdx, rdW (m.arr64 IW) (pp + 6), rdW (m.arr64 IW) (pp + 8),
      rdW (m.arr64 IW) (pp + 7), cv, co, cl] m with
  | error e1 =>
    rw [h1, icboE.k_check_sum_ctors.none] at he
    cases he
    have h := eSC hq henv hV hOpf hLC hLT hApd hCrk hP.sum ⟨m, Locals.init []⟩ a vis
      (rdW (m.arr64 EREC) (UInt64.ofNat cvp)) lo ll (UInt64.ofNat bs.nP) (UInt64.ofNat msh.nIdx)
      (rdW (m.arr64 IW) (pp + 6)) (rdW (m.arr64 IW) (pp + 8)) (rdW (m.arr64 IW) (pp + 7)) cv co cl
      bs.lps cvv msh.ctors hC hn32 hrs32 hlps hlb hcv hcd hA hTP hlpsP
      (by rw [hrse]; exact hsP) hcvP hws hcsP' (by rw [hfev]; exact hok₀) hfe n hn _ h1
    rw [hfev, hnm, hrse, h8, h7, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib] at h
    exact h
  | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, icboE.k_check_sum_ctors.arm1] at he
    cases h2 : callE p n "rec2" [r1.headD 0, r1.tail.headD 0] m1 with
    | error e2 =>
      rw [h2, icboE.k_rec2.none] at he; cases he
      exact ErrClaim.of_callE_nv hnv (blkE1_nv _ (by simp)) h2
    | ok q2 =>
      obtain ⟨r2, m2⟩ := q2
      rw [h2, icboE.k_rec2.arm1] at he
      cases h3 : callE p n "rec2" [r1.tail.tail.headD 0, r1.tail.tail.tail.headD 0] m2 with
      | error e3 =>
        rw [h3, icboE.k_rec2_2.none] at he; cases he
        exact ErrClaim.of_callE_nv hnv (blkE1_nv _ (by simp)) h3
      | ok q3 =>
        obtain ⟨r3, m3⟩ := q3
        rw [h3, icboE.k_rec2_2.arm1] at he; cases he

include hq henv hV hOpf hLC hLT hApd hCrk hnv eSC in
/-- **`check_block_ctors_go`'s error claim** (the model at fuel `n`; `icbgW_simC`'s hypotheses). -/
theorem icbgE_claim (hP : CtorsProg p) (pp lo ll : Word) (bs : BlockShape) {bsP : ConLeche.BlockShape}
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
    ∀ e, icbgE p n m vis vis pp lo ll mo ml co cl = .error e →
      ErrClaim (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs) a e := by
  induction n with
  | zero =>
    intro m a mo ml co cl mss cvs mssP cvsP _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he
    rw [icbgE.eq_1] at he; cases he; exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a mo ml co cl mss cvs mssP cvsP hC hqd hsrc hlps hlb hmss hcvs hA hbsP hmssP hcvsP hws hok₀ hfe e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  by_cases hml : ml = 0
  · rw [icbgE.arm1 p n m vis vis pp lo ll mo ml co cl hml] at he; cases he
  by_cases hcl : cl = 0
  · rw [icbgE.arm2 p n m vis vis pp lo ll mo ml co cl hml hcl] at he; cases he
  obtain ⟨q, msh, rest, rfl, hw, hqb, hdm, hrest⟩ := partsPSl_cons hmss hml
  obtain ⟨c, cvv, cvs', rfl, hwc, hcb, hdc, hcvs'⟩ := partsPSl_cons hcvs hcl
  obtain ⟨msP, restP, rfl, hmP, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmssP
  obtain ⟨cvP, cvsP', rfl, hcvP, hcvsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcvsP
  rw [icbgE.arm3 p n m vis vis pp lo ll mo ml co cl hml hcl, hw, hwc] at he
  simp only [ConRon.Arena.checkBlockCtors]
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  cases h1 : callE p n "check_block_ctors_one" [vis, vis, pp, lo, ll, UInt64.ofNat q, UInt64.ofNat c] m with
  | error e1 =>
    rw [h1, icbgE.k_check_block_ctors_one.none] at he
    cases he
    have hW := triple_of_callE_err (icboE_spec p hP.one n ⟨m, Locals.init []⟩ vis vis pp lo ll
      (UInt64.ofNat q) (UInt64.ofNat c)) h1 (Err.code_ne_of_cls hk0)
    simp only at hW
    cases n with
    | zero => rw [icboE.eq_1] at hW; cases hW; exact absurd Err.cls_outOfFuel hk0
    | succ k =>
    exact ErrClaim.bind_left (icboE_claim hq henv hV hOpf hLC hLT hApd hCrk hnv eSC hP k (by omega) hC hqd hsrc
      hlps hlb (by rw [hq']; exact hdm) (by rw [hc']; exact hdc) hA hbsP hmP hcvP (hws _ List.mem_cons_self)
      hok₀ hfe _ hW)
  | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, icbgE.k_check_block_ctors_one.arm1] at he
    cases n with
    | zero => have := callW_of_callE h1; rw [callW_zero] at this; cases this
    | succ k =>
    obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (icbo_spec p hP.one (k + 1) _ vis vis pp lo ll (UInt64.ofNat q) (UInt64.ofNat c)) (callW_of_callE h1)
    subst hs'
    obtain ⟨⟨cs, ss⟩, a1, hrun1, hC1, hg1, hd1, he1, hb1, hA1, c1⟩ :=
      icboW_simC hq henv hV hOpf hLC hLT hApd hCrk hP k (by omega) hC hqd hsrc hlps hlb (by rw [hq']; exact hdm)
        (by rw [hc']; exact hdc) hA hbsP hmP hcvP (hws _ List.mem_cons_self) hok₀ hfe r1 _ hW
    refine ErrClaim.bind_right hrun1 ?_
    dsimp only
    obtain ⟨-, hq9, -⟩ := partsShapeFacts hqd hsrc
    have x1 := c1.ext
    cases h2 : icbgE p (k + 1) s'.mem vis vis pp lo ll (mo + 1) (ml - 1) (co + 1) (cl - 1) with
    | error e2 =>
      rw [h2, icbgE.k_check_block_ctors_go.none] at he
      cases he
      exact ErrClaim.bind_left (ih (by omega) s'.mem a1 (mo + 1) (ml - 1) (co + 1) (cl - 1) rest cvs' restP cvsP' hC1
        (hqd.grow (decBS_mono _) hg1)
        (partsHsrc_grow hg1 hq9 hsrc) (by rw [decHL_grow3 hg1 hlb]; exact hlps) (Nat.le_trans hlb hg1.1)
        (hrest.grow decMS_mono hg1) (hcvs'.grow (fun q => OMono.decCVp q) hg1) hA1
        (ConRon.Bridge.Inductives.dShape_ext x1 _ _ hbsP)
        (ConRon.Bridge.Inductives.dMember_ext.list x1 _ _ hrestP)
        (ConRon.Bridge.Inductives.dExt_denoteCV.list x1 _ _ hcvsP')
        (fun cv h => hws cv (List.mem_cons_of_mem _ h)) (hok₀.mono x1)
        (ConRon.Bridge.denoteFEnv_mono x1 hfe) _ h2)
    | ok q2 =>
      obtain ⟨r2, m2⟩ := q2
      rw [h2, icbgE.k_check_block_ctors_go.arm1] at he
      cases h3 : callE p (k + 1) "sl_cons" [r1.headD 0, r2.headD 0, r2.tail.headD 0] m2 with
      | error e3 =>
        rw [h3, icbgE.k_sl_cons.none] at he; cases he
        exact ErrClaim.of_callE_nv hnv (blkE1_nv _ (by simp)) h3
      | ok q3 =>
        obtain ⟨r3, m3⟩ := q3
        rw [h3, icbgE.k_sl_cons.arm1] at he
        cases h4 : callE p (k + 1) "sl_cons" [r1.tail.headD 0, r2.tail.tail.headD 0,
            r2.tail.tail.tail.headD 0] m3 with
        | error e4 =>
          rw [h4, icbgE.k_sl_cons_2.none] at he; cases he
          exact ErrClaim.of_callE_nv hnv (blkE1_nv _ (by simp)) h4
        | ok q4 =>
          obtain ⟨r4, m4⟩ := q4
          rw [h4, icbgE.k_sl_cons_2.arm1] at he; cases he

end sims

/-- **`check_block_ctors`'s error claim** (`CheckBlockCtorsE`, the `err_stmt` of
`checkBlockCtors_refinesC`), from `check_sum_ctors`'s. -/
theorem checkBlockCtorsE_claim {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (eSC : CheckSumCtorsE p) : CheckBlockCtorsE p := by
  intro hq dn vis fe env henv hV hOpf hLC hLT hApd hCrk hP s₀ a₀ pp mo ml co cl bs mss cvs hC hqd hsrc hmss
    hcvs hA bsP mssP cvsP hbsP hmssP hcvsP hws hok₀ hfe F hF e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (ictE_spec p hP.ctors F ⟨s₀.mem, Locals.init []⟩ vis vis pp mo ml co cl) he
    (Err.code_ne_of_cls hk0)
  simp only at he
  cases F with
  | zero => rw [ictE.eq_1] at he; cases he; exact absurd Err.cls_outOfFuel hk0
  | succ n =>
  rw [ictE.arm1] at he
  cases h1 : callE p n "block_shape_lps" [pp] s₀.mem with
  | error e1 =>
    rw [h1, ictE.k_block_shape_lps.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (blkE1_nv _ (by simp)) h1
  | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, ictE.k_block_shape_lps.arm1] at he
    obtain ⟨s1, hs1, -, hW1, -⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (blockShapeLps_spec2 p hP.alloc hP.erCopy hP.erToIw hP.lps n _ pp) (callW_of_callE h1)
    subst hs1
    obtain ⟨hS1, hg1, hd1, hb1⟩ := lpsW_ok' hW1 hC.stage hqd
    have hA1 : AbsOK s1.mem := lpsW_afr hW1 hA
    have hC1 : StageC dn vis fe env s1.mem a₀ := hC.of_pstep hS1 hA1 (ConRon.Bridge.Inductives.PStep.refl hC.check.state)
    obtain ⟨-, hq9, -⟩ := partsShapeFacts hqd hsrc
    cases h2 : callE p n "check_block_ctors_go" [vis, vis, pp, r1.headD 0, r1.tail.headD 0, mo, ml, co, cl] s1.mem with
    | error e2 =>
      rw [h2, ictE.k_check_block_ctors_go.none] at he; cases he
      have hW := triple_of_callE_err (icbgE_spec p hP.go n ⟨s1.mem, Locals.init []⟩ vis vis pp (r1.headD 0)
        (r1.tail.headD 0) mo ml co cl) h2 (Err.code_ne_of_cls hk0)
      simp only at hW
      exact icbgE_claim hq henv hV hOpf hLC hLT hApd hCrk hnv eSC hP pp _ _ bs n (by omega) s1.mem a₀
        mo ml co cl mss cvs mssP cvsP hC1 (hqd.grow (decBS_mono _) hg1) (partsHsrc_grow hg1 hq9 hsrc) hd1 hb1
        (hmss.grow decMS_mono hg1) (hcvs.grow (fun q => OMono.decCVp q) hg1) hA1 hbsP hmssP hcvsP hws hok₀ hfe
        _ hW
    | ok q2 =>
      obtain ⟨r2, m2⟩ := q2
      rw [h2, ictE.k_check_block_ctors_go.arm1] at he; cases he

end L.Ind
