import ConAgua.Arena.IndT.Sum5
import ConAgua.Arena.IndT.Install5
import ConAgua.Arena.IndInstallSpec23
import ConAgua.Arena.IndInstallSpec22

/-!
# `checkBlockCtors` under `StageC` (lane `indstaget`)

The constructors of every member, from `StageC` and con-ron's preconditions of
`checkBlockCtors_specF` (the shape, the members and the formers denote, every stored former
closed, the environment denotes and its index spec holds — one environment, `vis0 = vis`, as
`check_block_pass` calls it), the twin side transcribed from that spec's proof: one member's
`checkSumCtors` (`checkSumCtors_refinesC`, con-ron's `checkSumCtors_spec` on its run for the
`CoreStep`), the records and conses (L only), the shape's level parameters (L only).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

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
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (sctsW_spec p hP (realCall p) (realCall_spec p) n _ vis vis T lo ll nP nIdx rs isP lg cvTa co cl) e
  have hfev : fe.restrictTo vis.toNat = fe := by rw [← hC.stage.1.env.vis]; rfl
  have h := sctsW_okC (dn := dn) (vis := vis) (fe := fe) hq henv hV hOpf hLC hLT hApd hCrk vis T lo ll nP nIdx rs isP lg cvTa lps cvv
    hT hrs hws n hn m a co cl cs csP hC hl hlb hcv hcs hA hTP hlpsP hrsP hcvTaP hcsP
    (by rw [hfev]; exact hok₀) hfe r s'.mem hW
  rw [hfev] at h
  obtain ⟨x, a', h1, hC', hg', hd1, hb1, hd2, hb2, hA', hc⟩ := h
  exact ⟨x, a', h1, hC', hg', ⟨hd1, hb1⟩, ⟨hd2, hb2⟩, hA', hc⟩

include hq henv hV hOpf hLC hLT hApd hCrk in
/-- **`check_block_ctors_one` under `StageC`** (twin side: one member of con-ron's
`checkBlockCtors_specF`'s proof). -/
theorem icboW_simC (hP : CtorsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
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
    Sim (icboW p (n + 1) m vis vis pp lo ll ms cv)
      (checkSumCtors V fe fe msh.cvT.name bs.lps bs.nP msh.nIdx bs.resSort bs.isProp bs.large cvv msh.ctors) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        DecB (fun m => decCNS m (r.headD 0).toNat) m' x.1 ∧
        DecB (fun m => decISS m (r.tail.headD 0).toNat) m' x.2 ∧
        DecB (fun m => decCNSB m (r.headD 0).toNat) m' x.1 ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a') := by
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
  rw [icboW.arm1]
  rw [hw0, hw1, hw2, hw3, hnpw]
  refine Sim.tail (K := icboW.k_check_sum_ctors p n) (body := fun r1 m1 => icboW.k_rec2 p n (r1.tail.tail.headD 0)
      (r1.tail.tail.tail.headD 0) (callW p n "rec2"
      [r1.headD 0, r1.tail.headD 0] m1)) rfl (fun _ _ => rfl)
    (by
      have h := installSimSumCtorsC (dn := dn) (fe := fe) hq henv hV hOpf hLC hLT hApd hCrk hP.sum n hn
        (rdW (m.arr64 EREC) (UInt64.ofNat cvp)) lo ll (UInt64.ofNat bs.nP) (UInt64.ofNat msh.nIdx)
        (rdW (m.arr64 IW) (pp + 6)) (rdW (m.arr64 IW) (pp + 8)) (rdW (m.arr64 IW) (pp + 7)) cv co cl
        hn32 hrs32 bs.lps cvv msh.ctors hC hlps hlb hcv hcd hA hTP hlpsP
        (by rw [hrse]; exact hsP) hcvP hws hcsP' hok₀ hfe
      rw [hnm, hrse, h8, h7, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib] at h
      exact h) ?_
  rintro r1 ⟨cs, ss⟩ m1 a1 ⟨hC1, hg1, hcs1, hss1, hA1, c1⟩ r' m' e
  obtain ⟨⟨r2, m2⟩, h2, e⟩ := of_K e rfl; rw [icboW.k_rec2.arm1] at e
  obtain ⟨hS2, hg2, hd2⟩ := installRec2PSl hP decCN_mono h2 hC1.stage hcs1
  have hd2b := installRec2PSlB hP decCN_mono h2 hC1.stage hcs1
  have hA2 : AbsOK m2 := by
    obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (rec2_specW p hP.alloc n hP.rec2 _ _ _) h2
    exact recW_afr hW hA1
  obtain ⟨⟨r3, m3⟩, h3, e⟩ := of_K e rfl; rw [icboW.k_rec2_2.arm1] at e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
  obtain ⟨hS3, hg3, hd3⟩ := installRec2PSl hP decIS_mono h3 hS2 (hss1.grow decIS_mono hg2)
  have hA3 : AbsOK m3 := by
    obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (rec2_specW p hP.alloc n hP.rec2 _ _ _) h3
    exact recW_afr hW hA2
  exact ⟨hC1.of_pstep hS3 hA3 (PStep.refl hC1.check.state), (hg1.trans hg2).trans hg3,
    hd2.grow (decCNS_mono _) hg3, hd3, hd2b.grow (decCNSB_mono _) hg3, hA3, c1⟩

include hq henv hV hOpf hLC hLT hApd hCrk in
/-- **`check_block_ctors_go` under `StageC`** (twin side: con-ron's `checkBlockCtors_specF`'s
proof). -/
theorem icbgW_simC (hP : CtorsProg p) (pp lo ll : Word) (bs : BlockShape) {bsP : ConLeche.BlockShape}
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
    Sim (icbgW p n m vis vis pp lo ll mo ml co cl) (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        PSlR decCNS x.1 (r.headD 0) (r.tail.headD 0) m' ∧
        PSlR decISS x.2 (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) m' ∧
        PSlR decCNSB x.1 (r.headD 0) (r.tail.headD 0) m' ∧ AbsOK m') := by
  induction n with
  | zero => intros; rw [icbgW.eq_1]; exact Sim.of_none
  | succ n ih =>
  intro m a mo ml co cl mss cvs mssP cvsP hC hqd hsrc hlps hlb hmss hcvs hA hbsP hmssP hcvsP hws hok₀ hfe
  by_cases hml : ml = 0
  · rw [icbgW.arm1 p n m vis vis pp lo ll mo ml co cl hml]
    have : mss = [] := by
      have h := hmss.1; simp only [DecB, hml] at h
      simpa [decPL] using h.symm
    subst this
    exact Sim.ret ⟨hC, IWGrow.refl m, PSlR.nil decCNS m, PSlR.nil decISS m, PSlR.nil decCNSB m, hA⟩
  by_cases hcl : cl = 0
  · rw [icbgW.arm2 p n m vis vis pp lo ll mo ml co cl hml hcl]
    have : cvs = [] := by
      have h := hcvs.1; simp only [DecB, hcl] at h
      simpa [decPL] using h.symm
    subst this
    have : ConRon.Arena.checkBlockCtors V fe fe bs mss [] = pure ([], []) := by
      cases mss <;> simp [ConRon.Arena.checkBlockCtors]
    rw [this]
    exact Sim.ret ⟨hC, IWGrow.refl m, PSlR.nil decCNS m, PSlR.nil decISS m, PSlR.nil decCNSB m, hA⟩
  obtain ⟨q, msh, rest, rfl, hw, hqb, hdm, hrest⟩ := partsPSl_cons hmss hml
  obtain ⟨c, cvv, cvs', rfl, hwc, hcb, hdc, hcvs'⟩ := partsPSl_cons hcvs hcl
  obtain ⟨msP, restP, rfl, hmP, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmssP
  obtain ⟨cvP, cvsP', rfl, hcvP, hcvsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcvsP
  rw [icbgW.arm3 p n m vis vis pp lo ll mo ml co cl hml hcl, hw, hwc]
  simp only [ConRon.Arena.checkBlockCtors]
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  rcases n with _ | k
  · rw [callW_zero]; rw [icbgW.k_check_block_ctors_one.none]; exact Sim.of_none
  refine Sim.bindK (K := icbgW.k_check_block_ctors_one p (k + 1) vis vis pp lo ll mo ml co cl)
      (body := fun r1 m1 => icbgW.k_check_block_ctors_go p (k + 1) (r1.headD 0) (r1.tail.headD 0)
      (icbgW p (k + 1) m1 vis vis pp lo ll (mo + 1) (ml - 1) (co + 1) (cl - 1))) (icbgW.k_check_block_ctors_one.none ..)
      (fun r m₁ => icbgW.k_check_block_ctors_one.arm1 p (k + 1) vis vis pp lo ll mo ml co cl r m₁)
    (Q := fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        DecB (fun m => decCNS m (r.headD 0).toNat) m' x.1 ∧
        DecB (fun m => decISS m (r.tail.headD 0).toNat) m' x.2 ∧
        DecB (fun m => decCNSB m (r.headD 0).toNat) m' x.1 ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a')
    (fun r m' e => by
      obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
        (icbo_spec p hP.one (k + 1) _ vis vis pp lo ll (UInt64.ofNat q) (UInt64.ofNat c)) e
      exact icboW_simC hq henv hV hOpf hLC hLT hApd hCrk hP k (by omega) hC hqd hsrc hlps hlb (by rw [hq']; exact hdm)
        (by rw [hc']; exact hdc) hA hbsP hmP hcvP (hws _ List.mem_cons_self) hok₀ hfe r s'.mem hW) ?_
  rintro r1 ⟨cs, ss⟩ m1 a1 ⟨hC1, hg1, hd1, he1, hb1, hA1, c1⟩
  dsimp only
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hqd hsrc
  have x1 := c1.ext
  refine Sim.bindK (K := icbgW.k_check_block_ctors_go p (k + 1) (r1.headD 0) (r1.tail.headD 0))
      (body := fun r2 m2 => icbgW.k_sl_cons p (k + 1) (r1.tail.headD 0) (r2.tail.tail.headD 0)
        (r2.tail.tail.tail.headD 0)
      (callW p (k + 1) "sl_cons" [r1.headD 0, r2.headD 0, r2.tail.headD 0] m2)) rfl (fun _ _ => rfl)
    (ih (by omega) m1 a1 (mo + 1) (ml - 1) (co + 1) (cl - 1) rest cvs' restP cvsP' hC1
      (hqd.grow (decBS_mono _) hg1)
      (partsHsrc_grow hg1 hq9 hsrc) (by rw [decHL_grow3 hg1 hlb]; exact hlps) (Nat.le_trans hlb hg1.1)
      (hrest.grow decMS_mono hg1) (hcvs'.grow (fun q => OMono.decCVp q) hg1) hA1
      (ConRon.Bridge.Inductives.dShape_ext x1 _ _ hbsP)
      (ConRon.Bridge.Inductives.dMember_ext.list x1 _ _ hrestP)
      (ConRon.Bridge.Inductives.dExt_denoteCV.list x1 _ _ hcvsP')
      (fun cv h => hws cv (List.mem_cons_of_mem _ h)) (hok₀.mono x1)
      (ConRon.Bridge.denoteFEnv_mono x1 hfe)) ?_
  rintro r2 ⟨rc, rs⟩ m2 a2 ⟨hC2, hg2, hc2, hs2, hcb2, hA2⟩
  dsimp only
  refine Sim.mstep (K := icbgW.k_sl_cons p (k + 1) (r1.tail.headD 0) (r2.tail.tail.headD 0)
    (r2.tail.tail.tail.headD 0)) rfl (fun _ _ => rfl) fun r3 m3 h3 => ?_
  obtain ⟨hS3, hg3, hd3⟩ := installConsRun hP.toCstProg decCNS_mono h3 hC2.stage hc2
    (hd1.grow (decCNS_mono _) hg2)
  obtain ⟨-, -, hb3⟩ := installConsRun hP.toCstProg decCNSB_mono h3 hC2.stage hcb2
    (hb1.grow (decCNSB_mono _) hg2)
  have hA3 := installCons_afr hP.toCstProg h3 hA2
  refine Sim.mstep (K := icbgW.k_sl_cons_2 p (r3.headD 0) (r3.tail.headD 0)) rfl (fun _ _ => rfl) fun r4 m4 h4 => ?_
  obtain ⟨hS4, hg4, hd4⟩ := installConsRun hP.toCstProg decISS_mono h4 hS3 (hs2.grow decISS_mono hg3)
    (he1.grow (decISS_mono _) (hg2.trans hg3))
  have hA4 := installCons_afr hP.toCstProg h4 hA3
  exact Sim.ret ⟨hC2.of_pstep hS4 hA4 (PStep.refl hC2.check.state), ((hg1.trans hg2).trans hg3).trans hg4,
    by simpa using hd3.grow decCNS_mono hg4, by simpa using hd4, by simpa using hb3.grow decCNSB_mono hg4, hA4⟩

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
  refine triple_post (ict_spec p hP.ctors (n + 1) s₀ vis vis pp mo ml co cl) ?_
  rintro r s' ⟨hl, hm⟩
  have hsim : Sim (ictW p (n + 1) s₀.mem vis vis pp mo ml co cl) (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs) a₀
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow s₀.mem m' ∧
        PSlR decCNS x.1 (r.headD 0) (r.tail.headD 0) m' ∧
        PSlR decISS x.2 (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) m' ∧
        PSlR decCNSB x.1 (r.headD 0) (r.tail.headD 0) m' ∧ AbsOK m') := by
    rw [ictW.arm1]
    refine Sim.mstep (K := ictW.k_block_shape_lps p n vis vis pp mo ml co cl) rfl (fun _ _ => rfl) fun r1 m1 h1 => ?_
    obtain ⟨s1, rfl, -, hW1, -⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (blockShapeLps_spec2 p hP.alloc hP.erCopy hP.erToIw hP.lps n _ pp) h1
    obtain ⟨hS1, hg1, hd1, hb1⟩ := lpsW_ok' hW1 hC.stage hqd
    have hA1 : AbsOK s1.mem := lpsW_afr hW1 hA
    have hC1 : StageC dn vis fe env s1.mem a₀ := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
    obtain ⟨-, hq9, -⟩ := partsShapeFacts hqd hsrc
    refine Sim.post (K := ictW.k_check_block_ctors_go p) rfl (fun _ _ => rfl) (fun r2 m2 e => icbgW_simC hq henv hV hOpf hLC hLT hApd hCrk hP pp _ _ bs n hn s1.mem a₀
      mo ml co cl mss cvs mssP cvsP hC1 (hqd.grow (decBS_mono _) hg1) (partsHsrc_grow hg1 hq9 hsrc) hd1 hb1
      (hmss.grow decMS_mono hg1) (hcvs.grow (fun q => OMono.decCVp q) hg1) hA1 hbsP hmssP hcvsP hws hok₀ hfe
      r2 m2 (by
        obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
          (icbg_spec p hP.go n _ vis vis pp (r1.headD 0) (r1.tail.headD 0) mo ml co cl) e
        exact hW2)) ?_
    rintro r2 x m2 a2 ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, hg1.trans h2, h3, h4, h5, h6⟩
  obtain ⟨hok, hQ⟩ := Sim.run hsim hm
  exact ⟨hl, hok, hQ⟩

end sims

end L.Ind
