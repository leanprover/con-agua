import ConAgua.Arena.IndT.Sum3
import ConAgua.Arena.IndInstallSpec.GrcProg
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl
import ConAgua.Verdict.PosTopEMono
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndT.Install1

/-!
# `check_block_idx_sorts`: one model and one refinement for both outcomes

`iisE` (`check_block_idx_sorts_one`) and `iisrE` (`check_block_idx_sorts`), `l_model … unified`:
`open_pis_at_fvars_f`, `rec2` and `sl_cons` (outside the verdict closure) through their `Option`
models, `check_struct_field_sorts_i` through its run (`callE`; its ok half by its `Option` spec
and `fsorts_ref` from the run, its error half by `fsorts_ref` and `RefE.run_err`), the member check
through its unified model. `iis_ref` and `iisr_ref` refine `idxOneAM` and `checkBlockIdxSorts`
for both outcomes; `checkBlockIdxSorts_refinesC` is the ok half.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model iisE_spec (p : Prog) (hP : IdxProg p) (hOpf : OpfF p)
  fns [hP.one ↦ iisE]
  specs [opfF_spec p hOpf n, rec2_specW p hP.alloc n hP.rec2]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model iisrE_spec (p : Prog) (hP : IdxProg p) (hOpf : OpfF p)
  fns [hP.idx ↦ iisrE]
  specs [iisE_spec p hP hOpf n, slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem iisE_k_opf_eq (p : Prog) (n : Nat) (vis nP ni srt : Word) (r : List Word) (m₁ : Mem)
    (h : r.headD 0 ≠ 0) :
    iisE.k_open_pis_at_fvars_f p n vis nP ni srt (.ok (r, m₁)) =
      iisE.j1 p n vis nP ni srt (idxTail nP (r.tail.headD 0) (r.tail.tail.headD 0)).1
        (idxTail nP (r.tail.headD 0) (r.tail.tail.headD 0)).2 m₁ := by
  unfold idxTail
  by_cases hl : nP < r.tail.tail.headD 0
  · rw [iisE.k_open_pis_at_fvars_f.arm1 _ _ _ _ _ _ _ _ h hl, ite_eq_left hl, UInt64.add_comm]
  · rw [iisE.k_open_pis_at_fvars_f.arm2 _ _ _ _ _ _ _ _ h hl, ite_eq_right hl]

/-- What `check_block_idx_sorts_one` gives besides the twin's index sorts `x` (from `m`, `a`): the
stage relation, growth, the sorts a slice behind the result word, the abstraction memos, the twin's
core step. -/
structure IisPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (w : Word) (m' : Mem) (x : List LIdx) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  sorts : DecB (fun m => decIS m w.toNat) m' x
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'

/-- What `check_block_idx_sorts` gives besides the twin's sorts `xs` (from `m`, `a`): as
`IisPost`, the sorts a slice of pointers `[r₀, r₁]`. -/
structure IisrPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (r : List Word) (m' : Mem) (xs : List (List LIdx)) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  sorts : PSlR decIS xs (r.headD 0) (r.tail.headD 0) m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env fe a a'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)

include hq henv hLC hLT in
/-- **`check_block_idx_sorts_one` refines one member of `checkBlockIdxSorts`** (`idxOneAM`), both
outcomes: an error is `check_struct_field_sorts_i`'s (its claim) or of class `0`. -/
theorem iis_ref (hP : IdxProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {pp ms cv : Word} {bs : BlockShape} {msh : MemberShape} {cvv : IConstantVal}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hqd : DecB (fun m => decBS m pp.toNat) m bs)
    (hsrc : ShapeSrc m pp)
    (hms : DecB (fun m => decMS m ms.toNat) m msh) (hcv : DecB (fun m => decCVp m cv.toNat) m cvv)
    {bsP : ConLeche.BlockShape} {cvP : ConLeche.ConstantVal}
    (hbsP : ConRon.Bridge.Inductives.dShape a.store bs = some bsP)
    (hcvP : Frontend.denoteCV a.store cvv = some cvP) (hw : ConLeche.Expr.WScoped 0 cvP.type)
    (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    RefE (VerdictCtx p) (iisE p n m vis pp ms cv) (idxOneAM fe bs msh cvv) a
      (fun v x a' => IisPost dn vis fe env m a v.1 v.2 x a') := by
  rcases n with _ | n
  · rw [iisE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  have hS := hC.stage
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hqd hsrc
  obtain ⟨hnpw, hnpb, hrs32, hrse⟩ := partsShapeWords (IWGrow.refl m) hqd hq9
  have hmsT : decMS (truncM m) ms.toNat = some msh := hms
  obtain ⟨-, hni, -⟩ := decMS_some hmsT
  have hnilt := partsIwLt hni
  obtain ⟨hw1, hnib, -⟩ := partsIwRd hni (w := ms + 1) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨htyl, htye⟩ := partsCVType hcv (w := cv) rfl
  obtain ⟨-, -, -, -, hsP, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hbsP
  by_cases hov : rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (ms + 1) < rdW (m.arr64 IW) (pp + 4)
  · rw [iisE.abort1 p n m vis pp ms cv hov]; exact RefE.of_cls0 rfl
  rw [iisE.arm1 p n m vis pp ms cv hov, hnpw, hw1]
  rw [hnpw, hw1] at hov
  have hk : (UInt64.ofNat bs.nP + UInt64.ofNat msh.nIdx : Word).toNat = bs.nP + msh.nIdx := by
    rw [partsAddNoOv hov, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib]
  unfold idxOneAM
  -- `open_pis_at_fvars_f`
  rcases h1 : opfF m [UInt64.ofNat bs.nP + UInt64.ofNat msh.nIdx, rdW (m.arr64 EREC) (cv + 3), 0]
    with _ | ⟨r1, m1⟩
  · rw [liftE_none, iisE.k_open_pis_at_fvars_f.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨x1, a1, hr1, hS1, hg1, hd1, hA1⟩ := opfF_okRA htyl h1 hS hA
  rw [hk, htye] at hr1
  refine RefE.bind_right hr1 ?_
  obtain ⟨p1, ho1⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC.check.state
    (ConRon.Bridge.denoteCV_type hcvP) hr1
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hd1
    rw [iisE.k_open_pis_at_fvars_f.abort1 _ _ _ _ _ _ _ _ h0]; exact RefE.of_cls0 rfl
  | some fb =>
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨xsP, xP, htq, hxs, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho1
  obtain ⟨h1', hfv, -⟩ := hd1
  obtain ⟨hfd, hfb⟩ := hfv
  have g1 : r1.getD 1 0 = r1.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r1.getD (1 + 1) 0 = r1.tail.tail.headD 0 := by
    rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  rw [iisE_k_opf_eq _ _ _ _ _ _ _ _ (by rw [h1']; decide), iisE.j1.arm1]
  show RefE _ _ (checkStructFieldSortsI V fe true false bs.resSort bs.nP (fvs.drop bs.nP) [] msh.nIdx) a1 _
  obtain ⟨hdT, hbT⟩ := installIdxTail (k := UInt64.ofNat bs.nP) hfd hfb
  rw [UInt64.toNat_ofNat_of_lt' hnpb] at hdT
  have hxPos : ∀ (i : Nat), i < (UInt64.ofNat msh.nIdx : Word).toNat → ∀ (x : ConLeche.Expr),
      (xsP.drop bs.nP)[i]? = some x →
      ConLeche.Expr.WScoped ((UInt64.ofNat bs.nP : Word).toNat + i) x.fvarTypeD := by
    intro i _ x hx
    rw [List.getElem?_drop] at hx
    have := ConRon.Bridge.Inductives.openers_typeD_WScoped htq hw (bs.nP + i) x hx
    rw [UInt64.toNat_ofNat_of_lt' hnpb]
    simpa using this
  have hxsd := ConRon.Bridge.Inductives.denoteEList_drop hxs bs.nP
  have hsP1 := ConRon.Bridge.denoteL_ext hsP p1.ext
  -- `check_struct_field_sorts_i` (through its run)
  rcases h2 : callE p n "check_struct_field_sorts_i" [vis, 1, 0, rdW (m.arr64 IW) (pp + 6), UInt64.ofNat bs.nP,
      (idxTail (UInt64.ofNat bs.nP) (r1.tail.headD 0) (r1.tail.tail.headD 0)).1,
      (idxTail (UInt64.ofNat bs.nP) (r1.tail.headD 0) (r1.tail.tail.headD 0)).2, 0, 0,
      UInt64.ofNat msh.nIdx] m1 with e2 | ⟨r2, m2⟩
  · rw [iisE.k_check_struct_field_sorts_i.none]
    intro hG hk0
    have h := RefE.run_err (fsortsE_spec p hP.sum.hcfs hP.sum.hcfg hP.sum.ha hP.sum.ad.ftd hP.sum.hfsb (n + 1)
      ⟨m1, Locals.init []⟩ vis 1 0 (rdW (m.arr64 IW) (pp + 6)) (UInt64.ofNat bs.nP) _ _ 0 0 (UInt64.ofNat msh.nIdx))
      hG.nv hG (fsorts_ref hq henv hLC hLT hP.sum.hg hP.sum.hpw hP.sum.het hP.sum.hcn n (by omega) m1 a1 1 0
        (rdW (m.arr64 IW) (pp + 6)) (UInt64.ofNat bs.nP) _ _ 0 0 (UInt64.ofNat msh.nIdx) (fvs.drop bs.nP) [] hC1
        hA1 hdT hbT (by simp [decHL, hslice?]) (by simp) hrs32 (by rw [hrse]; exact hsP1)
        (by rw [← partsAddNoOv hov]; exact UInt64.toNat_lt _) hxsd hxPos) (callE_err_mono n.le_succ h2 hk0)
    rw [hrse, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib,
      show ((1 : Word) != 0) = true from rfl, show ((0 : Word) != 0) = false from rfl] at h
    exact h hk0
  rw [iisE.k_check_struct_field_sorts_i.arm1]
  have hsim := installSimFsortsC (dn := dn) (fe := fe) hq henv hLC hLT hP.sum n (by omega) 1 0
    (rdW (m.arr64 IW) (pp + 6)) (UInt64.ofNat bs.nP) _ _ 0 0 (UInt64.ofNat msh.nIdx) hrs32
    (fvs.drop bs.nP) [] hC1 hA1 (by rw [hrse]; exact hsP1) hdT hbT (by simp [decHL, hslice?]) (by simp)
    (by rw [← partsAddNoOv hov]; exact UInt64.toNat_lt _) hxsd hxPos
  rw [hrse, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib,
    show ((1 : Word) != 0) = true from rfl, show ((0 : Word) != 0) = false from rfl] at hsim
  obtain ⟨isorts, a2, hr2, hC2, hg2, hdl, hbl, hA2⟩ := hsim r2 m2 (callW_of_callE h2)
  obtain ⟨c2, -⟩ := ConRon.Bridge.Inductives.checkStructFieldSortsI_spec fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv true false bs.resSort bsP.resSort bs.nP (fvs.drop bs.nP) []
    (xsP.drop bs.nP) [] msh.nIdx (fun i hi x hx => by
      have := hxPos i (by rw [UInt64.toNat_ofNat_of_lt' hnib]; exact hi) x hx
      rwa [UInt64.toNat_ofNat_of_lt' hnpb] at this) a1 a2 isorts hC1.check
    ⟨hsP1, hxsd, rfl, ConRon.Bridge.denoteFEnv_mono p1.ext hfe⟩ hr2
  -- `rec2` (L only)
  rcases h3 : recW m2 2 [r2.headD 0, r2.tail.headD 0] with _ | ⟨r3, m3⟩
  · rw [liftE_none, iisE.k_rec2.eq_1]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, iisE.k_rec2.eq_2]
  obtain ⟨hS3, hg3, hr3, hget, htop⟩ := recW_stage h3 hC2.stage rfl
  have hA3 := recW_afr h3 hA2
  subst hr3
  refine RefE.ret hr2 ⟨hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state), (hg1.trans hg2).trans hg3, ?_, hA3,
    (p1.toCore hC.check).trans c2⟩
  simp only [List.headD_cons]
  have hq0 : (rdW (m2.arr64 CTL) 200).toNat < iwTop m3 := by rw [htop]; simp [iwTop]
  have hq1 : (rdW (m2.arr64 CTL) 200).toNat + 1 < iwTop m3 := by rw [htop]; simp [iwTop]
  show decIS (truncM m3) _ = some isorts
  have w0 : iwN (truncM m3) (rdW (m2.arr64 CTL) 200).toNat = some (r2.headD 0).toNat := by
    rw [iwN_truncM hq0]; have := hget 0 (by simp); simp only [Nat.add_zero] at this
    simp [iwN, nat?, iwA, this]
  have w1 : iwN (truncM m3) ((rdW (m2.arr64 CTL) 200).toNat + 1) = some (r2.tail.headD 0).toNat := by
    rw [iwN_truncM hq1]; have := hget 1 (by simp)
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
    simp [iwN, nat?, iwA, this]
  have hdB := (decHL_decB hdl hbl).grow (OMono.decHL _ _) hg3
  simp only [decIS, decAt, w0, w1, Option.bind_eq_bind, Option.bind_some]
  exact hdB

include hq henv hLC hLT in
/-- **`check_block_idx_sorts` refines `checkBlockIdxSorts`**, both outcomes (the members' errors are
`check_struct_field_sorts_i`'s or of class `0`). -/
theorem iisr_ref (hP : IdxProg p) (pp : Word) (bs : BlockShape) {bsP : ConLeche.BlockShape}
    (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ {m : Mem} {a : AState} {mo ml co cl : Word} {mss : List MemberShape} {cvs : List IConstantVal}
      {cvsP : List ConLeche.ConstantVal},
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decBS m pp.toNat) m bs → ShapeSrc m pp →
    PSlR decMS mss mo ml m → PSlR decCVp cvs co cl m →
    ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    cvs.mapM (Frontend.denoteCV a.store) = some cvsP → (∀ cv ∈ cvsP, ConLeche.Expr.WScoped 0 cv.type) →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    RefE (VerdictCtx p) (iisrE p n m vis pp mo ml co cl)
      (ConRon.Arena.checkBlockIdxSorts V fe bs mss cvs) a
      (fun v xs a' => IisrPost dn vis fe env m a v.1 v.2 xs a') := by
  induction n with
  | zero => intros; rw [iisrE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a mo ml co cl mss cvs cvsP hC hA hqd hsrc hmss hcvs hbsP hcvsP hws hfe
  by_cases hml : ml = 0
  · rw [iisrE.arm1 p n m vis pp mo ml co cl hml]
    have : mss = [] := by
      have h := hmss.1; simp only [DecB, hml] at h
      simpa [decPL] using h.symm
    subst this
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, PSlR.nil decIS m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  by_cases hcl : cl = 0
  · rw [iisrE.arm2 p n m vis pp mo ml co cl hml hcl]
    have : cvs = [] := by
      have h := hcvs.1; simp only [DecB, hcl] at h
      simpa [decPL] using h.symm
    subst this
    have : ConRon.Arena.checkBlockIdxSorts V fe bs mss [] = pure [] := by
      cases mss <;> simp [ConRon.Arena.checkBlockIdxSorts]
    rw [this]
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, PSlR.nil decIS m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  obtain ⟨q, msh, rest, rfl, hw, hqb, hdm, hrest⟩ := partsPSl_cons hmss hml
  obtain ⟨c, cvv, cvs', rfl, hwc, hcb, hdc, hcvs'⟩ := partsPSl_cons hcvs hcl
  obtain ⟨cvP, cvsP', rfl, hcvP, hcvsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcvsP
  rw [iisrE.arm3 p n m vis pp mo ml co cl hml hcl, hw, hwc, installIdx_cons]
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  have h1 := iis_ref hq henv hLC hLT hP n (by omega) hC hA hqd hsrc (by rw [hq']; exact hdm)
    (by rw [hc']; exact hdc) hbsP hcvP (hws _ List.mem_cons_self) hfe (pp := pp)
    (ms := UInt64.ofNat q) (cv := UInt64.ofNat c)
  rcases h1e : iisE p n m vis pp (UInt64.ofNat q) (UInt64.ofNat c) with e1 | ⟨w1, m1⟩
  · rw [iisrE.k_check_block_idx_sorts_one.eq_1]
    rw [h1e] at h1
    exact RefE.bind_left h1
  rw [h1e] at h1
  obtain ⟨is, a1, hrun1, hR1⟩ := h1
  rw [iisrE.k_check_block_idx_sorts_one.arm1]
  refine RefE.bind_right hrun1 ?_
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hqd hsrc
  have c1 := hR1.core
  have h2 := ih (by omega) (m := m1) (a := a1) (mo := mo + 1) (ml := ml - 1) (co := co + 1)
    (cl := cl - 1) (mss := rest) (cvs := cvs') (cvsP := cvsP') hR1.stage hR1.abs
    (hqd.grow (decBS_mono _) hR1.grow) (partsHsrc_grow hR1.grow hq9 hsrc) (hrest.grow decMS_mono hR1.grow)
    (hcvs'.grow (fun q => OMono.decCVp q) hR1.grow) (ConRon.Bridge.Inductives.dShape_ext c1.ext _ _ hbsP)
    (ConRon.Bridge.Inductives.dExt_denoteCV.list c1.ext _ _ hcvsP')
    (fun cv h => hws cv (List.mem_cons_of_mem _ h)) (ConRon.Bridge.denoteFEnv_mono c1.ext hfe)
  rcases h2e : iisrE p n m1 vis pp (mo + 1) (ml - 1) (co + 1) (cl - 1) with e2 | ⟨r2, m2⟩
  · rw [iisrE.k_check_block_idx_sorts.none]
    rw [h2e] at h2
    exact RefE.bind_left h2
  rw [h2e] at h2
  obtain ⟨rs, a2, hrun2, hR2⟩ := h2
  rw [iisrE.k_check_block_idx_sorts.eq_2]
  refine RefE.bind_right hrun2 ?_
  rcases h3 : consW n m2 w1 (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩
  · rw [liftE_none, iisrE.k_sl_cons.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, iisrE.k_sl_cons.arm1]
  obtain ⟨hS3, hg3, hd3, htop3⟩ := partsConsPL decIS_mono h3 hR2.stage.stage hR2.sorts.2 hR2.sorts.1
    (hR1.sorts.grow (decIS_mono _) hR2.grow)
  have hA3 : AbsOK m3 := consW_afr h3 hR2.abs
  exact RefE.ret rfl ⟨hR2.stage.of_pstep hS3 hA3 (PStep.refl hR2.stage.check.state),
    (hR1.grow.trans hR2.grow).trans hg3, ⟨by simpa using hd3, by simpa using Nat.le_of_eq htop3⟩, hA3,
    c1.trans hR2.core⟩

include hq henv hOpf hLC hLT in
/-- **`check_block_idx_sorts` refines `checkBlockIdxSorts`** under `StageC` (the knot's core
calls; the denotations as con-ron's `checkBlockIdxSorts_specF` asks): every member's index sorts a
slice of `[off, len]` pointers below the tops. -/
@[refines ConRon.Arena.checkBlockIdxSorts]
theorem checkBlockIdxSorts_refinesC (hP : IdxProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (pp mo ml co cl : Word)
    (bs : BlockShape) (mss : List MemberShape) (cvs : List IConstantVal)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hqd : DecB (fun m => decBS m pp.toNat) s₀.mem bs)
    (hsrc : ShapeSrc s₀.mem pp) (hmss : PSlR decMS mss mo ml s₀.mem) (hcvs : PSlR decCVp cvs co cl s₀.mem)
    {bsP : ConLeche.BlockShape} {cvsP : List ConLeche.ConstantVal}
    (hbsP : ConRon.Bridge.Inductives.dShape a₀.store bs = some bsP)
    (hcvsP : cvs.mapM (Frontend.denoteCV a₀.store) = some cvsP)
    (hws : ∀ cv ∈ cvsP, ConLeche.Expr.WScoped 0 cv.type)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_idx_sorts" [vis, pp, mo, ml, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockIdxSorts V fe bs mss cvs) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.checkBlockIdxSorts V fe bs mss cvs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      PSlR decIS (AM.res (ConRon.Arena.checkBlockIdxSorts V fe bs mss cvs) a₀) (r.headD 0)
        (r.tail.headD 0) s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (iisrE_spec p hP hOpf n s₀ vis pp mo ml co cl)
    (iisr_ref hq henv hLC hLT hP pp bs n hn hC hA hqd hsrc hmss hcvs hbsP hcvsP hws hfe)) ?_
  rintro _r s' ⟨hl, _, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.sorts, hR.abs⟩

end sims

end L.Ind

end
