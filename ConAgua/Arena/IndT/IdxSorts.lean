module

import ConRon.Bridge.Inductives.SumInstall
import ConAgua.Arena.IndT.Sum3
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndT.Install1
import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.IndInstallSpec.GrcProg
public import ConAgua.Arena.KnotEntry
public import ConAgua.Verdict.VCtx
public import ConRon.Bridge.Checker.Hyp
import all ConAgua.Arena.IndInstall
import ConAgua.L.WordOff

@[expose] public section

/-!
# `check_block_idx_sorts`: one model and one refinement for both outcomes

`iisE` (`check_block_idx_sorts_one`) and `iisrE` (`check_block_idx_sorts`), `l_model … unified`:
`open_pis_at_fvars_f`, `rec2` and `sl_cons` (outside the verdict closure) through their `Option`
models, `check_struct_field_sorts_i` through its run (`callE`; `RefE.bindRun` with its spec and
`fsorts_ref`), the member check
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

/-- **`check_block_idx_sorts`' unified model**: `open_pis_at_fvars_f` through its `Option` model,
`check_struct_field_sorts_i` through its run (`callE`), the recursion. -/
l_model iisE_spec (p : Prog) (hP : IdxProg p) (hOpf : OpfF p)
  fns [hP.idx ↦ iisE]
  specs [opfF_spec p hOpf n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem iisE_k_opf_eq (p : Prog) (n : Nat) (vis pp msO msL nP ni srt : Word) (r : List Word) (m₁ : Mem)
    (h : r.headD 0 ≠ 0) :
    iisE.k_open_pis_at_fvars_f p n vis pp msO msL nP ni srt (.ok (r, m₁)) =
      iisE.j1 p n vis pp msO msL nP ni srt (idxTail nP (r.tail.headD 0) (r.tail.tail.headD 0)).1
        (idxTail nP (r.tail.headD 0) (r.tail.tail.headD 0)).2 m₁ := by
  unfold idxTail
  by_cases hl : nP < r.tail.tail.headD 0
  · rw [iisE.k_open_pis_at_fvars_f.arm1 _ _ _ _ _ _ _ _ _ _ _ h hl, ite_eq_left hl]
  · rw [iisE.k_open_pis_at_fvars_f.arm2 _ _ _ _ _ _ _ _ _ _ _ h hl, ite_eq_right hl]

/-- What `check_block_idx_sorts` gives besides the twin's run (from `m`, `a`): the stage relation,
growth, the abstraction memos, the twin's core step. -/
structure IisPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep env fe a a'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)

include hq henv hLC hLT in
/-- **`check_block_idx_sorts` refines `checkBlockIdxSorts`, both outcomes** (twin side con-ron's
`checkBlockIdxSorts_specF`'s proof): per member the telescope opened (`open_pis_at_fvars_f`, an
abort of class `0` where the twin's `unwrapOr` fails), the index binders' sorts
(`check_struct_field_sorts_i` through its run, `fsorts_ref`), the rest by induction. -/
theorem iis_ref (hP : IdxProg p) (pp : Word) (bs : BlockShape) {bsP : ConLeche.BlockShape}
    (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ {m : Mem} {a : AState} {msO msL : Word} {mss : List MemberShape} {mssP : List ConLeche.MemberShape},
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decBS m pp.toNat) m bs → ShapeSrc m pp →
    PSlR decMS mss msO msL m → ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    mss.mapM (ConRon.Bridge.Inductives.dMember a.store) = some mssP →
    (∀ ms ∈ mssP, ConLeche.Expr.WScoped 0 ms.cvT.type) →
    RefE (VerdictCtx p) (iisE p n m vis pp msO msL) (ConRon.Arena.checkBlockIdxSorts V fe bs mss) a
      (fun v _ a' => IisPost dn vis fe env m a v.2 a') := by
  induction n with
  | zero => intros; rw [iisE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a msO msL mss mssP hC hA hqd hsrc hmss hbsP hmssP hws
  by_cases hml : msL = 0
  · rw [iisE.arm1 p n m vis pp msO msL hml]
    have : mss = [] := by
      have h := hmss.1; simp only [DecB, hml] at h
      simpa [decPL] using h.symm
    subst this
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  have hS := hC.stage
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hqd hsrc
  obtain ⟨hnpw, hnpb, hrs32, hrse⟩ := partsShapeWords (IWGrow.refl m) hqd hq9
  obtain ⟨q, msh, rest, rfl, hw, hqb, hdm, hrest⟩ := partsPSl_cons hmss hml
  obtain ⟨msP, mssP', rfl, hmP, hmssP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmssP
  have hmsT : decMS (truncM m) q = some msh := hdm
  obtain ⟨⟨a0, hcvi, hcvd⟩, -, hni, -⟩ := decMS_some hmsT
  have hnilt := partsIwLt hni
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  obtain ⟨hw0, ha0b, -⟩ := partsIwRd hcvi (w := UInt64.ofNat q) hq'
  obtain ⟨hw1, hnib, -⟩ := partsIwRd hni (w := UInt64.ofNat q + 1) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨htyl, htye⟩ := partsCVType hcvd (w := UInt64.ofNat a0) (UInt64.toNat_ofNat_of_lt' ha0b)
  obtain ⟨hcvP, -⟩ := ConRon.Bridge.Inductives.dMember_inv hmP
  have hwT := hws msP List.mem_cons_self
  obtain ⟨-, -, -, -, hsP, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hbsP
  by_cases hov : rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (rdW (m.arr64 IW) msO + 1) <
      rdW (m.arr64 IW) (pp + 4)
  · rw [iisE.abort1 p n m vis pp msO msL hml hov]; exact RefE.of_cls0 rfl
  rw [iisE.arm2 p n m vis pp msO msL hml hov]
  rw [hw, hnpw, hw1, hw0]
  rw [hw, hnpw, hw1] at hov
  have hk : (UInt64.ofNat bs.nP + UInt64.ofNat msh.nIdx : Word).toNat = bs.nP + msh.nIdx := by
    rw [L.toNat_add_of_not_lt hov, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib]
  rw [installIdx_cons]
  unfold idxOneAM
  simp only [bind_assoc]
  -- `open_pis_at_fvars_f`
  rw [show rdW (m.arr64 (tierA EREC ((UInt64.ofNat a0 + 3) >>> 40))) ((UInt64.ofNat a0 + 3) &&& 1099511627775) =
    erRd m (UInt64.ofNat a0 + 3) from rfl]
  rcases h1 : opfF m [UInt64.ofNat bs.nP + UInt64.ofNat msh.nIdx, erRd m (UInt64.ofNat a0 + 3), 0]
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
    rw [iisE.k_open_pis_at_fvars_f.abort1 _ _ _ _ _ _ _ _ _ _ _ h0]; exact RefE.of_cls0 rfl
  | some fb =>
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨xsP, xP, htq, hxs, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho1
  obtain ⟨h1', hfv, -⟩ := hd1
  obtain ⟨hfd, hfb⟩ := hfv
  have g1 : r1.getD 1 0 = r1.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r1.getD (1 + 1) 0 = r1.tail.tail.headD 0 := by
    rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  rw [iisE_k_opf_eq _ _ _ _ _ _ _ _ _ _ _ (by rw [h1']; decide), iisE.j1.arm1]
  show RefE _ _ (checkStructFieldSortsI V fe true false bs.resSort bs.nP (fvs.drop bs.nP) [] msh.nIdx >>=
    fun _ => ConRon.Arena.checkBlockIdxSorts V fe bs rest) a1 _
  obtain ⟨hdT, hbT⟩ := installIdxTail (k := UInt64.ofNat bs.nP) hfd hfb
  rw [UInt64.toNat_ofNat_of_lt' hnpb] at hdT
  have hxPos : ∀ (i : Nat), i < (UInt64.ofNat msh.nIdx : Word).toNat → ∀ (x : ConLeche.Expr),
      (xsP.drop bs.nP)[i]? = some x →
      ConLeche.Expr.WScoped ((UInt64.ofNat bs.nP : Word).toNat + i) x.fvarTypeD := by
    intro i _ x hx
    rw [List.getElem?_drop] at hx
    have := ConRon.Bridge.Inductives.openers_typeD_WScoped htq hwT (bs.nP + i) x hx
    rw [UInt64.toNat_ofNat_of_lt' hnpb]
    simpa using this
  have hxsd := ConRon.Bridge.Inductives.denoteEList_drop hxs bs.nP
  have hsP1 := ConRon.Bridge.denoteL_ext hsP p1.ext
  -- `check_struct_field_sorts_i` (through its run)
  have hR2 := fsorts_ref hq henv hLC hLT hP.sum.hg hP.sum.hpw hP.sum.het hP.sum.hcn n (by omega) m1 a1 1 0
    (rdW (m.arr64 IW) (pp + 6)) (UInt64.ofNat bs.nP) _ _ 0 0 (UInt64.ofNat msh.nIdx) m1 (fvs.drop bs.nP) []
    _ hC1 hA1 (IWGrow.refl m1) hdT hbT (by simp [decHL, hslice?]) (by simp) hrs32 ⟨_, by rw [hrse]; exact hsP1⟩
    (by rw [← L.toNat_add_of_not_lt hov]; exact UInt64.toNat_lt _) hxsd hxPos
  rw [hrse, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib,
    show ((1 : Word) != 0) = true from rfl, show ((0 : Word) != 0) = false from rfl] at hR2
  refine RefE.bindRun (s₀ := ⟨m1, Locals.init []⟩) (fun _ => iisE.k_check_struct_field_sorts_i.none ..)
    (fsortsE_spec p hP.sum.hcfs hP.sum.ad.ftd hP.sum.hfsb n _ vis 1 0 _ _ _ _ 0 0 _)
    (fun hG => hG.nv) id hR2 fun r2 s2 u a2 _ _ hr2 ⟨hC2, hg2, hA2⟩ => ?_
  rw [iisE.k_check_struct_field_sorts_i.arm1]
  generalize s2.mem = m2 at hC2 hg2 hA2 ⊢
  obtain ⟨c2, -⟩ := ConRon.Bridge.Inductives.checkStructFieldSortsI_spec fe
    ConRon.Bridge.CoreSpec.of_core henv true false bs.resSort bsP.resSort bs.nP (fvs.drop bs.nP) []
    (xsP.drop bs.nP) [] msh.nIdx (fun i hi x hx => by
      have := hxPos i (by rw [UInt64.toNat_ofNat_of_lt' hnib]; exact hi) x hx
      rwa [UInt64.toNat_ofNat_of_lt' hnpb] at this) a1 a2 u hC1.check
    ⟨hsP1, hxsd, rfl⟩ hr2
  have c12 := (p1.toCore hC.check).trans c2
  have hg02 := hg1.trans hg2
  -- the rest
  have ih' := ih (by omega) (m := m2) (a := a2) (msO := msO + 1) (msL := msL - 1) (mss := rest)
    (mssP := mssP') hC2 hA2 (hqd.grow (decBS_mono _) hg02) (partsHsrc_grow hg02 hq9 hsrc)
    (hrest.grow decMS_mono hg02) (ConRon.Bridge.Inductives.dShape_ext c12.ext _ _ hbsP)
    (ConRon.Bridge.Inductives.dMember_ext.list c12.ext _ _ hmssP')
    (fun ms h => hws ms (List.mem_cons_of_mem _ h))
  exact RefE.lastE (K := iisE.k_check_block_idx_sorts p) (f := fun v => (0, v.2)) (fun _ => rfl)
    (fun _ => rfl) id ih' fun v _ a3 _ hR3 => ⟨hR3.stage, hg02.trans hR3.grow, hR3.abs, c12.trans hR3.core⟩

include hq henv hLC hLT in
/-- **`check_block_idx_sorts` refines `checkBlockIdxSorts`** under `StageC` (`iis_ref`'s ok half; the
denotations as con-ron's `checkBlockIdxSorts_specF` asks). -/
@[refines ConRon.Arena.checkBlockIdxSorts]
theorem checkBlockIdxSorts_refinesC (hP : IdxProg p) (hOpf : OpfF p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (pp msO msL : Word) (bs : BlockShape) (mss : List MemberShape)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hqd : DecB (fun m => decBS m pp.toNat) s₀.mem bs) (hsrc : ShapeSrc s₀.mem pp)
    (hmss : PSlR decMS mss msO msL s₀.mem) {bsP : ConLeche.BlockShape} {mssP : List ConLeche.MemberShape}
    (hbsP : ConRon.Bridge.Inductives.dShape a₀.store bs = some bsP)
    (hmssP : mss.mapM (ConRon.Bridge.Inductives.dMember a₀.store) = some mssP)
    (hws : ∀ ms ∈ mssP, ConLeche.Expr.WScoped 0 ms.cvT.type) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_idx_sorts" [vis, pp, msO, msL]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockIdxSorts V fe bs mss) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.checkBlockIdxSorts V fe bs mss) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (iisE_spec p hP hOpf n s₀ vis pp msO msL)
    (iis_ref hq henv hLC hLT hP pp bs n hn hC hA hqd hsrc hmss hbsP hmssP hws)) ?_
  rintro _r s' ⟨hl, _, a', run, hR⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, hR.abs⟩

end sims

end L.Ind

end
