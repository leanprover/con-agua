module

import ConRon.Bridge.Inductives.BlockShape
import ConRon.Bridge.Inductives.Run
import ConLeche.Verify.Cached.BlockRunC
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl
import ConAgua.Arena.IndInstallSpec.NestCtx
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.PartsAt
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.IndInstallSpec.InstallIwB
public import ConRon.Bridge.Inductives.Rel
import all ConAgua.Arena.IndInstall
public import ConAgua.Arena.IndInstallSpec.CapsProg
public import ConAgua.Arena.TwinStep
public import ConAgua.Arena.IndPartsSpec.PartsConsPL
public import ConAgua.Arena.IndPartsSpec.MemberNames

@[expose] public section

/-!
# `checkBlockCtors` under `StageC` (lane `indstaget`)

The constructors of every member, from `StageC` and con-ron's preconditions of
`checkBlockCtors_specF` (the shape, the members and the formers denote, every stored former
closed, the environment denotes and its index spec holds — one environment, `vis0 = vis`, as
`check_block_pass` calls it), the twin side transcribed from that spec's proof: one member's
`checkSumCtors` (`scts_ref` through its run, its post's `CoreStep`), the records and conses (L only), the shape's level parameters (L only).

`check_block_ctors_one` and `check_block_ctors_go` have one model each for both outcomes
(`icboE`, `icbgE`: `l_model … unified`) and one refinement each (`icbo_ref`, `icbg_ref`: `RefE`
under `VerdictCtxU`, what `check_sum_ctors`' refinement `scts_ref` assumes), walked by the rules
of `RefWalk.lean`.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_block_ctors`' unified model**: `block_shape_lps` (outside the verdict closure) lifted,
`check_sum_ctors` and the rest through their calls. -/
l_model ictE_spec (p : Prog) (hP : CtorsProg p)
  fns [hP.ctors ↦ ictE]
  specs [blockShapeLps_spec p hP.alloc hP.erCopy hP.erToIw hP.lps n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`check_sum_ctors(vis, vis, T, lps.off, lps.len, nP, nIdx, rs, isProp, large, cvTa, c.off,
c.len)`'s contract** (at one environment, `vis0 = vis`, as `check_block_ctors` calls it):
`checkSumCtors`, both outcomes, from `StageC` and con-ron's `checkSumCtors_specF` preconditions; the
stage after, the pools grown, `AbsOK`, the core step. (Its proof is the verdict area's `scts_ref`
at the new L.) -/
def SctsRefS (G : Prop) (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (vis : Word) (fe : IFEnv) (env env₀ : ConLeche.Env) (m : Mem)
    (a : AState) (T lo ll nP nIdx rs isP lg cvq cO cL : Word) (lps : List NIdx) (cvTa : IConstantVal)
    (cs : List (IConstantVal × Nat)) (TP : ConLeche.Name) (lpsP : List ConLeche.Name)
    (rsP : ConLeche.Level) (cvTaP : ConLeche.ConstantVal) (csP : List (ConLeche.ConstantVal × Nat)),
    StageC dn vis fe env m a → ConLeche.EnvWF env → AbsOK m → H T → H rs →
    decHL m lo.toNat ll.toNat = some lps → lo.toNat + ll.toNat ≤ iwTop m →
    DecB (fun m => decCVp m cvq.toNat) m cvTa →
    DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) m cs →
    denoteN a.store.ns (decI T) = some TP → Frontend.denoteNList a.store.ns lps = some lpsP →
    denoteL a.store.ls (decI rs) = some rsP → Frontend.denoteCV a.store cvTa = some cvTaP →
    cvTaP.type.hasFvar = false → ConRon.Bridge.Inductives.denoteCtors a.store cs = some csP →
    ConRon.Bridge.Inductives.IFEnvOKS env₀ fe a.store →
    RefE G (callE p n "check_sum_ctors" [vis, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvq, cO, cL] m)
      (checkSumCtors V fe fe (decI T) lps nP.toNat nIdx.toNat (decI rs) (isP != 0) (lg != 0) cvTa cs) a
      (fun rm _ a' => StageC dn vis fe env rm.2 a' ∧ IWGrow m rm.2 ∧ AbsOK rm.2 ∧
        ConRon.Bridge.CoreStep env fe a a')

/-- What `check_block_ctors` gives (from `m`, `a`): the stage invariant, the growth, `AbsOK`, the
core step. -/
structure BlkCtorsPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep env fe a a'

section sims
variable {p : Prog} {G : Prop} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {env env₀ : ConLeche.Env}

/-- **`check_block_ctors` refines `checkBlockCtors`, both outcomes** under `StageC` (at one
environment, `vis0 = vis`, as `check_block_pass` calls it; twin side: con-ron's
`checkBlockCtors_specF`'s proof; induction on the fuel): each member's `check_sum_ctors` by its
contract (`SctsRefS`), the shape's level parameters (outside the verdict closure) lifted. -/
theorem ict_ref (_hP : CtorsProg p) (hR : SctsRefS G p dn) (henv : ConLeche.EnvWF env) (pp : Word) (bs : BlockShape)
    {bsP : ConLeche.BlockShape} (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (mo ml : Word) (mss : List MemberShape)
      (mssP : List ConLeche.MemberShape),
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decBS m pp.toNat) m bs → ShapeSrc m pp →
    PSlR decMS mss mo ml m →
    ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    mss.mapM (ConRon.Bridge.Inductives.dMember a.store) = some mssP →
    (∀ ms ∈ mssP, ConLeche.Expr.WScoped 0 ms.cvT.type) →
    ConRon.Bridge.Inductives.IFEnvOKS env₀ fe a.store →
    RefE G (ictE p n m vis vis pp mo ml) (ConRon.Arena.checkBlockCtors V fe fe bs mss) a
      (fun v _ a' => BlkCtorsPost dn vis fe env m a v.2 a') := by
  induction n with
  | zero => intros; rw [ictE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a mo ml mss mssP hC hA hqd hsrc hmss hbsP hmssP hws hok₀
  by_cases hl0 : ml = 0
  · rw [ictE.arm1 p n m vis vis pp mo ml hl0]
    have : mss = [] := by
      have h := hmss.dec; simp only [DecB, hl0] at h
      simpa [decPL] using h.symm
    subst this
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  obtain ⟨q, msh, rest, rfl, hw, hqb, hdx, hrest⟩ := partsPSl_cons hmss hl0
  obtain ⟨msP, restP, rfl, hxP, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmssP
  rw [ictE.arm2 p n m vis vis pp mo ml hl0, hw]
  unfold ConRon.Arena.checkBlockCtors
  -- `block_shape_lps` (L only)
  refine RefE.onlySim (fun _ => ictE.k_block_shape_lps.none ..) (fun _ _ h => h) fun r1 m1 h1 => ?_
  rw [ictE.k_block_shape_lps.arm1]
  obtain ⟨hS1, hg1, hd1, hb1⟩ := lpsW_ok' h1 hC.stage hqd
  have hA1 : AbsOK m1 := lpsW_afr h1 hA
  have hC1 : StageC dn vis fe env m1 a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  -- the member's words
  have hT : iwTop m1 < 2 ^ 64 := (rdW (m1.arr64 CTL) 200).toNat_lt
  have hsz := hS1.iw.iwSize
  have hqd1 := hqd.grow (decBS_mono _) hg1
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hqd hsrc
  have hq91 : pp.toNat + 9 ≤ iwTop m1 := by have := hg1.iw; omega
  obtain ⟨hnpw, hnpb, hrs32, hrse⟩ := partsShapeWords hg1 hqd hq9
  have hqt : decBS (truncM m1) pp.toNat = some bs := hqd1
  obtain ⟨-, -, -, -, -, hlg, hpr⟩ := decBS_some hqt
  have h8 := installIwB (w := pp) (k := 8) hpr hsz
  have h7 := installIwB (w := pp) (k := 7) hlg hsz
  rw [show (UInt64.ofNat 8 : Word) = 8 from rfl] at h8
  rw [show (UInt64.ofNat 7 : Word) = 7 from rfl] at h7
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hms1 : DecB (fun m => decMS m (UInt64.ofNat q : Word).toNat) m1 msh := by
    rw [hq']; exact hdx.grow (decMS_mono _) hg1
  have hmsT : decMS (truncM m1) (UInt64.ofNat q : Word).toNat = some msh := hms1
  obtain ⟨⟨cvp, hcvp, hcvT⟩, -, hni, hct⟩ := decMS_some hmsT
  obtain ⟨co, cl, hco, hcl, hcd, hcb⟩ := partsAt decCN_mono hct
  have l3 := partsIwLt hcl
  obtain ⟨hw0, hcvb, -⟩ := partsIwRd hcvp (w := UInt64.ofNat q) rfl
  obtain ⟨hw1, hnib, -⟩ := partsIwRd hni (w := UInt64.ofNat q + 1) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨hw2, -, -⟩ := partsIwRd hco (w := UInt64.ofNat q + 2) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨hw3, -, -⟩ := partsIwRd hcl (w := UInt64.ofNat q + 3) (by rw [UInt64.toNat_add]; simp; omega)
  rw [UInt64.ofNat_toNat] at hw2 hw3
  have hcvm : decCVp m1 (UInt64.ofNat cvp : Word).toNat = some msh.cvT := by
    rw [UInt64.toNat_ofNat_of_lt' hcvb]; exact DecB.get (OMono.decCVp _) hcvT
  have hcvB : DecB (fun m => decCVp m (UInt64.ofNat cvp : Word).toNat) m1 msh.cvT := by
    rw [UInt64.toNat_ofNat_of_lt' hcvb]; exact hcvT
  obtain ⟨wx, hwx, hwxl, hname⟩ := decCV_name (a := erecP m1) hcvm
  have ex : rdW (m1.arr64 (tierA EREC ((UInt64.ofNat cvp : Word) >>> 40)))
      ((UInt64.ofNat cvp : Word) &&& 1099511627775) = wx := by
    rw [erRdT_congr rfl rfl]; exact erRdT_of _ _ hwx
  rw [hw0, ex, hw1, hw2, hw3, hnpw]
  -- twin denotations
  obtain ⟨hcvTP, -, hcsP, -⟩ := ConRon.Bridge.Inductives.dMember_inv hxP
  obtain ⟨-, -, -, -, hsP, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hbsP
  have hlpsP := ConRon.Bridge.Inductives.BlockShape.lps_spec hbsP
  have hcsP' : ConRon.Bridge.Inductives.denoteCtors a.store msh.ctors = some msP.ctors := by
    rw [← ConRon.Bridge.Inductives.dCtors_eq_denoteCtors]; exact hcsP
  have hTP : denoteN a.store.ns (decI wx) = some msP.cvT.name := by
    rw [← hname]; exact ConRon.Bridge.denoteCV_name hcvTP
  have hws0 := hws msP (List.mem_cons_self ..)
  -- `check_sum_ctors`
  have hR1 := hR n (by omega) vis fe env env₀ m1 a wx (r1.headD 0) (r1.tail.headD 0) (UInt64.ofNat bs.nP)
    (UInt64.ofNat msh.nIdx) (rdW (m1.arr64 IW) (pp + 6)) (rdW (m1.arr64 IW) (pp + 8))
    (rdW (m1.arr64 IW) (pp + 7)) (UInt64.ofNat cvp) co cl bs.lps msh.cvT msh.ctors _ _ _ _ _ hC1 henv hA1
    hwxl hrs32 hd1 hb1 hcvB hcd hTP hlpsP (by rw [hrse]; exact hsP) hcvTP
    (ConLeche.Cached.ws0_hasFvar hws0) hcsP' hok₀
  rw [← hname, hrse, h8, h7, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib] at hR1
  refine RefE.bindE (fun _ => ictE.k_check_sum_ctors.none ..) id hR1
    fun ⟨r2, m2⟩ _ a2 _ ⟨hC2, hg2, hA2, hc2⟩ => ?_
  rw [ictE.k_check_sum_ctors.arm1]
  -- the other members
  have hg02 := hg1.trans hg2
  refine RefE.lastE (fun _ => ictE.k_check_block_ctors.none ..) (fun _ => ictE.k_check_block_ctors.arm1 ..) id
    (ih (by omega) m2 a2 (mo + 1) (ml - 1) rest restP hC2 hA2 (hqd.grow (decBS_mono _) hg02)
      (partsHsrc_grow hg02 hq9 hsrc) (hrest.grow decMS_mono hg02)
      (ConRon.Bridge.Inductives.dShape_ext hc2.ext _ _ hbsP)
      (ConRon.Bridge.Inductives.dMember_ext.list hc2.ext _ _ hrestP)
      (fun ms h => hws ms (List.mem_cons_of_mem _ h)) (hok₀.mono hc2.ext))
    fun _ _ _ _ h3 => ⟨h3.stage, hg02.trans h3.grow, h3.abs, hc2.trans h3.core⟩

/-- **`check_block_ctors` refines `checkBlockCtors`** under `StageC` (the ok half of `ict_ref`). -/
@[refines ConRon.Arena.checkBlockCtors]
theorem checkBlockCtors_refinesC (hP : CtorsProg p) (hR : SctsRefS G p dn) (henv : ConLeche.EnvWF env) (n : Nat) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (pp mo ml : Word) (bs : BlockShape) (mss : List MemberShape)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hqd : DecB (fun m => decBS m pp.toNat) s₀.mem bs) (hsrc : ShapeSrc s₀.mem pp)
    (hmss : PSlR decMS mss mo ml s₀.mem) {bsP : ConLeche.BlockShape} {mssP : List ConLeche.MemberShape}
    (hbsP : ConRon.Bridge.Inductives.dShape a₀.store bs = some bsP)
    (hmssP : mss.mapM (ConRon.Bridge.Inductives.dMember a₀.store) = some mssP)
    (hws : ∀ ms ∈ mssP, ConLeche.Expr.WScoped 0 ms.cvT.type)
    (hok₀ : ConRon.Bridge.Inductives.IFEnvOKS env₀ fe a₀.store) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_ctors" [vis, vis, pp, mo, ml]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockCtors V fe fe bs mss) a₀ ∧
      BlkCtorsPost dn vis fe env s₀.mem a₀ s'.mem (AM.st (ConRon.Arena.checkBlockCtors V fe fe bs mss) a₀);
      ⊤⦄ := by
  refine triple_post (RefE.triple (ictE_spec p hP n s₀ vis vis pp mo ml)
    (ict_ref hP hR henv pp bs n hn _ a₀ mo ml mss mssP hC hA hqd hsrc hmss hbsP hmssP hws hok₀)) ?_
  rintro r s' ⟨hl, x, a', run, hR'⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR'⟩

end sims

end L.Ind
