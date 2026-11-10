module

public import ConAgua.Arena.IndT.BlockRM2
public import ConAgua.Arena.IndT.BlockCS
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndT.BlockNames
import all ConAgua.Arena.IndInstall
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.IndPartsSpec.RulePrefixAt

@[expose] public section

/-!
# `reduce_members`' contract (lane `ronsync2`, stage 3)

`reduce_members(vis, nP, ms.off, ms.len)` (`IndInstall.lean`) refines `reduceMembers .verified`,
both outcomes (`rms_ref`, induction on the fuel; twin side as con-ron's `reduceMembers_spec`): a
flush (`flushRefS_of`), the member (`rm_ref`, its memos by `IndMemoClosed`: `reduce_member` is in
`imFns`), the rest, and the `sl_cons` (outside the verdict closure) lifted. `rmRefS_of`: `IndT/BlockC`'s
`RmRefS` from it.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups `reduce_members`' model and refinement read. -/
structure RmsProg (p : Prog) : Prop extends RmProg p where
  fl : FlushProg p
  rms : p.lookup "reduce_members" = some reduceMembers

set_option experimental.vcgen true in
/-- **`reduce_members`' unified model**: `flush_caches` and `reduce_member` through their calls,
the `sl_cons` (outside the verdict closure) lifted. -/
l_model rmsE_spec (p : Prog) (hP : RmsProg p)
  fns [hP.rms ↦ rmsE]
  specs [callW_spec p n "sl_cons"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section rms
variable {p : Prog} (hV : CcvProg p) (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p)
  (hcrf : CrfF p) (hP : RmsProg p) (hWt : WhnfTopE p) (hl : IndLeaves p)
  {dn : NIdx → Option ConLeche.Name} (hCS : CcvSims p dn) {vis : Word} {fe : IFEnv}
  {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hV hq hap hkp hcrf hP hWt hl hCS henv in
/-- **`reduce_members` refines `reduceMembers`, both outcomes** under `BkSt` (induction on the
fuel; twin side as con-ron's `reduceMembers_spec`): the reduced members a slice below the top. -/
theorem rms_ref (nP : Word) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (o l : Word) (mss : List MemberShape)
      (mssP : List ConLeche.MemberShape),
    BkSt dn vis fe env m a → PSlR decMSB mss o l m →
    mss.mapM (ConRon.Bridge.Inductives.dMember a.store) = some mssP →
    RefE (VerdictCtxU p) (rmsE p n m vis nP o l) (ConRon.Arena.reduceMembers V fe nP.toNat mss) a
      (fun v ms a' => BkGo dn vis fe env m a v.2 a' ∧
        PSlR decMSB ms (v.1.headD 0) (v.1.tail.headD 0) v.2) := by
  induction n with
  | zero => intros; rw [rmsE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a o l mss mssP hB hms hmssP
  by_cases hl0 : l = 0
  · rw [rmsE.arm1 p n m vis nP o l hl0]
    have : mss = [] := by
      have h := hms.dec; simp only [DecB, hl0] at h
      simpa [decPL] using h.symm
    subst this
    exact RefE.ret rfl ⟨⟨hB, IWGrow.refl m, ⟨hB.c.check.state, ConRon.Arena.Ext.refl _, rfl⟩⟩,
      PSlR.nil decMSB m⟩
  obtain ⟨q, x, rest, rfl, hw, hqb, hdx, hrest⟩ := partsPSl_cons hms hl0
  obtain ⟨xP, restP, rfl, hxP, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmssP
  rw [rmsE.arm2 p n m vis nP o l hl0]
  unfold ConRon.Arena.reduceMembers
  -- `flush_caches`
  refine RefE.bindE (fun _ => rmsE.k_flush_caches.none ..) id
    (flushRefS_of (G := VerdictCtxU p) hP.fl (fun hG => hG.nv) n vis fe env m a hB)
    fun ⟨r1, m1⟩ _ a1 _ h1 => ?_
  rw [rmsE.k_flush_caches.arm1]
  have hw1 : rdW (m1.arr64 IW) o = UInt64.ofNat q := by
    have hb := hms.bound
    have : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    rw [rdW_iw_grow h1.grow (by omega), hw]
  rw [hw1]
  -- `reduce_member`
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hdx1 : DecB (fun m => decMSB m (UInt64.ofNat q : Word).toNat) m1 x := by
    rw [hq']; exact hdx.grow (decMSB_mono _) h1.grow
  have hxb : (UInt64.ofNat q : Word).toNat + 5 ≤ iwTop m1 := by
    obtain ⟨-, ⟨a4, ha4, -⟩, -, -⟩ := decMS_some (m := truncM m) (decMSB_decMS hdx)
    have h4 := (rec2IwN_trunc ha4).1
    have hg := h1.grow.iw
    simp only at hg
    rw [hq']; omega
  refine RefE.bindRun (s₀ := ⟨m1, Locals.init []⟩) (fun _ => rmsE.k_reduce_member.none ..)
    (rmE_spec p hP.toRmProg n _ vis _ nP) (fun hG => hG.nv) id
    (rm_ref hV hq hap hkp hcrf hP.toRmProg hWt hCS henv n (by omega) h1.st.c h1.st.abs hdx1 hxb
      (ConRon.Bridge.Inductives.dMember_ext h1.inst.ext _ _ hxP))
    fun r2 s2 x' a2 hc2 _ hr2 hR2 => ?_
  rw [rmsE.k_reduce_member.arm1]
  have hI2 : IndMemos s2.mem :=
    callW_indMemos hkp.closed hl (im_mem _ rfl) (callW_of_callE hc2) h1.st.ind
  have hB2 : BkSt dn vis fe env s2.mem a2 := ⟨hR2.stage, hI2, hR2.abs⟩
  have hg2 : IWGrow m s2.mem := h1.grow.trans hR2.grow
  have hi2 : ConRon.Bridge.Inductives.InstStep a a2 := h1.inst.trans hR2.core.toInst
  -- the rest
  refine RefE.bindE (fun _ => rmsE.k_reduce_members.none ..) id
    (ih (by omega) s2.mem a2 (o + 1) (l - 1) rest restP hB2 (hrest.grow decMSB_mono hg2)
      (ConRon.Bridge.Inductives.dMember_ext.list hi2.ext _ _ hrestP))
    fun ⟨r3, m3⟩ xs a3 _ ⟨h3, hsl3⟩ => ?_
  rw [rmsE.k_reduce_members.arm1]
  -- `sl_cons` (L only)
  refine RefE.onlySim (fun _ => rmsE.k_sl_cons.none ..) (fun _ _ h => h) fun r4 m4 h4 => ?_
  rw [rmsE.k_sl_cons.arm1]
  obtain ⟨s4, rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (slCons_specW p hP.alloc hP.copy hP.cons n _ _ _ _) h4
  obtain ⟨hS4, hg4, hd4, htop4⟩ := partsConsPL decMSB_mono hW h3.st.c.stage hsl3.bound hsl3.dec
    (hR2.dec.grow (decMSB_mono _) h3.grow)
  have hM4 := h3.st.mem.ofIW (consW_iwFrame hW)
  exact RefE.ret rfl ⟨⟨⟨h3.st.c.of_pstep hS4 hM4.abs
      (ConRon.Bridge.Inductives.PStep.refl h3.st.c.check.state), hM4.ind, hM4.abs⟩,
    (hg2.trans h3.grow).trans hg4, hi2.trans h3.inst⟩, ⟨hd4, Nat.le_of_eq htop4⟩⟩

end rms

/-- **`reduce_members`' contract** (`rms_ref` through its call). -/
theorem rmRefS_of {p : Prog} (hV : CcvProg p) (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hcrf : CrfF p) (hP : RmsProg p) (hWt : WhnfTopE p) (hl : IndLeaves p)
    {dn : NIdx → Option ConLeche.Name} (hCS : CcvSims p dn) : RmRefS (VerdictCtxU p) p dn := by
  intro n hn vis fe env m a nP mo ml mss msP hB henv hd hb hmss
  have h := RefE.ofCallE (s₀ := ⟨m, Locals.init []⟩) (rmsE_spec p hP n _ vis nP mo ml) (fun hG => hG.nv)
    (rms_ref hV hq hap hkp hcrf hP hWt hl hCS henv nP n hn m a mo ml mss msP hB ⟨hd, hb⟩ hmss)
  exact RefE.weakenP h fun ⟨r, m'⟩ y a' h => by
    obtain ⟨s', hs', -, hR⟩ := h
    simp only at hs'
    subst hs'
    exact ⟨hR.1, hR.2.dec, hR.2.bound⟩

end L.Ind

end
