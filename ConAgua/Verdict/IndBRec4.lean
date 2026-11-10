module

public import ConAgua.Verdict.IndBCrg
import ConAgua.Arena.RecGenSpec.Rec3TmdWDecB
import ConAgua.Arena.RecGenSpec.ClassFeR
import ConRon.Bridge.Inductives.GenRec
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RecClassSpec.PdWAfr
import ConAgua.Arena.RecGenSpec.FlushStage
import ConAgua.Arena.RefWalk
import ConAgua.Arena.ScratchRefine
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.KnotEntry
public import ConAgua.Arena.RecClassSpec.Classes
public import ConAgua.Arena.RecGenSpec.CrsProg
public import ConAgua.Arena.IndInstallSpec.BlockRawRec
import ConAgua.Arena.IndRealMemoCr
import all Init.Data.List.Control
import ConAgua.Arena.IndDeclConstsFrame
import ConAgua.Arena.IndInstallSpec.OfClosed
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.IndInstallSpec.TabSimSpg
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import all ConAgua.Arena.RecGen
import ConAgua.L.WordOff

@[expose] public section
/-!
# `class_rule_check`, `class_rule_ok`, `class_rules_ok_one`: one model and one refinement each

`crdW` is the hand-written model of `class_rule_check_domains` (`crdW_ok`: the twin's
`rbs.allM` — resolving at `feR`, naming none of the `pushed` recursors — through `crfF_ok` and
`maConstW_ok`). `crcE` (`l_model … unified`: the guards through `crgE`, the flush, `strip_lams` and
the domains lifted) and `crc_ref` refine `classRuleCheck` under `StageC`, carrying a well-formed
`mentions_any` memo (twin side con-ron's `classRuleCheck_spec`'s proof). Its own aborts are of class
`0` (the twin's `.internal`) but for the domains' site, a call of `unresolved_consts_error`
(`uce_errClaim_hi`, so `G` is `VerdictCtxU`); the guards' errors are `crg_ref`'s, the inference's
the core stub's claim. `class_rule_ok` (`crule_ref`) is the check, then the rule as built;
`class_rules_ok_one` (`cr1_ref`) is its word sum's overflow abort, then `class_rule_ok` in tail
position. The ok half is `classRuleOk_refinesC`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified


/-! ## `class_rule_check_domains`: `rbs.allM` (resolving at `feR`, naming no pushed recursor) -/

/-- **`class_rule_check_domains` is its model `crdW`** (generated). -/
l_model crdW_spec (p : Prog) (hp : p.lookup "class_rule_check_domains" = some classRuleCheckDomains)
    (hcr : CrfF p) (hM : MaProg p)
  fns [hp ↦ crdW list]
  specs [crfF_spec p hcr n,
    mentionsAnyConst_specK p hM.view hM.cont hM.find hM.put hM.go hM.node hM.clr hM.ma n]
  grind [arena_grind, ind_grind] finish [rdW_eq]

/-- **The twin's domain test** of `classRuleCheck`: resolving at `fe`, naming none of `pushed`. -/
def crdT (fe : IFEnv) (pushed : List NIdx) (b : EIdx) : AM Bool := do
  if ← constsResolveFFast fe b then pure !(← ConRon.Arena.mentionsAnyConst pushed b) else pure false

theorem crdT_run_false {fe : IFEnv} {pushed : List NIdx} {e : EIdx} {a a2 : AState}
    (h : (constsResolveFFast fe e).run a = .ok (false, a2)) : (crdT fe pushed e).run a = .ok (false, a2) := by
  simp only [crdT, StateT.run_bind, h, except_ok_bind]; rfl

theorem crdT_run_true {fe : IFEnv} {pushed : List NIdx} {e : EIdx} {a a2 a3 : AState} {mb : Bool}
    (h : (constsResolveFFast fe e).run a = .ok (true, a2))
    (h2 : (ConRon.Arena.mentionsAnyConst pushed e).run a2 = .ok (mb, a3)) :
    (crdT fe pushed e).run a = .ok (!mb, a3) := by
  simp only [crdT, StateT.run_bind, h, except_ok_bind, ite_true, h2]; rfl

theorem allM_cons_run {f : EIdx → AM Bool} {x : EIdx} {xs : List EIdx} {a a' : AState} {b : Bool}
    (h : (f x).run a = .ok (b, a')) :
    ((x :: xs).allM f).run a = if b then (xs.allM f).run a' else .ok (false, a') := by
  cases b <;> simp only [List.allM, StateT.run_bind, h, except_ok_bind] <;> rfl

/-- `mentions_any`'s memo across a core call (which writes the `hb` memo only). -/
theorem maMR_core {m m' : Mem} {mp : Std.HashMap EIdx Bool} (h : MFr [HBM] [214, 215] m m')
    (hm : maMR m mp) : maMR m' mp := by
  obtain ⟨A, C, f, hA, hC⟩ := h.memo maSch.arr maSch.cs (by decide) (by decide) (by decide) (by decide)
  exact memoRG_frame maSch maSch_wf bmKey _ A C hA hC m m' f mp hm

/-- **`class_rule_check_domains`' model refines the twin's `rbs.allM`** (from a well-formed
`mentions_any` memo; its twin state a `PStep` at `fe`'s read invariant). -/
theorem crdW_ok (fe : IFEnv) (v po pl : Word) (pushed : List NIdx) {env : ConLeche.Env} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (o l : Word) (xs : List EIdx) (xsP : List ConLeche.Expr) (r : List Word),
    crdW n m v po pl o l = some (r, m') → StageR v fe m a → decHL m o.toNat l.toNat = some xs →
    o.toNat + l.toNat < 2 ^ 64 → o.toNat + l.toNat ≤ iwTop m → AbsOK m →
    decHL m po.toNat pl.toNat = some pushed → po.toNat + pl.toNat ≤ iwTop m → (∃ mp, maMR m mp) →
    ConRon.Bridge.Inductives.ReadOK env fe a → Frontend.denoteEList a.store xs = some xsP →
    ∃ b a', (xs.allM (crdT fe pushed)).run a = .ok (b, a') ∧ KeepPost v fe decW0B m m' a' r b ∧
      AbsOK m' ∧ (∃ mp, maMR m' mp) ∧ ConRon.Bridge.Inductives.PStep a a' := by
  induction n with
  | zero => intro m m' a o l xs xsP r h; simp [crdW] at h
  | succ n ih =>
    intro m m' a o l xs xsP r h hS hd hb ht hA hpu hpb hma hok hxs
    obtain ⟨mp, hM⟩ := hma
    by_cases hl : l = 0
    · subst hl
      rw [crdW.arm1 n m v po pl o 0 rfl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : xs = [] := by simpa [decHL, hslice?] using hd.symm
      subst this
      exact ⟨true, a, rfl, ⟨hS, IWGrow.refl m, by simp [decW0B]⟩, hA, ⟨mp, hM⟩,
        ConRon.Bridge.Inductives.PStep.refl hok.state⟩
    obtain ⟨w, xs', rfl, hw, hw32, hd'⟩ := decHL_cons hd hl hb
    obtain ⟨hsum, -⟩ := toNat_succ_of_lt hb hl
    have hl0 : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
    simp only [Frontend.denoteEList] at hxs
    cases he : denoteE a.store (decI w) with
    | none => rw [he] at hxs; simp at hxs
    | some eP =>
    cases hr : Frontend.denoteEList a.store xs' with
    | none => rw [he, hr] at hxs; simp at hxs
    | some rest =>
    rw [he, hr] at hxs
    obtain rfl := (Option.some.inj hxs).symm
    rw [crdW.arm2 n m v po pl o l hl, hw] at h
    obtain ⟨rb, m2, h2, h⟩ := kSome_inv h (by simp [crdW.k_consts_resolve_ffast]) (fun _ _ => rfl)
    obtain ⟨c, a2, hrun2, ⟨hS2, hg2, hceq, -⟩, hA2⟩ := crfF_ok v fe w hw32 m m2 a rb h2 ⟨hS, hA⟩
    obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.constsResolveFFast_pstep hok he hrun2
    have hM2 : maMR m2 mp := maMR_mfr (crfF_mfr h2) hM
    by_cases hz : rb.headD 0 = 0
    · rw [crdW.k_consts_resolve_ffast.arm1 n v po pl o l rb m2 hz] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hc : c = false := by rw [← hceq, hz]; rfl
      subst hc
      refine ⟨false, a2, ?_, ⟨hS2, hg2, by simp [decW0B]⟩, hA2, ⟨mp, hM2⟩, p1⟩
      rw [allM_cons_run (crdT_run_false hrun2)]; rfl
    rw [crdW.k_consts_resolve_ffast.arm2 n v po pl o l rb m2 hz] at h
    have hc : c = true := by rw [← hceq]; exact bne_iff_ne.mpr hz
    subst hc
    have hto : o.toNat < iwTop m := by omega
    have hw2 : rdW (m2.arr64 IW) o = w := by
      rw [← hw]; simp only [rdW]; rw [hg2.iwGet _ hto]
    rw [hw2] at h
    cases n with
    | zero => simp [maConstWk, crdW.k_mentions_any_const] at h
    | succ n' =>
    obtain ⟨b3, m3, h3, h⟩ := kSome_inv h (by simp [crdW.k_mentions_any_const]) (fun _ _ => rfl)
    have hT : iwTop m2 < 2 ^ 64 := (rdW (m2.arr64 CTL) 200).toNat_lt
    have hpu2 : decHL m2 po.toNat pl.toNat = some pushed := by rw [decHL_grow hg2 hpb]; exact hpu
    obtain ⟨ws, hws, hnm, hwlt⟩ := slR_of_decHL m2 _ _ _ hpu2 (by have := hg2.iw; omega)
    rw [L.ofNat_toNat, L.ofNat_toNat] at hws
    obtain ⟨mb, hrunM, hbm, hM3, hS3, hg3⟩ :=
      maConstW_ok n' (fun _ => none) fe v m2 m3 a2 po pl w b3 ws mp h3 hS2 hw32 hws hwlt hM2
    have hA3 : AbsOK m3 := AFr.of_frame (maConstW_frame h3) (by decide) (by decide) hA2
    have hrunD : (crdT fe pushed (decI w)).run a = .ok (!mb, a2) := by
      rw [hnm]; exact crdT_run_true hrun2 hrunM
    have hg23 := hg2.trans hg3
    by_cases hmz : b3 ≠ 0
    · rw [crdW.k_mentions_any_const.arm1 (n' + 1) v po pl o l b3 m3 hmz] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : mb = true := by rw [← hbm]; simpa using hmz
      subst this
      refine ⟨false, a2, ?_, ⟨hS3, hg23, by simp [decW0B]⟩, hA3, ⟨∅, hM3⟩, p1⟩
      rw [allM_cons_run hrunD]; rfl
    rw [crdW.k_mentions_any_const.arm2 (n' + 1) v po pl o l b3 m3 (Classical.not_not.mp hmz)] at h
    have : mb = false := by rw [← hbm]; simpa using hmz
    subst this
    obtain ⟨r4, m4, h4, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
    rw [crdW.k_class_rule_check_domains.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨b4, a4, hrun4, ⟨hS4, hg4, hd4, hd41⟩, hA4, hM4, p4⟩ :=
      ih m3 m4 a2 (o + 1) (l - 1) xs' rest r4 h4 hS3
        (by rw [decHL_grow hg23 (by omega)]; exact hd') (by omega) (by have := hg23.iw; omega) hA3
        (by rw [decHL_grow hg23 hpb]; exact hpu) (by have := hg23.iw; omega) ⟨∅, hM3⟩
        (hok.mono p1.ok p1.ext p1.pins) (ConRon.Bridge.denoteEList_ext p1.ext _ _ hr)
    refine ⟨b4, a4, ?_, ⟨hS4, hg23.trans hg4, by simpa [decW0B] using And.intro hd4 hd41⟩, hA4, hM4,
      p1.trans p4⟩
    rw [allM_cons_run hrunD]; exact hrun4

/-! ## `class_rule_check` -/

l_model crcE_spec (p : Prog) (hp : CruleProg p)
  fns [hp.check ↦ crcE]
  specs [crgE_spec p hp n, flushCaches_spec p hp.toFlushProg n, stripLams_specF p hp.strip n,
    crdW_spec p hp.dom hp.hcr hp.ma n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `class_rule_check` gives besides the twin's check (from `m`, `a`): the stage invariant
under `StageC`, the growth, the abstraction memo, `mentions_any`'s memo, the core step. -/
structure CrcPost (dn : NIdx → Option ConLeche.Name) (visR : Word) (feR : IFEnv)
    (envR : ConLeche.Env) (m : Mem) (a : AState) (m' : Mem) (a' : AState) : Prop where
  stage : StageC dn visR feR envR m' a'
  grow : IWGrow m m'
  abs : AbsOK m'
  ma : ∃ mp, maMR m' mp
  core : ConRon.Bridge.CoreStep envR feR a a'

/-- What `class_rule_ok` gives besides the twin's rule `y` (from `m`, `a`): `CrcPost`'s facts and
the rule returned as built (`gen` itself). -/
structure CrulePost (dn : NIdx → Option ConLeche.Name) (visR : Word) (feR : IFEnv)
    (envR : ConLeche.Env) (m : Mem) (a : AState) (gen w : Word) (m' : Mem) (y : EIdx) (a' : AState) :
    Prop where
  stage : StageC dn visR feR envR m' a'
  grow : IWGrow m m'
  val : w = gen
  res : y = decI gen
  abs : AbsOK m'
  ma : ∃ mp, maMR m' mp
  core : ConRon.Bridge.CoreStep envR feR a a'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name}

include hq in
/-- **`class_rule_check` refines `classRuleCheck`, both outcomes** under `StageC` (twin side
con-ron's `classRuleCheck_spec`'s proof): the guards (`crg_ref`, against `crgT`: `crgT_bind`), the
inference (`inferC_rsim`; its error the core stub's claim), the flush (`ReadOK.flush`), the
λ-telescope (`stripLams_pstep`), the domains at `feR` naming no pushed recursor (`crdW_ok`); the
domains' site calls `unresolved_consts_error` (`uce_errClaim_hi`). -/
theorem crc_ref (hp : CruleProg p) (hApd : ApdF p) {visR : Word} {feR : IFEnv}
    {envR : ConLeche.Env} (henvR : ConLeche.EnvWF envR) {a : AState} (N : Nat) (hN : N ≤ 2 ^ 62)
    {m : Mem} {pO pL cvR n gen : Word} {cv : IConstantVal} {pushed : List NIdx}
    (hC : StageC dn visR feR envR m a) (hgen : H gen)
    (hqd : decCV (erecP m) cvR.toNat = some cv) (hqb : cvR.toNat + 3 < 2 ^ 64) (hA : AbsOK m)
    (hpu : decHL m pO.toNat pL.toNat = some pushed) (hpb : pO.toNat + pL.toNat ≤ iwTop m)
    (hma : ∃ mp, maMR m mp) {cvRP : ConLeche.ConstantVal} {genP : ConLeche.Expr}
    (hcvP : Frontend.denoteCV a.store cv = some cvRP)
    (hgP : denoteE a.store (decI gen) = some genP) :
    RefE (VerdictCtxU p) (crcE p N m visR pO pL cvR n gen)
      (ConRon.Arena.classRuleCheck .verified feR pushed cv n.toNat (decI gen)) a
      (fun v _ a' => CrcPost dn visR feR envR m a v.2 a') := by
  cases N with
  | zero => rw [crcE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ N =>
  rw [crcE.arm1]
  unfold ConRon.Arena.classRuleCheck
  rw [crgT_bind]
  refine RefE.bindE (fun _ => rfl) id (crg_ref hp hApd N hC hgen hqd hqb hA hcvP hgP)
    fun ⟨r1, m1⟩ _ a1 _ ⟨hC1, hg1, hA1, c14, hfvP, hf1⟩ => ?_
  dsimp only at hC1 hg1 hA1 hf1
  obtain ⟨mp, hM⟩ := hma
  have hM1 := maMR_mfr hf1 hM
  have hws : ConLeche.Expr.WScoped 0 genP := ConLeche.Expr.WScoped.of_not_hasFvar hfvP
  dsimp only [crcE.k_class_rule_check_guards]
  try simp only [fail_bindAM]
  -- the inference
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h2 => hG.core.inferTypeCore N (by omega) hC1.stageT 0 gen hgen _ h2)
    (inferC_rsim hq henvR N (by omega) hC1 hA1 0 gen hgen (ConRon.Bridge.denote_ext hgP c14.ext) hws)
    fun r2 m2 x6 a6 h2 _ ⟨hC2, hg2, _, hA2, c5, _⟩ => ?_
  have hM2 := maMR_core (callW_coreFrame hq.closed (by decide) (callW_of_callE h2)).mfr hM1
  -- the flush
  dsimp only [crcE.k_infer_type_core]
  refine RefE.abort0 rfl fun hno => ?_
  have hok : FlushOK m2 := by simpa using hno
  obtain ⟨hS3, hg3⟩ := flush_stage hC2.stage hok
  obtain ⟨hok6, -, hst6⟩ := ConRon.Bridge.Inductives.ReadOK.flush hC2.check.toR (flushCaches_run a6)
  have hA3 : AbsOK (flushMem m2) := AFr.of_frame (flushMem_frame _) (by decide) (by decide) hA2
  have hM3 : maMR (flushMem m2) mp := maMR_mfr (MFr.of_frame (flushMem_frame _) (by simp)
    (fun x hx => .inl (by have := flushCtl_lt x hx; omega))) hM2
  have hx6 : Ext a6.store ({ a6 with caches := Caches.empty } : AState).store := Ext.refl _
  have hC3 := hC2.of_check hS3 hA3 hok6 hx6
  have c16 := (c14.trans c5).trans
    (⟨hok6, by rw [hst6]; exact Ext.refl _, rfl⟩ :
      ConRon.Bridge.CoreStep envR feR a6 { a6 with caches := Caches.empty })
  refine RefE.bind_right (flushCaches_run a6) ?_
  -- the λ-telescope
  refine RefE.bindLift (fun _ => rfl) fun r4 m4 h4 => ?_
  obtain ⟨x7, a7, hs, hS4, hg4, hd4⟩ := stripF_lams_ok visR feR n gen hgen _ m4 _ r4 h4 hS3
  refine ⟨_, _, hs, ?_⟩
  have hA4 : AbsOK m4 := stripF_afr h4 hA3
  have hM4 : maMR m4 mp := maMR_mfr (MFr.ofStripF h4) hM3
  obtain ⟨hs7, hq7⟩ := ConRon.Bridge.Inductives.stripLams_pstep hok6.state
    (ConRon.Bridge.denote_ext hgP c16.ext) hs
  subst hs7
  have hC4 : StageC dn visR feR envR m4 { a6 with caches := Caches.empty } :=
    hC3.of_check hS4 hA4 hok6 (Ext.refl _)
  rcases x7 with _ | ⟨rbs, body⟩
  · rw [crcE.k_strip_lams.abort1 _ _ _ _ _ _ _ _ hd4]; exact RefE.of_cls0 rfl
  obtain ⟨h41, ⟨hdl, htl⟩, -⟩ := hd4
  rw [crcE.k_strip_lams.arm1 _ _ _ _ _ _ _ _ (by rw [h41]; decide)]
  simp only [L.getD_one, L.getD_two, Nat.reduceAdd] at hdl htl
  obtain ⟨rbsP, bodyP, -, hrbs, -⟩ := ConRon.Bridge.Inductives.denoteBP_some hq7
  -- the domains at `feR`
  refine RefE.bindLift (fun _ => rfl) fun r5 m5 h5 => ?_
  have hb4 : (r4.tail.headD 0).toNat + (r4.tail.tail.headD 0).toNat < 2 ^ 64 := by
    have h1 : iwTop m4 ≤ (m4.arr64 IW).size := hS4.iw.iw
    have h2 : (m4.arr64 IW).size < 2 ^ 64 := hS4.iw.iwSize
    omega
  have hg14 : IWGrow m m4 := ((hg1.trans hg2).trans hg3).trans hg4
  obtain ⟨b, a8, hdom, ⟨hS5, hg5, hb5⟩, hA5, hM5, p8⟩ := crdW_ok feR visR pO pL pushed N m4 m5 _ _ _
    rbs rbsP r5 h5 hS4 hdl hb4 htl hA4 (by rw [decHL_grow hg14 hpb]; exact hpu)
    (Nat.le_trans hpb hg14.iw) ⟨mp, hM4⟩ hok6.toR hrbs
  refine ⟨_, _, hdom, ?_⟩
  have c18 := c16.trans (p8.toCore hok6)
  have hC5 : StageC dn visR feR envR m5 a8 := hC4.of_check hS5 hA5 c18.ok p8.ext
  by_cases h50 : r5.headD 0 = 0
  · rw [crcE.k_class_rule_check_domains.arm1 _ _ _ _ _ _ h50]
    have eb : b = false := by rw [← hb5.1]; simpa using h50
    subst eb
    refine RefE.ite_neg (by decide) ?_
    rcases h6 : callE p N "unresolved_consts_error" [visR, gen, 4] m5 with e6 | ⟨r6, m6⟩
    · rw [crcE.k_unresolved_consts_error.eq_1]
      obtain ⟨M5, hC5'⟩ := hC5.stageT.core
      exact fun hG => uce_errClaim_hi hG.uce hG.nv hC5'.arena.base hC5'.pins hgen (by decide) h6 _
    · rw [crcE.k_unresolved_consts_error.abort1]; exact RefE.of_cls0 rfl
  rw [crcE.k_class_rule_check_domains.arm2 _ _ _ _ _ _ h50]
  have eb : b = true := by rw [← hb5.1]; simpa using h50
  subst eb
  exact RefE.ite_pos rfl (RefE.ret rfl ⟨hC5, ((((hg1.trans hg2).trans hg3).trans hg4).trans hg5), hA5, hM5, c18⟩)

end sims

/-! ## `class_rule_ok` -/

l_model cruleE_spec (p : Prog) (hp : CruleProg p)
  fns [hp.rule ↦ cruleE]
  specs [crcE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section sims2
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name}

include hq in
/-- **`class_rule_ok` refines `classRuleOk`, both outcomes** under `StageC`: the check
(`crc_ref`), then the rule returned as built. -/
theorem crule_ref (hp : CruleProg p) (hApd : ApdF p) {visR : Word} {feR : IFEnv}
    {envR : ConLeche.Env} (henvR : ConLeche.EnvWF envR) {a : AState} (N : Nat) (hN : N ≤ 2 ^ 62)
    {m : Mem} {pO pL cvR n gen : Word} {cv : IConstantVal} {pushed : List NIdx}
    (hC : StageC dn visR feR envR m a) (hgen : H gen)
    (hqd : decCV (erecP m) cvR.toNat = some cv) (hqb : cvR.toNat + 3 < 2 ^ 64) (hA : AbsOK m)
    (hpu : decHL m pO.toNat pL.toNat = some pushed) (hpb : pO.toNat + pL.toNat ≤ iwTop m)
    (hma : ∃ mp, maMR m mp) {cvRP : ConLeche.ConstantVal} {genP : ConLeche.Expr}
    (hcvP : Frontend.denoteCV a.store cv = some cvRP)
    (hgP : denoteE a.store (decI gen) = some genP) :
    RefE (VerdictCtxU p) (cruleE p N m visR pO pL cvR n gen)
      (ConRon.Arena.classRuleOk .verified feR pushed cv n.toNat (decI gen)) a
      (fun v y a' => CrulePost dn visR feR envR m a gen v.1 v.2 y a') := by
  cases N with
  | zero => rw [cruleE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ N =>
  rw [cruleE.arm1]
  unfold ConRon.Arena.classRuleOk
  refine RefE.bindE (fun _ => rfl) id
    (crc_ref hq hp hApd henvR N (by omega) hC hgen hqd hqb hA hpu hpb hma hcvP hgP)
    fun ⟨r1, m1⟩ _ a1 _ hP => ?_
  dsimp only [cruleE.k_class_rule_check]
  exact RefE.ret rfl ⟨hP.stage, hP.grow, rfl, rfl, hP.abs, hP.ma, hP.core⟩

include hq in
/-- **`class_rule_ok` refines `classRuleOk`** under `StageC` (`crule_ref`'s ok half): the rule is
returned as built. -/
@[refines ConRon.Arena.classRuleOk]
theorem classRuleOk_refinesC (hp : CruleProg p) (hApd : ApdF p) (N : Nat) (hN : N ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (visR pO pL : Word) (feR : IFEnv) {envR : ConLeche.Env}
    (henvR : ConLeche.EnvWF envR) (cvR n gen : Word) (cv : IConstantVal) (pushed : List NIdx)
    (hC : StageC dn visR feR envR s₀.mem a₀) (hgen : H gen)
    (hqd : decCV (erecP s₀.mem) cvR.toNat = some cv) (hqb : cvR.toNat + 3 < 2 ^ 64)
    (hA : AbsOK s₀.mem) (hpu : decHL s₀.mem pO.toNat pL.toNat = some pushed)
    (hpb : pO.toNat + pL.toNat ≤ iwTop s₀.mem) (hma : ∃ mp, maMR s₀.mem mp)
    {cvRP : ConLeche.ConstantVal} {genP : ConLeche.Expr}
    (hcvP : Frontend.denoteCV a₀.store cv = some cvRP)
    (hgP : denoteE a₀.store (decI gen) = some genP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_rule_ok" [visR, pO, pL, cvR, n, gen]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classRuleOk .verified feR pushed cv n.toNat (decI gen)) a₀ ∧
      StageC dn visR feR envR s'.mem
        (AM.st (ConRon.Arena.classRuleOk .verified feR pushed cv n.toNat (decI gen)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decW0E s'.mem r (AM.res (ConRon.Arena.classRuleOk .verified feR pushed cv n.toNat (decI gen)) a₀) ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (cruleE_spec p hp N s₀ visR pO pL cvR n gen)
    (crule_ref hq hp hApd henvR N hN hC hgen hqd hqb hA hpu hpb hma hcvP hgP)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow,
    by have hv : r.headD 0 = gen := hR.val
       rw [hres, hR.res]; exact ⟨by rw [hv]; exact hgen, by rw [hv]⟩, hR.abs⟩

end sims2

/-! ## `class_rules_ok_one` -/

/-- `CrsProg` with `class_rule_ok`'s lookups, and `class_gen_rule` keeping `mentions_any`'s memo
(at the checker: a write-set fact, `maMR.ofClosedL`). -/
structure CrsProgE (p : Prog) : Prop extends CrsProg p where
  cr : CruleProg p
  maKeep : ∀ (n : Nat) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem),
    callW p n "class_gen_rule" vs m = some (r, m') → (∃ mp, maMR m mp) → ∃ mp, maMR m' mp

l_model cr1E_spec (p : Prog) (hP : CrsProgE p)
  fns [hP.one ↦ cr1E] specs [cruleE_spec p hP.cr n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section cr1
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name}

include hq in
/-- **`class_rules_ok_one` refines `classRuleOk` at the telescope length `nP + |slots| + nF`, both
outcomes**: the word sum's overflow abort (class `0`), then `class_rule_ok` in tail position
(`crule_ref`). -/
theorem cr1_ref (hp : CruleProg p) (hApd : ApdF p) {visR : Word} {feR : IFEnv}
    {envR : ConLeche.Env} (henvR : ConLeche.EnvWF envR) {a : AState} (N : Nat) (hN : N ≤ 2 ^ 62)
    {m : Mem} {pO pL g cvR x gen : Word} {cv : IConstantVal} {pushed : List NIdx} {G : ClassGen}
    {X : ClassCtor}
    (hC : StageC dn visR feR envR m a) (hgen : H gen) (hcv : decCVp m cvR.toNat = some cv)
    (hext : CVExt m cvR.toNat) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hX : DecB (fun m => decCC m x.toNat) m X)
    (hA : AbsOK m) (hpu : decHL m pO.toNat pL.toNat = some pushed) (hpb : pO.toNat + pL.toNat ≤ iwTop m)
    (hma : ∃ mp, maMR m mp) {cvRP : ConLeche.ConstantVal} {genP : ConLeche.Expr}
    (hcvP : Frontend.denoteCV a.store cv = some cvRP)
    (hgP : denoteE a.store (decI gen) = some genP) :
    RefE (VerdictCtxU p) (cr1E p N m visR pO pL g cvR x gen)
      (ConRon.Arena.classRuleOk V feR pushed cv (G.nP + G.slots.length + X.nF) (decI gen)) a
      (fun v y a' => CrulePost dn visR feR envR m a gen v.1 v.2 y a') := by
  cases N with
  | zero => rw [cr1E.eq_1]; exact RefE.of_cls0 (by simp)
  | succ N =>
  have hsz := hC.stage.iw.iwSize
  obtain ⟨hnP, -⟩ := rec2CG_parts hG
  obtain ⟨hsl, -⟩ := rec3CG_parts hG
  obtain ⟨hnF, -, -⟩ := rec2CC_parts (hX.get (decCC_mono _))
  obtain ⟨e0, t0⟩ := rec2RdN (w := g) (k := 0) (by simpa using hnP) hsz
  obtain ⟨e8, t8⟩ := rec2RdN (w := g) (k := 8) hsl hsz
  obtain ⟨e1, t1⟩ := rec2RdN (w := x) (k := 1) hnF hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero,
    show UInt64.ofNat 8 = (8 : Word) from rfl, show UInt64.ofNat 1 = (1 : Word) from rfl] at e0 e8 e1
  by_cases hb : rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8) + rdW (m.arr64 IW) (x + 1) <
      rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)
  · rw [cr1E.abort1 p N m visR pO pL g cvR x gen hb]; exact RefE.of_cls0 rfl
  rw [cr1E.arm1 p N m visR pO pL g cvR x gen hb]
  have hn : (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8) + rdW (m.arr64 IW) (x + 1)).toNat =
      G.nP + G.slots.length + X.nF := by
    rw [L.toNat_add_of_not_lt hb, e0, e8, e1, t1]
    rw [UInt64.toNat_add, t0, t8]; exact congrArg (· + X.nF) (Nat.mod_eq_of_lt hns)
  have h := crule_ref hq hp hApd henvR N (by omega) hC hgen (rec2DecCV_erecP hcv hext)
    (rec3CVExt_lt hC.stage hext) hA hpu hpb hma hcvP hgP
    (n := rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8) + rdW (m.arr64 IW) (x + 1))
  rwa [hn] at h

end cr1

end L.Ind

end
