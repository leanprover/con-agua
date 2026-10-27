import ConAgua.Arena.IndT.Install2
import ConAgua.Arena.IndT.KeepC
import ConAgua.Arena.IndT.Install3
import ConAgua.Arena.IndRealSortDn
import ConAgua.Arena.IndInstallSpec.CbProg
import ConAgua.Arena.IndInstallSpec.IcvgW
import ConAgua.Arena.IndInstallSpec.IndsOut

/-!
# `checkBlockInds` under `StageC` (lane `indstaget`)

Stage 1 (`check_block_inds`) from `StageC` and con-ron's preconditions of `checkBlockInds_spec`
(the shape denotes, the environment denotes, the index is coherent), its twin side transcribed
from that spec's proof: member 0's former (`checkBlockTele_refinesC`, con-ron's
`checkBlockTele_specF` on its run for the answer's denotation), the other formers
(`checkBlockTeles_refinesC`, `checkBlockTeles_specF`), the agreements (`checkBlockAgree_refinesC`),
the shape's sort (`BlockShape.withSort_spec`), the formers' constants (L only), the formers consed
(`consBlockInds_spec`). The formers are checked at the ENTRY index, so the frame is the `CoreStep`
at `fe` (con-ron's); the stage relation after is at the returned view (`IndsOut`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A callee proved at every positive fuel up to a bound is simulated at every fuel up to it. -/
theorem _root_.L.Arena.Sim.callW_posB {α : Type} {p : Prog} {f : FnName} {args : List Word} {m : Mem} {op : AM α}
    {a : AState} {Q : List Word → α → Mem → AState → Prop} {N : Nat}
    (h : ∀ k, k + 1 ≤ N → Sim (callW p (k + 1) f args m) op a Q) (n : Nat) (hn : n ≤ N) :
    Sim (callW p n f args m) op a Q := by
  cases n with
  | zero => rw [callW_zero]; exact Sim.of_none
  | succ k => exact h k hn

/-- `block_shape_with_sort` as a `Sim` under `StageC`, its `lvl_eq_c` the real call
(`installWithSortSim`'s statement; `lvlEqC_simC` for the stub contract). -/
theorem installWithSortSimC {p : Prog} (hcl : CoreStageClosed p) (hLC : LvlCacheProg p)
    (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hpw : p.lookup "pin_word" = some pinWordL)
    (hp : p.lookup "block_shape_with_sort" = some blockShapeWithSort) (n : Nat)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env} {m : Mem}
    {a : AState} {pp s : Word} {bs : BlockShape} (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp) (hs : H s)
    {sP : ConLeche.Level} (hsP : denoteL a.store.ls (decI s) = some sP) :
    Sim (callW p n "block_shape_with_sort" [pp, s] m) (bs.withSort (decI s)) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        DecB (fun m => decBS m (r.headD 0).toNat) m' x ∧ ShapeSrc m' (r.headD 0) ∧
        (RecsB m pp → RecsB m' (r.headD 0))) := by
  intro r m' e
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeWithSort_specC p ha hpw hp (realCall p) (realCall_spec p) n _ pp s) e
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  have hS := hC.stage
  obtain ⟨bs', a', q, hrun, rfl, -, hS', hg, htopq, hcell, hD⟩ :=
    wsC_ok (realCall p) n dn fe vis m s'.mem a pp s r bs hW hS hs
      (fun m'' hg => hq.stab (decBS_mono _) m'' hg) hq9 (fun k r2 m2 h0 e2 => by
        have hF := hS.1.pins.full h0
        obtain ⟨lz, hdz⟩ := hC.stageT.twin.den.zero
        rw [hF.zeroLevel] at hdz
        obtain ⟨x, a2, hrun2, hC2, hg2, hd2, -, -⟩ :=
          lvlEqC_simC p hcl hLC k hC hA s (pinW m 53) hs hF.lv_lt.2.1 sP lz hsP hdz r2 m2 e2
        exact ⟨x, a2, hrun2, hC2.stage, hg2, hd2⟩)
  refine ⟨bs', a', hrun, hS', hg, by simpa using hD hq, ?_, fun hrb o l h1 h2 => ?_⟩
  rotate_left
  · simp only [List.headD_cons] at h1 h2
    have e2 := hcell 2 (by decide) (by decide) (by decide)
    have e3 := hcell 3 (by decide) (by decide) (by decide)
    have hp2 : iwN s'.mem (pp.toNat + 2) = iwN m (pp.toNat + 2) := iwN_grow hg (by omega)
    have hp3 : iwN s'.mem (pp.toNat + 3) = iwN m (pp.toNat + 3) := iwN_grow hg (by omega)
    have g2 : iwN s'.mem (q.toNat + 2) = iwN s'.mem (pp.toNat + 2) := by simp only [iwN, nat?, iwA, e2]
    have g3 : iwN s'.mem (q.toNat + 3) = iwN s'.mem (pp.toNat + 3) := by simp only [iwN, nat?, iwA, e3]
    rw [g2, hp2] at h1; rw [g3, hp3] at h2
    exact Nat.le_trans (hrb o l h1 h2) hg.1
  intro o l h1 h2
  simp only [List.headD_cons] at h1 h2
  have e0 := hcell 0 (by decide) (by decide) (by decide)
  have e1 := hcell 1 (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at e0
  have hp0 : iwN s'.mem pp.toNat = iwN m pp.toNat := iwN_grow hg (by omega)
  have hp1 : iwN s'.mem (pp.toNat + 1) = iwN m (pp.toNat + 1) := iwN_grow hg (by omega)
  have g0 : iwN s'.mem q.toNat = iwN s'.mem pp.toNat := by simp only [iwN, nat?, iwA, e0]
  have g1 : iwN s'.mem (q.toNat + 1) = iwN s'.mem (pp.toNat + 1) := by simp only [iwN, nat?, iwA, e1]
  rw [g0, hp0] at h1; rw [g1, hp1] at h2
  exact Nat.le_trans (hsrc o l h1 h2) hg.1

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p) (hOpf : OpfF p) (hLC : LvlCacheProg p)
  (hApd : ApdF p) (hCrk : CrKeep p) (hLz : LzcF p)

include hq henv hV hOpf hLC hApd hCrk hLz in
/-- **`check_block_inds` under `StageC`** (twin side: con-ron's `checkBlockInds_spec`'s proof). -/
theorem ibiW_simC (hP : IndsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {pp isRec : Word} {bs : BlockShape} {b : Bool}
    (hC : StageC dn vis fe env m a) (hqd : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcx : ShapeCV m pp) (hb : (isRec != 0) = b) (hA : AbsOK m)
    (hk : ∀ f ∈ indsKeepCalleesC, AbsKeep p f) {bsP : ConLeche.BlockShape}
    (hbsP : ConRon.Bridge.Inductives.dShape a.store bs = some bsP)
    (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) (hcoh : ConRon.Bridge.IFEnvCoh fe)
    (hlpsDn : ∀ ms ∈ bs.members, ∀ k ∈ ms.cvT.levelParams, (dn k).isSome) :
    Sim (ibiW p (n + 1) m vis pp isRec) (ConRon.Arena.checkBlockInds V fe ⟨bs⟩ b) a
      (fun r x m' a' => IndsOut dn m r x m' a' ∧ AbsOK m' ∧
        (RecsB m pp → RecsB m' (r.tail.tail.tail.headD 0)) ∧ ConRon.Bridge.CoreStep V env fe a a') := by
  have hS := hC.stage
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hq', hq9, -⟩ := partsShapeFacts hqd hsrc
  have hkw := partsShapeK hq' hq9
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hqd hq9
  have hqt : decBS (truncM m) pp.toNat = some bs := hqd
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some hqt
  obtain ⟨o, l, ho, hl, hdm, hob⟩ := partsAt decMS_mono hmem
  have hdm' : decPL (truncM m) (decMS (truncM m)) o.toNat l.toNat = some bs.members := hdm
  have hlk : bs.k = l.toNat := decPL_length _ hdm'
  have hkb : bs.k < 2 ^ 64 := by rw [hlk]; exact l.toNat_lt
  obtain ⟨hw0, -, -⟩ := partsIwRd ho (w := pp) rfl
  rw [UInt64.ofNat_toNat] at hw0
  have hkl : UInt64.ofNat bs.k = l := by rw [hlk]; exact UInt64.ofNat_toNat
  obtain ⟨hmsP, -, -, -, hsP, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hbsP
  rw [ibiW.eq_2]
  rw [hkw, hkl, hw0, hnpw]
  split
  · exact Sim.of_none
  rename_i hl0
  -- the members, with their formers' constant records below the tops
  have hob' : o.toNat + l.toNat ≤ iwTop m := hob.resolve_left hl0
  have hoN : iwN m pp.toNat = some o.toNat := (rec2IwN_trunc ho).2
  have hlN : iwN m (pp.toNat + 1) = some l.toNat := (rec2IwN_trunc hl).2
  have hms : MemsOK m o l bs.members :=
    ⟨⟨hdm, hob'⟩, fun j hj c hc d hd => hcx o.toNat l.toNat hoN hlN j hj c hc d hd⟩
  obtain ⟨q0, ms0, rest, hmeq, hw, hqb, hmok, hrest⟩ := hms.cons hl0
  rw [hw]
  unfold ConRon.Arena.checkBlockInds
  simp only [hmeq]
  rw [hmeq] at hmsP
  obtain ⟨ms0P, restP, -, hm0, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmsP
  have hq0 : (UInt64.ofNat q0 : Word).toNat = q0 := UInt64.toNat_ofNat_of_lt' hqb
  -- member 0's former
  refine Sim.bindK (K := ibiW.k_check_block_tele p n vis pp isRec o l (UInt64.ofNat bs.nP))
    (body := fun r1 m1 => ibiW.k_check_block_teles p n vis pp isRec (UInt64.ofNat bs.nP) (r1.headD 0) (r1.tail.headD 0)
      (callW p n "check_block_teles" [vis, UInt64.ofNat bs.nP, o + 1, l - 1] m1)) rfl (fun _ _ => rfl)
    (by
      have h := Sim.callW_posB (N := 2 ^ 62) (fun k hk => installSimCall
        (Q := fun r x m' a' => TeleOutC dn vis fe env m r x m' a' ∧ AbsOK m' ∧
          ConRon.Bridge.CoreStep V env fe a a')
        (checkBlockTele_refinesC hq henv hV hApd hCrk hP.toCstProg hP.bTele k (by omega) ⟨m, Locals.init []⟩ a
          (UInt64.ofNat bs.nP) _ ms0 hC hmok hA hm0 hfe)
        fun _ _ ⟨_, hok, hQ, hA', hc⟩ => ⟨hok, hQ, hA', hc⟩) n hn
      rw [UInt64.toNat_ofNat_of_lt' hnpb] at h; exact Sim.withRunC h) ?_
  rintro r1 ⟨cvTa0, s0⟩ m1 a1 ⟨⟨⟨hC1, hg1, hcv1, hcx1, hs32, hsd⟩, hA1, c1⟩, hr1⟩
  obtain ⟨-, ⟨cvTa₀P, s0P⟩, ⟨h1a, h1b, hw1⟩, hfk1⟩ := ConRon.Bridge.Inductives.checkBlockTele_specF fe rfl
    (ConRon.Bridge.CoreSpec.of_core rfl) henv bs.nP ms0 ms0P a a1 _ hC.check ⟨hm0, hfe⟩ hr1
  dsimp only at h1a h1b hw1
  have hS1 := hC1.stage
  have hc0 := installCvDecB hcv1 hcx1
  have hfe1 := ConRon.Bridge.denoteFEnv_mono c1.ext hfe
  -- the other members' formers
  refine Sim.bindK (K := ibiW.k_check_block_teles p n vis pp isRec (UInt64.ofNat bs.nP) (r1.headD 0) (r1.tail.headD 0))
    (body := fun r2 m2 => ibiW.k_check_block_agree p n vis pp isRec (r1.headD 0) (r1.tail.headD 0) (r2.headD 0)
      (r2.tail.headD 0) (callW p n "check_block_agree"
      [vis, UInt64.ofNat bs.nP, r1.headD 0, r1.tail.headD 0, r2.headD 0, r2.tail.headD 0] m2))
    rfl (fun _ _ => rfl)
    (by
      have h := Sim.callW_posB (N := 2 ^ 62) (fun k hk => installSimCall
        (Q := fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m1 m' ∧
          PSlR decTele x (r.headD 0) (r.tail.headD 0) m' ∧ AbsOK m')
        (checkBlockTeles_refinesC hq henv hV hApd hCrk hP.toInstProg (k + 1) hk ⟨m1, Locals.init []⟩ a1
        (UInt64.ofNat bs.nP) (o + 1) (l - 1) rest hC1 (hrest.grow hg1) hA1
        (ConRon.Bridge.Inductives.dMember_ext.list c1.ext _ _ hrestP) hfe1)
        fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩) n hn
      rw [UInt64.toNat_ofNat_of_lt' hnpb] at h; exact Sim.withRunC h) ?_
  rintro r2 cvs m2 a2 ⟨⟨hC2, hg2, hcvs, hA2⟩, hr2⟩
  obtain ⟨c2, cvsP, ⟨h2, hw2⟩, -⟩ := ConRon.Bridge.Inductives.checkBlockTeles_specF fe rfl
    (ConRon.Bridge.CoreSpec.of_core rfl) henv bs.nP rest restP a1 a2 cvs hC1.check
    ⟨ConRon.Bridge.Inductives.dMember_ext.list c1.ext _ _ hrestP, hfe1⟩ hr2
  have hS2 := hC2.stage
  -- the agreements
  have hsd' : decI (r1.tail.headD 0) = s0 := hsd
  rw [← hsd']
  rw [← hsd'] at h1b
  refine Sim.bindK (K := ibiW.k_check_block_agree p n vis pp isRec (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0))
    (body := fun _ m3 => ibiW.k_block_shape_with_sort p n vis isRec (r1.headD 0) (r2.headD 0) (r2.tail.headD 0) (callW p n "block_shape_with_sort"
      [pp, r1.tail.headD 0] m3)) rfl (fun _ _ => rfl)
    (by
      have h := Sim.callW_posB (N := 2 ^ 62) (fun k hk => installSimCall
        (Q := fun _ _ m' a' => StageC dn vis fe env m' a' ∧ IWGrow m2 m' ∧ AbsOK m')
        (checkBlockAgree_refinesC hq henv hOpf hLC hP.agreeP (k + 1) hk ⟨m2, Locals.init []⟩ a2
          (UInt64.ofNat bs.nP) (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) cvTa0 cvs hC2
          hA2 (hc0.grow (OMono.decCVp _) hg2) hs32 hcvs (ConRon.Bridge.denoteCV_ext h1a c2.ext) hw1
          (ConRon.Bridge.denoteL_ext h1b c2.ext) h2 hw2)
        fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩) n hn
      rw [UInt64.toNat_ofNat_of_lt' hnpb] at h
      exact Sim.withRunC h) ?_
  rintro _ _ m3 a3 ⟨⟨hC3, hg3, hA3⟩, hr3⟩
  obtain ⟨c3, -⟩ := ConRon.Bridge.Inductives.checkBlockAgree_specF fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv bs.nP cvTa0 cvTa₀P (decI (r1.tail.headD 0)) s0P hw1 cvs cvsP hw2 a2 a3 _ hC2.check
    ⟨ConRon.Bridge.denoteCV_ext h1a c2.ext, ConRon.Bridge.denoteL_ext h1b c2.ext, h2⟩ hr3
  have hS3 := hC3.stage
  have hg03 := (hg1.trans hg2).trans hg3
  have c13 := c1.trans (c2.trans c3)
  -- the shape with its sort
  refine Sim.bindK (K := ibiW.k_block_shape_with_sort p n vis isRec (r1.headD 0) (r2.headD 0) (r2.tail.headD 0))
    (body := fun r4 m4 => ibiW.k_check_block_inds_cv_tas p n vis isRec (r4.headD 0) (callW p n "check_block_inds_cv_tas"
      [r1.headD 0, r2.headD 0, r2.tail.headD 0] m4)) rfl (fun _ _ => rfl)
    (Sim.withRunC (Sim.withFr (installWithSortSimC hq.closed hLC hP.alloc hP.pinWord hP.withSort n hC3 hA3
      (hqd.grow (decBS_mono _) hg03) (partsHsrc_grow hg03 hq9 hsrc) hs32
      (ConRon.Bridge.denoteL_ext h1b (c2.ext.trans c3.ext)))
      (fun _ _ e => hk _ (by simp [indsKeepCalleesC]) _ _ _ _ _ e hA3))) ?_
  rintro r4 p1 m4 a4 ⟨⟨⟨hS4, hg4, hp1, hsrc4, hrb4⟩, hA4⟩, hr4⟩
  obtain ⟨c4, hp1P⟩ := ConRon.Bridge.Inductives.BlockShape.withSort_spec fe bs bsP
    (decI (r1.tail.headD 0)) s0P a3 a4 p1 hC3.check
    ⟨ConRon.Bridge.Inductives.dShape_ext c13.ext _ _ hbsP,
      ConRon.Bridge.denoteL_ext h1b (c2.ext.trans c3.ext)⟩ hr4
  have c14 := c13.trans c4
  have hSortDn : SortDn dn s0P :=
    sortDn_of_member hm0 hC.mem.dnN (hlpsDn ms0 (by rw [hmeq]; exact List.mem_cons_self ..)) hfk1
  have hC4 : StageC dn vis fe env m4 a4 := hC3.of_check hS4 hA4 c4.ok c4.ext
  -- the formers' constants
  refine Sim.mstep (K := ibiW.k_check_block_inds_cv_tas p n vis isRec (r4.headD 0)) rfl (fun _ _ => rfl) fun r5 m5 h5 => ?_
  obtain ⟨hS5, hg5, hcvT⟩ := installCvTasRun hP.toCstProg hP.cvTas hP.cvTasGo h5 hS4
    ((hc0.grow (OMono.decCVp _) ((hg2.trans hg3).trans hg4)))
    (hcvs.grow decTele_mono (hg3.trans hg4))
  have hA5 := hk _ (by simp [indsKeepCalleesC]) _ _ _ _ _ h5 hA4
  -- the formers consed
  have hp1' := hp1.grow (decBS_mono _) hg5
  obtain ⟨-, hp9, -⟩ := partsShapeFacts hp1 hsrc4
  have hsrc5 := partsHsrc_grow hg5 hp9 hsrc4
  have hx24 := c3.ext.trans c4.ext
  have hcvTas : (cvTa0 :: cvs.map (·.1)).mapM (Frontend.denoteCV a4.store) =
      some (cvTa₀P :: cvsP.map (·.1)) := by
    refine ConRon.Bridge.Inductives.mapM_option_cons
      (ConRon.Bridge.denoteCV_ext h1a (c2.ext.trans hx24)) ?_
    have h2' := ConRon.Bridge.Inductives.BI.dCvL_ext.list hx24 _ _ h2
    clear h2 hw2 hcvs
    generalize cvs = xs at h2'
    generalize cvsP = ys at h2'
    induction xs generalizing ys with
    | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h2'
      subst h2'; rfl
    | cons x xs ih =>
      obtain ⟨y, ys', rfl, hy, hys⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv h2'
      exact ConRon.Bridge.Inductives.mapM_option_cons (ConRon.Bridge.Inductives.BI.dCvL_inv hy).1
        (ih ys' hys)
  refine Sim.bindK (K := ibiW.k_cons_block_inds p (r4.headD 0) (r5.headD 0) (r5.tail.headD 0)) (body := fun r6 m6 =>
      some ([r6.headD 0, r5.headD 0, r5.tail.headD 0, r4.headD 0], m6)) rfl (fun _ _ => rfl)
    (Sim.withRunC (Sim.callW_pos (fun k => installSimCall
      (Q := fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m5 m')
      (consBlockInds_refinesR p hP.toConsIndsProg hLz (k + 1) ⟨m5, Locals.init []⟩ a4 dn vis fe (r4.headD 0) isRec
        (r5.headD 0) (r5.tail.headD 0) 0 p1 b _ hb hS5 hC4.lzFacts.1 (LzFacts.of_stageC hC4 hp1P hSortDn) hp1' hsrc5
        hcvT (by have := (r5.tail.headD 0).toNat_lt; simp only [UInt64.toNat_zero, Nat.zero_add]; exact this))
      fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩) n |>.withFr
      (fun _ _ e => hk _ (by simp [indsKeepCalleesC]) _ _ _ _ _ e hA5))) ?_
  rintro r6 fe1 m6 a6 ⟨⟨⟨hS6, hg6⟩, hA6⟩, hr6⟩
  obtain ⟨c5, -⟩ := ConRon.Bridge.Inductives.consBlockInds_spec fe p1 _ b _ _ 0 fe env hcoh a4 a6 fe1
    hC4.check ⟨hp1P, hcvTas, ConRon.Bridge.denoteFEnv_mono c14.ext hfe⟩ hr6
  obtain ⟨-, hp9', -⟩ := partsShapeFacts hp1' hsrc5
  refine Sim.ret ⟨⟨hS6, (((((hg1.trans hg2).trans hg3).trans hg4).trans hg5).trans hg6),
    hcvT.grow (fun q => OMono.decCVp q) hg6,
    hp1'.grow (decBS_mono _) hg6, partsHsrc_grow hg6 hp9' hsrc5⟩, hA6, fun hrb =>
    ((hrb4 ((hrb.grow (hg1.trans hg2) (by omega)).grow hg3 (by have := hg1.trans hg2; have := this.1; omega))).grow
      (hg5.trans hg6) (by omega)), c14.trans c5⟩

include hq henv hV hOpf hLC hApd hCrk hLz in
/-- **`check_block_inds` refines `checkBlockInds`** under `StageC` (stage 1; the shape's and the
environment's denotations as con-ron's `checkBlockInds_spec` asks): the environment with the
formers pushed at the returned view, the formers' constants and the shape with its sort below the
tops; the frame at the entry index a `CoreStep`. -/
@[refines ConRon.Arena.checkBlockInds]
theorem checkBlockInds_refinesC (hP : IndsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (pp isRec : Word) (bs : BlockShape)
    (b : Bool) (hC : StageC dn vis fe env s₀.mem a₀) (hqd : DecB (fun m => decBS m pp.toNat) s₀.mem bs)
    (hsrc : ShapeSrc s₀.mem pp) (hcx : ShapeCV s₀.mem pp) (hb : (isRec != 0) = b) (hA : AbsOK s₀.mem)
    (hk : ∀ f ∈ indsKeepCalleesC, AbsKeep p f) {bsP : ConLeche.BlockShape}
    (hbsP : ConRon.Bridge.Inductives.dShape a₀.store bs = some bsP)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) (hcoh : ConRon.Bridge.IFEnvCoh fe)
    (hlpsDn : ∀ ms ∈ bs.members, ∀ k ∈ ms.cvT.levelParams, (dn k).isSome) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_inds" [vis, pp, isRec]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockInds V fe ⟨bs⟩ b) a₀ ∧
      IndsOut dn s₀.mem r (AM.res (ConRon.Arena.checkBlockInds V fe ⟨bs⟩ b) a₀) s'.mem
        (AM.st (ConRon.Arena.checkBlockInds V fe ⟨bs⟩ b) a₀) ∧ AbsOK s'.mem ∧
      (RecsB s₀.mem pp → RecsB s'.mem (r.tail.tail.tail.headD 0)) ∧
      ConRon.Bridge.CoreStep V env fe a₀ (AM.st (ConRon.Arena.checkBlockInds V fe ⟨bs⟩ b) a₀); ⊤⦄ :=
  triple_post (ibi_spec p hP.inds (n + 1) s₀ vis pp isRec) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ, hA', hR', hc⟩ :=
      Sim.run (ibiW_simC hq henv hV hOpf hLC hApd hCrk hLz hP n hn hC hqd hsrc hcx hb hA hk hbsP hfe hcoh hlpsDn) hm
    ⟨hl, hok, hQ, hA', hR', hc⟩

end sims

end L.Ind
