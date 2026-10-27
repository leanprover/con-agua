import ConAgua.Verdict.IndBTmf
import ConAgua.Arena.IndT.RecGen19
import ConAgua.Verdict.IndBPins
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# Error refinement of `class_majors` (lane `verdicts-b`, helper `ib`)

Mirrors `clmW_simC` (`IndT/RecGen19`), by induction on the fuel: `intern_const`, `mk_app_n_f` and
`sl_cons` are `closedNV`; `target_major_of` is `tmf_claim`, `target_major_pins`
`targetMajorPins_claim`, the recursive call the induction hypothesis.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model clmE_spec (p : Prog) (hf : p.lookup "class_majors" = some classMajorsL)
  fns [hf ↦ clmE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog} (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p) (henv : ConLeche.EnvWF env)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hq hIlpf hLC henv hnv hcE in
/-- **`class_majors`' model error claim** (`clmW_simC`'s hypotheses). -/
theorem clmE_claim (hP : ClmProg p) (pp cao cal pfo pfl : Word) (bs : BlockShape)
    (css : List (List (IConstantVal × Nat))) (pfvs : List EIdx) (pP : ConLeche.BlockShape)
    (cssP : List (List (ConLeche.ConstantVal × Nat))) (pfvsP : List ConLeche.Expr)
    (hpw : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped pP.nP x) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (ko kl : Word) (ks : List ClassKey) (ksP : List ConLeche.ClassKey),
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decBS m pp.toNat) m bs → ShapeSrc m pp →
    PSlR decCNS css cao cal m → DecB (fun m => decHL m pfo.toNat pfl.toNat) m pfvs →
    pfo.toNat + pfl.toNat ≤ iwTop m → PSlR decCK ks ko kl m → PosMR m →
    (∀ key ∈ ksP, ∀ x ∈ key.ds, ∃ D, ConLeche.Expr.WScoped D x) →
    ConRon.Bridge.Inductives.dShape a.store bs = some pP →
    css.mapM (ConRon.Bridge.Inductives.dCtors a.store) = some cssP →
    Frontend.denoteEList a.store pfvs = some pfvsP →
    ks.mapM (ConRon.Bridge.Inductives.dClassKey a.store) = some ksP →
    ∀ e, clmE p n m vis pp cao cal pfo pfl ko kl = .error e →
      ErrClaim (ConRon.Arena.classMajors V fe bs css pfvs ks) a e := by
  induction n with
  | zero =>
    intro m a ko kl ks ksP _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he
    rw [clmE.eq_1] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a ko kl ks ksP hC hA hq' hsrc hcss hpf hpfb hks hPm hsc hsh hcas hpfP hksP e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  by_cases hkl : kl = 0
  · rw [clmE.arm1 p n m vis pp cao cal pfo pfl ko kl hkl] at he
    cases he
  rw [clmE.arm2 p n m vis pp cao cal pfo pfl ko kl hkl] at he
  obtain ⟨q, k0, ks', rfl, hw, hqb, hdk, hks'⟩ := partsPSl_cons hks hkl
  have hq'' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  rw [hw] at he
  rw [← hq''] at hdk
  obtain ⟨nk, hnk, rfl⟩ := decCK_decB_nk hdk
  obtain ⟨hcH, hcd, huH, hud, hds, hdsb, hk4⟩ := pos2_nk_fields hnk hT
  obtain ⟨keyP, ksP', rfl, hkey, hksP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hksP
  simp only [ConRon.Bridge.Inductives.dClassKey, ckOfNk, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hkey
  obtain ⟨ind, hind, lvls, hlvls, dsP, hdsP, rfl⟩ := hkey
  obtain ⟨-, -, hnP, -, -, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hsh
  simp only [ConRon.Arena.classMajors, ckOfNk]
  -- the head
  cases h1 : callE p n "intern_const" [rdW (m.arr64 IW) (UInt64.ofNat q), rdW (m.arr64 IW) (UInt64.ofNat q + 1)] m with
  | error e1 =>
    rw [h1, clmE.k_intern_const.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internConst_spec p hP.tmp.cf hP.tmp.cp hP.tmp.ic n _ _ _) (callW_of_callE h1)
  obtain ⟨a', hrun, hS1, hg1⟩ := internConst_stage hS _ _ hcH huH hW1
  rw [hcd, hud] at hrun
  obtain ⟨p1, hhd⟩ := ConRon.Bridge.Inductives.internConstE_run hC.check.state hind hlvls hrun
  have hA1 := ceinternW_afr hW1 hA
  have hC1 : StageC dn vis fe env s1.mem a' := hC.of_pstep hS1 hA1 p1
  have hP1 : PosMR s1.mem := hPm.fr (ceinternW_mfr hW1)
  refine ErrClaim.bind_right hrun ?_
  subst hs1
  by_cases hb : 4294967296 ≤ r1.headD 0
  · rw [h1, clmE.k_intern_const.abort1 p n vis pp cao cal pfo pfl ko kl _ r1 _ hb] at he
    cases he
    exact absurd (by decide) hk0
  rw [h1, clmE.k_intern_const.arm1 p n vis pp cao cal pfo pfl ko kl _ r1 _ hb] at he
  have hr1H : H (r1.headD 0) := lt_of_notbig hb
  have hkq : (UInt64.ofNat q : Word).toNat + 4 ≤ iwTop m := hk4
  have e2 : rdW (s1.mem.arr64 IW) (UInt64.ofNat q + 2) = rdW (m.arr64 IW) (UInt64.ofNat q + 2) := by
    have e : (UInt64.ofNat q + 2 : Word).toNat = (UInt64.ofNat q : Word).toNat + 2 :=
      word_add_toNat (by rw [show (2 : Word).toNat = 2 from rfl]; omega)
    simp only [rdW, e]; rw [hg1.2.2.1 _ (by omega)]
  have e3 : rdW (s1.mem.arr64 IW) (UInt64.ofNat q + 3) = rdW (m.arr64 IW) (UInt64.ofNat q + 3) := by
    have e : (UInt64.ofNat q + 3 : Word).toNat = (UInt64.ofNat q : Word).toNat + 3 :=
      word_add_toNat (by rw [show (3 : Word).toNat = 3 from rfl]; omega)
    simp only [rdW, e]; rw [hg1.2.2.1 _ (by omega)]
  rw [e2, e3] at he
  have hds1 : decHL s1.mem (rdW (m.arr64 IW) (UInt64.ofNat q + 2)).toNat
      (rdW (m.arr64 IW) (UInt64.ofNat q + 3)).toNat = some nk.ds := by
    rw [decHL_agree (RdS.of_grow hg1) hdsb]; exact hds
  -- the application
  cases h2 : callE p n "mk_app_n_f" [r1.headD 0, rdW (m.arr64 IW) (UInt64.ofNat q + 2),
      rdW (m.arr64 IW) (UInt64.ofNat q + 3)] s1.mem with
  | error e2' =>
    rw [h2, clmE.k_mk_app_n_f.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, hs2'⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (mknF_spec p hP.tmp.ad n _ [r1.headD 0, _, _]) (callW_of_callE h2)
  obtain ⟨x, a2, hrun2, hS2, hg2, hx⟩ :=
    mknF_ok dn vis fe _ _ _ hr1H nk.ds s1.mem s2.mem a' r2 hs2' ⟨hC1.stage, hds1⟩
  have hrun' : ConRon.Arena.mkAppN (decE (r1.headD 0)) nk.ds a' = .ok (x, a2) := hrun2
  obtain ⟨p2, hmty⟩ := ConRon.Bridge.Inductives.mkAppN_run nk.ds dsP p1.ok hhd
    (ConRon.Bridge.denoteEList_ext p1.ext _ _ hdsP) hrun'
  have hA2 := mknF_afr hs2' hA1
  have hC2 := hC1.of_pstep hS2 hA2 p2
  have hP2 := hP1.fr (MFr.ofMknF hs2')
  obtain ⟨hmH, hmd⟩ := hx
  refine ErrClaim.bind_right hrun' ?_
  subst hs2
  subst hmd
  rw [h2, clmE.k_mk_app_n_f.arm1] at he
  have hg02 := hg1.trans hg2
  have c12 := (p1.trans p2).toCore hC.check
  have hshP2 := ConRon.Bridge.Inductives.dShape_ext c12.ext _ _ hsh
  -- the major
  cases h3 : callE p n "target_major_of" [vis, pp, cao, cal, pfo, pfl, pfo, pfl, r2.headD 0] s2.mem with
  | error e3 =>
    rw [h3, clmE.k_target_major_of.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    exact CoreSpecE.of_callE (tmf_claim hP.tmf hIlpf hq.closed hLC hnv n (s₀ := ⟨s2.mem, Locals.init []⟩)
      hC2.stage (hq'.grow (decBS_mono _) hg02) (partsHsrc_grow hg02 (partsShapeFacts hq' hsrc).2.1 hsrc)
      (hcss.grow decCNS_mono hg02) (hpf.grow (OMono.decHL _ _) hg02) (hpf.grow (OMono.decHL _ _) hg02)
      (Nat.le_trans hpfb hg02.1) hmH hP2 hC2 hA2 hshP2 hmty) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    cases n with
    | zero =>
      obtain ⟨e', he', hc'⟩ := callE_zero p "target_major_of" [vis, pp, cao, cal, pfo, pfl, pfo, pfl, r2.headD 0] s2.mem
      rw [h3] at he'; cases he'
    | succ k => exact ⟨k, rfl⟩
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (tmf_spec p hP.tmf.tmf k _ vis pp cao cal pfo pfl pfo pfl (r2.headD 0)) (callW_of_callE h3)
  obtain ⟨x3, a3', hrun3, hd3, hS3, hg3, hP3, hA3⟩ := tmfW_simC hP.tmf hIlpf hq.closed hLC k hC2.stage
    (hq'.grow (decBS_mono _) hg02) (partsHsrc_grow hg02 (partsShapeFacts hq' hsrc).2.1 hsrc)
    (hcss.grow decCNS_mono hg02) (hpf.grow (OMono.decHL _ _) hg02) (hpf.grow (OMono.decHL _ _) hg02)
    (Nat.le_trans hpfb hg02.1) hmH hP2 hC2 hA2 hshP2 hmty r3 s3.mem hW3
  obtain ⟨c3, MP, hm, hF1⟩ := ConRon.Bridge.Inductives.targetMajorOf_spec fe bs pP css cssP pfvs pfvs
    pfvsP pfvsP _ _ a2 _ _ hC2.check
    ⟨hshP2, ConRon.Bridge.Inductives.dCtors_ext.list c12.ext _ _ hcas,
      ConRon.Bridge.denoteEList_ext c12.ext _ _ hpfP, ConRon.Bridge.denoteEList_ext c12.ext _ _ hpfP,
      hmty⟩ hrun3
  obtain ⟨hMpf, hMmem, hMout⟩ := ConRon.Bridge.Inductives.classMajorOf_shape hF1
  have hdsW : ∀ x ∈ MP.ds, ConLeche.Expr.WScoped pP.nP x := by
    intro x hx
    cases hmm : MP.member with
    | some t =>
      rw [hMmem t hmm] at hx
      exact hpw x (List.mem_of_mem_take hx)
    | none =>
      obtain ⟨hxa, -, hfb⟩ := (hMout hmm).2 x hx
      rw [ConLeche.Expr.getAppArgs_mkAppN] at hxa
      simp only [ConLeche.Expr.getAppArgs, List.nil_append] at hxa
      obtain ⟨D, hD⟩ := hsc _ List.mem_cons_self x hxa
      exact ConLeche.WScoped.of_fvarsBelow hD (ConLeche.Expr.fvarB_le hfb)
  have hC3 := hC2.of_cstep hS3 hA3 c3
  subst hs3
  refine ErrClaim.bind_right hrun3 ?_
  have hg03 := hg02.trans hg3
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords hg03 hq' (partsShapeFacts hq' hsrc).2.1
  rw [h3, clmE.k_target_major_of.arm1] at he
  have hrB : (rdW (s3.mem.arr64 IW) (pp + 4)).toNat = bs.nP := by
    rw [hnpw, UInt64.toNat_ofNat_of_lt' hnpb]
  have hrP : (rdW (s3.mem.arr64 IW) (pp + 4)).toNat = pP.nP := hrB.trans hnP
  -- the pins
  cases h4 : callE p (k + 1) "target_major_pins" [vis, rdW (s3.mem.arr64 IW) (pp + 4), r3.headD 0] s3.mem with
  | error e4 =>
    rw [h4, clmE.k_target_major_pins.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    have := CoreSpecE.of_callE (targetMajorPins_claim hq henv hnv hcE hP.tmp (k + 1) (by omega)
      ⟨s3.mem, Locals.init []⟩ a3' (rdW (s3.mem.arr64 IW) (pp + 4)) (r3.headD 0) x3 hC3 hA3 hd3 hm
      (fun _ => by rw [hrP]; exact hdsW)) h4
    rw [hrB] at this
    exact this
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (targetMajorPins_spec p hP.tmp (realCall p) (realCall_spec p) (k + 1) _ vis _ _) (callW_of_callE h4)
  obtain ⟨a4, hrun4, hC4, hg4, hA4⟩ := tmpW_okC hq henv
    (by omega) hW4 hC3 hA3 hd3 hm (fun _ => by rw [hrP]; exact hdsW)
  have hrun4' := hrun4
  rw [hrP] at hrun4'
  obtain ⟨c4, -⟩ := ConRon.Bridge.Inductives.targetMajorPins_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv pP.nP _ MP (fun _ => hdsW) a3' a4 () hC3.check hm hrun4'
  rw [hrB] at hrun4
  refine ErrClaim.bind_right hrun4 ?_
  have hP4 : PosMR s4.mem := hP3.fr (tmpW_mfrR hq hW4)
  subst hs4
  have hg04 := hg03.trans hg4
  have c14 := (c12.trans c3).trans c4
  rw [h4, clmE.k_target_major_pins.arm1] at he
  -- the rest
  cases h5 : clmE p (k + 1) s4.mem vis pp cao cal pfo pfl (ko + 1) (kl - 1) with
  | error e5 =>
    rw [h5, clmE.k_class_majors.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    exact ih (by omega) s4.mem a4 (ko + 1) (kl - 1) ks' ksP' hC4 hA4 (hq'.grow (decBS_mono _) hg04)
      (partsHsrc_grow hg04 (partsShapeFacts hq' hsrc).2.1 hsrc) (hcss.grow decCNS_mono hg04)
      (hpf.grow (OMono.decHL _ _) hg04) (Nat.le_trans hpfb hg04.1) (hks'.grow decCK_mono hg04) hP4
      (fun k hk' => hsc k (List.mem_cons_of_mem _ hk'))
      (ConRon.Bridge.Inductives.dShape_ext c14.ext _ _ hsh)
      (ConRon.Bridge.Inductives.dCtors_ext.list c14.ext _ _ hcas)
      (ConRon.Bridge.denoteEList_ext c14.ext _ _ hpfP)
      (ConRon.Bridge.Inductives.dClassKey_ext.list c14.ext _ _ hksP') e h5
  | ok q5 =>
    obtain ⟨r5, m5⟩ := q5
    rw [h5, clmE.k_class_majors.arm1] at he
    cases h6 : callE p (k + 1) "sl_cons" [r3.headD 0, r5.headD 0, r5.tail.headD 0] m5 with
    | error e6 =>
      rw [h6, clmE.k_sl_cons.none] at he
      cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h6
    | ok q6 =>
      rw [h6, clmE.k_sl_cons.arm1] at he
      cases he

include hq hIlpf hLC henv hnv hcE in
/-- **`class_majors`' error claim** (every fuel up to `2 ^ 62`). -/
theorem classMajors_claim (hP : ClmProg p) (N : Nat) (hn : N ≤ 2 ^ 62) (s₀ : St) (a : AState)
    (pp cao cal pfo pfl ko kl : Word) (bs : BlockShape) (css : List (List (IConstantVal × Nat)))
    (pfvs : List EIdx) (ks : List ClassKey) (hC : StageC dn vis fe env s₀.mem a) (hA : AbsOK s₀.mem)
    (hq' : DecB (fun m => decBS m pp.toNat) s₀.mem bs) (hsrc : ShapeSrc s₀.mem pp)
    (hcss : PSlR decCNS css cao cal s₀.mem)
    (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) s₀.mem pfvs)
    (hpfb : pfo.toNat + pfl.toNat ≤ iwTop s₀.mem) (hks : PSlR decCK ks ko kl s₀.mem)
    (hPm : PosMR s₀.mem) {pP : ConLeche.BlockShape} {cssP : List (List (ConLeche.ConstantVal × Nat))}
    {pfvsP : List ConLeche.Expr} {ksP : List ConLeche.ClassKey}
    (hpw : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped pP.nP x)
    (hsc : ∀ key ∈ ksP, ∀ x ∈ key.ds, ∃ D, ConLeche.Expr.WScoped D x)
    (hsh : ConRon.Bridge.Inductives.dShape a.store bs = some pP)
    (hcas : css.mapM (ConRon.Bridge.Inductives.dCtors a.store) = some cssP)
    (hpfP : Frontend.denoteEList a.store pfvs = some pfvsP)
    (hksP : ks.mapM (ConRon.Bridge.Inductives.dClassKey a.store) = some ksP) :
    CoreSpecE p N "class_majors" [vis, pp, cao, cal, pfo, pfl, ko, kl]
      (ConRon.Arena.classMajors V fe bs css pfvs ks) s₀ a :=
  CoreSpecE.of_runs fun e hc => by
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    exact clmE_claim hq hIlpf hLC henv hnv hcE hP pp cao cal pfo pfl bs css pfvs pP cssP pfvsP hpw N hn
      s₀.mem a ko kl ks ksP hC hA hq' hsrc hcss hpf hpfb hks hPm hsc hsh hcas hpfP hksP e
      (triple_of_callE_err (clmE_spec p hP.cm N s₀ vis pp cao cal pfo pfl ko kl) hc (Err.code_ne_of_cls hk0))

end sims

end L.Ind
