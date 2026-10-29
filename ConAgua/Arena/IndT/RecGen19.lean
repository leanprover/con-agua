import ConAgua.Arena.IndT.RecGenTmf
import ConAgua.Arena.IndT.RecCheckPins
import ConAgua.Verdict.IndBClm
import ConAgua.Arena.RecGenSpec.CntW
import ConRon.Bridge.Inductives.GenRec

/-!
# `classMajors` under `StageC`, both outcomes (lane `indstaget`, helper `indstaget-tpt`)

`clm_ref`: `class_majors`' unified model `clmE` (its `target_major_of` through `tmf_ref`, its
`target_major_pins` through `tmp_ref`) refines `classMajors` from `StageC`, `AbsOK` and the inputs'
denotations con-ron's `classMajors_spec` asks, the twin side transcribed from that spec's proof: the
key's intern (`internConstE_run`), `mkAppN` (`mkAppN_run`), `targetMajorOf` (`targetMajorOf_spec`,
a `CoreStep`), `targetMajorPins` (`targetMajorPins_spec`). The `@[refines]` theorem is its ok half.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `class_majors` -/

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

/-- **`StageC` across a twin step con-ron calls a `CoreStep`**, the memory's half from `AbsOK`
after (`StageC.of_pstep` for a `CSpec`'s step). -/
theorem StageC.of_cstep {m m' : Mem} {a a' : AState} (h : StageC dn vis fe env m a)
    (hS : StageR dn vis fe m' a') (hA : AbsOK m') (hs : ConRon.Bridge.CoreStep V env fe a a') :
    StageC dn vis fe env m' a' :=
  ⟨hS, hs.ok,
    ⟨hA.wk.2.1, hA.wk.2.2.1, hA.wk.2.2.2.1, ⟨hA.il, hA.ab, hA.wk.1⟩,
      fun k x e => hs.ext.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    hA.wk.2.2.2.2⟩

theorem slConsC_afr {p : Prog} (hP : KeysProg p) {n : Nat} {x o l : Word} {r : List Word} {m m' : Mem}
    (h : callW p n "sl_cons" [x, o, l] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slCons_specW p hP.rx.ha hP.copy hP.cons n _ x o l) h
  exact consW_afr hW

variable {p : Prog} (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p) (henv : ConLeche.EnvWF env)

/-- What `class_majors` gives besides the twin's classes `xs` (from `m`): the stage, the growth, the
classes a slice of fresh `TargetMajor` records at the result words, `PosMR`, `AbsOK`. -/
structure ClmPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (r : List Word) (m' : Mem) (xs : List TargetMajor) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  dec : PSlR decTM xs (r.headD 0) (r.tail.headD 0) m'
  pos : PosMR m'
  abs : AbsOK m'

include hq hIlpf hLC henv in
/-- **`class_majors` refines `classMajors`, both outcomes** (twin side: con-ron's `classMajors_spec`'s
proof): `intern_const`, `mk_app_n_f` and `sl_cons` lifted (the cap on the head is an abort `0`),
`target_major_of` is `tmf_ref`, `target_major_pins` `tmp_ref`, the rest the induction hypothesis. -/
theorem clm_ref (hP : ClmProg p) (pp cao cal pfo pfl : Word) (bs : BlockShape)
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
    RefE (VerdictCtx p) (clmE p n m vis pp cao cal pfo pfl ko kl) (ConRon.Arena.classMajors V fe bs css pfvs ks) a
      (fun v xs a' => ClmPost dn vis fe env m v.1 v.2 xs a') := by
  induction n with
  | zero =>
    intro m a ko kl ks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [clmE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a ko kl ks ksP hC hA hq' hsrc hcss hpf hpfb hks hPm hsc hsh hcas hpfP hksP
  have hS := hC.stage
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  by_cases hkl : kl = 0
  · rw [clmE.arm1 p n m vis pp cao cal pfo pfl ko kl hkl]
    have : ks = [] := by
      have h := hks.1; simp only [DecB, hkl] at h
      simpa [decPL] using h.symm
    subst this
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, PSlR.nil decTM m, hPm, hA⟩
  obtain ⟨q, k0, ks', rfl, hw, hqb, hdk, hks'⟩ := partsPSl_cons hks hkl
  have hq'' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  rw [clmE.arm2 p n m vis pp cao cal pfo pfl ko kl hkl, hw]
  rw [← hq''] at hdk
  obtain ⟨nk, hnk, rfl⟩ := decCK_decB_nk hdk
  obtain ⟨hcH, hcd, huH, hud, hds, hdsb, hk4⟩ := pos2_nk_fields hnk hT
  -- the key's denotation (con-ron's proof)
  obtain ⟨keyP, ksP', rfl, hkey, hksP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hksP
  simp only [ConRon.Bridge.Inductives.dClassKey, ckOfNk, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hkey
  obtain ⟨ind, hind, lvls, hlvls, dsP, hdsP, rfl⟩ := hkey
  obtain ⟨-, -, hnP, -, -, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hsh
  simp only [ConRon.Arena.classMajors, ckOfNk]
  -- the head
  rcases h1 : ceinternW m (rdW (m.arr64 IW) (UInt64.ofNat q)) (rdW (m.arr64 IW) (UInt64.ofNat q + 1))
    with _ | ⟨⟨r1, m1⟩⟩
  · rw [liftE_none, clmE.k_intern_const.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨a1, hrun, hS1, hg1⟩ := internConst_stage hS _ _ hcH huH h1
  rw [hcd, hud] at hrun
  obtain ⟨p1, hhd⟩ := ConRon.Bridge.Inductives.internConstE_run hC.check.state hind hlvls hrun
  have hA1 := ceinternW_afr h1 hA
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
  have hP1 : PosMR m1 := hPm.fr (ceinternW_mfr h1)
  refine RefE.bind_right hrun ?_
  by_cases hb : 4294967296 ≤ r1
  · rw [clmE.k_intern_const.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ hb]; exact RefE.of_cls0 (by decide)
  rw [clmE.k_intern_const.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ hb]
  have hr1H : H r1 := lt_of_notbig hb
  have hkq : (UInt64.ofNat q : Word).toNat + 4 ≤ iwTop m := hk4
  have e2 : rdW (m1.arr64 IW) (UInt64.ofNat q + 2) = rdW (m.arr64 IW) (UInt64.ofNat q + 2) := by
    have e : (UInt64.ofNat q + 2 : Word).toNat = (UInt64.ofNat q : Word).toNat + 2 :=
      word_add_toNat (by rw [show (2 : Word).toNat = 2 from rfl]; omega)
    simp only [rdW, e]; rw [hg1.2.2.1 _ (by omega)]
  have e3 : rdW (m1.arr64 IW) (UInt64.ofNat q + 3) = rdW (m.arr64 IW) (UInt64.ofNat q + 3) := by
    have e : (UInt64.ofNat q + 3 : Word).toNat = (UInt64.ofNat q : Word).toNat + 3 :=
      word_add_toNat (by rw [show (3 : Word).toNat = 3 from rfl]; omega)
    simp only [rdW, e]; rw [hg1.2.2.1 _ (by omega)]
  rw [e2, e3]
  have hds1 : decHL m1 (rdW (m.arr64 IW) (UInt64.ofNat q + 2)).toNat
      (rdW (m.arr64 IW) (UInt64.ofNat q + 3)).toNat = some nk.ds := by
    rw [decHL_agree (RdS.of_grow hg1) hdsb]; exact hds
  -- the application
  rcases h2 : mknF m1 [r1, rdW (m.arr64 IW) (UInt64.ofNat q + 2), rdW (m.arr64 IW) (UInt64.ofNat q + 3)]
    with _ | ⟨⟨r2, m2⟩⟩
  · rw [liftE_none, clmE.k_mk_app_n_f.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, clmE.k_mk_app_n_f.arm1]
  obtain ⟨x, a2, hrun2, hS2, hg2, hmH, hmd⟩ :=
    mknF_ok dn vis fe _ _ _ hr1H nk.ds m1 m2 a1 r2 h2 ⟨hC1.stage, hds1⟩
  have hrun' : ConRon.Arena.mkAppN (decE r1) nk.ds a1 = .ok (x, a2) := hrun2
  obtain ⟨p2, hmty⟩ := ConRon.Bridge.Inductives.mkAppN_run nk.ds dsP p1.ok hhd
    (ConRon.Bridge.denoteEList_ext p1.ext _ _ hdsP) hrun'
  have hA2 := mknF_afr h2 hA1
  have hC2 := hC1.of_pstep hS2 hA2 p2
  have hP2 := hP1.fr (MFr.ofMknF h2)
  refine RefE.bind_right hrun' ?_
  subst hmd
  have hg02 := hg1.trans hg2
  have c12 := (p1.trans p2).toCore hC.check
  have hshP2 := ConRon.Bridge.Inductives.dShape_ext c12.ext _ _ hsh
  -- the major
  have hR3 := tmf_ref hP.tmf hIlpf hq.closed hLC n hC2.stage
    (hq'.grow (decBS_mono _) hg02) (partsHsrc_grow hg02 (partsShapeFacts hq' hsrc).2.1 hsrc)
    (hcss.grow decCNS_mono hg02) (hpf.grow (OMono.decHL _ _) hg02) (hpf.grow (OMono.decHL _ _) hg02)
    (Nat.le_trans hpfb hg02.1) hmH hP2 hC2 hA2 hshP2 hmty
  rcases h3 : tmfE p n m2 vis pp cao cal pfo pfl pfo pfl (r2.headD 0) with e3 | ⟨r3, m3⟩ <;> rw [h3] at hR3
  · rw [clmE.k_target_major_of.none]; exact RefE.bind_left fun hV => hR3 hV.nv
  rw [clmE.k_target_major_of.arm1]
  obtain ⟨tm, a3, hrun3, hR3⟩ := hR3
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
  have hC3 := hC2.of_cstep hR3.stage hR3.abs c3
  refine RefE.bind_right hrun3 ?_
  have hg03 := hg02.trans hR3.grow
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords hg03 hq' (partsShapeFacts hq' hsrc).2.1
  have hrB : (rdW (m3.arr64 IW) (pp + 4)).toNat = bs.nP := by
    rw [hnpw, UInt64.toNat_ofNat_of_lt' hnpb]
  have hrP : (rdW (m3.arr64 IW) (pp + 4)).toNat = pP.nP := hrB.trans hnP
  -- the pins
  have hR4 := tmp_ref hq henv n (by omega) hC3 hR3.abs hR3.dec hm (fun _ => by rw [hrP]; exact hdsW)
  rcases h4 : tmpE p n m3 vis (rdW (m3.arr64 IW) (pp + 4)) r3 with e4 | ⟨r4, m4⟩ <;> rw [h4] at hR4
  · rw [clmE.k_target_major_pins.none]; rw [hrB] at hR4; exact RefE.bind_left hR4
  rw [clmE.k_target_major_pins.arm1]
  obtain ⟨⟨⟩, a4, hrun4, hR4⟩ := hR4
  have hrun4' := hrun4
  rw [hrP] at hrun4'
  obtain ⟨c4, -⟩ := ConRon.Bridge.Inductives.targetMajorPins_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv pP.nP tm MP (fun _ => hdsW) a3 a4 () hC3.check hm hrun4'
  rw [hrB] at hrun4
  refine RefE.bind_right hrun4 ?_
  have hP4 : PosMR m4 := hR3.pos.fr hR4.mfr
  have hg04 := hg03.trans hR4.grow
  have c14 := (c12.trans c3).trans c4
  -- the rest
  have hR5 := ih (by omega) m4 a4 (ko + 1) (kl - 1) ks' ksP' hR4.stage hR4.abs (hq'.grow (decBS_mono _) hg04)
    (partsHsrc_grow hg04 (partsShapeFacts hq' hsrc).2.1 hsrc) (hcss.grow decCNS_mono hg04)
    (hpf.grow (OMono.decHL _ _) hg04) (Nat.le_trans hpfb hg04.1) (hks'.grow decCK_mono hg04) hP4
    (fun k hk' => hsc k (List.mem_cons_of_mem _ hk'))
    (ConRon.Bridge.Inductives.dShape_ext c14.ext _ _ hsh)
    (ConRon.Bridge.Inductives.dCtors_ext.list c14.ext _ _ hcas)
    (ConRon.Bridge.denoteEList_ext c14.ext _ _ hpfP)
    (ConRon.Bridge.Inductives.dClassKey_ext.list c14.ext _ _ hksP')
  rcases h5 : clmE p n m4 vis pp cao cal pfo pfl (ko + 1) (kl - 1) with e5 | ⟨r5, m5⟩ <;> rw [h5] at hR5
  · rw [clmE.k_class_majors.none]; exact RefE.bind_left hR5
  rw [clmE.k_class_majors.arm1]
  obtain ⟨xs, a5, hrun5, hR5⟩ := hR5
  refine RefE.bind_right hrun5 ?_
  rcases h6 : consW n m5 r3 (r5.headD 0) (r5.tail.headD 0) with _ | ⟨⟨r6, m6⟩⟩
  · rw [liftE_none, clmE.k_sl_cons.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, clmE.k_sl_cons.arm1]
  obtain ⟨hS6, hg6, hd6, hf6⟩ := clsConsW decTM_mono h6 hR5.stage.stage hR5.dec
    (hR3.dec.grow (decTM_mono _) (hR4.grow.trans hR5.grow))
  have hA6 := consW_afr h6 hR5.abs
  exact RefE.ret rfl ⟨hR5.stage.of_pstep hS6 hA6 (PStep.refl hR5.stage.check.state),
    (hg04.trans hR5.grow).trans hg6, by simpa using hd6, hR5.pos.fr hf6, hA6⟩

include hq hIlpf hLC henv in
/-- **`class_majors` refines `classMajors`** under `StageC` (the knot's core calls in
`target_major_pins`; the inputs' denotations as con-ron's `classMajors_spec` asks): the keys a slice
of `ClassKey` records decoded below the tops; the classes a slice of fresh `TargetMajor` records. -/
@[refines ConRon.Arena.classMajors]
theorem classMajors_refinesC (hP : ClmProg p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (pp cao cal pfo pfl ko kl : Word)
    (bs : BlockShape) (css : List (List (IConstantVal × Nat))) (pfvs : List EIdx)
    (ks : List ClassKey) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hq' : DecB (fun m => decBS m pp.toNat) s₀.mem bs) (hsrc : ShapeSrc s₀.mem pp)
    (hcss : PSlR decCNS css cao cal s₀.mem)
    (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) s₀.mem pfvs)
    (hpfb : pfo.toNat + pfl.toNat ≤ iwTop s₀.mem) (hks : PSlR decCK ks ko kl s₀.mem)
    (hPm : PosMR s₀.mem) {pP : ConLeche.BlockShape} {cssP : List (List (ConLeche.ConstantVal × Nat))}
    {pfvsP : List ConLeche.Expr} {ksP : List ConLeche.ClassKey}
    (hpw : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped pP.nP x)
    (hsc : ∀ key ∈ ksP, ∀ x ∈ key.ds, ∃ D, ConLeche.Expr.WScoped D x)
    (hsh : ConRon.Bridge.Inductives.dShape a₀.store bs = some pP)
    (hcas : css.mapM (ConRon.Bridge.Inductives.dCtors a₀.store) = some cssP)
    (hpfP : Frontend.denoteEList a₀.store pfvs = some pfvsP)
    (hksP : ks.mapM (ConRon.Bridge.Inductives.dClassKey a₀.store) = some ksP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_majors" [vis, pp, cao, cal, pfo, pfl, ko, kl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classMajors V fe bs css pfvs ks) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.classMajors V fe bs css pfvs ks) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      PSlR decTM (AM.res (ConRon.Arena.classMajors V fe bs css pfvs ks) a₀) (r.headD 0)
        (r.tail.headD 0) s'.mem ∧ PosMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (clmE_spec p hP n s₀ vis pp cao cal pfo pfl ko kl)
    (clm_ref hq hIlpf hLC henv hP pp cao cal pfo pfl bs css pfvs pP cssP pfvsP hpw n hn _ a₀ ko kl ks ksP
      hC hA hq' hsrc hcss hpf hpfb hks hPm hsc hsh hcas hpfP hksP)) ?_
  rintro r s' ⟨hl', c, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.dec, hR.pos, hR.abs⟩

end sims

end L.Ind
