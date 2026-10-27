import ConAgua.Arena.IndT.RecGenTmf
import ConAgua.Arena.IndT.RecCheckPins
import ConAgua.Arena.RecGenSpec.Clm
import ConAgua.Arena.RecGenSpec.CntW
import ConRon.Bridge.Inductives.GenRec
import ConAgua.Census.Attr

/-!
# `classMajors` under `StageC` (lane `indstaget`, helper `indstaget-tpt`)

`class_majors`' model at `realCall p` (its `target_major_pins` through `tmpW_okC`), from `StageC`,
`AbsOK` and the inputs' denotations con-ron's `classMajors_spec` asks, the twin side transcribed
from that spec's proof: the key's intern (`internConstE_run`), `mkAppN` (`mkAppN_run`),
`targetMajorOf` (`targetMajorOf_spec`, a `CoreStep`), `targetMajorPins` (`targetMajorPins_spec`).

`AbsOK` across `target_major_of` (`tmfW_afr`): the walk memos' frames of its model's callees
(`inst_lp_fast`, which writes the `instLP` memos 52‥54, through its stub's `stub_afr`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Frames of `target_major_pins` at `realCall p` -/

section mfr
variable {p : Prog} (hq : KnotStageProg p)

include hq in
theorem coreC_mfr {n : Nat} {args r : List Word} {m m' : Mem}
    (h : realCall p n "infer_type_core" args m = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (run_memFrame hq.closed (by decide) (run_of_callW h)).1 coreStageA_stage coreStageC_stage

include hq in
theorem tptW_mfrR : ∀ (n : Nat) (m m' : Mem) (vis d xo xl : Word) (r : List Word),
    tptW (realCall p) n m vis d xo xl = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, h => by simp [tptW] at h
  | n + 1, m, m', vis, d, xo, xl, r, h => by
    by_cases hl : xl = 0
    · rw [tptW_nil (realCall p) n m vis d xo xl hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    rw [tptW_cons (realCall p) n m vis d xo xl hl] at h
    obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp only [tptK])
    rw [tptK_some] at h
    refine (coreC_mfr hq h1).trans ?_
    obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl
    rw [tptK2_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact tptW_mfrR n _ _ _ _ _ _ _ h2

include hq in
theorem tmpW_mfrR {N : Nat} {m m' : Mem} {vis rP M : Word} {r : List Word}
    (h : tmpW (realCall p) N m vis rP M = some (r, m')) : MFr [] [] m m' := by
  rcases N with _ | N
  · simp [tmpW] at h
  by_cases hm : rdW (m.arr64 IW) (M + 8) ≠ 0
  · rw [tmpW_mem (realCall p) N m vis rP M hm] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
  rw [tmpW_out (realCall p) N m vis rP M hm] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl
  rw [tmpK1_some] at h
  refine (tptW_mfrR hq _ _ _ _ _ _ _ _ h1).trans ?_
  obtain ⟨⟨hd, m2⟩, h2, h⟩ := of_K h rfl
  rw [tmpK2_some] at h
  refine (ceinternW_mfr h2).trans ?_
  obtain ⟨hb, h⟩ := of_ite_none h
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h rfl
  rw [tmpK3_some] at h
  refine (MFr.ofMknF h3).trans ?_
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h rfl
  rw [tmpK4_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]; exact coreC_mfr hq h4

end mfr

/-! ## `class_majors` -/

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

/-- **`StageC` across a twin step con-ron calls a `CoreStep`**, the memory's half from `AbsOK`
after (`StageC.of_pstep` for a `CSpec`'s step). -/
theorem StageC.of_cstep {m m' : Mem} {a a' : AState} (h : StageC dn vis fe env m a)
    (hS : StageR dn vis fe m' a') (hA : AbsOK m') (hs : ConRon.Bridge.CoreStep V env fe a a') :
    StageC dn vis fe env m' a' :=
  ⟨hS, hs.ok,
    ⟨hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.1, ⟨hA.2.2.2.1, hA.1, hA.2.2.2.2.1⟩,
      fun k x e => hs.ext.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    hA.2.2.2.2.2.2.2.2⟩

theorem slConsC_afr {p : Prog} (hP : KeysProg p) {n : Nat} {x o l : Word} {r : List Word} {m m' : Mem}
    (h : callW p n "sl_cons" [x, o, l] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slCons_specW p hP.rx.ha hP.copy hP.cons n _ x o l) h
  exact consW_afr hW

variable {p : Prog} (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p) (henv : ConLeche.EnvWF env)

include hq hIlpf hLC henv in
/-- **`class_majors` under `StageC`** (twin side: con-ron's `classMajors_spec`'s proof). -/
theorem clmW_simC (hP : ClmProg p) (pp cao cal pfo pfl : Word) (bs : BlockShape)
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
    Sim (clmW p n m vis pp cao cal pfo pfl ko kl) (ConRon.Arena.classMajors V fe bs css pfvs ks) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        PSlR decTM x (r.headD 0) (r.tail.headD 0) m' ∧ PosMR m' ∧ AbsOK m') := by
  induction n with
  | zero => intro m a ko kl ks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rw [clmW.eq_1]; exact Sim.of_none
  | succ n ih =>
  intro m a ko kl ks ksP hC hA hq' hsrc hcss hpf hpfb hks hPm hsc hsh hcas hpfP hksP
  have hS := hC.stage
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  by_cases hkl : kl = 0
  · rw [clmW.arm1 p n m vis pp cao cal pfo pfl ko kl hkl]
    have : ks = [] := by
      have h := hks.1; simp only [DecB, hkl] at h
      simpa [decPL] using h.symm
    subst this
    exact Sim.ret ⟨hC, IWGrow.refl m, PSlR.nil decTM m, hPm, hA⟩
  obtain ⟨q, k0, ks', rfl, hw, hqb, hdk, hks'⟩ := partsPSl_cons hks hkl
  have hq'' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  rw [clmW.arm2 p n m vis pp cao cal pfo pfl ko kl hkl, hw]
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
  refine Sim.bindK (K := clmW.k_intern_const p n vis pp cao cal pfo pfl ko kl (UInt64.ofNat q))
    (by simp [clmW.k_intern_const]) (fun r m₁ => clmW.k_intern_const.eq_2 ..)
    (Q := fun r x m' a' => decE (r.headD 0) = x ∧ StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
      PosMR m' ∧ AbsOK m' ∧ PStep a a' ∧ denoteE a'.store x = some (.const ind lvls)) ?_ ?_
  · intro r1 m1 e1
    obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (internConst_spec p hP.tmp.cf hP.tmp.cp hP.tmp.ic n _ _ _) e1
    obtain ⟨a', hrun, hS1, hg1⟩ := internConst_stage hS _ _ hcH huH hW1
    rw [hcd, hud] at hrun
    obtain ⟨p1, hhd⟩ := ConRon.Bridge.Inductives.internConstE_run hC.check.state hind hlvls hrun
    have hA1 := ceinternW_afr hW1 hA
    exact ⟨_, a', hrun, rfl, hC.of_pstep hS1 hA1 p1, hg1, hPm.fr (ceinternW_mfr hW1), hA1, p1, hhd⟩
  rintro r1 hd m1 a1 ⟨rfl, hC1, hg1, hP1, hA1, p1, hhd⟩
  by_cases hb : 4294967296 ≤ r1.headD 0
  · rw [ite_eq_left hb]; exact Sim.of_none
  rw [ite_eq_right hb]
  have hr1H : H (r1.headD 0) := lt_of_notbig hb
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
  refine Sim.bindK (K := clmW.k_mk_app_n_f p n vis pp cao cal pfo pfl ko kl) (by simp [clmW.k_mk_app_n_f])
    (fun r m₁ => clmW.k_mk_app_n_f.arm1 ..)
    (Q := fun r x m' a' => decW0E m' r x ∧ StageC dn vis fe env m' a' ∧ IWGrow m1 m' ∧ PosMR m' ∧
      AbsOK m' ∧ PStep a1 a' ∧ denoteE a'.store x = some (ConLeche.Expr.mkAppN (.const ind lvls) dsP))
    ?_ ?_
  · intro r2 m2 e2
    obtain ⟨s2, rfl, -, hs2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (mknF_spec p hP.tmp.ad n _ [r1.headD 0, _, _]) e2
    obtain ⟨x, a', hrun, hS2, hg2, hx⟩ :=
      mknF_ok dn vis fe _ _ _ hr1H nk.ds m1 s2.mem a1 r2 hs2 ⟨hC1.stage, hds1⟩
    have hrun' : ConRon.Arena.mkAppN (decE (r1.headD 0)) nk.ds a1 = .ok (x, a') := hrun
    obtain ⟨p2, hmty⟩ := ConRon.Bridge.Inductives.mkAppN_run nk.ds dsP p1.ok hhd
      (ConRon.Bridge.denoteEList_ext p1.ext _ _ hdsP) hrun'
    have hA2 := mknF_afr hs2 hA1
    exact ⟨x, a', hrun, hx, hC1.of_pstep hS2 hA2 p2, hg2, hP1.fr (MFr.ofMknF hs2), hA2, p2, hmty⟩
  rintro r2 mty m2 a2 ⟨⟨hmH, hmd⟩, hC2, hg2, hP2, hA2, p2, hmty⟩
  have hg02 := hg1.trans hg2
  have c12 := (p1.trans p2).toCore hC.check
  -- the major
  refine Sim.bindK (K := clmW.k_target_major_of p n vis pp cao cal pfo pfl ko kl) (by simp [clmW.k_target_major_of])
    (fun r m₁ => clmW.k_target_major_of.arm1 ..)
    (Q := fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧
      StageC dn vis fe env m' a' ∧ IWGrow m2 m' ∧ PosMR m' ∧ AbsOK m' ∧
      ConRon.Bridge.CoreStep V env fe a2 a' ∧ ∃ MP, dMajor a'.store x = some MP ∧
        ∀ y ∈ MP.ds, ConLeche.Expr.WScoped pP.nP y) ?_ ?_
  · intro r3 m3 e3
    rcases n with _ | k
    · rw [callW_zero] at e3; cases e3
    obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (tmf_spec p hP.tmf.tmf k _ vis pp cao cal pfo pfl pfo pfl (r2.headD 0)) e3
    have hshP2 := ConRon.Bridge.Inductives.dShape_ext c12.ext _ _ hsh
    obtain ⟨x3, a3', hrun3, hd3, hS3, hg3, hP3, hA3⟩ := tmfW_simC hP.tmf hIlpf hq.closed hLC k hC2.stage
      (hq'.grow (decBS_mono _) hg02) (partsHsrc_grow hg02 (partsShapeFacts hq' hsrc).2.1 hsrc)
      (hcss.grow decCNS_mono hg02) (hpf.grow (OMono.decHL _ _) hg02) (hpf.grow (OMono.decHL _ _) hg02)
      (Nat.le_trans hpfb hg02.1) hmH hP2 hC2 hA2 hshP2 (by rw [hmd]; exact hmty) r3 s3.mem hW3
    rw [hmd] at hrun3
    obtain ⟨c3, MP, hm, hF1⟩ := ConRon.Bridge.Inductives.targetMajorOf_spec fe bs pP css cssP pfvs pfvs
      pfvsP pfvsP mty _ a2 _ _ hC2.check
      ⟨ConRon.Bridge.Inductives.dShape_ext c12.ext _ _ hsh,
        ConRon.Bridge.Inductives.dCtors_ext.list c12.ext _ _ hcas,
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
    exact ⟨_, _, hrun3, hd3, hC2.of_cstep hS3 hA3 c3, hg3, hP3, hA3, c3, MP, hm, hdsW⟩
  rintro r3 tm m3 a3 ⟨hd3, hC3, hg3, hP3, hA3, c3, MP, hm, hdsW⟩
  have hg03 := hg02.trans hg3
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords hg03 hq' (partsShapeFacts hq' hsrc).2.1
  -- the pins
  refine Sim.bindK (K := clmW.k_target_major_pins p n vis pp cao cal pfo pfl ko kl (r3.headD 0))
    (by simp [clmW.k_target_major_pins]) (fun r m₁ => clmW.k_target_major_pins.arm1 ..)
    (Q := fun _ _ m' a' => StageC dn vis fe env m' a' ∧ IWGrow m3 m' ∧ PosMR m' ∧ AbsOK m' ∧
      ConRon.Bridge.CoreStep V env fe a3 a') ?_ ?_
  · intro r4 m4 e4
    obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (targetMajorPins_spec p hP.tmp (realCall p) (realCall_spec p) n _ vis _ _) e4
    have hrB : (rdW (m3.arr64 IW) (pp + 4)).toNat = bs.nP := by
      rw [hnpw, UInt64.toNat_ofNat_of_lt' hnpb]
    have hrP : (rdW (m3.arr64 IW) (pp + 4)).toNat = pP.nP := hrB.trans hnP
    obtain ⟨a4, hrun4, hC4, hg4, hA4⟩ := tmpW_okC hq henv
      (by omega) hW4 hC3 hA3 hd3 hm (fun _ => by rw [hrP]; exact hdsW)
    have hrun4' := hrun4
    rw [hrP] at hrun4'
    obtain ⟨c4, -⟩ := ConRon.Bridge.Inductives.targetMajorPins_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
      henv pP.nP tm MP (fun _ => hdsW) a3 a4 () hC3.check hm hrun4'
    rw [hrB] at hrun4
    exact ⟨(), a4, hrun4, hC4, hg4, hP3.fr (tmpW_mfrR hq hW4), hA4, c4⟩
  rintro r4 - m4 a4 ⟨hC4, hg4, hP4, hA4, c4⟩
  have hg04 := hg03.trans hg4
  have c14 := (c12.trans c3).trans c4
  -- the rest
  refine Sim.bindK (K := clmW.k_class_majors p n (r3.headD 0)) (body := fun r5 m5 => clmW.k_sl_cons p (callW p n "sl_cons"
      [r3.headD 0, r5.headD 0, r5.tail.headD 0] m5)) rfl (fun _ _ => rfl)
    (ih (by omega) m4 a4 (ko + 1) (kl - 1) ks' ksP' hC4 hA4 (hq'.grow (decBS_mono _) hg04)
      (partsHsrc_grow hg04 (partsShapeFacts hq' hsrc).2.1 hsrc) (hcss.grow decCNS_mono hg04)
      (hpf.grow (OMono.decHL _ _) hg04) (Nat.le_trans hpfb hg04.1) (hks'.grow decCK_mono hg04) hP4
      (fun k hk' => hsc k (List.mem_cons_of_mem _ hk'))
      (ConRon.Bridge.Inductives.dShape_ext c14.ext _ _ hsh)
      (ConRon.Bridge.Inductives.dCtors_ext.list c14.ext _ _ hcas)
      (ConRon.Bridge.denoteEList_ext c14.ext _ _ hpfP)
      (ConRon.Bridge.Inductives.dClassKey_ext.list c14.ext _ _ hksP')) ?_
  rintro r5 xs m5 a5 ⟨hC5, hg5, hd5, hP5, hA5⟩
  refine Sim.mstep (K := clmW.k_sl_cons p) rfl (fun _ _ => rfl) fun r6 m6 h6 => ?_
  obtain ⟨hS6, hg6, hd6, hf6⟩ := clsCons hP.keys decTM_mono h6 hC5.stage hd5
    (hd3.grow (decTM_mono _) (hg4.trans hg5))
  have hA6 := slConsC_afr hP.keys h6 hA5
  exact Sim.ret ⟨hC5.of_pstep hS6 hA6 (PStep.refl hC5.check.state), (hg04.trans hg5).trans hg6,
    by simpa using hd6, hP5.fr hf6, hA6⟩

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
        (r.tail.headD 0) s'.mem ∧ PosMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (clm_spec p hP.cm n s₀ vis pp cao cal pfo pfl ko kl) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (clmW_simC hq hIlpf hLC henv hP pp cao cal pfo pfl bs css pfvs pP cssP pfvsP
      hpw n hn _ a₀ ko kl ks ksP hC hA hq' hsrc hcss hpf hpfb hks hPm hsc hsh hcas hpfP hksP) hm
    ⟨hl, hok, hQ⟩

end sims

end L.Ind
