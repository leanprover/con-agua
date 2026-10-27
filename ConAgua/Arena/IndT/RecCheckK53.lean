import ConAgua.Arena.IndT.RecCheckTmn
import ConAgua.Arena.IndT.RecGen19
import ConAgua.Arena.RecCheckSpec.Tka
import ConAgua.Arena.RecCheckSpec.TkhK2V2
import ConAgua.Census.Attr

/-!
# `targetK53` under `StageC` (lane `indstaget`, helper `pds`)

`target_k53`'s model at `realCall p`, from `StageC` and the inputs' denotations con-ron's
`targetK53_spec` asks; its twin side transcribed from that spec's proof: `stripPis`
(`stripPis_pstep`, read-only), the telescopes' annotations erased (`mapM_RE_P` of
`eraseFVarTys_spec`), the heads and arguments (`getAppFn_run`, `viewConst_run`, `getAppArgs_run`,
read-only), the arguments' check (`internConstE_run`, `mkAppN_run`; `nestOcc` read-only), then
`tcmF_okC`.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs dShape dCtors dCtorNf dMajor PSpecP REL)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Frames -/

theorem eftF_afr {n : Nat} {m m' : Mem} {e : Word} {r : List Word} (h : eftF n m e = some (r, m')) :
    AFr m m' := by
  obtain _ | n := n
  · simp [eftF] at h
  simp only [eftF, eftW] at h
  rcases ha : allocW m 1 with _ | ⟨f, m1⟩ <;> simp only [ha, eftK1, reduceCtorEq] at h
  rcases hr : rxW n (m1.set64 IW f 2) f e with _ | ⟨z, m2⟩ <;> simp only [hr, eftK2, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact ((allocW_afr ha).trans (set64IW_afr _ _ _)).trans (rxW_afr hr)

theorem eeW_afr : ∀ (n : Nat) {m m' : Mem} {o l : Word} {r : List Word}, eeW n m o l = some (r, m') →
    AFr m m'
  | 0, _, _, _, _, _, h => by simp [eeW] at h
  | n + 1, m, m', o, l, r, h => by
    by_cases hl : l = 0
    · rw [eeW_nil (h := hl)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      exact AFr.refl _
    rw [eeW_cons (h := hl)] at h
    rcases h1 : eftF n m (rdW (m.arr64 IW) o) with _ | ⟨rv, m1⟩ <;> simp only [h1, eeK0, reduceCtorEq] at h
    rcases h2 : eeW n m1 (o + 1) (l - 1) with _ | ⟨rr, m2⟩ <;> simp only [h2, eeK1, reduceCtorEq] at h
    rcases h3 : consW n m2 (rv.headD 0) (rr.headD 0) (rr.tail.headD 0) with _ | ⟨rc, m3⟩ <;> simp only [h3, eeK2, reduceCtorEq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact ((eftF_afr h1).trans (eeW_afr n h2)).trans (consW_afr h3)

theorem noF_afr {n : Nat} {m m' : Mem} {no nl lo hi e r : Word}
    (h : noF n m no nl lo hi e = some (r, m')) : AFr m m' := by
  cases n with
  | zero => simp [noF] at h
  | succ n => exact noConstWf_afr (n := n + 1) h

/-- The annotations of a denoted handle list erased: con-ron's `mapM_RE_P` of `eraseFVarTys_spec`. -/
theorem eraseAll_spec (xs : List EIdx) (xsP : List ConLeche.Expr) :
    PSpecP (fun st => True ∧ Frontend.denoteEList st xs = some xsP)
      (xs.mapM ConRon.Arena.eraseFVarTys) (REL (xsP.map ConLeche.Expr.eraseFVarTys)) :=
  ConRon.Bridge.Inductives.mapM_RE_P (fun _ => True) (fun _ h => h)
    (fun e eP => fun s₀ s' r hok hp hpre hrun =>
      ConRon.Bridge.Inductives.eraseFVarTys_spec e eP s₀ s' r hok hp hpre.2 hrun) xs xsP

theorem tteW_afr {n : Nat} {m m' : Mem} {bso bsl teo tel : Word} {r : List Word}
    (h : tteW n m bso bsl teo tel = some (r, m')) : AFr m m' := by
  obtain _ | n := n
  · simp [tteW] at h
  rw [tteW_succ] at h
  rcases h1 : eeW n m bso bsl with _ | ⟨r1, m1⟩ <;> simp only [h1, tteK1, reduceCtorEq] at h
  rcases h2 : eeW n m1 teo tel with _ | ⟨r2, m2⟩ <;> simp only [h2, tteK2, reduceCtorEq] at h
  rcases h3 : eqW n m2 (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) with _ | e <;> simp only [h3, tteK3, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (eeW_afr n h1).trans (eeW_afr n h2)

/-- The telescope check is a twin step con-ron calls a `CoreStep` (two `eraseAll_spec` runs). -/
theorem tkTele_cstep {fe : IFEnv} {env : ConLeche.Env} {teleW tele : List EIdx}
    {twP tP : List ConLeche.Expr} {s₀ s' : AState}
    {c : Bool} (hok : ConRon.Bridge.CheckOK V env fe s₀)
    (hw : Frontend.denoteEList s₀.store teleW = some twP)
    (ht : Frontend.denoteEList s₀.store tele = some tP)
    (hrun : (tkTele teleW tele).run s₀ = .ok (c, s')) : CoreStep V env fe s₀ s' := by
  have hrun' : (tkTele teleW tele) s₀ = .ok (c, s') := hrun
  simp only [tkTele] at hrun'
  obtain ⟨ew, s1, k1, z1⟩ := ConRon.Bridge.AM.bind_ok hrun'
  obtain ⟨q1, -⟩ := ConRon.Bridge.Inductives.RC.pspecP_core (eraseAll_spec teleW twP) hok
    ⟨trivial, hw⟩ k1
  obtain ⟨et, s2, k2, z2⟩ := ConRon.Bridge.AM.bind_ok z1
  obtain ⟨q2, -⟩ := ConRon.Bridge.Inductives.RC.pspecP_core (eraseAll_spec tele tP) q1.ok
    ⟨trivial, denoteEList_ext q1.ext _ _ ht⟩ k2
  obtain ⟨-, rfl⟩ := ConRon.Bridge.AM.pure_ok z2
  exact q1.trans q2

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`target_k53_args` under `StageC`** (twin side: con-ron's `targetK53_spec`, the arguments'
part). -/
theorem tkaW_okC (n : Nat) (hn : n ≤ 2 ^ 62) {m m' : Mem} {a : AState}
    {q fto ftl Mc ip usp lao lal mao mal : Word}
    {r : List Word} {bs : BlockShape} {formerTys : List EIdx} {TM : TargetMajor} {la ma : List EIdx}
    (h : tkaW (realCall p) n m vis q fto ftl Mc ip usp lao lal mao mal = some (r, m'))
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hMc : DecB (fun m => decTM m Mc.toNat) m TM)
    (hip : H ip) (hus : H usp) (hla : HSl0 m lao lal la) (hma : HSl0 m mao mal ma) (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP laP maP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
    {I'P : ConLeche.Name} {us'P : List ConLeche.Level}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hMcP : dMajor a.store TM = some McP)
    (hipP : denoteN a.store.ns (decI ip) = some I'P)
    (husP : denoteLs a.store.lss (decI usp) = some us'P)
    (hlaP : Frontend.denoteEList a.store la = some laP)
    (hmaP : Frontend.denoteEList a.store ma = some maP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    ∃ c a', (tkArgs fe bs formerTys TM (decI ip) (decI usp) la ma).run a = .ok (c, a') ∧
      (r.headD 0 != 0) = c ∧ StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ RcMR m' ∧ AbsOK m' := by
  have hS := hC.stage
  obtain ⟨-, hMlv, hMds, hMnpc, -, -, -, -, hMpf⟩ := ConRon.Bridge.Inductives.dMajor_inv hMcP
  obtain _ | n := n
  · simp [tkaW] at h
  rw [tkaW_succ] at h
  have hsz := hS.2.2.2.1
  obtain ⟨hlvH, hlvD, hdsS, hnP, hpfS, hMt⟩ := tmFields hMc hsz
  have hMk : ∀ k : Nat, k ≤ 12 → (Mc + UInt64.ofNat k).toNat < iwTop m := fun k hk => by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt (by
      have := (rdW (m.arr64 CTL) 200).toNat_lt; simp only [iwTop] at hMt; omega)]; omega
  generalize hK : rdW (m.arr64 IW) (Mc + 4) = K at h hnP
  rcases h1 : eeW n m (if lal < K then lao else lao + K) (if lal < K then 0 else lal - K) with _ | ⟨r1, m1⟩ <;> simp only [h1, tkaK1, reduceCtorEq] at h
  obtain ⟨le, a1, run1, hd1, hb1, hS1, hg1, hP1⟩ := eeW_ok dn fe vis n h1 hS hla.drop hP
  have hA1 := eeW_afr n h1 hA
  rcases h2 : eeW n m1 (if mal < K then mao else mao + K) (if mal < K then 0 else mal - K) with _ | ⟨r2, m2⟩ <;> simp only [h2, tkaK2, reduceCtorEq] at h
  obtain ⟨me, a2, run2, hd2, hb2, hS2, hg2, hP2⟩ := eeW_ok dn fe vis n h2 hS1 (hma.grow hg1).drop hP1
  have hA2 := eeW_afr n h2 hA1
  rcases h3 : eqW n m2 (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) with _ | e <;> rw [h3] at h <;>
    try (simp only [tkaK3, reduceCtorEq] at h; done)
  have he := eqW_dec h3 (by rw [decHL_grow hg2 hb1]; exact hd1) (hS2.lt64 (by have := hg2.1; omega)) hd2
    (hS2.lt64 hb2)
  have hg12 := hg1.trans hg2
  rw [hnP] at run1 run2
  obtain ⟨q1, -⟩ := eraseAll_spec (la.drop TM.nPc) (laP.drop TM.nPc) a a1 le hC.check.state
    hC.check.pins ⟨trivial, ConRon.Bridge.Inductives.denoteEList_drop hlaP TM.nPc⟩ run1
  have hC1 := hC.of_pstep hS1 hA1 q1
  obtain ⟨q2, -⟩ := eraseAll_spec (ma.drop TM.nPc) (maP.drop TM.nPc) a1 a2 me hC1.check.state
    hC1.check.pins ⟨trivial, ConRon.Bridge.Inductives.denoteEList_drop
      (denoteEList_ext q1.ext _ _ hmaP) TM.nPc⟩ run2
  have hC2 := hC1.of_pstep hS2 hA2 q2
  have q12 := q1.trans q2
  by_cases he0 : e = 0
  · rw [tkaK3_no (h := he0)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hne : le ≠ me := by intro hq; rw [hq] at he; simp at he; exact absurd he (by rw [he0]; decide)
    refine ⟨false, a2, ?_, rfl, hC2, hg12, hP2, hA2⟩
    have : (le != me) = true := by simpa using hne
    simp only [tkArgs, StateT.run_bind, run1, except_ok_bind, run2, this, ite_true]; rfl
  rw [tkaK3_yes (h := he0)] at h
  have heq : le = me := by
    by_cases hq : le = me
    · exact hq
    · rw [ite_eq_right hq] at he; exact absurd he he0
  subst heq
  -- the leaf's class
  rcases h4 : ceinternW m2 ip usp with _ | ⟨hd, m3⟩ <;> rw [h4] at h <;>
    try (simp only [tkaK4, reduceCtorEq] at h; done)
  obtain ⟨a3, run3, hS3, hg3⟩ := internConst_stage hS2 ip usp hip hus h4
  have hA3 := ceinternW_afr h4 hA2
  obtain ⟨q3, hhdP⟩ := ConRon.Bridge.Inductives.internConstE_run hC2.check.state
    (ConRon.Bridge.denoteN_ext hipP q12.ext) (ConRon.Bridge.denoteLs_ext husP q12.ext) run3
  have hC3 := hC2.of_pstep hS3 hA3 q3
  have q13 := q12.trans q3
  by_cases hb4 : 4294967296 ≤ hd
  · rw [tkaK4_big (h := hb4)] at h; cases h
  rw [tkaK4_ok (h := hb4)] at h
  have hhd : H hd := by simp only [H]; rw [UInt64.le_iff_toNat_le] at hb4; simp at hb4; omega
  have hP3 : RcMR m3 := hP2.fr (ceinternW_mfr h4)
  have hg03 := hg12.trans hg3
  have hlp := (hla.grow hg03).take (k := K)
  rw [hnP] at hlp
  generalize hL : (if lal < K then lal else K) = lpl at h hlp
  rcases h5 : mknF m3 [hd, lao, lpl] with _ | ⟨ra, m4⟩ <;> simp only [h5, tkaK5, reduceCtorEq] at h
  obtain ⟨app, a4, run4, hS4, hg4, happH, happD⟩ := mknF_ok dn vis fe hd lao lpl hhd _ m3 m4 a3 ra h5
    ⟨hS3, hlp.1⟩
  have hA4 := mknF_afr h5 hA3
  have hlpP := denoteEList_ext q13.ext _ _ (ConRon.Bridge.Inductives.denoteEList_take hlaP TM.nPc)
  obtain ⟨q4, -⟩ := ConRon.Bridge.Inductives.mkAppN_run (la.take TM.nPc) (laP.take TM.nPc)
    hC3.check.state hhdP hlpP run4
  have hC4 := hC3.of_pstep hS4 hA4 q4
  have q14 := q13.trans q4
  have hP4 : RcMR m4 := hP3.fr (MFr.ofMknF h5)
  have hg04 := hg03.trans hg4
  rcases h6 : memberNamesW n m4 q with _ | ⟨rn, m5⟩ <;> simp only [h6, tkaK6, reduceCtorEq] at h
  have hbs4 := hbs.grow hg04
  obtain ⟨hS5, hg5, -, hdn, htn⟩ := memberNamesW_stage h6 hS4 hbs4
  have hf5 := (memberNamesW_dec h6 hS4.2.2.2.1 hS4.2.2.2.2.2 hbs4.dec
    (by have := hbs4.ptop; have := hS4.lt64 (Nat.le_refl _); omega) hbs4.2.1 hbs4.2.2).2.2.2.1
  have hP5 : RcMR m5 := hP4.fr (MFr.of_iw hf5)
  have hA5 := AFr.iw hf5 hA4
  have hC5 := hC4.of_pstep hS5 hA5 (PStep.refl hC4.check.state)
  rcases h7 : noF n m5 (rn.headD 0) (rn.tail.headD 0) 0 0 (ra.headD 0) with _ | ⟨occ, m6⟩ <;> rw [h7] at h <;>
    try (simp only [tkaK7, reduceCtorEq] at h; done)
  obtain ⟨b, run6, hb6, hS6, hg6, hP6⟩ := noF_ok dn fe vis n h7 hS5 happH hdn (Nat.le_of_eq htn) hP5
  have hA6 := noF_afr h7 hA5
  have hC6 := hC5.of_pstep hS6 hA6 (PStep.refl hC5.check.state)
  have hg06 := (hg04.trans hg5).trans hg6
  have hdecApp : decE (ra.headD 0) = app := happD
  have hrun4 : (mkAppN (decE hd) (la.take TM.nPc)).run a3 = .ok (decE (ra.headD 0), a4) := by
    rw [hdecApp]; exact run4
  by_cases ho : occ = 0
  · rw [tkaK7_no (h := ho)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have : b = false := by rw [← hb6, ho]; rfl
    subst this
    refine ⟨false, a4, ?_, rfl, hC6, hg06, hP6, hA6⟩
    simp only [tkArgs, StateT.run_bind, run1, except_ok_bind, run2, bne_self_eq_false, Bool.false_eq_true,
      ite_false, ConRon.Arena.internConstE, run3, hrun4, run6]
    rfl
  rw [tkaK7_yes (h := ho)] at h
  have hb1 : b = true := by rw [← hb6]; simpa using ho
  subst hb1
  have hMk6 : ∀ k : Nat, k ≤ 12 → rdW (m6.arr64 IW) (Mc + UInt64.ofNat k) = rdW (m.arr64 IW) (Mc + UInt64.ofNat k) :=
    fun k hk => rdW_grow hg06 (hMk k hk)
  have e11 := hMk6 11 (by omega); have e12 := hMk6 12 (by omega); have e1 := hMk6 1 (by omega)
  have e2 := hMk6 2 (by omega); have e3 := hMk6 3 (by omega)
  simp only [show UInt64.ofNat 11 = (11 : Word) from rfl, show UInt64.ofNat 12 = (12 : Word) from rfl,
    show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
    show UInt64.ofNat 3 = (3 : Word) from rfl] at e11 e12 e1 e2 e3
  rw [e11, e12, e1, e2, e3] at h
  rcases h8 : tcmF (realCall p) n m6 vis q fto ftl (rdW (m.arr64 IW) (Mc + 11)) (rdW (m.arr64 IW) (Mc + 12))
      (rdW (m.arr64 IW) (Mc + 1)) (rdW (m.arr64 IW) (Mc + 2)) (rdW (m.arr64 IW) (Mc + 3)) usp lao lpl with _ | ⟨r8, m8⟩ <;> simp only [h8, tkaK8, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  have hpfl := ConRon.Bridge.Inductives.denoteEList_length (denoteEList_ext q14.ext _ _ hMpf)
  obtain ⟨c, a8, run8, hc, hC8, hg8, hP8, hA8⟩ := tcmF_okC hq henv n (by omega) h8 hC6 hA6
    (hbs.grow hg06) hlvH hus
    (by rw [decHL_grow hg06 hftb]; exact hft) (by have := hg06.1; omega) (hpfS.grow hg06) (hdsS.grow hg06)
    (hlp.grow ((hg4.trans hg5).trans hg6)) hP6
    (ConRon.Bridge.Inductives.dShape_ext q14.ext _ _ hsh) (denoteEList_ext q14.ext _ _ hftP)
    (denoteEList_ext q14.ext _ _ hMpf) (by rw [hlvD]; exact ConRon.Bridge.denoteLs_ext hMlv q14.ext)
    (denoteEList_ext q14.ext _ _ hMds) (ConRon.Bridge.denoteLs_ext husP q14.ext) (denoteEList_ext q4.ext _ _ hlpP) hformer
    hMs.1
  rw [hlvD] at run8
  refine ⟨c, a8, ?_, by simpa using hc, hC8, hg06.trans hg8, hP8, hA8⟩
  simp only [tkArgs, StateT.run_bind, run1, except_ok_bind, run2, bne_self_eq_false, Bool.false_eq_true,
    ite_false, ConRon.Arena.internConstE, run3, hrun4, run6, ite_true]
  exact run8

include hq henv in
/-- **`target_k53_heads` under `StageC`** (twin side: con-ron's `targetK53_spec`, the heads' part:
read-only steps). -/
theorem tkhW_okC (n : Nat) (hn : n ≤ 2 ^ 62) {m m' : Mem} {a : AState} {q fto ftl Mc leafW majDom : Word}
    {r : List Word} {bs : BlockShape} {formerTys : List EIdx} {TM : TargetMajor}
    (h : tkhW (realCall p) n m vis q fto ftl Mc leafW majDom = some (r, m'))
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hMc : DecB (fun m => decTM m Mc.toNat) m TM)
    (hl : H leafW) (hmj : H majDom) (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
    {lwP mdP : ConLeche.Expr}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hMcP : dMajor a.store TM = some McP)
    (hlwP : denoteE a.store (decE leafW) = some lwP) (hmdP : denoteE a.store (decE majDom) = some mdP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    ∃ c a', (tkHeads fe bs formerTys TM (decE leafW) (decE majDom)).run a = .ok (c, a') ∧
      (r.headD 0 != 0) = c ∧ StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ RcMR m' ∧ AbsOK m' := by
  have hS := hC.stage
  obtain _ | n := n
  · simp [tkhW] at h
  rw [tkhW_succ] at h
  rcases h1 : gafF m [CWF, leafW] with _ | ⟨rl, m1⟩ <;> simp only [h1, tkhK1, reduceCtorEq] at h
  obtain ⟨lh, a1, run1, hS1, hg1, hlhH, hlhD⟩ := gafF_ok dn vis fe CWF leafW hl m m1 a rl h1 hS
  rw [CWF_eq, ← decE_eq] at run1
  rw [← hlhD, ← decE_eq] at run1
  have hP1 := hP.fr (MFr.ofGafF h1)
  have hA1 := gafF_afr h1 hA
  obtain ⟨e1, hlh⟩ := ConRon.Bridge.Inductives.getAppFn_run hC.check.state hlwP run1
  subst a1
  have hC1 := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  rcases h2 : gafF m1 [CWF, majDom] with _ | ⟨rm, m2⟩ <;> rw [h2] at h <;>
    try (simp only [tkhK2, reduceCtorEq] at h; done)
  obtain ⟨mh, a2, run2, hS2, hg2, hmhH, hmhD⟩ := gafF_ok dn vis fe CWF majDom hmj m1 m2 a rm h2 hS1
  rw [CWF_eq, ← decE_eq] at run2
  rw [← hmhD, ← decE_eq] at run2
  have hP2 := hP1.fr (MFr.ofGafF h2)
  have hA2 := gafF_afr h2 hA1
  obtain ⟨e2, hmh⟩ := ConRon.Bridge.Inductives.getAppFn_run hC.check.state hmdP run2
  subst a2
  have hC2 := hC1.of_pstep hS2 hA2 (PStep.refl hC.check.state)
  have hg12 := hg1.trans hg2
  by_cases t1 : rl.headD 0 >>> 28 ≠ 3
  · rw [tkhK2_l (h := t1)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨false, a, ?_, rfl, hC2, hg12, hP2, hA2⟩
    have : ¬ (decE (rl.headD 0)).tag = ETag.const := fun e => t1 ((decE_tag_const _ hlhH).mp e)
    have hb : ((decE (rl.headD 0)).tag == ETag.const) = false := by rw [beq_eq_false_iff_ne]; exact this
    simp only [tkHeads, StateT.run_bind, run1, except_ok_bind, run2, hb, Bool.false_and,
      Bool.false_eq_true, ite_false]
    rfl
  by_cases t2 : rm.headD 0 >>> 28 ≠ 3
  · rw [tkhK2_m (h := t1) (h2 := t2)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨false, a, ?_, rfl, hC2, hg12, hP2, hA2⟩
    have : ¬ (decE (rm.headD 0)).tag = ETag.const := fun e => t2 ((decE_tag_const _ hmhH).mp e)
    have hb : ((decE (rm.headD 0)).tag == ETag.const) = false := by rw [beq_eq_false_iff_ne]; exact this
    simp only [tkHeads, StateT.run_bind, run1, except_ok_bind, run2, hb, Bool.and_false,
      Bool.false_eq_true, ite_false]
    rfl
  have t1' : rl.headD 0 >>> 28 = 3 := by simpa using t1
  have t2' : rm.headD 0 >>> 28 = 3 := by simpa using t2
  by_cases v1 : eViewW m2 (rl.headD 0) = []
  · rw [tkhK2_v1 (h := t1) (h2 := t2) (h3 := v1)] at h; cases h
  by_cases v2 : eViewW m2 (rm.headD 0) = []
  · rw [tkhK2_v2 (h := t1) (h2 := t2) (h3 := v1) (h4 := v2)] at h; cases h
  rw [tkhK2_ok (h := t1) (h2 := t2) (h3 := v1) (h4 := v2)] at h
  obtain ⟨vr1, hipH, husH⟩ := viewConstW hS2.1.arena.1 v1 t1'
  obtain ⟨vr2, hiiH, -⟩ := viewConstW hS2.1.arena.1 v2 t2'
  generalize hip : (eViewW m2 (rl.headD 0)).tail.headD 0 = ip at h vr1 hipH
  generalize hus : (eViewW m2 (rl.headD 0)).tail.tail.headD 0 = usp at h vr1 husH
  generalize hii : (eViewW m2 (rm.headD 0)).tail.headD 0 = ii at h vr2 hiiH
  have c1 : (decE (rl.headD 0)).tag = ETag.const := (decE_tag_const _ hlhH).mpr t1'
  have c2 : (decE (rm.headD 0)).tag = ETag.const := (decE_tag_const _ hmhH).mpr t2'
  have ct1 : ((decE (rl.headD 0)).tag == ETag.const) = true := by rw [beq_iff_eq]; exact c1
  obtain ⟨-, hv1⟩ := ConRon.Bridge.Inductives.viewConst_run vr1
  obtain ⟨I'P, us'P, -, hI', hus'⟩ := ConRon.Bridge.denote_const_inv hC.check.state.wf
    (ConRon.Bridge.view_of_viewConst_tag ct1 hv1.symm) hlh
  rcases h3 : gaaF m2 [CWF, leafW] with _ | ⟨ra, m3⟩ <;> simp only [h3, tkhK3, reduceCtorEq] at h
  obtain ⟨la, a3, run3, hS3, hg3, hla, hlab⟩ := gaaF_ok dn vis fe CWF leafW hl m2 m3 a ra h3 hS2
  rw [CWF_eq, ← decE_eq] at run3
  have hP3 := hP2.fr (MFr.ofGaaF h3)
  have hA3 := gaaF_afr h3 hA2
  obtain ⟨e3, hlaP⟩ := ConRon.Bridge.Inductives.getAppArgs_run hC.check.state hlwP run3
  subst a3
  rcases h4 : gaaF m3 [CWF, majDom] with _ | ⟨rb, m4⟩ <;> rw [h4] at h <;>
    try (simp only [tkhK4, reduceCtorEq] at h; done)
  obtain ⟨ma, a4, run4, hS4, hg4, hma, hmab⟩ := gaaF_ok dn vis fe CWF majDom hmj m3 m4 a rb h4 hS3
  rw [CWF_eq, ← decE_eq] at run4
  have hP4 := hP3.fr (MFr.ofGaaF h4)
  have hA4 := gaaF_afr h4 hA3
  obtain ⟨e4, hmaP⟩ := ConRon.Bridge.Inductives.getAppArgs_run hC.check.state hmdP run4
  subst a4
  have hC4 := hC2.of_pstep hS4 hA4 (PStep.refl hC.check.state)
  have hg14 := (hg12.trans hg3).trans hg4
  simp only [getD_zero, getD_one, Nat.zero_add] at hla hlab hma hmab
  have hla4 : HSl0 m4 (ra.headD 0) (ra.tail.headD 0) la := (HSl0.of hla hlab).grow hg4
  have hma4 : HSl0 m4 (rb.headD 0) (rb.tail.headD 0) ma := HSl0.of hma hmab
  have hpre : (tkHeads fe bs formerTys TM (decE leafW) (decE majDom)).run a =
      (if !(decI ip == (decI ii : NIdx) && la.length == ma.length) then
        (pure false : AM Bool) else tkArgs fe bs formerTys TM (decI ip) (decI usp) la ma).run a := by
    have hc2 : ((decE (rm.headD 0)).tag == ETag.const) = true := by rw [beq_iff_eq]; exact c2
    simp only [tkHeads, StateT.run_bind, run1, except_ok_bind, run2, ct1, hc2, Bool.and_self,
      ite_true, vr1, vr2, run3, run4]
  by_cases hi : ip ≠ ii
  · rw [tkhK4_i (h := hi)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨false, a, ?_, rfl, hC4, hg14, hP4, hA4⟩
    have : (decI ip == (decI ii : NIdx)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => hi (decI_inj hipH hiiH e)
    rw [hpre]; simp [this]; rfl
  have hii' : ip = ii := by simpa using hi
  subst hii'
  have hlen1 : la.length = (ra.tail.headD 0).toNat := hla4.len
  have hlen2 : ma.length = (rb.tail.headD 0).toNat := hma4.len
  by_cases hl2 : ra.tail.headD 0 ≠ rb.tail.headD 0
  · rw [tkhK4_l (h := hi) (h2 := hl2)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨false, a, ?_, rfl, hC4, hg14, hP4, hA4⟩
    have : (la.length == ma.length) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, hlen1, hlen2]
      exact fun e => hl2 (UInt64.toNat_inj.mp e)
    rw [hpre]; simp [this]; rfl
  rw [tkhK4_ok (h := hi) (h2 := hl2)] at h
  have hll : (la.length == ma.length) = true := by
    simp only [beq_iff_eq, hlen1, hlen2]; exact congrArg UInt64.toNat (by simpa using hl2)
  rcases h5 : tkaW (realCall p) n m4 vis q fto ftl Mc ip usp (ra.headD 0) (ra.tail.headD 0) (rb.headD 0)
      (rb.tail.headD 0) with _ | ⟨r5, m5⟩ <;> simp only [h5, tkhK5, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨c, a5, run5, hc, hC5, hg5, hP5, hA5⟩ := tkaW_okC hq henv n (by omega) h5 hC4 hA4
    (hbs.grow hg14) (by rw [decHL_grow hg14 hftb]; exact hft) (by have := hg14.1; omega)
    (hMc.grow (decTM_mono _) hg14) hipH husH hla4 hma4 hP4 hsh hftP hMcP hI' hus' hlaP hmaP hformer hMs
  refine ⟨c, a5, ?_, by simpa using hc, hC5, hg14.trans hg5, hP5, hA5⟩
  rw [hpre]; simp only [beq_self_eq_true, hll, Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false]
  exact run5

include hq henv in
/-- **`target_k53` under `StageC`** (twin side: con-ron's `targetK53_spec`'s proof). -/
theorem tkW_okC (n : Nat) (hn : n ≤ 2 ^ 62) {m m' : Mem} {a : AState}
    {q fto ftl Mc teo tel majDom f : Word}
    {r : List Word} {bs : BlockShape} {formerTys : List EIdx} {TM : TargetMajor} {tele : List EIdx}
    (h : tkW (realCall p) n m vis q fto ftl Mc teo tel majDom f = some (r, m'))
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hMc : DecB (fun m => decTM m Mc.toNat) m TM)
    (htl : HSl0 m teo tel tele) (hmj : H majDom) (hf : H f) (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP teleP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
    {mdP fP : ConLeche.Expr}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hMcP : dMajor a.store TM = some McP)
    (htlP : Frontend.denoteEList a.store tele = some teleP)
    (hmdP : denoteE a.store (decE majDom) = some mdP) (hfP : denoteE a.store (decE f) = some fP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    ∃ c a', (ConRon.Arena.targetK53 V fe bs formerTys TM tele (decE majDom) (decE f)).run a =
      .ok (c, a') ∧ (r.headD 0 != 0) = c ∧ StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ RcMR m' ∧
      AbsOK m' := by
  have hS := hC.stage
  obtain _ | n := n
  · simp [tkW] at h
  rw [tkW_succ] at h
  rw [tk53_eq]
  rcases h1 : stripF 6 m [tel, f] with _ | ⟨rs, m1⟩ <;> rw [h1] at h <;>
    try (simp only [tkK1, reduceCtorEq] at h; done)
  obtain ⟨o, a1, run1, hS1, hg1, hd1⟩ := stripF_pis_ok dn vis fe tel f hf m m1 a rs h1 hS
  rw [← decE_eq, ← htl.len] at run1
  have hP1 := hP.fr (MFr.ofStripF h1)
  have hA1 := stripF_afr h1 hA
  obtain ⟨e1, hbp⟩ := ConRon.Bridge.Inductives.stripPis_pstep hC.check.state hfP run1
  subst a1
  have hC1 := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  rcases o with _ | ⟨teleW, leafW⟩
  · have h0 : rs.headD 0 = 0 := hd1
    rw [tkK1_no (h := h0)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨false, a, ?_, rfl, hC1, hg1, hP1, hA1⟩
    simp only [StateT.run_bind, run1, except_ok_bind]; rfl
  obtain ⟨twP, lwP, -, htw, hlw⟩ := ConRon.Bridge.Inductives.denoteBP_some hbp
  obtain ⟨h0, ⟨hdl, hbl⟩, hlwH, hlwD⟩ := hd1
  rw [tkK1_ok (h := by rw [h0]; decide)] at h
  simp only [show (1 + 1 : Nat) = 2 from rfl, getD_one, getD_two] at hdl hbl
  have hl3 : (rs.drop 3).headD 0 = rs.tail.tail.tail.headD 0 := by
    rcases rs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [hl3] at hlwH hlwD
  rcases h2 : tteW n m1 (rs.tail.headD 0) (rs.tail.tail.headD 0) teo tel with _ | ⟨rt, m2⟩ <;> rw [h2] at h <;>
    try (simp only [tkK2, reduceCtorEq] at h; done)
  obtain ⟨c1, a2, run2, hc1, hS2, hg2, hP2⟩ := tteW_ok dn fe vis n h2 hS1 (HSl0.of hdl hbl) (htl.grow hg1) hP1
  have hA2 := tteW_afr h2 hA1
  have q2 := tkTele_cstep hC.check htw htlP run2
  have hC2 := hC1.of_cstep hS2 hA2 q2
  have hg12 := hg1.trans hg2
  by_cases hz : rt.headD 0 = 0
  · rw [tkK2_no (h := hz)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have : c1 = false := by rw [← hc1, hz]; rfl
    subst this
    refine ⟨false, a2, ?_, rfl, hC2, hg12, hP2, hA2⟩
    simp only [StateT.run_bind, run1, except_ok_bind, run2, Bool.false_eq_true, ite_false]; rfl
  rw [tkK2_ok (h := hz)] at h
  have : c1 = true := by rw [← hc1]; simpa using hz
  subst this
  rcases h3 : tkhW (realCall p) n m2 vis q fto ftl Mc (rs.tail.tail.tail.headD 0) majDom with _ | ⟨r3, m3⟩ <;> simp only [h3, tkK3, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  rw [← decE_eq] at hlwD
  obtain ⟨c, a3, run3, hc, hC3, hg3, hP3, hA3⟩ := tkhW_okC hq henv n (by omega) h3 hC2 hA2
    (hbs.grow hg12) (by rw [decHL_grow hg12 hftb]; exact hft) (by have := hg12.1; omega)
    (hMc.grow (decTM_mono _) hg12) hlwH hmj hP2
    (ConRon.Bridge.Inductives.dShape_ext q2.ext _ _ hsh) (denoteEList_ext q2.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dMajor_ext q2.ext _ _ hMcP) (by rw [hlwD]; exact denote_ext hlw q2.ext)
    (denote_ext hmdP q2.ext) hformer hMs
  refine ⟨c, a3, ?_, by simpa using hc, hC3, hg12.trans hg3, hP3, hA3⟩
  rw [hlwD] at run3
  simp only [StateT.run_bind, run1, except_ok_bind, run2, ite_true]
  exact run3

include hq henv in
/-- **`target_k53` refines `targetK53`** under `StageC` (the knot's core calls; the inputs'
denotations and scoping as con-ron's `targetK53_spec` asks). -/
@[refines ConRon.Arena.targetK53]
theorem targetK53_refinesC (L : K53Look p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (q fto ftl Mc teo tel majDom f : Word)
    (bs : BlockShape) (formerTys : List EIdx) (TM : TargetMajor) (tele : List EIdx)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hMc : DecB (fun m => decTM m Mc.toNat) s₀.mem TM) (htl : HSl0 s₀.mem teo tel tele)
    (hmj : H majDom) (hf : H f) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP teleP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
    {mdP fP : ConLeche.Expr}
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hMcP : dMajor a₀.store TM = some McP)
    (htlP : Frontend.denoteEList a₀.store tele = some teleP)
    (hmdP : denoteE a₀.store (decE majDom) = some mdP) (hfP : denoteE a₀.store (decE f) = some fP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_k53" [vis, q, fto, ftl, Mc, teo, tel, majDom, f]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetK53 V fe bs formerTys TM tele (decE majDom) (decE f)) a₀ ∧
      (r.headD 0 != 0) =
        AM.res (ConRon.Arena.targetK53 V fe bs formerTys TM tele (decE majDom) (decE f)) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.targetK53 V fe bs formerTys TM tele (decE majDom) (decE f)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (tk_spec p L (realCall p) (realCall_spec p) n s₀ vis q fto ftl Mc teo tel majDom f) ?_
  rintro r s' ⟨hl', hm⟩
  obtain ⟨c, a', run, hc, hC', hg, hP', hA'⟩ := tkW_okC hq henv n hn hm hC hA hbs hft hftb hMc htl hmj
    hf hP hsh hftP hMcP htlP hmdP hfP hformer hMs
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hres]; exact hc, by rw [hst]; exact hC', hg, hP', hA'⟩

end sims

end L.Ind
