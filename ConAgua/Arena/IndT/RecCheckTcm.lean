import ConAgua.Arena.IndT.RecCheckTpd
import ConAgua.Arena.IndRealLvlC
import ConAgua.Arena.IndSumSpec.StructCtorResidOk
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl
import ConAgua.Arena.IndInstallSpec.NestCtx
import ConAgua.Census.Attr

/-!
# `targetClassMatch` under `StageC` (lane `indstaget`, helper `pds`)

`target_class_match`'s model at `realCall p`, from `StageC` and the inputs' denotations con-ron's
`targetClassMatch_spec` asks; its twin side transcribed from that spec's proof: `lvlsEq?`
(`lvlsEqC_simC`, the real `lvls_eq_c` under `StageC`), the shape's member names
and parameters (L only), `paramLevels` (`paramLevels_spec`), `targetHoles` (`targetHoles_spec`), then
`pdeW_okC`.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs dShape)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem thW_afr : ∀ (n : Nat) {m m' : Mem} {tyo tyl base : Word} {r : List Word},
    thW n m tyo tyl base = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [thW] at h
  | n + 1, m, m', tyo, tyl, base, r, h => by
    by_cases hl : tyl = 0
    · rw [thW_nil (h := hl)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      exact AFr.refl _
    rw [thW_cons (h := hl)] at h
    rcases hf : fvinternW m base (rdW (m.arr64 IW) tyo) with _ | ⟨v, m1⟩ <;> rw [hf] at h <;>
      try (simp only [thK1, reduceCtorEq] at h; done)
    by_cases hb : 4294967296 ≤ v
    · rw [thK1_big (h := hb)] at h; cases h
    rw [thK1_ok (h := hb)] at h
    rcases hg : thW n m1 (tyo + 1) (tyl - 1) (base + 1) with _ | ⟨r2, m2⟩ <;> simp only [hg, thK2, reduceCtorEq] at h
    rcases hc : consW n m2 v (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩ <;> simp only [hc, thK3, reduceCtorEq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact ((fvinternW_afr hf).trans (thW_afr n hg)).trans (consW_afr hc)

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`target_class_match` under `StageC`** (twin side: con-ron's `targetClassMatch_spec`'s
proof). -/
theorem tcmW_okC (n : Nat) (hn : n ≤ 2 ^ 62) {m m' : Mem} {a : AState}
    {q fto ftl pfo pfl us dso dsl lvls edso edsl : Word}
    {r : List Word} {bs : BlockShape} {formerTys pfvs ds eds : List EIdx}
    (h : tcmW (realCall p) n m vis q fto ftl pfo pfl us dso dsl lvls edso edsl = some (r, m'))
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hbs : BSOK m q.toNat bs) (hus : H us)
    (hlv : H lvls)
    (hft : decHL m fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop m)
    (hpf : HSl0 m pfo pfl pfvs) (hds : HSl0 m dso dsl ds) (heds : HSl0 m edso edsl eds)
    (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP edsP : List ConLeche.Expr}
    {usP lvlsP : List ConLeche.Level}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hpfP : Frontend.denoteEList a.store pfvs = some pfvsP)
    (husP : denoteLs a.store.lss (decI us) = some usP)
    (hdsP : Frontend.denoteEList a.store ds = some dsP)
    (hlvP : denoteLs a.store.lss (decI lvls) = some lvlsP)
    (hedsP : Frontend.denoteEList a.store eds = some edsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hpw : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped pfvsP.length x) :
    ∃ c a', (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds).run a =
      .ok (c, a') ∧ (r.headD 0 != 0) = c ∧ StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ RcMR m' ∧
      AbsOK m' := by
  have hS := hC.stage
  unfold tcmW at h
  rcases h1 : realCall p n "lvls_eq_c" [us, lvls] m with _ | ⟨r1, m1⟩ <;> rw [h1] at h <;>
    try (simp only [tcmK1, reduceCtorEq] at h; done)
  obtain ⟨o1, a1, run1, hC1, hg1, hd1, hA1, c1, -⟩ :=
    lvlsEqC_simC p hq.closed hq.knot.lvc n hC hA us lvls hus hlv husP hlvP r1 m1 h1
  have hS1 := hC1.stage
  have hP1 := hP.fr (MFr.ofCore hq.closed (by decide) h1)
  by_cases hne : r1.headD 0 ≠ 2
  · rw [tcmK1_no (h := hne)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨false, a1, ?_, rfl, hC1, hg1, hP1, hA1⟩
    simp only [ConRon.Arena.targetClassMatch, StateT.run_bind, run1, except_ok_bind]
    simp only [decLvlEq] at hd1
    rcases o1 with _ | _ | _
    · rfl
    · rfl
    · exact absurd hd1 hne
  rw [tcmK1_yes (h := hne)] at h
  have ho1 : o1 = some true := by
    simp only [decLvlEq] at hd1
    rcases o1 with _ | _ | _
    · exfalso; apply hne; simp only at hd1; rw [hd1]; decide
    · exfalso; apply hne; simp only at hd1; rw [hd1]; decide
    · rfl
  subst ho1
  have hsz := hS1.2.2.2.1
  have hbs1 := hbs.grow hg1
  rcases h2 : memberNamesW n m1 q with _ | ⟨rn, m2⟩ <;> simp only [h2, tcmK2, reduceCtorEq] at h
  obtain ⟨hS2, hg2, -, hdn, htn⟩ := memberNamesW_stage h2 hS1 hbs1
  have hf2 := (memberNamesW_dec h2 hsz hS1.2.2.2.2.2 hbs1.dec (by have := hbs1.ptop; have := hS1.lt64 (Nat.le_refl _); omega)
    hbs1.2.1 hbs1.2.2).2.2.2.1
  have hP2 := hP1.fr (MFr.of_iw hf2)
  have hA2 := AFr.iw hf2 hA1
  have hC2 := hC1.of_pstep hS2 hA2 (PStep.refl hC1.check.state)
  rcases h3 : lpsW n m2 q with _ | ⟨rl, m3⟩ <;> simp only [h3, tcmK3, reduceCtorEq] at h
  obtain ⟨hS3, hg3, hdl, hbl⟩ := lpsW_ok' h3 hS2 ((hbs1.1.grow (decBS_mono _) hg2))
  have hP3 := hP2.fr (lpsW_mfr h3)
  have hA3 := lpsW_afr h3 hA2
  have hC3 := hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state)
  rcases h4 : plW n m3 (rl.headD 0) (rl.tail.headD 0) with _ | ⟨rb, m4⟩ <;> rw [h4] at h <;>
    try (simp only [tcmK4, reduceCtorEq] at h; done)
  obtain ⟨blv, a4, run4, hS4, hg4, hH4, hdb⟩ := plW_ok dn vis fe n m3 m4 a1 _ _ bs.lps rb h4 hS3 hdl
    (hS3.lt64 hbl) hbl
  have hP4 := hP3.fr (plW_mfr h4)
  have hA4 := plW_afr h4 hA3
  obtain ⟨q4, hbl4⟩ := ConRon.Bridge.Inductives.paramLevels_spec bs.lps pP.lps a1 a4 blv
    hC3.check.state (ConRon.Bridge.denoteNListE_ext c1.ext _ _
      (ConRon.Bridge.Inductives.BlockShape.lps_spec hsh)) run4
  have hC4 := hC3.of_pstep hS4 hA4 q4
  by_cases hw : pfl + ftl < pfl
  · rw [tcmK4_wrap (h := hw)] at h; cases h
  rw [tcmK4_ok (h := hw)] at h
  have hd : (pfl + ftl).toNat = pfl.toNat + ftl.toNat := word_add_nowrap hw
  have hg14 := (hg2.trans hg3).trans hg4
  have hg04 := hg1.trans hg14
  rcases h5 : thW n m4 fto ftl pfl with _ | ⟨rh, m5⟩ <;> simp only [h5, tcmK5, reduceCtorEq] at h
  obtain ⟨holes, a5, run5, hS5, hg5, hdh, hbh⟩ := thW_ok dn vis fe n m4 m5 a4 fto ftl pfl rh formerTys h5 hS4
    (by rw [decHL_grow hg04 hftb]; exact hft) (hS.lt64 hftb) (by have := hg04.1; omega)
    (by rw [← hd]; exact (pfl + ftl).toNat_lt)
  have hP5 := hP4.fr (thW_mfr n h5)
  have hA5 := thW_afr n h5 hA4
  have hlen : pfvs.length = pfl.toNat := hpf.len
  have hlenf : formerTys.length = ftl.toNat := decHL_length _ hft
  have hlenP : pfvs.length = pfvsP.length := ConRon.Bridge.Inductives.denoteEList_length hpfP
  have hlenfP : formerTys.length = formerTysP.length :=
    ConRon.Bridge.Inductives.denoteEList_length hftP
  have c14 := c1.trans (q4.toCore hC1.check)
  rw [← hlen] at run5
  obtain ⟨q5, hhs⟩ := ConRon.Bridge.Inductives.targetHoles_spec formerTys formerTysP pfvs.length a4 a5
    holes hC4.check.state (denoteEList_ext c14.ext _ _ hftP) run5
  have hC5 := hC4.of_pstep hS5 hA5 q5
  have hg05 := hg04.trans hg5
  have c15 := c14.trans (q5.toCore hC4.check)
  rcases h6 : pdeW (realCall p) n m5 vis (pfl + ftl) (rn.headD 0) (rn.tail.headD 0) (rb.headD 0)
      (rh.headD 0) (rh.tail.headD 0) pfo pfl dso dsl edso edsl with _ | ⟨r6, m6⟩ <;> simp only [h6, tcmK6, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  have hg25 := (hg3.trans hg4).trans hg5
  have hdP : (pfl + ftl).toNat = pfvsP.length + formerTysP.length := by
    rw [hd, ← hlen, ← hlenf, hlenP, hlenfP]
  rw [← hdb] at hbl4
  obtain ⟨c, a6, run6, hc, hC6, hg6, hP6, hA6⟩ := pdeW_okC hq henv n hn h6 hC5 hA5 hH4
    (by rw [decHL_grow hg25 (by omega)]; exact hdn) (by have := hg25.1; omega) hdh hbh
    (hpf.grow hg05) (hds.grow hg05) (heds.grow hg05) hP5
    (namesP := pP.memberNames) (lvlsP := pP.lps.map ConLeche.Level.param)
    (holesP := ConLeche.targetHoles formerTysP pfvsP.length)
    ⟨ConRon.Bridge.denoteNListE_ext c15.ext _ _
        (ConRon.Bridge.Inductives.BlockShape.memberNames_spec hsh),
      ConRon.Bridge.denoteLs_ext hbl4 q5.ext, by rw [← hlenP]; exact hhs⟩
    (denoteEList_ext c15.ext _ _ hpfP) (denoteEList_ext c15.ext _ _ hdsP)
    (denoteEList_ext c15.ext _ _ hedsP)
    (by
      rw [hdP]
      exact ConLeche.targetAbs_WScoped (ConLeche.Cached.targetHoles_WScoped hformer pfvsP.length))
    (fun x hx => by rw [hdP]; exact (hpw x hx).mono (by omega))
  refine ⟨c, a6, ?_, by simpa using hc, hC6, hg05.trans hg6, hP6, hA6⟩
  rw [hd, ← hlen, ← hlenf, hdb] at run6
  simp only [ConRon.Arena.targetClassMatch, StateT.run_bind, run1, except_ok_bind, run4, run5]
  exact run6

include hq henv in
/-- **`target_class_match` refines `targetClassMatch`** under `StageC` (the knot's core calls; the
inputs' denotations as con-ron's `targetClassMatch_spec` asks; `lvls_eq_c` by `lvlsEqC_simC`). -/
@[refines ConRon.Arena.targetClassMatch]
theorem targetClassMatch_refinesC (L : TcmLook p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (q fto ftl pfo pfl us dso dsl lvls edso edsl : Word)
    (bs : BlockShape) (formerTys pfvs ds eds : List EIdx) (hC : StageC dn vis fe env s₀.mem a₀)
    (hA : AbsOK s₀.mem) (hbs : BSOK s₀.mem q.toNat bs) (hus : H us) (hlv : H lvls)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hpf : HSl0 s₀.mem pfo pfl pfvs) (hds : HSl0 s₀.mem dso dsl ds)
    (heds : HSl0 s₀.mem edso edsl eds) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP edsP : List ConLeche.Expr}
    {usP lvlsP : List ConLeche.Level}
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hpfP : Frontend.denoteEList a₀.store pfvs = some pfvsP)
    (husP : denoteLs a₀.store.lss (decI us) = some usP)
    (hdsP : Frontend.denoteEList a₀.store ds = some dsP)
    (hlvP : denoteLs a₀.store.lss (decI lvls) = some lvlsP)
    (hedsP : Frontend.denoteEList a₀.store eds = some edsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hpw : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped pfvsP.length x) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_class_match"
      [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, lvls, edso, edsl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds) a₀ ∧
      (r.headD 0 != 0) =
        AM.res (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.targetClassMatch V fe bs formerTys pfvs (decI us) ds (decI lvls) eds) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (targetClassMatch_spec p L (realCall p) (realCall_spec p) n s₀ vis q fto ftl pfo
    pfl us dso dsl lvls edso edsl) ?_
  rintro r s' ⟨hl', hm⟩
  obtain ⟨c, a', run, hc, hC', hg, hP', hA'⟩ := tcmW_okC hq henv n hn hm hC hA hbs hus hlv hft hftb
    hpf hds heds hP hsh hftP hpfP husP hdsP hlvP hedsP hformer hpw
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hres]; exact hc, by rw [hst]; exact hC', hg, hP', hA'⟩

end sims

end L.Ind
