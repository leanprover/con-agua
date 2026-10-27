import ConAgua.Arena.IndT.RecCheckTcm
import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.IndSumSpec.SoaW
import ConAgua.Arena.RecCheckSpec.CnfW
import ConAgua.Arena.RecCheckSpec.TargetMajorDefault
import ConAgua.Arena.RecCheckSpec.Tmn

/-!
# `targetMajorNfs` under `StageC` (lane `indstaget`, helper `pds`)

`target_major_nfs`' model at `realCall p`, from `StageC` and the inputs' denotations con-ron's
`targetMajorNfs_spec` asks; its twin side transcribed from that spec's proof: the tail first (its
`CoreStep` from con-ron's spec on the tail's run), the name test (L only), `targetClassMatch`
(`tcmF_okC`), the kept entry consed (L only).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep TAArgs dShape dCtors dCtorNf)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- `tcmW_okC` at the exec fuel (`tcmF`). -/
theorem tcmF_okC (n : Nat) (hn : n ≤ 2 ^ 62) {m m' : Mem} {a : AState}
    {q fto ftl pfo pfl us dso dsl lvls edso edsl : Word}
    {r : List Word} {bs : BlockShape} {formerTys pfvs ds eds : List EIdx}
    (h : tcmF (realCall p) n m vis q fto ftl pfo pfl us dso dsl lvls edso edsl = some (r, m'))
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
  cases n with
  | zero => simp [tcmF] at h
  | succ n =>
    exact tcmW_okC hq henv n (by omega) h hC hA hbs hus hlv hft hftb hpf hds heds hP hsh hftP
      hpfP husP hdsP hlvP hedsP hformer hpw

include hq henv in
/-- **`target_major_nfs` under `StageC`** (twin side: con-ron's `targetMajorNfs_spec`'s list
induction). -/
theorem tmnW_okC (n : Nat) (hn : n ≤ 2 ^ 62) : ∀ {m m' : Mem} {a : AState}
    {q fto ftl pfo pfl us dso dsl cto ctl nfo nfl : Word}
    {r : List Word} {bs : BlockShape} {formerTys pfvs ds : List EIdx} {ctors : List (IConstantVal × Nat)}
    {nfs : List NestCtorNf} {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP : List ConLeche.Expr}
    {usP : List ConLeche.Level} {ctorsP : List (ConLeche.ConstantVal × Nat)}
    {nfsP : List ConLeche.NestCtorNf},
    tmnW (realCall p) n m vis q fto ftl pfo pfl us dso dsl cto ctl nfo nfl = some (r, m') →
    StageC dn vis fe env m a → AbsOK m → BSOK m q.toNat bs → H us →
    decHL m fto.toNat ftl.toNat = some formerTys → fto.toNat + ftl.toNat ≤ iwTop m →
    HSl0 m pfo pfl pfvs → HSl0 m dso dsl ds → PSlR decCN ctors cto ctl m → PSlR decNCN nfs nfo nfl m →
    RcMR m →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    Frontend.denoteEList a.store pfvs = some pfvsP → denoteLs a.store.lss (decI us) = some usP →
    Frontend.denoteEList a.store ds = some dsP → dCtors a.store ctors = some ctorsP →
    nfs.mapM (dCtorNf a.store) = some nfsP →
    (∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t) →
    (∀ x ∈ pfvsP, ConLeche.Expr.WScoped pfvsP.length x) →
    ∃ ys a', (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs).run a =
      .ok (ys, a') ∧ PSlR decNCN ys (r.headD 0) (r.tail.headD 0) m' ∧ StageC dn vis fe env m' a' ∧
      IWGrow m m' ∧ RcMR m' ∧ AbsOK m' := by
  induction n with
  | zero =>
    intro m m' a q fto ftl pfo pfl us dso dsl cto ctl nfo nfl r bs formerTys pfvs ds ctors nfs pP
      formerTysP pfvsP dsP usP ctorsP nfsP h
    simp [tmnW] at h
  | succ n ih =>
  intro m m' a q fto ftl pfo pfl us dso dsl cto ctl nfo nfl r bs formerTys pfvs ds ctors nfs pP
    formerTysP pfvsP dsP usP ctorsP nfsP h hC hA hbs hus hft hftb hpf hds hct hnf hP hsh hftP hpfP
    husP hdsP hctP hnfP hformer hpw
  have hS := hC.stage
  by_cases hl : nfl = 0
  · rw [tmnW_nil (h := hl)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hl
    have : nfs = [] := by
      have := decPL_length _ (hnf.1.get (OMono.decPL decNCN_mono _ _)); simpa using this
    subst this
    exact ⟨[], a, rfl, PSlR.nil _ _, hC, IWGrow.refl _, hP, hA⟩
  rw [tmnW_cons (h := hl)] at h
  have hsz := hS.2.2.2.1
  obtain ⟨nf, nfs', rfl, hnf0, hnf'⟩ := hnf.uncons hl hsz
  obtain ⟨nfP, nfsP', rfl, hnfP, hnfsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hnfP
  rcases h1 : tmnW (realCall p) n m vis q fto ftl pfo pfl us dso dsl cto ctl (nfo + 1) (nfl - 1) with _ | ⟨rr, m1⟩ <;> simp only [h1, tmnK1, reduceCtorEq] at h
  obtain ⟨ys, a1, run1, hys, hC1, hg1, hP1, hA1⟩ := ih (by omega) h1 hC hA hbs hus hft hftb hpf hds
    hct hnf' hP hsh hftP hpfP husP hdsP hctP hnfsP' hformer hpw
  obtain ⟨c1, -⟩ := ConRon.Bridge.Inductives.targetMajorNfs_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv bs pP formerTys pfvs formerTysP pfvsP (decI us) usP ds dsP ctors ctorsP hformer hpw nfs'
    nfsP' a a1 ys hC.check ⟨hsh, hftP, hpfP, husP, hdsP, hctP, hnfsP'⟩ run1
  have hS1 := hC1.stage
  -- the head entry, in `m1`
  have hnfo : nfo.toNat < iwTop m := by
    have := hnf.2; have := (slice_step hl (hS.lt64 hnf.2)).2.2; omega
  have he : rdW (m1.arr64 IW) nfo = rdW (m.arr64 IW) nfo := by
    simp only [rdW]; rw [hg1.2.2.1 _ hnfo]
  rw [he] at h
  generalize hE : rdW (m.arr64 IW) nfo = e at h hnf0
  have hnf1 : DecB (fun m' => decNCN m' e.toNat) m1 nf := hnf0.grow (decNCN_mono _) hg1
  have hsz1 := hS1.2.2.2.1
  obtain ⟨hcH, hcD, hlH, hlD, hdsl⟩ := decNCN_fields hnf1 hsz1
  have hct1 := hct.grow (fun q => decCN_mono q) hg1
  rcases h2 : chnW n m1 cto ctl (rdW (m1.arr64 IW) e) with _ | hv <;> rw [h2] at h <;>
    try (simp only [tmnK2, reduceCtorEq] at h; done)
  obtain ⟨hany, -⟩ := chnW_ok n m1 cto ctl _ hv ctors h2 (hct1.1.get (OMono.decPL decCN_mono _ _)) hcH
    (hS1.lt64 hct1.2)
  rw [hcD] at hany
  have hrun_tail : ∀ {α : Type} (k : List NestCtorNf → AM α),
      ((ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs') >>= k).run a =
        (k ys).run a1 := by
    intro α k; simp only [StateT.run_bind, run1]; rfl
  by_cases hh : hv = 0
  · rw [tmnK2_no (h := hh)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨ys, a1, ?_, hys, hC1, hg1, hP1, hA1⟩
    have hf : ctors.any (fun c => c.1.name == nf.ctor) = false := by rw [← hany, hh]; rfl
    rw [ConRon.Arena.targetMajorNfs, hrun_tail]; simp only [hf, Bool.false_eq_true, ite_false]; rfl
  rw [tmnK2_yes (h := hh)] at h
  have ht : ctors.any (fun c => c.1.name == nf.ctor) = true := by rw [← hany]; simpa using hh
  obtain ⟨-, hlvP, hedP, -⟩ := ConRon.Bridge.Inductives.RC.dCtorNf_inv
    (ConRon.Bridge.Inductives.dCtorNf_ext c1.ext _ _ hnfP)
  cases h3 : tcmF (realCall p) n m1 vis q fto ftl pfo pfl us dso dsl (rdW (m1.arr64 IW) (e + 1))
      (rdW (m1.arr64 IW) (e + 2)) (rdW (m1.arr64 IW) (e + 3)) with
  | none => rw [h3] at h; simp [tmnK3] at h
  | some x =>
  obtain ⟨rk, m2⟩ := x
  rw [h3] at h
  obtain ⟨c, a2, run2, hc, hC2, hg2, hP2, hA2⟩ := tcmF_okC hq henv n (by omega) h3 hC1 hA1
    (hbs.grow hg1) hus hlH (by rw [decHL_grow hg1 hftb]; exact hft) (by have := hg1.1; omega)
    (hpf.grow hg1) (hds.grow hg1) hdsl hP1
    (ConRon.Bridge.Inductives.dShape_ext c1.ext _ _ hsh) (denoteEList_ext c1.ext _ _ hftP)
    (denoteEList_ext c1.ext _ _ hpfP) (ConRon.Bridge.denoteLs_ext husP c1.ext)
    (denoteEList_ext c1.ext _ _ hdsP) (by rw [hlD]; exact hlvP) hedP hformer hpw
  rw [hlD] at run2
  have hg12 := hg1.trans hg2
  by_cases hk : rk.headD 0 = 0
  · rw [tmnK3_drop (h := hk)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hc0 : c = false := by rw [← hc, hk]; rfl
    subst hc0
    refine ⟨ys, a2, ?_, hys.grow (fun q => decNCN_mono q) hg2, hC2, hg12, hP2, hA2⟩
    rw [ConRon.Arena.targetMajorNfs, hrun_tail]
    simp only [ht, ite_true, StateT.run_bind, run2, except_ok_bind, Bool.false_eq_true, ite_false]; rfl
  rw [tmnK3_keep (h := hk)] at h
  have hc1 : c = true := by rw [← hc]; simpa using hk
  subst hc1
  rcases h4 : consW n m2 e (rr.headD 0) (rr.tail.headD 0) with _ | ⟨rc, m3⟩ <;> simp only [h4, tmnK4, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hS3, hg3, hps3, hf3⟩ := consW_pslr (fun q => decNCN_mono q) h4 hC2.stage
    (hys.grow (fun q => decNCN_mono q) hg2) (hnf1.grow (decNCN_mono _) hg2)
  have hA3 := consW_afr h4 hA2
  refine ⟨nf :: ys, a2, ?_, by simpa using hps3,
    hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state), hg12.trans hg3, hP2.fr hf3, hA3⟩
  rw [ConRon.Arena.targetMajorNfs, hrun_tail]
  simp only [ht, ite_true, StateT.run_bind, run2, except_ok_bind]; rfl

include hq henv in
/-- **`target_major_nfs` refines `targetMajorNfs`** under `StageC` (the knot's core calls; the
inputs' denotations as con-ron's `targetMajorNfs_spec` asks). -/
@[refines ConRon.Arena.targetMajorNfs]
theorem targetMajorNfs_refinesC (L : TmnLook p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (q fto ftl pfo pfl us dso dsl cto ctl nfo nfl : Word)
    (bs : BlockShape) (formerTys pfvs ds : List EIdx) (ctors : List (IConstantVal × Nat))
    (nfs : List NestCtorNf) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hbs : BSOK s₀.mem q.toNat bs) (hus : H us)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hpf : HSl0 s₀.mem pfo pfl pfvs) (hds : HSl0 s₀.mem dso dsl ds)
    (hct : PSlR decCN ctors cto ctl s₀.mem) (hnf : PSlR decNCN nfs nfo nfl s₀.mem) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP pfvsP dsP : List ConLeche.Expr}
    {usP : List ConLeche.Level} {ctorsP : List (ConLeche.ConstantVal × Nat)}
    {nfsP : List ConLeche.NestCtorNf}
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hpfP : Frontend.denoteEList a₀.store pfvs = some pfvsP)
    (husP : denoteLs a₀.store.lss (decI us) = some usP)
    (hdsP : Frontend.denoteEList a₀.store ds = some dsP) (hctP : dCtors a₀.store ctors = some ctorsP)
    (hnfP : nfs.mapM (dCtorNf a₀.store) = some nfsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hpw : ∀ x ∈ pfvsP, ConLeche.Expr.WScoped pfvsP.length x) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_major_nfs"
      [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo, nfl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a₀ ∧
      PSlR decNCN (AM.res (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a₀)
        (r.headD 0) (r.tail.headD 0) s'.mem ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.targetMajorNfs V fe bs formerTys pfvs (decI us) ds ctors nfs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (tmn_spec p L (realCall p) (realCall_spec p) n s₀ vis q fto ftl pfo pfl us dso dsl
    cto ctl nfo nfl) ?_
  rintro r s' ⟨hl', hm⟩
  obtain ⟨ys, a', run, hys, hC', hg, hP', hA'⟩ := tmnW_okC hq henv n hn hm hC hA hbs hus hft hftb hpf
    hds hct hnf hP hsh hftP hpfP husP hdsP hctP hnfP hformer hpw
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hres]; exact hys, by rw [hst]; exact hC', hg, hP', hA'⟩

end sims

end L.Ind
