module

public import ConRon.Bridge.Checker.Arms
public import ConRon.Bridge.Checker.Base
public import ConAgua.Verdict.DeclValsE
public import ConAgua.Arena.DeclStepGo
public import ConRon.Bridge.Checker.Split
import all ConRon.Bridge.Checker.Inv

@[expose] public section

/-!
# The declaration arms under `StageT` (lane `loopt2`)

`DeclArm*.lean`'s arms run from the stage relation, the core's entry points read through their
stubs. Here they run from `StageT`, reading the program's own calls (`realCall p`), through the
`StageT` versions of the value checks (`DeclValT.lean`). An arm's post is the stage relation at its
environment and the core's memos well formed (`CoreMemos`): after an arm no core call follows in
the step, and the loop re-derives the twin's invariants at the next declaration.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


noncomputable section

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)

local notation "V" => ConLeche.CheckMode.verified

/-- **`erec_ci` writes the record pool and its top** (`EREC`, `CTL[129]`). -/
theorem erecCiW_frame {n : Nat} {m m' : Mem} {i k : Word} {r : List Word}
    (h : erecCiW n m i k = some (r, m')) : MemFrame [EREC] [129] m m' := by
  cases n with
  | zero => simp [erecCiW] at h
  | succ n =>
  rw [erecCiW_step] at h
  cases h1 : L.Ind.erAllocW m (rdW (m.arr64 DECL) (4 + 8 * i)) with
  | none => rw [h1] at h; cases h
  | some q1 =>
  obtain ⟨s, m1⟩ := q1
  rw [h1, eciK1_some] at h
  cases h2 : dlpCopyW n m1 s (1 + rdW (m.arr64 DECL) (3 + 8 * i)) (rdW (m.arr64 DECL) (4 + 8 * i)) with
  | none => rw [h2] at h; cases h
  | some m2 =>
  rw [h2, eciK2_some] at h
  cases h3 : L.Ind.erAllocW m2 8 with
  | none => rw [h3] at h; cases h
  | some q3 =>
  obtain ⟨p, m3⟩ := q3
  rw [h3, eciK3_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have fA : ∀ {x y : Mem} {k : Word} {o : Word}, L.Ind.erAllocW x k = some (o, y) →
      MemFrame [EREC] [129] x y := by
    intro x y k o hx
    rw [erAllocW_mem hx]
    exact (MemFrame.setCtl x 129 _).mono (by simp) (by simp)
  have f2 : MemFrame [EREC] [129] m1 m2 := by
    rw [dlpCopyW_eq n m1 m2 _ _ _ h2]; exact (wrER_frame _ _ _).mono (by simp) (by simp)
  have f4 : MemFrame [EREC] [129] m3 (eciMem m3 p i k s (rdW (m.arr64 DECL) (4 + 8 * i))) := by
    rw [eciMem_eq]; exact (wrER_frame _ _ _).mono (by simp) (by simp)
  exact (((fA h1).trans f2).trans (fA h3)).trans f4

/-- `StageT` across `erec_ci` (an `EREC` writer: `TwinOK.frame`). -/
theorem erecCiW_okT {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {i ck : Word} {r : List Word} {ds : Array IDeclaration}
    {ci : IConstantInfo}
    (h : erecCiW n m i ck = some (r, m')) (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hci : stepCI ck.toNat ds[i.toNat] = some ci) :
    StageT dn vis fe m' a ∧ IWGrow m m' ∧ decCI (erecP m') dn (r.headD 0).toNat = some ci ∧
      decCV (erecP m') ((r.headD 0).toNat + 1) = some (stepCV ds[i.toNat]) ∧
      hd? (erecP m') ((r.headD 0).toNat + 5) = some (stepVal ds[i.toNat]) ∧
      (r.headD 0).toNat + 8 ≤ erTop m' := by
  obtain ⟨hS', hg, h1, h2, h3, h4⟩ := erecCiW_ok h hS.stage hD hi hci
  have hf := erecCiW_frame h
  refine ⟨⟨hS', hS.twin.frame hf ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩,
    by simp only [pinW, hf.arr PINS (by decide) (by decide)]; exact hS.flag⟩, hg, h1, h2, h3, h4⟩

/-- `lvl_eq_c` at its text (`FireProg.lvlText`). -/
theorem _root_.L.Ind.KnotStageProg.lvlEqC {p : Prog} (hq : KnotStageProg p) :
    p.lookup "lvl_eq_c" = some lvlEqCL :=
  (hq.knot.fire.lvlText _ (by decide)).trans rfl

/-- **`check_constant_val` refines `checkConstantVal .verified`** under `StageT`, at the call (the
census link since lane `indstaget`). -/
@[refines ConRon.Arena.checkConstantVal]
theorem checkConstantVal_refinesT (p : Prog) (hp : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis q : Word) (cv : IConstantVal) (hS : StageT dn vis fe s₀.mem a₀)
    (hqd : decCV (erecP s₀.mem) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a₀.store.ns) = some ks) (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_constant_val" [vis, q]
    ⦃fun _r s' => LocEq s' s₀ ∧ AM.ok (checkConstantVal V fe cv) a₀ ∧
      StageT dn vis fe s'.mem (AM.st (checkConstantVal V fe cv) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      L.Stubs.CrOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (checkConstantVal_specE p hp n s₀ vis q)
    (ccv_ref hq hap hkp hn hS hqd hqb hlps hCr)) ?_
  rintro r s' ⟨hl, _, a', hrun, hP⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hP.stage, hP.grow, hP.crOK⟩

/-- **`check_thm_val` refines `checkThmVal .verified`** under `StageT`, at the call: the stage
relation at the extended environment and the core's memos after it (the census link since lane
`indstaget`). -/
@[refines ConRon.Arena.checkThmVal]
theorem checkThmVal_refinesT (p : Prog) (hp : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis c : Word) (cv : IConstantVal) (v : EIdx) (hS : StageT dn vis fe s₀.mem a₀)
    (hc : decCI (erecP s₀.mem) dn c.toNat = some (.thmInfo cv))
    (hv : hd? (erecP s₀.mem) (c.toNat + 5) = some v)
    (hpre : ∃ env cP, ConLeche.EnvWF env ∧ ConRon.Bridge.CheckOK V env fe a₀ ∧
      Frontend.denoteCV a₀.store cv = some cP ∧ ConLeche.Expr.WScoped 0 cP.type)
    (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_thm_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkThmVal V fe cv v) a₀ ∧
      StageR dn (r.headD 0) (AM.res (checkThmVal V fe cv v) a₀) s'.mem
        (AM.st (checkThmVal V fe cv v) a₀) ∧ CoreMemos s'.mem ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (checkThmVal_specE p hp n s₀ vis c)
    (tv_ref hq hp hap hkp hn hS hc hv hpre hCr)) ?_
  rintro r s' ⟨hl, fe', a', hrun, hP⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hP.stage, hP.memos, hP.grow⟩

/-- **`check_defn_val` refines `checkDefnVal .verified`** under `StageT`, at the arm's record
(`dv_ref`, `ov_ref`). -/
@[refines ConRon.Arena.checkDefnVal]
theorem checkDefnVal_refinesT (p : Prog) (hp : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis c : Word) (cv : IConstantVal) (v : EIdx) (hh : ConLeche.ReducibilityHint)
    (hS : StageT dn vis fe s₀.mem a₀)
    (hc : decCI (erecP s₀.mem) dn c.toNat = some (.defnInfo cv v hh))
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a₀.store.ns) = some ks)
    (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_defn_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkDefnVal V fe cv v hh) a₀ ∧
      StageR dn (r.headD 0) (AM.res (checkDefnVal V fe cv v hh) a₀) s'.mem
        (AM.st (checkDefnVal V fe cv v hh) a₀) ∧ CoreMemos s'.mem ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  obtain ⟨hcv, hv⟩ := decls_decCI_defn hc
  refine triple_post (RefE.triple (checkDefnVal_specE p hp n s₀ vis c)
    (dv_ref hq hp hap hkp hn "type mismatch in definition" hS hc hcv hv hlps hCr)) ?_
  rintro r s' ⟨hl, y, a', hrun, hP⟩
  rw [← checkDefnVal_dvT] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres, hP.res]; exact hP.stage, hP.memos, hP.grow⟩

/-- **`check_opaque_val` refines `checkOpaqueVal .verified`** under `StageT`, at the arm's record
(`dv_ref`, `ov_ref`). -/
@[refines ConRon.Arena.checkOpaqueVal]
theorem checkOpaqueVal_refinesT (p : Prog) (hp : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis c : Word) (cv : IConstantVal) (v : EIdx) (hS : StageT dn vis fe s₀.mem a₀)
    (hc : decCI (erecP s₀.mem) dn c.toNat = some (.axiomInfo cv))
    (hv : hd? (erecP s₀.mem) (c.toNat + 5) = some v)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a₀.store.ns) = some ks)
    (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_opaque_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkOpaqueVal V fe cv v) a₀ ∧
      StageR dn (r.headD 0) (AM.res (checkOpaqueVal V fe cv v) a₀) s'.mem
        (AM.st (checkOpaqueVal V fe cv v) a₀) ∧ CoreMemos s'.mem ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  have hcv := decCI_cvTA hc (.inr rfl)
  refine triple_post (RefE.triple (checkOpaqueVal_specE p hp n s₀ vis c)
    (ov_ref hq hp hap hkp hn "type mismatch in opaque" hS hc hcv hv hlps hCr)) ?_
  rintro r s' ⟨hl, y, a', hrun, hP⟩
  rw [← checkOpaqueVal_dvT] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres, hP.res]; exact hP.stage, hP.memos, hP.grow⟩

set_option experimental.vcgen true in
/-- **The model of `check_decl_thm`, both outcomes**: `erec_ci` lifted, `check_constant_val` and
`check_thm_val` by their unified models. -/
l_model checkDeclThm_specE (p : Prog) (hV : ValProg p)
  (hf : p.lookup "check_decl_thm" = some checkDeclThm)
  fns [hf ↦ checkDeclThmE]
  specs [erecCi_specW p hV.rcp n, checkConstantVal_specE p hV n, checkThmVal_specE p hV n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What the theorem arm's error arms assume: `check_constant_val`'s (`VerdictCtxU`), and
`install_value_guards`' claim for `check_thm_val`'s (`TvCtx`). -/
structure CdtCtx (p : Prog) : Prop extends VerdictCtxU p where
  ivg : IvgE p

theorem CdtCtx.tv {p : Prog} (h : CdtCtx p) : TvCtx p :=
  ⟨h.core, h.ivg, fun _ _ _ _ he =>
    callE_nv h.nv (_root_.L.Checker.nv_mem (f := "lvl_eq_c") (by decide +kernel)) _ _ _ he⟩

/-- **The theorem arm `check_decl_thm` refines `checkDecl` on a theorem under `StageT`, both
outcomes** (`ccv_ref`, then `tv_ref`). -/
theorem cdt_ref {p : Prog} (hV : ValProg p) (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {env : ConLeche.Env} {c : ConLeche.ConstantVal}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {i : Word}
    {ds : Array IDeclaration} {pins : List INatOpPinSet} {cv : IConstantVal} {v : EIdx}
    (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .thmDecl cv v) (hfold : ConRon.Bridge.FoldOK V env fe a)
    (hcvd : Frontend.denoteCV a.store cv = some c) (hCr : L.Stubs.CrOK m) :
    RefE (CdtCtx p) (checkDeclThmE p n m i vis) (checkDecl V pins fe (.thmDecl cv v)) a
      (fun x fe' a' => ArmPost dn m x.1 x.2 fe' a') := by
  cases n with
  | zero => rw [checkDeclThmE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkDeclThmE.arm1]
  show RefE _ _ (do checkConstantVal V fe cv; checkThmVal V fe cv v) a _
  refine RefE.onlySim (fun _ => checkDeclThmE.k_erec_ci.none ..) (fun _ _ h => h) fun r1 m1 h1 => ?_
  rw [checkDeclThmE.k_erec_ci.arm1]
  have hCr1 := CrOK.frame hCr (erecCiW_frame h1) (by decide) (by decide)
  obtain ⟨hS1, hg1, hci1, hcv1, hval1, htop1⟩ :=
    erecCiW_okT (ci := .thmInfo cv) h1 hS hD hi (by rw [hd]; rfl)
  rw [hd] at hcv1 hval1
  simp only [stepCV, stepVal] at hcv1 hval1
  generalize hq0 : r1.headD 0 = q at hci1 hcv1 hval1 htop1 ⊢
  have hqb : q.toNat + 8 < 2 ^ 64 := by
    have := hS1.stage.iw.er; have := hS1.stage.iw.erSize; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 (by omega)
  -- `check_constant_val(vis, q + 1)`
  refine RefE.bindE (fun _ => checkDeclThmE.k_check_constant_val.none ..) (fun hG => hG.toVerdictCtxU)
    (ccv_ref hq hap hkp hn' hS1 (by rw [hq1]; exact hcv1) (by omega) (denoteCV_lps hcvd) hCr1)
    fun ⟨r2, m2⟩ u2 a2 hrun2 hP2 => ?_
  rw [checkDeclThmE.k_check_constant_val.arm1]
  obtain ⟨hstep1, _F1, hpure1⟩ :=
    ConRon.Bridge.checkConstantVal_bridge_of_fold rfl (ConRon.Bridge.CoreSpec.of_core rfl) hfold hcvd hrun2
  have hok1 := hfold.ofCore hstep1
  have hcA := ConRon.Bridge.denoteCV_ext hcvd hstep1.ext
  have hwsT : ConLeche.Expr.WScoped 0 c.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar (ConRon.Bridge.checkConstantVal_typeWF hpure1).fvar
  -- `check_thm_val(vis, q)`
  have hx2 : ArrExt (erecP m1) (erecP m2) := IWGrow.erecPExt hP2.grow
  exact RefE.lastE (K := id) (fun _ => rfl) (fun _ => rfl) (fun hG => hG.tv)
    (tv_ref hq hV hap hkp hn' hP2.stage (ArrExt.decCI hx2 hci1) (ArrExt.hd? hx2 hval1)
      ⟨env, c, hok1.envWF, hok1.check, hcA, hwsT⟩ hP2.crOK)
    fun _ _ _ _ hP3 => ⟨hP3.stage, hP3.memos, hg1.trans (hP2.grow.trans hP3.grow)⟩

/-- **`erec_vg` writes the record pool and its top.** -/
theorem erecVgW_frame {m m' : Mem} {q vk : Word} {r : List Word} (h : erecVgW m q vk = some (r, m')) :
    MemFrame [EREC] [129] m m' := by
  unfold erecVgW at h
  split at h
  · cases h
  rename_i g m1 h1
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have f1 : MemFrame [EREC] [129] m m1 := by
    rw [erAllocW_mem h1]; exact (MemFrame.setCtl m 129 _).mono (by simp) (by simp)
  have fs : ∀ (x : Mem) (j : Word), MemFrame [EREC] [129] x (vgSet x g q j) := fun x j =>
    (MemFrame.set64 x EREC (by decide) _ _).mono (by simp) (by simp)
  have f0 : MemFrame [EREC] [129] m1 (m1.set64 EREC g vk) :=
    (MemFrame.set64 m1 EREC (by decide) g vk).mono (by simp) (by simp)
  exact (((((f1.trans f0).trans (fs _ 1)).trans (fs _ 2)).trans (fs _ 3)).trans (fs _ 4)).trans
    (fs _ 5)

set_option experimental.vcgen true in
/-- **The model of `install_value`, both outcomes**: `erec_ci`, `erec_vg` lifted, `install_header`
by its unified model, `install_value_guards` and `env_push` through their runs. -/
l_model installValue_specE (p : Prog) (hP : IvProg p)
  fns [hP.iv ↦ installValueE list]
  specs [erecCi_specW p hP.recP n, installHeader_specE p hP.ih n, erecVg_specW p hP.recP n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `install_value`'s error arms assume: `install_header`'s (`IhCtx`) and
`install_value_guards`' claim. -/
structure IvCtx (p : Prog) : Prop where
  nv : closedNV p L.Checker.nvFns = true
  uce : UceProg p
  ivg : IvgE p

/-- `install_value`'s twin for a record of kind `vk`: the header, the value's guards unless a
theorem (`vk = 1`), the push. `ivT` of each kind is this (`ivT_eq_core`). -/
def ivCoreT (fe : IFEnv) (cv : IConstantVal) (v : EIdx) (vk : Word) (ci : IConstantInfo)
    (k : ValueKind) : AM (IFEnv × Option ValueGroup) := do
  installHeader fe cv
  if vk ≠ 1 then installValueGuards fe cv v else pure ()
  pure (fe.push ci, some ⟨k, cv, v⟩)

/-- What `install_value` gives besides the twin's run: the stage at the extended environment,
the core's memos, the growth, the value group's record. -/
structure IvPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (v : List Word × Mem)
    (y : IFEnv × Option ValueGroup) (a' : AState) : Prop where
  stage : StageR dn (v.1.headD 0) y.1 v.2 a'
  memos : CoreMemos v.2
  grow : IWGrow m v.2
  vg : y.2 = decVG (erecP v.2) (v.1.tail.headD 0).toNat
  some : y.2 ≠ none

/-- **`install_value` refines `ivCoreT`, both outcomes**, under `StageT`: `install_header` by
`ih_ref`, the value's guards by `ivg_ref`; after the push the stage
relation at the extended environment and `CoreMemos`. -/
theorem ivc_ref {p : Prog} (hRp : RecProg p) (hC : CvgProg p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} (n : Nat) {m : Mem} {i ck vk : Word}
    {ds : Array IDeclaration} {ci : IConstantInfo} {k : ValueKind} {env : ConLeche.Env}
    {c : ConLeche.ConstantVal} (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hci : stepCI ck.toNat ds[i.toNat] = some ci) (hk : decVK vk.toNat = some k)
    (hfold : ConRon.Bridge.FoldOK V env fe a)
    (hcvd : Frontend.denoteCV a.store (stepCV ds[i.toNat]) = some c) (hCr : L.Stubs.CrOK m) :
    RefE (IvCtx p) (installValueE p n m i vis ck vk)
      (ivCoreT fe (stepCV ds[i.toNat]) (stepVal ds[i.toNat]) vk ci k) a
      (fun v y a' => IvPost dn m v y a') := by
  cases n with
  | zero => rw [installValueE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  rw [installValueE.arm1]
  refine RefE.onlySim (fun _ => installValueE.k_erec_ci.none ..) (fun _ _ h => h) fun r1 m1 h1 => ?_
  rw [installValueE.k_erec_ci.arm1]
  have hCr1 := CrOK.frame hCr (erecCiW_frame h1) (by decide) (by decide)
  obtain ⟨hS1, hg1, hci1, hcv1, hval1, htop1⟩ := erecCiW_okT h1 hS hD hi hci
  generalize hq : r1.headD 0 = q at hci1 hcv1 hval1 htop1 ⊢
  have hb : q.toNat + 8 < 2 ^ 64 := by
    have h1 := hS1.stage.iw.er; have h2 := hS1.stage.iw.erSize; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  -- `install_header(vis, q + 1)`
  simp only [ivCoreT]
  refine RefE.bindE (fun _ => installValueE.k_install_header.none ..) (fun hG => ⟨hG.nv, hG.uce⟩)
    (ih_ref hap hkp.crf n hS1 (by rw [hq1]; exact hcv1) (by rw [hq1]; omega) (denoteCV_lps hcvd) hCr1)
    fun ⟨r2, m2⟩ _ a2 hrun2 hP2 => ?_
  -- the parameters' names read back after the header: con-ron's `installHeader_bridge`
  have hlps2 : ∃ ks, (stepCV ds[i.toNat]).levelParams.mapM (denoteN a2.store.ns) = some ks := by
    obtain ⟨hstep, -⟩ := ConRon.Bridge.installHeader_bridge hfold hcvd hrun2
    exact denoteCV_lps (ConRon.Bridge.denoteCV_ext hcvd hstep.ext)
  have tail : ∀ (m3 : Mem) (a3 : AState), StageT dn vis fe m3 a3 → IWGrow m1 m3 →
      RefE (IvCtx p) (installValueE.j1 p n vis vk q m3)
        (pure (fe.push ci, some ⟨k, stepCV ds[i.toNat], stepVal ds[i.toNat]⟩) : AM _) a3
        (fun v y a' => IvPost dn m v y a') := by
    intro m3 a3 hS3 hg3
    rw [installValueE.j1.arm1]
    have hx3 : ArrExt (erecP m1) (erecP m3) := IWGrow.erecPExt hg3
    have hci3 := ArrExt.decCI hx3 hci1
    obtain ⟨w, hw1, hwl, -⟩ := decCI_name hci3
    have hw : (rdW (m3.arr64 EREC) (q + 1)).toNat < 2 ^ 32 := by
      rw [rdW_of_get? hq1.symm (erecP_get hw1)]; exact hwl
    rcases h4 : callE p n "env_push" [vis, q] m3 with e4 | ⟨r4, m4⟩
    · rw [installValueE.k_env_push.none]
      exact fun hG => nvl hG.nv (by decide +kernel) h4
    rw [installValueE.k_env_push.arm1]
    obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (envPush_specW p hRp n ⟨m3, Locals.init []⟩ vis q hw) (callW_of_callE h4)
    subst hs4
    obtain ⟨hS4, hg4⟩ := envPushW_ok hW4 hS3.stage hci3
    have hM4 : CoreMemos s4.mem := hS3.twin.memos.frame (envPushW_frame hW4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    refine RefE.onlySim (fun _ => installValueE.k_erec_vg.none ..) (fun _ _ h => h) fun r5 m5 h5 => ?_
    rw [installValueE.k_erec_vg.arm1]
    have hx4 : ArrExt (erecP m1) (erecP s4.mem) := IWGrow.erecPExt (hg3.trans hg4)
    have htop4 : q.toNat + 8 ≤ erTop s4.mem := by
      have := (hg3.trans hg4).er; omega
    obtain ⟨hS5, hg5, hvg⟩ := erecVgW_ok h5 hS4 (ArrExt.decCV hx4 hcv1) (ArrExt.hd? hx4 hval1)
      htop4 hk
    have hM5 : CoreMemos m5 := hM4.frame (erecVgW_frame h5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact RefE.ret rfl ⟨by simpa using hS5, hM5, hg1.trans (hg3.trans (hg4.trans hg5)),
      by simpa using hvg.symm, by simp⟩
  by_cases hv1 : vk ≠ 1
  · rw [installValueE.k_install_header.arm1 p _ _ _ _ _ _ hv1, ite_eq_left hv1]
    have hval2 : hd? (erecP m2) (q.toNat + 5) = some (stepVal ds[i.toNat]) :=
      ArrExt.hd? (IWGrow.erecPExt hP2.grow) hval1
    obtain ⟨wv, hwv, hwvl, hwvd⟩ := hd?_some hval2
    have hq5 : (q + 5).toNat = q.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
    have ev : rdW (m2.arr64 EREC) (q + 5) = wv := rdW_of_get? hq5.symm (erecP_get hwv)
    rw [ev]
    have hcv2 : decCV (erA m2) (q + 1).toNat = some (stepCV ds[i.toNat]) := by
      rw [hq1]; exact ArrExt.decCV (IWGrow.erecExt hP2.grow) hcv1
    rcases h3 : callE p n "install_value_guards" [vis, q + 1, wv] m2 with e3 | ⟨r3, m3⟩
    · rw [installValueE.k_install_value_guards.none]
      refine RefE.bind_left fun hG => ?_
      rw [hwvd]
      exact hG.ivg h3 hP2.stage hcv2 (by rw [hq1]; omega) hwvl hlps2 hP2.crOK
    rw [installValueE.k_install_value_guards.arm1]
    obtain ⟨s3, hs3, -, _, a3, hrun3, hS3, hg3, -⟩ := RefE.run_ok
      (s₀ := ⟨m2, Locals.init []⟩)
      (installValueGuards_specE p hC n _ vis (q + 1) wv)
      (ivg_ref hap hkp.crf n hP2.stage hcv2 (by rw [hq1]; omega) hwvl hlps2 hP2.crOK) h3
    subst hs3
    rw [← hwvd] at hrun3
    exact RefE.bind_right hrun3 (tail _ a3 hS3 (hP2.grow.trans hg3))
  · rw [installValueE.k_install_header.arm2 p _ _ _ _ _ _ (by simpa using hv1), ite_eq_right hv1]
    exact tail m2 a2 hP2.stage hP2.grow

/-- **`install_value` refines `ivT`, both outcomes** (`ivc_ref` at the record's kind). -/
theorem iv_ref {p : Prog} (hRp : RecProg p) (hC : CvgProg p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} (n : Nat) {m : Mem} {i ck vk : Word}
    {ds : Array IDeclaration} (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hk : IvArgs ck vk (dsAt ds i)) (hF : ∃ env, ConRon.Bridge.FoldOK V env fe a)
    (hcvd : ∃ c, Frontend.denoteCV a.store (stepCV (dsAt ds i)) = some c) (hCr : L.Stubs.CrOK m) :
    RefE (IvCtx p) (installValueE p n m i vis ck vk) (ivT fe (dsAt ds i)) a
      (fun v y a' => IvPost dn m v y a') := by
  have hd : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
  rw [hd] at hk hcvd ⊢
  obtain ⟨env, hF⟩ := hF
  obtain ⟨c, hcvd⟩ := hcvd
  cases hdi : ds[i.toNat] with
  | defnDecl cv v hint =>
    rw [hdi] at hk
    obtain ⟨rfl, rfl⟩ := hk
    refine RefE.of_run_eq ?_ (ivc_ref (ci := .defnInfo cv v hint) (k := .defn) hRp hC hap hkp n hS
      hD hi (by rw [hdi]; rfl) rfl hF hcvd hCr)
    simp [hdi, ivT, ivCoreT, stepCV, stepVal]
  | thmDecl cv v =>
    rw [hdi] at hk
    obtain ⟨rfl, rfl⟩ := hk
    refine RefE.of_run_eq ?_ (ivc_ref (ci := .thmInfo cv) (k := .thm) hRp hC hap hkp n hS
      hD hi (by rw [hdi]; rfl) rfl hF hcvd hCr)
    simp [hdi, ivT, ivCoreT, stepCV, stepVal]
  | opaqueDecl cv v =>
    rw [hdi] at hk
    obtain ⟨rfl, rfl⟩ := hk
    refine RefE.of_run_eq ?_ (ivc_ref (ci := .axiomInfo cv) (k := .opaque) hRp hC hap hkp n hS
      hD hi (by rw [hdi]; rfl) rfl hF hcvd hCr)
    simp [hdi, ivT, ivCoreT, stepCV, stepVal]
  | axiomDecl _ => rw [hdi] at hk; exact hk.elim
  | quotDecl _ _ => rw [hdi] at hk; exact hk.elim
  | indDecl _ _ => rw [hdi] at hk; exact hk.elim
  | basisDecl _ => rw [hdi] at hk; exact hk.elim

end L.Arena
