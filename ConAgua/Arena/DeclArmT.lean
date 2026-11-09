module

import ConRon.Bridge.Checker.Arms
import ConRon.Bridge.Checker.Base
public import ConAgua.Verdict.DeclValsE
public import ConAgua.Arena.DeclStepGo
import all ConRon.Bridge.Checker.Inv
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.DeclValT
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.ModelGen
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.DeclStep

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
    (h : erecCiW n m i k = some (r, m')) : MemFrame [EREC, tier1 EREC] [129, 130] m m' := by
  cases n with
  | zero => simp [erecCiW] at h
  | succ n =>
  rw [erecCiW_step] at h
  cases h1 : erAllocW m (rdW (m.arr64 DECL) (4 + 8 * i)) with
  | none => rw [h1] at h; cases h
  | some x =>
  obtain ⟨s, m1⟩ := x
  rw [h1, eciK1_some] at h
  cases h2 : dlpCopyW n m1 s (1 + rdW (m.arr64 DECL) (3 + 8 * i)) (rdW (m.arr64 DECL) (4 + 8 * i)) with
  | none => rw [h2] at h; cases h
  | some m2 =>
  rw [h2, eciK2_some] at h
  cases h3 : erAllocW m2 8 with
  | none => rw [h3] at h; cases h
  | some x =>
  obtain ⟨p, m3⟩ := x
  rw [h3, eciK3_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have fA : ∀ {m m1 : Mem} {k q : Word}, erAllocW m k = some (q, m1) →
      MemFrame [EREC, tier1 EREC] [129, 130] m m1 := fun {m m1 k q} hh => by
    rw [erAllocW_mem hh]
    refine ⟨fun b _ hc => ?_, fun x hx => ?_, fun b => ?_⟩
    · unfold erAllocMem; split <;> exact Mem.arr64_set64_ne _ _ _ _ _ hc
    · unfold erAllocMem; split <;> simp only [rdW_set64] <;> grind
    · unfold erAllocMem; split <;> simp [Mem.size64_set64]
  have fW : ∀ (m : Mem) (q : Word) (ws : List Word), MemFrame [EREC, tier1 EREC] [129, 130] m (wrER m q ws) :=
    fun m q ws => (wrER_frame ws m q).mono (fun _ h => h) (fun _ h => by simp at h)
  rw [dlpCopyW_eq _ _ _ _ _ _ h2] at h3
  exact (((fA h1).trans (fW _ _ _)).trans (fA h3)).trans (by rw [eciMem_eq]; exact fW _ _ _)

/-- `StageT` across `erec_ci` (an `EREC` writer: `TwinOK.frame`). -/
theorem erecCiW_okT {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {i ck : Word} {r : List Word} {ds : Array IDeclaration}
    {ci : IConstantInfo}
    (h : erecCiW n m i ck = some (r, m')) (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hci : stepCI ck.toNat ds[i.toNat] = some ci) :
    StageT dn vis fe m' a ∧ IWGrow m m' ∧ decCI (erecP m') (r.headD 0).toNat = some ci ∧
      decCV (erecP m') ((r.headD 0).toNat + 1) = some (stepCV ds[i.toNat]) ∧
      hd? (erecP m') ((r.headD 0).toNat + 5) = some (stepVal ds[i.toNat]) ∧
      erOff (r.headD 0) + 8 ≤ erTopOf m' (r.headD 0) := by
  obtain ⟨hS', hg, h1, h2, h3, h4⟩ := erecCiW_ok h hS.stage hD hi hci
  have hf := erecCiW_frame h
  refine ⟨⟨hS', hS.twin.frame hf ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩ (by decide) hg,
    by simp only [pinW, hf.arr PINS (by decide) (by decide)]; exact hS.flag⟩, hg, h1, h2, h3, h4⟩

/-- `lvl_eq_c` at its text (`FireProg.lvlText`). -/
theorem _root_.L.Ind.KnotStageProg.lvlEqC {p : Prog} (hq : KnotStageProg p) :
    p.lookup "lvl_eq_c" = some lvlEqCL := by
  sorry

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_thm_val` refines `checkThmVal .verified`** under `StageT`, at the call: the stage
relation at the extended environment and the core's memos after it (the census link since lane
`indstaget`). -/
@[refines ConRon.Arena.checkThmVal]
theorem checkThmVal_refinesT (p : Prog) (hp : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis c : Word) (cv : IConstantVal) (v : EIdx) (hS : StageT dn vis fe s₀.mem a₀)
    (hc : decCI (erecP s₀.mem) c.toNat = some (.thmInfo cv))
    (hv : hd? (erecP s₀.mem) (c.toNat + 5) = some v)
    (hpre : ∃ env cP, ConLeche.EnvWF env ∧ ConRon.Bridge.CheckOK V env fe a₀ ∧
      Frontend.denoteCV a₀.store cv = some cP ∧ ConLeche.Expr.WScoped 0 cP.type)
    (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_thm_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkThmVal V fe cv v) a₀ ∧
      StageR (r.headD 0) (AM.res (checkThmVal V fe cv v) a₀) s'.mem
        (AM.st (checkThmVal V fe cv v) a₀) ∧ CoreMemos s'.mem ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_defn_val` refines `checkDefnVal .verified`** under `StageT`, at the arm's record
(`dv_ref`, `ov_ref`). -/
@[refines ConRon.Arena.checkDefnVal]
theorem checkDefnVal_refinesT (p : Prog) (hp : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis c : Word) (cv : IConstantVal) (v : EIdx) (hh : ConLeche.ReducibilityHint)
    (hS : StageT dn vis fe s₀.mem a₀)
    (hc : decCI (erecP s₀.mem) c.toNat = some (.defnInfo cv v hh))
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a₀.store.ns) = some ks)
    (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_defn_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkDefnVal V fe cv v hh) a₀ ∧
      StageR (r.headD 0) (AM.res (checkDefnVal V fe cv v hh) a₀) s'.mem
        (AM.st (checkDefnVal V fe cv v hh) a₀) ∧ CoreMemos s'.mem ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_opaque_val` refines `checkOpaqueVal .verified`** under `StageT`, at the arm's record
(`dv_ref`, `ov_ref`). -/
@[refines ConRon.Arena.checkOpaqueVal]
theorem checkOpaqueVal_refinesT (p : Prog) (hp : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis c : Word) (cv : IConstantVal) (v : EIdx) (hS : StageT dn vis fe s₀.mem a₀)
    (hc : decCI (erecP s₀.mem) c.toNat = some (.axiomInfo cv))
    (hv : hd? (erecP s₀.mem) (c.toNat + 5) = some v)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a₀.store.ns) = some ks)
    (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_opaque_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkOpaqueVal V fe cv v) a₀ ∧
      StageR (r.headD 0) (AM.res (checkOpaqueVal V fe cv v) a₀) s'.mem
        (AM.st (checkOpaqueVal V fe cv v) a₀) ∧ CoreMemos s'.mem ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
-/

/-- What the theorem arm's error arms assume: `check_constant_val`'s (`VerdictCtxU`), and
`install_value_guards`' claim for `check_thm_val`'s (`TvCtx`). -/
structure CdtCtx (p : Prog) : Prop extends VerdictCtxU p where

-- RS2B ronsync2 stage 2: commented out (statement at the old twin/L)
theorem CdtCtx.tv {p : Prog} (h : CdtCtx p) : TvCtx p := by
  sorry

-- RS2E

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
-/

/-- What `install_value`'s error arms assume: `install_header`'s (`IhCtx`) and
`install_value_guards`' claim. -/
structure IvCtx (p : Prog) : Prop where
  nv : closedNV p L.Checker.nvFns = true
  uce : UceProg p

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- What `install_value` gives besides the twin's run: the stage at the extended environment,
the core's memos, the growth, the value group's record. -/
structure IvPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (v : List Word × Mem)
    (y : IFEnv × Option ValueGroup) (a' : AState) : Prop where
  stage : StageR (v.1.headD 0) y.1 v.2 a'
  memos : CoreMemos v.2
  grow : IWGrow m v.2
  vg : y.2 = decVG (erecP v.2) (v.1.tail.headD 0).toNat
  some : y.2 ≠ none
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
-/

end L.Arena
