import ConAgua.Arena.DeclValT
import ConAgua.Verdict.DeclHdrE
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

/-!
# `check_constant_val`'s refinement; the verdict claims of `check_defn_val`, `check_opaque_val`

`check_constant_val`: one unified model and one refinement for both outcomes (`ccv_ref`), its error
claim `ccvE_okT` from it. `check_defn_val`, `check_opaque_val`: error claims under the hypotheses
of the ok refinements (`checkDefnVal_refinesT`, `checkOpaqueVal_refinesT`) and the callees' error
claims (`CoreStubsE`, `IvgE`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- **The model of `check_constant_val`, both outcomes**: `install_header` by its unified model,
the core stubs through their runs. -/
l_model checkConstantVal_specE (p : Prog) (hp : ValProg p)
  fns [hp.ccv ↦ checkConstantValE] specs [installHeader_specE p hp.ih n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The model of `check_defn_val`, both outcomes**: its callees through their runs. -/
l_model checkDefnVal_specE (p : Prog) (hp : ValProg p)
  fns [hp.dv ↦ checkDefnValE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] unified

/-- **The model of `check_opaque_val`, both outcomes**: its callees through their runs. -/
l_model checkOpaqueVal_specE (p : Prog) (hp : ValProg p)
  fns [hp.ov ↦ checkOpaqueValE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] unified

/-- What `check_constant_val` gives besides the twin's run: the stage, the growth, the memos; the
walk memos (`AbsOK`) kept. -/
structure CcvPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a' : AState) : Prop where
  stage : StageT dn vis fe m' a'
  grow : IWGrow m m'
  crOK : L.Stubs.CrOK m'
  abs : AbsOK m → AbsOK m'

/-- **`check_constant_val` refines `checkConstantVal .verified`, both outcomes**, under `StageT`:
`install_header` by `ih_ref`, the core stubs by `KnotStageProg` (ok) and `CoreStubsE` (errors). -/
theorem ccv_ref {p : Prog} (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {q : Word} {cv : IConstantVal}
    (hS : StageT dn vis fe m a) (hqd : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkConstantValE p n m vis q) (checkConstantVal V fe cv) a
      (fun v _ a' => CcvPost dn vis fe m v.2 a') := by
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hqd
  have et : rdW (m.arr64 EREC) (q + 3) = wt :=
    rdW_of_get? (k := q.toNat + 3) (toNat_add_small q 3 hqb).symm (erecP_get hwt)
  cases n with
  | zero => rw [checkConstantValE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkConstantValE.arm1, et, checkConstantVal_eq]
  -- `install_header(vis, q)`
  have h1R := ih_ref hap hkp.crf n hS hqd hqb hlps hCr
  rcases h1 : installHeaderE p n m vis q with e1 | ⟨r1, m1⟩
  · rw [checkConstantValE.k_install_header.none]
    rw [h1] at h1R
    exact RefE.bind_left fun hG => h1R ⟨hG.nv, hG.uce⟩
  rw [checkConstantValE.k_install_header.arm1]
  rw [h1] at h1R
  obtain ⟨_, a1, hrun1, hP1⟩ := h1R
  refine RefE.bind_right hrun1 ?_
  -- the type's type
  rcases h2 : callE p n "infer_type_core" [vis, 0, wt] m1 with e2 | ⟨r2, m2⟩
  · rw [checkConstantValE.k_infer_type_core.none]
    intro hG
    have := hG.core.inferTypeCore n hn' hP1.stage 0 wt hwtl _ h2
    rw [show ((0 : Word).toNat) = 0 from rfl, ← hty] at this
    exact ErrClaim.bind_left this
  rw [checkConstantValE.k_infer_type_core.arm1]
  have h2w := callW_of_callE h2
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ := hq.inferTypeCore_sim n hn' hP1.stage 0 wt hwtl r2 m2 h2w
  have hCr2 := hkp.call (im_mem _ rfl) h2w hP1.crOK
  rw [show ((0 : Word).toNat) = 0 from rfl, ← hty] at hrun2
  refine RefE.bind_right hrun2 ?_
  -- its sort
  rcases h3 : callE p n "ensure_sort_core" [vis, 0, r2.headD 0] m2 with e3 | ⟨r3, m3⟩
  · rw [checkConstantValE.k_ensure_sort_core.none]
    intro hG
    have := hG.core.ensureSortCore n hn' hS2 0 (r2.headD 0) hx2l _ h3
    rw [show ((0 : Word).toNat) = 0 from rfl, hx2] at this
    exact ErrClaim.bind_left this
  rw [checkConstantValE.k_ensure_sort_core.arm1]
  have h3w := callW_of_callE h3
  obtain ⟨x3, a3, hrun3, hS3, hg3, -⟩ := hq.ensureSortCore_sim n hn' hS2 0 (r2.headD 0) hx2l r3 m3 h3w
  have hCr3 := hkp.call (im_mem _ rfl) h3w hCr2
  rw [show ((0 : Word).toNat) = 0 from rfl, hx2] at hrun3
  refine RefE.bind_right hrun3 (RefE.ret rfl ⟨hS3, hP1.grow.trans (hg2.trans hg3), hCr3, ?_⟩)
  intro hA
  exact absOK_core hq.closed (by decide) h3w
    (absOK_core hq.closed (by decide) h2w (hP1.afr hA) hS2) hS3

/-- **`check_constant_val`'s error claim under `StageT`** (`ccv_ref`'s error half). -/
theorem ccvE_okT {p : Prog} (hq : KnotStageProg p) (hp : ValProg p) (hap : ApdF p)
    (hkp : CrKeep p) (hnv : closedNV p L.Checker.nvFns = true) (hcE : CoreStubsE p)
    (hUL : UceLookups p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {q : Word} {cv : IConstantVal} {e : Err}
    (hc : callE p n "check_constant_val" [vis, q] m = .error e) (hS : StageT dn vis fe m a)
    (hqd : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    ErrClaim (checkConstantVal V fe cv) a e :=
  RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkConstantVal_specE p hp n _ vis q) hnv
    ⟨⟨hnv, hcE⟩, ⟨hUL, strLitSupported_core p hq.knot.str⟩⟩
    (ccv_ref hq hap hkp hn hS hqd hqb hlps hCr) hc

/-- What `check_defn_val`'s and `check_opaque_val`'s error arms assume: `env_push` outside the
verdict closure, the core stubs' and `install_value_guards`' claims. -/
structure DvCtx (p : Prog) : Prop where
  env : NVAt p "env_push"
  core : CoreStubsE p
  ivg : IvgE p

/-- What `check_defn_val`/`check_opaque_val` give besides the twin's run: the stage at the
extended environment `fe'` (the twin's result), the core's memos, the growth. -/
structure DvPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (fe' : IFEnv) (w : Word × Mem)
    (y : IFEnv) (a' : AState) : Prop where
  stage : StageR dn w.1 fe' w.2 a'
  memos : CoreMemos w.2
  grow : IWGrow m w.2
  res : y = fe'

/-- **`check_defn_val` refines its twin `dvT …`, both outcomes**, under `StageT`: the value's guards
by `ivg_ref`, the core stubs by `KnotStageProg` and `CoreStubsE`, the
type mismatch the twin's `invalid`; after the push the stage at the extended environment. -/
theorem dv_ref {p : Prog} (hq : KnotStageProg p) (hp : ValProg p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c : Word} {cv : IConstantVal} {v : EIdx}
    {ci : IConstantInfo} (msg : String) (hS : StageT dn vis fe m a)
    (hci : decCI (erecP m) dn c.toNat = some ci) (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    RefE (DvCtx p) (checkDefnValE p n m vis c) (dvT fe cv v ci msg) a
      (fun w y a' => DvPost dn m (fe.push ci) w y a') := by
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hcb : c.toNat + 5 < 2 ^ 64 := erecP_bound hwv hS.stage.2
  have ev : rdW (m.arr64 EREC) (c + 5) = wv :=
    rdW_of_get? (toNat_add_small c 5 (by omega)).symm (erecP_get hwv)
  have et : rdW (m.arr64 EREC) (c + 4) = wt :=
    rdW_of_get? (toNat_add_small c 4 (by omega)).symm (erecP_get (by simpa [Nat.add_assoc] using hwt))
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  cases n with
  | zero => rw [checkDefnValE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkDefnValE.arm1, ev, et]
  unfold dvT
  have h00 : (0 : Word).toNat = 0 := rfl
  -- `install_value_guards(vis, c + 1, v)`
  rcases h1 : callE p n "install_value_guards" [vis, c + 1, wv] m with e1 | ⟨r1, m1⟩
  · rw [checkDefnValE.k_install_value_guards.none]
    exact RefE.bind_left fun hG => hG.ivg h1 hS (by rw [hc1]; exact ArrExt.decCV (erecP_ext m) hcv)
      (by rw [hc1]; omega) hwvl hlps hCr
  rw [checkDefnValE.k_install_value_guards.arm1]
  obtain ⟨s1, hs1, -, _, a1, hrun1, hS1, hg1, -⟩ := RefE.run_ok
    (s₀ := ⟨m, Locals.init []⟩)
    (installValueGuards_specE p hp.cvg n _ vis (c + 1) wv)
    (ivg_ref hap hkp.crf n hS (by rw [hc1]; exact ArrExt.decCV (erecP_ext m) hcv)
      (by rw [hc1]; omega) hwvl hlps hCr) h1
  subst hs1
  refine RefE.bind_right hrun1 ?_
  -- the value's type
  rcases h2 : callE p n "infer_type_core" [vis, 0, wv] s1.mem with e2 | ⟨r2, m2⟩
  · rw [checkDefnValE.k_infer_type_core.none]
    intro hG
    have := hG.core.inferTypeCore n hn' hS1 0 wv hwvl _ h2
    rw [h00] at this
    exact ErrClaim.bind_left this
  rw [checkDefnValE.k_infer_type_core.arm1]
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    hq.inferTypeCore_sim n hn' hS1 0 wv hwvl r2 m2 (callW_of_callE h2)
  rw [h00] at hrun2
  refine RefE.bind_right hrun2 ?_
  -- the comparison with the declared type
  rcases h3 : callE p n "is_def_eq_core" [vis, 0, r2.headD 0, wt] m2 with e3 | ⟨r3, m3⟩
  · rw [checkDefnValE.k_is_def_eq_core.none]
    intro hG
    have := hG.core.isDefEqCore n hn' hS2 0 (r2.headD 0) wt hx2l hwtl _ h3
    rw [h00, hx2, ← hty] at this
    exact ErrClaim.bind_left this
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ :=
    hq.isDefEqCore_sim n hn' hS2 0 (r2.headD 0) wt hx2l hwtl r3 m3 (callW_of_callE h3)
  rw [h00, hx2, ← hty] at hrun3
  refine RefE.bind_right hrun3 ?_
  by_cases hb3 : r3.headD 0 = 0
  · rw [checkDefnValE.k_is_def_eq_core.abort1 p n vis c r3 m3 hb3]
    have ex3 : x3 = false := by rw [← hx3, decBool, hb3]; rfl
    rw [ex3]
    exact fun _ => ErrClaim.bind_left (ErrClaim.fail _ _ rfl)
  rw [checkDefnValE.k_is_def_eq_core.arm1 p n vis c r3 m3 hb3]
  have ex3 : x3 = true := by rw [← hx3]; simpa [decBool] using hb3
  rw [ex3]
  -- the push
  have hx13 : ArrExt (erecP m) (erecP m3) := IWGrow.erecPExt (hg1.trans (hg2.trans hg3))
  have hci3 := ArrExt.decCI hx13 hci
  obtain ⟨w, hw1, hwl, -⟩ := decCI_name hci3
  have hw : (rdW (m3.arr64 EREC) (c + 1)).toNat < 2 ^ 32 := by
    rw [rdW_of_get? hc1.symm (erecP_get hw1)]; exact hwl
  rcases h4 : callE p n "env_push" [vis, c] m3 with e4 | ⟨r4, m4⟩
  · rw [checkDefnValE.k_env_push.none]; exact fun hG => ErrClaim.of_cls0 (hG.env _ _ _ _ h4)
  rw [checkDefnValE.k_env_push.arm1]
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (envPush_specW p hp.rcp n ⟨m3, Locals.init []⟩ vis c hw) (callW_of_callE h4)
  subst hs4
  obtain ⟨hS4, hg4⟩ := envPushW_ok hW4 hS3.stage hci3
  have hM4 : CoreMemos s4.mem := hS3.twin.memos.frame (envPushW_frame hW4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact RefE.ret rfl ⟨by simpa using hS4, hM4, hg1.trans (hg2.trans (hg3.trans hg4)), rfl⟩

/-- **`check_opaque_val` refines its twin `dvT …`, both outcomes**, under `StageT`: the value's guards
by `ivg_ref`, the core stubs by `KnotStageProg` and `CoreStubsE`, the
type mismatch the twin's `invalid`; after the push the stage at the extended environment. -/
theorem ov_ref {p : Prog} (hq : KnotStageProg p) (hp : ValProg p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c : Word} {cv : IConstantVal} {v : EIdx}
    {ci : IConstantInfo} (msg : String) (hS : StageT dn vis fe m a)
    (hci : decCI (erecP m) dn c.toNat = some ci) (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    RefE (DvCtx p) (checkOpaqueValE p n m vis c) (dvT fe cv v ci msg) a
      (fun w y a' => DvPost dn m (fe.push ci) w y a') := by
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hcb : c.toNat + 5 < 2 ^ 64 := erecP_bound hwv hS.stage.2
  have ev : rdW (m.arr64 EREC) (c + 5) = wv :=
    rdW_of_get? (toNat_add_small c 5 (by omega)).symm (erecP_get hwv)
  have et : rdW (m.arr64 EREC) (c + 4) = wt :=
    rdW_of_get? (toNat_add_small c 4 (by omega)).symm (erecP_get (by simpa [Nat.add_assoc] using hwt))
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  cases n with
  | zero => rw [checkOpaqueValE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkOpaqueValE.arm1, ev, et]
  unfold dvT
  have h00 : (0 : Word).toNat = 0 := rfl
  -- `install_value_guards(vis, c + 1, v)`
  rcases h1 : callE p n "install_value_guards" [vis, c + 1, wv] m with e1 | ⟨r1, m1⟩
  · rw [checkOpaqueValE.k_install_value_guards.none]
    exact RefE.bind_left fun hG => hG.ivg h1 hS (by rw [hc1]; exact ArrExt.decCV (erecP_ext m) hcv)
      (by rw [hc1]; omega) hwvl hlps hCr
  rw [checkOpaqueValE.k_install_value_guards.arm1]
  obtain ⟨s1, hs1, -, _, a1, hrun1, hS1, hg1, -⟩ := RefE.run_ok
    (s₀ := ⟨m, Locals.init []⟩)
    (installValueGuards_specE p hp.cvg n _ vis (c + 1) wv)
    (ivg_ref hap hkp.crf n hS (by rw [hc1]; exact ArrExt.decCV (erecP_ext m) hcv)
      (by rw [hc1]; omega) hwvl hlps hCr) h1
  subst hs1
  refine RefE.bind_right hrun1 ?_
  -- the value's type
  rcases h2 : callE p n "infer_type_core" [vis, 0, wv] s1.mem with e2 | ⟨r2, m2⟩
  · rw [checkOpaqueValE.k_infer_type_core.none]
    intro hG
    have := hG.core.inferTypeCore n hn' hS1 0 wv hwvl _ h2
    rw [h00] at this
    exact ErrClaim.bind_left this
  rw [checkOpaqueValE.k_infer_type_core.arm1]
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    hq.inferTypeCore_sim n hn' hS1 0 wv hwvl r2 m2 (callW_of_callE h2)
  rw [h00] at hrun2
  refine RefE.bind_right hrun2 ?_
  -- the comparison with the declared type
  rcases h3 : callE p n "is_def_eq_core" [vis, 0, r2.headD 0, wt] m2 with e3 | ⟨r3, m3⟩
  · rw [checkOpaqueValE.k_is_def_eq_core.none]
    intro hG
    have := hG.core.isDefEqCore n hn' hS2 0 (r2.headD 0) wt hx2l hwtl _ h3
    rw [h00, hx2, ← hty] at this
    exact ErrClaim.bind_left this
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ :=
    hq.isDefEqCore_sim n hn' hS2 0 (r2.headD 0) wt hx2l hwtl r3 m3 (callW_of_callE h3)
  rw [h00, hx2, ← hty] at hrun3
  refine RefE.bind_right hrun3 ?_
  by_cases hb3 : r3.headD 0 = 0
  · rw [checkOpaqueValE.k_is_def_eq_core.abort1 p n vis c r3 m3 hb3]
    have ex3 : x3 = false := by rw [← hx3, decBool, hb3]; rfl
    rw [ex3]
    exact fun _ => ErrClaim.bind_left (ErrClaim.fail _ _ rfl)
  rw [checkOpaqueValE.k_is_def_eq_core.arm1 p n vis c r3 m3 hb3]
  have ex3 : x3 = true := by rw [← hx3]; simpa [decBool] using hb3
  rw [ex3]
  -- the push
  have hx13 : ArrExt (erecP m) (erecP m3) := IWGrow.erecPExt (hg1.trans (hg2.trans hg3))
  have hci3 := ArrExt.decCI hx13 hci
  obtain ⟨w, hw1, hwl, -⟩ := decCI_name hci3
  have hw : (rdW (m3.arr64 EREC) (c + 1)).toNat < 2 ^ 32 := by
    rw [rdW_of_get? hc1.symm (erecP_get hw1)]; exact hwl
  rcases h4 : callE p n "env_push" [vis, c] m3 with e4 | ⟨r4, m4⟩
  · rw [checkOpaqueValE.k_env_push.none]; exact fun hG => ErrClaim.of_cls0 (hG.env _ _ _ _ h4)
  rw [checkOpaqueValE.k_env_push.arm1]
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (envPush_specW p hp.rcp n ⟨m3, Locals.init []⟩ vis c hw) (callW_of_callE h4)
  subst hs4
  obtain ⟨hS4, hg4⟩ := envPushW_ok hW4 hS3.stage hci3
  have hM4 : CoreMemos s4.mem := hS3.twin.memos.frame (envPushW_frame hW4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact RefE.ret rfl ⟨by simpa using hS4, hM4, hg1.trans (hg2.trans (hg3.trans hg4)), rfl⟩

/-- **`check_defn_val`'s error claim under `StageT`** (`dv_ref`'s error half). -/
theorem defnvE_okT {p : Prog} (hq : KnotStageProg p) (hp : ValProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hcE : CoreStubsE p) (hivE : IvgE p) (hnvE : NVAt p "env_push")
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c : Word} {cv : IConstantVal} {v : EIdx}
    (hh : ConLeche.ReducibilityHint) (hS : StageT dn vis fe m a)
    (hc : decCI (erecP m) dn c.toNat = some (.defnInfo cv v hh))
    (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m)
    {e : Err} (hce : callE p n "check_defn_val" [vis, c] m = .error e) :
    ErrClaim (checkDefnVal V fe cv v hh) a e :=
  RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkDefnVal_specE p hp n _ vis c) trivial
    ⟨hnvE, hcE, hivE⟩ (dv_ref hq hp hap hkp hn _ hS hc hcv hv hlps hCr) hce

/-- **`check_opaque_val`'s error claim under `StageT`** (`ov_ref`'s error half). -/
theorem opaquevE_okT {p : Prog} (hq : KnotStageProg p) (hp : ValProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hcE : CoreStubsE p) (hivE : IvgE p) (hnvE : NVAt p "env_push")
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c : Word} {cv : IConstantVal} {v : EIdx}
    (hS : StageT dn vis fe m a)
    (hc : decCI (erecP m) dn c.toNat = some (.axiomInfo cv))
    (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m)
    {e : Err} (hce : callE p n "check_opaque_val" [vis, c] m = .error e) :
    ErrClaim (checkOpaqueVal V fe cv v) a e :=
  RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkOpaqueVal_specE p hp n _ vis c) trivial
    ⟨hnvE, hcE, hivE⟩ (ov_ref hq hp hap hkp hn _ hS hc hcv hv hlps hCr) hce

end L.Arena
