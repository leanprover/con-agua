import ConAgua.Verdict.DeclHdrE
import ConAgua.Arena.DeclArmT

/-!
# The verdict claims of `check_constant_val`, `check_defn_val`, `check_opaque_val` (lane
`verdicts-b`, helper `d`)

Under the hypotheses of the ok refinements (`checkConstantVal_refinesT`, `checkDefnVal_refinesT`,
`checkOpaqueVal_refinesT`) and the callees' error claims (`CoreStubsE`, `IvgE`; `install_header`
by `ihE_okT`).
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

l_model checkConstantVal_specE (p : Prog)
  (hf : p.lookup "check_constant_val" = some checkConstantValL)
  fns [hf ↦ checkConstantValE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model checkDefnVal_specE (p : Prog)
  (hf : p.lookup "check_defn_val" = some checkDefnValL)
  fns [hf ↦ checkDefnValE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model checkOpaqueVal_specE (p : Prog)
  (hf : p.lookup "check_opaque_val" = some checkOpaqueValL)
  fns [hf ↦ checkOpaqueValE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

/-- **`check_constant_val`'s error claim under `StageT`**: `install_header` by `ihE_okT`, the core
stubs by `CoreStubsE`. -/
theorem ccvE_okT {p : Prog} (hq : KnotStageProg p) (hp : ValProg p) (hap : ApdF p)
    (hkp : CrKeep p) (hnv : closedNV p L.Checker.nvFns = true) (hcE : CoreStubsE p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {q : Word} {cv : IConstantVal} {e : Err}
    (hc : callE p n "check_constant_val" [vis, q] m = .error e) (hS : StageT dn vis fe m a)
    (hqd : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    ErrClaim (checkConstantVal V fe cv) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkConstantVal_specE p hp.ccv n ⟨m, Locals.init []⟩ vis q) hc
    (Err.code_ne_of_cls hk0)
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hqd
  have et : rdW (m.arr64 EREC) (q + 3) = wt :=
    rdW_of_get? (k := q.toNat + 3) (toNat_add_small q 3 hqb).symm (erecP_get hwt)
  cases n with
  | zero => rw [checkConstantValE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkConstantValE.arm1, et] at hW
  rw [checkConstantVal_eq]
  -- `install_header(vis, q)`
  cases h1 : callE p n "install_header" [vis, q] m with
  | error e1 =>
    rw [h1, checkConstantValE.k_install_header.eq_1] at hW; cases hW
    exact ErrClaim.bind_left (ihE_okT hp.ih hap hkp hnv h1 hS hqd hqb hlps hCr)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, checkConstantValE.k_install_header.eq_2] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE
    (ih_specW p hp.ih (realCall p) (realCall_spec p) n ⟨m, Locals.init []⟩ vis q) h1
  subst hs1
  obtain ⟨a1, hrun1, hS1, hg1, hCr1, -⟩ := ihW_okT hap hkp.crf hW1 hS hqd hqb hlps hCr
  refine ErrClaim.bind_right hrun1 ?_
  -- the type's type
  cases h2 : callE p n "infer_type_core" [vis, 0, wt] s1.mem with
  | error e2 =>
    rw [h2, checkConstantValE.k_infer_type_core.eq_1] at hW; cases hW
    have := hcE.inferTypeCore n hn' hS1 0 wt hwtl _ h2
    rw [show ((0 : Word).toNat) = 0 from rfl, ← hty] at this
    exact ErrClaim.bind_left this
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, checkConstantValE.k_infer_type_core.eq_2] at hW
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    hq.inferTypeCore_sim n hn' hS1 0 wt hwtl r2 m2 (callW_of_callE h2)
  rw [show ((0 : Word).toNat) = 0 from rfl, ← hty] at hrun2
  refine ErrClaim.bind_right hrun2 ?_
  -- its sort
  cases h3 : callE p n "ensure_sort_core" [vis, 0, r2.headD 0] m2 with
  | error e3 =>
    rw [h3, checkConstantValE.k_ensure_sort_core.eq_1] at hW; cases hW
    have := hcE.ensureSortCore n hn' hS2 0 (r2.headD 0) hx2l _ h3
    rw [show ((0 : Word).toNat) = 0 from rfl, hx2] at this
    exact ErrClaim.bind_left this
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, checkConstantValE.k_ensure_sort_core.eq_2] at hW
  cases hW

/-- **`check_defn_val`'s error claim under `StageT`**: the value's guards by `IvgE`, the core
stubs by `CoreStubsE`, the type mismatch is the twin's `invalid`; `env_push` claims nothing. -/
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
    ErrClaim (checkDefnVal V fe cv v hh) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkDefnVal_specE p hp.dv n ⟨m, Locals.init []⟩ vis c) hce
    (Err.code_ne_of_cls hk0)
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hcb : c.toNat + 5 < 2 ^ 64 := erecP_bound hwv hS.stage.2
  have ev : rdW (m.arr64 EREC) (c + 5) = wv :=
    rdW_of_get? (toNat_add_small c 5 (by omega)).symm (erecP_get hwv)
  have et : rdW (m.arr64 EREC) (c + 4) = wt :=
    rdW_of_get? (toNat_add_small c 4 (by omega)).symm (erecP_get (by simpa [Nat.add_assoc] using hwt))
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  cases n with
  | zero => rw [checkDefnValE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkDefnValE.arm1, ev, et] at hW
  rw [checkDefnVal_dvT]
  unfold dvT
  have h00 : (0 : Word).toNat = 0 := rfl
  -- `install_value_guards(vis, c + 1, v)`
  cases h1 : callE p n "install_value_guards" [vis, c + 1, wv] m with
  | error e1 =>
    rw [h1, checkDefnValE.k_install_value_guards.none] at hW; cases hW
    exact ErrClaim.bind_left (hivE h1 hS (by rw [hc1]; exact ArrExt.decCV (erecP_ext m) hcv)
      (by rw [hc1]; omega) hwvl hlps hCr)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, checkDefnValE.k_install_value_guards.eq_2] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE
    (ivg_specW p hp.cvg (realCall p) (realCall_spec p) n ⟨m, Locals.init []⟩ vis (c + 1) wv) h1
  subst hs1
  obtain ⟨a1, hrun1, hS1, hg1, -⟩ :=
    ivgW_okT hap hkp hW1 hS (by rw [hc1]; exact ArrExt.decCV (erecP_ext m) hcv)
      (by rw [hc1]; omega) hwvl hlps hCr
  refine ErrClaim.bind_right hrun1 ?_
  -- the value's type
  cases h2 : callE p n "infer_type_core" [vis, 0, wv] s1.mem with
  | error e2 =>
    rw [h2, checkDefnValE.k_infer_type_core.eq_1] at hW; cases hW
    have := hcE.inferTypeCore n hn' hS1 0 wv hwvl _ h2
    rw [h00] at this
    exact ErrClaim.bind_left this
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, checkDefnValE.k_infer_type_core.eq_2] at hW
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    hq.inferTypeCore_sim n hn' hS1 0 wv hwvl r2 m2 (callW_of_callE h2)
  rw [h00] at hrun2
  refine ErrClaim.bind_right hrun2 ?_
  -- the comparison with the declared type
  cases h3 : callE p n "is_def_eq_core" [vis, 0, r2.headD 0, wt] m2 with
  | error e3 =>
    rw [h3, checkDefnValE.k_is_def_eq_core.eq_1] at hW; cases hW
    have := hcE.isDefEqCore n hn' hS2 0 (r2.headD 0) wt hx2l hwtl _ h3
    rw [h00, hx2, ← hty] at this
    exact ErrClaim.bind_left this
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3] at hW
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ :=
    hq.isDefEqCore_sim n hn' hS2 0 (r2.headD 0) wt hx2l hwtl r3 m3 (callW_of_callE h3)
  rw [h00, hx2, ← hty] at hrun3
  refine ErrClaim.bind_right hrun3 ?_
  by_cases hb3 : r3.headD 0 = 0
  · rw [checkDefnValE.k_is_def_eq_core.abort1 p n vis c r3 m3 hb3] at hW
    cases hW
    have ex3 : x3 = false := by rw [← hx3, decBool, hb3]; rfl
    rw [ex3]
    exact ErrClaim.bind_left (ErrClaim.fail _ _ rfl)
  rw [checkDefnValE.k_is_def_eq_core.arm1 p n vis c r3 m3 hb3] at hW
  cases h4 : callE p n "env_push" [vis, c] m3 with
  | error e4 =>
    rw [h4, checkDefnValE.k_env_push.none] at hW; cases hW
    exact ErrClaim.of_cls0 (hnvE _ _ _ _ h4)
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, checkDefnValE.k_env_push.arm1] at hW
  cases hW

/-- **`check_opaque_val`'s error claim under `StageT`**: the value's guards by `IvgE`, the core
stubs by `CoreStubsE`, the type mismatch is the twin's `invalid`; `env_push` claims nothing. -/
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
    ErrClaim (checkOpaqueVal V fe cv v) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkOpaqueVal_specE p hp.ov n ⟨m, Locals.init []⟩ vis c) hce
    (Err.code_ne_of_cls hk0)
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hcb : c.toNat + 5 < 2 ^ 64 := erecP_bound hwv hS.stage.2
  have ev : rdW (m.arr64 EREC) (c + 5) = wv :=
    rdW_of_get? (toNat_add_small c 5 (by omega)).symm (erecP_get hwv)
  have et : rdW (m.arr64 EREC) (c + 4) = wt :=
    rdW_of_get? (toNat_add_small c 4 (by omega)).symm (erecP_get (by simpa [Nat.add_assoc] using hwt))
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  cases n with
  | zero => rw [checkOpaqueValE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkOpaqueValE.arm1, ev, et] at hW
  rw [checkOpaqueVal_dvT]
  unfold dvT
  have h00 : (0 : Word).toNat = 0 := rfl
  -- `install_value_guards(vis, c + 1, v)`
  cases h1 : callE p n "install_value_guards" [vis, c + 1, wv] m with
  | error e1 =>
    rw [h1, checkOpaqueValE.k_install_value_guards.none] at hW; cases hW
    exact ErrClaim.bind_left (hivE h1 hS (by rw [hc1]; exact ArrExt.decCV (erecP_ext m) hcv)
      (by rw [hc1]; omega) hwvl hlps hCr)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, checkOpaqueValE.k_install_value_guards.eq_2] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE
    (ivg_specW p hp.cvg (realCall p) (realCall_spec p) n ⟨m, Locals.init []⟩ vis (c + 1) wv) h1
  subst hs1
  obtain ⟨a1, hrun1, hS1, hg1, -⟩ :=
    ivgW_okT hap hkp hW1 hS (by rw [hc1]; exact ArrExt.decCV (erecP_ext m) hcv)
      (by rw [hc1]; omega) hwvl hlps hCr
  refine ErrClaim.bind_right hrun1 ?_
  -- the value's type
  cases h2 : callE p n "infer_type_core" [vis, 0, wv] s1.mem with
  | error e2 =>
    rw [h2, checkOpaqueValE.k_infer_type_core.eq_1] at hW; cases hW
    have := hcE.inferTypeCore n hn' hS1 0 wv hwvl _ h2
    rw [h00] at this
    exact ErrClaim.bind_left this
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, checkOpaqueValE.k_infer_type_core.eq_2] at hW
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    hq.inferTypeCore_sim n hn' hS1 0 wv hwvl r2 m2 (callW_of_callE h2)
  rw [h00] at hrun2
  refine ErrClaim.bind_right hrun2 ?_
  -- the comparison with the declared type
  cases h3 : callE p n "is_def_eq_core" [vis, 0, r2.headD 0, wt] m2 with
  | error e3 =>
    rw [h3, checkOpaqueValE.k_is_def_eq_core.eq_1] at hW; cases hW
    have := hcE.isDefEqCore n hn' hS2 0 (r2.headD 0) wt hx2l hwtl _ h3
    rw [h00, hx2, ← hty] at this
    exact ErrClaim.bind_left this
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3] at hW
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ :=
    hq.isDefEqCore_sim n hn' hS2 0 (r2.headD 0) wt hx2l hwtl r3 m3 (callW_of_callE h3)
  rw [h00, hx2, ← hty] at hrun3
  refine ErrClaim.bind_right hrun3 ?_
  by_cases hb3 : r3.headD 0 = 0
  · rw [checkOpaqueValE.k_is_def_eq_core.abort1 p n vis c r3 m3 hb3] at hW
    cases hW
    have ex3 : x3 = false := by rw [← hx3, decBool, hb3]; rfl
    rw [ex3]
    exact ErrClaim.bind_left (ErrClaim.fail _ _ rfl)
  rw [checkOpaqueValE.k_is_def_eq_core.arm1 p n vis c r3 m3 hb3] at hW
  cases h4 : callE p n "env_push" [vis, c] m3 with
  | error e4 =>
    rw [h4, checkOpaqueValE.k_env_push.none] at hW; cases hW
    exact ErrClaim.of_cls0 (hnvE _ _ _ _ h4)
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, checkOpaqueValE.k_env_push.arm1] at hW
  cases hW

end L.Arena
