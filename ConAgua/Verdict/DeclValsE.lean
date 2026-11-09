module

public import ConAgua.Verdict.DeclHdrE
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.DeclValT
import ConAgua.Arena.IndT.Base
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.DeclValRef
public import ConAgua.Arena.DeclBasisSpec
public import ConAgua.Arena.QuotAtT
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# `check_constant_val`'s refinement; the verdict claims of `check_defn_val`, `check_opaque_val`

`check_constant_val`: one unified model and one refinement for both outcomes (`ccv_ref`).
`check_defn_val`, `check_opaque_val`: one refinement over both models (`dvo_ref`, on `dvoE`),
and error claims under the hypotheses
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

/-- The lookups `check_constant_val`'s refinement takes. -/
structure CcvProg (p : Prog) : Prop where
  val : ValProg p
  resF : p.lookup "reserved_from" = some reservedFrom
  resC : p.lookup "reserved_contains" = some reservedContains
  cont : p.lookup "sl_contains" = some slContains
  nodup : p.lookup "sl_nodup" = some slNodup
  basis : BasisProg p

/-- **The model of `check_constant_val`, both outcomes**: the callees outside the verdict closure
with `Option` models through those models, the gates `all_level_params_defined`,
`consts_resolve_ffast` and the core through `callE`. -/
l_model checkConstantVal_specE (p : Prog) (hp : CcvProg p)
  fns [hp.val.ccv ↦ checkConstantValE]
  specs [callW_spec p n "env_find", resCont_spec p hp.resF hp.resC n, callW_spec p n "nat_op_name",
    callW_spec p n "erec_alloc", callW_spec p n "erec_put",
    callW_spec p n "lit_shape_ok",
    cvLps_specW p hp.val.cvg.alloc hp.val.cvg.copy hp.val.cvg.eti hp.val.cvg.lps n,
    slNodup_spec p hp.cont hp.nodup n, lbbF_spec p hp.val.cvg.bvb n, hffF_spec p hp.val.cvg.hf n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The model of `check_defn_val`, both outcomes**: its callees through their runs. -/
l_model checkDefnVal_specE (p : Prog) (hp : ValProg p)
  fns [hp.dv ↦ checkDefnValE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified

/-- **The model of `check_opaque_val`, both outcomes**: its callees through their runs. -/
l_model checkOpaqueVal_specE (p : Prog) (hp : ValProg p)
  fns [hp.ov ↦ checkOpaqueValE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified

theorem word_add11 (d : Word) : d + 1 + 1 = d + 2 := by rw [UInt64.add_assoc]; rfl
theorem word_add31 (d : Word) : d + 3 + 1 = d + 4 := by rw [UInt64.add_assoc]; rfl

/-- **The fresh `axiomInfo cv` record `check_constant_val` builds for `lit_shape_ok`**:
`erec_alloc(5)`, then the kind word `0` and the four words of the constant value at `q` (name,
the universe parameters' slice, type) copied above the top: `StageT` kept, the pools grown, only
the record pool and its tops written, the record decoding to `axiomInfo cv`. -/
theorem ccv_rec {p : Prog} (hp : RecProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m1 m2 m3 m4 m5 m6 : Mem} {q nw t : Word}
    {cv : IConstantVal} {r1 r2 r3 r4 r5 r6 : List Word}
    (hS : StageT dn vis fe m a) (hqd : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hw0 : erecP m q.toNat = some nw) (hw3 : erecP m (q.toNat + 3) = some t)
    (h1 : callW p n "erec_alloc" [5] m = some (r1, m1))
    (h2 : callW p n "erec_put" [r1.headD 0, 0] m1 = some (r2, m2))
    (h3 : callW p n "erec_put" [r1.headD 0 + 1, nw] m2 = some (r3, m3))
    (h4 : callW p n "erec_put" [r1.headD 0 + 2,
      rdW (m3.arr64 (L.tierA EREC ((q + 1) >>> 40))) (q + 1 &&& 1099511627775)] m3 = some (r4, m4))
    (h5 : callW p n "erec_put" [r1.headD 0 + 3,
      rdW (m4.arr64 (L.tierA EREC ((q + 2) >>> 40))) (q + 2 &&& 1099511627775)] m4 = some (r5, m5))
    (h6 : callW p n "erec_put" [r1.headD 0 + 4, t] m5 = some (r6, m6)) :
    StageT dn vis fe m6 a ∧ IWGrow m m6 ∧ MemFrame [EREC, tier1 EREC] [129, 130] m m6 ∧
      decCI (erecP m6) (r1.headD 0).toNat = some (.axiomInfo cv) := by
  have hA := callW_erecAlloc hp.alloc h1
  generalize r1.headD 0 = A at hA h2 h3 h4 h5 h6 ⊢
  obtain ⟨hT1, hg1, hoff, htop, h41⟩ := erAlloc_stageT hA hS
  have hf1 : MemFrame [] [129, 130] m m1 := (erAllocW_spec hA hS.stage.iw).2.1
  rw [callW_erecPut hp.put h2] at h3
  rw [callW_erecPut hp.put h3] at h4
  rw [callW_erecPut hp.put h4] at h5
  rw [callW_erecPut hp.put h5] at h6
  rw [callW_erecPut hp.put h6]
  -- the source words, read below the top
  have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hq2 : (q + 2).toNat = q.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨w1, hw1⟩ : ∃ w, erecP m (q.toNat + 1) = some w := by
    simp only [decCV, hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff, nat?, Option.map_eq_some_iff] at hqd
    obtain ⟨_, _, _, ⟨_, ⟨w, hw, -⟩, _⟩, _⟩ := hqd; exact ⟨w, hw⟩
  obtain ⟨w2, hw2⟩ : ∃ w, erecP m (q.toNat + 2) = some w := by
    simp only [decCV, hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff, nat?, Option.map_eq_some_iff] at hqd
    obtain ⟨_, _, _, ⟨_, _, _, ⟨w, hw, -⟩, _⟩, _⟩ := hqd; exact ⟨w, hw⟩
  have hfq : MemFrame quotA quotC m m1 :=
    hf1.mono (fun _ h => by simp at h) (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> decide)
  have h5n : (5 : Word).toNat = 5 := rfl
  have htop' : erOff A + 5 ≤ erTopOf m1 A := by rw [htop]; omega
  have hbase : erTopOf m A ≤ erOff A := by omega
  -- the copied slice words, read before the copy
  obtain ⟨-, hgP2, -, -, -⟩ := wrER_fresh hS.stage [0, nw] m1 a A hT1.stage hfq hg1 hbase
    (by simp; omega) h41
  have hx2 : rdW ((wrER m1 A [0, nw]).arr64 (L.tierA EREC ((q + 1) >>> 40))) (q + 1 &&& 1099511627775)
      = w1 := by
    rw [erRdT_congr rfl rfl]; exact erRdT_of _ _ (by rw [hq1]; exact hgP2.ext _ _ hw1)
  have e3 : erecPutMem (erecPutMem m1 A 0) (A + 1) nw = wrER m1 A [0, nw] := rfl
  rw [e3, hx2] at h5 h6 ⊢
  have e4 : erecPutMem (wrER m1 A [0, nw]) (A + 2) w1 = wrER m1 A [0, nw, w1] := by
    simp only [wrER, word_add11]
  rw [e4] at h5 h6 ⊢
  obtain ⟨-, hgP3, -, -, -⟩ := wrER_fresh hS.stage [0, nw, w1] m1 a A hT1.stage hfq hg1 hbase
    (by simp; omega) h41
  have hx3 : rdW ((wrER m1 A [0, nw, w1]).arr64 (L.tierA EREC ((q + 2) >>> 40))) (q + 2 &&& 1099511627775)
      = w2 := by
    rw [erRdT_congr rfl rfl]; exact erRdT_of _ _ (by rw [hq2]; exact hgP3.ext _ _ hw2)
  rw [hx3]
  have e6 : erecPutMem (erecPutMem (wrER m1 A [0, nw, w1]) (A + 3) w2) (A + 4) t =
      wrER m1 A [0, nw, w1, w2, t] := by
    simp only [wrER, word_add11, word_add21, word_add31]
  rw [e6]
  obtain ⟨hS6, hg6, -, hrd, -⟩ := wrER_fresh hS.stage [0, nw, w1, w2, t] m1 a A hT1.stage hfq hg1 hbase
    (by simp; omega) h41
  refine ⟨StageT.of_wrER hT1 hS6, hg6,
    (hf1.mono (fun _ h => by simp at h) (fun _ h => h)).trans
      ((wrER_frame _ _ _).mono (fun _ h => h) (fun _ h => by simp at h)), ?_⟩
  have r0 := hrd 0 (by simp)
  have r1 := hrd 1 (by simp)
  have r2 := hrd 2 (by simp)
  have r3 := hrd 3 (by simp)
  have r4 := hrd 4 (by simp)
  simp only [Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ] at r0 r1 r2 r3 r4
  have hcv6 : decCV (erecP (wrER m1 A [0, nw, w1, w2, t])) (A.toNat + 1) = some cv :=
    L.Arena.decCV_move hg6.ext (by rw [r1, hw0]) (by rw [show A.toNat + 1 + 1 = A.toNat + 2 by omega, r2, hw1])
      (by rw [show A.toNat + 1 + 2 = A.toNat + 3 by omega, r3, hw2])
      (by rw [show A.toNat + 1 + 3 = A.toNat + 4 by omega, r4, hw3]) hqd
  have hk0 : nat? (erecP (wrER m1 A [0, nw, w1, w2, t])) A.toNat = some 0 := by simp [nat?, r0]
  simp [decCI, hk0, hcv6]

/-- What `check_constant_val` gives besides the twin's run: the stage, the growth, the memos; the
walk memos (`AbsOK`) kept. -/
structure CcvPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a' : AState) : Prop where
  stage : StageT dn vis fe m' a'
  grow : IWGrow m m'
  crOK : L.Stubs.CrOK m'
  abs : AbsOK m → AbsOK m'

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
  rw [checkConstantValE.arm1, et, checkConstantVal_eq, hty]
  -- `install_header(vis, q)`
  refine RefE.bindE (fun _ => rfl) (fun hG => ⟨hG.nv, hG.uce⟩) (ih_ref hap hkp.crf n hS hqd hqb hlps hCr)
    fun ⟨r1, m1⟩ _ a1 _ hP1 => ?_
  dsimp only [checkConstantValE.k_install_header]
  -- the type's type
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h2 => hG.core.inferTypeCore n hn' hP1.stage 0 wt hwtl _ h2)
    (fun b h2 => hq.inferTypeCore_sim n hn' hP1.stage 0 wt hwtl b.1 b.2 h2)
    fun r2 m2 x2 a2 h2 _ ⟨hS2, hg2, hx2l, hx2⟩ => ?_
  dsimp only [checkConstantValE.k_infer_type_core]
  have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hP1.crOK
  subst hx2
  -- its sort
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h3 => hG.core.ensureSortCore n hn' hS2 0 (r2.headD 0) hx2l _ h3)
    (fun b h3 => hq.ensureSortCore_sim n hn' hS2 0 (r2.headD 0) hx2l b.1 b.2 h3)
    fun r3 m3 _ a3 h3 _ ⟨hS3, hg3, _⟩ => ?_
  dsimp only [checkConstantValE.k_ensure_sort_core]
  refine RefE.ret rfl ⟨hS3, hP1.grow.trans (hg2.trans hg3),
    hkp.call (im_mem _ rfl) (callW_of_callE h3) hCr2, fun hA => ?_⟩
  exact absOK_core hq.closed (by decide) (callW_of_callE h3)
    (absOK_core hq.closed (by decide) (callW_of_callE h2) (hP1.afr hA) hS2) hS3
-/

/-- What `check_defn_val`'s and `check_opaque_val`'s error arms assume: `env_push` outside the
verdict closure, the core stubs' and `install_value_guards`' claims. -/
structure DvCtx (p : Prog) : Prop where
  env : NVAt p "env_push"
  core : CoreStubsE p

/-- What `check_defn_val`/`check_opaque_val` give besides the twin's run: the stage at the
extended environment `fe'` (the twin's result), the core's memos, the growth. -/
structure DvPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (fe' : IFEnv) (w : Word × Mem)
    (y : IFEnv) (a' : AState) : Prop where
  stage : StageR w.1 fe' w.2 a'
  memos : CoreMemos w.2
  grow : IWGrow m w.2
  res : y = fe'

/-! `dvoE k`: `checkDefnValE` and `checkOpaqueValE` with the mismatch's abort code `k` a
parameter. The two L functions have the same text but for that code (as their twins are `dvT` but
for the message), so one refinement (`dvo_ref`) serves both; `checkDefnValE_dvo` and
`checkOpaqueValE_dvo` are definitional. -/

/-- `dvoE`'s continuation after `env_push`. -/
def dvoE.k_env_push : Except Err (List Word × Mem) → Except Err (Word × Mem)
  | .error ε => .error ε
  | .ok (r, m₁) => .ok (r.headD 0, m₁)

/-- `dvoE`'s continuation after `is_def_eq_core`: the mismatch guard. -/
def dvoE.k_is_def_eq_core (k : Word) (p : Prog) (n : Nat) (vis c : Word) :
    Except Err (List Word × Mem) → Except Err (Word × Mem)
  | .error ε => .error ε
  | .ok (r, m₁) => if r.headD 0 = 0 then .error (.abort k)
    else dvoE.k_env_push (callE p n "env_push" [vis, c] m₁)

/-- `dvoE`'s continuation after `infer_type_core`. -/
def dvoE.k_infer_type_core (k : Word) (p : Prog) (n : Nat) (vis c t : Word) :
    Except Err (List Word × Mem) → Except Err (Word × Mem)
  | .error ε => .error ε
  | .ok (r, m₁) => dvoE.k_is_def_eq_core k p n vis c (callE p n "is_def_eq_core" [vis, 0, r.headD 0, t] m₁)

/-- `dvoE`'s continuation after `install_value_guards`. -/
def dvoE.k_install_value_guards (k : Word) (p : Prog) (n : Nat) (vis c v t : Word) :
    Except Err (List Word × Mem) → Except Err (Word × Mem)
  | .error ε => .error ε
  | .ok (_, m₁) => dvoE.k_infer_type_core k p n vis c t (callE p n "infer_type_core" [vis, 0, v] m₁)

/-- **`check_defn_val`'s and `check_opaque_val`'s model, over the mismatch's abort code `k`**: the
two L functions have the same text but for that code, as their twins are `dvT` but for the
message. -/
def dvoE (k : Word) (p : Prog) : Nat → Mem → Word → Word → Except Err (Word × Mem)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, m, vis, c => dvoE.k_install_value_guards k p n vis c (rdW (m.arr64 EREC) (c + 5))
    (rdW (m.arr64 EREC) (c + 4)) (callE p n "install_value_guards" [vis, c + 1, rdW (m.arr64 EREC) (c + 5)] m)

theorem checkDefnValE_dvo (p : Prog) (n : Nat) (m : Mem) (vis c : Word) :
    checkDefnValE p n m vis c = dvoE R_TYPE_MISMATCH_IN p n m vis c := by
  sorry

theorem checkOpaqueValE_dvo (p : Prog) (n : Nat) (m : Mem) (vis c : Word) :
    checkOpaqueValE p n m vis c = dvoE R_TYPE_MISMATCH_IN_OPAQUE p n m vis c := by
  sorry

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`dvoE k` refines its twin `dvT …`, both outcomes**, under `StageT`, for a code `k` of the
twin's mismatch class: the value's guards by `ivg_ref`, the core stubs by `KnotStageProg` and
`CoreStubsE`, the type mismatch the twin's `invalid`; after the push the stage at the extended
environment. -/
theorem dvo_ref {p : Prog} (hq : KnotStageProg p) (hp : ValProg p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c : Word} {cv : IConstantVal} {v : EIdx}
    {ci : IConstantInfo} {k : Word} (msg : String) (hk : (Err.abort k).cls = twinCls (.invalid msg))
    (hS : StageT dn vis fe m a)
    (hci : decCI (erecP m) c.toNat = some ci) (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    RefE (DvCtx p) (dvoE k p n m vis c) (dvT fe cv v ci msg) a
      (fun w y a' => DvPost dn m (fe.push ci) w y a') := by
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hcb : c.toNat + 5 < 2 ^ 64 := erecP_bound hwv hS.stage.iw
  have ev : rdW (m.arr64 EREC) (c + 5) = wv :=
    rdW_of_get? (toNat_add_small c 5 (by omega)).symm (erecP_get hwv)
  have et : rdW (m.arr64 EREC) (c + 4) = wt :=
    rdW_of_get? (toNat_add_small c 4 (by omega)).symm (erecP_get (by simpa [Nat.add_assoc] using hwt))
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  cases n with
  | zero => exact RefE.of_cls0 rfl
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [dvoE, ev, et]
  unfold dvT
  rw [hty]
  -- `install_value_guards(vis, c + 1, v)`
  rcases h1 : callE p n "install_value_guards" [vis, c + 1, wv] m with e1 | ⟨r1, m1⟩
  · exact RefE.bind_left fun hG => hG.ivg h1 hS (by rw [hc1]; exact ArrExt.decCV (erecP_ext m) hcv)
      (by rw [hc1]; omega) hwvl hlps hCr
  obtain ⟨s1, hs1, -, _, a1, hrun1, hS1, hg1, -⟩ := RefE.run_ok
    (s₀ := ⟨m, Locals.init []⟩)
    (installValueGuards_specE p hp.cvg n _ vis (c + 1) wv)
    (ivg_ref hap hkp.crf n hS (by rw [hc1]; exact ArrExt.decCV (erecP_ext m) hcv)
      (by rw [hc1]; omega) hwvl hlps hCr) h1
  subst hs1
  dsimp only [dvoE.k_install_value_guards]
  refine RefE.bind_right hrun1 ?_
  -- the value's type
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h2 => hG.core.inferTypeCore n hn' hS1 0 wv hwvl _ h2)
    (fun b h2 => hq.inferTypeCore_sim n hn' hS1 0 wv hwvl b.1 b.2 h2)
    fun r2 m2 x2 a2 _ _ ⟨hS2, hg2, hx2l, hx2⟩ => ?_
  dsimp only [dvoE.k_infer_type_core]
  subst hx2
  -- the comparison with the declared type
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h3 => hG.core.isDefEqCore n hn' hS2 0 (r2.headD 0) wt hx2l hwtl _ h3)
    (fun b h3 => hq.isDefEqCore_sim n hn' hS2 0 (r2.headD 0) wt hx2l hwtl b.1 b.2 h3)
    fun r3 m3 x3 a3 _ _ ⟨hS3, hg3, hx3⟩ => ?_
  dsimp only [dvoE.k_is_def_eq_core]
  refine RefE.guard hk (fun hb3 => by rw [← hx3, decBool, hb3]; rfl)
    (fun hb3 => by rw [← hx3] at hb3; simpa [decBool] using hb3) fun _ _ => ?_
  -- the push
  have hx13 : ArrExt (erecP m) (erecP m3) := IWGrow.erecPExt (hg1.trans (hg2.trans hg3))
  have hci3 := ArrExt.decCI hx13 hci
  obtain ⟨w, hw1, hwl, -⟩ := decCI_name hci3
  have hw : (rdW (m3.arr64 EREC) (c + 1)).toNat < 2 ^ 32 := by
    rw [rdW_of_get? hc1.symm (erecP_get hw1)]; exact hwl
  rcases h4 : callE p n "env_push" [vis, c] m3 with e4 | ⟨r4, m4⟩
  · exact fun hG => ErrClaim.of_cls0 (hG.env _ _ _ _ h4)
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (envPush_specW p hp.rcp n ⟨m3, Locals.init []⟩ vis c hw) (callW_of_callE h4)
  subst hs4
  obtain ⟨hS4, hg4⟩ := envPushW_ok hW4 hS3.stage hci3
  have hM4 : CoreMemos s4.mem := hS3.twin.memos.frame (envPushW_frame hW4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact RefE.ret rfl ⟨by simpa using hS4, hM4, hg1.trans (hg2.trans (hg3.trans hg4)), rfl⟩
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_defn_val` refines its twin `dvT …`, both outcomes** (`dvo_ref`). -/
theorem dv_ref {p : Prog} (hq : KnotStageProg p) (hp : ValProg p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c : Word} {cv : IConstantVal} {v : EIdx}
    {ci : IConstantInfo} (msg : String) (hS : StageT dn vis fe m a)
    (hci : decCI (erecP m) c.toNat = some ci) (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    RefE (DvCtx p) (checkDefnValE p n m vis c) (dvT fe cv v ci msg) a
      (fun w y a' => DvPost dn m (fe.push ci) w y a') := by
  rw [checkDefnValE_dvo]; exact dvo_ref hq hp hap hkp hn msg rfl hS hci hcv hv hlps hCr
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_opaque_val` refines its twin `dvT …`, both outcomes** (`dvo_ref`). -/
theorem ov_ref {p : Prog} (hq : KnotStageProg p) (hp : ValProg p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c : Word} {cv : IConstantVal} {v : EIdx}
    {ci : IConstantInfo} (msg : String) (hS : StageT dn vis fe m a)
    (hci : decCI (erecP m) c.toNat = some ci) (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    RefE (DvCtx p) (checkOpaqueValE p n m vis c) (dvT fe cv v ci msg) a
      (fun w y a' => DvPost dn m (fe.push ci) w y a') := by
  rw [checkOpaqueValE_dvo]; exact dvo_ref hq hp hap hkp hn msg rfl hS hci hcv hv hlps hCr
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_defn_val`'s error claim under `StageT`** (`dv_ref`'s error half). -/
theorem defnvE_okT {p : Prog} (hq : KnotStageProg p) (hp : ValProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hcE : CoreStubsE p) (hivE : IvgE p) (hnvE : NVAt p "env_push")
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c : Word} {cv : IConstantVal} {v : EIdx}
    (hh : ConLeche.ReducibilityHint) (hS : StageT dn vis fe m a)
    (hc : decCI (erecP m) c.toNat = some (.defnInfo cv v hh))
    (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m)
    {e : Err} (hce : callE p n "check_defn_val" [vis, c] m = .error e) :
    ErrClaim (checkDefnVal V fe cv v hh) a e :=
  RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkDefnVal_specE p hp n _ vis c) trivial
    ⟨hnvE, hcE, hivE⟩ (dv_ref hq hp hap hkp hn _ hS hc hcv hv hlps hCr) hce
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_opaque_val`'s error claim under `StageT`** (`ov_ref`'s error half). -/
theorem opaquevE_okT {p : Prog} (hq : KnotStageProg p) (hp : ValProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hcE : CoreStubsE p) (hivE : IvgE p) (hnvE : NVAt p "env_push")
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c : Word} {cv : IConstantVal} {v : EIdx}
    (hS : StageT dn vis fe m a)
    (hc : decCI (erecP m) c.toNat = some (.axiomInfo cv))
    (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m)
    {e : Err} (hce : callE p n "check_opaque_val" [vis, c] m = .error e) :
    ErrClaim (checkOpaqueVal V fe cv v) a e :=
  RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkOpaqueVal_specE p hp n _ vis c) trivial
    ⟨hnvE, hcE, hivE⟩ (ov_ref hq hp hap hkp hn _ hS hc hcv hv hlps hCr) hce
-/

end L.Arena
