module

public import ConAgua.Verdict.DeclHdrE
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import ConAgua.Verdict.FrontValidE
import ConAgua.Arena.IlpRd
import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.DeclCvgT
import ConAgua.Arena.IndT.WalkC
import ConAgua.Arena.IndInstallSpec.DomsW
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

/-- **`AbsOK` across `consts_resolve_ffast`** (it writes only its own memo), from `StageT` and
`CrOK` after it. -/
theorem absOK_crfF' {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {args r : List Word} {a' : AState} (h : crfF m args = some (r, m'))
    (hA : AbsOK m) (hCr : L.Stubs.CrOK m') (hT : StageT dn vis fe m' a') : AbsOK m' :=
  have hf := L.Ind.crfF_frame h
  ⟨hT.twin.memos.ab, hA.i1.frame hf (by decide) (by decide), hCr, hT.twin.memos.il,
    hT.twin.memos.walk, hT.twin.erec, hT.twin.spn, hT.twin.bstk, hT.flag⟩

/-- The slice words of a decoded constant value. -/
theorem decCV_sliceW {R : Nat → Option Word} {q : Nat} {cv : IConstantVal} (h : decCV R q = some cv) :
    ∃ w1 w2, R (q + 1) = some w1 ∧ R (q + 2) = some w2 ∧
      hslice? R w1.toNat w2.toNat = some cv.levelParams := by
  simp only [decCV, hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff, nat?,
    Option.map_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨nm, -, ps, ⟨o, ⟨w1, hw1, rfl⟩, l, ⟨w2, hw2, rfl⟩, hs⟩, t, -, rfl⟩ := h
  exact ⟨w1, w2, hw1, hw2, hs⟩

/-- **The leaves `check_constant_val` takes as hypotheses**: `nat_op_name` (the certified
operations' pins) and `lit_shape_ok` (the literal types' shape gates) under `StageT`. -/
structure CcvSims (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop where
  natOp : ∀ (n : Nat) (vis : Word) (fe : IFEnv) (m : Mem) (a : AState) (w : Word),
    StageR vis fe m a → w.toNat < 2 ^ 32 →
    Sim (callW p n "nat_op_name" [w] m) (natOpName (decI w)) a
      (fun r b m' a' => m' = m ∧ a' = a ∧ (r.headD 0 ≠ 0 ↔ b = true))
  lit : ∀ (n : Nat) (vis : Word) (fe : IFEnv) (m : Mem) (a : AState) (c : Word) (ci : IConstantInfo),
    StageT dn vis fe m a → decCI (erecP m) c.toNat = some ci →
    Sim (callW p n "lit_shape_ok" [c] m) (litShapeOk ci) a
      (fun r b m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ (L.Stubs.CrOK m → L.Stubs.CrOK m') ∧
        AFr m m' ∧ (∀ cv' x, Frontend.denoteCV a.store cv' = some x →
          Frontend.denoteCV a'.store cv' = some x) ∧ (r.headD 0 ≠ 0 ↔ b = true))

/-- **`check_constant_val` refines `checkConstantVal .verified`, both outcomes**, under `StageT`:
the duplicate and reserved-name guards, the certified-operation name, the literal shape of a fresh
`axiomInfo cv` record (`ccv_rec`, `CcvSims.lit`), the universe parameters, the closedness walks,
the consts-resolve site (`uce_errClaim_lo`), then the type's sort by the core. -/
theorem ccv_ref {p : Prog} (hP : CcvProg p) (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hcrf : L.Ind.CrfF p)
    {dn : NIdx → Option ConLeche.Name} (hC : CcvSims p dn) {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {q allow : Word} {cv : IConstantVal}
    {c : ConLeche.ConstantVal} (hS : StageT dn vis fe m a) (hqd : decCV (erecP m) q.toNat = some cv)
    (hqb : q.toNat + 3 < 2 ^ 64) (hden : Frontend.denoteCV a.store cv = some c)
    (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkConstantValE p n m vis q allow) (checkConstantVal V fe cv (allow != 0)) a
      (fun v _ a' => CcvPost dn vis fe m v.2 a') := by
  obtain ⟨wx, hwx, hwxl, hname⟩ := decCV_name hqd
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_sliceW hqd
  obtain ⟨wt, hwt, hwtl, hty⟩ := (decCV_words hqd).2.2
  have ex : rdW (m.arr64 (L.tierA EREC (q >>> 40))) (q &&& 1099511627775) = wx := by
    rw [erRdT_congr rfl rfl]; exact erRdT_of _ _ hwx
  have hq3 : (q + 3).toNat = q.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have et : rdW (m.arr64 (L.tierA EREC ((q + 3) >>> 40))) (q + 3 &&& 1099511627775) = wt := by
    rw [erRdT_congr rfl rfl]; exact erRdT_of _ _ (by rw [hq3]; exact hwt)
  have hnm : denoteN a.store.ns cv.name = some c.name := (ConRon.Bridge.denoteCV_inv hden).1
  cases n with
  | zero => rw [checkConstantValE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkConstantValE.arm1, ex, et]
  simp only [checkConstantVal, fail_bindAM]
  -- `env_find(x, vis)`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r1 m1 h1 => ?_
  obtain ⟨hm1, rfl⟩ := envFind_callB hP.basis hwxl hS.stage.check.env h1
  subst m1
  dsimp only [checkConstantValE.k_env_find]
  refine RefE.guardThen (by rfl)
    (fun hb1 => by
      rw [hname]; obtain ⟨e1, ci', e2⟩ := findRes_hit hS.stage.check.env hwxl hb1; rw [e1, e2]; rfl)
    (fun hb => Classical.byContradiction fun hb1 => by
      rw [hname, findRes_miss hS.stage.check.env hwxl (by simpa using hb1)] at hb; cases hb)
    fun hb1 _ => ?_
  -- `reserved_contains(x)`
  rcases h2 : resContW n m wx with _ | c2
  · rw [liftE_none, checkConstantValE.k_reserved_contains.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  by_cases hb2 : c2 ≠ 0
  · rw [checkConstantValE.k_reserved_contains.abort1 p _ _ _ _ _ _ _ _ hb2]
    obtain ⟨l, hrunR, hcl⟩ := resContW_hit hb2 h2 hS.stage.check.pins
    refine RefE.bind_right hrunR (RefE.ite_pos ?_ (fun _ => ErrClaim.fail_abort _ _ rfl))
    rw [hname]; exact hcl
  have hc0 : c2 = 0 := by simpa using hb2
  subst hc0
  rw [checkConstantValE.k_reserved_contains.arm1 p _ _ _ _ _ _ _ _ rfl]
  obtain ⟨l, hrunR, hcl⟩ := resContW_miss hwxl h2 hS.stage.check.pins
  refine RefE.bind_right hrunR (RefE.ite_neg ?_ ?_)
  · rw [hname, hcl]; decide
  -- `nat_op_name(x)`
  refine RefE.bindSim (fun _ => checkConstantValE.k_nat_op_name.none ..)
    (hname ▸ hC.natOp n vis fe m a wx hS.stage hwxl) fun r3 x3 m3 a3 h3 hrun3 ⟨hm3, ha3, hx3⟩ => ?_
  subst m3 a3
  by_cases hb3 : r3.headD 0 ≠ 0 ∧ allow = 0
  · rw [checkConstantValE.k_nat_op_name.abort1 p _ _ _ _ _ _ _ _ hb3]
    have hx : x3 = true := hx3.mp hb3.1
    subst hx
    refine RefE.ite_pos (by simp [hb3.2]) fun _ => ?_
    exact ErrClaim.bind_right (L.Front.Ind.readName_run a _ _ hnm) (ErrClaim.fail_abort _ _ rfl)
  rw [checkConstantValE.k_nat_op_name.arm1 p _ _ _ _ _ _ _ _ hb3]
  refine RefE.ite_neg (fun hc => hb3 ?_) ?_
  · simp only [Bool.and_eq_true, Bool.not_eq_true', bne_eq_false_iff_eq] at hc
    exact ⟨hx3.mpr hc.1, hc.2⟩
  -- the fresh `axiomInfo cv` record
  refine RefE.onlySim (fun _ => checkConstantValE.k_erec_alloc.none ..) (fun _ _ h => h) fun r4 m4 h4 => ?_
  rw [checkConstantValE.k_erec_alloc.arm1]
  refine RefE.onlySim (fun _ => checkConstantValE.k_erec_put.none ..) (fun _ _ h => h) fun r5 m5 h5 => ?_
  rw [checkConstantValE.k_erec_put.arm1]
  refine RefE.onlySim (fun _ => checkConstantValE.k_erec_put_2.none ..) (fun _ _ h => h) fun r6 m6 h6 => ?_
  rw [checkConstantValE.k_erec_put_2.arm1]
  refine RefE.onlySim (fun _ => checkConstantValE.k_erec_put_3.none ..) (fun _ _ h => h) fun r7 m7 h7 => ?_
  rw [checkConstantValE.k_erec_put_3.arm1]
  refine RefE.onlySim (fun _ => checkConstantValE.k_erec_put_4.none ..) (fun _ _ h => h) fun r8 m8 h8 => ?_
  rw [checkConstantValE.k_erec_put_4.arm1]
  refine RefE.onlySim (fun _ => checkConstantValE.k_erec_put_5.none ..) (fun _ _ h => h) fun r9 m9 h9 => ?_
  rw [checkConstantValE.k_erec_put_5.arm1]
  obtain ⟨hT9, hg9, hf9, hci9⟩ := ccv_rec hP.val.rcp hS hqd hqb hwx hwt h4 h5 h6 h7 h8 h9
  have hCr9 := CrOK.frame hCr hf9 (by decide) (by decide)
  have hA9 : AFr m m9 := AFr.of_frame hf9
  -- `lit_shape_ok(a)`
  refine RefE.bindSim (fun _ => checkConstantValE.k_lit_shape_ok.none ..)
    (hC.lit n vis fe m9 a _ _ hT9 hci9)
    fun r10 x10 m10 a10 h10 hrun10 ⟨hT10, hg10, hcr10, hA10, hden10, hx10⟩ => ?_
  dsimp only [checkConstantValE.k_lit_shape_ok]
  refine RefE.guardIf rfl (fun hb => by cases hx : x10; rfl; exact absurd (hx10.mpr hx) (by simpa using hb))
    (fun hb => Classical.byContradiction fun hb' => by have := hx10.mp hb'; simp_all) fun _ _ => ?_
  have hg0 : IWGrow m m10 := hg9.trans hg10
  have hCr10 := hcr10 hCr9
  have hden' := hden10 _ _ hden
  have hlpsN : ∃ ks, cv.levelParams.mapM (denoteN a10.store.ns) = some ks := denoteCV_lps hden'
  -- `cv_lps(q)`
  have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hq2 : (q + 2).toNat = q.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e1 : rdW (m10.arr64 (L.tierA EREC ((q + 1) >>> 40))) (q + 1 &&& 1099511627775) = w1 := by
    rw [erRdT_congr rfl rfl]; exact erRdT_of _ _ (by rw [hq1]; exact hg0.ext _ _ hw1)
  have e2 : rdW (m10.arr64 (L.tierA EREC ((q + 2) >>> 40))) (q + 2 &&& 1099511627775) = w2 := by
    rw [erRdT_congr rfl rfl]; exact erRdT_of _ _ (by rw [hq2]; exact hg0.ext _ _ hw2)
  have hsl10 : hslice? (erA m10) w1.toNat w2.toNat = some cv.levelParams := ArrExt.hslice? hg0.ext hsl
  refine RefE.onlySim (fun _ => checkConstantValE.k_cv_lps.none ..) (fun _ _ h => h) fun r11 m11 h11 => ?_
  rw [checkConstantValE.k_cv_lps.arm1]
  cases n with
  | zero => simp [cvLpsW] at h11
  | succ n =>
  rw [cvLpsW_step, e1, e2] at h11
  obtain ⟨hS11R, hg11, hdec11, htop11, -⟩ := erToIwW_stage h11 hT10.stage hsl10
  have hT11 := StageT.of_iw hT10 hS11R (erToIwW_iwFr h11)
  have hCr11 := CrOK.frame hCr10 (erToIwW_iwFr h11) (by decide) (by decide)
  have hA11 : AFr m m11 := (hA9.trans hA10).trans (erToIwW_afr h11)
  -- `sl_nodup(o, l)`
  rcases h12 : nodupW (n + 1) m11 (r11.headD 0) (r11.tail.headD 0) with _ | d
  · rw [liftE_none, checkConstantValE.k_sl_nodup.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have htopb : iwTop m11 < 2 ^ 64 := by simp only [iwTop]; exact UInt64.toNat_lt _
  obtain ⟨ws, hws, hlps, hwsl⟩ := slR_of_decHL m11 _ _ _ hdec11 (by omega)
  simp only [UInt64.ofNat_toNat] at hws
  have hd := nodupW_ok _ _ _ _ _ _ hws h12
  dsimp only [checkConstantValE.k_sl_nodup]
  refine RefE.guardIf (by rfl)
    (fun hb5 => by
      rw [hlps, nameNodup_map ws hwsl]
      by_cases hn : ws.Nodup
      · rw [ite_eq_left hn, hb5] at hd; exact absurd hd (by decide)
      · simp [hn])
    (fun hnd => Classical.byContradiction fun hb5 => by
      rw [hlps, nameNodup_map ws hwsl] at hnd
      by_cases hn : ws.Nodup
      · simp [hn] at hnd
      · rw [ite_eq_right hn] at hd; exact hb5 hd) fun _ _ => ?_
  -- `loose_bvars_bounded_fast(4000000000, 0, t)`
  rw [hty]
  refine RefE.bindSim (fun _ => rfl) (fun r m' h => lbbF_okT dn vis fe 4000000000 0 wt hwtl m11 m' a10 r h hT11)
    fun r6 x6 m6 a6 h6 hrun6 ⟨hS6, hg6, hx6, _⟩ => ?_
  have hCr6 := CrOK.frame hCr11 (lbbF_frame h6) (by decide) (by decide)
  have hA6 : AFr m m6 := hA11.trans (AFr.of_frame (lbbF_frame h6))
  dsimp only [checkConstantValE.k_loose_bvars_bounded_fast]
  refine RefE.guardIf rfl (fun hb6 => by rw [← hx6]; simpa using hb6)
    (fun hb6 => by rw [← hx6] at hb6; simpa using hb6) fun _ _ => ?_
  -- `has_fvar_fast(4000000000, t)`
  refine RefE.bindSim (fun _ => rfl) (fun r m' h => hffF_okT dn vis fe 4000000000 wt hwtl m6 m' a6 r h hS6)
    fun r7 x7 m7 a7 h7 hrun7 ⟨hS7, hg7, hx7, _⟩ => ?_
  have hCr7 := CrOK.frame hCr6 (hffF_frame h7) (by decide) (by decide)
  have hA7 : AFr m m7 := hA6.trans (AFr.of_frame (hffF_frame h7))
  dsimp only [checkConstantValE.k_has_fvar_fast]
  refine RefE.guardThen rfl (fun hb7 => by rw [← hx7]; simpa using hb7)
    (fun hb7 => by rw [← hx7] at hb7; simpa using hb7) fun _ _ => ?_
  -- `all_level_params_defined(o, l, t)`
  have hdec7 : decHL m7 (r11.headD 0).toNat (r11.tail.headD 0).toNat = some cv.levelParams := by
    rw [decHL_grow (hg6.trans hg7) (by omega), hdec11]
  have hst7 : a7.store = a10.store := (hffF_store hrun7).trans (lbbF_store hrun6)
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h8 => nvl hG.nv (by decide +kernel) h8)
    (fun b h8 => apdF_okT dn vis fe (r11.headD 0) (r11.tail.headD 0) wt hwtl cv.levelParams m7 b.2 a7 b.1
      (apdF_of_callW hap h8) ⟨hS7, hdec7, by rw [hst7]; exact hlpsN⟩)
    fun r8 m8 x8 a8 h8 _ ⟨hS8, hg8, hx8, _⟩ => ?_
  have h8' := apdF_of_callW hap (callW_of_callE h8)
  have hCr8 := CrOK.frame hCr7 (apdF_frame h8') (by decide) (by decide)
  have hA8 : AFr m m8 := fun hA => absOK_apdF h8' (hA7 hA) hS8
  dsimp only [checkConstantValE.k_all_level_params_defined]
  refine RefE.guardIf rfl (fun hb8 => by rw [← hx8]; simpa using hb8)
    (fun hb8 => by rw [← hx8] at hb8; simpa using hb8) fun _ _ => ?_
  -- `consts_resolve_ffast(vis, t)`
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h9 => nvl hG.nv (by decide +kernel) h9)
    (fun b h9 => crfF_okT dn vis fe wt hwtl m8 b.2 a8 b.1 (crfF_of_callW hcrf h9) ⟨hS8, hCr8.crMemo⟩)
    fun r9 m9' x9 a9 h9 _ ⟨⟨hS9, hg9', hx9, _⟩, hCr9'⟩ => ?_
  have hA9' : AFr m m9' := fun hA =>
    absOK_crfF' (crfF_of_callW hcrf (callW_of_callE h9)) (hA8 hA) hCr9'.crOK hS9
  dsimp only [checkConstantValE.k_consts_resolve_ffast]
  refine RefE.splitNot (fun hb9 => by rw [← hx9]; simpa using hb9)
    (fun hb9 => by rw [← hx9] at hb9; simpa using hb9) (fun _ _ => ?_) fun _ _ => ?_
  · -- the unresolved constants' error (`unresolvedConstsErrorL` over `strLitStored`)
    sorry
  -- the type's type
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h2 => hG.core.inferTypeCore (n + 1) hn' hS9 0 wt hwtl _ h2)
    (fun b h2 => hq.inferTypeCore_sim (n + 1) hn' hS9 0 wt hwtl b.1 b.2 h2)
    fun r2 m2 x2 a2 h2 _ ⟨hS2, hg2, hx2l, hx2⟩ => ?_
  dsimp only [checkConstantValE.k_infer_type_core]
  have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hCr9'.crOK
  subst hx2
  -- its sort
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h3 => hG.core.ensureSortCore (n + 1) hn' hS2 0 (r2.headD 0) hx2l _ h3)
    (fun b h3 => hq.ensureSortCore_sim (n + 1) hn' hS2 0 (r2.headD 0) hx2l b.1 b.2 h3)
    fun r3 m3 _ a3 h3 _ ⟨hS3, hg3, _⟩ => ?_
  dsimp only [checkConstantValE.k_ensure_sort_core]
  refine RefE.ret rfl ⟨hS3, hg0.trans (hg11.trans (hg6.trans (hg7.trans (hg8.trans (hg9'.trans
    (hg2.trans hg3)))))), hkp.call (im_mem _ rfl) (callW_of_callE h3) hCr2, fun hA => ?_⟩
  exact absOK_core hq.closed (by decide) (callW_of_callE h3)
    (absOK_core hq.closed (by decide) (callW_of_callE h2) (hA9' hA) hS2) hS3


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
    (ivg_ref hap hcrf n hS (by rw [hc1]; exact ArrExt.decCV (erecP_ext m) hcv)
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
