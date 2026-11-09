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
public import ConAgua.Arena.StrLitShape
public import ConAgua.Arena.StubNamesRefine
import ConAgua.Arena.IndRealIlpL
import ConAgua.Arena.CrOKFrame
import ConAgua.Arena.LvlGrow
import ConRon.Bridge.Core.Walks.Cached
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
  vg : p.lookup "value_guards" = some valueGuardsL

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
    ⟨hT.twin.memos.walk, hT.twin.erec, hT.twin.spn, hT.twin.bstk, hT.flag⟩, hT.twin.memos.hb⟩

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
    (∃ ks, ci.toConstantVal.levelParams.mapM (denoteN a.store.ns) = some ks) →
    Sim (callW p n "lit_shape_ok" [c] m) (litShapeOk ci) a
      (fun r b m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ (L.Stubs.CrOK m → L.Stubs.CrOK m') ∧
        AFr m m' ∧ (∀ cv' x, Frontend.denoteCV a.store cv' = some x →
          Frontend.denoteCV a'.store cv' = some x) ∧ (r.headD 0 ≠ 0 ↔ b = true))

/-- **`CcvSims` from the program**: `nat_op_name` by `natOpName_sim`, `lit_shape_ok` by
`litShapeOk_call` under `CoreS`, `StageT` after it by the leaves' write set, the store extended
(`emono_litShapeOk`). -/
theorem ccvSims_of {p : Prog} (hp : StrLitProg p) (hcl : LitShapeClosed p)
    (hno : p.lookup "nat_op_name" = some L.Stubs.natOpNameL)
    (hpr : p.lookup "pin_range_has" = some L.Stubs.pinRangeHas)
    (dn : NIdx → Option ConLeche.Name) : CcvSims p dn where
  natOp n _ _ _ _ _ hS hw := L.Stubs.natOpName_sim hno hpr hp.pinAt n hS hw
  lit n vis fe m a c ci hT hci hlps := by
    intro r m' h
    obtain ⟨M, hC⟩ := hT.core
    have R := litShapeOk_call p hp hC hci hlps h
    obtain ⟨M', hC', -, -⟩ := R.after
    have hfr := callW_litShapeFrame hcl (by decide) h
    obtain ⟨hT', hg⟩ := StageT.of_coreFrame hfr coreStageA_iw coreStageA_erec coreStageA_pins
      coreStageC_129 coreStageC_200 hT hC' coreStageA_erec1 coreStageC_130
    have hrun := AM.run_of_ok _ _ R.run
    refine ⟨_, _, hrun, hT', hg, fun hCr => CrOK.frame hCr hfr coreStageA_155 coreStageC_158,
      fun hA => ⟨hT'.twin.memos.ab, hA.i1.frame hfr coreStageA_51 coreStageC_52,
        hA.cr.frame hfr coreStageA_155 coreStageC_158, hT'.twin.memos.il, ⟨hT'.twin.memos.walk,
        hT'.twin.erec, hT'.twin.spn, hT'.twin.bstk, hT'.flag⟩, hT'.twin.memos.hb⟩,
      fun cv' x hx => ConRon.Bridge.denoteCV_ext hx ((emono_litShapeOk ci).run hrun), ?_⟩
    rw [R.res]; unfold decBool; simp

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
    (hC.lit n vis fe m9 a _ _ hT9 hci9 (denoteCV_lps hden))
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
    rcases h10 : callE p (n + 1) "unresolved_consts_error" [vis, wt, 0] m9' with e10 | ⟨r10, m10⟩ <;>
      dsimp only [checkConstantValE.k_unresolved_consts_error]
    · obtain ⟨M9, hC9⟩ := hS9.core
      exact fun hG => uce_errClaim_lo hG.uce hG.nv hC9 hwtl (by decide) h10 "type"
    · exact RefE.of_cls0 rfl
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


/-! ## `value_guards(vis, q, v)` -/

/-- **The model of `value_guards`, both outcomes**: the walks `loose_bvars_bounded_fast`,
`has_fvar_fast` and `cv_lps` through their `Option` models, the gates through `callE`. -/
l_model valueGuards_specE (p : Prog) (hp : CcvProg p)
  fns [hp.vg ↦ valueGuardsE]
  specs [cvLps_specW p hp.val.cvg.alloc hp.val.cvg.copy hp.val.cvg.eti hp.val.cvg.lps n,
    lbbF_spec p hp.val.cvg.bvb n, hffF_spec p hp.val.cvg.hf n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`value_guards(vis, q, v)` refines `valueGuards fe cv v`, both outcomes**, under `StageT`:
the two walks, the record's level parameters copied to `IW` (`cv_lps`), the declared universe
parameters (`apdF_okT`, the names read back at the entry), the constants resolving (`crfF_okT`,
its memo carried across), the unresolved constants' error by `uce_errClaim_lo`. -/
theorem vg_ref {p : Prog} (hP : CcvProg p) (hap : ApdF p) (hcrf : L.Ind.CrfF p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} (n : Nat) {m : Mem}
    {q v : Word} {cv : IConstantVal} (hS : StageT dn vis fe m a)
    (hqd : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64) (hv : v.toNat < 2 ^ 32)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (valueGuardsE p n m vis q v) (valueGuards fe cv (decI v)) a
      (fun w _ a' => CcvPost dn vis fe m w.2 a') := by
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_sliceW hqd
  have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hq2 : (q + 2).toNat = q.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  cases n with
  | zero => rw [valueGuardsE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  rw [valueGuardsE.arm1]
  simp only [valueGuards, fail_bindAM]
  -- `loose_bvars_bounded_fast(4000000000, 0, v)`
  refine RefE.bindSim (fun _ => rfl) (fun r m' h => lbbF_okT dn vis fe 4000000000 0 v hv m m' a r h hS)
    fun r6 x6 m6 a6 h6 hrun6 ⟨hS6, hg6, hx6, _⟩ => ?_
  have hCr6 := CrOK.frame hCr (lbbF_frame h6) (by decide) (by decide)
  have hA6 : AFr m m6 := AFr.of_frame (lbbF_frame h6)
  dsimp only [valueGuardsE.k_loose_bvars_bounded_fast]
  refine RefE.guardIf rfl (fun hb6 => by rw [← hx6]; simpa using hb6)
    (fun hb6 => by rw [← hx6] at hb6; simpa using hb6) fun _ _ => ?_
  -- `has_fvar_fast(4000000000, v)`
  refine RefE.bindSim (fun _ => rfl) (fun r m' h => hffF_okT dn vis fe 4000000000 v hv m6 m' a6 r h hS6)
    fun r7 x7 m7 a7 h7 hrun7 ⟨hS7, hg7, hx7, _⟩ => ?_
  have hCr7 := CrOK.frame hCr6 (hffF_frame h7) (by decide) (by decide)
  have hA7 : AFr m m7 := hA6.trans (AFr.of_frame (hffF_frame h7))
  dsimp only [valueGuardsE.k_has_fvar_fast]
  refine RefE.guardThen rfl (fun hb7 => by rw [← hx7]; simpa using hb7)
    (fun hb7 => by rw [← hx7] at hb7; simpa using hb7) fun _ _ => ?_
  -- `cv_lps(q)`
  have hg0 : IWGrow m m7 := hg6.trans hg7
  have e1 : rdW (m7.arr64 (L.tierA EREC ((q + 1) >>> 40))) (q + 1 &&& 1099511627775) = w1 := by
    rw [erRdT_congr rfl rfl]; exact erRdT_of _ _ (by rw [hq1]; exact hg0.ext _ _ hw1)
  have e2 : rdW (m7.arr64 (L.tierA EREC ((q + 2) >>> 40))) (q + 2 &&& 1099511627775) = w2 := by
    rw [erRdT_congr rfl rfl]; exact erRdT_of _ _ (by rw [hq2]; exact hg0.ext _ _ hw2)
  have hsl7 : hslice? (erA m7) w1.toNat w2.toNat = some cv.levelParams := ArrExt.hslice? hg0.ext hsl
  refine RefE.onlySim (fun _ => valueGuardsE.k_cv_lps.none ..) (fun _ _ h => h) fun r11 m11 h11 => ?_
  rw [valueGuardsE.k_cv_lps.arm1]
  cases n with
  | zero => simp [cvLpsW] at h11
  | succ n =>
  rw [cvLpsW_step, e1, e2] at h11
  obtain ⟨hS11R, hg11, hdec11, -, -⟩ := erToIwW_stage h11 hS7.stage hsl7
  have hT11 := StageT.of_iw hS7 hS11R (erToIwW_iwFr h11)
  have hCr11 := CrOK.frame hCr7 (erToIwW_iwFr h11) (by decide) (by decide)
  have hA11 : AFr m m11 := hA7.trans (erToIwW_afr h11)
  -- `all_level_params_defined(o, l, v)`
  have hst7 : a7.store = a.store := (hffF_store hrun7).trans (lbbF_store hrun6)
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h8 => nvl hG.nv (by decide +kernel) h8)
    (fun b h8 => apdF_okT dn vis fe (r11.headD 0) (r11.tail.headD 0) v hv cv.levelParams m11 b.2 a7 b.1
      (apdF_of_callW hap h8) ⟨hT11, hdec11, by rw [hst7]; exact hlps⟩)
    fun r8 m8 x8 a8 h8 _ ⟨hS8, hg8, hx8, _⟩ => ?_
  have h8' := apdF_of_callW hap (callW_of_callE h8)
  have hCr8 := CrOK.frame hCr11 (apdF_frame h8') (by decide) (by decide)
  have hA8 : AFr m m8 := fun hA => absOK_apdF h8' (hA11 hA) hS8
  dsimp only [valueGuardsE.k_all_level_params_defined]
  refine RefE.guardIf rfl (fun hb8 => by rw [← hx8]; simpa using hb8)
    (fun hb8 => by rw [← hx8] at hb8; simpa using hb8) fun _ _ => ?_
  -- `consts_resolve_ffast(vis, v)`
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h9 => nvl hG.nv (by decide +kernel) h9)
    (fun b h9 => crfF_okT dn vis fe v hv m8 b.2 a8 b.1 (crfF_of_callW hcrf h9) ⟨hS8, hCr8.crMemo⟩)
    fun r9 m9' x9 a9 h9 _ ⟨⟨hS9, hg9', hx9, _⟩, hCr9'⟩ => ?_
  have hA9' : AFr m m9' := fun hA =>
    absOK_crfF' (crfF_of_callW hcrf (callW_of_callE h9)) (hA8 hA) hCr9'.crOK hS9
  dsimp only [valueGuardsE.k_consts_resolve_ffast]
  refine RefE.splitNot (fun hb9 => by rw [← hx9]; simpa using hb9)
    (fun hb9 => by rw [← hx9] at hb9; simpa using hb9) (fun _ _ => ?_) fun _ _ => ?_
  · rcases h10 : callE p (n + 1) "unresolved_consts_error" [vis, v, 1] m9' with e10 | ⟨r10, m10⟩ <;>
      dsimp only [valueGuardsE.k_unresolved_consts_error]
    · obtain ⟨M9, hC9⟩ := hS9.core
      exact fun hG => uce_errClaim_lo hG.uce hG.nv hC9 hv (by decide) h10 "value"
    · exact RefE.of_cls0 rfl
  exact RefE.ret rfl ⟨hS9, hg0.trans (hg11.trans (hg8.trans hg9')), hCr9'.crOK, hA9'⟩

/-- **`check_defn_val(vis, c)` refines `checkDefnVal`, both outcomes**, under `StageT`: the value's
guards (`vg_ref`), its type (`infer_type_core`) against the declared one (`is_def_eq_core`), the
mismatch the twin's `invalid`; the record `c` returned, unpushed. -/
theorem checkDefnVal_ref {p : Prog} (hP : CcvProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (hcrf : L.Ind.CrfF p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c : Word}
    {cv : IConstantVal} {wv : Word} {hint : ConLeche.ReducibilityHint} (hS : StageT dn vis fe m a)
    (hcv : decCV (erecP m) (c.toNat + 1) = some cv) (hwv : erecP m (c.toNat + 5) = some wv)
    (hwvl : wv.toNat < 2 ^ 32)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkDefnValE p n m vis c) (checkDefnVal V fe cv (decI wv) hint) a
      (fun w y a' => CcvPost dn vis fe m w.2 a' ∧ w.1 = c ∧ y = .defnInfo cv (decI wv) hint) := by
  obtain ⟨wt, hwt, hwtl, hty⟩ := (decCV_words hcv).2.2
  have hc5 : c.toNat + 5 < 2 ^ 64 := erecP_lt64 hwv
  have e5 : (c + 5).toNat = c.toNat + 5 := toNat_add_small c 5 (by omega)
  have e4 : (c + 4).toNat = c.toNat + 4 := toNat_add_small c 4 (by omega)
  have e1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  have ev : rdW (m.arr64 (L.tierA EREC ((c + 5) >>> 40))) (c + 5 &&& 1099511627775) = wv := by
    rw [erRdT_congr rfl rfl]; exact erRdT_of _ _ (by rw [e5]; exact hwv)
  have et : rdW (m.arr64 (L.tierA EREC ((c + 4) >>> 40))) (c + 4 &&& 1099511627775) = wt := by
    rw [erRdT_congr rfl rfl]; exact erRdT_of _ _ (by rw [e4]; simpa [Nat.add_assoc] using hwt)
  cases n with
  | zero => rw [checkDefnValE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkDefnValE.arm1, ev, et]
  simp only [checkDefnVal]
  -- the value's guards
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => checkDefnValE.k_value_guards.none ..)
    (valueGuards_specE p hP n ⟨m, Locals.init []⟩ vis (c + 1) wv) (fun hG => hG.nv) id
    (vg_ref hP hap hcrf n hS (by rw [e1]; exact hcv) (by rw [e1]; omega) hwvl hlps hCr)
    fun r1 s1 y1 a1 _ _ _ hP1 => ?_
  rw [checkDefnValE.k_value_guards.arm1]
  have hS1 := hP1.stage
  -- the value's type
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h2 => hG.core.inferTypeCore n hn' hS1 0 wv hwvl _ h2)
    (fun b h2 => hq.inferTypeCore_sim n hn' hS1 0 wv hwvl b.1 b.2 h2)
    fun r2 m2 x2 a2 h2 _ ⟨hS2, hg2, hx2l, hx2⟩ => ?_
  rw [checkDefnValE.k_infer_type_core.arm1]
  subst hx2
  rw [hty]
  -- the comparison with the declared type
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h3 => hG.core.isDefEqCore n hn' hS2 0 (r2.headD 0) wt hx2l hwtl _ h3)
    (fun b h3 => hq.isDefEqCore_sim n hn' hS2 0 (r2.headD 0) wt hx2l hwtl b.1 b.2 h3)
    fun r3 m3 x3 a3 h3 _ ⟨hS3, hg3, hx3⟩ => ?_
  rw [checkDefnValE.k_is_def_eq_core.eq_2]
  refine RefE.guard rfl (fun hb3 => by rw [← hx3, decBool, hb3]; rfl)
    (fun hb3 => by rw [← hx3] at hb3; simpa [decBool] using hb3) fun _ _ => ?_
  have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hP1.crOK
  exact RefE.ret rfl ⟨⟨hS3, hP1.grow.trans (hg2.trans hg3),
    hkp.call (im_mem _ rfl) (callW_of_callE h3) hCr2, fun hA => absOK_core hq.closed (by decide)
      (callW_of_callE h3) (absOK_core hq.closed (by decide) (callW_of_callE h2) (hP1.abs hA) hS2) hS3⟩,
    rfl, rfl⟩

/-- **`check_opaque_val(vis, c)` refines `checkOpaqueVal`, both outcomes**, under `StageT`: the value's
guards (`vg_ref`), its type (`infer_type_core`) against the declared one (`is_def_eq_core`), the
mismatch the twin's `invalid`; the record `c` returned, unpushed. -/
theorem checkOpaqueVal_ref {p : Prog} (hP : CcvProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (hcrf : L.Ind.CrfF p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c : Word}
    {cv : IConstantVal} {wv : Word} (hS : StageT dn vis fe m a)
    (hcv : decCV (erecP m) (c.toNat + 1) = some cv) (hwv : erecP m (c.toNat + 5) = some wv)
    (hwvl : wv.toNat < 2 ^ 32)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkOpaqueValE p n m vis c) (checkOpaqueVal V fe cv (decI wv)) a
      (fun w y a' => CcvPost dn vis fe m w.2 a' ∧ w.1 = c ∧ y = .axiomInfo cv) := by
  obtain ⟨wt, hwt, hwtl, hty⟩ := (decCV_words hcv).2.2
  have hc5 : c.toNat + 5 < 2 ^ 64 := erecP_lt64 hwv
  have e5 : (c + 5).toNat = c.toNat + 5 := toNat_add_small c 5 (by omega)
  have e4 : (c + 4).toNat = c.toNat + 4 := toNat_add_small c 4 (by omega)
  have e1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  have ev : rdW (m.arr64 (L.tierA EREC ((c + 5) >>> 40))) (c + 5 &&& 1099511627775) = wv := by
    rw [erRdT_congr rfl rfl]; exact erRdT_of _ _ (by rw [e5]; exact hwv)
  have et : rdW (m.arr64 (L.tierA EREC ((c + 4) >>> 40))) (c + 4 &&& 1099511627775) = wt := by
    rw [erRdT_congr rfl rfl]; exact erRdT_of _ _ (by rw [e4]; simpa [Nat.add_assoc] using hwt)
  cases n with
  | zero => rw [checkOpaqueValE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkOpaqueValE.arm1, ev, et]
  simp only [checkOpaqueVal]
  -- the value's guards
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => checkOpaqueValE.k_value_guards.none ..)
    (valueGuards_specE p hP n ⟨m, Locals.init []⟩ vis (c + 1) wv) (fun hG => hG.nv) id
    (vg_ref hP hap hcrf n hS (by rw [e1]; exact hcv) (by rw [e1]; omega) hwvl hlps hCr)
    fun r1 s1 y1 a1 _ _ _ hP1 => ?_
  rw [checkOpaqueValE.k_value_guards.arm1]
  have hS1 := hP1.stage
  -- the value's type
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h2 => hG.core.inferTypeCore n hn' hS1 0 wv hwvl _ h2)
    (fun b h2 => hq.inferTypeCore_sim n hn' hS1 0 wv hwvl b.1 b.2 h2)
    fun r2 m2 x2 a2 h2 _ ⟨hS2, hg2, hx2l, hx2⟩ => ?_
  rw [checkOpaqueValE.k_infer_type_core.arm1]
  subst hx2
  rw [hty]
  -- the comparison with the declared type
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h3 => hG.core.isDefEqCore n hn' hS2 0 (r2.headD 0) wt hx2l hwtl _ h3)
    (fun b h3 => hq.isDefEqCore_sim n hn' hS2 0 (r2.headD 0) wt hx2l hwtl b.1 b.2 h3)
    fun r3 m3 x3 a3 h3 _ ⟨hS3, hg3, hx3⟩ => ?_
  rw [checkOpaqueValE.k_is_def_eq_core.eq_2]
  refine RefE.guard rfl (fun hb3 => by rw [← hx3, decBool, hb3]; rfl)
    (fun hb3 => by rw [← hx3] at hb3; simpa [decBool] using hb3) fun _ _ => ?_
  have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hP1.crOK
  exact RefE.ret rfl ⟨⟨hS3, hP1.grow.trans (hg2.trans hg3),
    hkp.call (im_mem _ rfl) (callW_of_callE h3) hCr2, fun hA => absOK_core hq.closed (by decide)
      (callW_of_callE h3) (absOK_core hq.closed (by decide) (callW_of_callE h2) (hP1.abs hA) hS2) hS3⟩,
    rfl, rfl⟩


/-- **`check_thm_val(vis, c)` refines `checkThmVal`, both outcomes**, under `StageT`: the type's
sort compared with the zero level (`lvl_eq_fueled`, `lef_ref`), the value's guards (`vg_ref`), its
type against the declared one; the record `c` returned, unpushed. The parameters' names read back
at the guards because the prefix only extends the store (`thmPrefix_ext`). -/
theorem checkThmVal_ref {p : Prog} (hP : CcvProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (hcrf : L.Ind.CrfF p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c : Word}
    {cv : IConstantVal} {wv : Word} (hS : StageT dn vis fe m a)
    (hcv : decCV (erecP m) (c.toNat + 1) = some cv) (hwv : erecP m (c.toNat + 5) = some wv)
    (hwvl : wv.toNat < 2 ^ 32)
    (hpre : ∃ env cP, ConLeche.EnvWF env ∧ ConRon.Bridge.CheckOK false env fe a ∧
      Frontend.denoteCV a.store cv = some cP ∧ ConLeche.Expr.WScoped 0 cP.type)
    (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkThmValE p n m vis c) (checkThmVal V fe cv (decI wv)) a
      (fun w y a' => StageT dn vis fe w.2 a' ∧ IWGrow m w.2 ∧ L.Stubs.CrOK w.2 ∧ w.1 = c ∧
        y = .thmInfo cv) := by
  have hL := hq.knot.lvc
  obtain ⟨wt, hwt, hwtl, hty⟩ := (decCV_words hcv).2.2
  have hc5 : c.toNat + 5 < 2 ^ 64 := erecP_lt64 hwv
  have e5 : (c + 5).toNat = c.toNat + 5 := toNat_add_small c 5 (by omega)
  have e4 : (c + 4).toNat = c.toNat + 4 := toNat_add_small c 4 (by omega)
  have e1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  have ev : rdW (m.arr64 (L.tierA EREC ((c + 5) >>> 40))) (c + 5 &&& 1099511627775) = wv := by
    rw [erRdT_congr rfl rfl]; exact erRdT_of _ _ (by rw [e5]; exact hwv)
  have et : rdW (m.arr64 (L.tierA EREC ((c + 4) >>> 40))) (c + 4 &&& 1099511627775) = wt := by
    rw [erRdT_congr rfl rfl]; exact erRdT_of _ _ (by rw [e4]; simpa [Nat.add_assoc] using hwt)
  cases n with
  | zero => rw [checkThmValE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkThmValE.arm1, ev, et]
  simp only [checkThmVal, zeroLevel, hty]
  -- the type's type
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h1 => hG.core.inferTypeCore n hn' hS 0 wt hwtl _ h1)
    (fun b h1 => hq.inferTypeCore_sim n hn' hS 0 wt hwtl b.1 b.2 h1)
    fun r1 m1 x1 a1 h1 hrun1 ⟨hS1, hg1, hx1l, hx1⟩ => ?_
  rw [checkThmValE.k_infer_type_core.arm1]
  have hCr1 := hkp.call (im_mem _ rfl) (callW_of_callE h1) hCr
  subst hx1
  -- its sort
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h2 => hG.core.ensureSortCore n hn' hS1 0 (r1.headD 0) hx1l _ h2)
    (fun b h2 => hq.ensureSortCore_sim n hn' hS1 0 (r1.headD 0) hx1l b.1 b.2 h2)
    fun r2 m2 x2 a2 h2 hrun2 ⟨hS2, hg2, hx2l, hx2⟩ => ?_
  rw [checkThmValE.k_ensure_sort_core.arm1]
  have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hCr1
  -- the zero level
  have hflag : pinW m2 0 ≠ 0 := hS2.flag
  have hF := hS2.stage.check.pins.full hflag
  have hz : rdW (m2.arr64 PINS) 53 = pinW m2 53 := by simp [rdW, pinW]
  have h3 : pinWordW m2 53 = some ([pinW m2 53], m2) := by
    simp only [pinWordW, hflag, ite_false, hz]
  rw [h3, liftE_some, checkThmValE.k_pin_word.arm1]
  simp only [List.headD_cons]
  refine RefE.bind_right (pinZeroLevel_run hF) ?_
  -- the two levels read back
  obtain ⟨xs, hxs⟩ := ensureSort_view (r := pureFnsA V false fe checkFuel) (fe := fe)
    (d := (0 : Word).toNat) (e := decI (r1.headD 0)) hrun2
  obtain ⟨lu, hdu⟩ := hS2.twin.den.sort _ _ hxs
  rw [← hx2] at hdu
  obtain ⟨lz, hdz⟩ : ∃ l, denoteL _ _ = some l := ⟨_, hS2.twin.den.zero⟩
  rw [hF.zeroLevel] at hdz
  -- the comparison
  rw [← hx2, lefT_bind]
  refine RefE.bindRun (s₀ := ⟨m2, Locals.init []⟩) (fun _ => checkThmValE.k_lvl_eq_fueled.none ..)
    (lefE_spec p hP.val.lef n ⟨m2, Locals.init []⟩ (r2.headD 0) (pinW m2 53)) (fun _ => trivial)
    (fun hG => fun n args m e h => callE_nv hG.nv (L.Checker.nv_mem (by decide +kernel)) n args m h)
    (lef_ref hq.closed hL n hS2 hx2l hF.lv_lt.2.1 hdu hdz)
    fun r4 s4 b4 a4 h4 _ _ ⟨hrun4, hr4, hS4, hg4, hmfr4, _⟩ => ?_
  dsimp only at hS4 hg4 hr4
  have hCr4 := hkp.call (im_mem _ rfl) (callW_of_callE h4) hCr2
  rw [checkThmValE.k_lvl_eq_fueled.eq_2]
  -- the type is not a proposition
  refine RefE.guard rfl (fun hb4 => by cases b4; rfl; exact absurd hr4 (by rw [hb4]; decide))
    (fun hb => by subst hb; simpa using hr4) fun _ hb => ?_
  subst hb
  -- the parameters' names read back at the guards: the prefix extends the store
  have hlps4 : ∃ ks, cv.levelParams.mapM (denoteN a4.store.ns) = some ks := by
    obtain ⟨env, cP, henv, hck, hcvd, hws⟩ := hpre
    obtain ⟨hck2, hx02⟩ := thmPrefix_ext henv hck hcvd hws (by rw [hty]; exact hrun1) hrun2
    obtain ⟨-, hst4, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a2) rfl hrun4
      (ConRon.Bridge.Core.lvlEq?_spec a2 _ _ hck2)
    rw [hst4]
    exact denoteCV_lps (ConRon.Bridge.denoteCV_ext hcvd hx02)
  have hg14 := hg1.trans (hg2.trans hg4)
  -- the value's guards
  refine RefE.bindRun (s₀ := ⟨s4.mem, Locals.init []⟩) (fun _ => checkThmValE.k_value_guards.none ..)
    (valueGuards_specE p hP n ⟨s4.mem, Locals.init []⟩ vis (c + 1) wv) (fun hG => hG.nv) id
    (vg_ref hP hap hcrf n hS4 (by rw [e1]; exact ArrExt.decCV (IWGrow.erecPExt hg14) hcv)
      (by rw [e1]; omega) hwvl hlps4 hCr4)
    fun r5 s5 y5 a5 _ _ _ hP5 => ?_
  rw [checkThmValE.k_value_guards.arm1]
  have hS5 := hP5.stage
  -- the value's type
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h7 => hG.core.inferTypeCore n hn' hS5 0 wv hwvl _ h7)
    (fun b h7 => hq.inferTypeCore_sim n hn' hS5 0 wv hwvl b.1 b.2 h7)
    fun r7 m7 x7 a7 h7 _ ⟨hS7, hg7, hx7l, hx7⟩ => ?_
  rw [checkThmValE.k_infer_type_core_2.arm1]
  subst hx7
  -- the comparison with the declared type
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h8 => hG.core.isDefEqCore n hn' hS7 0 (r7.headD 0) wt hx7l hwtl _ h8)
    (fun b h8 => hq.isDefEqCore_sim n hn' hS7 0 (r7.headD 0) wt hx7l hwtl b.1 b.2 h8)
    fun r8 m8 x8 a8 h8 _ ⟨hS8, hg8, hx8⟩ => ?_
  rw [checkThmValE.k_is_def_eq_core.eq_2]
  refine RefE.guard rfl (fun hb8 => by rw [← hx8, decBool, hb8]; rfl)
    (fun hb8 => by rw [← hx8] at hb8; simpa [decBool] using hb8) fun _ _ => ?_
  have hCr7 := hkp.call (im_mem _ rfl) (callW_of_callE h7) hP5.crOK
  exact RefE.ret rfl ⟨hS8, hg14.trans (hP5.grow.trans (hg7.trans hg8)),
    hkp.call (im_mem _ rfl) (callW_of_callE h8) hCr7, rfl, rfl⟩

end L.Arena
