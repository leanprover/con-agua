module

public import ConAgua.Verdict.DeclHdrE
public import ConAgua.Arena.GrindAttr
import ConAgua.Verdict.FrontValidE
import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.DeclCvgT
import ConAgua.Arena.IndT.WalkC
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndT.Base
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.DeclBasisSpec
public import ConAgua.Arena.QuotAtT
public import ConAgua.Arena.StrLitShape
public import ConAgua.Arena.StubNamesRefine
import ConAgua.Arena.IndRealIlpL
import ConAgua.Arena.LvlGrow
import ConRon.Bridge.Core.Walks.Cached
import all ConAgua.Arena.DeclArms
public import ConAgua.Verdict.DeclValE
public import ConAgua.Verdict.VCtx
import ConAgua.Verdict.LefRef
public import ConAgua.Arena.CrOKFrame
public import ConAgua.Arena.IndRealApdT
public import ConAgua.Arena.KnotEntry
public import ConLeche.Verify.Shift
import ConAgua.Arena.RecCheckSpec.ErToIwWStage
import ConAgua.Arena.IlpRd
import ConAgua.Arena.RecInfoW
import ConAgua.Arena.DeclCanonLvl
import ConAgua.Arena.IndReal
import ConAgua.Arena.IndRealMemoCr

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
  cont : p.lookup "sl_contains" = some slContains
  nodup : p.lookup "sl_nodup" = some slNodup
  basis : BasisProg p
  vg : p.lookup "value_guards" = some valueGuardsL
  pa : p.lookup "pin_at" = some pinAtL

/-- **The model of `check_constant_val`, both outcomes**: the callees outside the verdict closure
with `Option` models through those models, the gates `all_level_params_defined`,
`consts_resolve_ffast` and the core through `callE`. (Heartbeats 10× the default: the three
reserved-name guards; it timed out at 400000.) -/
l_model checkConstantVal_specE (p : Prog) (hp : CcvProg p)
  fns [hp.val.ccv ↦ checkConstantValE]
  specs [callW_spec p n "env_find", callW_spec p n "nat_op_name", pinAt_specW p hp.pa n,
    callW_spec p n "erec_alloc", callW_spec p n "erec_put",
    callW_spec p n "lit_shape_ok",
    cvLps_specW p hp.val.cvg.alloc hp.val.cvg.copy hp.val.cvg.eti hp.val.cvg.lps n,
    slNodup_spec p hp.cont hp.nodup n, lbbF_spec p hp.val.cvg.bvb n, hffF_spec p hp.val.cvg.hf n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
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

theorem word_add31 (d : Word) : d + 3 + 1 = d + 4 := by rw [UInt64.add_assoc]; rfl

/-- **A fresh `axiomInfo cv` record** (`CI.axImg`): allocated (`CI.axiomSize`) above the top, the
kind word `0`, then the constant value at `q` copied field by field; `StageT` kept, the pools grown,
only the record pool and its tops written, the record decoding to `axiomInfo cv`. -/
theorem axRec_core {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m1 : Mem} {A q : Word} {cv : IConstantVal}
    (hS : StageT dn vis fe m a) (hqd : decCV (erecP m) q.toNat = some cv)
    (hA : erAllocW m CI.axiomSize = some (A, m1)) :
    StageT dn vis fe (wrERo m1 A (CI.axImg 0 (erRd m q) (erRd m (q + CV.lpsOff))
        (erRd m (q + CV.lpsLen)) (erRd m (q + CV.type)))) a ∧
      IWGrow m (wrERo m1 A (CI.axImg 0 (erRd m q) (erRd m (q + CV.lpsOff))
        (erRd m (q + CV.lpsLen)) (erRd m (q + CV.type)))) ∧
      MemFrame [EREC, tier1 EREC] [129, 130] m (wrERo m1 A (CI.axImg 0 (erRd m q)
        (erRd m (q + CV.lpsOff)) (erRd m (q + CV.lpsLen)) (erRd m (q + CV.type)))) ∧
      decCI (erecP (wrERo m1 A (CI.axImg 0 (erRd m q) (erRd m (q + CV.lpsOff))
        (erRd m (q + CV.lpsLen)) (erRd m (q + CV.type))))) A.toNat = some (.axiomInfo cv) := by
  obtain ⟨hT1, hg1, hoff, htop, h41⟩ := erAlloc_stageT hA hS
  have hf1 : MemFrame [] [129, 130] m m1 := (erAllocW_spec hA hS.stage.iw).2.1
  have hfq : MemFrame quotA quotC m m1 :=
    hf1.mono (fun _ h => by simp at h) (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> decide)
  generalize hI : CI.axImg 0 (erRd m q) (erRd m (q + CV.lpsOff)) (erRd m (q + CV.lpsLen))
    (erRd m (q + CV.type)) = I
  have hIl : I.length = CI.axiomSize.toNat := by rw [← hI, CI.axImg_length]
  obtain ⟨hS6, hg6, -, hrd, -⟩ := wrERo_fresh hS.stage I m1 a A hT1.stage hfq hg1 (by omega)
    (by rw [hIl, htop]; omega) h41
  refine ⟨StageT.of_wrERo hT1 hS6, hg6,
    (hf1.mono (fun _ h => by simp at h) (fun _ h => h)).trans
      ((wrERo_frame _ _ _).mono (fun _ h => h) (fun _ h => by simp at h)), ?_⟩
  have g := fun {o : Word} {x : Word} (e : I[o.toNat]? = some (some x)) => hrd o.toNat x e
  obtain ⟨en, enl, hsl, -, et, etl⟩ := decCV_rd (erRdOK m) hqd
  have adj : ∀ f : Word, f.toNat ≤ 64 →
      A.toNat + (CI.cv + f).toNat = A.toNat + CI.cv.toNat + f.toNat := fun f hf => by
    rw [CI.cv_add_toNat hf, Nat.add_assoc]
  have hw : CVRecW (erecP (wrERo m1 A I)) (A.toNat + CI.cv.toNat) (erRd m q) (erRd m (q + CV.lpsOff))
      (erRd m (q + CV.lpsLen)) (erRd m (q + CV.type)) :=
    ⟨by rw [← adj _ CV.name_le]; exact g (hI ▸ CI.axImg_name ..),
      by rw [← adj _ CV.lpsOff_le]; exact g (hI ▸ CI.axImg_lo ..),
      by rw [← adj _ CV.lpsLen_le]; exact g (hI ▸ CI.axImg_ll ..),
      by rw [← adj _ CV.type_le]; exact g (hI ▸ CI.axImg_ty ..)⟩
  have n0 := g (o := CI.kind) (hI ▸ CI.axImg_kind ..)
  rw [show CI.kind.toNat = 0 from rfl, Nat.add_zero] at n0
  refine decCI_axiomInfo_iff.mpr ⟨by simp [nat?, n0], ?_⟩
  rw [decCV_of_words hw enl etl (ArrExt.hslice? hg6.ext hsl), ← en, ← et]

/-- A word of the old pool is not overwritten by a store into a fresh region (`erFreshW`); the
allocation itself leaves the pool's words. -/
theorem axRd_fresh {m m1 : Mem} {A x : Word} {k : Word} (hA : erAllocW m k = some (A, m1))
    (hW : IWOK m) {w : Word} (hx : erecP m x.toNat = some w) :
    erRd m1 x = erRd m x ∧ ∀ (M : Mem) (o v : Word), o.toNat < k.toNat →
      erRd (erecPutMem M (A + o) v) x = erRd M x := by
  obtain ⟨-, hf1, -⟩ := erAllocW_spec hA hW
  refine ⟨by unfold erRd; rw [hf1.arr _ (by simp) (by rw [tierA_EREC]; split <;> decide)],
    fun M o v ho => erRd_erecPutMem_ne (erFreshW hA hW hx ho)⟩

/-- The stores of a fresh `axiomInfo` record (`axRec_core`'s image), in field order. -/
theorem axImg_eq (m1 : Mem) (A n lo ll t : Word) :
    erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem m1 A 0) (A + (CI.cv + CV.name)) n)
      (A + (CI.cv + CV.lpsOff)) lo) (A + (CI.cv + CV.lpsLen)) ll) (A + (CI.cv + CV.type)) t =
    wrERo m1 A (CI.axImg 0 n lo ll t) := by
  -- the image's entries in order (the layout's numbers: a whole-record writer)
  simp [wrERo, CI.axImg, recImg, rec_unfold, UInt64.add_assoc]

/-- **The fresh `axiomInfo cv` record `check_constant_val` builds for `lit_shape_ok`**: the stores
of `axRec_core`, the name and type read before them, the slice words between them. -/
theorem ccv_rec {p : Prog} (hp : RecProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m1 m2 m3 m4 m5 m6 : Mem} {q nw t : Word}
    {cv : IConstantVal} {r1 r2 r3 r4 r5 r6 : List Word}
    (hS : StageT dn vis fe m a) (hqd : decCV (erecP m) q.toNat = some cv)
    (hw0 : erRd m q = nw) (hw3 : erRd m (q + CV.type) = t)
    (h1 : callW p n "erec_alloc" [CI.axiomSize] m = some (r1, m1))
    (h2 : callW p n "erec_put" [r1.headD 0, 0] m1 = some (r2, m2))
    (h3 : callW p n "erec_put" [r1.headD 0 + (CI.cv + CV.name), nw] m2 = some (r3, m3))
    (h4 : callW p n "erec_put" [r1.headD 0 + (CI.cv + CV.lpsOff),
      rdW (m3.arr64 (L.tierA EREC ((q + CV.lpsOff) >>> 40))) (q + CV.lpsOff &&& 1099511627775)] m3 =
        some (r4, m4))
    (h5 : callW p n "erec_put" [r1.headD 0 + (CI.cv + CV.lpsLen),
      rdW (m4.arr64 (L.tierA EREC ((q + CV.lpsLen) >>> 40))) (q + CV.lpsLen &&& 1099511627775)] m4 =
        some (r5, m5))
    (h6 : callW p n "erec_put" [r1.headD 0 + (CI.cv + CV.type), t] m5 = some (r6, m6)) :
    StageT dn vis fe m6 a ∧ IWGrow m m6 ∧ MemFrame [EREC, tier1 EREC] [129, 130] m m6 ∧
      decCI (erecP m6) (r1.headD 0).toNat = some (.axiomInfo cv) := by
  have hA := callW_erecAlloc hp.alloc h1
  generalize r1.headD 0 = A at hA h2 h3 h4 h5 h6 ⊢
  rw [callW_erecPut hp.put h2] at h3
  rw [callW_erecPut hp.put h3] at h4
  rw [callW_erecPut hp.put h4] at h5
  rw [callW_erecPut hp.put h5] at h6
  rw [callW_erecPut hp.put h6]
  simp only [erRd_foldN]
  -- the slice words, read between the stores: the pool's words, above which the stores are
  obtain ⟨w1, w2, hw1, hw2, -⟩ := decCV_slice hqd
  have fo := axRd_fresh hA hS.stage.iw (by rw [rd_off_toNat (erRdOK m) hw1]; exact hw1)
  have fl := axRd_fresh hA hS.stage.iw (by rw [rd_off_toNat (erRdOK m) hw2]; exact hw2)
  have o0 : ∀ {x : Word} (f : erRd m1 x = erRd m x ∧ ∀ (M : Mem) (o v : Word),
      o.toNat < CI.axiomSize.toNat → erRd (erecPutMem M (A + o) v) x = erRd M x) (M : Mem) (v : Word),
      erRd (erecPutMem M A v) x = erRd M x := fun f M v => by simpa using f.2 M 0 v (by decide)
  rw [fo.2 _ _ _ (by decide), o0 fo, fo.1, fl.2 _ _ _ (by decide), fl.2 _ _ _ (by decide), o0 fl,
    fl.1, ← hw0, ← hw3, axImg_eq]
  exact axRec_core hS hqd hA

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

/-- `apdF_okT` with the twin state named: the run ends at the state it starts from
(`apdEntry_ok`), which the value guards' message (`readName`) needs. -/
theorem apdF_okT_keep (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (o l e : Word)
    (he : H e) (lps : List NIdx) (a₀ : AState) :
    RelW apdF [o, l, e]
      (fun m a => StageT dn vis fe m a ∧ decHL m o.toNat l.toNat = some lps ∧
        (∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks) ∧ a = a₀)
      (allLevelParamsDefined lps (decI e))
      (fun m m' a r x => KeepPostT dn vis fe decW0B m m' a r x ∧ a = a₀) := by
  intro m m' a r h ⟨hT, hdec, ⟨ks, hks⟩, ha⟩
  obtain ⟨n, hc⟩ := callF_run h
  rcases n with _ | n
  · rw [callW_zero] at hc; cases hc
  obtain ⟨s', hs', -, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (allLevelParamsDefined_spec_raw apdP apdP_prog.eview apdP_prog.lsnode apdP_prog.find
      apdP_prog.put apdP_prog.clear apdP_prog.lmem apdP_prog.lnode apdP_prog.lapd apdP_prog.ls
      apdP_prog.go apdP_prog.entry n ⟨m, Locals.init []⟩ o l e) hc
  subst hs'
  obtain ⟨b, hrun, hr, hS', hg, mp, hM⟩ := apdEntry_ok n hT.stage
    (ApdEnv.of_den hT.twin.den hT.twin.nwf) o l e _ lps ks hks hdec he
    (apdMR_clear hT.twin.memos.walk) hm
  have hf := apdF_frame h
  refine ⟨b, a, hrun, ⟨⟨hS', hT.twin.apd hf hM, ?_⟩, hg, L.Ind.decW0B_of hr⟩, ha⟩
  rw [pinW_frame hf (by decide)]; exact hT.flag

/-- `crfF_okT` with the twin state named: the run ends at the state it starts from
(`constsResolveFFast_keepsSt`). -/
theorem crfF_okT_keep (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (e : Word) (he : H e)
    (a₀ : AState) :
    RelW crfF [vis, e] (fun m a => StageT dn vis fe m a ∧ CrMemo m ∧ a = a₀) (constsResolveFFast fe (decI e))
      (fun m m' a r x => (KeepPostT dn vis fe decW0B m m' a r x ∧ CrMemo m') ∧ a = a₀) := by
  intro m m' a r h ⟨hT, hCr, ha⟩
  subst ha
  have hf := crfF_frame h
  obtain ⟨x, a', hrun, ⟨hS', hg, hd⟩, hCr', rfl⟩ := relW_callF (P := crfP)
    (L.Stubs.constsResolveFFast_keepsSt crfP_prog (vis := vis) (fe := fe) e he a).refAM
    m m' a r h ⟨hT.stage, hCr, rfl⟩
  exact ⟨x, _, hrun, ⟨⟨⟨hS', hT.twin.frame hf (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide), by rw [pinW_frame hf (by decide)]; exact hT.flag⟩, hg, hd⟩, hCr'⟩, rfl⟩

/-- **`check_constant_val` refines `checkConstantVal .verified`, both outcomes**, under `StageT`:
the duplicate guard, the certified-operation name, the literal shape of a fresh
`axiomInfo cv` record (`ccv_rec`, `CcvSims.lit`), the universe parameters, the closedness walks,
the consts-resolve site (`uce_errClaim_lo`), then the type's sort by the core. -/
theorem ccv_ref {p : Prog} (hP : CcvProg p) (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hcrf : L.Ind.CrfF p)
    {dn : NIdx → Option ConLeche.Name} (hC : CcvSims p dn) {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {q allow allowRd allowSorry : Word} {cv : IConstantVal}
    {c : ConLeche.ConstantVal} (hS : StageT dn vis fe m a) (hqd : decCV (erecP m) q.toNat = some cv)
    (hden : Frontend.denoteCV a.store cv = some c)
    (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkConstantValE p n m vis q allow allowRd allowSorry)
      (checkConstantVal V fe cv (allow != 0) (allowRd != 0) (allowSorry != 0)) a
      (fun v _ a' => CcvPost dn vis fe m v.2 a') := by
  obtain ⟨wx, hwx, hwxl, hname⟩ := decCV_name hqd
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hqd
  obtain ⟨wt, hwt, hwtl, hty⟩ := (decCV_words hqd).2.2
  have ex : rdW (m.arr64 (L.tierA EREC (q >>> 40))) (q &&& 1099511627775) = wx := by
    rw [erRd_congr rfl rfl]; exact erRd_of _ _ hwx
  have et : rdW (m.arr64 (L.tierA EREC ((q + CV.type) >>> 40))) (q + CV.type &&& 1099511627775) = wt :=
    (erRdOK m).at CV.type rfl hwt
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
  -- `nat_op_name(x)`
  refine RefE.bindSim (fun _ => checkConstantValE.k_nat_op_name.none ..)
    (hname ▸ hC.natOp n vis fe m a wx hS.stage hwxl) fun r3 x3 m3 a3 h3 hrun3 ⟨hm3, ha3, hx3⟩ => ?_
  subst m3 a3
  by_cases hb3 : r3.headD 0 ≠ 0 ∧ allow = 0
  · rw [checkConstantValE.k_nat_op_name.abort1 p _ _ _ _ _ _ _ _ _ _ hb3]
    have hx : x3 = true := hx3.mp hb3.1
    subst hx
    refine RefE.ite_pos (by simp [hb3.2]) fun _ => ?_
    exact ErrClaim.bind_right (L.Front.Ind.readName_run a _ _ hnm) (ErrClaim.fail_abort _ _ rfl)
  rw [checkConstantValE.k_nat_op_name.arm1 p _ _ _ _ _ _ _ _ _ _ hb3]
  refine RefE.ite_neg (fun hc => hb3 ?_) ?_
  · simp only [Bool.and_eq_true, Bool.not_eq_true', bne_eq_false_iff_eq] at hc
    exact ⟨hx3.mpr hc.1, hc.2⟩
  -- the compiler-trust names (`reduceOpNames`, pin slots `43`, `44`)
  refine RefE.onlySim (fun _ => checkConstantValE.k_pin_at.none ..) (fun _ _ h => h) fun r4 m4 h4 => ?_
  obtain ⟨hm4, hr4, hl4, hrun4⟩ := pinAtW_ok h4 hS.stage.check.pins
  subst m4 r4
  rw [checkConstantValE.k_pin_at.arm1]
  refine RefE.onlySim (fun _ => checkConstantValE.k_pin_at_2.none ..) (fun _ _ h => h) fun r5 m5 h5 => ?_
  obtain ⟨hm5, hr5, hl5, hrun5⟩ := pinAtW_ok h5 hS.stage.check.pins
  subst m5 r5
  have hnames : (reduceOpNames).run a =
      .ok ([decI (pinW m (1 + (43 : Word).toNat)), decI (pinW m (1 + (44 : Word).toNat))], a) := by
    simp only [reduceOpNames, reduceNatName, reduceBoolName, pinReduceNat, pinReduceBool,
      StateT.run_bind, show PIN_REDUCE_NAT = (43 : Word).toNat from rfl,
      show PIN_REDUCE_BOOL = (44 : Word).toNat from rfl, hrun4, L.Arena.except_ok_bind, hrun5]
    rfl
  refine RefE.bind_right hnames ?_
  have hb43 := decI_beq (k := .name) wx (pinW m (1 + (43 : Word).toNat)) hwxl hl4
  have hb44 := decI_beq (k := .name) wx (pinW m (1 + (44 : Word).toNat)) hwxl hl5
  have hcont : ([decI (pinW m (1 + (43 : Word).toNat)), decI (pinW m (1 + (44 : Word).toNat))] :
      List NIdx).contains (decI wx) = decide (wx = pinW m (1 + (43 : Word).toNat) ∨
        wx = pinW m (1 + (44 : Word).toNat)) := by
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, hb43, hb44]
    by_cases h1 : wx = pinW m (1 + (43 : Word).toNat) <;> by_cases h2 : wx = pinW m (1 + (44 : Word).toNat) <;>
      simp [h1, h2]
  rw [hname, hcont]
  by_cases hb5 : (wx = pinW m (1 + (43 : Word).toNat) ∨ wx = pinW m (1 + (44 : Word).toNat)) ∧ allowRd = 0
  · rw [checkConstantValE.k_pin_at_2.abort1 p _ _ _ _ _ _ _ _ _ _ hb5.1 hb5.2]
    refine RefE.ite_pos (by simpa [hb5.2] using hb5.1) fun _ => ?_
    exact ErrClaim.bind_right (L.Front.Ind.readName_run a _ _ (by rw [← hname]; exact hnm))
      (ErrClaim.fail_abort _ _ rfl)
  refine RefE.ite_neg (fun hc => hb5 (by simpa using hc)) ?_
  have hj : checkConstantValE.k_pin_at_2 p n vis q allowRd allowSorry wx wt (pinW m (1 + (43 : Word).toNat))
      (.ok ([pinW m (1 + (44 : Word).toNat)], m)) = checkConstantValE.j1 p n vis q allowSorry wx wt m := by
    by_cases hor : wx = pinW m (1 + (43 : Word).toNat) ∨ wx = pinW m (1 + (44 : Word).toNat)
    · exact checkConstantValE.k_pin_at_2.arm1 p _ _ _ _ _ _ _ _ _ _ hor (fun h => hb5 ⟨hor, h⟩)
    · exact checkConstantValE.k_pin_at_2.arm2 p _ _ _ _ _ _ _ _ _ _ hor
  simp only [List.headD_cons] at hj ⊢
  rw [hj]
  -- `sorryAx`'s name (pin slot `13`)
  rw [checkConstantValE.j1.arm1]
  refine RefE.onlySim (fun _ => checkConstantValE.k_pin_at_3.none ..) (fun _ _ h => h) fun r6 m6 h6 => ?_
  obtain ⟨hm6, hr6, hl6, hrun6⟩ := pinAtW_ok h6 hS.stage.check.pins
  subst m6 r6
  refine RefE.bind_right (x := pinSorryAx)
    (by simpa only [pinSorryAx, show PIN_SORRY_AX = (13 : Word).toNat from rfl] using hrun6) ?_
  have hb13 := decI_beq (k := .name) wx (pinW m (1 + (13 : Word).toNat)) hwxl hl6
  rw [hb13]
  by_cases hb6 : wx = pinW m (1 + (13 : Word).toNat) ∧ allowSorry = 0
  · rw [checkConstantValE.k_pin_at_3.abort1 p _ _ _ _ _ _ _ _ hb6]
    refine RefE.ite_pos (by simpa [hb6.2] using hb6.1) fun _ => ?_
    exact ErrClaim.bind_right (L.Front.Ind.readName_run a _ _ (by rw [← hname]; exact hnm))
      (ErrClaim.fail_abort _ _ rfl)
  rw [checkConstantValE.k_pin_at_3.arm1 p _ _ _ _ _ _ _ _ hb6]
  refine RefE.ite_neg (fun hc => hb6 (by simpa using hc)) ?_
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
  obtain ⟨hT9, hg9, hf9, hci9⟩ := ccv_rec hP.val.rcp hS hqd (erRd_of _ _ hwx) ((erRdOK m).at CV.type rfl hwt)
    h4 h5 h6 h7 h8 h9
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
  have e1 : rdW (m10.arr64 (L.tierA EREC ((q + CV.lpsOff) >>> 40))) (q + CV.lpsOff &&& 1099511627775) =
      w1 := by
    rw [erRd_congr rfl rfl]; exact (erRdOK m10).at _ rfl (hg0.ext _ _ hw1)
  have e2 : rdW (m10.arr64 (L.tierA EREC ((q + CV.lpsLen) >>> 40))) (q + CV.lpsLen &&& 1099511627775) =
      w2 := by
    rw [erRd_congr rfl rfl]; exact (erRdOK m10).at _ rfl (hg0.ext _ _ hw2)
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
    (fun b h8 => apdF_okT_keep dn vis fe (r11.headD 0) (r11.tail.headD 0) wt hwtl cv.levelParams a7 m7 b.2
      a7 b.1 (apdF_of_callW hap h8) ⟨hS7, hdec7, by rw [hst7]; exact hlpsN, rfl⟩)
    fun r8 m8 x8 a8 h8 _ ⟨⟨hS8, hg8, hx8, _⟩, ha8⟩ => ?_
  have h8' := apdF_of_callW hap (callW_of_callE h8)
  have hCr8 := CrOK.frame hCr7 (apdF_frame h8') (by decide) (by decide)
  have hA8 : AFr m m8 := fun hA => absOK_apdF h8' (hA7 hA) hS8
  dsimp only [checkConstantValE.k_all_level_params_defined]
  refine RefE.guardIf rfl (fun hb8 => by rw [← hx8]; simpa using hb8)
    (fun hb8 => by rw [← hx8] at hb8; simpa using hb8) fun _ _ => ?_
  -- `consts_resolve_ffast(vis, t)`
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h9 => nvl hG.nv (by decide +kernel) h9)
    (fun b h9 => crfF_okT_keep dn vis fe wt hwtl a8 m8 b.2 a8 b.1 (crfF_of_callW hcrf h9)
      ⟨hS8, hCr8.crMemo, rfl⟩)
    fun r9 m9' x9 a9 h9 _ ⟨⟨⟨hS9, hg9', hx9, _⟩, hCr9'⟩, ha9⟩ => ?_
  have hA9' : AFr m m9' := fun hA =>
    absOK_crfF' (crfF_of_callW hcrf (callW_of_callE h9)) (hA8 hA) hCr9'.crOK hS9
  have hnm9 : denoteN a9.store.ns (decI wx) = some c.name := by
    rw [ha9, ha8, hst7, ← hname]; exact (ConRon.Bridge.denoteCV_inv hden').1
  dsimp only [checkConstantValE.k_consts_resolve_ffast]
  refine RefE.splitNot (fun hb9 => by rw [← hx9]; simpa using hb9)
    (fun hb9 => by rw [← hx9] at hb9; simpa using hb9) (fun _ _ => ?_) fun _ _ => ?_
  · -- the unresolved constants' error (`unresolvedConstsErrorL` over `strLitStored`)
    rcases h10 : callE p (n + 1) "unresolved_consts_error" [vis, wt, 0] m9' with e10 | ⟨r10, m10⟩ <;>
      dsimp only [checkConstantValE.k_unresolved_consts_error]
    · obtain ⟨M9, hC9⟩ := hS9.core
      exact fun hG => ErrClaim.bind_right (L.Front.Ind.readName_run a9 _ _ hnm9)
        (uce_errClaim_lo hG.uce hG.nv hC9 hwtl (by decide) h10 _)
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
theorem vg_ref {p : Prog} (_hP : CcvProg p) (hap : ApdF p) (hcrf : L.Ind.CrfF p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} (n : Nat) {m : Mem}
    {q v : Word} {cv : IConstantVal} (hS : StageT dn vis fe m a)
    (hqd : decCV (erecP m) q.toNat = some cv) (hv : v.toNat < 2 ^ 32)
    (hcvd : ∃ c, Frontend.denoteCV a.store cv = some c) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (valueGuardsE p n m vis q v) (valueGuards fe cv (decI v)) a
      (fun w _ a' => CcvPost dn vis fe m w.2 a') := by
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hqd
  obtain ⟨cP, hcP⟩ := hcvd
  have hlps := denoteCV_lps hcP
  have hnm : denoteN a.store.ns cv.name = some cP.name := (ConRon.Bridge.denoteCV_inv hcP).1
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
  have e1 : rdW (m7.arr64 (L.tierA EREC ((q + CV.lpsOff) >>> 40))) (q + CV.lpsOff &&& 1099511627775) =
      w1 := by
    rw [erRd_congr rfl rfl]; exact (erRdOK m7).at _ rfl (hg0.ext _ _ hw1)
  have e2 : rdW (m7.arr64 (L.tierA EREC ((q + CV.lpsLen) >>> 40))) (q + CV.lpsLen &&& 1099511627775) =
      w2 := by
    rw [erRd_congr rfl rfl]; exact (erRdOK m7).at _ rfl (hg0.ext _ _ hw2)
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
    (fun b h8 => apdF_okT_keep dn vis fe (r11.headD 0) (r11.tail.headD 0) v hv cv.levelParams a7 m11 b.2 a7
      b.1 (apdF_of_callW hap h8) ⟨hT11, hdec11, by rw [hst7]; exact hlps, rfl⟩)
    fun r8 m8 x8 a8 h8 _ ⟨⟨hS8, hg8, hx8, _⟩, ha8⟩ => ?_
  have h8' := apdF_of_callW hap (callW_of_callE h8)
  have hCr8 := CrOK.frame hCr11 (apdF_frame h8') (by decide) (by decide)
  have hA8 : AFr m m8 := fun hA => absOK_apdF h8' (hA11 hA) hS8
  dsimp only [valueGuardsE.k_all_level_params_defined]
  refine RefE.guardIf rfl (fun hb8 => by rw [← hx8]; simpa using hb8)
    (fun hb8 => by rw [← hx8] at hb8; simpa using hb8) fun _ _ => ?_
  -- `consts_resolve_ffast(vis, v)`
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h9 => nvl hG.nv (by decide +kernel) h9)
    (fun b h9 => crfF_okT_keep dn vis fe v hv a8 m8 b.2 a8 b.1 (crfF_of_callW hcrf h9)
      ⟨hS8, hCr8.crMemo, rfl⟩)
    fun r9 m9' x9 a9 h9 _ ⟨⟨⟨hS9, hg9', hx9, _⟩, hCr9'⟩, ha9⟩ => ?_
  have hA9' : AFr m m9' := fun hA =>
    absOK_crfF' (crfF_of_callW hcrf (callW_of_callE h9)) (hA8 hA) hCr9'.crOK hS9
  have hnm9 : denoteN a9.store.ns cv.name = some cP.name := by rw [ha9, ha8, hst7]; exact hnm
  dsimp only [valueGuardsE.k_consts_resolve_ffast]
  refine RefE.splitNot (fun hb9 => by rw [← hx9]; simpa using hb9)
    (fun hb9 => by rw [← hx9] at hb9; simpa using hb9) (fun _ _ => ?_) fun _ _ => ?_
  · rcases h10 : callE p (n + 1) "unresolved_consts_error" [vis, v, 1] m9' with e10 | ⟨r10, m10⟩ <;>
      dsimp only [valueGuardsE.k_unresolved_consts_error]
    · obtain ⟨M9, hC9⟩ := hS9.core
      exact fun hG => ErrClaim.bind_right (L.Front.Ind.readName_run a9 _ _ hnm9)
        (uce_errClaim_lo hG.uce hG.nv hC9 hv (by decide) h10 _)
    · exact RefE.of_cls0 rfl
  exact RefE.ret rfl ⟨hS9, hg0.trans (hg11.trans (hg8.trans hg9')), hCr9'.crOK, hA9'⟩

/-- **`check_defn_val(vis, c)` refines `checkDefnVal`, both outcomes**, under `StageT`: the value's
guards (`vg_ref`), its type (`infer_type_core`) against the declared one (`is_def_eq_core`), the
mismatch the twin's `invalid`; the record `c` returned, unpushed. -/
theorem checkDefnVal_ref {p : Prog} (hP : CcvProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (hcrf : L.Ind.CrfF p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c : Word}
    {cv : IConstantVal} {wv : Word} {hint : ConLeche.ReducibilityHint} (hS : StageT dn vis fe m a)
    (hcv : decCV (erecP m) (c.toNat + CI.cv.toNat) = some cv) (hwv : erecP m (c.toNat + CI.defnValue.toNat) = some wv)
    (hwvl : wv.toNat < 2 ^ 32)
    (hcvd : ∃ c, Frontend.denoteCV a.store cv = some c) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkDefnValE p n m vis c) (checkDefnVal V fe cv (decI wv) hint) a
      (fun w y a' => CcvPost dn vis fe m w.2 a' ∧ w.1 = c ∧ y = .defnInfo cv (decI wv) hint) := by
  obtain ⟨wt, hwt, hwtl, hty⟩ := (decCV_words hcv).2.2
  have e1 : (c + CI.cv).toNat = c.toNat + CI.cv.toNat :=
    off_add_toNat rfl (by have := erecP_lt64 hwt; omega)
  have ev : rdW (m.arr64 (L.tierA EREC ((c + CI.defnValue) >>> 40))) (c + CI.defnValue &&& 1099511627775) =
      wv := (erRdOK m).at _ rfl hwv
  have et : rdW (m.arr64 (L.tierA EREC ((c + (CI.cv + CV.type)) >>> 40)))
      (c + (CI.cv + CV.type) &&& 1099511627775) = wt :=
    (erRdOK m).at _ (CI.cv_add_toNat CV.type_le) (by rw [← Nat.add_assoc]; exact hwt)
  cases n with
  | zero => rw [checkDefnValE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkDefnValE.arm1, ev, et]
  simp only [checkDefnVal]
  -- the value's guards
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => checkDefnValE.k_value_guards.none ..)
    (valueGuards_specE p hP n ⟨m, Locals.init []⟩ vis (c + CI.cv) wv) (fun hG => hG.nv) id
    (vg_ref hP hap hcrf n hS (by rw [e1]; exact hcv) hwvl hcvd hCr)
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
    (hcv : decCV (erecP m) (c.toNat + CI.cv.toNat) = some cv) (hwv : erecP m (c.toNat + CI.defnValue.toNat) = some wv)
    (hwvl : wv.toNat < 2 ^ 32)
    (hcvd : ∃ c, Frontend.denoteCV a.store cv = some c) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkOpaqueValE p n m vis c) (checkOpaqueVal V fe cv (decI wv)) a
      (fun w y a' => CcvPost dn vis fe m w.2 a' ∧ w.1 = c ∧ y = .axiomInfo cv) := by
  obtain ⟨wt, hwt, hwtl, hty⟩ := (decCV_words hcv).2.2
  have e1 : (c + CI.cv).toNat = c.toNat + CI.cv.toNat :=
    off_add_toNat rfl (by have := erecP_lt64 hwt; omega)
  have ev : rdW (m.arr64 (L.tierA EREC ((c + CI.defnValue) >>> 40))) (c + CI.defnValue &&& 1099511627775) =
      wv := (erRdOK m).at _ rfl hwv
  have et : rdW (m.arr64 (L.tierA EREC ((c + (CI.cv + CV.type)) >>> 40)))
      (c + (CI.cv + CV.type) &&& 1099511627775) = wt :=
    (erRdOK m).at _ (CI.cv_add_toNat CV.type_le) (by rw [← Nat.add_assoc]; exact hwt)
  cases n with
  | zero => rw [checkOpaqueValE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkOpaqueValE.arm1, ev, et]
  simp only [checkOpaqueVal]
  -- the value's guards
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => checkOpaqueValE.k_value_guards.none ..)
    (valueGuards_specE p hP n ⟨m, Locals.init []⟩ vis (c + CI.cv) wv) (fun hG => hG.nv) id
    (vg_ref hP hap hcrf n hS (by rw [e1]; exact hcv) hwvl hcvd hCr)
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
    (hcv : decCV (erecP m) (c.toNat + CI.cv.toNat) = some cv) (hwv : erecP m (c.toNat + CI.defnValue.toNat) = some wv)
    (hwvl : wv.toNat < 2 ^ 32)
    (hpre : ∃ env cP, ConLeche.EnvWF env ∧ ConRon.Bridge.CheckOK false env fe a ∧
      Frontend.denoteCV a.store cv = some cP ∧ ConLeche.Expr.WScoped 0 cP.type)
    (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkThmValE p n m vis c) (checkThmVal V fe cv (decI wv)) a
      (fun w y a' => StageT dn vis fe w.2 a' ∧ IWGrow m w.2 ∧ L.Stubs.CrOK w.2 ∧ w.1 = c ∧
        y = .thmInfo cv) := by
  have hL := hq.knot.lvc
  obtain ⟨wt, hwt, hwtl, hty⟩ := (decCV_words hcv).2.2
  have e1 : (c + CI.cv).toNat = c.toNat + CI.cv.toNat :=
    off_add_toNat rfl (by have := erecP_lt64 hwt; omega)
  have ev : rdW (m.arr64 (L.tierA EREC ((c + CI.defnValue) >>> 40))) (c + CI.defnValue &&& 1099511627775) =
      wv := (erRdOK m).at _ rfl hwv
  have et : rdW (m.arr64 (L.tierA EREC ((c + (CI.cv + CV.type)) >>> 40)))
      (c + (CI.cv + CV.type) &&& 1099511627775) = wt :=
    (erRdOK m).at _ (CI.cv_add_toNat CV.type_le) (by rw [← Nat.add_assoc]; exact hwt)
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
  have hcvd4 : ∃ c, Frontend.denoteCV a4.store cv = some c := by
    obtain ⟨env, cP, henv, hck, hcvd, hws⟩ := hpre
    obtain ⟨hck2, hx02⟩ := thmPrefix_ext henv hck hcvd hws (by rw [hty]; exact hrun1) hrun2
    obtain ⟨-, hst4, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a2) rfl hrun4
      (ConRon.Bridge.Core.lvlEq?_spec a2 _ _ hck2)
    rw [hst4]
    exact ⟨_, ConRon.Bridge.denoteCV_ext hcvd hx02⟩
  have hg14 := hg1.trans (hg2.trans hg4)
  -- the value's guards
  refine RefE.bindRun (s₀ := ⟨s4.mem, Locals.init []⟩) (fun _ => checkThmValE.k_value_guards.none ..)
    (valueGuards_specE p hP n ⟨s4.mem, Locals.init []⟩ vis (c + CI.cv) wv) (fun hG => hG.nv) id
    (vg_ref hP hap hcrf n hS4 (by rw [e1]; exact ArrExt.decCV (L.Ind.IWGrow.ext hg14) hcv)
      hwvl hcvd4 hCr4)
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
