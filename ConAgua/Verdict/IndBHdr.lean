module

import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.DeclCvgT
import ConAgua.Arena.IndT.WalkC
public import ConAgua.Arena.IndT.Base
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Verdict.DeclValsE
import all ConAgua.Arena.RecGen
import ConAgua.Arena.RecCheckSpec.ErToIwWStage
import ConAgua.L.WordOff
import ConAgua.Arena.IlpRd

@[expose] public section
/-!
# `class_const_ok_header`, `class_const_ok`: one model and one refinement for both outcomes

`class_const_ok_header` is `classConstOk`'s guards (the twin prefix `cchT`, `cchT_bind`): its
`l_model … unified` model lifts the callees outside the verdict closure, and `cch_ref` refines
`cchT` under `StageT`;
the consts-resolve site calls `unresolved_consts_error` (`uce_errClaim_hi`, so `G` is
`VerdictCtxU`); the literal-shape guard calls `class_const_ok_lit` (its model `cclLitW`, the fresh
`axiomInfo` record `ccl_rec`, `ccl_sim` through `CcvSims.lit`). `class_const_ok` (`cco_ref`) is the guards through `cch_ref`, then the knot's
`infer_type_core` and `ensure_sort_core`; its ok half is `classConstOk_refinesT` and
`class_rec_ty_ok`'s refinement, its error half the callers' error claims.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups `class_const_ok`'s refinement takes (`class_const_ok_header`'s callees, the
literal's record, `class_const_ok` itself). -/
structure CchProg (p : Prog) : Prop where
  cont : p.lookup "sl_contains" = some slContains
  nodup : p.lookup "sl_nodup" = some slNodup
  cvg : CvgProg p
  rcp : RecProg p
  basis : BasisProg p
  lit : p.lookup "class_const_ok_lit" = some classConstOkLit
  hdr : p.lookup "class_const_ok_header" = some classConstOkHeader
  cco : p.lookup "class_const_ok" = some classConstOkL

/-- **The model of `class_const_ok_lit(cv)`**: the fresh `axiomInfo` record, then `lit_shape_ok`. -/
l_model classConstOkLit_specW (p : Prog) (hp : p.lookup "class_const_ok_lit" = some classConstOkLit)
  fns [hp ↦ cclLitW list]
  specs [callW_spec p n "erec_alloc", callW_spec p n "erec_put", callW_spec p n "lit_shape_ok"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The fresh `axiomInfo cv` record `class_const_ok_lit` builds** (as `ccv_rec`, each source word
read just before its copy): `axRec_core`'s stores, the reads between them. -/
theorem ccl_rec {p : Prog} (hp : RecProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m1 m2 m3 m4 m5 m6 : Mem} {q : Word}
    {cv : IConstantVal} {r1 r2 r3 r4 r5 r6 : List Word}
    (hS : StageT dn vis fe m a) (hqd : decCV (erecP m) q.toNat = some cv)
    (h1 : callW p n "erec_alloc" [CI.axiomSize] m = some (r1, m1))
    (h2 : callW p n "erec_put" [r1.headD 0, 0] m1 = some (r2, m2))
    (h3 : callW p n "erec_put" [r1.headD 0 + (CI.cv + CV.name),
      rdW (m2.arr64 (L.tierA EREC (q >>> 40))) (q &&& 1099511627775)] m2 = some (r3, m3))
    (h4 : callW p n "erec_put" [r1.headD 0 + (CI.cv + CV.lpsOff),
      rdW (m3.arr64 (L.tierA EREC ((q + CV.lpsOff) >>> 40))) (q + CV.lpsOff &&& 1099511627775)] m3 = some (r4, m4))
    (h5 : callW p n "erec_put" [r1.headD 0 + (CI.cv + CV.lpsLen),
      rdW (m4.arr64 (L.tierA EREC ((q + CV.lpsLen) >>> 40))) (q + CV.lpsLen &&& 1099511627775)] m4 = some (r5, m5))
    (h6 : callW p n "erec_put" [r1.headD 0 + (CI.cv + CV.type),
      rdW (m5.arr64 (L.tierA EREC ((q + CV.type) >>> 40))) (q + CV.type &&& 1099511627775)] m5 = some (r6, m6)) :
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
  -- each source word, read between the stores: the pool's word, above which the stores are
  obtain ⟨⟨w0, hw0, -⟩, -, ⟨w3, hw3, -⟩⟩ := decCV_words hqd
  obtain ⟨w1, w2, hw1, hw2, -⟩ := decCV_slice hqd
  have r := erRdOK m
  have fn := axRd_fresh hA hS.stage.iw hw0
  have fo := axRd_fresh hA hS.stage.iw (by rw [rd_off_toNat r hw1]; exact hw1)
  have fl := axRd_fresh hA hS.stage.iw (by rw [rd_off_toNat r hw2]; exact hw2)
  have ft := axRd_fresh hA hS.stage.iw (by rw [rd_off_toNat r hw3]; exact hw3)
  have o0 : ∀ {x : Word} (f : erRd m1 x = erRd m x ∧ ∀ (M : Mem) (o v : Word),
      o.toNat < CI.axiomSize.toNat → erRd (erecPutMem M (A + o) v) x = erRd M x) (M : Mem) (v : Word),
      erRd (erecPutMem M A v) x = erRd M x := fun f M v => by simpa using f.2 M 0 v (by decide)
  rw [o0 fn, fn.1, fo.2 _ _ _ (by decide), o0 fo, fo.1, fl.2 _ _ _ (by decide),
    fl.2 _ _ _ (by decide), o0 fl, fl.1, ft.2 _ _ _ (by decide), ft.2 _ _ _ (by decide),
    ft.2 _ _ _ (by decide), o0 ft, ft.1, axImg_eq]
  exact axRec_core hS hqd hA

/-- **`class_const_ok_lit(q)` refines `litShapeOk (.axiomInfo cv)`** under `StageT` (`ccl_rec`, then
`CcvSims.lit` at the fresh record). -/
theorem ccl_sim {p : Prog} (hp : RecProg p) (hl : p.lookup "class_const_ok_lit" = some classConstOkLit)
    {dn : NIdx → Option ConLeche.Name} (hC : CcvSims p dn) {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m : Mem} {q : Word} {cv : IConstantVal}
    (hS : StageT dn vis fe m a) (hqd : decCV (erecP m) q.toNat = some cv)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) :
    Sim (callW p n "class_const_ok_lit" [q] m) (litShapeOk (.axiomInfo cv)) a
      (fun r b m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ (L.Stubs.CrOK m → L.Stubs.CrOK m') ∧
        AFr m m' ∧ (∀ cv' x, Frontend.denoteCV a.store cv' = some x →
          Frontend.denoteCV a'.store cv' = some x) ∧ (r.headD 0 ≠ 0 ↔ b = true)) := by
  intro r m' h
  obtain ⟨s', rfl, -, h0⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (classConstOkLit_specW p hl n _ q) h
  dsimp only at h0
  cases n with
  | zero => rw [cclLitW.eq_1] at h0; cases h0
  | succ n =>
  rw [cclLitW.arm1] at h0
  rcases h1 : callW p n "erec_alloc" [CI.axiomSize] m with _ | ⟨r1, m1⟩ <;> rw [h1] at h0
  · simp [cclLitW.k_erec_alloc] at h0
  rw [cclLitW.k_erec_alloc.arm1] at h0
  rcases h2 : callW p n "erec_put" [r1.headD 0, 0] m1 with _ | ⟨r2, m2⟩ <;> rw [h2] at h0
  · simp [cclLitW.k_erec_put] at h0
  rw [cclLitW.k_erec_put.arm1] at h0
  rcases h3 : callW p n "erec_put" [r1.headD 0 + (CI.cv + CV.name),
      rdW (m2.arr64 (L.tierA EREC (q >>> 40))) (q &&& 1099511627775)] m2 with _ | ⟨r3, m3⟩ <;> rw [h3] at h0
  · simp [cclLitW.k_erec_put_2] at h0
  rw [cclLitW.k_erec_put_2.arm1] at h0
  rcases h4 : callW p n "erec_put" [r1.headD 0 + (CI.cv + CV.lpsOff),
      rdW (m3.arr64 (L.tierA EREC ((q + CV.lpsOff) >>> 40))) (q + CV.lpsOff &&& 1099511627775)] m3 with _ | ⟨r4, m4⟩ <;>
    rw [h4] at h0
  · simp [cclLitW.k_erec_put_3] at h0
  rw [cclLitW.k_erec_put_3.arm1] at h0
  rcases h5 : callW p n "erec_put" [r1.headD 0 + (CI.cv + CV.lpsLen),
      rdW (m4.arr64 (L.tierA EREC ((q + CV.lpsLen) >>> 40))) (q + CV.lpsLen &&& 1099511627775)] m4 with _ | ⟨r5, m5⟩ <;>
    rw [h5] at h0
  · simp [cclLitW.k_erec_put_4] at h0
  rw [cclLitW.k_erec_put_4.arm1] at h0
  rcases h6 : callW p n "erec_put" [r1.headD 0 + (CI.cv + CV.type),
      rdW (m5.arr64 (L.tierA EREC ((q + CV.type) >>> 40))) (q + CV.type &&& 1099511627775)] m5 with _ | ⟨r6, m6⟩ <;>
    rw [h6] at h0
  · simp [cclLitW.k_erec_put_5] at h0
  rw [cclLitW.k_erec_put_5.arm1] at h0
  rcases h7 : callW p n "lit_shape_ok" [r1.headD 0] m6 with _ | ⟨r7, m7⟩ <;> rw [h7] at h0
  · simp [cclLitW.k_lit_shape_ok] at h0
  obtain ⟨hT6, hg6, hf6, hci6⟩ := ccl_rec hp hS hqd h1 h2 h3 h4 h5 h6
  obtain ⟨b, a', hrun, hT7, hg7, hcr7, hA7, hden7, hx7⟩ := hC.lit n vis fe m6 a _ _ hT6 hci6 hlps r7 m7 h7
  simp only [cclLitW.k_lit_shape_ok, Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  exact ⟨b, a', hrun, hT7, hg6.trans hg7, fun hCr => hcr7 (CrOK.frame hCr hf6 (by decide) (by decide)),
    (AFr.of_frame hf6).trans hA7, hden7, by simpa using hx7⟩

/-- **The model of `class_const_ok_header`, both outcomes**: the callees outside the verdict
closure through their `Option` models, the gates `all_level_params_defined`,
`consts_resolve_ffast` through `callE`. -/
l_model classConstOkHeaderE_spec (p : Prog) (hP : CchProg p)
  fns [hP.hdr ↦ classConstOkHeaderE]
  specs [callW_spec p n "env_find", callW_spec p n "class_const_ok_lit",
    cvLps_specW p hP.cvg.alloc hP.cvg.copy hP.cvg.eti hP.cvg.lps n,
    slNodup_spec p hP.cont hP.nodup n, lbbF_spec p hP.cvg.bvb n, hffF_spec p hP.cvg.hf n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


/-- **The twin's guards of `classConstOk`** (the prefix `class_const_ok_header` stands for): the
syntactic checks of the constant, in `classConstOk`'s order and with its messages. -/
def cchT (fe : IFEnv) (cv : IConstantVal) : AM Unit := do
  if (fe.find? cv.name).isSome then
    fail (.invalid "duplicate declaration")
  unless ← litShapeOk (.axiomInfo cv) do
    fail (.notImplemented "a declaration at a literal's name with another shape ()")
  unless nameNodup cv.levelParams do
    fail (.invalid "duplicate universe parameters in")
  unless ← looseBVarsBoundedFast coreWalkFuel 0 cv.type do
    fail (.internal "generated recursor: loose bound variable in type of")
  if ← hasFvarFast coreWalkFuel cv.type then
    fail (.internal "generated recursor: free variable in type of")
  unless ← allLevelParamsDefined cv.levelParams cv.type do
    fail (.invalid "undeclared universe parameter in type of")
  unless ← constsResolveFFast fe cv.type do
    fail (← unresolvedConstsError "type of" cv.type)

/-- `classConstOk` is its guards, then the inference. -/
theorem cchT_bind (mode : ConLeche.CheckMode) (fe : IFEnv) (cv : IConstantVal) :
    ConRon.Arena.classConstOk mode fe cv = cchT fe cv >>= fun _ => (do
      let stype ← inferTypeCore mode fe checkFuel 0 cv.type
      let _u ← ensureSortCore mode fe checkFuel 0 stype) := by
  simp only [ConRon.Arena.classConstOk, cchT, bind_assoc, ite_bindAM, fail_bindAM, pure_bind]

/-- What `class_const_ok_header` gives besides the twin's run of `classConstOk`'s guards (from `m`):
the stage invariant, the growth, the abstraction memo carried. -/
structure CchPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a' : AState) : Prop where
  stage : StageT dn vis fe m' a'
  grow : IWGrow m m'
  afr : AFr m m'

/-- **`class_const_ok_header` refines `classConstOk`'s guards (`cchT`), both outcomes**: the
name's guard (`env_find`), the literal's shape (`class_const_ok_lit`,
`ccl_sim`), the level parameters' copy and their duplicates (`cv_lps`, `sl_nodup`), the four walks
under `StageT` (`lbbF_okT`, `hffF_okT`, `apdF_okT`, `crfF_okT`), each a reject site of the twin's;
the consts-resolve site calls `unresolved_consts_error` (`uce_errClaim_hi`). -/
theorem cch_ref {p : Prog} (hP : CchProg p) (hApd : ApdF p) (hCrf : CrfF p)
    {dn : NIdx → Option ConLeche.Name} (hC : CcvSims p dn)
    {vis : Word} {fe : IFEnv} {a : AState} (n : Nat) {m : Mem} {q : Word} {cv : IConstantVal}
    {c : ConLeche.ConstantVal}
    (hS : StageT dn vis fe m a) (hqd : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hden : Frontend.denoteCV a.store cv = some c) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (classConstOkHeaderE p n m vis q) (cchT fe cv) a
      (fun v _ a' => CchPost dn vis fe m v.2 a') := by
  obtain ⟨wx, hwx, hwxl, hname⟩ := decCV_name hqd
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hqd
  obtain ⟨wt, hwt, hwtl, hty⟩ := (decCV_words hqd).2.2
  have ex : rdW (m.arr64 (L.tierA EREC (q >>> 40))) (q &&& 1099511627775) = wx := by
    rw [erRd_congr rfl rfl]; exact erRd_of _ _ hwx
  have hq3 : (q + 3).toNat = q.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have et : rdW (m.arr64 (L.tierA EREC ((q + 3) >>> 40))) (q + 3 &&& 1099511627775) = wt := by
    rw [erRd_congr rfl rfl]; exact erRd_of _ _ (by rw [hq3]; exact hwt)
  cases n with
  | zero => rw [classConstOkHeaderE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  rw [classConstOkHeaderE.arm1, ex, et]
  simp only [cchT, fail_bindAM]
  -- `env_find(x, vis)`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r1 m1 h1 => ?_
  obtain ⟨hm1, rfl⟩ := envFind_callB hP.basis hwxl hS.stage.check.env h1
  subst m1
  dsimp only [classConstOkHeaderE.k_env_find]
  refine RefE.guardThen (by rfl)
    (fun hb1 => by
      rw [hname]; obtain ⟨e1, ci', e2⟩ := findRes_hit hS.stage.check.env hwxl hb1; rw [e1, e2]; rfl)
    (fun hb => Classical.byContradiction fun hb1 => by
      rw [hname, findRes_miss hS.stage.check.env hwxl (by simpa using hb1)] at hb; cases hb)
    fun hb1 _ => ?_
  -- `class_const_ok_lit(q)`
  refine RefE.bindSim (fun _ => classConstOkHeaderE.k_class_const_ok_lit.none ..)
    (ccl_sim hP.rcp hP.lit hC hS hqd (denoteCV_lps hden))
    fun r3 x3 m3 a3 h3 hrun3 ⟨hT3, hg3, hcr3, hA3, hden3, hx3⟩ => ?_
  dsimp only [classConstOkHeaderE.k_class_const_ok_lit]
  refine RefE.guardIf rfl (fun hb => by cases hx : x3; rfl; exact absurd (hx3.mpr hx) (by simpa using hb))
    (fun hb => Classical.byContradiction fun hb' => by have := hx3.mp hb'; simp_all) fun _ _ => ?_
  have hCr3 := hcr3 hCr
  have hlpsN : ∃ ks, cv.levelParams.mapM (denoteN a3.store.ns) = some ks := denoteCV_lps (hden3 _ _ hden)
  -- `cv_lps(q)`
  have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hq2 : (q + 2).toNat = q.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e1 : rdW (m3.arr64 (L.tierA EREC ((q + 1) >>> 40))) (q + 1 &&& 1099511627775) = w1 := by
    rw [erRd_congr rfl rfl]; exact erRd_of _ _ (by rw [hq1]; exact hg3.ext _ _ hw1)
  have e2 : rdW (m3.arr64 (L.tierA EREC ((q + 2) >>> 40))) (q + 2 &&& 1099511627775) = w2 := by
    rw [erRd_congr rfl rfl]; exact erRd_of _ _ (by rw [hq2]; exact hg3.ext _ _ hw2)
  have hsl3 : hslice? (erA m3) w1.toNat w2.toNat = some cv.levelParams := ArrExt.hslice? hg3.ext hsl
  refine RefE.onlySim (fun _ => classConstOkHeaderE.k_cv_lps.none ..) (fun _ _ h => h) fun r11 m11 h11 => ?_
  rw [classConstOkHeaderE.k_cv_lps.arm1]
  cases n with
  | zero => simp [cvLpsW] at h11
  | succ n =>
  rw [cvLpsW_step, e1, e2] at h11
  obtain ⟨hS11R, hg11, hdec11, htop11, -⟩ := erToIwW_stage h11 hT3.stage hsl3
  have hT11 := StageT.of_iw hT3 hS11R (erToIwW_iwFr h11)
  have hCr11 := CrOK.frame hCr3 (erToIwW_iwFr h11) (by decide) (by decide)
  have hA11 : AFr m m11 := hA3.trans (erToIwW_afr h11)
  -- `sl_nodup(o, l)`
  rcases h12 : nodupW (n + 1) m11 (r11.headD 0) (r11.tail.headD 0) with _ | d
  · rw [liftE_none, classConstOkHeaderE.k_sl_nodup.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have htopb : iwTop m11 < 2 ^ 64 := by simp only [iwTop]; exact UInt64.toNat_lt _
  obtain ⟨ws, hws, hlps, hwsl⟩ := slR_of_decHL m11 _ _ _ hdec11 (by omega)
  simp only [UInt64.ofNat_toNat] at hws
  have hd := nodupW_ok _ _ _ _ _ _ hws h12
  dsimp only [classConstOkHeaderE.k_sl_nodup]
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
  refine RefE.bindSim (fun _ => rfl) (fun r m' h => lbbF_okT dn vis fe 4000000000 0 wt hwtl m11 m' a3 r h hT11)
    fun r6 x6 m6 a6 h6 hrun6 ⟨hS6, hg6, hx6, _⟩ => ?_
  have hCr6 := CrOK.frame hCr11 (lbbF_frame h6) (by decide) (by decide)
  have hA6 : AFr m m6 := hA11.trans (AFr.of_frame (lbbF_frame h6))
  dsimp only [classConstOkHeaderE.k_loose_bvars_bounded_fast]
  refine RefE.abort0 rfl fun hb6 => ?_
  rw [show x6 = true by rw [← hx6]; simpa using hb6]
  refine RefE.ite_pos rfl ?_
  -- `has_fvar_fast(4000000000, t)`
  refine RefE.bindSim (fun _ => rfl) (fun r m' h => hffF_okT dn vis fe 4000000000 wt hwtl m6 m' a6 r h hS6)
    fun r7 x7 m7 a7 h7 hrun7 ⟨hS7, hg7, hx7, _⟩ => ?_
  have hCr7 := CrOK.frame hCr6 (hffF_frame h7) (by decide) (by decide)
  have hA7 : AFr m m7 := hA6.trans (AFr.of_frame (hffF_frame h7))
  dsimp only [classConstOkHeaderE.k_has_fvar_fast]
  refine RefE.abort0 rfl fun hb7 => ?_
  rw [show x7 = false by rw [← hx7]; simpa using hb7]
  refine RefE.ite_neg (by decide) ?_
  -- `all_level_params_defined(o, l, t)`
  have hdec7 : decHL m7 (r11.headD 0).toNat (r11.tail.headD 0).toNat = some cv.levelParams := by
    rw [decHL_grow (hg6.trans hg7) (by omega), hdec11]
  have hst7 : a7.store = a3.store := (hffF_store hrun7).trans (lbbF_store hrun6)
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h8 => nvl hG.nv (by decide +kernel) h8)
    (fun b h8 => apdF_okT dn vis fe (r11.headD 0) (r11.tail.headD 0) wt hwtl cv.levelParams m7 b.2 a7 b.1
      (apdF_of_callW hApd h8) ⟨hS7, hdec7, by rw [hst7]; exact hlpsN⟩)
    fun r8 m8 x8 a8 h8 _ ⟨hS8, hg8, hx8, _⟩ => ?_
  have h8' := apdF_of_callW hApd (callW_of_callE h8)
  have hCr8 := CrOK.frame hCr7 (apdF_frame h8') (by decide) (by decide)
  have hA8 : AFr m m8 := fun hA => absOK_apdF h8' (hA7 hA) hS8
  dsimp only [classConstOkHeaderE.k_all_level_params_defined]
  refine RefE.guardIf rfl (fun hb8 => by rw [← hx8]; simpa using hb8)
    (fun hb8 => by rw [← hx8] at hb8; simpa using hb8) fun _ _ => ?_
  -- `consts_resolve_ffast(vis, t)`
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h9 => nvl hG.nv (by decide +kernel) h9)
    (fun b h9 => crfF_okT dn vis fe wt hwtl m8 b.2 a8 b.1 (crfF_of_callW hCrf h9) ⟨hS8, hCr8.crMemo⟩)
    fun r9 m9 x9 a9 h9 _ ⟨⟨hS9, hg9, hx9, _⟩, hCr9⟩ => ?_
  have hA9 : AFr m m9 := fun hA =>
    absOK_crfF' (crfF_of_callW hCrf (callW_of_callE h9)) (hA8 hA) hCr9.crOK hS9
  dsimp only [classConstOkHeaderE.k_consts_resolve_ffast]
  refine RefE.splitNot (fun hb9 => by rw [← hx9]; simpa using hb9)
    (fun hb9 => by rw [← hx9] at hb9; simpa using hb9) (fun _ _ => ?_) fun _ _ => RefE.ret rfl
      ⟨hS9, hg3.trans (hg11.trans (hg6.trans (hg7.trans (hg8.trans hg9)))), hA9⟩
  rcases h10 : callE p (n + 1) "unresolved_consts_error" [vis, wt, 2] m9 with e10 | ⟨r10, m10⟩ <;>
    dsimp only [classConstOkHeaderE.k_unresolved_consts_error]
  · obtain ⟨M9, hC9⟩ := hS9.core
    exact fun hG => uce_errClaim_hi hG.uce hG.nv hC9.arena.base hC9.pins hwtl (by decide) h10 "type of"
  · exact RefE.of_cls0 rfl

end L.Arena

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model classConstOkE_spec (p : Prog) (h : CchProg p)
  fns [h.cco ↦ classConstOkE] specs [classConstOkHeaderE_spec p h n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `class_const_ok` gives besides the twin's run (from `m`): the stage invariant, the
growth, the abstraction memo. -/
structure CcoPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a' : AState) : Prop where
  stage : StageT dn vis fe m' a'
  grow : IWGrow m m'
  abs : AbsOK m'

section cco
variable {p : Prog} (hP : CchProg p) (hq : KnotStageProg p) (hApd : ApdF p) (hCrf : CrfF p)
  {dn : NIdx → Option ConLeche.Name} (hC : CcvSims p dn) {vis : Word} {fe : IFEnv}

include hP hq hApd hCrf hC in
/-- **`class_const_ok` refines `classConstOk`, both outcomes**: its guards (`cch_ref`, against
`cchT`: `cchT_bind`), then the knot's `infer_type_core` and `ensure_sort_core` (their ok halves
`Base.lean`'s, their errors the core stubs' claims). -/
theorem cco_ref (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {q : Word} {cv : IConstantVal}
    {c : ConLeche.ConstantVal}
    (hS : StageT dn vis fe m a) (hq' : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hA : AbsOK m) (hden : Frontend.denoteCV a.store cv = some c) :
    RefE (VerdictCtxU p) (classConstOkE p n m vis q) (ConRon.Arena.classConstOk V fe cv) a
      (fun v _ a' => CcoPost dn vis fe m v.2 a') := by
  cases n with
  | zero => rw [classConstOkE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  rw [classConstOkE.arm1, cchT_bind]
  refine RefE.bindE (fun _ => rfl) id (cch_ref hP hApd hCrf hC n hS hq' hqb hden hA.cr)
    fun ⟨r1, m1⟩ _ a1 hrun ⟨hS1, hg1, hA1⟩ => ?_
  dsimp only [classConstOkE.k_class_const_ok_header]
  obtain ⟨wt, hwt, hwtl, hty⟩ := (decCV_words hq').2.2
  have hq3 : (q + 3).toNat = q.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have et : rdW (m1.arr64 (L.tierA EREC ((q + 3) >>> 40))) (q + 3 &&& 1099511627775) = wt := by
    rw [erRd_congr rfl rfl]; exact erRd_of _ _ (by rw [hq3]; exact hg1.ext _ _ hwt)
  rw [et, hty]
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h2 => hG.core.inferTypeCore n (by omega) hS1 0 wt hwtl _ h2)
    (RSim.coreAbs hq.closed (by decide) (hA1 hA) (inferT_rsim hq n (by omega) hS1 0 wt hwtl))
    fun r2 m2 _ a2 _ hrun2 ⟨⟨hS2, hg2, hb2, rfl⟩, hA2⟩ => ?_
  dsimp only [classConstOkE.k_infer_type_core]
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h3 => hG.core.ensureSortCore n (by omega) hS2 0 (r2.headD 0) hb2 _ h3)
    (RSim.coreAbs hq.closed (by decide) hA2 (ensureSortT_rsim hq n (by omega) hS2 0 (r2.headD 0) hb2))
    fun r3 m3 _ a3 _ hrun3 ⟨⟨hS3, hg3, _⟩, hA3⟩ => ?_
  exact RefE.ret rfl ⟨hS3, (hg1.trans hg2).trans hg3, hA3⟩

include hP hq hApd hCrf hC in
/-- **`class_const_ok` refines `classConstOk`** under `StageT` (`cco_ref`'s ok half). -/
@[refines ConRon.Arena.classConstOk]
theorem classConstOk_refinesT (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (q : Word) (cv : IConstantVal) {c : ConLeche.ConstantVal} (hS : StageT dn vis fe s₀.mem a₀)
    (hq' : decCV (erecP s₀.mem) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hA : AbsOK s₀.mem) (hden : Frontend.denoteCV a₀.store cv = some c) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_const_ok" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classConstOk V fe cv) a₀ ∧
      KPT dn vis fe s₀.mem decUnit (r, s'.mem) (AM.st (ConRon.Arena.classConstOk V fe cv) a₀)
        (AM.res (ConRon.Arena.classConstOk V fe cv) a₀) ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (classConstOkE_spec p hP n s₀ vis q)
    (cco_ref hP hq hApd hCrf hC n hn hS hq' hqb hA hden)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, ⟨by rw [hst]; exact hR.stage, hR.grow, trivial⟩, hR.abs⟩

end cco

end L.Ind

end
