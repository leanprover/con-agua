module

import ConRon.Bridge.Checker.Base
public import ConAgua.Verdict.DeclValsE
import ConAgua.Arena.RecClassSpec.CrW
import ConAgua.Arena.RecGenSpec.ClassFeR
public import ConAgua.Arena.RecGenSpec.ClassMinorSlot
import ConAgua.L.ModelGen
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RefWalk
import ConAgua.Arena.StageC
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.RecGen
public import ConRon.Bridge.Inductives.Records

@[expose] public section

/-!
# `classStreamRecs` under `StageC`, both outcomes (lane `indstaget`)

`class_stream_recs`' unified model (`csrE`): each recursor constant checked by the program's own
`check_constant_val` (its unified model, `ccv_ref`; `CheckOK` after from con-ron's
`checkConstantVal_bridge`), the recursion through the model itself, `sl_cons` (outside the verdict
closure) through its `Option` model. One refinement for both outcomes, `csr_ref`.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dRec dRec_ext dExt_denoteCV mapM_option_cons_inv dRec_inv)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

set_option experimental.vcgen true in
/-- **The model of `class_stream_recs`, both outcomes**: `check_constant_val` by its unified model,
the recursion by the model, `sl_cons` lifted. -/
l_model csrE_spec (p : Prog) (hV : CcvProg p) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hf : p.lookup "class_stream_recs" = some classStreamRecsL)
  fns [hf ↦ csrE]
  specs [checkConstantVal_specE p hV n, slCons_specW p ha hc hsc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `class_stream_recs` gives besides the twin's run: the stage, the growth, the result slice
(the recursors' constant pointers, in order), the walk memos. -/
structure CsrPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (w : List Word × Mem) (cvs : List IConstantVal) (a' : AState) : Prop where
  stage : StageC dn vis fe env w.2 a'
  grow : IWGrow m w.2
  res : CsRes w.2 w.1 cvs
  abs : AbsOK w.2

section sims
variable {dn : NIdx → Option ConLeche.Name} {env : ConLeche.Env}
variable {p : Prog} (hq : KnotStageProg p) (henv : ConLeche.EnvWF env) (hV : CcvProg p) (hcr : CrfF p) (hCS : CcvSims p dn)
  (hApd : ApdF p) (hCrk : CrKeep p)

include hq henv hV hcr hCS hApd hCrk in
/-- **`class_stream_recs` refines `classStreamRecs .verified` under `StageC`, both outcomes**
(twin side con-ron's `classStreamRecs_spec`): `check_constant_val` by `ccv_ref`, the rest by
induction. -/
theorem csr_ref (fe : IFEnv) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (vis rcso rcsl : Word) (recs : List RecShape)
      (recsP : List ConLeche.RecShape),
    StageC dn vis fe env m a → AbsOK m →
    RecsOK m rcso.toNat rcsl.toNat (recs.map (·.cvR)) → recs.mapM (dRec a.store) = some recsP →
    RefE (VerdictCtxU p) (csrE p n m vis rcso rcsl) (ConRon.Arena.classStreamRecs V fe recs) a
      (fun w cvs a' => CsrPost dn vis fe env m w cvs a') := by
  induction n with
  | zero =>
    intro m a vis rcso rcsl recs recsP _ _ _ _
    rw [csrE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a vis rcso rcsl recs recsP hC hA hOK hrecsP
  have hS := hC.stage
  by_cases hrl : rcsl = 0
  · rw [csrE.arm1 p n m vis rcso rcsl hrl]
    have hz : rcsl.toNat = 0 := by rw [hrl]; rfl
    have hlen := hOK.2.1
    rw [hz] at hlen
    have hnil : recs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hnil
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, ⟨[], by simp [decNL], by simp [decPL], by simp, by simp⟩, hA⟩
  rw [csrE.arm2 p n m vis rcso rcsl hrl]
  have hpos : 1 ≤ rcsl.toNat := by
    rcases Nat.eq_zero_or_pos rcsl.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hrl
    · omega
  obtain ⟨l1, hl1⟩ : ∃ l1, rcsl.toNat = l1 + 1 := ⟨rcsl.toNat - 1, by omega⟩
  have hlen := hOK.2.1
  obtain ⟨rc, rest, rfl⟩ : ∃ rc rest, recs = rc :: rest := by
    cases recs with
    | nil => simp at hlen; omega
    | cons rc rest => exact ⟨rc, rest, rfl⟩
  obtain ⟨rcP, restP, rfl, hrcP, hrestP⟩ := mapM_option_cons_inv hrecsP
  have hcvR := (dRec_inv hrcP).1
  rw [hl1] at hOK
  obtain ⟨⟨p0, q, hp0, hp1, hq', hcv, hext⟩, hOKt⟩ := RecsOK_cons (by simpa using hOK)
  have e0 : UInt64.ofNat rcso.toNat = rcso := UInt64.ofNat_toNat
  have hIW64 : (m.arr64 IW).size < 2 ^ 64 := hS.iw.iwSize
  have hrd0 := iwN_rdW hp0 (by have := iwN_lt hp0; omega)
  rw [e0] at hrd0
  have hrdq := iwN_rdW hq' (by omega)
  have hqb : q < 2 ^ 64 := hrdq.2
  rw [hrd0.1, hrdq.1]
  have hqt : (UInt64.ofNat q).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  unfold ConRon.Arena.classStreamRecs
  -- `check_constant_val`
  have h1R := ccv_ref (allow := 0) (allowRd := 0) (allowSorry := 0) hV hq hApd hCrk hcr hCS (n := n) (by omega) hC.stageT
    (by rw [hqt]; exact rec2DecCV_erecP hcv hext) hcvR hA.cr.crOK
  rcases h1 : checkConstantValE p n m vis (UInt64.ofNat q) 0 0 0 with e1 | ⟨r0, m1⟩
  · rw [csrE.k_check_constant_val.none]; rw [h1] at h1R; exact RefE.bind_left h1R
  rw [csrE.k_check_constant_val.arm1]
  rw [h1] at h1R
  obtain ⟨u, a1, hrun1, hP1⟩ := h1R
  obtain ⟨c1, -⟩ := ConRon.Bridge.checkConstantVal_bridge ConRon.Bridge.CoreSpec.of_core
    hC.check henv hcvR hrun1
  have hC1 : StageC dn vis fe env m1 a1 := StageC.of_T hP1.stage c1.ok
  have hA1 := hP1.abs hA
  have hg1 := hP1.grow
  refine RefE.bind_right hrun1 ?_
  have hOK1 : RecsOK m1 (rcso + 1).toNat (rcsl - 1).toNat (rest.map (·.cvR)) := by
    have htopsz : iwTop m ≤ (m.arr64 IW).size := hS.iw.iw
    have hOKb := hOK.1
    have hro1 : (rcso + 1).toNat = rcso.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hrl1 : (rcsl - 1).toNat = l1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp; omega
    rw [hro1, hrl1]
    exact RecsOK_grow hg1 hOKt
  -- the rest
  have h2R := ih (by omega) m1 a1 vis (rcso + 1) (rcsl - 1) rest restP hC1 hA1 hOK1
    (dRec_ext.list c1.ext _ _ hrestP)
  rcases h2 : csrE p n m1 vis (rcso + 1) (rcsl - 1) with e2 | ⟨r2, m2⟩
  · rw [csrE.k_class_stream_recs.none]; rw [h2] at h2R; exact RefE.bind_left h2R
  rw [csrE.k_class_stream_recs.arm1]
  rw [h2] at h2R
  obtain ⟨cvs2, a2, hrun2, hR2⟩ := h2R
  obtain ⟨hC2, hg2, ⟨ptrs2, hdn2, hdp2, hext2, htop2⟩, hA2⟩ := hR2
  dsimp only at hC2 hg2 hdn2 hdp2 hext2 htop2 hA2
  refine RefE.bind_right hrun2 ?_
  -- `sl_cons` (outside the verdict closure)
  refine RefE.onlySim (fun _ => csrE.k_sl_cons.none ..) (fun _ _ h => h) fun r3 m3 h3 => ?_
  rw [csrE.k_sl_cons.arm1]
  obtain ⟨hS3, hg3, hdn3, ht3⟩ := consW_stageN h3 hC2.stage htop2 hdn2
  have hA3 := consW_afr h3 hA2
  have hg13 := (hg1.trans hg2).trans hg3
  have hextm3 : CVExt m3 q := CVExt_grow hg13 hext
  refine RefE.ret rfl ⟨hC2.of_check hS3 hA3 hC2.check (Ext.refl _), hg13, ?_, hA3⟩
  refine ⟨q :: ptrs2, by simpa [hqt] using hdn3, ?_, ?_, by simpa using Nat.le_of_eq ht3⟩
  · have hdn3' : decNL m3 (r3.headD 0).toNat (r3.tail.headD 0).toNat = some (q :: ptrs2) := by
      simpa [hqt] using hdn3
    rw [decPL_eq_bind]
    simp only [List.headD_cons, List.tail_cons]
    rw [hdn3']
    simp only [Option.bind_some, List.mapM_cons]
    rw [decCVp_grow_r hg13 hext, hcv]
    have h2' : ptrs2.mapM (decCVp m2) = some cvs2 := by
      rw [decPL_eq_bind, hdn2] at hdp2; simpa using hdp2
    rw [mapM_decCVp_grow hg3 ptrs2 hext2, h2']
    rfl
  · intro q' hq''
    simp only [List.mem_cons] at hq''
    rcases hq'' with rfl | hq''
    · exact hextm3
    · exact CVExt_grow hg3 (hext2 q' hq'')

include hq henv hV hcr hCS hApd hCrk in
/-- **`class_stream_recs` refines `classStreamRecs .verified`** under `StageC` (the program's own
`check_constant_val`; `csr_ref`'s ok half): the result slice holds the recursors' constant
pointers, in order. -/
@[refines ConRon.Arena.classStreamRecs]
theorem classStreamRecs_refinesC (hc : p.lookup "iw_copy" = some iwCopy)
    (ha : p.lookup "iw_alloc" = some iwAlloc) (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "class_stream_recs" = some classStreamRecsL) (n : Nat) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (fe : IFEnv) (vis rcso rcsl : Word) (recs : List RecShape)
    (recsP : List ConLeche.RecShape) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hOK : RecsOK s₀.mem rcso.toNat rcsl.toNat (recs.map (·.cvR)))
    (hrecsP : recs.mapM (dRec a₀.store) = some recsP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_stream_recs" [vis, rcso, rcsl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classStreamRecs V fe recs) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.classStreamRecs V fe recs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ CsRes s'.mem r (AM.res (ConRon.Arena.classStreamRecs V fe recs) a₀) ∧
      AbsOK s'.mem; ⊤⦄ :=
  triple_post (RefE.triple (csrE_spec p hV ha hc hsc hp n s₀ vis rcso rcsl)
      (csr_ref hq henv hV hcr hCS hApd hCrk fe n hn _ a₀ vis rcso rcsl recs recsP hC hA hOK hrecsP))
    fun _ _ ⟨hl, _, _, hrun, hR⟩ => by
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
      exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.res, hR.abs⟩

end sims

/-- **`class_stream_recs`' error claim** (the hypotheses of `classStreamRecs_refinesC`). -/
theorem classStreamRecs_claim {p : Prog} {dn : NIdx → Option ConLeche.Name} {env : ConLeche.Env}
    (hq : KnotStageProg p) (henv : ConLeche.EnvWF env) (hV : CcvProg p) (hcr : CrfF p)
    (hCS : CcvSims p dn) (hApd : ApdF p) (hCrk : CrKeep p) (hG : VerdictCtxU p) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "class_stream_recs" = some classStreamRecsL) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (fe : IFEnv) (vis rcso rcsl : Word) (recs : List RecShape)
    (recsP : List ConLeche.RecShape) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hOK : RecsOK s₀.mem rcso.toNat rcsl.toNat (recs.map (·.cvR)))
    (hrecsP : recs.mapM (dRec a₀.store) = some recsP) :
    CoreSpecE p n "class_stream_recs" [vis, rcso, rcsl] (ConRon.Arena.classStreamRecs V fe recs) s₀ a₀ :=
  RefE.coreSpecE (csrE_spec p hV ha hc hsc hp n s₀ vis rcso rcsl) hG.nv hG
    (csr_ref hq henv hV hcr hCS hApd hCrk fe n hn s₀.mem a₀ vis rcso rcsl recs recsP hC hA hOK hrecsP)

end L.Ind

end
