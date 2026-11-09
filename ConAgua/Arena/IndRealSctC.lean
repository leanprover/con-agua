module

import ConRon.Bridge.Inductives.BlockInstall
import ConRon.Bridge.Inductives.StructParts
import ConAgua.Arena.RecCheckSpec.DecHLTruncMBound
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.TblFrame
import ConAgua.Arena.IndSumSpec.CheckSumCtor
import ConAgua.Arena.IndInstallSpec.ConsBlockCtors
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl
import ConAgua.Arena.IndInstallSpec.NestCtx
import ConAgua.Arena.IndInstallSpec.PosFreeMfr
public import ConAgua.Arena.IndSumSpec.Row
public import ConAgua.Arena.IndSumSpec.StructUsedLater
public import ConAgua.Arena.IndPosSpec.MatesW
public import ConRon.Arena.Inductives.BlockTail
import ConAgua.Arena.IndInstallSpec.TabSimSpg
public import ConAgua.Arena.IndRealApdT
import ConRon.Bridge.Inductives.BlockTail
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import all Init.Data.List.Control
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndInstallSpec.PartsAt
import ConAgua.Arena.IndPartsSpec.EqW
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndRealMemoCr
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.IndInstallSpec.DecCNS
public import ConAgua.Arena.IndInstallSpec.DecISS
public import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
public import ConAgua.Arena.IndSumSpec.StructProjBodies
import all ConAgua.Arena.Env
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.IndSum

@[expose] public section

/-!
# `check_struct_proj_table_scoped` through the real `all_level_params_defined` (lane `indproofs4`, helper `sct`)

`sctW` reads `all_level_params_defined` through a `CallM` (`IndSumSpec/ConsBlockRecsTF.lean`); `sctW_ok` is the
`stubCall` reading (the stub contract `allLevelParamsDefined_spec`). Here the `realCall p` reading,
by the real refinement (lane `decls3`'s `apdEntry_ok`, the core of `apdF_okT`):

* **The walk's needs.** `all_level_params_defined` reads the twin's store only: its `ApdEnv`
  (`ApdEnv.of_state`: from `StateOK`, as `TwinOK.of_check` derives `StoreDen`'s two level fields)
  and the parameters' names read back (`∃ ks, lps.mapM (denoteN …) = some ks`, the caller's); its
  L side writes its memo only (array 151 and `CTL[152‥153]`, shared with the core's `wscopedBFast`
  memo, which `AbsOK`'s `WalkMemos` holds: `apdMR_clear` before, `apdMR_ws` after), so `AbsOK` is
  kept (`apdF_simR`).
* **The twin state.** None of the four walks changes the twin's store, caches or pins (`sp`):
  `hasFvarFast`, `looseBVarsBoundedFast` touch the per-call memos only (`memos_only_of_sp`),
  `allLevelParamsDefined` (`apdEntry_ok`) and `constsResolveFFast` (`constsResolveFFast_keepsSt`)
  leave the state as it was. So the precondition on the twin side (`StateOK`, the names) holds
  for every body, and `StageC` is carried (`StageC.of_sp`).

`sctW_okR` is the walk under `StageR` with `StateOK` and the names; `sctW_okC` its `StageC` form.

`check_struct_proj_table`, `check_block_tables_one` and `check_block_tables` have one model each
(`tblE`, `ctoE`, `ctbE`: `l_model … unified`) and one refinement each for both outcomes (`tbl_ref`,
`cto_ref`, `ctb_ref`: `RefE` under `True`, as every error of class other than `0` is the table's own
reject).
-/


noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind
set_option experimental.vcgen true

open L.Arena

/-! ## The walk's twin-side environment from `StateOK` -/

/-- **`ApdEnv` from the store's well-formedness** (`TwinOK.of_check`'s two level fields). -/
theorem ApdEnv.of_state {a : AState} (hok : ConRon.Bridge.StateOK a) : ApdEnv a := by
  obtain ⟨rk, hw⟩ := hok.wf
  have hLs : LsStoreWF a.store.lss := hw.lss
  have hL : LStoreWF a.store.ls := hLs.ls
  refine ⟨hw.nsWF, fun x u hv => ?_, fun x c us hv => ?_⟩
  · exact denoteL_of_viewW hL (hw.lchildOK x _ hv u (by simp [ENodeView.lchildren])).1
  · have hs := (hw.lschildOK x _ hv us (by simp [ENodeView.lschildren])).1
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨xs, hxs⟩ := denoteLs_of_viewW hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩

/-- `StateOK` reads the store only. -/
theorem stateOK_of_sp {a a' : AState} (h : ConRon.Bridge.StateOK a) (e : sp a' = sp a) :
    ConRon.Bridge.StateOK a' := by
  simp only [sp, Prod.mk.injEq] at e
  exact ⟨by rw [e.1]; exact h.wf⟩

/-! ## `all_level_params_defined`, the real walk -/

/-- **`all_level_params_defined`'s model under `StageR`, `AbsOK` and the twin's `StateOK`**: the
twin state stays as it was, `AbsOK` holds after (the walk's memo is the core's `wscopedBFast`
memo, `apdMR_ws`; the rest is framed). -/
theorem apdF_simR {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (o l e : Word) (he : H e) (lps : List NIdx) (hS : StageR vis fe m a)
    (hA : AbsOK m) (hok : ConRon.Bridge.StateOK a) (hdec : decHL m o.toNat l.toNat = some lps)
    (hks : ∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks) :
    Sim (apdF m [o, l, e]) (allLevelParamsDefined lps (decI e)) a
      (fun r x m' a' => StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r x ∧ AbsOK m' ∧
        sp a' = sp a) := by
  intro r m' h
  obtain ⟨ks, hks⟩ := hks
  obtain ⟨n, hc⟩ := callF_run h
  rcases n with _ | n
  · rw [callW_zero] at hc; cases hc
  obtain ⟨s', hs', -, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (allLevelParamsDefined_spec_raw apdP apdP_prog.eview apdP_prog.lsnode apdP_prog.find
      apdP_prog.put apdP_prog.clear apdP_prog.lmem apdP_prog.lnode apdP_prog.lapd apdP_prog.ls
      apdP_prog.go apdP_prog.entry n ⟨m, Locals.init []⟩ o l e) hc
  subst hs'
  obtain ⟨hAb, hI1, hCr, hIl, hW, hE, hSp, hB, hP⟩ := hA
  obtain ⟨b, hrun, hr, hS', hg, mp, hM⟩ := apdEntry_ok n hS (ApdEnv.of_state hok) o l e _ lps ks hks
    hdec he (apdMR_clear hW) hm
  have hf := apdF_frame h
  refine ⟨b, a, hrun, hS', hg, apd_decW0B hr, ?_, rfl⟩
  obtain ⟨-, ⟨mf, hfl⟩, ⟨ml, hlsb⟩, hLP⟩ := hW
  refine ⟨hAb.frame hf (by decide) (by decide), hI1.frame hf (by decide) (by decide),
    hCr.frame hf (by decide) (by decide), hIl.frame hf (by decide) (by decide),
    ⟨apdMR_ws hM, ⟨mf, ?_⟩, ⟨ml, ?_⟩, hLP.frame hf (by decide) (by decide)⟩,
    by rw [hf.size]; exact hE, by rw [hf.size]; exact hSp, by rw [hf.size]; exact hB,
    by rw [pinW_frame hf (by decide)]; exact hP⟩
  · exact memoRG_frame coreFlSch coreFlSch_wf bmKey _ _ _ (by decide) (by decide) _ _ hf mf hfl
  · exact memoRG_frame coreLsbSch coreLsbSch_wf bmKey _ _ _ (by decide) (by decide) _ _ hf ml hlsb

/-- `apdF_simR` at the program's own call (`realCall p`'s reading). -/
theorem apdCall_simR {p : Prog} (hp : ApdF p) (k : Nat)
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} (o l e : Word) (he : H e) (lps : List NIdx)
    (hS : StageR vis fe m a) (hA : AbsOK m) (hok : ConRon.Bridge.StateOK a)
    (hdec : decHL m o.toNat l.toNat = some lps)
    (hks : ∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks) :
    Sim (realCall p k "all_level_params_defined" [o, l, e] m) (allLevelParamsDefined lps (decI e)) a
      (fun r x m' a' => StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r x ∧ AbsOK m' ∧
        sp a' = sp a) :=
  fun r m' h => apdF_simR o l e he lps hS hA hok hdec hks r m' (apdF_of_callW hp h)

/-! ## The other three walks keep the twin's store -/

/-- `has_fvar_fast` (`hffF_ok`), the twin's store, caches and pins kept. -/
theorem hffF_simR {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (f e : Word) (he : H e) (hS : StageR vis fe m a) :
    Sim (hffF m [f, e]) (hasFvarFast f.toNat (decI e)) a
      (fun r x m' a' => (StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r x) ∧ sp a' = sp a) := by
  intro r m' h
  obtain ⟨x, a', hrun, hK⟩ := hffF_ok dn vis fe f e he m m' a r h hS
  obtain ⟨X, rfl⟩ := memos_only_of_sp (Keeps.bind (keeps_fvarB_sp _ _) fun _ => Keeps.pure _) x a' hrun
  exact ⟨x, _, hrun, hK, rfl⟩

/-- `loose_bvars_bounded_fast` (`lbbF_ok`), the twin's store, caches and pins kept. -/
theorem lbbF_simR {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (f k e : Word) (he : H e) (hS : StageR vis fe m a) :
    Sim (lbbF m [f, k, e]) (looseBVarsBoundedFast f.toNat k.toNat (decI e)) a
      (fun r x m' a' => (StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r x) ∧ sp a' = sp a) := by
  intro r m' h
  obtain ⟨x, a', hrun, hK⟩ := lbbF_ok dn vis fe f k e he m m' a r h hS
  obtain ⟨X, rfl⟩ := memos_only_of_sp (Keeps.bind (keeps_bvarB_sp _ _) fun _ => Keeps.pure _) x a' hrun
  exact ⟨x, _, hrun, hK, rfl⟩

/-- `consts_resolve_ffast` (`constsResolveFFast_keepsSt`), the twin state kept, `AbsOK` after. -/
theorem crfF_simR {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (e : Word) (he : H e) (hS : StageR vis fe m a) (hA : AbsOK m) :
    Sim (crfF m [vis, e]) (constsResolveFFast fe (decI e)) a
      (fun r x m' a' => (StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r x) ∧ AbsOK m' ∧
        sp a' = sp a) := by
  intro r m' h
  obtain ⟨hAb, hI1, hCr, hIl, hWk⟩ := hA
  have hfr := crfF_frame h
  obtain ⟨x, a', hrun, hK, hCr', ha'⟩ := relW_callF (P := crfP)
    (L.Stubs.constsResolveFFast_keepsSt crfP_prog (vis := vis) (fe := fe) e he a).refAM
    m m' a r h ⟨hS, hCr, rfl⟩
  subst ha'
  exact ⟨x, _, hrun, hK, ⟨hAb.frame hfr (by decide) (by decide), hI1.frame hfr (by decide) (by decide),
    hCr', hIl.frame hfr (by decide) (by decide),
    hWk.frame hfr (by decide) (by decide) (by decide) (by decide) (by decide)⟩, rfl⟩

/-! ## `check_struct_proj_table_scoped`, the real reading -/

/-- The parameters' names read back in a store that is the same. -/
theorem names_of_sp {a a' : AState} {lps : List NIdx} (e : sp a' = sp a)
    (h : ∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks) :
    ∃ ks, lps.mapM (denoteN a'.store.lss.ls.ns) = some ks := by
  simp only [sp, Prod.mk.injEq] at e
  rw [e.1]; exact h

/-- **`check_struct_proj_table_scoped`'s model (`realCall p`) refines the twin's
`bodies.toList.allM`** under `StageR`, `AbsOK`, the twin's `StateOK` and the parameters' names
read back; the twin's store, caches and pins are kept. -/
theorem sctW_okR {p : Prog} (hp : ApdF p) {vis : Word}
    {fe : IFEnv} (nP lo ll : Word) (lps : List NIdx) (hnP : nP.toNat + 1 < 2 ^ 64) (n : Nat) :
    ∀ (m : Mem) (a : AState) (bO bL : Word) (bs : List EIdx),
    StageR vis fe m a → ConRon.Bridge.StateOK a →
    (∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks) →
    decHL m lo.toNat ll.toNat = some lps → lo.toNat + ll.toNat ≤ iwTop m →
    decHL m bO.toNat bL.toNat = some bs → bO.toNat + bL.toNat ≤ iwTop m → AbsOK m →
    Sim (sctW (realCall p) n m vis nP lo ll bO bL) (bs.allM (scopeT fe lps nP.toNat)) a
      (fun r b m' a' => StageR vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0 != 0) = b ∧
        (r.headD 0).toNat ≤ 1 ∧ AbsOK m' ∧ sp a' = sp a) := by
  induction n with
  | zero => intro m a bO bL bs _ _ _ _ _ _ _ _; exact Sim.of_none
  | succ n ih =>
  intro m a bO bL bs hS hok hks hlps hlb hbs hbb hA
  by_cases hl : bL = 0
  · rw [sctW_nil (h := hl)]
    have : bs = [] := by
      subst hl; have := decHL_length m hbs; simp at this; exact this
    subst this
    exact Sim.ret ⟨hS, IWGrow.refl _, rfl, by decide, hA, rfl⟩
  rw [sctW_cons (h := hl)]
  obtain ⟨w, bs', rfl, hw, hwl, hbs'⟩ := decHL_cons hbs hl (hS.lt64 hbb)
  rw [hw]
  simp only [List.allM, scopeT, bind_assoc, pure_bind]
  have hcwf : CWF.toNat = coreWalkFuel := CWF_eq
  have h1 := hffF_simR (dn := fun _ => none) (vis := vis) (fe := fe) CWF w hwl hS
  rw [hcwf] at h1
  refine Sim.bindK (K := sctK1 (realCall p) n _ vis nP lo ll w) rfl (fun _ _ => rfl)
    (Sim.withFr (F := AbsOK) h1 fun _ _ e => (show AFr _ _ from AFr.of_frame (hffF_frame e)) hA)
    fun r1 a1 m1 s1 hQ => ?_
  obtain ⟨⟨⟨hS1, hg1, hb1, hl1⟩, he1⟩, hA1⟩ := hQ
  rw [sctK1_some]
  refine Sim.bindK (K := sctK2 _ vis nP w (r1.headD 0)) rfl (fun _ _ => rfl)
    (apdCall_simR hp n lo ll w hwl lps hS1 hA1 (stateOK_of_sp hok he1)
      (by rw [decHL_grow hg1 hlb]; exact hlps) (names_of_sp he1 hks))
    fun r2 a2 m2 s2 hQ => ?_
  obtain ⟨hS2, hg2, ⟨hb2, hl2⟩, hA2, he2⟩ := hQ
  rw [sctK2_some]
  refine Sim.bindK (K := sctK3 _ nP w (r1.headD 0) (r2.headD 0)) rfl (fun _ _ => rfl)
    (crfF_simR w hwl hS2 hA2) fun r3 a3 m3 s3 hQ => ?_
  obtain ⟨⟨hS3, hg3, hb3, hl3⟩, hA3, he3⟩ := hQ
  rw [sctK3_some]
  have h4 := lbbF_simR (dn := fun _ => none) (vis := vis) (fe := fe) CWF (nP + 1) w hwl hS3
  rw [hcwf, sumToNat_succ (by omega)] at h4
  refine Sim.bindK (K := sctK4 _ (r1.headD 0) (r2.headD 0) (r3.headD 0)) rfl (fun _ _ => rfl)
    (Sim.withFr (F := AbsOK) h4 fun _ _ e => (show AFr _ _ from AFr.of_frame (lbbF_frame e)) hA3)
    fun r4 a4 m4 s4 hQ => ?_
  obtain ⟨⟨⟨hS4, hg4, hb4, hl4⟩, he4⟩, hA4⟩ := hQ
  have he14 : sp s4 = sp a := he4.trans (he3.trans (he2.trans he1))
  have hg14 := ((hg1.trans hg2).trans hg3).trans hg4
  obtain ⟨-, e1⟩ := sumB01 hb1 hl1
  obtain ⟨e2, -⟩ := sumB01 hb2 hl2
  obtain ⟨e3, -⟩ := sumB01 hb3 hl3
  obtain ⟨e4, -⟩ := sumB01 hb4 hl4
  by_cases hc : r1.headD 0 = 0 ∧ r2.headD 0 = 1 ∧ r3.headD 0 = 1 ∧ r4.headD 0 = 1
  · rw [sctK4_yes (h := hc)]
    have ht : (!a1 && a2 && a3 && a4) = true := by
      rw [e1.mp hc.1, e2.mp hc.2.1, e3.mp hc.2.2.1, e4.mp hc.2.2.2]; rfl
    simp only [ht]
    have hT := hS.lt64 hbb
    have hbL : bL.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
    have hb1' : (bO + 1).toNat + (bL - 1).toNat ≤ iwTop m := by
      rw [sumToNat_succ (by omega), sumToNat_pred hl]; omega
    refine sumSim_map (K := sctK5) rfl (fun _ _ => rfl)
      (ih m4 s4 (bO + 1) (bL - 1) bs' hS4 (stateOK_of_sp hok he14) (names_of_sp he14 hks)
        (by rw [decHL_grow hg14 hlb]; exact hlps)
        (by have := hg14.iw; omega) (by rw [decHL_grow hg14 hb1']; exact hbs') (by have := hg14.iw; omega) hA4)
      fun r b m' a' hQ => ⟨hQ.1, hg14.trans hQ.2.1, by simpa using hQ.2.2.1, by simpa using hQ.2.2.2.1,
        hQ.2.2.2.2.1, hQ.2.2.2.2.2.trans he14⟩
  · rw [sctK4_no (h := hc)]
    have ht : (!a1 && a2 && a3 && a4) = false := by
      cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> simp_all
    simp only [ht]
    exact Sim.ret ⟨hS4, hg14, rfl, by decide, hA4, he14⟩

/-! ## `check_struct_proj_table`, the real reading -/

/-- `sctW (realCall p)`'s frame. -/
theorem sctW_mfr_real {p : Prog} (hp : ApdF p) : ∀ (n : Nat) (m m' : Mem) (vis nP lo ll bO bL : Word)
    (r : List Word), sctW (realCall p) n m vis nP lo ll bO bL = some (r, m') → MFr [] [] m m' :=
  sctW_mfr fun _ _ _ _ _ h => MFr.of_frame (apdF_frame (apdF_of_callW hp h))
    (fun b hb => .inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb; decide))
    (fun x hx => .inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                          rcases hx with rfl | rfl <;> decide))

/-- Names read back in a store read back in its extension. -/
theorem names_ext {st st' : EStore} (hx : ConRon.Arena.Ext st st') {lps : List NIdx}
    (h : ∃ ks, lps.mapM (denoteN st.lss.ls.ns) = some ks) :
    ∃ ks, lps.mapM (denoteN st'.lss.ls.ns) = some ks := by
  obtain ⟨ks, hks⟩ := h
  refine ⟨ks, ?_⟩
  induction lps generalizing ks with
  | nil => simpa using hks
  | cons k lps ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hks ⊢
    obtain ⟨x, hx1, xs, hxs, rfl⟩ := hks
    exact ⟨x, hx.lss.ls.ns k x hx1, xs, ih xs hxs, rfl⟩

/-- **The model of `check_struct_proj_table`, both outcomes**: its callees (outside the verdict
closure) lifted, `check_struct_proj_table_scoped` reading the real `all_level_params_defined`. -/
l_model tblE_spec (p : Prog) (hP : TblProg p)
  fns [hP.htbl ↦ tblE]
  specs [spbW_spec p hP.ha hP.hc hP.hsc hP.hv hP.hd hP.hpf hP.hpp hP.hib hP.hjf hP.hjp hP.hji hP.hmp hP.hap
      hP.hpg hP.hgo hP.hps hP.hpj hP.hspb hP.hi1 hP.hipal n,
    sctW_spec p hP.hbb hP.hhf hP.hcr hP.hsct (realCall p) (realCall_spec p) n,
    callW_spec p n "env_find", callW_spec p n "find_table"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


/-- What `check_struct_proj_table` gives (from `m`, `a`): the stage at `vis` of `fe` (nothing is
pushed), the growth, the frame (no memo touched), `AbsOK`, the twin's run a `PStep`. -/
structure TblPost (vis : Word) (fe : IFEnv) (m : Mem) (a : AState) (m' : Mem) (a' : AState) : Prop where
  stage : StageR vis fe m' a'
  grow : IWGrow m m'
  frame : MFr [] [] m m'
  abs : AbsOK m'
  step : ConRon.Bridge.Inductives.PStep a a'

/-- **`check_struct_proj_table` refines `checkStructProjTable`, both outcomes** (the scoping
through the real walks). -/
theorem tbl_ref {vis : Word} {fe : IFEnv} (p : Prog) (hP : TblProg p) (hp : ApdF p)
    (n : Nat) (m : Mem) (a : AState) (T lo ll nP nF cvCaw : Word) (lps : List NIdx)
    (cvCa : IConstantVal) (hS : StageR vis fe m a) (hT : H T) (hnP : nP.toNat + 1 < 2 ^ 64)
    (hlps : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hcv : DecB (fun m => decCVp m cvCaw.toNat) m cvCa) (hA : AbsOK m)
    (hok : ConRon.Bridge.StateOK a) (hks : ∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks)
    {TP : ConLeche.Name} (hTP : denoteN a.store.ns (decI T) = some TP)
    {ctyP : ConLeche.Expr} (hcty : denoteE a.store cvCa.type = some ctyP) :
    RefE True (tblE p (n + 2) m T lo ll nP nF cvCaw vis)
      (checkStructProjTable (decI T) lps nP.toNat nF.toNat cvCa fe) a
      (fun v _ a' => TblPost vis fe m a v.2 a') := by
  obtain ⟨w, hw, hwl, hwd⟩ := sumTypeWord (DecB.get (OMono.decCVp _) hcv)
  rw [tblE.arm1, show rdW (m.arr64 (tierA EREC ((cvCaw + 3) >>> 40))) (cvCaw + 3 &&& 1099511627775) = w
    from hw]
  rw [← hwd] at hcty
  unfold checkStructProjTable
  rw [← hwd]
  -- `struct_proj_bodies`
  refine RefE.onlySim (fun _ => tblE.k_struct_proj_bodies.none ..) (fun _ _ h => h) fun rb m1 h1 => ?_
  obtain ⟨x, a1, h1', hS1, hg1, hdec1, hA1⟩ := spbW_ok (fun _ => none) vis fe (n + 1) m m1 a T nP nF w rb h1
    hS hwl (by omega) nF.toNat_lt hA
  obtain ⟨ps1, -⟩ := ConRon.Bridge.Inductives.structProjBodies_spec (decI T) TP nP.toNat nF.toNat
    (decI w) ctyP a a1 x hok ⟨hTP, hcty⟩ h1'
  have hf1 := spbW_mfr h1
  refine RefE.bind_right h1' ?_
  by_cases h10 : rb.headD 0 = 0
  · rw [tblE.k_struct_proj_bodies.abort1 p (n + 1) T lo ll nP nF vis rb _ h10]
    exact RefE.of_cls0 rfl
  rw [tblE.k_struct_proj_bodies.arm1 p (n + 1) T lo ll nP nF vis rb _ h10]
  cases x with
  | none => exact absurd hdec1 h10
  | some bodies =>
  obtain ⟨-, hbd, hbb⟩ := hdec1
  simp only [unwrapOr, pure_bind]
  have hlps1 : decHL m1 lo.toNat ll.toNat = some lps := by rw [decHL_grow hg1 hlb]; exact hlps
  have hlb1 : lo.toNat + ll.toNat ≤ iwTop m1 := by have := hg1.iw; omega
  -- the scoping
  refine RefE.onlySim (fun _ => tblE.k_check_struct_proj_table_scoped.none ..) (fun _ _ h => h)
    fun rs' m2 h2 => ?_
  obtain ⟨b, a2, hrun2, hS2, hg2, hsok, hsl, hA2, he2⟩ := sctW_okR hp nP lo ll lps hnP (n + 1) m1 a1 _ _
    bodies.toList hS1 ps1.ok (names_ext ps1.ext hks) hlps1 hlb1 hbd hbb hA1 rs' m2 h2
  have hf2 := sctW_mfr_real hp _ _ _ _ _ _ _ _ _ _ h2
  have ps2 : ConRon.Bridge.Inductives.PStep a a2 := by
    have e' := he2
    simp only [sp, Prod.mk.injEq] at e'
    exact ps1.trans (ConRon.Bridge.Inductives.PStep.of_caches (stateOK_of_sp ps1.ok he2)
      (by rw [e'.1]; exact ConRon.Arena.Ext.refl _) e'.2.1 e'.2.2)
  by_cases hlen0 : rb.tail.tail.headD 0 ≠ nF
  · rw [tblE.k_check_struct_proj_table_scoped.abort1 p (n + 1) T nF vis _ rs' _ hlen0]
    exact RefE.of_cls0 rfl
  have hlen : rb.tail.tail.headD 0 = nF := Decidable.of_not_not hlen0
  by_cases h10' : rs'.headD 0 ≠ 1
  · rw [tblE.k_check_struct_proj_table_scoped.abort2 p (n + 1) T nF vis _ rs' _ hlen h10']
    exact RefE.of_cls0 rfl
  have h1r : rs'.headD 0 = 1 := Decidable.of_not_not h10'
  rw [tblE.k_check_struct_proj_table_scoped.arm1 p (n + 1) T nF vis _ rs' _ hlen h1r]
  refine RefE.bind_right hrun2 ?_
  have hsz : bodies.size = nF.toNat := by
    rw [← Array.length_toList, decHL_length m1 hbd, hlen]
  have hsok' : b = true := (sumB01 hsok hsl).1.mp h1r
  subst hsok'
  simp only [hsz, and_self, ite_true]
  -- `env_find`: the structure is stored
  refine RefE.onlySim (fun _ => tblE.k_env_find.none ..) (fun _ _ h => h) fun rf m3 hf => ?_
  by_cases hf0 : rf.headD 0 = 0
  · rw [tblE.k_env_find.abort1 p (n + 1) T vis rf m3 hf0]
    exact RefE.of_cls0 rfl
  rw [tblE.k_env_find.arm1 p (n + 1) T vis rf m3 hf0]
  obtain ⟨s3, hs3, hm3, -, hrf⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (envFind_spec p hP.hft.rowGet hP.hft.baseGet hP.hft.find (n + 1) _ vis T) hf
  obtain rfl : m3 = m2 := hs3.symm.trans hm3
  subst hrf
  obtain ⟨hfind0, ci0, hci0⟩ := findRes_hit hS2.check.env hT hf0
  have hhit : (fe.find? (decI T)).isSome := by rw [hfind0, hci0]; rfl
  simp only [hhit, ite_true]
  -- `find_table`: the table is not taken
  refine RefE.onlySim (fun _ => tblE.k_find_table.none ..) (fun _ _ h => h) fun rt m4 hft => ?_
  obtain ⟨s4, hs4, hm4, -, hfind, hsome4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (findTable_refines p hP.hft (n + 1) _ vis T hS2.check.env hT) hft
  obtain rfl : m4 = m3 := hs4.symm.trans hm4
  by_cases ht0 : rt.headD 0 ≠ 0
  · rw [tblE.k_find_table.abort1 p rt m4 ht0]
    have hsome : ¬ (fe.findTable? (decI T)).isNone = true := by
      rw [hfind]
      obtain ⟨tb, htb⟩ := hsome4 ht0
      dsimp only at htb
      simp only [tblFound, ht0, ↓reduceIte, htb, Option.isNone_some]
      decide
    exact fun _ => ErrClaim.ite_neg hsome (ErrClaim.fail _ _ (by decide))
  have ht0' : rt.headD 0 = 0 := Decidable.of_not_not ht0
  rw [tblE.k_find_table.arm1 p rt m4 ht0']
  have hnone : fe.findTable? (decI T) = none := by rw [hfind, ht0']; simp [tblFound]
  simp only [hnone, Option.isNone_none, ite_true]
  exact RefE.ret rfl ⟨hS2, hg1.trans hg2, hf1.trans hf2, hA2, ps2⟩

/-- **`check_struct_proj_table` refines `checkStructProjTable` under `StageC`** (`tbl_ref`'s ok
half): from `StageC` at `vis` of `fe`, the decodings and the walk memos, and the twin's readings of
the structure's name, the level parameters and the constructor, a returning run keeps the stage
and the twin's run is a `PStep`. -/
@[refines ConRon.Arena.checkStructProjTable]
theorem checkStructProjTable_refinesC (p : Prog) (hP : TblProg p) (hp : ApdF p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) {env : ConLeche.Env}
    (T lo ll nP nF cvCaw vis : Word)
    (lps : List NIdx) (cvCa : IConstantVal) (hC : StageC dn vis fe env s₀.mem a₀)
    (hT : H T) (hnP : nP.toNat + 1 < 2 ^ 64)
    (hlps : decHL s₀.mem lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop s₀.mem)
    (hcv : DecB (fun m => decCVp m cvCaw.toNat) s₀.mem cvCa) (hA : AbsOK s₀.mem)
    {TP : ConLeche.Name} (hTP : denoteN a₀.store.ns (decI T) = some TP)
    {lpsP : List ConLeche.Name} (hlpsP : Frontend.denoteNList a₀.store.ns lps = some lpsP)
    {cvCaP : ConLeche.ConstantVal} (hcvP : Frontend.denoteCV a₀.store cvCa = some cvCaP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "check_struct_proj_table"
      [T, lo, ll, nP, nF, cvCaw, vis]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (checkStructProjTable (decI T) lps nP.toNat nF.toNat cvCa fe) a₀ ∧
      StageR vis fe s'.mem (AM.st (checkStructProjTable (decI T) lps nP.toNat nF.toNat cvCa fe) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem ∧
      ConRon.Bridge.Inductives.PStep a₀ (AM.st (checkStructProjTable (decI T) lps nP.toNat nF.toNat
        cvCa fe) a₀); ⊤⦄ :=
  triple_post (RefE.triple (tblE_spec p hP (n + 2) s₀ T lo ll nP nF cvCaw vis)
      (tbl_ref p hP hp n _ a₀ T lo ll nP nF cvCaw lps cvCa hC.stage hT hnP hlps hlb hcv hA
        hC.check.state ⟨lpsP, denoteNList_mapM hlpsP⟩ hTP
        (ConRon.Bridge.denoteCV_type hcvP))) fun _ _ ⟨hl, _, _, hrun, hR⟩ => by
    obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
    exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, hR.abs, by rw [hst]; exact hR.step⟩

/-! ## `check_block_tables`, one model and one refinement each -/



/-- **The model of `check_block_tables`, both outcomes**: `block_shape_lps` lifted, each
structure-like member's table by `check_struct_proj_table`'s unified model. -/
l_model ctbE_spec (p : Prog) (hP : TabsProg p)
  fns [hP.tabs ↦ ctbE]
  specs [blockShapeLps_spec p hP.tbl.ha hP.erCopy hP.erToIw hP.lps n, tblE_spec p hP.tbl n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]



theorem TblPost.trans {vis : Word} {fe : IFEnv} {m m1 m2 : Mem} {a a1 a2 : AState}
    (h1 : TblPost vis fe m a m1 a1) (h2 : TblPost vis fe m1 a1 m2 a2) : TblPost vis fe m a m2 a2 :=
  ⟨h2.stage, h1.grow.trans h2.grow, h1.frame.trans h2.frame, h2.abs, h1.step.trans h2.step⟩

/-- `tbl_ref` at every fuel (below `2` the model is an error of class `0`). -/
theorem tblRef_any {vis : Word} {fe : IFEnv} (p : Prog) (hP : TblProg p) (hp : ApdF p)
    (n : Nat) (m : Mem) (a : AState) (T lo ll nP nF cvCaw : Word) (lps : List NIdx)
    (cvCa : IConstantVal) (hS : StageR vis fe m a) (hT : H T) (hnP : nP.toNat + 1 < 2 ^ 64)
    (hlps : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hcv : DecB (fun m => decCVp m cvCaw.toNat) m cvCa) (hA : AbsOK m)
    (hok : ConRon.Bridge.StateOK a) (hks : ∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks)
    {TP : ConLeche.Name} (hTP : denoteN a.store.ns (decI T) = some TP)
    {ctyP : ConLeche.Expr} (hcty : denoteE a.store cvCa.type = some ctyP) :
    RefE True (tblE p n m T lo ll nP nF cvCaw vis)
      (checkStructProjTable (decI T) lps nP.toNat nF.toNat cvCa fe) a
      (fun v _ a' => TblPost vis fe m a v.2 a') := by
  match n with
  | 0 => rw [tblE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | 1 =>
    rw [tblE.arm1]
    exact RefE.onlySim (fun _ => tblE.k_struct_proj_bodies.none ..) (Q := fun _ _ => False)
      (fun _ _ h => by cases h) fun _ _ h => h.elim
  | k + 2 => exact tbl_ref p hP hp k m a T lo ll nP nF cvCaw lps cvCa hS hT hnP hlps hlb hcv hA hok hks hTP hcty

/-- The level parameters' names of a shape that denotes. -/
theorem lps_names_of_dShape {st : EStore} {bs : BlockShape} {pP : ConLeche.BlockShape}
    (h : ConRon.Bridge.Inductives.dShape st bs = some pP) :
    ∃ ks, bs.lps.mapM (denoteN st.lss.ls.ns) = some ks := by
  simp only [ConRon.Bridge.Inductives.dShape, bind, Option.bind_eq_some_iff] at h
  obtain ⟨ms, hms, -⟩ := h
  unfold BlockShape.lps
  match hm : bs.members, hms with
  | [], _ => exact ⟨[], rfl⟩
  | m0 :: _, hms =>
    obtain ⟨y, -, -, hy, -⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hms
    simp only [ConRon.Bridge.Inductives.dMember, bind, Option.bind_eq_some_iff] at hy
    obtain ⟨c, hc, -⟩ := hy
    exact denoteCV_lps hc

/-- A structure-like member's readings: the former's name and the constructor's type denote. -/
theorem member_facts {st : EStore} {cvT dcl : IConstantVal} {nI : Nat} {cA : IConstantVal} {nF : Nat}
    {y : ConLeche.MemberShape}
    (h : ConRon.Bridge.Inductives.dMember st ⟨cvT, dcl, nI, [(cA, nF)]⟩ = some y) :
    (∃ TP, denoteN st.ns cvT.name = some TP) ∧ ∃ ctyP, denoteE st cA.type = some ctyP := by
  simp only [ConRon.Bridge.Inductives.dMember, bind, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, -, -, cs, hcs, -⟩ := h
  obtain ⟨y1, -, -, hy1, -⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcs
  simp only [ConRon.Bridge.Inductives.dCtor, Option.map_eq_some_iff] at hy1
  obtain ⟨c', hc', -⟩ := hy1
  exact ⟨⟨_, ConRon.Bridge.denoteCV_name hc⟩, ⟨_, ConRon.Bridge.denoteCV_type hc'⟩⟩

/-- **`check_block_tables` refines `checkBlockTables`, both outcomes** (each structure-like member's
table by `tbl_ref`), from the twin's `StateOK`, the shape's level parameters' names and the members'
readings (each table's check a `PStep`, so they hold at the next); the stage kept, the twin's run a
`PStep`. -/
theorem ctb_ref {p : Prog} (hP : TabsProg p) (hp : ApdF p) (pp vis : Word) (fe : IFEnv) (bs : BlockShape)
    (hnP : bs.nP + 1 < 2 ^ 64) (n : Nat) :
    ∀ (m : Mem) (a : AState) (mo ml : Word) (mss : List MemberShape),
    StageR vis fe m a → DecB (fun m => decBS m pp.toNat) m bs → PSlR decMS mss mo ml m → AbsOK m →
    ConRon.Bridge.StateOK a → (∃ ks, bs.lps.mapM (denoteN a.store.lss.ls.ns) = some ks) →
    (∃ msP, mss.mapM (ConRon.Bridge.Inductives.dMember a.store) = some msP) →
    RefE True (ctbE p n m pp vis mo ml) (ConRon.Arena.checkBlockTables bs fe mss) a
      (fun v _ a' => TblPost vis fe m a v.2 a') := by
  induction n with
  | zero => intros; rw [ctbE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a mo ml mss hS hq hmss hA hok hks ⟨msP, hmsP⟩
  by_cases hml : ml = 0
  · rw [ctbE.arm1 p n m pp vis mo ml hml]
    have : mss = [] := by
      subst hml
      have := decPL_length _ (hmss.1.get (OMono.decPL (fun q => decMS_mono q) _ _)); simpa using this
    subst this
    exact RefE.ret rfl ⟨hS, IWGrow.refl m, MFr.refl _ _ m, hA, ConRon.Bridge.Inductives.PStep.refl hok⟩
  have hsz := hS.iw.iwSize
  obtain ⟨x, ys, rfl, hx, hys⟩ := hmss.uncons hml hsz
  obtain ⟨y0, ys0, -, hy0, hys0⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmsP
  generalize hmsp : rdW (m.arr64 IW) mo = msp at hx
  have hx' : decMS (truncM m) msp.toNat = some x := hx
  simp only [decMS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hx'
  obtain ⟨cvp, hcvp, cvT, hcvT, dp, -, dcl, -, nI, hnI, cs, hcs, hxe⟩ := hx'
  subst hxe
  obtain ⟨hlt0, hcvpm⟩ := rec2IwN_trunc (i := msp.toNat + 0) (by simpa using hcvp)
  obtain ⟨e0, t0⟩ := rec2RdN (w := msp) (k := 0) hcvpm hsz
  obtain ⟨-, hnIm⟩ := rec2IwN_trunc hnI
  obtain ⟨e1, t1⟩ := rec2RdN (w := msp) (k := 1) hnIm hsz
  obtain ⟨co, cl, hco, hcl, hcsd⟩ := decAt_some hcs
  obtain ⟨-, hcom⟩ := rec2IwN_trunc hco
  obtain ⟨-, hclm⟩ := rec2IwN_trunc hcl
  obtain ⟨e2, t2⟩ := rec2RdN (w := msp) (k := 2) hcom hsz
  obtain ⟨e3, t3⟩ := rec2RdN (w := msp) (k := 3) (by simpa [Nat.add_assoc] using hclm) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, show UInt64.ofNat 1 = (1 : Word) from rfl,
    show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl,
    UInt64.add_zero] at e0 e1 e2 e3
  have hlen : cs.length = cl := decPL_length _ hcsd
  have hmn : (mo + 1).toNat + (ml - 1).toNat ≤ iwTop m := hys.2
  by_cases hsc : cl = 1 ∧ nI = 0
  · obtain ⟨rfl, rfl⟩ := hsc
    obtain ⟨cp, c, cs', rfl, hcp, hc, hcs'⟩ := decPL_cons (l := 0) hcsd
    obtain rfl : cs' = [] := by have := decPL_length _ hcs'; simpa using this
    simp only [decCN, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
    obtain ⟨cap, hcap, cA, hcA, nF, hnF, hce⟩ := hc
    subst hce
    obtain ⟨-, hcpm⟩ := rec2IwN_trunc (i := (UInt64.ofNat co : Word).toNat + 0) (by rw [t2]; simpa using hcp)
    obtain ⟨e4, t4⟩ := rec2RdN (w := UInt64.ofNat co) (k := 0) hcpm hsz
    simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at e4
    rw [ctbE.arm2 p n m pp vis mo ml hml (by rw [hmsp, e3]; rfl) (by rw [hmsp, e1]; rfl), hmsp, e2, e4]
    obtain ⟨hTP, hcty⟩ := member_facts hy0
    simp only [ConRon.Arena.checkBlockTables, MemberShape.structCtor?, beq_self_eq_true, ↓reduceIte]
    refine RefE.onlySim (fun _ => ctbE.k_block_shape_lps.none ..) (Q := fun r m1 => lpsW n m pp = some (r, m1))
      (fun _ _ h => h) fun r m1 h1 => ?_
    rw [ctbE.k_block_shape_lps.arm1]
    obtain ⟨hS1, hg1, hl1, hlb1⟩ := lpsW_ok' h1 hS hq
    have hsz1 := hS1.iw.iwSize
    have iwN1 : ∀ i, i < iwTop m → iwN m1 i = iwN m i := fun i hi => by
      simp only [iwN, nat?, iwA, aread_apply]; rw [hg1.iwGet _ hi]
    -- the reads at `m1`
    have r0 : rdW (m1.arr64 IW) msp = UInt64.ofNat cvp := by
      have := (rec2RdN (m := m1) (w := msp) (k := 0) (by rw [iwN1 _ hlt0]; exact hcvpm) hsz1).1
      simpa using this
    have hqt : decBS (truncM m) pp.toNat = some bs := hq
    obtain ⟨-, -, hnPd, -, -, -, -⟩ := decBS_some hqt
    obtain ⟨hlt4, hnPm⟩ := rec2IwN_trunc hnPd
    obtain ⟨r4, tnP⟩ := rec2RdN (m := m1) (w := pp) (k := 4) (by rw [iwN1 _ hlt4]; exact hnPm) hsz1
    obtain ⟨hlt5, hcapm⟩ := rec2IwN_trunc (i := (UInt64.ofNat cp : Word).toNat + 0) (by rw [t4]; simpa using hcap)
    obtain ⟨r6, tcap⟩ := rec2RdN (m := m1) (w := UInt64.ofNat cp) (k := 0) (by rw [iwN1 _ hlt5]; exact hcapm) hsz1
    obtain ⟨hlt6, hnFm⟩ := rec2IwN_trunc (i := (UInt64.ofNat cp : Word).toNat + 1) (by rw [t4]; exact hnF)
    obtain ⟨r5, tnF⟩ := rec2RdN (m := m1) (w := UInt64.ofNat cp) (k := 1) (by rw [iwN1 _ hlt6]; exact hnFm) hsz1
    simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, show UInt64.ofNat 1 = (1 : Word) from rfl,
      show UInt64.ofNat 4 = (4 : Word) from rfl, UInt64.add_zero] at r4 r5 r6
    rw [r0, r4, r5, r6]
    -- the former's name word
    have hcv1 : decCV (erecP m1) (UInt64.ofNat cvp : Word).toNat = some cvT := by
      rw [t0]; exact (IWGrow.ext hg1).decCV (decCVp_truncM hcvT)
    have hnm := hcv1
    simp only [decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hnm
    obtain ⟨nm, hnmd, _, -, _, -, hcve⟩ := hnm
    obtain ⟨wN, hwN, hwNH, hwNd⟩ := hd?_some hnmd
    have hwN' : erRd m1 (UInt64.ofNat cvp) = wN := (erRd_of_erecP hwN).1
    rw [show rdW (m1.arr64 (tierA EREC (UInt64.ofNat cvp >>> 40))) (UInt64.ofNat cvp &&& 1099511627775) = wN
      from hwN']
    have hnmE : decI wN = cvT.name := by rw [← hwNd, ← hcve]
    have hcvA : DecB (fun m => decCVp m (UInt64.ofNat cap : Word).toNat) m1 cA := by
      have : DecB (fun m => decCVp m (UInt64.ofNat cap : Word).toNat) m cA := by
        show decCVp (truncM m) _ = some cA; rw [tcap]; exact hcA
      exact this.grow (OMono.decCVp _) hg1
    have hR := tblRef_any (fe := fe) p hP.tbl hp n m1 a wN (r.headD 0) (r.tail.headD 0) (UInt64.ofNat bs.nP)
      (UInt64.ofNat nF) (UInt64.ofNat cap) bs.lps cA hS1 hwNH (by rw [tnP]; exact hnP) hl1 hlb1 hcvA
      (lpsW_afr h1 hA) hok hks (by rw [hnmE]; exact hTP.choose_spec) hcty.choose_spec
    rw [tnP, tnF, hnmE] at hR
    refine RefE.bindE (fun _ => ctbE.k_check_struct_proj_table.none ..) id hR fun v y a1 _ hQ => ?_
    obtain ⟨u, m2⟩ := v
    rw [ctbE.k_check_struct_proj_table.arm1, ctbE.j1.arm1]
    have hP1 : TblPost vis fe m a m1 a :=
      ⟨hS1, hg1, lpsW_mfr h1, lpsW_afr h1 hA, ConRon.Bridge.Inductives.PStep.refl hok⟩
    have hP2 := hP1.trans hQ
    exact RefE.tail_eq (f := fun v => (0, v.2)) (fun e => ctbE.k_check_block_tables.none p e)
      (fun v => ctbE.k_check_block_tables.arm1 p v.1 v.2) id rfl (fun v y a' hR => hP2.trans hR)
      (ih m2 a1 (mo + 1) (ml - 1) ys hQ.stage (hq.grow (decBS_mono _) hP2.grow)
        (hys.grow (fun q => decMS_mono q) hP2.grow) hQ.abs hQ.step.ok (names_ext hQ.step.ext hks)
        ⟨_, ConRon.Bridge.Inductives.DExt.list ConRon.Bridge.Inductives.dMember_ext hQ.step.ext _ _ hys0⟩)
  · have hnone : MemberShape.structCtor? ⟨cvT, dcl, nI, cs⟩ = none := by
      unfold MemberShape.structCtor?
      match cs, hlen with
      | [], _ => rfl
      | [_], h =>
        have : nI ≠ 0 := fun e => hsc ⟨h.symm, e⟩
        simp [this]
      | _ :: _ :: _, _ => rfl
    have hj : ctbE p (n + 1) m pp vis mo ml = ctbE.j1 p n pp vis mo ml m := by
      by_cases h3 : cl = 1
      · exact ctbE.arm3 p n m pp vis mo ml hml (by rw [hmsp, e3, h3]; rfl)
          (by rw [hmsp, e1]; intro e; apply hsc ⟨h3, by rw [← t1, e]; rfl⟩)
      · exact ctbE.arm4 p n m pp vis mo ml hml (by rw [hmsp, e3]; intro e; apply h3; rw [← t3, e]; rfl)
    rw [hj, ctbE.j1.arm1]
    simp only [ConRon.Arena.checkBlockTables, hnone]
    exact RefE.tail_eq (f := fun v => (0, v.2)) (fun e => ctbE.k_check_block_tables.none p e)
      (fun v => ctbE.k_check_block_tables.arm1 p v.1 v.2) id rfl (fun v y a' hR => hR)
      (ih m a (mo + 1) (ml - 1) ys hS hq hys hA hok hks ⟨_, hys0⟩)

end L.Ind
