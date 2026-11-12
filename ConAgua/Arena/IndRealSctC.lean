module

import ConRon.Bridge.Inductives.BlockInstall
import ConRon.Bridge.Inductives.StructParts
import ConAgua.Arena.IndDeclConstsTable
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.IndSumSpec.CheckSumCtor
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl
import ConAgua.Arena.IndInstallSpec.NestCtx
public import ConRon.Arena.Inductives.BlockTail
import ConAgua.Arena.IndInstallSpec.TabSimSpg
public import ConAgua.Arena.IndRealApdT
import ConRon.Bridge.Inductives.BlockTail
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import all Init.Data.List.Control
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndRealMemoCr
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
public import ConAgua.Arena.IndSumSpec.StructProjBodies
import all ConAgua.Arena.Env
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.IndSum
public import ConAgua.Arena.IndInstallSpec.TabsProg
public import ConAgua.Arena.TwinStep
public import ConAgua.Arena.IndPartsSpec.MemberNames
public import ConRon.Bridge.Inductives.Run
import ConAgua.L.WordOff
import ConAgua.Arena.DeclCanonLvl
import ConAgua.Arena.IndInstallSpec.InstallRec2Tele

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
  obtain ⟨hAb, hI1, hCr, hIl, ⟨hW, hE, hSp, hB, hP⟩, hHb⟩ := hA
  obtain ⟨b, hrun, hr, hS', hg, mp, hM⟩ := apdEntry_ok n hS (ApdEnv.of_state hok) o l e _ lps ks hks
    hdec he (apdMR_clear hW) hm
  have hf := apdF_frame h
  refine ⟨b, a, hrun, hS', hg, L.Ind.decW0B_of hr, ?_, rfl⟩
  obtain ⟨-, ⟨mf, hfl⟩, ⟨ml, hlsb⟩, hLP⟩ := hW
  refine ⟨hAb.frame hf (by decide) (by decide), hI1.frame hf (by decide) (by decide),
    hCr.frame hf (by decide) (by decide), hIl.frame hf (by decide) (by decide),
    ⟨⟨apdMR_ws hM, ⟨mf, ?_⟩, ⟨ml, ?_⟩, hLP.frame hf (by decide) (by decide)⟩,
    by rw [hf.size]; exact hE, by rw [hf.size]; exact hSp, by rw [hf.size]; exact hB,
    by rw [pinW_frame hf (by decide)]; exact hP⟩, hbOK_frame hHb hf (by decide) (by decide)⟩
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
  obtain ⟨hAb, hI1, hCr, hIl, hWk, hHb⟩ := hA
  have hfr := crfF_frame h
  obtain ⟨x, a', hrun, hK, hCr', ha'⟩ := relW_callF (P := crfP)
    (L.Stubs.constsResolveFFast_keepsSt crfP_prog (vis := vis) (fe := fe) e he a).refAM
    m m' a r h ⟨hS, hCr, rfl⟩
  subst ha'
  exact ⟨x, _, hrun, hK, ⟨hAb.frame hfr (by decide) (by decide), hI1.frame hfr (by decide) (by decide),
    hCr', hIl.frame hfr (by decide) (by decide),
    hWk.frame hfr (by decide) (by decide) (by decide) (by decide) (by decide),
    hbOK_frame hHb hfr (by decide) (by decide)⟩, rfl⟩

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
  | zero => intro m a bO bL bs _ _ _ _ _ _ _ _; rw [sctW.eq_1]; exact Sim.of_none
  | succ n ih =>
  intro m a bO bL bs hS hok hks hlps hlb hbs hbb hA
  by_cases hl : bL = 0
  · rw [sctW.arm1 (hc1 := hl)]
    have : bs = [] := by
      subst hl; have := decHL_length m hbs; simp at this; exact this
    subst this
    exact Sim.ret ⟨hS, IWGrow.refl _, rfl, by decide, hA, rfl⟩
  rw [sctW.arm2 (hc1 := hl)]
  obtain ⟨w, bs', rfl, hw, hwl, hbs'⟩ := decHL_cons hbs hl (hS.lt64 hbb)
  rw [hw]
  simp only [List.allM, scopeT, bind_assoc, pure_bind]
  have hcwf : CWF.toNat = coreWalkFuel := CWF_eq
  have h1 := hffF_simR (dn := fun _ => none) (vis := vis) (fe := fe) CWF w hwl hS
  rw [hcwf] at h1
  refine Sim.bindK (K := sctW.k_has_fvar_fast (realCall p) n vis nP lo ll bO bL w)
    (sctW.k_has_fvar_fast.none ..) (fun _ _ => rfl)
    (Sim.withFr (F := AbsOK) h1 fun _ _ e => (show AFr _ _ from AFr.of_frame (hffF_frame e)) hA)
    fun r1 a1 m1 s1 hQ => ?_
  obtain ⟨⟨⟨hS1, hg1, hb1, hl1⟩, he1⟩, hA1⟩ := hQ
  rw [sctW.k_has_fvar_fast.arm1]
  refine Sim.bindK (K := sctW.k_all_level_params_defined (realCall p) n vis nP lo ll bO bL w (r1.headD 0))
    (sctW.k_all_level_params_defined.none ..) (fun _ _ => rfl)
    (apdCall_simR hp n lo ll w hwl lps hS1 hA1 (stateOK_of_sp hok he1)
      (by rw [decHL_grow hg1 hlb]; exact hlps) (names_of_sp he1 hks))
    fun r2 a2 m2 s2 hQ => ?_
  obtain ⟨hS2, hg2, ⟨hb2, hl2⟩, hA2, he2⟩ := hQ
  rw [sctW.k_all_level_params_defined.arm1]
  refine Sim.bindK (K := sctW.k_consts_resolve_ffast (realCall p) n vis nP lo ll bO bL w (r1.headD 0)
      (r2.headD 0))
    (sctW.k_consts_resolve_ffast.none ..) (fun _ _ => rfl)
    (crfF_simR w hwl hS2 hA2) fun r3 a3 m3 s3 hQ => ?_
  obtain ⟨⟨hS3, hg3, hb3, hl3⟩, hA3, he3⟩ := hQ
  rw [sctW.k_consts_resolve_ffast.arm1]
  have h4 := lbbF_simR (dn := fun _ => none) (vis := vis) (fe := fe) CWF (nP + 1) w hwl hS3
  rw [hcwf, sumToNat_succ (by omega)] at h4
  refine Sim.bindK (K := sctW.k_loose_bvars_bounded_fast (realCall p) n vis nP lo ll bO bL (r1.headD 0)
      (r2.headD 0) (r3.headD 0))
    (sctW.k_loose_bvars_bounded_fast.none ..) (fun _ _ => rfl)
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
  · rw [sctW.k_loose_bvars_bounded_fast.arm1 (hc1 := hc)]
    have ht : (!a1 && a2 && a3 && a4) = true := by
      rw [e1.mp hc.1, e2.mp hc.2.1, e3.mp hc.2.2.1, e4.mp hc.2.2.2]; rfl
    simp only [ht]
    have hT := hS.lt64 hbb
    have hbL : bL.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
    have hb1' : (bO + 1).toNat + (bL - 1).toNat ≤ iwTop m := by
      rw [sumToNat_succ (by omega), L.toNat_sub_one_of_ne hl]; omega
    refine L.Arena.Sim.post (K := sctW.k_check_struct_proj_table_scoped (realCall p))
      (sctW.k_check_struct_proj_table_scoped.none _) (fun _ _ => rfl)
      (ih m4 s4 (bO + 1) (bL - 1) bs' hS4 (stateOK_of_sp hok he14) (names_of_sp he14 hks)
        (by rw [decHL_grow hg14 hlb]; exact hlps)
        (by have := hg14.iw; omega) (by rw [decHL_grow hg14 hb1']; exact hbs') (by have := hg14.iw; omega) hA4)
      fun r b m' a' hQ => ⟨hQ.1, hg14.trans hQ.2.1, by simpa using hQ.2.2.1, by simpa using hQ.2.2.2.1,
        hQ.2.2.2.2.1, hQ.2.2.2.2.2.trans he14⟩
  · rw [sctW.k_loose_bvars_bounded_fast.arm2 (hc1 := hc)]
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
  specs [erToIw_specW p hP.ha hP.hecp hP.heti n,
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

/-- A decoded handle list at words `q + j`, `q + j + 1` (`InferProj.lean`'s `hlist_words`). -/
private theorem sct_hlist_words {k : IdxKind} {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd)
    {q : Word} {j : Nat} {l : List (Idx k)}
    (h : hlist? R (q.toNat + j) = some l) :
    hslice? R (rd (q + UInt64.ofNat j)).toNat (rd (q + UInt64.ofNat (j + 1))).toNat = some l := by
  simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨o, ⟨wo, hwo, rfl⟩, c, ⟨wc, hwc, rfl⟩, hs⟩ := h
  have hj := hR.lt _ _ hwc
  have r1 : rd (q + UInt64.ofNat j) = wo := hR.offN hwo (by omega)
  have r2 : rd (q + UInt64.ofNat (j + 1)) = wc :=
    hR.offN (by simpa [Nat.add_assoc] using hwc) (by omega)
  rw [r1, r2]; exact hs

/-- **The words of a decoded table record** `check_struct_proj_table` reads. -/
theorem sct_decTbl {m : Mem} {t : Word} {tb : IProjTable} (h : decTbl (erecP m) t.toNat = some tb) :
    HW (erRd m (t + 2)) ∧ tb.structName = decI (erRd m (t + 2)) ∧
    hslice? (erecP m) (erRd m (t + 3)).toNat (erRd m (t + 4)).toNat = some tb.levelParams ∧
    tb.numParams = (erRd m (t + 5)).toNat ∧ tb.numFields = (erRd m (t + 7)).toNat ∧
    hslice? (erecP m) (erRd m (t + 9)).toNat (erRd m (t + 10)).toNat = some tb.bodies.toList := by
  have hR := erRdOK m
  simp only [decTbl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨sn, hsn, lps, hlps, np, hnp, ct, -, nf, hnf, bd, hbd, rfl⟩ := h
  obtain ⟨w2, hw2, hw2l, hw2d⟩ := hd?_some hsn
  have r2 : erRd m (t + 2) = w2 := hR.offN (k := 2) hw2 (by decide)
  simp only [nat?, Option.map_eq_some_iff] at hnp hnf
  obtain ⟨wnp, hwnp, rfl⟩ := hnp
  obtain ⟨wnf, hwnf, rfl⟩ := hnf
  have r5 : erRd m (t + 5) = wnp := hR.offN (k := 5) hwnp (by decide)
  have r7 : erRd m (t + 7) = wnf := hR.offN (k := 7) hwnf (by decide)
  refine ⟨by rw [r2]; exact hw2l, by rw [r2, hw2d], sct_hlist_words hR (j := 3) hlps, by rw [r5],
    by rw [r7], by simpa using sct_hlist_words hR (j := 9) hbd⟩

/-- **`check_struct_proj_table` refines `checkStructProjTable`, both outcomes**, at the table record
`t` (`decTbl`): the two lists copied to `IW` (`er_to_iw`), the scoping through the real walks. -/
theorem tbl_ref {vis : Word} {fe : IFEnv} (p : Prog) (hP : TblProg p) (hp : ApdF p)
    (n : Nat) (m : Mem) (a : AState) (t : Word) (tb : IProjTable)
    (hS : StageR vis fe m a) (ht : decTbl (erecP m) t.toNat = some tb) (hnP : tb.numParams + 1 < 2 ^ 64)
    (hA : AbsOK m) (hok : ConRon.Bridge.StateOK a)
    (hks : ∃ ks, tb.levelParams.mapM (denoteN a.store.lss.ls.ns) = some ks) :
    RefE True (tblE p (n + 1) m t vis) (checkStructProjTable tb fe) a
      (fun v _ a' => TblPost vis fe m a v.2 a') := by
  obtain ⟨hT, hTn, hlps, hnp, hnf, hbds⟩ := sct_decTbl ht
  rw [tblE.arm1]
  simp only [erRd_foldN]
  unfold checkStructProjTable
  -- the level parameters' copy
  refine RefE.onlySim (fun _ => tblE.k_er_to_iw.none ..) (fun _ _ h => h) fun r1 m1 h1 => ?_
  obtain ⟨hS1, hg1, hd1, ht1, hE1⟩ := erToIwW_stage h1 hS hlps
  obtain ⟨-, -, -, hf1, -, -⟩ := erToIwW_dec h1 hS.iw.iwSize hS.iw.ctl hlps
  have hA1 : AbsOK m1 := erToIwW_afr h1 hA
  have hE1' : m1.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) := hf1.arr _ (by decide) (by decide)
  rw [tblE.k_er_to_iw.arm1]
  simp only [erRd_congr hE1 hE1']
  -- the bodies' copy
  refine RefE.onlySim (fun _ => tblE.k_er_to_iw_2.none ..) (fun _ _ h => h) fun r2 m2 h2 => ?_
  have hbds1 : hslice? (erA m1) (erRd m (t + 9)).toNat (erRd m (t + 10)).toNat = some tb.bodies.toList :=
    (IWGrow.ext hg1).hslice? hbds
  obtain ⟨hS2, hg2, hd2, ht2, hE2⟩ := erToIwW_stage h2 hS1 hbds1
  obtain ⟨-, -, -, hf2, -, -⟩ := erToIwW_dec h2 hS1.iw.iwSize hS1.iw.ctl hbds1
  have hA2 : AbsOK m2 := erToIwW_afr h2 hA1
  have hE2' : m2.arr64 (tier1 EREC) = m1.arr64 (tier1 EREC) := hf2.arr _ (by decide) (by decide)
  rw [tblE.k_er_to_iw_2.arm1]
  have hEE : m2.arr64 EREC = m.arr64 EREC := hE2.trans hE1
  have hEE' : m2.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) := hE2'.trans hE1'
  simp only [erRd_congr hEE hEE']
  have hd1' : decHL m2 (r1.headD 0).toNat (r1.tail.headD 0).toNat = some tb.levelParams :=
    decHL_grow' hg2 (by omega) hd1
  -- the scoping
  refine RefE.onlySim (fun _ => tblE.k_check_struct_proj_table_scoped.none ..) (fun _ _ h => h)
    fun rs m3 h3 => ?_
  have hnPw : (erRd m (t + 5)).toNat + 1 < 2 ^ 64 := by rw [← hnp]; exact hnP
  obtain ⟨b, a3, hrun3, hS3, hg3, hsok, hsl, hA3, he3⟩ := sctW_okR hp (erRd m (t + 5)) _ _ tb.levelParams
    hnPw n m2 a _ _ tb.bodies.toList hS2 hok hks hd1' (by have := hg2.iw; omega) hd2 (by omega) hA2
    rs m3 h3
  have hf3 := sctW_mfr_real hp _ _ _ _ _ _ _ _ _ _ h3
  have ps3 : ConRon.Bridge.Inductives.PStep a a3 := by
    have e' := he3
    simp only [sp, Prod.mk.injEq] at e'
    exact ConRon.Bridge.Inductives.PStep.of_caches (stateOK_of_sp hok he3)
      (by rw [e'.1]; exact ConRon.Arena.Ext.refl _) e'.2.1 e'.2.2
  have hlen : tb.bodies.size = (r2.tail.headD 0).toNat := by
    rw [← Array.length_toList, decHL_length m2 hd2]
  have hg03 : IWGrow m m3 := (hg1.trans hg2).trans hg3
  obtain ⟨hT3, hTn3, -, -, hnf3, -⟩ := sct_decTbl ((IWGrow.ext hg03).decTbl ht)
  by_cases hbl : r2.tail.headD 0 ≠ erRd m3 (t + 7)
  · rw [tblE.k_check_struct_proj_table_scoped.abort1 (hc1 := hbl)]
    exact RefE.of_cls0 rfl
  have hbl' : r2.tail.headD 0 = erRd m3 (t + 7) := Decidable.of_not_not hbl
  by_cases h10 : rs.headD 0 ≠ 1
  · rw [tblE.k_check_struct_proj_table_scoped.abort2 (hc1 := hbl') (hc2 := h10)]
    exact RefE.of_cls0 rfl
  have h1r : rs.headD 0 = 1 := Decidable.of_not_not h10
  rw [tblE.k_check_struct_proj_table_scoped.arm1 (hc1 := hbl') (hc2 := h1r)]
  simp only [erRd_foldN]
  rw [← hnp] at hrun3
  refine RefE.bind_right hrun3 ?_
  have hsz : tb.bodies.size = tb.numFields := by rw [hlen, hbl', hnf3]
  have hsok' : b = true := (sumB01 hsok hsl).1.mp h1r
  subst hsok'
  simp only [hsz, and_self, ite_true]
  -- `env_find`: the structure is stored
  refine RefE.onlySim (fun _ => tblE.k_env_find.none ..) (fun _ _ h => h) fun rf m4 hf => ?_
  by_cases hf0 : rf.headD 0 = 0
  · rw [tblE.k_env_find.abort1 (hc1 := hf0)]
    exact RefE.of_cls0 rfl
  rw [tblE.k_env_find.arm1 (hc1 := hf0)]
  simp only [erRd_foldN]
  obtain ⟨s4, hs4, hm4, -, hrf⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (envFind_spec p hP.hft.rowGet hP.hft.baseGet hP.hft.find n _ vis _) hf
  obtain rfl : m4 = m3 := hs4.symm.trans hm4
  subst hrf
  obtain ⟨hfind0, ci0, hci0⟩ := findRes_hit hS3.check.env hT3 hf0
  have hhit : (fe.find? tb.structName).isSome := by rw [hTn3, hfind0, hci0]; rfl
  simp only [hhit, ite_true]
  -- `find_table`: the table is not taken
  refine RefE.onlySim (fun _ => tblE.k_find_table.none ..) (fun _ _ h => h) fun rt m5 hft => ?_
  obtain ⟨s5, hs5, hm5, -, hfind, hsome5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
    (findTable_refines p hP.hft n _ vis _ hS3.check.env hT3) hft
  obtain rfl : m5 = m4 := hs5.symm.trans hm5
  by_cases ht0 : rt.headD 0 ≠ 0
  · rw [tblE.k_find_table.abort1 (hc1 := ht0)]
    have hsome : ¬ (fe.findTable? tb.structName).isNone = true := by
      rw [hTn3, hfind]
      obtain ⟨tbb, htb⟩ := hsome5 ht0
      dsimp only at htb
      simp only [tblFound, ht0, ↓reduceIte, htb, Option.isNone_some]
      decide
    exact fun _ => ErrClaim.ite_neg hsome (ErrClaim.fail _ _ (by decide))
  have ht0' : rt.headD 0 = 0 := Decidable.of_not_not ht0
  rw [tblE.k_find_table.arm1 (hc1 := ht0')]
  have hnone : fe.findTable? tb.structName = none := by rw [hTn3, hfind, ht0']; simp [tblFound]
  simp only [hnone, Option.isNone_none, ite_true]
  exact RefE.ret rfl ⟨hS3, hg03, ((erToIwW_mfr h1).trans (erToIwW_mfr h2)).trans hf3, hA3, ps3⟩


/-- **`check_struct_proj_table` refines `checkStructProjTable` under `StageC`** (`tbl_ref`'s ok
half): from `StageC` at `vis` of `fe`, the table record decoded and its level parameters' names read
back, a returning run keeps the stage and the twin's run is a `PStep`. -/
@[refines ConRon.Arena.checkStructProjTable]
theorem checkStructProjTable_refinesC (p : Prog) (hP : TblProg p) (hp : ApdF p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) {env : ConLeche.Env}
    (t vis : Word) (tb : IProjTable) (hC : StageC dn vis fe env s₀.mem a₀)
    (ht : decTbl (erecP s₀.mem) t.toNat = some tb) (hnP : tb.numParams + 1 < 2 ^ 64)
    (hA : AbsOK s₀.mem)
    {lpsP : List ConLeche.Name} (hlpsP : Frontend.denoteNList a₀.store.ns tb.levelParams = some lpsP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_struct_proj_table" [t, vis]
    ⦃fun _r s' => LocEq s' s₀ ∧
      AM.ok (checkStructProjTable tb fe) a₀ ∧
      StageR vis fe s'.mem (AM.st (checkStructProjTable tb fe) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem ∧
      ConRon.Bridge.Inductives.PStep a₀ (AM.st (checkStructProjTable tb fe) a₀); ⊤⦄ :=
  triple_post (RefE.triple (tblE_spec p hP (n + 1) s₀ t vis)
      (tbl_ref p hP hp n _ a₀ t tb hC.stage ht hnP hA hC.check.state
        ⟨lpsP, denoteNList_mapM hlpsP⟩)) fun _ _ ⟨hl, _, _, hrun, hR⟩ => by
    obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
    exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, hR.abs, by rw [hst]; exact hR.step⟩

/-! ## `check_block_tables`, one model and one refinement -/

/-- **The model of `check_block_tables`, both outcomes**: each table by
`check_struct_proj_table`'s unified model. -/
l_model ctbE_spec (p : Prog) (hP : TabsProg p)
  fns [hP.tabs ↦ ctbE]
  specs [tblE_spec p hP.tbl n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem TblPost.trans {vis : Word} {fe : IFEnv} {m m1 m2 : Mem} {a a1 a2 : AState}
    (h1 : TblPost vis fe m a m1 a1) (h2 : TblPost vis fe m1 a1 m2 a2) : TblPost vis fe m a m2 a2 :=
  ⟨h2.stage, h1.grow.trans h2.grow, h1.frame.trans h2.frame, h2.abs, h1.step.trans h2.step⟩

/-- `tbl_ref` at every fuel (at `0` the model is an error of class `0`). -/
theorem tblRef_any {vis : Word} {fe : IFEnv} (p : Prog) (hP : TblProg p) (hp : ApdF p)
    (n : Nat) (m : Mem) (a : AState) (t : Word) (tb : IProjTable)
    (hS : StageR vis fe m a) (ht : decTbl (erecP m) t.toNat = some tb) (hnP : tb.numParams + 1 < 2 ^ 64)
    (hA : AbsOK m) (hok : ConRon.Bridge.StateOK a)
    (hks : ∃ ks, tb.levelParams.mapM (denoteN a.store.lss.ls.ns) = some ks) :
    RefE True (tblE p n m t vis) (checkStructProjTable tb fe) a
      (fun v _ a' => TblPost vis fe m a v.2 a') := by
  match n with
  | 0 => rw [tblE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | k + 1 => exact tbl_ref p hP hp k m a t tb hS ht hnP hA hok hks

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

/-- What the tables' checks need of each table: its level parameters' names read back and its
parameter count bounded. -/
def TblsOK (st : EStore) (Q : List IProjTable) : Prop :=
  ∀ t ∈ Q, (∃ ks, t.levelParams.mapM (denoteN st.lss.ls.ns) = some ks) ∧ t.numParams + 1 < 2 ^ 64

/-- **`check_block_tables` refines `checkBlockTables`, both outcomes** (each table by `tbl_ref`),
over the `IW` slice of table records; the stage kept, the twin's run a `PStep`. -/
theorem ctb_ref {p : Prog} (hP : TabsProg p) (hp : ApdF p) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m : Mem) (a : AState) (tO tL : Word) (Q : List IProjTable),
    StageR vis fe m a → decPL m (decTbl (erecP m)) tO.toNat tL.toNat = some Q →
    tO.toNat + tL.toNat ≤ iwTop m → AbsOK m → ConRon.Bridge.StateOK a → TblsOK a.store Q →
    RefE True (ctbE p n m vis tO tL) (ConRon.Arena.checkBlockTables fe Q) a
      (fun v _ a' => TblPost vis fe m a v.2 a') := by
  induction n with
  | zero => intros; rw [ctbE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a tO tL Q hS hQ hb hA hok hT
  by_cases hl : tL = 0
  · rw [ctbE.arm1 (hc1 := hl)]
    have : Q = [] := by
      have h := decPL_length _ hQ; subst hl; exact List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this
    exact RefE.ret rfl ⟨hS, IWGrow.refl m, MFr.refl _ _ m, hA, ConRon.Bridge.Inductives.PStep.refl hok⟩
  obtain ⟨l1, hl1, hll⟩ := L.exists_toNat_eq_succ hl
  have hQ' := hQ
  rw [hl1, decPL_succ_do] at hQ'
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hQ'
  obtain ⟨t0, ⟨q, hq, ht0⟩, ts, hts, rfl⟩ := hQ'
  have hT64 : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hrq, -⟩ := iwN_rdW hq (by omega)
  rw [UInt64.ofNat_toNat] at hrq
  rw [ctbE.arm2 (hc1 := hl), hrq]
  have hqn : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' (by
    have := iwN_lt hq; have := hS.iw.iwSize
    simp only [iwN, nat?, iwA, aread_apply, Option.map_eq_some_iff] at hq
    obtain ⟨w, hw, rfl⟩ := hq; exact w.toNat_lt)
  obtain ⟨hk0, hn0⟩ := hT t0 (List.mem_cons_self ..)
  have hR := tblRef_any (fe := fe) p hP.tbl hp n m a (UInt64.ofNat q) t0 hS (by rw [hqn]; exact ht0) hn0 hA hok hk0
  simp only [ConRon.Arena.checkBlockTables]
  refine RefE.bindE (fun _ => ctbE.k_check_struct_proj_table.none ..) id hR fun v y a1 _ hQ1 => ?_
  obtain ⟨u, m2⟩ := v
  rw [ctbE.k_check_struct_proj_table.arm1]
  have hto1 : (tO + 1).toNat = tO.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hts' : decPL m2 (decTbl (erecP m2)) (tO + 1).toNat (tL - 1).toNat = some ts := by
    rw [hto1, hll]; exact decPL_tbl_grow hQ1.grow (by omega) hts
  exact RefE.tail_eq (f := fun v => (0, v.2)) (fun e => ctbE.k_check_block_tables.none p e)
    (fun v => ctbE.k_check_block_tables.arm1 p v.1 v.2) id rfl (fun v y a' hR => hQ1.trans hR)
    (ih m2 a1 (tO + 1) (tL - 1) ts hQ1.stage hts' (by rw [hto1, hll]; have h1 := hQ1.grow.iw; have h2 := hb; rw [hl1] at h2; simp only at h1; omega) hQ1.abs hQ1.step.ok
      (fun t ht => ⟨names_ext hQ1.step.ext (hT t (List.mem_cons_of_mem _ ht)).1,
        (hT t (List.mem_cons_of_mem _ ht)).2⟩))


end L.Ind
