import ConAgua.Arena.IndSumSpec14
import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.IndT.Lift

/-!
# `check_struct_proj_table_scoped` through the real `all_level_params_defined` (lane `indproofs4`, helper `sct`)

`sctW` reads `all_level_params_defined` through a `CallM` (`IndSumSpec14.lean`); `sctW_ok` is the
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
-/

set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The walk's twin-side environment from `StateOK` -/

/-- **`ApdEnv` from the store's well-formedness** (`TwinOK.of_check`'s two level fields). -/
theorem ApdEnv.of_state {a : AState} (hok : ConRon.Bridge.StateOK a) : ApdEnv a := by
  obtain ⟨rk, hw⟩ := hok.wf
  have hw' : StoreWF' a.store := StoreWF'.of_wf ⟨rk, hw⟩
  obtain ⟨rk', hw''⟩ := hw'
  have hLs : LsStoreWF' a.store.lss := hw''.lss
  have hL : LStoreWF' a.store.ls := hLs.ls
  refine ⟨hw.nsWF, fun x u hv => ?_, fun x c us hv => ?_⟩
  · exact ConRon.Bridge.denoteL_of_view hL (hw.lchildOK x _ hv u (by simp [ENodeView.lchildren])).1
  · have hs := (hw.lschildOK x _ hv us (by simp [ENodeView.lschildren])).1
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨xs, hxs⟩ := ConRon.Bridge.denoteLs_of_view hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩

/-- `StateOK` reads the store only. -/
theorem stateOK_of_sp {a a' : AState} (h : ConRon.Bridge.StateOK a) (e : sp a' = sp a) :
    ConRon.Bridge.StateOK a' := by
  simp only [sp, Prod.mk.injEq] at e
  exact ⟨by rw [e.1]; exact h.wf⟩

/-- **`StageC` across a step that keeps the twin's store, caches and pins**. -/
theorem StageC.of_sp {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} {m m' : Mem} {a a' : AState} (h : StageC dn vis fe env m a)
    (hS : StageR dn vis fe m' a') (hA : AbsOK m') (e : sp a' = sp a) : StageC dn vis fe env m' a' := by
  have e' := e
  simp only [sp, Prod.mk.injEq] at e'
  exact h.of_pstep hS hA (ConRon.Bridge.Inductives.PStep.of_caches (stateOK_of_sp h.check.state e)
    (by rw [e'.1]; exact ConRon.Arena.Ext.refl _) e'.2.1 e'.2.2)

/-! ## `all_level_params_defined`, the real walk -/

/-- **`all_level_params_defined`'s model under `StageR`, `AbsOK` and the twin's `StateOK`**: the
twin state stays as it was, `AbsOK` holds after (the walk's memo is the core's `wscopedBFast`
memo, `apdMR_ws`; the rest is framed). -/
theorem apdF_simR {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (o l e : Word) (he : H e) (lps : List NIdx) (hS : StageR dn vis fe m a)
    (hA : AbsOK m) (hok : ConRon.Bridge.StateOK a) (hdec : decHL m o.toNat l.toNat = some lps)
    (hks : ∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks) :
    Sim (apdF m [o, l, e]) (allLevelParamsDefined lps (decI e)) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r x ∧ AbsOK m' ∧
        sp a' = sp a) := by
  intro r m' h
  obtain ⟨ks, hks⟩ := hks
  obtain ⟨n, hc⟩ := callF_run h
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
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
    by rw [hf.2.2.1]; exact hE, by rw [hf.2.2.1]; exact hSp, by rw [hf.2.2.1]; exact hB,
    by rw [pinW_frame hf (by decide)]; exact hP⟩
  · exact memoRG_frame coreFlSch coreFlSch_wf bmKey _ _ _ (by decide) (by decide) _ _ hf mf hfl
  · exact memoRG_frame coreLsbSch coreLsbSch_wf bmKey _ _ _ (by decide) (by decide) _ _ hf ml hlsb

/-- `apdF_simR` at the program's own call (`realCall p`'s reading). -/
theorem apdCall_simR {p : Prog} (hp : ApdF p) (k : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} (o l e : Word) (he : H e) (lps : List NIdx)
    (hS : StageR dn vis fe m a) (hA : AbsOK m) (hok : ConRon.Bridge.StateOK a)
    (hdec : decHL m o.toNat l.toNat = some lps)
    (hks : ∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks) :
    Sim (realCall p k "all_level_params_defined" [o, l, e] m) (allLevelParamsDefined lps (decI e)) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r x ∧ AbsOK m' ∧
        sp a' = sp a) :=
  fun r m' h => apdF_simR o l e he lps hS hA hok hdec hks r m' (apdF_of_callW hp h)

/-! ## The other three walks keep the twin's store -/

/-- `has_fvar_fast` (`hffF_ok`), the twin's store, caches and pins kept. -/
theorem hffF_simR {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (f e : Word) (he : H e) (hS : StageR dn vis fe m a) :
    Sim (hffF m [f, e]) (hasFvarFast f.toNat (decI e)) a
      (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r x) ∧ sp a' = sp a) := by
  intro r m' h
  obtain ⟨x, a', hrun, hK⟩ := hffF_ok dn vis fe f e he m m' a r h hS
  obtain ⟨X, rfl⟩ := memos_only_of_sp (Keeps.bind (keeps_fvarB_sp _ _) fun _ => Keeps.pure _) x a' hrun
  exact ⟨x, _, hrun, hK, rfl⟩

/-- `loose_bvars_bounded_fast` (`lbbF_ok`), the twin's store, caches and pins kept. -/
theorem lbbF_simR {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (f k e : Word) (he : H e) (hS : StageR dn vis fe m a) :
    Sim (lbbF m [f, k, e]) (looseBVarsBoundedFast f.toNat k.toNat (decI e)) a
      (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r x) ∧ sp a' = sp a) := by
  intro r m' h
  obtain ⟨x, a', hrun, hK⟩ := lbbF_ok dn vis fe f k e he m m' a r h hS
  obtain ⟨X, rfl⟩ := memos_only_of_sp (Keeps.bind (keeps_bvarB_sp _ _) fun _ => Keeps.pure _) x a' hrun
  exact ⟨x, _, hrun, hK, rfl⟩

/-- `consts_resolve_ffast` (`constsResolveFFast_keepsSt`), the twin state kept, `AbsOK` after. -/
theorem crfF_simR {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (e : Word) (he : H e) (hS : StageR dn vis fe m a) (hA : AbsOK m) :
    Sim (crfF m [vis, e]) (constsResolveFFast fe (decI e)) a
      (fun r x m' a' => (StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r x) ∧ AbsOK m' ∧
        sp a' = sp a) := by
  intro r m' h
  obtain ⟨hAb, hI1, hCr, hIl, hWk⟩ := hA
  have hfr := crfF_frame h
  obtain ⟨x, a', hrun, hK, hCr', ha'⟩ := relW_callF (P := crfP)
    (L.Stubs.constsResolveFFast_keepsSt crfP_prog (dn := dn) (vis := vis) (fe := fe) e he a).refAM
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
theorem sctW_okR {p : Prog} (hp : ApdF p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} (nP lo ll : Word) (lps : List NIdx) (hnP : nP.toNat + 1 < 2 ^ 64) (n : Nat) :
    ∀ (m : Mem) (a : AState) (bO bL : Word) (bs : List EIdx),
    StageR dn vis fe m a → ConRon.Bridge.StateOK a →
    (∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks) →
    decHL m lo.toNat ll.toNat = some lps → lo.toNat + ll.toNat ≤ iwTop m →
    decHL m bO.toNat bL.toNat = some bs → bO.toNat + bL.toNat ≤ iwTop m → AbsOK m →
    Sim (sctW (realCall p) n m vis nP lo ll bO bL) (bs.allM (scopeT fe lps nP.toNat)) a
      (fun r b m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0 != 0) = b ∧
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
  have h1 := hffF_simR (dn := dn) (vis := vis) (fe := fe) CWF w hwl hS
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
  have h4 := lbbF_simR (dn := dn) (vis := vis) (fe := fe) CWF (nP + 1) w hwl hS3
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
        (by have := hg14.1; omega) (by rw [decHL_grow hg14 hb1']; exact hbs') (by have := hg14.1; omega) hA4)
      fun r b m' a' hQ => ⟨hQ.1, hg14.trans hQ.2.1, by simpa using hQ.2.2.1, by simpa using hQ.2.2.2.1,
        hQ.2.2.2.2.1, hQ.2.2.2.2.2.trans he14⟩
  · rw [sctK4_no (h := hc)]
    have ht : (!a1 && a2 && a3 && a4) = false := by
      cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> simp_all
    simp only [ht]
    exact Sim.ret ⟨hS4, hg14, rfl, by decide, hA4, he14⟩

/-- **`check_struct_proj_table_scoped`'s model (`realCall p`) under `StageC`** (`sctW_okR`, with
`StageC` carried: the twin's store, caches and pins are kept). -/
theorem sctW_okC {p : Prog} (hp : ApdF p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {env : ConLeche.Env} (nP lo ll : Word) (lps : List NIdx)
    (hnP : nP.toNat + 1 < 2 ^ 64) (n : Nat) (m : Mem) (a : AState) (bO bL : Word) (bs : List EIdx)
    (hC : StageC dn vis fe env m a) (hks : ∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks)
    (hlps : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hbs : decHL m bO.toNat bL.toNat = some bs) (hbb : bO.toNat + bL.toNat ≤ iwTop m) (hA : AbsOK m) :
    Sim (sctW (realCall p) n m vis nP lo ll bO bL) (bs.allM (scopeT fe lps nP.toNat)) a
      (fun r b m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ (r.headD 0 != 0) = b ∧
        (r.headD 0).toNat ≤ 1 ∧ AbsOK m' ∧ sp a' = sp a) :=
  Sim.mono (sctW_okR hp nP lo ll lps hnP n m a bO bL bs hC.stage hC.check.state hks hlps hlb hbs hbb hA)
    fun _ _ _ _ h => ⟨hC.of_sp h.1 h.2.2.2.2.1 h.2.2.2.2.2, h.2⟩

end L.Ind
