import ConAgua.Arena.IndSumSpec14
import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndInstallSpec27

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

/-! ## `check_struct_proj_table`, the real reading -/

/-- `sctW (realCall p)`'s frame. -/
theorem sctW_mfr_real {p : Prog} (hp : ApdF p) : ∀ (n : Nat) (m m' : Mem) (vis nP lo ll bO bL : Word)
    (r : List Word), sctW (realCall p) n m vis nP lo ll bO bL = some (r, m') → MFr [] [] m m' :=
  sctW_mfr fun _ _ _ _ _ h => MFr.of_frame (apdF_frame (apdF_of_callW hp h))
    (fun b hb => .inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb; decide))
    (fun x hx => .inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                          rcases hx with rfl | rfl <;> decide))

/-- A `Sim` also records the twin's run. -/
theorem sctSim_withRun {β α : Type} {mo : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} (h : Sim mo op a Q) :
    Sim mo op a (fun r x m' a' => Q r x m' a' ∧ op.run a = .ok (x, a')) := by
  intro r m' e; obtain ⟨x, a', h1, h2⟩ := h r m' e; exact ⟨x, a', h1, h2, h1⟩

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

/-- **`check_struct_proj_table`'s model (`realCall p`) refines `checkStructProjTable`** (`tblW_okM`
with the scoping through the real `all_level_params_defined`, `sctW_okR`): beyond `tblW_okM`'s
hypotheses the twin's `StateOK`, the level parameters' names, the structure's name and the
constructor's type read back; the twin's run is a `PStep` (con-ron's `structProjBodies_spec`, the
scoping keeping the state, `projTableName_spec`). -/
theorem tblW_okR {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (p : Prog)
    (hP : TblProg p) (hp : ApdF p)
    (n : Nat) (m : Mem) (a : AState) (T C lo ll nP nF rs go gl off cvCaw : Word) (lps : List NIdx)
    (guards : List LIdx) (cvCa : IConstantVal) (hS : StageR dn vis fe m a) (hT : H T) (hC : H C)
    (hrs : H rs) (hnP : nP.toNat + 1 < 2 ^ 64)
    (hlps : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hgs : decHL m go.toNat gl.toNat = some guards) (hgb : go.toNat + gl.toNat ≤ iwTop m)
    (hcv : DecB (fun m => decCVp m cvCaw.toNat) m cvCa) (hA : AbsOK m)
    (hok : ConRon.Bridge.StateOK a) (hks : ∃ ks, lps.mapM (denoteN a.store.lss.ls.ns) = some ks)
    {TP : ConLeche.Name} (hTP : denoteN a.store.ns (decI T) = some TP)
    {ctyP : ConLeche.Expr} (hcty : denoteE a.store cvCa.type = some ctyP) :
    Sim (tblW (realCall p) p n m T C lo ll nP nF rs go gl off cvCaw vis)
      (checkStructProjTable (decI T) (decI C) lps nP.toNat nF.toNat (decI rs) guards off.toNat cvCa fe) a
      (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m' ∧ MFr [] [] m m' ∧ AbsOK m' ∧
        ConRon.Bridge.Inductives.PStep a a') := by
  unfold tblW checkStructProjTable
  obtain ⟨w, hw, hwl, hwd⟩ := sumTypeWord (DecB.get (OMono.decCVp _) hcv) hS.2.2.2.2.1
  rw [hw, ← hwd]
  rw [← hwd] at hcty
  -- `struct_proj_bodies`
  refine Sim.bindK (K := tblK1 (realCall p) p n vis T lo ll nP C nF rs off go gl) rfl (fun _ _ => rfl)
    (Q := fun rb ob m1 a1 => (StageR dn vis fe m1 a1 ∧ IWGrow m m1 ∧ PBDecA m1 rb ob ∧ AbsOK m1) ∧
      MFr [] [] m m1 ∧ ConRon.Bridge.Inductives.PStep a a1)
    (fun r m' e => by
      obtain ⟨x, a', h1, h2⟩ := spbW_ok dn vis fe (n + 1) m m' a T nP nF w r e hS hwl (by omega)
        nF.toNat_lt hA
      obtain ⟨ps, -⟩ := ConRon.Bridge.Inductives.structProjBodies_spec (decI T) TP nP.toNat nF.toNat
        (decI w) ctyP a a' x hok ⟨hTP, hcty⟩ h1
      exact ⟨x, a', h1, h2, spbW_mfr e, ps⟩) fun rb ob m1 a1 hQ => ?_
  obtain ⟨⟨hS1, hg1, hdec1, hA1⟩, hf1, ps1⟩ := hQ
  by_cases h10 : rb.headD 0 = 0
  · rw [tblK1_no (h := h10)]; exact Sim.of_none
  rw [tblK1_yes (h := h10)]
  cases ob with
  | none => exact absurd hdec1 h10
  | some bodies =>
  obtain ⟨-, hbd, hbb⟩ := hdec1
  refine Sim.bind_twin (x := bodies) (a₁ := a1) rfl ?_
  have hlps1 : decHL m1 lo.toNat ll.toNat = some lps := by rw [decHL_grow hg1 hlb]; exact hlps
  have hlb1 : lo.toNat + ll.toNat ≤ iwTop m1 := by have := hg1.1; omega
  -- the scoping
  refine Sim.bindK (K := tblK2 p n vis T lo ll nP C nF rs off go gl _ _) rfl (fun _ _ => rfl)
    (Sim.withFr (F := fun m2 => MFr [] [] m1 m2)
      (sctW_okR hp nP lo ll lps hnP (n + 1) m1 a1 _ _ bodies.toList hS1 ps1.ok (names_ext ps1.ext hks)
        hlps1 hlb1 hbd hbb hA1)
      (fun _ _ e => sctW_mfr_real hp _ _ _ _ _ _ _ _ _ _ e))
    fun rs' sok m2 a2 hQ => ?_
  obtain ⟨⟨hS2, hg2, hsok, hsl, hA2, he2⟩, hf2⟩ := hQ
  have ps2 : ConRon.Bridge.Inductives.PStep a a2 := by
    have e' := he2
    simp only [sp, Prod.mk.injEq] at e'
    exact ps1.trans (ConRon.Bridge.Inductives.PStep.of_caches (stateOK_of_sp ps1.ok he2)
      (by rw [e'.1]; exact ConRon.Arena.Ext.refl _) e'.2.1 e'.2.2)
  by_cases hlen0 : rb.tail.tail.headD 0 ≠ nF
  · rw [tblK2_len (h := hlen0)]; exact Sim.of_none
  have hlen : rb.tail.tail.headD 0 = nF := Decidable.of_not_not hlen0
  by_cases h10' : rs'.headD 0 ≠ 1
  · rw [tblK2_bad (h := hlen) (h1 := h10')]; exact Sim.of_none
  have h1 : rs'.headD 0 = 1 := Decidable.of_not_not h10'
  rw [tblK2_ok (h := hlen) (h1 := h1)]
  have hsz : bodies.size = nF.toNat := by
    rw [← Array.length_toList, decHL_length m1 hbd, hlen]
  have hsok' : sok = true := (sumB01 hsok hsl).1.mp h1
  subst hsok'
  simp only [hsz, and_self, ite_true]
  -- `proj_table_name`
  refine Sim.bindK (K := tblK3 p n vis T lo ll nP C nF rs off go gl _ _) rfl (fun _ _ => rfl)
    (sctSim_withRun (Sim.withFr (F := fun m3 => MFr [] [] m2 m3 ∧ AFr m2 m3)
      (sumSim_of_relW (ptF_ok dn vis fe T hT) hS2)
      (fun _ _ e => ⟨MFr.of_frame (ptF_frame e) (by simp [POOL, POOL1, NSREC, NSSLOT, NNREC, NNSLOT]) (by simp),
        AFr.of_frame (ptF_frame e)⟩))) fun rt tn m3 a3 hQ => ?_
  obtain ⟨⟨⟨hS3, hg3, htnl, htn⟩, hf3, ha3⟩, hrun3⟩ := hQ
  have ps3 : ConRon.Bridge.Inductives.PStep a a3 := by
    obtain ⟨hwf3, hx3, -, hc3, hp3, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a2) rfl hrun3
      (ConRon.Bridge.Core.projTableName_spec a2 (decI T) TP ps2.ok.wf (ConRon.Bridge.denoteN_ext hTP ps2.ext))
    exact ps2.trans (ConRon.Bridge.Inductives.PStep.of_caches ⟨hwf3⟩ hx3 hc3 hp3)
  subst htn
  rw [tblK3_some]
  -- `env_find`
  rcases hf : envFindW m3 (rt.headD 0) vis with _ | ⟨rf, m4⟩
  · exact Sim.of_none
  by_cases hf0 : rf.headD 0 ≠ 0
  · rw [tblK4_found (h := hf0)]; exact Sim.of_none
  have hf0' : rf.headD 0 = 0 := Decidable.of_not_not hf0
  rw [tblK4_free (h := hf0')]
  obtain ⟨hm43, hmiss⟩ := envFindW_miss hf hS3.1.env htnl hf0'
  rw [hm43]
  simp only [hmiss, Option.isNone_none, ite_true]
  -- the three copies
  have hg13 := (hg1.trans hg2).trans hg3
  rcases h5 : efW n m3 lo ll with _ | ⟨rl, m5⟩
  · exact Sim.of_none
  obtain ⟨hS5, hg5, hrl1, hrl0, hsl5, ht5⟩ := efW_stage n h5 hS3
    (by rw [decHL_grow hg13 hlb]; exact hlps) (by have := hg13.1; omega)
  rw [tblK5_some]
  have hg25 := (hg2.trans hg3).trans hg5
  rcases h6 : efW n m5 (rb.tail.headD 0) (rb.tail.tail.headD 0) with _ | ⟨rb2, m6⟩
  · exact Sim.of_none
  obtain ⟨hS6, hg6, hrb1, hrb0, hsl6, ht6⟩ := efW_stage n h6 hS5
    (by rw [decHL_grow hg25 hbb]; exact hbd) (by have := hg25.1; omega)
  rw [tblK6_some]
  have hg06 := (((hg1.trans hg2).trans hg3).trans hg5).trans hg6
  rcases h7 : efW n m6 go gl with _ | ⟨rg, m7⟩
  · exact Sim.of_none
  obtain ⟨hS7, hg7, hrg1, hrg0, hsl7, ht7⟩ := efW_stage n h7 hS6
    (by rw [decHL_grow hg06 hgb]; exact hgs) (by have := hg06.1; omega)
  rw [tblK7_some]
  -- the record
  rcases h8 : erAllocW m7 14 with _ | ⟨q, m8⟩
  · exact Sim.of_none
  rw [tblK8_some, tblMem_eq]
  obtain ⟨hSM, hgM, hq, htM, hget⟩ := erRec_stage h8 hS7
    [6, rt.headD 0, T, rl.headD 0, rl.tail.headD 0, nP, C, nF, rs, rb2.headD 0, rb2.tail.headD 0,
      rg.headD 0, rg.tail.headD 0, off] rfl
  have hfM : MFr [] [] m7 (wrER m8 q [6, rt.headD 0, T, rl.headD 0, rl.tail.headD 0, nP, C, nF, rs,
      rb2.headD 0, rb2.tail.headD 0, rg.headD 0, rg.tail.headD 0, off]) :=
    (erAllocW_mfr h8).trans (wrER_mfr _ _ _)
  generalize hM : wrER m8 q _ = M at hSM hgM htM hget hfM
  have hPE : ∀ i < 14, (erecP M)[q.toNat + i]? = (M.arr64 EREC)[q.toNat + i]? :=
    fun i hi => erecP_getE (by simp at htM; omega)
  have he6 := IWGrow.erecPExtR (hg6.trans hg7 |>.trans hgM)
  have he7 := IWGrow.erecPExtR (hg7.trans hgM)
  have he5 := IWGrow.erecPExtR ((hg6.trans hg7).trans hgM)
  have hci := sumDecTbl (a := erecP M) (dn := dn) (q := q.toNat)
    (fun i hi => by rw [hPE i hi, hget i (by simpa using hi)]) htnl hT hC hrs
    (by rw [hrl1]; exact ArrExt.hslice? he5 hsl5) (by rw [hrb1]; exact ArrExt.hslice? he7 hsl6)
    (by rw [hrg1]; exact ArrExt.hslice? (IWGrow.erecPExtR hgM) hsl7)
  -- `env_push`
  have hq1 : (rdW (M.arr64 EREC) (q + 1)).toNat < 2 ^ 32 := by
    have h1 := hget 1 (by simp)
    have hlt : q.toNat + 1 < (M.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp (by simpa using h1)).1
    rw [rdW_of_get? (by rw [sumToNat_succ (by have := hSM.2.2.2.2.1; omega)]) (by simpa using h1)]
    simpa using htnl
  rcases hc : callW p (n + 1) "env_push" [vis, q] M with _ | ⟨rv, m9⟩
  · exact Sim.of_none
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨M, Locals.init []⟩)
    (envPush_specW p hP.hrec (n + 1) ⟨M, Locals.init []⟩ vis q hq1) hc
  subst hs4
  obtain ⟨hS9, hg9⟩ := envPushW_ok hW4 hSM hci
  rw [tblK9_some]
  refine Sim.ret ⟨by simpa using hS9, ?_, ?_, ?_, ps3⟩
  · exact ((((((hg1.trans hg2).trans hg3).trans hg5).trans hg6).trans hg7).trans hgM).trans hg9
  · exact ((((((hf1.trans hf2).trans hf3).trans (efW_mfr h5)).trans (efW_mfr h6)).trans (efW_mfr h7)).trans
      hfM).trans (envPushW_mfr hW4)
  · subst hM
    exact ((((((ha3.trans (efW_afr h5)).trans (efW_afr h6)).trans (efW_afr h7)).trans
      (erAllocW_afr h8)).trans (wrER_afr _ _ _)).trans (envPushW_afr hW4)) hA2

/-- **`check_struct_proj_table` refines `checkStructProjTable` under `StageC`**, through the real
`all_level_params_defined` (`realCall p`; `checkStructProjTable_refines`' with the stub contract):
from `StageC` at `vis` of `fe`, `checkStructProjTable_refines`' decodings and the walk memos, and
the twin's readings of the structure's name, the level parameters and the constructor
(`checkStructProjTable_runF`'s), a returning run returns the view of `fe` with the `projInfo`
table pushed, and the twin's run is a `PStep`. -/
@[refines ConRon.Arena.checkStructProjTable]
theorem checkStructProjTable_refinesC (p : Prog) (hP : TblProg p) (hp : ApdF p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) {env : ConLeche.Env}
    (T C lo ll nP nF rs go gl off cvCaw vis : Word)
    (lps : List NIdx) (guards : List LIdx) (cvCa : IConstantVal) (hC : StageC dn vis fe env s₀.mem a₀)
    (hT : H T) (hC' : H C) (hrs : H rs) (hnP : nP.toNat + 1 < 2 ^ 64)
    (hlps : decHL s₀.mem lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop s₀.mem)
    (hgs : decHL s₀.mem go.toNat gl.toNat = some guards) (hgb : go.toNat + gl.toNat ≤ iwTop s₀.mem)
    (hcv : DecB (fun m => decCVp m cvCaw.toNat) s₀.mem cvCa) (hA : AbsOK s₀.mem)
    {TP : ConLeche.Name} (hTP : denoteN a₀.store.ns (decI T) = some TP)
    {lpsP : List ConLeche.Name} (hlpsP : Frontend.denoteNList a₀.store.ns lps = some lpsP)
    {cvCaP : ConLeche.ConstantVal} (hcvP : Frontend.denoteCV a₀.store cvCa = some cvCaP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "check_struct_proj_table"
      [T, C, lo, ll, nP, nF, rs, go, gl, off, cvCaw, vis]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (checkStructProjTable (decI T) (decI C) lps nP.toNat nF.toNat (decI rs) guards off.toNat
        cvCa fe) a₀ ∧
      StageR dn (r.headD 0) (AM.res (checkStructProjTable (decI T) (decI C) lps nP.toNat nF.toNat
        (decI rs) guards off.toNat cvCa fe) a₀) s'.mem (AM.st (checkStructProjTable (decI T) (decI C)
          lps nP.toNat nF.toNat (decI rs) guards off.toNat cvCa fe) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem ∧
      ConRon.Bridge.Inductives.PStep a₀ (AM.st (checkStructProjTable (decI T) (decI C) lps nP.toNat
        nF.toNat (decI rs) guards off.toNat cvCa fe) a₀); ⊤⦄ := by
  refine triple_post (tblW_spec p hP (realCall p) (realCall_spec p) n s₀ T C lo ll nP nF rs go gl off
    cvCaw vis) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hok, hS', hg', -, hA', hps⟩ := (tblW_okR p hP hp n _ a₀ T C lo ll nP nF rs go gl off cvCaw lps
    guards cvCa hC.stage hT hC' hrs hnP hlps hlb hgs hgb hcv hA hC.check.state
    ⟨lpsP, denoteNList_mapM hlpsP⟩ hTP (ConRon.Bridge.denoteCV_type hcvP)).run hm
  exact ⟨hl, hok, hS', hg', hA', hps⟩

/-! ## `check_block_tables`, the real reading -/

/-- **`check_block_tables_one`'s model refines one member's install** (`ctoW_sim`, the table through
the real `all_level_params_defined`: `tblW_okR`), from the twin's `StateOK`, `PinsOK` and the
shape's, the member's, the constructor's and its sorts' readings; the twin's run is a `PStep`
(con-ron's `structProjGuards_spec`, `tblW_okR`'s). -/
theorem ctoW_simR {p : Prog} (hP : TabsProg p) (hp : ApdF p) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState} {pp ms co so : Word} {bs : BlockShape} {msh : MemberShape}
    {cA : IConstantVal} {nF : Nat} {sorts : List LIdx}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hms : DecB (fun m => decMS m ms.toNat) m msh) (hcs : PSlR decCN [(cA, nF)] co 1 m)
    (hss : PSlR decIS [sorts] so 1 m) (hM : HbMemo m) (hA : AbsOK m)
    (hkeep : ∀ f ∈ tablesKeepCallees, AbsKeep p f)
    (hok : ConRon.Bridge.StateOK a) (hpins : ConRon.Bridge.PinsOK a)
    {pP : ConLeche.BlockShape} (hsh : ConRon.Bridge.Inductives.dShape a.store bs = some pP)
    {mP : ConLeche.MemberShape} (hmP : ConRon.Bridge.Inductives.dMember a.store msh = some mP)
    {cAP : ConLeche.ConstantVal} (hcAP : Frontend.denoteCV a.store cA = some cAP)
    {sortsP : List ConLeche.Level} (hsP : denoteLList a.store.ls sorts = some sortsP) :
    Sim (ctoW p n m pp ms co so vis) (tabOne fe bs msh cA nF sorts) a
      (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m' ∧ HbMemo m' ∧ AbsOK m' ∧
        ConRon.Bridge.Inductives.PStep a a') := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  -- the constructor `[cv, nF]`
  obtain ⟨pc, y, ys, hy, hw0, hpcb, hdc, -⟩ := partsPSl_cons hcs (by decide)
  simp only [List.cons.injEq] at hy
  obtain ⟨rfl, -⟩ := hy
  obtain ⟨⟨cvp, hcvp, hcv⟩, hnF⟩ := decCN_some (show decCN (truncM m) pc = some (cA, nF) from hdc)
  have hpc' : (UInt64.ofNat pc : Word).toNat = pc := UInt64.toNat_ofNat_of_lt' hpcb
  have hlt1 := partsIwLt hnF
  obtain ⟨hw1, hcvb, -⟩ := partsIwRd hcvp hpc'
  obtain ⟨hw2, hnFb, -⟩ := partsIwRd hnF (w := UInt64.ofNat pc + 1)
    (by rw [UInt64.toNat_add, hpc']; simp; omega)
  -- the sorts `[off, len]`
  obtain ⟨ps, z, zs, hz, hw3, hpsb, hds, -⟩ := partsPSl_cons hss (by decide)
  simp only [List.cons.injEq] at hz
  obtain ⟨rfl, -⟩ := hz
  have hps' : (UInt64.ofNat ps : Word).toNat = ps := UInt64.toNat_ofNat_of_lt' hpsb
  obtain ⟨so', sl', hso, hsl, hdd⟩ := decAt_some (show decIS (truncM m) ps = some sorts from hds)
  have hlt2 := partsIwLt hsl
  obtain ⟨hw4, hsob, -⟩ := partsIwRd hso hps'
  obtain ⟨hw5, hslb, -⟩ := partsIwRd hsl (w := UInt64.ofNat ps + 1)
    (by rw [UInt64.toNat_add, hps']; simp; omega)
  have hso' : (UInt64.ofNat so' : Word).toNat = so' := UInt64.toNat_ofNat_of_lt' hsob
  have hsl' : (UInt64.ofNat sl' : Word).toNat = sl' := UInt64.toNat_ofNat_of_lt' hslb
  have hsorts : decHL m so' sl' = some sorts ∧ (sl' = 0 ∨ so' + sl' ≤ iwTop m) := by
    by_cases h0 : sl' = 0
    · subst h0
      have : sorts = [] := by simpa [decHL, hslice?] using hdd.symm
      subst this; exact ⟨by simp [decHL, hslice?], .inl rfl⟩
    · have hb := decHL_truncM_bound hdd h0
      exact ⟨by rw [← decHL_truncM hb]; exact hdd, .inr hb⟩
  -- the shape's words
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨hnpw, hnpb, hrs32, hrse⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  -- the member's name
  have hmsT : decMS (truncM m) ms.toNat = some msh := hms
  obtain ⟨⟨cvm, hcvm, hcvT⟩, -, -⟩ := decMS_some hmsT
  obtain ⟨hw6, hcvmb, -⟩ := partsIwRd hcvm rfl
  -- the fuel
  match n with
  | 0 =>
    intro r m' e
    simp only [ctoW, callW_zero] at e
    split at e <;> simp [ctoK1] at e
  | 1 =>
    intro r m' e
    have hz0 : ∀ a1 a2 a3 a4 a5 : Word, callW p 1 "struct_proj_guards" [a1, a2, a3, a4, a5] m = none := by
      intro a1 a2 a3 a4 a5
      cases h : callW p 1 "struct_proj_guards" [a1, a2, a3, a4, a5] m with
      | none => rfl
      | some y =>
        obtain ⟨s', -, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
          (spg_spec p hP.tbl.hv hP.hf hP.hput hP.hins hP.hgo hP.hbp hP.hst hP.hsg hP.tbl.ha hP.tbl.hc hP.tbl.hsc
            hP.hul hP.hgd hP.hmf hP.hmp hP.him hP.hcol hP.hrow hP.hpw hP.hcl hP.hspg 0 _ a1 a2 a3 a4 a5) h
        rw [spgW_zero] at hW; cases hW
    simp only [ctoW, hz0] at e
    split at e <;> simp [ctoK1] at e
  | j + 2 =>
  unfold ctoW
  rw [hw0, hw1, hw2, hw3, hw4, hw5, hnpw]
  by_cases hg : UInt64.ofNat bs.nP + UInt64.ofNat nF + 1 ≤ (UInt64.ofNat bs.nP : Word)
  · rw [if_pos hg]; exact Sim.of_none
  rw [if_neg hg]
  have hb := nPnF_bound hg
  rw [UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnFb] at hb
  obtain ⟨w, hwT, hwl, hwd⟩ := sumTypeWord (q := UInt64.ofNat cvp)
    (by rw [UInt64.toNat_ofNat_of_lt' hcvb]; exact DecB.get (OMono.decCVp _) hcv) hS.2.2.2.2.1
  rw [hwT]
  unfold tabOne
  -- `struct_proj_guards`
  refine Sim.bindK (K := ctoK1 p (j + 2) pp ms (UInt64.ofNat cvp) (UInt64.ofNat nF) vis) rfl (fun _ _ => rfl)
    (by
      have h := tabSimSpg hP (j + 1) w (UInt64.ofNat bs.nP) (UInt64.ofNat nF) (UInt64.ofNat so')
        (UInt64.ofNat sl') sorts hwl
        (by rw [UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnFb]; exact hb) hS hM
        (by rw [hso', hsl']; exact hsorts.1)
        (by rcases hsorts.2 with h | h
            · left; rw [h]; rfl
            · right; rw [hso', hsl']; exact h)
      rw [hwd, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnFb] at h
      exact sctSim_withRun (Sim.withFr (F := fun m1 => AFr m m1) h
        fun _ _ e => hkeep _ (by simp [tablesKeepCallees]) _ _ _ _ _ e)) ?_
  rintro rg guards m1 a1 ⟨⟨⟨hS1, hg1, hgd1, hgt1, hM1⟩, ha1⟩, hrun1⟩
  obtain ⟨ps1, -⟩ := ConRon.Bridge.Inductives.structProjGuards_spec cA.type cAP.type bs.nP nF sorts sortsP
    a a1 guards hok hpins ⟨ConRon.Bridge.denoteCV_type hcAP, hsP⟩ hrun1
  rw [ctoK1_some]
  -- `block_shape_lps` (model only)
  refine Sim.mstep (K := ctoK2 p (j + 2) pp ms (UInt64.ofNat cvp) (UInt64.ofNat nF) vis rg) rfl
    (fun _ _ => rfl) fun rl m2 h2 => ?_
  obtain ⟨s2, rfl, -, hW2, -⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (blockShapeLps_spec2 p hP.tbl.ha hP.erCopy hP.erToIw hP.lps (j + 2) _ pp) h2
  obtain ⟨hS2, hg2, hl2, hlb2⟩ := lpsW_ok' hW2 hS1 (hq.grow (decBS_mono _) hg1)
  have hM2 : HbMemo s2.mem := hM1.fr (lpsW_mfrT hW2)
  have hA2 : AbsOK s2.mem := lpsW_afr hW2 (ha1 hA)
  have hg12 := hg1.trans hg2
  -- `check_struct_proj_table`
  rw [ctoK2_some]
  obtain ⟨hnpw2, -, hrs2, hrse2⟩ := partsShapeWords hg12 hq hq9
  have hms2 : rdW (s2.mem.arr64 IW) ms = UInt64.ofNat cvm := by
    rw [partsRdIW_grow hg12 (by have := partsIwLt hcvm; omega)]; exact hw6
  obtain ⟨hT32, hTn⟩ := partsCVName hg12 hcvT hcvmb
  obtain ⟨hC32, hCn⟩ := partsCVName hg12 hcv hcvb
  rw [hnpw2, hms2]
  refine Sim.post (K := ctoK3) rfl (fun _ _ => rfl)
    (Q := fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow s2.mem m' ∧ MFr [] [] s2.mem m' ∧ AbsOK m' ∧
      ConRon.Bridge.Inductives.PStep a1 a')
    (fun r m' e => by
      obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
        (tblW_spec p hP.tbl (realCall p) (realCall_spec p) j _ (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvm))
          (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvp)) (rl.headD 0) (rl.tail.headD 0) (UInt64.ofNat bs.nP)
          (UInt64.ofNat nF) (rdW (s2.mem.arr64 IW) (pp + 6)) (rg.headD 0) (rg.tail.headD 0)
          (UInt64.ofNat cvp) vis) e
      have h := tblW_okR (dn := dn) (vis := vis) (fe := fe) p hP.tbl hp j s2.mem a1
        (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvm)) (rdW (s2.mem.arr64 EREC) (UInt64.ofNat cvp))
        (rl.headD 0) (rl.tail.headD 0) (UInt64.ofNat bs.nP) (UInt64.ofNat nF) (rdW (s2.mem.arr64 IW) (pp + 6))
        (rg.headD 0) (rg.tail.headD 0)
        (UInt64.ofNat cvp) bs.lps guards cA hS2 hT32 hC32 hrs2
        (by rw [UInt64.toNat_ofNat_of_lt' hnpb]; omega) hl2 hlb2
        (by rw [decHL_grow hg2 (Nat.le_of_eq hgt1)]; exact hgd1) (by rw [hgt1]; exact hg2.1)
        (by rw [UInt64.toNat_ofNat_of_lt' hcvb]; exact DecB.grow (OMono.decCVp _) hg12 hcv) hA2 ps1.ok
        (names_ext ps1.ext ⟨pP.lps, denoteNList_mapM (ConRon.Bridge.Inductives.BlockShape.lps_spec hsh)⟩)
        (TP := mP.cvT.name) (by
          rw [hTn]
          exact ConRon.Bridge.denoteN_ext
            (ConRon.Bridge.denoteCV_name (ConRon.Bridge.Inductives.dMember_inv hmP).1) ps1.ext)
        (ConRon.Bridge.denoteCV_type (ConRon.Bridge.denoteCV_ext hcAP ps1.ext))
      rw [hTn, hCn, hrse2, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnFb] at h
      exact h r s3.mem hW3)
    fun r x m3 a3 h => ⟨h.1, hg12.trans h.2.1, hM2.fr h.2.2.1, h.2.2.2.1, ps1.trans h.2.2.2.2⟩

/-- **`check_block_tables`' model refines `checkBlockTables`** (`ctbW_sim`, the tables through the
real `all_level_params_defined`: `ctoW_simR`), from the twin's `StateOK`, `PinsOK` and the shape's,
the members', the constructors' and their sorts' readings (each member's install a `PStep`, so they
hold at the next); the twin's run is a `PStep`. -/
theorem ctbW_simR {p : Prog} (hP : TabsProg p) (hp : ApdF p) (dn : NIdx → Option ConLeche.Name) (pp : Word) (bs : BlockShape)
    (n : Nat) :
    ∀ (m : Mem) (a : AState) (vis : Word) (fe : IFEnv) (mo ml co cl so sl : Word) (mss : List MemberShape)
      (css : List (List (IConstantVal × Nat))) (sss : List (List (List LIdx))),
    StageR dn vis fe m a → DecB (fun m => decBS m pp.toNat) m bs →
    ShapeSrc m pp → PSlR decMS mss mo ml m → PSlR decCNS css co cl m → PSlR decISS sss so sl m → HbMemo m →
    AbsOK m → (∀ f ∈ tablesKeepCallees, AbsKeep p f) →
    ConRon.Bridge.StateOK a → ConRon.Bridge.PinsOK a →
    (∃ pP, ConRon.Bridge.Inductives.dShape a.store bs = some pP) →
    (∃ msP, mss.mapM (ConRon.Bridge.Inductives.dMember a.store) = some msP) →
    (∃ cssP, css.mapM (ConRon.Bridge.Inductives.dCtors a.store) = some cssP) →
    (∃ sssP, sss.mapM (ConRon.Bridge.Inductives.denoteLLists a.store) = some sssP) →
    Sim (ctbW p n m pp mo ml co cl so sl vis) (ConRon.Arena.checkBlockTables bs mss css sss fe) a
      (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m' ∧ HbMemo m' ∧ AbsOK m' ∧
        ConRon.Bridge.Inductives.PStep a a') := by
  induction n with
  | zero => intros; rw [ctbW_zero]; exact Sim.of_none
  | succ n ih =>
  intro m a vis fe mo ml co cl so sl mss css sss hS hq hsrc hmss hcss hsss hM hA hkeep hok hpins
    ⟨pP, hsh⟩ ⟨msP, hmsP⟩ ⟨cssP, hcsP⟩ ⟨sssP, hssP⟩
  by_cases hml : ml = 0
  · subst hml
    rw [ctbW_nil1 p n m pp mo 0 co cl so sl vis rfl, cbt_nil bs mss css sss fe (.inl (partsPSl_nil hmss))]
    exact Sim.ret ⟨hS, IWGrow.refl m, hM, hA, ConRon.Bridge.Inductives.PStep.refl hok⟩
  by_cases hcl : cl = 0
  · subst hcl
    rw [ctbW_nil2 p n m pp mo ml co 0 so sl vis hml rfl,
      cbt_nil bs mss css sss fe (.inr (.inl (partsPSl_nil hcss)))]
    exact Sim.ret ⟨hS, IWGrow.refl m, hM, hA, ConRon.Bridge.Inductives.PStep.refl hok⟩
  by_cases hsl : sl = 0
  · subst hsl
    rw [ctbW_nil3 p n m pp mo ml co cl so 0 vis hml hcl rfl,
      cbt_nil bs mss css sss fe (.inr (.inr (partsPSl_nil hsss)))]
    exact Sim.ret ⟨hS, IWGrow.refl m, hM, hA, ConRon.Bridge.Inductives.PStep.refl hok⟩
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨msp, msh, rest, rfl, hwm, hmsb, hdm, hrest⟩ := partsPSl_cons hmss hml
  obtain ⟨csp, cs, css', rfl, hwc, hcsb, hdc, hcss'⟩ := partsPSl_cons hcss hcl
  obtain ⟨ssp, ss, sss', rfl, hws, hssb, hds, hsss'⟩ := partsPSl_cons hsss hsl
  obtain ⟨mP, msP', -, hmP, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmsP
  obtain ⟨csP, cssP', -, hcsy, hcssP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcsP
  obtain ⟨ssP, sssP', -, hssy, hsssP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hssP
  have hmsp' : (UInt64.ofNat msp : Word).toNat = msp := UInt64.toNat_ofNat_of_lt' hmsb
  have hcsp' : (UInt64.ofNat csp : Word).toNat = csp := UInt64.toNat_ofNat_of_lt' hcsb
  have hssp' : (UInt64.ofNat ssp : Word).toNat = ssp := UInt64.toNat_ofNat_of_lt' hssb
  -- the member's constructors `[off, len]`
  obtain ⟨o1, l1, ho1, hl1, hd1, hb1⟩ := partsAt decCN_mono
    (show decAt (truncM m) (decPL (truncM m) (decCN (truncM m))) csp = some cs from hdc)
  have hlt1 := partsIwLt hl1
  obtain ⟨hwo1, -, -⟩ := partsIwRd ho1 hcsp'
  obtain ⟨hwl1, -, -⟩ := partsIwRd hl1 (w := UInt64.ofNat csp + 1)
    (by rw [UInt64.toNat_add, hcsp']; simp; omega)
  rw [ofNat_toNat_word] at hwo1 hwl1
  have hlen1 : cs.length = l1.toNat := decPL_length _ hd1
  -- the member's sorts `[off, len]`
  obtain ⟨o2, l2, ho2, hl2, hd2, hb2⟩ := partsAt decIS_mono
    (show decAt (truncM m) (fun o l => decPL (truncM m) (decIS (truncM m)) o l) ssp = some ss from hds)
  have hlt2 := partsIwLt hl2
  obtain ⟨hwo2, -, -⟩ := partsIwRd ho2 hssp'
  obtain ⟨hwl2, -, -⟩ := partsIwRd hl2 (w := UInt64.ofNat ssp + 1)
    (by rw [UInt64.toNat_add, hssp']; simp; omega)
  rw [ofNat_toNat_word] at hwo2 hwl2
  have hlen2 : ss.length = l2.toNat := decPL_length _ hd2
  -- the member's index count
  obtain ⟨-, hni, -⟩ := decMS_some (show decMS (truncM m) msp = some msh from hdm)
  have hlt3 := partsIwLt hni
  obtain ⟨hwn, hnib, -⟩ := partsIwRd hni (w := UInt64.ofNat msp + 1)
    (by rw [UInt64.toNat_add, hmsp']; simp; omega)
  have hni0 : (UInt64.ofNat msh.nIdx : Word) = 0 ↔ msh.nIdx = 0 := by
    constructor
    · intro e; have := congrArg UInt64.toNat e; rwa [UInt64.toNat_ofNat_of_lt' hnib] at this
    · intro e; rw [e]; rfl
  have hw1 : ∀ w : Word, w = 1 ↔ w.toNat = 1 := fun w =>
    ⟨fun e => by rw [e]; rfl, fun e => UInt64.toNat_inj.mp (by rw [e]; rfl)⟩
  by_cases hc : l1 = 1 ∧ l2 = 1 ∧ msh.nIdx = 0
  · obtain ⟨e1, e2, e3⟩ := hc
    subst e1 e2
    obtain ⟨⟨cA, nF⟩, rfl⟩ := List.length_eq_one_iff.mp (show cs.length = 1 by rw [hlen1]; rfl)
    obtain ⟨sorts, rfl⟩ := List.length_eq_one_iff.mp (show ss.length = 1 by rw [hlen2]; rfl)
    obtain ⟨cAP', -, -, hcA1, -⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcsy
    obtain ⟨cAP, hcAP, -⟩ := Option.map_eq_some_iff.mp hcA1
    obtain ⟨sortsP, -, -, hsP, -⟩ := ConRon.Bridge.Inductives.BT.denoteLLists_cons_inv hssy
    rw [ctbW_one p n m pp mo ml co cl so sl vis hml hcl hsl (by rw [hwc, hwl1]) (by rw [hws, hwl2])
      (by rw [hwm, hwn, (hni0).mpr e3]), cbt_one bs msh rest css' sss' fe cA nF sorts e3, hwm, hwc, hws, hwo1, hwo2]
    have hcall : Sim (callW p n "check_block_tables_one" [pp, UInt64.ofNat msp, o1, o2, vis] m)
        (tabOne fe bs msh cA nF sorts) a
        (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m' ∧ HbMemo m' ∧ AbsOK m' ∧
          ConRon.Bridge.Inductives.PStep a a') := by
      cases n with
      | zero => rw [callW_zero]; exact Sim.of_none
      | succ k =>
        intro r m' e
        obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
          (cto_spec p hP.one k _ pp (UInt64.ofNat msp) o1 o2 vis) e
        exact ctoW_simR hP hp k hS hq hsrc (by rw [hmsp']; exact hdm)
          ⟨hd1, hb1.resolve_left (by decide)⟩ ⟨hd2, hb2.resolve_left (by decide)⟩ hM hA hkeep hok hpins
          hsh hmP hcAP hsP r s'.mem hW
    refine Sim.bindK (K := ctbK1 p n pp mo ml co cl so sl) (by simp [ctbK1.eq_def])
      (fun r m1 => ctbK1_some p n m1 pp mo ml co cl so sl r) hcall ?_
    rintro r fe₂ m1 a1 ⟨hS1, hg1, hM1, hA1, ps1⟩
    exact Sim.post (K := ctbK2) rfl (fun _ _ => rfl)
      (ih m1 a1 (r.headD 0) fe₂ (mo + 1) (ml - 1) (co + 1) (cl - 1) (so + 1) (sl - 1) rest css' sss'
        hS1 (hq.grow (decBS_mono _) hg1) (partsHsrc_grow hg1 hq9 hsrc) (hrest.grow decMS_mono hg1)
        (hcss'.grow decCNS_mono hg1) (hsss'.grow decISS_mono hg1) hM1 hA1 hkeep ps1.ok
        (hpins.mono ps1.ext ps1.pins) ⟨pP, ConRon.Bridge.Inductives.dShape_ext ps1.ext _ _ hsh⟩
        ⟨msP', ConRon.Bridge.Inductives.dMember_ext.list ps1.ext _ _ hrestP⟩
        ⟨cssP', ConRon.Bridge.Inductives.dCtors_ext.list ps1.ext _ _ hcssP'⟩
        ⟨sssP', ConRon.Bridge.Inductives.DExt.list
          (d := ConRon.Bridge.Inductives.denoteLLists)
          (fun hx x y h => ConRon.Bridge.Inductives.BI.denoteLLists_ext hx x y h) ps1.ext _ _ hsssP'⟩)
      (fun r x m a ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, hg1.trans h2, h3, h4, ps1.trans h5⟩)
  · rw [ctbW_skip p n m pp mo ml co cl so sl vis hml hcl hsl (by
        rw [hwc, hwl1, hws, hwl2, hwm, hwn, hni0]; exact hc),
      cbt_skip bs msh rest cs css' ss sss' fe (by
        rw [hlen1, hlen2, ← hw1, ← hw1]; exact hc)]
    exact Sim.post (K := ctbK2) rfl (fun _ _ => rfl)
      (ih m a vis fe (mo + 1) (ml - 1) (co + 1) (cl - 1) (so + 1) (sl - 1) rest css' sss'
        hS hq hsrc hrest hcss' hsss' hM hA hkeep hok hpins ⟨pP, hsh⟩ ⟨msP', hrestP⟩ ⟨cssP', hcssP'⟩
        ⟨sssP', hsssP'⟩)
      (fun r x m a ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩)

end L.Ind
