module

public import ConAgua.Arena.IotaFrameAt
public import ConAgua.Arena.StageTLift
public import ConAgua.Arena.TwinStep
public import ConRon.Bridge.Inductives.Run
import ConRon.Bridge.Inductives.Rel
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Pers
import ConRon.Bridge.Checker.Inv
import ConRon.Bridge.Checker.Canon
import ConAgua.Arena.RecLayout.CIDec
import ConAgua.Arena.RecCheckSpec.ErToIwWStage
import ConAgua.Arena.IlpRd

@[expose] public section

/-!
# The ι reading rule, part 1: the twin steps of `iota_parts_at`'s interning callees (lane ronsync8)

`ctorLevelsAt` and `iotaParamsAt` intern (level lists, bound variables): each is a `PStep` of
the twin state (con-ron's `Bridge/Inductives/Run.lean` frame: the store grown, the read-back
caches' invariants kept, the pins unchanged), so `TwinOK` survives them (`TwinOK.of_pstep`) and
`iota_parts_at` can call the core walk `inst_lp_fast` under `StageT` after them.
-/

open ConRon.Arena

/-- **`TwinOK` across a twin `PStep`** (`TwinOK.of_grow` with the caches' frame `CacheFrame`
for the cache equation): the memory is unchanged. -/
theorem L.Arena.TwinOK.of_pstep {dn : NIdx → Option ConLeche.Name} {m : L.Mem} {a a' : AState}
    {fe : IFEnv} (h : L.Arena.TwinOK dn m a fe) (hp : ConRon.Bridge.Inductives.PStep a a') :
    L.Arena.TwinOK dn m a' fe := by
  obtain ⟨rk, hw⟩ := hp.ok.wf
  have hx := hp.ext
  have hLs : LsStoreWF a'.store.lss := hw.lss
  have hL : LStoreWF a'.store.ls := hLs.ls
  have hN : ∀ i n, denoteN a.store.ns i = some n → denoteN a'.store.ns i = some n :=
    hx.lss.ls.ns
  have hNs : ∀ (l : List NIdx) ks, l.mapM (denoteN a.store.ns) = some ks →
      l.mapM (denoteN a'.store.ns) = some ks := by
    intro l; induction l with
    | nil => intro ks h; simpa using h
    | cons x xs ih =>
      intro ks h
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h ⊢
      obtain ⟨y, hy, ys, hys, rfl⟩ := h
      exact ⟨y, hN _ _ hy, ys, ih _ hys, rfl⟩
  have hLv : ∀ u l, denoteL a.store.ls u = some l → denoteL a'.store.ls u = some l :=
    hx.lss.ls.lvl
  refine ⟨hp.cframe.readL h.readL, hp.cframe.readLs h.readLs, hw.nsWF, h.erec, h.spn, h.memos,
    h.bstk, ?_⟩
  refine ⟨fun x u hv => ?_, fun x c us hv => ?_, ?_, ?_, hp.cframe.readN h.den.readN,
    fun c ci hf => ?_, fun c tbl hf => ?_, fun u hu => L.Arena.denoteL_of_viewW hL hu,
    fun us hus => ?_, fun k x e => hN _ _ (h.den.dnN k x e),
    fun c cv mI rP isK rules hf r hr lvls pins hfi u hu => ?_,
    fun c cv mI rP isK rules hf r hr lvls hfi u hu => ?_⟩
  · exact L.Arena.denoteL_of_viewW hL (hw.lchildOK x _ hv u (by simp [ENodeView.lchildren])).1
  · have hs := (hw.lschildOK x _ hv us (by simp [ENodeView.lschildren])).1
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨xs, hxs⟩ := L.Arena.denoteLs_of_viewW hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · rw [hp.pins]; exact hLv _ _ h.den.zero
  · obtain ⟨l, hl⟩ := h.den.emptyLs; exact ⟨l, by rw [hp.pins]; exact hx.lss.lst _ _ hl⟩
  · obtain ⟨ks, hks⟩ := h.den.constLps c ci hf; exact ⟨ks, hNs _ _ hks⟩
  · obtain ⟨ks, hks⟩ := h.den.proj c tbl hf; exact ⟨ks, hNs _ _ hks⟩
  · obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hus
    obtain ⟨xs, hxs⟩ := L.Arena.denoteLs_of_viewW hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · obtain ⟨L, hL'⟩ := h.den.recRules c cv mI rP isK rules hf r hr lvls pins hfi u hu
    exact ⟨L, hLv _ _ hL'⟩
  · obtain ⟨L, hL'⟩ := h.den.recLevels c cv mI rP isK rules hf r hr lvls hfi u hu
    exact ⟨L, hLv _ _ hL'⟩

namespace L.Ind

open L.Arena
open Std.WP
open ConRon.Bridge ConRon.Bridge.Inductives

/-! ## The twin steps -/

/-- **`ctorLevelsAt` is a `PStep`** (upstream `ctorLevelsAt_run`'s frame half, from `StateOK`). -/
theorem ctorLevelsAt_pstep {s s' : AState} {rl : IRecRule} {fP : ConLeche.RecRuleFire}
    {lps : List NIdx} {lpsP : List ConLeche.Name} {r : LsIdx} (hok : StateOK s)
    (hf : ConRon.Arena.Frontend.denoteFire s.store rl.fire = some fP)
    (hlps : ConRon.Arena.Frontend.denoteNList s.store.ns lps = some lpsP)
    (hrun : ctorLevelsAt rl lps s = .ok (r, s')) : PStep s s' := by
  simp only [ctorLevelsAt] at hrun
  cases hfr : rl.fire with
  | plain =>
    rw [hfr] at hrun
    obtain ⟨p, -⟩ := paramLevels_run hok hlps hrun
    exact PStep.of_caches p.ok p.ext p.caches p.pins
  | nested lvls pins =>
    rw [hfr] at hrun hf
    simp only [ConRon.Arena.Frontend.denoteFire] at hf
    cases h1 : denoteLList s.store.ls lvls with
    | none => rw [h1] at hf; simp at hf
    | some ls => exact (internLsNode_run hok h1 hrun).1
  | levels lvls =>
    rw [hfr] at hrun hf
    simp only [ConRon.Arena.Frontend.denoteFire, Option.map_eq_some_iff] at hf
    obtain ⟨ls, h1, -⟩ := hf
    exact (internLsNode_run hok h1 hrun).1

/-- **`iotaBVars` is a `PStep`** (upstream `iotaBVars_run`'s frame half). -/
theorem iotaBVars_pstep (rP n : Nat) : ∀ (k i : Nat), n - i = k → ∀ {s s' : AState}
    {r : List EIdx}, StateOK s → iotaBVars rP n i s = .ok (r, s') → PStep s s' := by
  intro k
  induction k with
  | zero =>
    intro i hk s s' r hok hrun
    rw [iotaBVars, ite_eq_right (by omega)] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact PStep.refl hok
  | succ k ih =>
    intro i hk s s' r hok hrun
    rw [iotaBVars, ite_eq_left (by omega)] at hrun
    obtain ⟨b, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨p1, -⟩ := internBVarE_run hok k1
    obtain ⟨bs, s₂, k2, z2⟩ := AM.bind_ok z1
    have p2 := ih (i + 1) (by omega) p1.ok k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    exact p1.trans p2

/-- **`iotaParamsAt` is a `PStep`**. -/
theorem iotaParamsAt_pstep {s s' : AState} {rl : IRecRule} {rP cnP : Nat} {r : List EIdx}
    (hok : StateOK s) (hrun : iotaParamsAt rl rP cnP s = .ok (r, s')) : PStep s s' := by
  simp only [iotaParamsAt] at hrun
  cases hfr : rl.fire with
  | nested lvls pins =>
    rw [hfr] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact PStep.refl hok
  | plain => rw [hfr] at hrun; exact iotaBVars_pstep rP _ _ 0 rfl hok hrun
  | levels lvls => rw [hfr] at hrun; exact iotaBVars_pstep rP _ _ 0 rfl hok hrun

/-! ## `StageT` across the interning callees -/

theorem iotaRC_not {x : Word} (hx : memoFreeC [x] = false) : x ∉ iotaRC := fun h => by
  have := (List.mem_filter.mp h).2; simp_all

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`StageT` across a call of a reading function** whose twin op is a `PStep`: the memory
frame (`iotaRFns`' write set) keeps the core memos and the pins. -/
theorem StageT.of_iotaStep {p : Prog} (P : IotaFrameProg p) {f : FnName} (hf : f ∈ iotaRFns)
    {n : Nat} {args r : List Word} {m m' : Mem} {a a' : AState}
    (hc : callW p n f args m = some (r, m')) (hT : StageT dn vis fe m a)
    (hS : StageR vis fe m' a') (hp : PStep a a') : StageT dn vis fe m' a' := by
  have hfr := (run_memFrame P.rclosed hf (run_of_callW hc)).1
  have hP : m'.arr64 PINS = m.arr64 PINS := hfr.arr PINS (by decide) (by decide)
  refine ⟨hS, (L.Arena.TwinOK.frame hfr (by decide)
    ⟨iotaRC_not (by decide), iotaRC_not (by decide)⟩ (by decide)
    ⟨iotaRC_not (by decide), iotaRC_not (by decide), iotaRC_not (by decide)⟩ (by decide)
    ⟨iotaRC_not (by decide), iotaRC_not (by decide), iotaRC_not (by decide)⟩ hT.twin (by decide)
    (iotaRC_not (by decide))).of_pstep hp, by simp only [pinW, hP]; exact hT.flag⟩

end

theorem getD_succ_tailW (r : List Word) (i : Nat) : r.getD (i + 1) 0 = r.tail.getD i 0 := by
  cases r <;> simp

theorem getD_zero_headW (r : List Word) : r.getD 0 0 = r.headD 0 := by
  cases r <;> simp

/-- `decOIPD` reads the first ten words only. -/
theorem decOIPD_ten {m : Mem} {r : List Word} {x : Option (IIotaParts × List EIdx)}
    (h : decOIPD m r x) :
    decOIPD m [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
      r.tail.tail.tail.tail.headD 0, r.tail.tail.tail.tail.tail.headD 0,
      r.tail.tail.tail.tail.tail.tail.headD 0, r.tail.tail.tail.tail.tail.tail.tail.headD 0,
      r.tail.tail.tail.tail.tail.tail.tail.tail.headD 0,
      r.tail.tail.tail.tail.tail.tail.tail.tail.tail.headD 0] x := by
  rcases x with _ | ⟨x, pd⟩
  · exact h
  · simp only [decOIPD, decIPAt, decRL, getD_succ_tailW, getD_zero_headW, List.tail_cons,
      List.headD_cons, Nat.reduceAdd] at h ⊢
    exact h

/-! ## `iota_parts_at` -/

open ConRon.Arena.Frontend in
/-- **`iota_parts_at` refines `iotaPartsAt`** (`IotaFrameIface.iotaPartsAt_rel`'s proof). -/
theorem iotaPartsAt_rel' {p : Prog} (P : IotaFrameProg p) (n : Nat)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (qj cnP mI rP r : Word)
    (cvj : IConstantVal) (rl : IRecRule) :
    RelW (fun m args => callW p n "iota_parts_at" args m) [qj, cnP, mI, rP, r]
      (fun m a => StageT dn vis fe m a ∧ AbsOK m ∧ StateOK a ∧
        decCV (erecP m) qj.toNat = some cvj ∧ decRule (erecP m) r.toNat = some rl ∧
        (∃ c, denoteCV a.store cvj = some c) ∧ (∃ R, denoteRule a.store rl = some R))
      (iotaPartsAt cvj cnP.toNat mI.toNat rP.toNat rl)
      (fun m m' a r x => KeepPost vis fe decOIPD m m' a r x ∧ AbsOK m') := by
  intro m m' a r0 hc ⟨hT, hA, hok, hcv, hrl, ⟨c, hc'⟩, ⟨R, hR⟩⟩
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iotaPartsAt_specW p P.iota_parts_at n _ qj cnP mI rP r) hc
  rcases n with _ | n
  · simp [iotaPartsAtW] at hW
  simp only [iotaPartsAtW] at hW
  by_cases g1 : 4294967296 ≤ cnP ∨ 4294967296 ≤ mI ∨ 4294967296 ≤ rP
  · rw [ite_eq_left g1] at hW; cases hW
  rw [ite_eq_right g1] at hW
  by_cases g2 : 4294967296 ≤ erRd m (r + Rule.nfields)
  · rw [ite_eq_left g2] at hW; cases hW
  rw [ite_eq_right g2] at hW
  -- `cv_lps`
  rcases h1 : callW p n "cv_lps" [qj] m with _ | ⟨q1, m1⟩
  · rw [h1] at hW; simp [iotaPartsAtW.k_cv_lps] at hW
  rw [h1] at hW
  simp only [iotaPartsAtW.k_cv_lps] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (cvLps_spec p (P.strip.get "iw_alloc") P.er_copy P.er_to_iw P.cv_lps n _ qj) h1
  rw [hs1] at hW1
  obtain ⟨hS1, hg1, -, hlp1, hlt1⟩ := cvLpsW_stage hW1 hT.stage hcv
  have hT1 : StageT dn vis fe m1 a := StageT.of_iotaStep P (by decide) h1 hT hS1 (PStep.refl hok)
  have hA1 : AbsOK m1 := iota_afr P (by decide) h1 hA
  have hrl1 := hg1.ext.decRule hrl
  have hcv1 := hg1.ext.decCV hcv
  -- `ctor_levels_at`
  rcases h2 : callW p n "ctor_levels_at" [r, q1.headD 0, q1.tail.headD 0] m1 with _ | ⟨q2, m2⟩
  · rw [h2] at hW; simp [iotaPartsAtW.k_ctor_levels_at] at hW
  rw [h2] at hW
  simp only [iotaPartsAtW.k_ctor_levels_at] at hW
  obtain ⟨lv, a2, hrun2, hS2, hg2, hH2, hd2⟩ := ctorLevelsAt_rel P n vis fe r _ _ rl cvj.levelParams
    m1 m2 a q2 h2 ⟨hS1, hrl1, hlp1, by omega⟩
  obtain ⟨-, hlpD, -⟩ := ConRon.Bridge.denoteCV_inv hc'
  obtain ⟨-, hfD, -, -⟩ := ConRon.Bridge.denoteRule_inv hR
  have hp2 : PStep a a2 := ctorLevelsAt_pstep hok hfD hlpD hrun2
  have hT2 : StageT dn vis fe m2 a2 := StageT.of_iotaStep P (by decide) h2 hT1 hS2 hp2
  have hA2 : AbsOK m2 := iota_afr P (by decide) h2 hA1
  -- `iota_params_at`
  rcases h3 : callW p n "iota_params_at" [r, rP, cnP] m2 with _ | ⟨q3, m3⟩
  · rw [h3] at hW; simp [iotaPartsAtW.k_iota_params_at] at hW
  rw [h3] at hW
  simp only [iotaPartsAtW.k_iota_params_at] at hW
  have hrl2 := hg2.ext.decRule hrl1
  obtain ⟨params, a3, hrun3, hS3, hg3, hd3⟩ :=
    iotaParamsAt_rel P n vis fe r rP cnP rl m2 m3 a2 q3 h3 ⟨hS2, hrl2⟩
  have hp3 : PStep a2 a3 := iotaParamsAt_pstep hp2.ok hrun3
  have hT3 : StageT dn vis fe m3 a3 := StageT.of_iotaStep P (by decide) h3 hT2 hS3 hp3
  have hA3 : AbsOK m3 := iota_afr P (by decide) h3 hA2
  simp only [decRL, Nat.zero_add, L.getD_zero, L.getD_one] at hd3
  obtain ⟨hpar3, hparb3⟩ := hd3
  -- `inst_lp_fast`
  rcases h4 : callW p n "inst_lp_fast"
      [CWF, q1.headD 0, q1.tail.headD 0, q2.headD 0, erRd m3 (qj + CV.type)] m3 with _ | ⟨q4, m4⟩
  · rw [h4] at hW; simp [iotaPartsAtW.k_inst_lp_fast] at hW
  rw [h4] at hW
  simp only [iotaPartsAtW.k_inst_lp_fast] at hW
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (ilpfF_spec p P.ilpf n _ _) h4
  rw [hs4] at hW4
  have hg23 := hg2.trans hg3
  have hcv3 := hg23.ext.decCV hcv1
  obtain ⟨-, -, -, -, hty, htyH⟩ := decCV_rd (erRdOK m3) hcv3
  have hlp3 : decHL m3 (q1.headD 0).toNat (q1.tail.headD 0).toNat = some cvj.levelParams :=
    decHL_grow' hg23 (by omega) hlp1
  obtain ⟨ty, a4, hrun4, ⟨hT4, hg4, hty4⟩, hA4⟩ := ilpfF_okTA (dn := dn) (vis := vis) (fe := fe)
    CWF _ _ _ _ hH2 htyH cvj.levelParams m3 m4 a3 q4 hW4 ⟨hT3, hA3, hlp3⟩
  rw [CWF_eq, ← hty, hd2] at hrun4
  unfold iotaPartsAt
  rw [StateT.run_bind, hrun2, except_ok_bind, StateT.run_bind, hrun3, except_ok_bind,
    StateT.run_bind, hrun4, except_ok_bind]
  -- `strip_pis`
  rcases h5 : callW p n "strip_pis" [cnP, q4.headD 0] m4 with _ | ⟨q5, m5⟩
  · rw [h5] at hW; simp [iotaPartsAtW.k_strip_pis] at hW
  rw [h5] at hW
  simp only [iotaPartsAtW.k_strip_pis] at hW
  have hs5 := stripF_of_callW P.strip h5
  obtain ⟨x5, a5, hrun5, hS5, hg5, hd5⟩ :=
    stripF_pis_ok vis fe _ _ hty4.1 m4 m5 a4 q5 hs5 hT4.stage
  have hA5 : AbsOK m5 := AFr.of_frame (stripF_frame hs5) (by decide) (by decide) hA4
  rw [hty4.2] at hrun5
  rw [StateT.run_bind, hrun5, except_ok_bind]
  have hg15 := hg1.trans (hg23.trans (hg4.trans hg5))
  rcases x5 with _ | ⟨pd, cb⟩
  · simp only [decOLE] at hd5
    rw [ite_eq_left hd5] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨none, a5, rfl, ⟨hS5, hg15, rfl⟩, hA5⟩
  obtain ⟨h51, hpd, hcb⟩ := hd5
  rw [ite_eq_right (by rw [h51]; decide)] at hW
  dsimp only
  simp only [decW0E, headD_drop3] at hcb
  -- `iota_parts_at_body`
  rcases h6 : callW p n "iota_parts_at_body" [cnP, mI, rP, r, q2.headD 0, q3.headD 0,
      q3.tail.headD 0, q5.tail.headD 0, q5.tail.tail.headD 0, q5.tail.tail.tail.headD 0] m5 with
    _ | ⟨q6, m6⟩
  · rw [h6] at hW; simp [iotaPartsAtW.k_iota_parts_at_body] at hW
  rw [h6] at hW
  simp only [iotaPartsAtW.k_iota_parts_at_body] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have hg35 := hg4.trans hg5
  have hrl5 := (hg3.trans hg35).ext.decRule hrl2
  simp only [decRL, L.getD_one, L.getD_two, Nat.reduceAdd] at hpd
  obtain ⟨x6, a6, hrun6, ⟨hS6, hg6, hd6⟩, hA6⟩ := iotaPartsAtBody_rel P n vis fe cnP mI rP r
    (q2.headD 0) (q3.headD 0) (q3.tail.headD 0) (q5.tail.headD 0) (q5.tail.tail.headD 0) _ rl
    params pd hcb.1 m5 _ a5 q6 h6
    ⟨hS5, hA5, hrl5, decHL_grow' hg35 hparb3 hpar3, Nat.le_trans hparb3 hg35.iw, hpd.1, hpd.2, hH2⟩
  rw [hcb.2, hd2] at hrun6
  exact ⟨x6, a6, hrun6, ⟨hS6, hg15.trans hg6, decOIPD_ten hd6⟩, hA6⟩

end L.Ind
