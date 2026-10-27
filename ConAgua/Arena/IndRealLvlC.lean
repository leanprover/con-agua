import ConAgua.Arena.IndRealLvlT
import ConAgua.Arena.IndT.Lift
import ConRon.Bridge.Inductives.RecCheck

/-!
# The level callees under `StageC` (lane `indproofs4`, helper `lvl`)

The `StageT` sims of `lvl_eq_c`, `lvls_eq_c` (`IndRealLvlT.lean`) and `lv_zero_caps`
(`IndRealLvlZT.lean`) lifted to lane `indstaget`'s `StageC` (`IndT/Lift.lean`): con-ron's frame
lemmas make the twin's run a `PStep` (`lvlEq?_pstep`, `readLevelM_pstep`) or a `CoreStep`
(`RC.lvlsEq?_run`, which also names the verdict); `lv_leq_top`'s from `IndTwin.lvLeqTop_simT`'s proof, and `AbsOK` is carried across the call (the
core's write set, `absOK_core`; `lv_zero_caps`' own, `lzcF_frame`). For the `StageC` proofs that
read these calls through the stub contracts (`IndT/RecCheckTcm.lean`'s `lvlsEqStub_spec`).
-/


open ConRon.Arena

namespace L.Ind

open L.Arena

section
variable (p : Prog) (hcl : CoreStageClosed p) (hL : LvlCacheProg p)
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

include hcl hL in
/-- **`lvl_eq_c` under `StageC`** (replaces `IndStubs.lvlEqStub_spec` for a caller carrying
`StageC`, `AbsOK` and the two handles' readbacks). -/
theorem lvlEqC_simC (n : Nat) {m : Mem} {a : AState} (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (u v : Word) (hu : H u) (hv : H v) (lu lv : ConLeche.Level)
    (hdu : denoteL a.store.ls (decI u) = some lu) (hdv : denoteL a.store.ls (decI v) = some lv) :
    Sim (callW p n "lvl_eq_c" [u, v] m) (lvlEq? (decI u) (decI v)) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ decLvlEq m' r x ∧ AbsOK m' ∧
        ConRon.Bridge.Inductives.PStep a a') := by
  intro r m' e
  obtain ⟨x, a', hrun, hT', hg, hd⟩ :=
    lvlEqC_simTE p hcl hL n hC.stageT u v hu hv lu lv hdu hdv r m' e
  have hA' := absOK_core hcl (by decide) e hA hT'
  have hs := ConRon.Bridge.Inductives.lvlEq?_pstep hC.check.state hrun
  exact ⟨x, a', hrun, StageC.of_pstep hC hT'.stage hA' hs, hg, hd, hA', hs⟩

include hcl hL in
/-- **`lvls_eq_c` under `StageC`** (replaces `RecCheckSpec12.lvlsEqStub_spec` for a caller
carrying `StageC`, `AbsOK` and the two lists' readbacks): the verdict con-leche's
`isEquivList`. -/
theorem lvlsEqC_simC (n : Nat) {m : Mem} {a : AState} (hC : StageC dn vis fe env m a)
    (hA : AbsOK m) (us vs : Word) (hu : H us) (hv : H vs) {usP vsP : List ConLeche.Level}
    (husP : denoteLs a.store.lss (decI us) = some usP)
    (hvsP : denoteLs a.store.lss (decI vs) = some vsP) :
    Sim (callW p n "lvls_eq_c" [us, vs] m) (lvlsEq? (decI us) (decI vs)) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ decLvlEq m' r x ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep .verified env fe a a' ∧ x = ConLeche.Level.isEquivList usP vsP) := by
  intro r m' e
  obtain ⟨x, a', hrun, hT', hg, hd⟩ := lvlsEqC_simT p hcl hL n hC.stageT us vs hu hv r m' e
  have hA' := absOK_core hcl (by decide) e hA hT'
  obtain ⟨c, hx⟩ := ConRon.Bridge.Inductives.RC.lvlsEq?_run hC.check husP hvsP hrun
  exact ⟨x, a', hrun, StageC.of_check hC hT'.stage hA' c.ok c.ext, hg, hd, hA', c, hx⟩

end

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

/-- **`lv_leq_top` under `StageC`** (replaces `IndStubs.lvLeqTopStub_spec` for a caller carrying
`StageC`, `AbsOK` and the two handles' readbacks): `IndTwin.lvLeqTop_simT`'s proof with the twin's
two readbacks as `PStep`s and the level heap's frame for `AbsOK`. -/
theorem lvLeqTop_simC (p : Prog) (hL : LevelProg p) (hpt : p.lookup "lv_leq_top" = some lvLeqTop)
    (n : Nat) {m : Mem} {a : AState} (hC : StageC dn vis fe env m a) (hA : AbsOK m) (u v : Word)
    (hu : H u) (hv : H v) (lu lv : ConLeche.Level) (hdu : denoteL a.store.ls (decI u) = some lu)
    (hdv : denoteL a.store.ls (decI v) = some lv) :
    Sim (callW p n "lv_leq_top" [u, v] m) (leqTopAM (decI u) (decI v)) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ decLvlEq m' r x ∧ AbsOK m' ∧
        ConRon.Bridge.Inductives.PStep a a' ∧ x = ConLeche.Level.leq lu lv) := by
  intro r m' e
  have hS := hC.stageT
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lvLeqTop_spec p hL hpt n _ u v) e
  obtain ⟨M, hCo⟩ := hS.core
  have hlu := denoteL_lvR hCo.arena.1 (decI u) lu hdu
  have hlv := denoteL_lvR hCo.arena.1 (decI v) lv hdv
  rw [word_decI _ _ hu |>.mpr rfl] at hlu
  rw [word_decI _ _ hv |>.mpr rfl] at hlv
  obtain ⟨hx, hz⟩ := leqTopW_ok (nameN_rel _ hCo.nwf) n _ _ _ _ _ _ _ hlu hlv hW
  obtain ⟨X1, h1, hc1⟩ := readLevelM_run' a (decI u) lu hdu hCo.readL
  obtain ⟨X2, h2, hc2⟩ := readLevelM_run' { a with caches := { a.caches with readLC := X1 } } (decI v)
    lv hdv hc1
  have hC1 := hCo.withReadLC X1 hc1
  have hC2 := hC1.withReadLC X2 hc2
  obtain ⟨hT', hg⟩ := StageT.of_heap hS hC2 hx.memFrame
  have hA' := hA.frameD hx.memFrame (by decide) (by decide)
  have hs1 := ConRon.Bridge.Inductives.readLevelM_pstep hC.check.state h1
  have hs2 := ConRon.Bridge.Inductives.readLevelM_pstep hs1.ok h2
  have hs := hs1.trans hs2
  refine ⟨ConLeche.Level.leq lu lv, _, ?_, StageC.of_pstep hC hT'.stage hA' hs, hg, ?_, hA', hs, rfl⟩
  · simp only [leqTopAM, StateT.run_bind, h1, except_ok_bind, h2]; rfl
  · show r.headD 0 = _
    rw [hz]; cases ConLeche.Level.leq lu lv with
    | none => rfl
    | some b => cases b <;> rfl

end

end L.Ind
