module

import ConAgua.Arena.IndRealLvlT
import ConAgua.Arena.IndT.Lift
import ConRon.Bridge.Inductives.RecCheck
import ConAgua.Arena.IndRealAbs
import ConAgua.Arena.IndT.Base
public import ConAgua.Arena.TwinStep
public import ConRon.Bridge.Checker.Hyp
public import ConRon.Bridge.Inductives.Run

@[expose] public section

/-!
# The level callees under `StageC` (lane `indproofs4`, helper `lvl`)

The `StageT` sims of `lvl_eq_c`, `lvls_eq_c` (`IndRealLvlT.lean`) and `lv_zero_caps`
(`IndRealLvlZT.lean`) lifted to lane `indstaget`'s `StageC` (`IndT/Lift.lean`): con-ron's frame
lemmas make the twin's run a `PStep` (`lvlEq?_pstep`, `readLevelM_pstep`) or a `CoreStep`
(`RC.lvlsEq?_run`, which also names the verdict); `lv_leq_top`'s from `IndTwin.lvLeqTop_simT`'s proof, and `AbsOK` is carried across the call (the
core's write set, `absOK_core`; `lv_zero_caps`' own, `lzcF_frame`). For the `StageC` proofs that
read these calls through the stub contracts (`tcm_ref`, `Verdict/IndBTcm.lean`).
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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
include hcl hL in
/-- **`lvls_eq_c` under `StageC`** (replaces `RecCheckSpec/TcmLook.lvlsEqStub_spec` for a caller
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
-/

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
  sorry

end

end L.Ind
