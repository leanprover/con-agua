module

public import ConAgua.Arena.IotaRelRefL
public import ConAgua.Arena.IotaFrameIface
public import ConAgua.Arena.IndT.Lift
import ConRon.Bridge.Checker.Basis

@[expose] public section

/-!
# The ι reading rule, part 2: the driver (lane ronsync8)

`rule_reads`, `rules_read`, `rec_reads`, `recs_read` against the twin's `ruleReads`, `rulesRead`,
`recReads`, `recsRead`. They run at the index `feR` with the block's constants pushed, so the
invariant `RInv` carries the stage at `feR`, con-ron's `CheckOK` at the entry index, con-ron's
`IFEnvOK E feR` (the pushed environment `E`), the walk memos (`AbsOK`) and the record decoder's
names; `RInv.stageT` rebuilds `StageT` at `feR` for `iota_parts_at`.
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

/-! ## `TwinOK` at an index the environment invariant is known for -/

/-- `TwinOK.of_check` with the index's invariant `IFEnvOK E feR` given apart from `CheckOK`. -/
theorem twinOK_of_ienv {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {fe feR : IFEnv}
    {env E : ConLeche.Env} (hok : ConRon.Bridge.CheckOK false env fe a)
    (hi : ConRon.Bridge.IFEnvOK E feR a) (hm : TwinMem dn m a) :
    TwinOK dn m a feR := by
  have hwf := hok.state.wf
  obtain ⟨rk, hw⟩ := hwf
  have hLs : LsStoreWF a.store.lss := hw.lss
  have hL : LStoreWF a.store.ls := hLs.ls
  have hc := hok.caches
  have hp := hok.pins
  refine ⟨hc.readL, hc.readLs, hw.nsWF, hm.erec, hm.spn, hm.memos, hm.bstk, ?_⟩
  refine ⟨fun x u hv => ?_, fun x c us hv => ?_, hp.zeroLevel, ⟨_, hp.emptyLevels⟩, hc.readN,
    fun c ci hf => ?_, fun c tbl hf => ?_, fun u hu => denoteL_of_viewW hL hu,
    fun us hus => ?_, hm.dnN, fun c cv mI rP isK rules hf r hr lvls pins hfi u hu => ?_,
    fun c cv mI rP isK rules hf r hr lvls hfi u hu => ?_⟩
  · exact denoteL_of_viewW hL (hw.lchildOK x _ hv u (by simp [ENodeView.lchildren])).1
  · have hs := (hw.lschildOK x _ hv us (by simp [ENodeView.lschildren])).1
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨xs, hxs⟩ := denoteLs_of_viewW hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · obtain ⟨-, d, -, hd, -⟩ := hi.hit c ci hf
    obtain ⟨y, hy⟩ := denoteCI_cv hd
    exact denoteCV_lps hy
  · obtain ⟨-, pt, -, hpt, -⟩ := hi.tblHit c tbl hf
    obtain ⟨ks, hks⟩ := denoteProjTable_lps hpt
    exact ⟨ks, denoteNList_mapM hks⟩
  · obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hus
    obtain ⟨xs, hxs⟩ := denoteLs_of_viewW hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · obtain ⟨-, d, -, hd, -⟩ := hi.hit c _ hf
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    cases h2 : ConRon.Arena.Frontend.denoteRules a.store rules with
    | none => rw [h2] at hd; split at hd <;> simp_all
    | some ys => exact denoteRules_mem h2 r hr lvls pins hfi u hu
  · obtain ⟨-, d, -, hd, -⟩ := hi.hit c _ hf
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    cases h2 : ConRon.Arena.Frontend.denoteRules a.store rules with
    | none => rw [h2] at hd; split at hd <;> simp_all
    | some ys => exact denoteRules_memL h2 r hr lvls hfi u hu

/-! ## The invariant of the driver -/

/-- **The driver's invariant** at the pushed index `feR` (environment `E`), con-ron's `CheckOK` at
the entry index `fe` (environment `env`). -/
structure RInv (dn : NIdx → Option ConLeche.Name) (vis : Word) (feR : IFEnv) (env : ConLeche.Env)
    (fe : IFEnv) (E : ConLeche.Env) (m : Mem) (a : AState) : Prop where
  stage : StageR vis feR m a
  check : ConRon.Bridge.CheckOK false env fe a
  ienv : ConRon.Bridge.IFEnvOK E feR a
  abs : AbsOK m
  dnN : ∀ (k : NIdx) (x : ConLeche.Name), dn k = some x → denoteN a.store.ns k = some x

section inv
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {feR : IFEnv} {env : ConLeche.Env}
  {fe : IFEnv} {E : ConLeche.Env}

theorem RInv.stageT {m : Mem} {a : AState} (h : RInv dn vis feR env fe E m a) : StageT dn vis feR m a :=
  ⟨h.stage, twinOK_of_ienv h.check h.ienv
    ⟨h.abs.wk.2.1, h.abs.wk.2.2.1, h.abs.wk.2.2.2.1, h.abs.coreMemos, h.dnN⟩, h.abs.wk.2.2.2.2⟩

theorem RInv.step {m m' : Mem} {a a' : AState} (h : RInv dn vis feR env fe E m a)
    (hS : StageR vis feR m' a') (hA : AbsOK m') (hs : ConRon.Bridge.CoreStep env fe a a') :
    RInv dn vis feR env fe E m' a' :=
  ⟨hS, hs.ok, h.ienv.mono hs.ext, hA, fun k x e => hs.ext.lss.ls.ns k x (h.dnN k x e)⟩

end inv

/-! ## Words of a result list -/

theorem irHeadD (r : List Word) : r.headD 0 = r.getD 0 0 := by cases r <;> rfl

theorem irTailGetD (r : List Word) (k : Nat) : r.tail.getD k 0 = r.getD (k + 1) 0 := by
  cases r <;> simp

end L.Ind
