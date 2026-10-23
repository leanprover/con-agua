import ConAgua.Arena.IndT.Base
import ConAgua.Arena.StageC
import ConAgua.Arena.IndRealAbs
import ConRon.Bridge.Inductives.Rel

/-!
# Lifting stage facts to `StageC` by con-ron's specs (lane `indstaget`)

`StageC dn vis fe env m a` (`TwinStep.lean`) is `StageR` with con-ron's `CheckOK .verified env fe a`,
the memory's half of `TwinOK` (`TwinMem`) and the pin flag. A stage theorem proved under `StageR`
for a callee that calls no core entry point lifts to `StageC` by con-ron's spec of the twin
(`PSpec`/`PSpecP`/`PSpecL`, `Bridge/Inductives/Run.lean`: from `StateOK` and the inputs'
denotations, the twin's run is a `PStep`, which with `CheckOK` before is a `CoreStep`) and the
L run's memory facts (`AbsOK` after: its `WkOK` and the two core walk memos it holds).
-/

set_option linter.deprecated false

open ConRon.Arena
open ConRon.Bridge.Inductives (PStep PSpec PSpecP PSpecL CSpec)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section lift
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

/-- **`StageC` across a twin step con-ron calls a `PStep`**: the stage relation after it, the
memory's half (`AbsOK` after: `WkOK` and the two core walk memos it holds). -/
theorem StageC.of_pstep {m m' : Mem} {a a' : AState} (h : StageC dn vis fe env m a)
    (hS : StageR dn vis fe m' a') (hA : AbsOK m') (hs : PStep a a') :
    StageC dn vis fe env m' a' :=
  ⟨hS, (hs.toCore h.check).ok,
    ⟨hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.1, ⟨hA.2.2.2.1, hA.1, hA.2.2.2.2.1⟩,
      fun k x e => hs.ext.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    hA.2.2.2.2.2.2.2.2⟩

/-- **A `StageR` `RSim` of a core-free callee is a `StageC` `RSim`**, by con-ron's `PSpec` of the
twin at the inputs' denotation `P`; the post `Q` gives the stage relation and `AbsOK` after. -/
theorem RSim.liftP {β α : Type} {o : Option (β × Mem)} {op : AM α} {m : Mem} {a : AState}
    {Q : β × Mem → AState → α → Prop} {P : EStore → Prop} {R : EStore → α → Prop}
    (hC : StageC dn vis fe env m a) (h : RSim o op a Q)
    (hq : ∀ b a' x, Q b a' x → StageR dn vis fe b.2 a' ∧ AbsOK b.2)
    (hsp : PSpec P op R) (hP : P a.store) :
    RSim o op a (fun b a' x => StageC dn vis fe env b.2 a' ∧ Q b a' x ∧ R a'.store x ∧
      PStep a a') := by
  intro b hb
  obtain ⟨x, a', hr, hq'⟩ := h b hb
  obtain ⟨hs, hR⟩ := hsp a a' x hC.check.state hP hr
  exact ⟨x, a', hr, hC.of_pstep (hq _ _ _ hq').1 (hq _ _ _ hq').2 hs, hq', hR, hs⟩

/-- `RSim.liftP` for a `PSpecP` (the twin reads the pins). -/
theorem RSim.liftPP {β α : Type} {o : Option (β × Mem)} {op : AM α} {m : Mem} {a : AState}
    {Q : β × Mem → AState → α → Prop} {P : EStore → Prop} {R : EStore → α → Prop}
    (hC : StageC dn vis fe env m a) (h : RSim o op a Q)
    (hq : ∀ b a' x, Q b a' x → StageR dn vis fe b.2 a' ∧ AbsOK b.2)
    (hsp : PSpecP P op R) (hP : P a.store) :
    RSim o op a (fun b a' x => StageC dn vis fe env b.2 a' ∧ Q b a' x ∧ R a'.store x ∧
      PStep a a') := by
  intro b hb
  obtain ⟨x, a', hr, hq'⟩ := h b hb
  obtain ⟨hs, hR⟩ := hsp a a' x hC.check.state hC.check.pins hP hr
  exact ⟨x, a', hr, hC.of_pstep (hq _ _ _ hq').1 (hq _ _ _ hq').2 hs, hq', hR, hs⟩

/-- `RSim.liftP` for a `PSpecL` (the twin reads levels back through the cache). -/
theorem RSim.liftPL {β α : Type} {o : Option (β × Mem)} {op : AM α} {m : Mem} {a : AState}
    {Q : β × Mem → AState → α → Prop} {P : EStore → Prop} {R : EStore → α → Prop}
    (hC : StageC dn vis fe env m a) (h : RSim o op a Q)
    (hq : ∀ b a' x, Q b a' x → StageR dn vis fe b.2 a' ∧ AbsOK b.2)
    (hsp : PSpecL P op R) (hP : P a.store) :
    RSim o op a (fun b a' x => StageC dn vis fe env b.2 a' ∧ Q b a' x ∧ R a'.store x ∧
      PStep a a') := by
  intro b hb
  obtain ⟨x, a', hr, hq'⟩ := h b hb
  obtain ⟨hs, hR⟩ := hsp a a' x hC.check.state hC.check.caches.readL hP hr
  exact ⟨x, a', hr, hC.of_pstep (hq _ _ _ hq').1 (hq _ _ _ hq').2 hs, hq', hR, hs⟩

/-- **A `StageT` `RSim` of a core-calling callee is a `StageC` `RSim`**, by con-ron's `CSpec` of
the twin (`CheckOK` after, from its `CoreStep`). -/
theorem RSim.liftC {β α : Type} {o : Option (β × Mem)} {op : AM α} {m : Mem} {a : AState}
    {Q : β × Mem → AState → α → Prop} {P : EStore → Prop} {R : EStore → α → Prop}
    (hC : StageC dn vis fe env m a)
    (h : RSim o op a (fun b a' x => StageT dn vis fe b.2 a' ∧ Q b a' x))
    (hsp : CSpec V env fe P op R) (hP : P a.store) :
    RSim o op a (fun b a' x => StageC dn vis fe env b.2 a' ∧ Q b a' x ∧ R a'.store x ∧
      ConRon.Bridge.CoreStep V env fe a a') := by
  intro b hb
  obtain ⟨x, a', hr, hT, hq⟩ := h b hb
  obtain ⟨hs, hR⟩ := hsp a a' x hC.check hP hr
  exact ⟨x, a', hr, StageC.of_T hT hs.ok, hq, hR, hs⟩

end lift

end L.Ind
