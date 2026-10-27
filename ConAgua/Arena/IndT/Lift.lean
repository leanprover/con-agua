import ConAgua.Arena.IndT.Base
import ConAgua.Arena.StageC
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

/-- **`StageC` after a twin step whose result con-ron's lemmas give `CheckOK` for** (a `CoreStep`,
a flush, …), the store extended. -/
theorem StageC.of_check {m m' : Mem} {a a' : AState} (h : StageC dn vis fe env m a)
    (hS : StageR dn vis fe m' a') (hA : AbsOK m') (hck : ConRon.Bridge.CheckOK V env fe a')
    (hx : ConRon.Arena.Ext a.store a'.store) : StageC dn vis fe env m' a' :=
  ⟨hS, hck,
    ⟨hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.1, ⟨hA.2.2.2.1, hA.1, hA.2.2.2.2.1⟩,
      fun k x e => hx.lss.ls.ns k x (h.mem.dnN k x e)⟩,
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

/-! ## The core's entry points under `StageC`

The knot's `StageT` sims (`Base.lean`) with con-ron's `*_crun` (`Bridge/Inductives/Rel.lean`: from
`CheckOK`, the input's denotation and scoping, the twin's run is a `CoreStep` and its answer
denotes) and `AbsOK` across the call (`absOK_core`). -/

section entriesC
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

open ConRon.Bridge.Inductives (infer_crun ensureSort_crun whnf_crun defeq_crun) in
include hq henv in
/-- `infer_type_core` read through `realCall p` under `StageC`. -/
theorem inferC_rsim (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (dep e : Word) (he : H e) {eP : ConLeche.Expr}
    (hd : denoteE a.store (decI e) = some eP) (hw : ConLeche.Expr.WScoped dep.toNat eP) :
    RSim (realCall p n "infer_type_core" [vis, dep, e] m)
      (inferTypeCore V fe checkFuel dep.toNat (decI e)) a
      (fun b a' x => StageC dn vis fe env b.2 a' ∧ IWGrow m b.2 ∧ decW0E b.2 b.1 x ∧ AbsOK b.2 ∧
        ConRon.Bridge.CoreStep V env fe a a' ∧ ∃ w, denoteE a'.store x = some w ∧
          ConLeche.Expr.WScoped dep.toNat w) := by
  intro b hb
  obtain ⟨x, a', hr, ⟨hT, hg, hdec⟩, hA'⟩ :=
    RSim.coreAbs hq.closed (by decide) hA (inferT_rsim hq n hn hC.stageT dep e he) b hb
  obtain ⟨hs, w, hw', hsc, -⟩ := infer_crun (ConRon.Bridge.CoreSpec.of_core rfl) henv hC.check hd hw hr
  exact ⟨x, a', hr, StageC.of_T hT hs.ok, hg, hdec, hA', hs, w, hw', hsc⟩

open ConRon.Bridge.Inductives (infer_crun ensureSort_crun whnf_crun defeq_crun) in
include hq henv in
/-- `whnf_top` read through `realCall p` under `StageC`. -/
theorem whnfC_rsim (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (dep e : Word) (he : H e) {eP : ConLeche.Expr}
    (hd : denoteE a.store (decI e) = some eP) (hw : ConLeche.Expr.WScoped dep.toNat eP) :
    RSim (realCall p n "whnf_top" [vis, dep, e] m)
      (whnf V fe checkFuel dep.toNat (decI e)) a
      (fun b a' x => StageC dn vis fe env b.2 a' ∧ IWGrow m b.2 ∧ decW0E b.2 b.1 x ∧ AbsOK b.2 ∧
        ConRon.Bridge.CoreStep V env fe a a' ∧ ∃ w, denoteE a'.store x = some w ∧
          ConLeche.Expr.WScoped dep.toNat w) := by
  intro b hb
  obtain ⟨x, a', hr, ⟨hT, hg, hdec⟩, hA'⟩ :=
    RSim.coreAbs hq.closed (by decide) hA (whnfT_rsim hq n hn hC.stageT dep e he) b hb
  obtain ⟨hs, w, hw', hsc, -⟩ := whnf_crun (ConRon.Bridge.CoreSpec.of_core rfl) henv hC.check hd hw hr
  exact ⟨x, a', hr, StageC.of_T hT hs.ok, hg, hdec, hA', hs, w, hw', hsc⟩

open ConRon.Bridge.Inductives (infer_crun ensureSort_crun whnf_crun defeq_crun) in
include hq henv in
/-- `ensure_sort_core` read through `realCall p` under `StageC`. -/
theorem ensureSortC_rsim (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (dep t : Word) (ht : H t) {tP : ConLeche.Expr}
    (hd : denoteE a.store (decI t) = some tP) (hw : ConLeche.Expr.WScoped dep.toNat tP) :
    RSim (realCall p n "ensure_sort_core" [vis, dep, t] m)
      (ensureSortCore V fe checkFuel dep.toNat (decI t)) a
      (fun b a' x => StageC dn vis fe env b.2 a' ∧ IWGrow m b.2 ∧ decW0L b.2 b.1 x ∧ AbsOK b.2 ∧
        ConRon.Bridge.CoreStep V env fe a a' ∧ ∃ u, denoteL a'.store.ls x = some u) := by
  intro b hb
  obtain ⟨x, a', hr, ⟨hT, hg, hdec⟩, hA'⟩ :=
    RSim.coreAbs hq.closed (by decide) hA (ensureSortT_rsim hq n hn hC.stageT dep t ht) b hb
  obtain ⟨hs, u, hu, -⟩ := ensureSort_crun (ConRon.Bridge.CoreSpec.of_core rfl) henv hC.check hd hw hr
  exact ⟨x, a', hr, StageC.of_T hT hs.ok, hg, hdec, hA', hs, u, hu⟩

open ConRon.Bridge.Inductives (infer_crun ensureSort_crun whnf_crun defeq_crun) in
include hq henv in
/-- `is_def_eq_core` read through `realCall p` under `StageC`. -/
theorem isDefEqC_rsim (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (dep x y : Word) (hx : H x) (hy : H y)
    {xP yP : ConLeche.Expr} (hdx : denoteE a.store (decI x) = some xP)
    (hdy : denoteE a.store (decI y) = some yP) (hwx : ConLeche.Expr.WScoped dep.toNat xP)
    (hwy : ConLeche.Expr.WScoped dep.toNat yP) :
    RSim (realCall p n "is_def_eq_core" [vis, dep, x, y] m)
      (isDefEqCore V fe checkFuel dep.toNat (decI x) (decI y)) a
      (fun b a' c => StageC dn vis fe env b.2 a' ∧ IWGrow m b.2 ∧ decBool b.1 = c ∧ AbsOK b.2 ∧
        ConRon.Bridge.CoreStep V env fe a a') := by
  intro b hb
  obtain ⟨c, a', hr, ⟨hT, hg, hdec⟩, hA'⟩ :=
    RSim.coreAbs hq.closed (by decide) hA (isDefEqT_rsim hq n hn hC.stageT dep x y hx hy) b hb
  obtain ⟨hs, -⟩ := defeq_crun ((ConRon.Bridge.CoreSpec.of_core rfl).knot env fe henv) hC.check hdx hdy
    hwx hwy hr
  exact ⟨c, a', hr, StageC.of_T hT hs.ok, hg, hdec, hA', hs⟩

end entriesC

end L.Ind
