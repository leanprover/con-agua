import ConAgua.Arena.KnotEntry
import ConAgua.Arena.StageTLift

/-!
# The inductive stage under `StageT`: the shared pieces (lane `indstaget`)

The stage's word models read the core's entry points through a `CallM` (`IndCallM.lean`); at
`realCall p` the knot's `StageT` sims (`KnotEntry.lean`) are their twin side. Here: `KPT` (the
usual `RSim` post with `StageT`), a `Sim` as a `RSim`, and the four entry points as `RSim`s of
`realCall p`.
-/


open ConRon.Arena

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The usual `RSim` post with `StageT`: the stage relation with the twin's invariants, growth
from `m`, the result decoded by `dec`. -/
def KPT {α : Type} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem)
    (dec : Mem → List Word → α → Prop) (b : List Word × Mem) (a' : AState) (x : α) : Prop :=
  StageT dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ dec b.2 b.1 x

theorem KPT.kp {α : Type} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {dec : Mem → List Word → α → Prop} {b : List Word × Mem} {a' : AState} {x : α}
    (h : KPT dn vis fe m dec b a' x) : KP dn vis fe m dec b a' x := ⟨h.1.stage, h.2⟩

/-- A `Sim` is a `RSim` of the same model. -/
theorem _root_.L.Arena.Sim.rsim {β α : Type} {mo : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} (h : Sim mo op a Q) :
    RSim mo op a (fun b a' x => Q b.1 x b.2 a') := by
  intro ⟨r, m'⟩ e
  exact h r m' e

/-- **The walk memos `AbsOK` holds across a core call**: the core keeps `CoreMemos` (in `StageT`
after), writes neither array 51 nor 155 nor their epochs (`CoreStageClosed`), keeps the sizes and
the pin flag. -/
theorem absOK_core {p : Prog} (hcl : CoreStageClosed p) {f : FnName} (hf : f ∈ stageCoreFns)
    {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word} {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {a' : AState} (h : callW p n f vs m = some (r, m'))
    (hA : AbsOK m) (hT : StageT dn vis fe m' a') : AbsOK m' := by
  obtain ⟨hfr, -⟩ := run_memFrame hcl hf (run_of_callW h)
  exact ⟨hT.twin.memos.2.1, hA.2.1.frame hfr coreStageA_51 coreStageC_52,
    hA.2.2.1.frame hfr coreStageA_155 coreStageC_158, hT.twin.memos.1,
    hT.twin.memos.2.2, hT.twin.erec, hT.twin.spn, hT.twin.bstk, hT.flag⟩

/-- A core call's `RSim` with `AbsOK` added to its post. -/
theorem RSim.coreAbs {α : Type} {p : Prog} (hcl : CoreStageClosed p) {f : FnName}
    (hf : f ∈ stageCoreFns) {n : Nat} {vs : List Word} {m : Mem} {op : AM α} {a : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {Q : List Word × Mem → AState → α → Prop} (hA : AbsOK m)
    (h : RSim (callW p n f vs m) op a (fun b a' x => StageT dn vis fe b.2 a' ∧ Q b a' x)) :
    RSim (callW p n f vs m) op a
      (fun b a' x => (StageT dn vis fe b.2 a' ∧ Q b a' x) ∧ AbsOK b.2) := by
  intro b hb
  obtain ⟨x, a', hr, hT, hq⟩ := h b hb
  exact ⟨x, a', hr, ⟨hT, hq⟩, absOK_core hcl hf (r := b.1) (m' := b.2) hb hA hT⟩

section entries
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv}

include hq in
/-- `whnf_top` read through `realCall p`, as a `RSim` with `KPT`. -/
theorem whnfT_rsim (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hS : StageT dn vis fe m a) (dep e : Word) (he : H e) :
    RSim (realCall p n "whnf_top" [vis, dep, e] m) (whnf V fe checkFuel dep.toNat (decI e)) a
      (KPT dn vis fe m decW0E) :=
  (hq.whnfTop_sim n hn hS dep e he).rsim

include hq in
/-- `infer_type_core` read through `realCall p`. -/
theorem inferT_rsim (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hS : StageT dn vis fe m a) (dep e : Word) (he : H e) :
    RSim (realCall p n "infer_type_core" [vis, dep, e] m)
      (inferTypeCore V fe checkFuel dep.toNat (decI e)) a (KPT dn vis fe m decW0E) :=
  (hq.inferTypeCore_sim n hn hS dep e he).rsim

include hq in
/-- `ensure_sort_core` read through `realCall p`. -/
theorem ensureSortT_rsim (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hS : StageT dn vis fe m a) (dep t : Word) (ht : H t) :
    RSim (realCall p n "ensure_sort_core" [vis, dep, t] m)
      (ensureSortCore V fe checkFuel dep.toNat (decI t)) a (KPT dn vis fe m decW0L) :=
  (hq.ensureSortCore_sim n hn hS dep t ht).rsim

include hq in
/-- `is_def_eq_core` read through `realCall p` (the result decoded by `decW0B`). -/
theorem isDefEqT_rsim (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hS : StageT dn vis fe m a) (dep x y : Word) (hx : H x) (hy : H y) :
    RSim (realCall p n "is_def_eq_core" [vis, dep, x, y] m)
      (isDefEqCore V fe checkFuel dep.toNat (decI x) (decI y)) a
      (fun b a' c => StageT dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ decBool b.1 = c) :=
  (hq.isDefEqCore_sim n hn hS dep x y hx hy).rsim

end entries

end L.Ind
