import ConAgua.Arena.DefEqKnot
import ConAgua.Arena.IndTwin

/-!
# The knot's entry points, for callers (lane `knotwire`)

`knot_all` (`DefEqKnot.lean`) gives the knot at every L fuel from program lookups alone
(`KnotAllProg p`). This file packages the entry points the declaration checker and the inductive
stage call (`whnf_top`, `infer_type_core`, `is_def_eq_core`, `ensure_sort_core`) as specs with no
knot hypothesis left:

* **Under `CoreS`** (`L.Arena`, `KnotTopProg p`): `CoreSpec` at L fuel `n + 1` (`n + 2` for
  `ensure_sort_core`), the twin at verified mode (deliberate deviation D15) and any fuel `F ≥ n`.
  These are the census refinements of `whnf`, `inferTypeCore`, `isDefEqCore`, `ensureSortCore`.
* **Under `StageT`** (`L.Ind`, `KnotStageProg p`, lane `indproofs3`'s `IndTwin.lean`): a `Sim` of
  `callW p n f args m` against the twin at `checkFuel`, `StageT` after, the pools unchanged
  (`IWGrow`). These replace `IndStubs`' `whnf_spec`, `inferTypeCore_spec`, `ensureSortCore_spec`,
  `isDefEqCore_spec` for a caller carrying `StageT`; the word model of the call is `callW` itself
  (`callW_spec p n f` inside `vcgen`), in place of `stubM f` / `stubM_spec`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **What the entry points need of a program**: the knot's program (`KnotAllProg`), the three
`*_core` entries (`KnotEntryProg`) and `whnf_top`. -/
structure KnotTopProg (p : Prog) : Prop where
  knot : KnotAllProg p
  entry : KnotEntryProg p
  whnfTop : p.lookup "whnf_top" = some whnfTopL

section top
variable {p : Prog} (hq : KnotTopProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv}

include hq in
/-- The knot at every L fuel. -/
theorem KnotTopProg.knotOK (n : Nat) : KnotOK p n := knot_all hq.knot n

include hq in
/-- **`whnf_top(vis, dep, e)` refines `whnf .verified fe F dep e`** under `CoreS`. -/
@[refines ConRon.Arena.whnf]
theorem KnotTopProg.whnfTop_core (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (F : Nat) (hF : n ≤ F) (s₀ : St)
    (a₀ : AState) (M : ModeMaps) (dep e : Word) (hS : CoreS dn s₀.mem a₀ vis fe M 0) (he : HW e) :
    CoreSpec p (n + 1) "whnf_top" [vis, dep, e]
      (whnf .verified fe F dep.toNat (decE e)) decH s₀ a₀ dn vis fe M 0 :=
  L.Ind.whnfTop_core p hq.whnfTop hq.knotOK n hn F hF s₀ a₀ M dep e hS he

include hq in
/-- **`infer_type_core(vis, dep, e)` refines `inferTypeCore .verified fe F dep e`** under `CoreS`. -/
@[refines ConRon.Arena.inferTypeCore]
theorem KnotTopProg.inferTypeCore_core (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (F : Nat) (hF : n ≤ F)
    (s₀ : St) (a₀ : AState) (M : ModeMaps) (dep e : Word) (hS : CoreS dn s₀.mem a₀ vis fe M 0)
    (he : HW e) :
    CoreSpec p (n + 1) "infer_type_core" [vis, dep, e]
      (inferTypeCore .verified fe F dep.toNat (decE e)) decH s₀ a₀ dn vis fe M 0 :=
  inferTypeCore_refines p hq.entry n (hq.knotOK n).infer F s₀ a₀ dn vis fe M dep e hF (by omega)
    hS he

include hq in
/-- **`is_def_eq_core(vis, dep, x, y)` refines `isDefEqCore .verified fe F dep x y`** under
`CoreS`. -/
@[refines ConRon.Arena.isDefEqCore]
theorem KnotTopProg.isDefEqCore_core (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (F : Nat) (hF : n ≤ F)
    (s₀ : St) (a₀ : AState) (M : ModeMaps) (dep x y : Word) (hS : CoreS dn s₀.mem a₀ vis fe M 0)
    (hx : HW x) (hy : HW y) :
    CoreSpec p (n + 1) "is_def_eq_core" [vis, dep, x, y]
      (isDefEqCore .verified fe F dep.toNat (decE x) (decE y)) decBool s₀ a₀ dn vis fe M 0 :=
  isDefEqCore_refines p hq.entry n (hq.knotOK n).defeq F s₀ a₀ dn vis fe M dep x y hF (by omega)
    hS hx hy

include hq in
/-- **`ensure_sort_core(vis, dep, t)` refines `ensureSortCore .verified fe F dep t`** under
`CoreS` (at L fuel `n + 2`: `ensure_sort` calls the `whnf` slot one level down). -/
@[refines ConRon.Arena.ensureSortCore]
theorem KnotTopProg.ensureSortCore_core (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (F : Nat) (hF : n + 1 ≤ F)
    (s₀ : St) (a₀ : AState) (M : ModeMaps) (dep t : Word) (hS : CoreS dn s₀.mem a₀ vis fe M 0)
    (ht : HW t) :
    CoreSpec p (n + 2) "ensure_sort_core" [vis, dep, t]
      (ensureSortCore .verified fe F dep.toNat (decE t)) decLv s₀ a₀ dn vis fe M 0 :=
  ensureSortCore_refines p hq.knot.infer.leaf hq.entry n (knotUpTo_all hq.knot n) F s₀ a₀ dn vis fe
    M dep t hF hn hS ht

end top

end L.Arena

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **What the entry points under `StageT` need of a program**: `KnotTopProg` and the core's write
set (`CoreStageClosed`, decided for the checker's program in `ConAgua/Checker/IndCore.lean`). -/
structure KnotStageProg (p : Prog) : Prop extends KnotTopProg p where
  closed : CoreStageClosed p

section stage
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv}

include hq in
/-- **`whnf_top` under `StageT`** (replaces `IndStubs.whnf_spec`). -/
theorem KnotStageProg.whnfTop_sim (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hS : StageT dn vis fe m a) (dep e : Word) (he : H e) :
    Sim (callW p n "whnf_top" [vis, dep, e] m) (whnf V fe checkFuel dep.toNat (decI e)) a
      (fun r x m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ decW0E m' r x) :=
  whnfTop_simT p hq.whnfTop hq.knotOK hq.closed n hn hS dep e he

include hq in
/-- **`infer_type_core` under `StageT`** (replaces `IndStubs.inferTypeCore_spec`). -/
theorem KnotStageProg.inferTypeCore_sim (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hS : StageT dn vis fe m a) (dep e : Word) (he : H e) :
    Sim (callW p n "infer_type_core" [vis, dep, e] m)
      (inferTypeCore V fe checkFuel dep.toNat (decI e)) a
      (fun r x m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ decW0E m' r x) :=
  inferTypeCore_simT p hq.entry hq.knotOK hq.closed n hn hS dep e he

include hq in
/-- **`is_def_eq_core` under `StageT`** (replaces `IndStubs.isDefEqCore_spec`). -/
theorem KnotStageProg.isDefEqCore_sim (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hS : StageT dn vis fe m a) (dep x y : Word) (hx : H x) (hy : H y) :
    Sim (callW p n "is_def_eq_core" [vis, dep, x, y] m)
      (isDefEqCore V fe checkFuel dep.toNat (decI x) (decI y)) a
      (fun r b m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ decBool r = b) :=
  isDefEqCore_simT p hq.entry hq.knotOK hq.closed n hn hS dep x y hx hy

include hq in
/-- **`ensure_sort_core` under `StageT`** (replaces `IndStubs.ensureSortCore_spec`). -/
theorem KnotStageProg.ensureSortCore_sim (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hS : StageT dn vis fe m a) (dep t : Word) (ht : H t) :
    Sim (callW p n "ensure_sort_core" [vis, dep, t] m)
      (ensureSortCore V fe checkFuel dep.toNat (decI t)) a
      (fun r x m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ decW0L m' r x) :=
  ensureSortCore_simT p hq.entry hq.knotOK hq.closed hq.knot.infer.leaf n hn hS dep t ht

end stage

end L.Ind
