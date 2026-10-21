import ConAgua.Arena.CoreRefine
import ConAgua.Arena.View
import ConAgua.Arena.NatArms
import ConAgua.Arena.Pins
import ConRon.Arena.Core
import ConAgua.Census.Attr

/-!
# The whnf family's shared statements: arguments, the spine stack, the relation, the knot

Everything the L code of `whnfCore`/`whnf` and their arms (`WhnfSpine.lean`, `WhnfCore.lean`,
`WhnfDelta.lean`, `WhnfIota.lean`) is stated against.

**Arguments.** The twin's bodies take `mode : CheckMode`, the knot record `r : CoreFnsA`, the
environment view `fe : IFEnv` and `depth : Nat`. In L: a mode word (`decMode`: `0` verified, `1`
trusted, `2` verified-eager, `3` trusted-eager; bit 0 is "trusted", bit 1 "eager"), the view word
`vis` (`EnvR dn m vis fe`), the depth word; the record is the program itself (the knot's slots
are L functions, `whnf_core`, `whnf`, `infer`, `infer_io`, `defeq`), tied at the twin's knot
`coreKnot mode fe id F` for every `F` at or above the L fuel (the `GoOK` shape of `WalkRefine`).

**The spine stack.** The twin's `Array EIdx`/`List EIdx` values (spines, accumulators, rule
arguments) live in the word array `SPN` (144) as slices `(off, cnt)`; `CTL[136]` is the top.
A function that needs room pushes above the top and puts the top back before it returns
(`StackKept`); one that returns a slice leaves it at the old top (`StackGrew`). `SpineR m off len
xs`: the slice denotes `xs` (handle words, each below `2^32`). Overflow is an `abort` (a
capacity, as every table's).

**The relation.** `CoreS dn m a vis fe M G g`: `ArenaD`, the core tier at explicit maps
(`CoreRM`, so that the eager slot can state the saved banks), the filled pin table, the
environment. After a core run: `CoreAfter` (some maps that keep every other bank, `KeptAll`, and
the stack below the top).

**Stubs.** Callees whose L code does not exist yet are named L functions with an abstract
spec (`WhnfCallees`); the refinements are proved from it, and the census-tagged theorems
instantiate it with `whnfCallees_stub` (a `sorry`) until the callees land.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedVariables false

namespace L.Arena

/-! ## Arguments -/

/-- The mode word. -/
def decMode (w : Word) : ConLeche.CheckMode :=
  if w = 0 then .verified else if w = 1 then .trusted else if w = 2 then .verifiedEager
  else .trustedEager

/-- A handle word (an index `< 2^32` of any kind). -/
def HW (w : Word) : Prop := w.toNat < 2 ^ 32

/-- A `Bool` result word. -/
def decBool (r : List Word) : Bool := r.headD 0 != 0

/-- A handle result word. -/
def decH (r : List Word) : EIdx := decE (r.headD 0)

/-- An `Option EIdx` result: `(flag, handle)`. -/
def decOptR (r : List Word) : Option EIdx := decOpt (r.headD 0) (r.tail.headD 0)

/-- A `WhnfStep` result: `(0, e)` is `.done e`, `(1, e)` is `.cont e`. -/
def decStep (r : List Word) : WhnfStep :=
  if r.headD 0 = 0 then .done (decE (r.tail.headD 0)) else .cont (decE (r.tail.headD 0))

/-! ## The spine stack: array 144, top `CTL[136]` -/

abbrev SPN : ArrId := 144

/-- The stack top. -/
def spTop (m : Mem) : Word := rdW (m.arr64 CTL) 136

/-- Word `i` of the stack. -/
def spW (m : Mem) (i : Word) : Word := rdW (m.arr64 SPN) i

/-- **A slice of the stack denotes a handle array.** -/
structure SpineR (m : Mem) (off cnt : Word) (xs : Array EIdx) : Prop where
  size : xs.size = cnt.toNat
  bound : off.toNat + cnt.toNat ≤ (m.arr64 SPN).size
  lt : ∀ i : Nat, i < cnt.toNat → (spW m (off + i.toUInt64)).toNat < 2 ^ 32
  get : ∀ (i : Nat) (h : i < xs.size), xs[i] = decE (spW m (off + i.toUInt64))

/-- The stack below the top is unchanged, and so is the top. -/
def StackKept (m m' : Mem) : Prop :=
  spTop m' = spTop m ∧ (m'.arr64 SPN).size = (m.arr64 SPN).size ∧
    ∀ i : Word, i < spTop m → spW m' i = spW m i

/-- The stack below the old top is unchanged; the top may have grown (a returned slice). -/
def StackGrew (m m' : Mem) : Prop :=
  spTop m ≤ spTop m' ∧ (m'.arr64 SPN).size = (m.arr64 SPN).size ∧
    ∀ i : Word, i < spTop m → spW m' i = spW m i

theorem StackKept.refl (m : Mem) : StackKept m m := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem StackKept.trans {m₁ m₂ m₃ : Mem} (h₁ : StackKept m₁ m₂) (h₂ : StackKept m₂ m₃) :
    StackKept m₁ m₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1,
    fun i hi => (h₂.2.2 i (h₁.1 ▸ hi)).trans (h₁.2.2 i hi)⟩

/-! ## The relation the core runs under -/

/-- All six mode memos keep the banks of every other generation `≤ G`. -/
def KeptAll (M M' : ModeMaps) (G g : Word) : Prop :=
  Kept M.wc M'.wc G g ∧ Kept M.wk M'.wk G g ∧ Kept M.wh M'.wh G g ∧ Kept M.inf M'.inf G g ∧
    Kept M.io M'.io G g ∧ Kept M.de M'.de G g

theorem KeptAll.refl (M : ModeMaps) (G g : Word) : KeptAll M M G g :=
  ⟨Kept.refl _ _ _, Kept.refl _ _ _, Kept.refl _ _ _, Kept.refl _ _ _, Kept.refl _ _ _,
    Kept.refl _ _ _⟩

/-- **The core's relation** at explicit cache maps. -/
structure CoreS (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (G g : Word) : Prop where
  arena : ArenaD m a
  core : CoreRM m a.caches M G g
  pins : PinsFull m a.pins
  env : EnvR dn m vis fe

/-- **After a core run** from `m₀` at maps `M`, `G`, generation `g`: the relation holds at some
maps that keep every other generation's bank, and the stack below the top is as it was. -/
def CoreAfter (dn : NIdx → Option ConLeche.Name) (m₀ m : Mem) (a : AState) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (G g : Word) : Prop :=
  ∃ M' G', CoreS dn m a vis fe M' G' g ∧ KeptAll M M' G g ∧ StackKept m₀ m

/-- **The refinement post of a core function**: the twin run `T` from `a₀` succeeds, the relation
holds after it, and the result words decode (`dec`) to its result. -/
def CoreRef {α : Type} [Inhabited α] (T : AM α) (a₀ : AState) (dec : List Word → α)
    (dn : NIdx → Option ConLeche.Name) (m₀ : Mem) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (G g : Word) (r : List Word) (m : Mem) : Prop :=
  AM.ok T a₀ ∧ CoreAfter dn m₀ m (AM.st T a₀) vis fe M G g ∧ AM.res T a₀ = dec r

/-- The spec shape: from `s₀` under `CoreS`, the call refines `T`. -/
def CoreSpec {α : Type} [Inhabited α] (p : Prog) (n : Nat) (f : FnName) (args : List Word)
    (T : AM α) (dec : List Word → α) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (G g : Word) : Prop :=
  ⦃fun s => s = s₀⦄
  invoke p (exec p n) f args
  ⦃fun r s' => LocEq s' s₀ ∧ CoreRef T a₀ dec dn s₀.mem vis fe M G g r s'.mem; ⊤⦄

/-! ## The knot's slots

`coreKnot mode fe id F` is the twin's record; the L slot at fuel `n` refines it at every
`F ≥ n`. The two `whnf` slots are this lane's (`WhnfCore.lean`, `WhnfDelta.lean`); `infer`,
`infer_io` and `defeq` are phases 6–7, stubs here. -/

/-- The common hypotheses of a slot call. -/
structure SlotPre (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (G g : Word) (mode : Word) : Prop where
  rel : CoreS dn s₀.mem a₀ vis fe M G g
  mode : mode < 4

/-- `whnf_core(mode, cheap, vis, d, e)` refines the knot's `whnfCore` slot. -/
def WhnfCoreSlot (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (G g mode cheap d e : Word), n ≤ F → SlotPre s₀ a₀ dn vis fe M G g mode →
    HW e →
    CoreSpec p n "whnf_core" [mode, cheap, vis, d, e]
      ((coreKnot (decMode mode) fe id F).whnfCore (cheap != 0) d.toNat (decE e)) decH s₀ a₀ dn vis
      fe M G g

/-- `whnf(mode, vis, d, e)` refines the knot's `whnf` slot. -/
def WhnfSlot (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (G g mode d e : Word), n ≤ F → SlotPre s₀ a₀ dn vis fe M G g mode → HW e →
    CoreSpec p n "whnf" [mode, vis, d, e]
      ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE e)) decH s₀ a₀ dn vis fe M G g

/-- `infer(mode, vis, d, e)` refines the knot's full-grade `infer` slot (phase 7). -/
def InferSlot (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (G g mode d e : Word), n ≤ F → SlotPre s₀ a₀ dn vis fe M G g mode → HW e →
    CoreSpec p n "infer" [mode, vis, d, e]
      ((coreKnot (decMode mode) fe id F).infer d.toNat (decE e)) decH s₀ a₀ dn vis fe M G g

/-- `infer_io(mode, vis, d, e)` refines the knot's io-grade `inferIO` slot (phase 7). -/
def InferIOSlot (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (G g mode d e : Word), n ≤ F → SlotPre s₀ a₀ dn vis fe M G g mode → HW e →
    CoreSpec p n "infer_io" [mode, vis, d, e]
      ((coreKnot (decMode mode) fe id F).inferIO d.toNat (decE e)) decH s₀ a₀ dn vis fe M G g

/-- `defeq(mode, vis, d, a, b)` refines the knot's `defeq` slot (phase 6). -/
def DefeqSlot (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (G g mode d x y : Word), n ≤ F → SlotPre s₀ a₀ dn vis fe M G g mode → HW x →
    HW y →
    CoreSpec p n "defeq" [mode, vis, d, x, y]
      ((coreKnot (decMode mode) fe id F).defeq d.toNat (decE x) (decE y)) decBool s₀ a₀ dn vis fe
      M G g

/-- **The knot at L fuel `n`**: every slot. -/
structure KnotOK (p : Prog) (n : Nat) : Prop where
  whnfCore : WhnfCoreSlot p n
  whnf : WhnfSlot p n
  infer : InferSlot p n
  inferIO : InferIOSlot p n
  defeq : DefeqSlot p n

/-! ## Stubs: callees whose L code is not written yet

Each is a named L function with the spec its twin will get. `WhnfCallees p` bundles them; the
whnf family's refinements take it as a hypothesis, the census-tagged ones get it from
`whnfCallees_stub` (a `sorry`, listed in DESIGN.md). -/

/-- `inst_list(e, off, cnt, d)` refines `instantiateListFast coreWalkFuel e xs d` (phase 4),
the accumulator a stack slice. -/
def InstListOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (G g e off cnt d : Word) (xs : Array EIdx), CoreS dn s₀.mem a₀ vis fe M G g →
    HW e → SpineR s₀.mem off cnt xs → off.toNat + cnt.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p n "inst_list" [e, off, cnt, d]
      (instantiateListFast coreWalkFuel (decE e) xs d.toNat) decH s₀ a₀ dn vis fe M G g

/-- `inst_lp(po, pl, us, e)` refines `instLPFast coreWalkFuel lps us e` (phase 4), the level
parameters a slice of the environment's record pool (`EREC`). -/
def InstLPOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (G g po pl us e : Word) (lps : List NIdx), CoreS dn s₀.mem a₀ vis fe M G g →
    HW e → HW us → hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps →
    CoreSpec p n "inst_lp" [po, pl, us, e]
      (instLPFast coreWalkFuel lps (decI us) (decE e)) decH s₀ a₀ dn vis fe M G g

/-- `str_lit_ctor(h)` refines `strLitToConstructor s` at a string literal `h` (the `lit` store
does not keep a string's characters yet: see DESIGN.md). -/
def StrLitCtorOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (G g h : Word) (s : String), CoreS dn s₀.mem a₀ vis fe M G g → HW h →
    a₀.store.view (decE h) = some (.lit (.strVal s)) →
    CoreSpec p n "str_lit_ctor" [h] (strLitToConstructor s) decH s₀ a₀ dn vis fe M G g

/-- `str_lit_supported(vis)` refines `strLitSupported fe`. -/
def StrLitSupportedOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (G g : Word), CoreS dn s₀.mem a₀ vis fe M G g →
    CoreSpec p n "str_lit_supported" [vis] (strLitSupported fe) decBool s₀ a₀ dn vis fe M G g

/-- **The stub callees.** -/
structure WhnfCallees (p : Prog) : Prop where
  instList : InstListOK p
  instLP : InstLPOK p
  strLitCtor : StrLitCtorOK p
  strLitSupported : StrLitSupportedOK p
  /-- The knot's `infer`, `infer_io`, `defeq` slots one level up from the whnf slots: their
  induction step is phases 6–7. -/
  inferStep : ∀ n, KnotOK p n → InferSlot p (n + 1)
  inferIOStep : ∀ n, KnotOK p n → InferIOSlot p (n + 1)
  defeqStep : ∀ n, KnotOK p n → DefeqSlot p (n + 1)

/-- **The stubs' specs, assumed** until their L code lands (phases 4, 6, 7; string literals). -/
theorem whnfCallees_stub (p : Prog) : WhnfCallees p := sorry

end L.Arena
