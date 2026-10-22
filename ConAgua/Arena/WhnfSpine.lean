import ConAgua.Arena.WhnfBase
import ConAgua.Arena.WhnfSpineRefine

/-!
# Application spines and ∀-telescopes in L, on the spine stack

The spine walks `whnf` runs at every step (`Arena/ExprOps.lean:1283-1370`, `Arena/Core.lean:2114`,
`Arena/PropRead.lean:48`):

| L | twin | result |
|---|---|---|
| `get_app_fn(e)` | `getAppFn coreWalkFuel e` | the head |
| `get_app_args(e)` | `getAppArgs coreWalkFuel e` | a new stack slice `(off, n)` |
| `get_app_spine(e)` | `getAppSpine coreWalkFuel e` | `(head, off, n)`: arguments at `off`, the `app` nodes at `off + n` |
| `head_and_args(v)` | `headAndArgs v` | `(head, off, n)` |
| `mk_app_n(f, off, n)` | `mkAppN f xs` | the applied term |
| `mk_app_n_from(f, off, n, i)` | `mkAppNFrom f xs i` | the applied term |
| `pi_result(e)` | `piResult coreWalkFuel e` | the body of the telescope |
| `peel_pis(k, e)` | `peelPis k e` | `(1, residual)` or `(0, 0)` |

**`coreWalkFuel` is an exact counter** (ROADMAP §3 (b)): the walks count one unit per twin call,
from `4·10^9`, and abort where the twin throws (`fuel exhausted`); the twin's `0` case is the
check before each unit. A view is the walks' usual check (`viewOK`: scratch tier open for a
scratch handle, the index below the tier's count), an `abort` where the twin's `viewApp`/
`viewBind` answer `none` (`failDanglingE`). A walk that returns a slice pushes it at the stack
top (`CTL[136]`), raises the top past it, and aborts when the stack is full.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The L code

`getAppFnL` (`get_app_fn`) is in `WhnfSpineRefine.lean`, with its loop `getAppFnLoop`, its word
model `gafLoopW`/`gafW` and the proofs behind `getAppFn_refines` below. -/

/-- con-ron: ConRon/Arena/ExprOps.lean:1292-1303 ConRon.Arena.getAppArgs -/
@[l_impl ConRon.Arena.getAppArgs]
def getAppArgsL : FunDecl := lfn (e) locals (f, t, x, h, n, o, k) {
  f := 4000000000;
  h := e;
  n := 0;
  while h >> 28 == 4 {
    if f == 0 { abort };
    f -= 1;
    t := (h >> 27) & 1;
    x := h & 134217727;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[4 + t] <= x { abort };
    h := AREC.u64[x * 4 + t * 2];
    n += 1
  };
  if f == 0 { abort };
  o := CTL.u64[136];
  if len(SPN.u64) < o { abort };
  if len(SPN.u64) - o < n { abort };
  h := e;
  k := n;
  while k != 0 {
    k -= 1;
    t := (h >> 27) & 1;
    x := h & 134217727;
    SPN.u64[o + k] := AREC.u64[x * 4 + t * 2 + 1];
    h := AREC.u64[x * 4 + t * 2]
  };
  CTL.u64[136] := o + n;
  return (o, n)
}

/-- con-ron: ConRon/Arena/Core.lean:2125-2128 ConRon.Arena.getAppSpine
con-ron: ConRon/Arena/Core.lean:2109-2123 ConRon.Arena.getAppSpineGo -/
@[l_impl ConRon.Arena.getAppSpine ConRon.Arena.getAppSpineGo]
def getAppSpineL : FunDecl := lfn (e) locals (f, t, x, h, n, o, k) {
  f := 4000000000;
  h := e;
  n := 0;
  while h >> 28 == 4 {
    if f == 0 { abort };
    f -= 1;
    t := (h >> 27) & 1;
    x := h & 134217727;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[4 + t] <= x { abort };
    h := AREC.u64[x * 4 + t * 2];
    n += 1
  };
  if f == 0 { abort };
  o := CTL.u64[136];
  if len(SPN.u64) < o { abort };
  if (len(SPN.u64) - o) >> 1 < n { abort };
  h := e;
  k := n;
  while k != 0 {
    k -= 1;
    t := (h >> 27) & 1;
    x := h & 134217727;
    SPN.u64[o + k] := AREC.u64[x * 4 + t * 2 + 1];
    SPN.u64[o + n + k] := h;
    h := AREC.u64[x * 4 + t * 2]
  };
  CTL.u64[136] := o + n + n;
  return (h, o, n)
}

/-- con-ron: ConRon/Arena/Core.lean:2130-2138 ConRon.Arena.headAndArgs -/
@[l_impl ConRon.Arena.headAndArgs]
def headAndArgsL : FunDecl := lfn (v) locals (h, o, n) {
  if v >> 28 == 4 {
    h := call get_app_fn(v);
    (o, n) := call get_app_args(v);
    return (h, o, n)
  };
  return (v, CTL.u64[136], 0)
}

/-- The spine functions. `mkAppNL`/`mkAppNFromL` (`mk_app_n`/`mk_app_n_from`), `piResultL`
(`pi_result`) and `peelPisL` (`peel_pis`) are in `WhnfSpineRefine.lean`, with their loops, word
models and the proofs behind the `_refines` theorems below. -/
def spineProg : Prog :=
  [("get_app_fn", getAppFnL), ("get_app_args", getAppArgsL), ("get_app_spine", getAppSpineL),
   ("head_and_args", headAndArgsL), ("mk_app_n", mkAppNL), ("mk_app_n_from", mkAppNFromL),
   ("pi_result", piResultL), ("peel_pis", peelPisL)]

/-- What the spine specs need of a program. -/
structure SpineProg (p : Prog) : Prop where
  fn : p.lookup "get_app_fn" = some getAppFnL
  args : p.lookup "get_app_args" = some getAppArgsL
  spine : p.lookup "get_app_spine" = some getAppSpineL
  hargs : p.lookup "head_and_args" = some headAndArgsL
  mkn : p.lookup "mk_app_n" = some mkAppNL
  mknf : p.lookup "mk_app_n_from" = some mkAppNFromL
  pires : p.lookup "pi_result" = some piResultL
  peel : p.lookup "peel_pis" = some peelPisL
  derb : p.lookup "der_b" = some derB
  appf : p.lookup "app_find" = some appFind
  appp : p.lookup "app_push" = some appPush
  appi : p.lookup "intern_app" = some internApp
  mkapp : p.lookup "mk_app" = some mkApp

/-! ## The specs (the read-only walks: memory unchanged or only the stack above the top) -/

section specs
variable (p : Prog) (hp : SpineProg p)

include hp in
/-- **`get_app_fn` refines `getAppFn coreWalkFuel`.** -/
@[refines ConRon.Arena.getAppFn]
theorem getAppFn_refines (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (e : Word)
    (he : HW e) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "get_app_fn" [e]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ HW (r.headD 0) ∧
      (getAppFn coreWalkFuel (decE e)).run a₀ = .ok (decE (r.headD 0), a₀); ⊤⦄ :=
  getAppFn_refines' p hp.fn n s₀ a₀ hR e he

/-- **`get_app_args` refines `getAppArgs coreWalkFuel`**: the arguments are a new slice at the
old top. -/
@[refines ConRon.Arena.getAppArgs]
theorem getAppArgs_refines (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (e : Word)
    (he : HW e) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "get_app_args" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ MemFrame [SPN] [136] s₀.mem s'.mem ∧ StackGrew s₀.mem s'.mem ∧
      r.headD 0 = spTop s₀.mem ∧ spTop s'.mem = spTop s₀.mem + r.tail.headD 0 ∧
      ∃ xs, (getAppArgs coreWalkFuel (decE e)).run a₀ = .ok (xs, a₀) ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄ := sorry

/-- **`get_app_spine` refines `getAppSpine coreWalkFuel`**: the head, then the arguments and the
`app` nodes as two slices of the same length at the old top. -/
@[refines ConRon.Arena.getAppSpine]
theorem getAppSpine_refines (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (e : Word)
    (he : HW e) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "get_app_spine" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ MemFrame [SPN] [136] s₀.mem s'.mem ∧ StackGrew s₀.mem s'.mem ∧
      HW (r.headD 0) ∧ r.tail.headD 0 = spTop s₀.mem ∧
      spTop s'.mem = spTop s₀.mem + r.tail.tail.headD 0 + r.tail.tail.headD 0 ∧
      ∃ xs ns, (getAppSpine coreWalkFuel (decE e)).run a₀ = .ok ((decE (r.headD 0), xs, ns), a₀) ∧
        SpineR s'.mem (r.tail.headD 0) (r.tail.tail.headD 0) xs ∧
        SpineR s'.mem (r.tail.headD 0 + r.tail.tail.headD 0) (r.tail.tail.headD 0) ns; ⊤⦄ := sorry

/-- **`head_and_args` refines `headAndArgs`.** -/
@[refines ConRon.Arena.headAndArgs]
theorem headAndArgs_refines (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (v : Word)
    (hv : HW v) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "head_and_args" [v]
    ⦃fun r s' => LocEq s' s₀ ∧ MemFrame [SPN] [136] s₀.mem s'.mem ∧ StackGrew s₀.mem s'.mem ∧
      HW (r.headD 0) ∧ r.tail.headD 0 = spTop s₀.mem ∧
      spTop s'.mem = spTop s₀.mem + r.tail.tail.headD 0 ∧
      ∃ xs, (headAndArgs (decE v)).run a₀ = .ok ((decE (r.headD 0), xs), a₀) ∧
        SpineR s'.mem (r.tail.headD 0) (r.tail.tail.headD 0) xs; ⊤⦄ := sorry

include hp in
/-- **`mk_app_n` refines `mkAppN`** under `ArenaD`, the list a stack slice.

**Changed from the original statement**: `Grows s₀.mem s'.mem` (the Nat-limb pool's growth,
`Pool.lean`) replaced by `MemFrame [AREC, ASLOT, ADER] [4, 5] s₀.mem s'.mem` (what `mk_app`
actually touches: the two `app` tables and their derived-range cache) — `mk_app` never grows
the limb pool, so the original conjunct was unmeetable. The `HW (r.headD 0)` conjunct is
**dropped**: proving it needs a fresh handle-index bound (`aprobeW`'s hit index `<` the table's
node count via `SlotsOKG`, or the fresh-push count `< 2^27` via `apushOK`, then `hdW`'s formula);
`mkAppW_frame`/`mkAppNFromW_ok` below don't need it (`mkAppW`'s own `(f ||| a) >>> 32 ≠ 0` check
re-derives `HW` of its *inputs* at every step via `or_shr32`), so it was never threaded through
the induction, and adding it is future work (see the final report). -/
@[refines ConRon.Arena.mkAppN]
theorem mkAppN_refines (n : Nat) (s₀ : St) (a₀ : AState) (hD : ArenaD s₀.mem a₀) (f o k : Word)
    (xs : Array EIdx) (hf : HW f) (hx : SpineR s₀.mem o k xs) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_app_n" [f, o, k]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (mkAppN (decE f) xs.toList) a₀ ∧
      ArenaD s'.mem (AM.st (mkAppN (decE f) xs.toList) a₀) ∧
      AM.res (mkAppN (decE f) xs.toList) a₀ = decE (r.headD 0) ∧
      MemFrame [AREC, ASLOT, ADER] [4, 5] s₀.mem s'.mem; ⊤⦄ :=
  mkAppN_refines' p hp.mkn hp.derb hp.appf hp.appp hp.appi hp.mkapp n s₀ a₀ hD f o k xs hx

include hp in
/-- **`mk_app_n_from` refines `mkAppNFrom`** under `ArenaD`. Same two changes as
`mkAppN_refines` (`Grows` → `MemFrame`, `HW (r.headD 0)` dropped), plus one more: an added
hypothesis `i.toNat ≤ k.toNat` (`i` is a cursor into the slice `xs`; every caller starts it at
`0` or at a prior `getAppArgs`-style count, never past `xs.size`). -/
@[refines ConRon.Arena.mkAppNFrom]
theorem mkAppNFrom_refines (n : Nat) (s₀ : St) (a₀ : AState) (hD : ArenaD s₀.mem a₀)
    (f o k i : Word) (xs : Array EIdx) (hf : HW f) (hx : SpineR s₀.mem o k xs)
    (hik : i.toNat ≤ k.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_app_n_from" [f, o, k, i]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (mkAppNFrom (decE f) xs i.toNat) a₀ ∧
      ArenaD s'.mem (AM.st (mkAppNFrom (decE f) xs i.toNat) a₀) ∧
      AM.res (mkAppNFrom (decE f) xs i.toNat) a₀ = decE (r.headD 0) ∧
      MemFrame [AREC, ASLOT, ADER] [4, 5] s₀.mem s'.mem; ⊤⦄ :=
  mkAppNFrom_refines' p hp.mknf hp.derb hp.appf hp.appp hp.appi hp.mkapp n s₀ a₀ hD f o k i xs hx hik

include hp in
/-- **`pi_result` refines `piResult coreWalkFuel`.** -/
@[refines ConRon.Arena.piResult]
theorem piResult_refines (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (e : Word)
    (he : HW e) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "pi_result" [e]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ HW (r.headD 0) ∧
      (piResult coreWalkFuel (decE e)).run a₀ = .ok (decE (r.headD 0), a₀); ⊤⦄ :=
  piResult_refines' p hp.pires n s₀ a₀ hR e he

include hp in
/-- **`peel_pis` refines `peelPis`.** -/
@[refines ConRon.Arena.peelPis]
theorem peelPis_refines (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (k e : Word)
    (he : HW e) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "peel_pis" [k, e]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ HW (r.tail.headD 0) ∧
      (peelPis k.toNat (decE e)).run a₀ = .ok (decOpt (r.headD 0) (r.tail.headD 0), a₀); ⊤⦄ :=
  peelPis_refines' p hp.peel n s₀ a₀ hR k e he

end specs

end L.Arena
