import ConAgua.Arena.WhnfBase

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

/-! ## The L code -/

@[l_impl ConRon.Arena.getAppFn]
def getAppFnL : FunDecl := lfn (e) locals (f, t, x) {
  f := 4000000000;
  while e >> 28 == 4 {
    if f == 0 { abort };
    f -= 1;
    t := (e >> 27) & 1;
    x := e & 134217727;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[4 + t] <= x { abort };
    e := AREC.u64[x * 4 + t * 2]
  };
  if f == 0 { abort };
  return e
}

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

@[l_impl ConRon.Arena.headAndArgs]
def headAndArgsL : FunDecl := lfn (v) locals (h, o, n) {
  if v >> 28 == 4 {
    h := call get_app_fn(v);
    (o, n) := call get_app_args(v);
    return (h, o, n)
  };
  return (v, CTL.u64[136], 0)
}

@[l_impl ConRon.Arena.mkAppN]
def mkAppNL : FunDecl := lfn (f, o, n) locals (i) {
  i := 0;
  while i < n {
    f := call mk_app(f, SPN.u64[o + i]);
    i += 1
  };
  return f
}

@[l_impl ConRon.Arena.mkAppNFrom]
def mkAppNFromL : FunDecl := lfn (f, o, n, i) locals () {
  while i < n {
    f := call mk_app(f, SPN.u64[o + i]);
    i += 1
  };
  return f
}

@[l_impl ConRon.Arena.piResult]
def piResultL : FunDecl := lfn (e) locals (f, t, x) {
  f := 4000000000;
  while e >> 28 == 6 {
    if f == 0 { abort };
    f -= 1;
    t := (e >> 27) & 1;
    x := e & 134217727;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[30 + t] <= x { abort };
    e := FAREC.u64[x * 4 + t * 2 + 1]
  };
  if f == 0 { abort };
  return e
}

@[l_impl ConRon.Arena.peelPis]
def peelPisL : FunDecl := lfn (k, e) locals (t, x) {
  while k != 0 {
    if e >> 28 != 6 { return (0, 0) };
    t := (e >> 27) & 1;
    x := e & 134217727;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[30 + t] <= x { abort };
    e := FAREC.u64[x * 4 + t * 2 + 1];
    k -= 1
  };
  return (1, e)
}

/-- The spine functions. -/
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

/-- **`get_app_fn` refines `getAppFn coreWalkFuel`.** -/
@[refines ConRon.Arena.getAppFn]
theorem getAppFn_refines (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (e : Word)
    (he : HW e) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "get_app_fn" [e]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ HW (r.headD 0) ∧
      (getAppFn coreWalkFuel (decE e)).run a₀ = .ok (decE (r.headD 0), a₀); ⊤⦄ := sorry

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

/-- **`mk_app_n` refines `mkAppN`** under `ArenaD`, the list a stack slice. -/
@[refines ConRon.Arena.mkAppN]
theorem mkAppN_refines (n : Nat) (s₀ : St) (a₀ : AState) (hD : ArenaD s₀.mem a₀) (f o k : Word)
    (xs : Array EIdx) (hf : HW f) (hx : SpineR s₀.mem o k xs) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_app_n" [f, o, k]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (mkAppN (decE f) xs.toList) a₀ ∧
      ArenaD s'.mem (AM.st (mkAppN (decE f) xs.toList) a₀) ∧
      AM.res (mkAppN (decE f) xs.toList) a₀ = decE (r.headD 0) ∧ HW (r.headD 0) ∧
      Grows s₀.mem s'.mem; ⊤⦄ := sorry

/-- **`mk_app_n_from` refines `mkAppNFrom`** under `ArenaD`. -/
@[refines ConRon.Arena.mkAppNFrom]
theorem mkAppNFrom_refines (n : Nat) (s₀ : St) (a₀ : AState) (hD : ArenaD s₀.mem a₀)
    (f o k i : Word) (xs : Array EIdx) (hf : HW f) (hx : SpineR s₀.mem o k xs) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_app_n_from" [f, o, k, i]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (mkAppNFrom (decE f) xs i.toNat) a₀ ∧
      ArenaD s'.mem (AM.st (mkAppNFrom (decE f) xs i.toNat) a₀) ∧
      AM.res (mkAppNFrom (decE f) xs i.toNat) a₀ = decE (r.headD 0) ∧ HW (r.headD 0) ∧
      Grows s₀.mem s'.mem; ⊤⦄ := sorry

/-- **`pi_result` refines `piResult coreWalkFuel`.** -/
@[refines ConRon.Arena.piResult]
theorem piResult_refines (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (e : Word)
    (he : HW e) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "pi_result" [e]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ HW (r.headD 0) ∧
      (piResult coreWalkFuel (decE e)).run a₀ = .ok (decE (r.headD 0), a₀); ⊤⦄ := sorry

/-- **`peel_pis` refines `peelPis`.** -/
@[refines ConRon.Arena.peelPis]
theorem peelPis_refines (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (k e : Word)
    (he : HW e) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "peel_pis" [k, e]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ HW (r.tail.headD 0) ∧
      (peelPis k.toNat (decE e)).run a₀ = .ok (decOpt (r.headD 0) (r.tail.headD 0), a₀); ⊤⦄ :=
  sorry

end specs

end L.Arena
