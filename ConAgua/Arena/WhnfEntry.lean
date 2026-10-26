import ConAgua.Arena.WhnfDeltaSlot
import ConAgua.Arena.WhnfSpine
import ConAgua.Arena.IndIface

/-!
# Lane `induct`'s conventions for this phase's functions (adapters)

Lane `induct` (`IndIface.lean`, `stubFns`) calls the whnf family with its own conventions: the
verified mode, an explicit walk fuel, lists as `IW` slices. This lane's functions take the mode
word, count `coreWalkFuel` themselves, and put lists on the spine stack `SPN`. The adapters
below give `induct`'s conventions under their own names (lane `induct`'s call sites rename
`whnf` → `whnf_top`, `get_app_fn` → `get_app_fn_f`, `get_app_args` → `get_app_args_f`,
`mk_app_n` → `mk_app_n_f`, `pi_result` → `pi_result_f`; DESIGN.md, lane `whnf`).

| adapter | `induct`'s convention | runs |
|---|---|---|
| `whnf_top(vis, dep, e)` | `whnf .verified fe checkFuel dep e` | `whnf(0, vis, dep, e)` |
| `get_app_fn_f(fuel, e)` | `getAppFn fuel e` | `get_app_fn(e)` at `fuel = CWF`, else abort |
| `pi_result_f(fuel, e)` | `piResult fuel e` | `pi_result(e)` at `fuel = CWF`, else abort |
| `get_app_args_f(fuel, e)` | `getAppArgs fuel e`, an `IW` slice | `get_app_args(e)`, the slice copied to `IW`, the stack top put back |
| `mk_app_n_f(f, off, len)` | `mkAppN f xs`, `xs` an `IW` slice | the slice copied to the stack top, `mk_app_n`, the top put back |

`induct` passes `⟪CWF⟫` (= `coreWalkFuel`) at every call site, so the abort at any other fuel is
never taken; its `RelAM` specs speak of successful runs only.
-/

open ConRon.Arena
open L.Ind (CWF IW)

namespace L.Arena

/-- con-ron: ConRon/Arena/Core.lean:3644-3648 ConRon.Arena.whnf -/
@[l_impl ConRon.Arena.whnf]
def whnfTopL : FunDecl := lfn (vis, dep, e) locals (r) {
  r := call whnf(0, vis, dep, e);
  return r
}

-- con-ron: none — the explicit-fuel convention of lane `induct` (the walk counts `CWF` itself)
def getAppFnFL : FunDecl := lfn (f, e) locals (r) {
  if f != ⟪CWF⟫ { abort };
  r := call get_app_fn(e);
  return r
}

-- con-ron: none — the explicit-fuel convention of lane `induct` (the walk counts `CWF` itself)
def piResultFL : FunDecl := lfn (f, e) locals (r) {
  if f != ⟪CWF⟫ { abort };
  r := call pi_result(e);
  return r
}

/-- `spn_to_iw(d, s, l)`: `IW[d + j] := SPN[s + j]` for `j < l`. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
def spnToIwL : FunDecl := lfn (d, s, l) locals (u) {
  if l == 0 { return 0 };
  IW.u64[d] := SPN.u64[s];
  u := call spn_to_iw(d + 1, s + 1, l - 1);
  return 0
}

/-- `iw_to_spn(d, s, l)`: `SPN[d + j] := IW[s + j]` for `j < l`. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
def iwToSpnL : FunDecl := lfn (d, s, l) locals (u) {
  if l == 0 { return 0 };
  SPN.u64[d] := IW.u64[s];
  u := call iw_to_spn(d + 1, s + 1, l - 1);
  return 0
}

-- con-ron: none — lane `induct`'s `IW`-slice convention over `get_app_args`'s stack slice
def getAppArgsFL : FunDecl := lfn (f, e) locals (top, o, n, q, u) {
  if f != ⟪CWF⟫ { abort };
  top := CTL.u64[136];
  (o, n) := call get_app_args(e);
  q := call iw_alloc(n);
  u := call spn_to_iw(q, o, n);
  CTL.u64[136] := top;
  return (q, n)
}

-- con-ron: none — lane `induct`'s `IW`-slice convention over `mk_app_n`'s stack slice
def mkAppNFL : FunDecl := lfn (f, off, cnt) locals (top, u, r) {
  top := CTL.u64[136];
  if len(SPN.u64) < top { abort };
  if len(SPN.u64) - top < cnt { abort };
  u := call iw_to_spn(top, off, cnt);
  CTL.u64[136] := top + cnt;
  r := call mk_app_n(f, top, cnt);
  CTL.u64[136] := top;
  return r
}

end L.Arena
