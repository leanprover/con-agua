import ConAgua.Arena.IndIface
import ConAgua.Arena.LevelApd

/-!
# `all_level_params_defined(o, l, e)`: the twin's memoized `allLevelParamsDefined` (lane `decls3`)

The twin (`ConRon/Arena/CheckerBase.lean`, `allLevelParamsDefined lps e`): every universe
parameter in `e`'s `sort`s and `const` level lists is one of `lps`; one DAG walk with a memo keyed
on the node (fresh per call), at `coreWalkFuel`. In L:

* the parameters are an `IW` slice `(o, l)` of name handles (`cv_lps`), compared as words (the
  twin reads them back once and compares names; names are hash-consed, so the handle comparison is
  the name comparison): lane `levels`' `lv_apd` (`LevelApd.lean`, `Level.allParamsDefined`) at
  `A = IW`;
* the memo is the memo library's table `APDM` (word array 151, `CTL[152]` stamp − 1, `CTL[153]`
  live count; a walk-local memo, cleared at the entry), key `(h, 0)`, value `0`/`1`;
* the fuel is the twin's: one unit per level of recursion, `0` aborts (the twin's `.internal`).

`alpd_go` re-probes before its put: the recursive calls may have filled the slot the first probe
returned. A hit returns the slot's value word `APDM.u64[j * 4 + 3]` (`d` is the probe depth, not
the value: the first version of this file returned `d`, which the spec in `DeclApdSpec.lean` exposed).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- The walk's memo table. -/
abbrev APDM : ArrId := 151

/-- Its schema: array 151, `CTL[152]`, `CTL[153]`. -/
abbrev apdSch : MemoSch := ⟨APDM, 152⟩

/-- `alpd_ls(o, l, lo, ll)`: every level of `POOL[lo ‥ lo + ll)` has its parameters in the
slice. -/
-- con-ron: ConRon/Arena/CheckerBase.lean:56-91 ConRon.Arena.allLevelParamsDefinedGo
def alpdLs : FunDecl := lfn (o, l, lo, ll) locals (r) {
  if ll == 0 { return 1 };
  r := call lv_apd(POOL⦃lo⦄, o, l);
  if r == 0 { return 0 };
  r := call alpd_ls(o, l, lo + 1, ll - 1);
  return r
}

/-- `alpd_go(o, l, f, h)`: the memoized walk at fuel `f`. -/
-- con-ron: ConRon/Arena/CheckerBase.lean:56-91 ConRon.Arena.allLevelParamsDefinedGo
@[l_impl ConRon.Arena.allLevelParamsDefinedGo]
def alpdGo : FunDecl := lfn (o, l, f, h) locals (fd, j, d, g, x, y, w, r, lo, ll) {
  if f == 0 { abort };
  (fd, j, d) := call apd_find(h, 0);
  if fd != 0 { return APDM.u64[j * 4 + 3] };
  (g, x, y, w) := call e_view(h);
  r := 1;
  if g == 2 { r := call lv_apd(x, o, l) }
  else if g == 3 { (lo, ll) := call ls_node(y); r := call alpd_ls(o, l, lo, ll) }
  else if g == 1 { r := call alpd_go(o, l, f - 1, y) }
  else if g == 4 || g == 5 || g == 6 {
    r := call alpd_go(o, l, f - 1, x);
    if r != 0 { r := call alpd_go(o, l, f - 1, y) }
  }
  else if g == 7 {
    r := call alpd_go(o, l, f - 1, x);
    if r != 0 {
      r := call alpd_go(o, l, f - 1, y);
      if r != 0 { r := call alpd_go(o, l, f - 1, w) }
    }
  }
  else if g == 9 { r := call alpd_go(o, l, f - 1, w) };
  (fd, j, d) := call apd_find(h, 0);
  d := call apd_put(h, 0, r, fd, j);
  return r
}

/-- `all_level_params_defined(o, l, e)`: `allLevelParamsDefined lps e`, `1`/`0`; the parameters
an `IW` slice. -/
-- con-ron: ConRon/Arena/CheckerBase.lean:93-98 ConRon.Arena.allLevelParamsDefined
@[l_impl ConRon.Arena.allLevelParamsDefined]
def allLevelParamsDefinedL : FunDecl := lfn (o, l, e) locals (z, r) {
  z := call apd_clear();
  r := call alpd_go(o, l, 4000000000, e);
  return r
}

/-- This module's functions, with lane `levels`' `lv_apd`/`lv_mem` at `A = IW` and the memo's
three library functions. -/
def apdFns : Prog :=
  [("all_level_params_defined", allLevelParamsDefinedL), ("alpd_go", alpdGo), ("alpd_ls", alpdLs),
   ("apd_find", memoFindG apdSch), ("apd_put", memoPutG apdSch), ("apd_clear", memoClearG apdSch),
   ("lv_apd", lvApd), ("lv_mem", lvMemG IW)]

end L.Ind
