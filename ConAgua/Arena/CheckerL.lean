module

public import ConAgua.Arena.DeclBase
import ConAgua.Census.Attr
public import ConAgua.Arena.Reasons

@[expose] public section

/-!
# The check phase's L functions: the stream index and the jobs

con-ron's driver (#143, con-leche's #480): after the parse, the preparation and the pins, the
stream's index is built from the records alone (`buildIndex`, `Arena/StreamIndex.lean`): every
record's constants and tables, read off it with no inference (`declConstants`, `declTables`),
a name's first entry winning; then every record's check is a **job** at the index's view of its
position (`recordJob`). The refinements are in `Arena/Checker.lean`; the L code is kept apart
so that the assembled program (`Checker/Prog.lean`) does not wait for them.

* `build_index(cnt)`: `buildIndex` over the front's records `0‥cnt - 1`: for record `k`,
  `FIRSTS[k]` is the next counter (`IStreamIndex.firsts`), its constants go to the stream
  index's rows (`insertConsts`: a row is written only where none is, the counter always moves),
  its tables to the table rows at position `k` (`insertTables`). The next counter is `CTL[128]`.
  It runs with the scratch tier off, so every record lands in `EREC`'s tier 0. The ten literal
  names go to `CTL[162‥171]` first (`str_lit_names`); past the last record the index is frozen
  (`index_freeze`): the literal flags' thresholds into `CTL[172]`, `CTL[173]`.
* `record_job(k)`: `recordJob`: the scratch bracket, the view of position `k` (`CTL[134]` its
  first counter, `CTL[135]` the position, the literal flags `CTL[160]`, `CTL[161]` by `from_le`
  against the thresholds), a fresh own layer (the stamp `CTL[133]` bumped,
  `vis = 0`), the `And` pin, then `checkRecord` at the run's solution: `check_decl(k, 0)` when
  the flag `CTL[224]` is `0` (`J = none`, every flat run), `check_record_sol(k, 0)` otherwise
  (`J = some sol`, the challenge's jobs of `--compare`, `Arena/JustifyIface.lean`); the tier-1 records dropped with the bracket.
* `check_jobs(j, hi)`: the jobs `j‥hi - 1` in order (`checkJobList` over a range).
-/

namespace L.Arena

open L.Front (DECL)
open L.Ind (IW)

/-! ## The stream index -/

/-- `idx_consts(o, n)`: `insertConsts` over the `n` constant records `IW[o‥o + n)`: each name's row
written if it has none, at the next counter `CTL[128]`, which always moves. -/
-- con-ron: ConRon/Arena/StreamIndex.lean:49-54 ConRon.Arena.insertConsts
@[no_expose, l_impl ConRon.Arena.insertConsts]
def idxConstsL : FunDecl := lfn (o, n) locals (j, q, w, c, p, nx, z) {
  j := 0;
  for j < n {
    q := IW.u64[o + j];
    w := EREC⦃q + ⟪CI.cv + CV.name⟫⦄;
    nx := CTL.u64[128];
    if 4294967294 <= nx { abort };
    (c, p) := call base_row_get(w);
    if c == 0 { z := call base_row_set(w, nx + 1, q) };
    CTL.u64[128] := nx + 1
  };
  return 0
}

/-- `idx_tables(o, n, r)`: `insertTables` over the `n` table records `IW[o‥o + n)` of record
position `r`: each structure's table row written if it has none. -/
-- con-ron: ConRon/Arena/StreamIndex.lean:56-61 ConRon.Arena.insertTables
@[no_expose, l_impl ConRon.Arena.insertTables]
def idxTablesL : FunDecl := lfn (o, n, r) locals (j, q, w, c, p, z) {
  j := 0;
  for j < n {
    q := IW.u64[o + j];
    w := EREC⦃q + ⟪ProjTbl.structName⟫⦄;
    (c, p) := call tbl_base_get(w);
    if c == 0 { z := call tbl_base_set(w, r + 1, q) }
  };
  return 0
}

/-- `idx_add(k)`: `IStreamIndex.add` of record `k`: its first counter, its constants, its tables
(the work pool emptied first: the slices live only for the record). -/
-- con-ron: ConRon/Arena/StreamIndex.lean:63-72 ConRon.Arena.IStreamIndex.add
@[no_expose, l_impl ConRon.Arena.IStreamIndex.add]
def idxAddL : FunDecl := lfn (k) locals (o, n, z) {
  z := call iw_reset();
  if len(FIRSTS.u64) <= k { abort };
  FIRSTS.u64[k] := CTL.u64[128];
  (o, n) := call decl_constants(k);
  z := call idx_consts(o, n);
  (o, n) := call decl_tables(k);
  z := call idx_tables(o, n, k);
  return 0
}

/-- `lit_from(i, stop)`: `litFrom` over the stream index's rows of the literal names
`CTL[162 + i‥162 + stop)`: from which counter a view holds them all, as `optW` (`0` none, `k + 1`
some `k`): one past the largest counter of their rows, none if one has no row (or the range is
past the ten names). -/
-- con-ron: ConRon/Arena/Env.lean:244-258 ConRon.Arena.litFrom
@[no_expose, l_impl ConRon.Arena.litFrom]
def litFromL : FunDecl := lfn (i, stop) locals (c, p, k) {
  if stop <= i { return 1 };
  if 10 <= i { return 0 };
  (c, p) := call base_row_get(CTL.u64[162 + i]);
  if c == 0 { return 0 };
  k := call lit_from(i + 1, stop);
  if k == 0 { return 0 };
  if c <= k - 1 { return k };
  return c + 1
}

/-- `str_lit_names()`: the ten literal names off the pin table into `CTL[162‥171]`
(`strLitNames`' order: `Nat`, `Nat.zero`, `Nat.succ`, then `String`, `String.ofList`, `List`,
`List.nil`, `List.cons`, `Char`, `Char.ofNat`). Written before the stream index is built: the
builder's environment already holds the literal names (the twin's `mkIFEnvLits`, and its proofs'
`driverFE`), and the pins do not change during the build, so the freeze reads the same names. -/
-- con-ron: ConRon/Arena/Core.lean:125-138 ConRon.Arena.strLitNames
-- con-ron: ConRon/Arena/Core.lean:116-123 ConRon.Arena.natLitNames
@[no_expose, l_impl ConRon.Arena.strLitNames ConRon.Arena.natLitNames]
def strLitNamesL : FunDecl := lfn () locals (a) {
  a := call pin_at(1);
  CTL.u64[162] := a;
  a := call pin_at(2);
  CTL.u64[163] := a;
  a := call pin_at(3);
  CTL.u64[164] := a;
  a := call pin_at(5);
  CTL.u64[165] := a;
  a := call pin_at(6);
  CTL.u64[166] := a;
  a := call pin_at(7);
  CTL.u64[167] := a;
  a := call pin_at(8);
  CTL.u64[168] := a;
  a := call pin_at(9);
  CTL.u64[169] := a;
  a := call pin_at(10);
  CTL.u64[170] := a;
  a := call pin_at(12);
  CTL.u64[171] := a;
  return 0
}

/-- `index_freeze()`: `IStreamIndex.freeze`: the two literal flags' thresholds over the literal
names `CTL[162‥171]` (written by `str_lit_names` before the build) into `CTL[172]` (the first
three), `CTL[173]` (all ten). -/
-- con-ron: ConRon/Arena/StreamIndex.lean:74-81 ConRon.Arena.IStreamIndex.freeze
@[no_expose, l_impl ConRon.Arena.IStreamIndex.freeze]
def indexFreezeL : FunDecl := lfn () locals (nf, sf) {
  nf := call lit_from(0, 3);
  sf := call lit_from(0, 10);
  CTL.u64[172] := nf;
  CTL.u64[173] := sf;
  return 0
}

/-- `build_index(cnt)`: `buildIndex` over records `0‥cnt - 1`, from the empty index (zero rows,
`CTL[128] = 0`), the literal names written first (`str_lit_names`), frozen past the last record
(`index_freeze`). -/
-- con-ron: ConRon/Arena/StreamIndex.lean:83-100 ConRon.Arena.buildIndexGo
-- con-ron: ConRon/Arena/StreamIndex.lean:102-105 ConRon.Arena.buildIndex
@[no_expose, l_impl ConRon.Arena.buildIndexGo ConRon.Arena.buildIndex]
def buildIndexL : FunDecl := lfn (cnt) locals (k, z) {
  z := call str_lit_names();
  k := 0;
  for k < cnt {
    z := call idx_add(k)
  };
  z := call index_freeze();
  return 0
}

/-- `from_le(o, c)`: `fromLe` of the threshold `o` (`optW`: `0` none, `k + 1` some `k`) at the
counter `c`: `k ≤ c`. -/
-- con-ron: ConRon/Arena/Env.lean:260-264 ConRon.Arena.fromLe
@[no_expose, l_impl ConRon.Arena.fromLe]
def fromLeL : FunDecl := lfn (o, c) locals () {
  if o == 0 { return 0 };
  return u64(o - 1 <= c)
}

/-! ## The jobs -/

/-- `record_job(k)`: `recordJob` of record `k` at the view of position `k`: the bracket, the view
(`IStreamIndex.view`), a fresh own layer, `recordCheck` at the solution `J = none` (the `And` pin,
then `check_decl` at `vis = 0`: the twin's `checkRecord` at `none` is `checkDecl`), the bracket closed (the job's own records, `EREC`'s tier 1, with it). -/
-- con-ron: ConRon/Arena/StreamIndex.lean:107-114 ConRon.Arena.IStreamIndex.view
-- con-ron: ConRon/Arena/Justify.lean:323-331 ConRon.Arena.recordCheck
-- con-ron: ConRon/Arena/Justify.lean:333-341 ConRon.Arena.recordJob
@[no_expose, l_impl ConRon.Arena.IStreamIndex.view ConRon.Arena.recordCheck ConRon.Arena.recordJob]
def recordJobL : FunDecl := lfn (k) locals (z, st, ok, v, c) {
  z := call scratch_enter();
  CTL.u64[130] := 0;
  z := call iw_reset();
  st := CTL.u64[133];
  if 4294967294 <= st { abort };
  CTL.u64[133] := st + 1;
  if len(FIRSTS.u64) <= k { abort };
  c := FIRSTS.u64[k];
  CTL.u64[134] := c;
  CTL.u64[135] := k;
  z := call from_le(CTL.u64[172], c);
  CTL.u64[160] := z;
  z := call from_le(CTL.u64[173], c);
  CTL.u64[161] := z;
  ok := call and_pin_ok(k);
  if ok == 0 { fail L.Arena.R_AND_MUST_BE };
  if CTL.u64[224] != 0 { v := call check_record_sol(k, 0) } else { v := call check_decl(k, 0) };
  z := call scratch_drop();
  CTL.u64[130] := 0;
  return 0
}

/-- `check_jobs(j, hi)`: the jobs `j‥hi - 1`, in order (`checkJobList` at the solution `J = none`
over that range, from the worker's state). -/
-- con-ron: ConRon/Arena/Checker.lean:89-99 ConRon.Arena.checkJobList
@[no_expose, l_impl ConRon.Arena.checkJobList]
def checkJobsL : FunDecl := lfn (j, hi) locals (z) {
  for j < hi {
    z := call record_job(j)
  };
  return 0
}

/-- The check phase's functions. -/
def checkerProgL : Prog :=
  [("idx_consts", idxConstsL), ("idx_tables", idxTablesL), ("idx_add", idxAddL),
   ("lit_from", litFromL), ("str_lit_names", strLitNamesL), ("index_freeze", indexFreezeL), ("build_index", buildIndexL),
   ("from_le", fromLeL), ("record_job", recordJobL), ("check_jobs", checkJobsL)]

end L.Arena
