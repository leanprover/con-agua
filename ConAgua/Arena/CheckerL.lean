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
  It runs with the scratch tier off, so every record lands in `EREC`'s tier 0.
* `record_job(k)`: `recordJob`: the scratch bracket, the view of position `k` (`CTL[134]` its
  first counter, `CTL[135]` the position), a fresh own layer (the stamp `CTL[133]` bumped,
  `vis = 0`), the `And` pin, then `check_decl(k, 0)`; the tier-1 records dropped with the bracket.
* `check_jobs(j, hi)`: the jobs `j‥hi - 1` in order (`checkJobList` over a range).
-/

namespace L.Arena

open L.Front (DECL)
open L.Ind (IW)

/-! ## The stream index -/

/-- `idx_consts(o, n)`: `insertConsts` over the `n` constant records `IW[o‥o + n)`: each name's row
written if it has none, at the next counter `CTL[128]`, which always moves. -/
-- con-ron: ConRon/Arena/StreamIndex.lean:42-47 ConRon.Arena.insertConsts
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
-- con-ron: ConRon/Arena/StreamIndex.lean:49-54 ConRon.Arena.insertTables
@[no_expose, l_impl ConRon.Arena.insertTables]
def idxTablesL : FunDecl := lfn (o, n, r) locals (j, q, w, c, p, z) {
  j := 0;
  for j < n {
    q := IW.u64[o + j];
    w := EREC⦃q + 2⦄;
    (c, p) := call tbl_base_get(w);
    if c == 0 { z := call tbl_base_set(w, r + 1, q) }
  };
  return 0
}

/-- `idx_add(k)`: `IStreamIndex.add` of record `k`: its first counter, its constants, its tables
(the work pool emptied first: the slices live only for the record). -/
-- con-ron: ConRon/Arena/StreamIndex.lean:56-65 ConRon.Arena.IStreamIndex.add
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

/-- `build_index(cnt)`: `buildIndex` over records `0‥cnt - 1`, from the empty index (zero rows,
`CTL[128] = 0`). -/
-- con-ron: ConRon/Arena/StreamIndex.lean:67-77 ConRon.Arena.buildIndexGo
-- con-ron: ConRon/Arena/StreamIndex.lean:79-82 ConRon.Arena.buildIndex
@[no_expose, l_impl ConRon.Arena.buildIndexGo ConRon.Arena.buildIndex]
def buildIndexL : FunDecl := lfn (cnt) locals (k, z) {
  k := 0;
  for k < cnt {
    z := call idx_add(k)
  };
  return 0
}

/-! ## The jobs -/

/-- `record_job(k)`: `recordJob` of record `k` at the view of position `k`: the bracket, the view
(`IStreamIndex.view`), a fresh own layer, `recordCheck` (the `And` pin, then `check_decl` at
`vis = 0`), the bracket closed (the job's own records, `EREC`'s tier 1, with it). -/
-- con-ron: ConRon/Arena/StreamIndex.lean:84-89 ConRon.Arena.IStreamIndex.view
-- con-ron: ConRon/Arena/StreamIndex.lean:91-99 ConRon.Arena.recordCheck
-- con-ron: ConRon/Arena/StreamIndex.lean:101-109 ConRon.Arena.recordJob
@[no_expose, l_impl ConRon.Arena.IStreamIndex.view ConRon.Arena.recordCheck ConRon.Arena.recordJob]
def recordJobL : FunDecl := lfn (k) locals (z, st, ok, v) {
  z := call scratch_enter();
  CTL.u64[130] := 0;
  z := call iw_reset();
  st := CTL.u64[133];
  if 4294967294 <= st { abort };
  CTL.u64[133] := st + 1;
  if len(FIRSTS.u64) <= k { abort };
  CTL.u64[134] := FIRSTS.u64[k];
  CTL.u64[135] := k;
  ok := call and_pin_ok(k);
  if ok == 0 { fail L.Arena.R_AND_MUST_BE };
  v := call check_decl(k, 0);
  z := call scratch_drop();
  CTL.u64[130] := 0;
  return 0
}

/-- `check_jobs(j, hi)`: the jobs `j‥hi - 1`, in order (`checkJobList` over that range, from the
worker's state). -/
-- con-ron: ConRon/Arena/Checker.lean:85-95 ConRon.Arena.checkJobList
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
   ("build_index", buildIndexL), ("record_job", recordJobL), ("check_jobs", checkJobsL)]

end L.Arena
