module

public import ConAgua.Checker.Entry
public import ConAgua.Arena.JustifyIface

@[expose] public section

/-!
# The compared run's entries (lane compare)

con-ron's `compare_json` (`crates/con-ron-core/src/driver/compare_json.rs`) as three L runs of
`check` on one region, by the mode word, with the worker and the in-place jobs of the parallel
mode between them (docs/design/compare.md §0):

* mode `4`, `check_c1()`: `cap_check`, `pb_check`, `presize_tables`, `intern_reserved_pins`,
  `builtin_prelude`, `front_run` on the challenge's bytes (descriptor `0`), then `cmp_stash`:
  the records so far (the prelude's, the challenge's) copied to `CDECL`, `DECL` cut back to the
  prelude's, the id tables emptied (the twin's second `parseChunks` starts from a fresh parse
  state). Returns `2^63`, or `1` if a line did not apply.
* (the driver points descriptor `0` at the solution's bytes)
* mode `5`, `check_c2()`: `front_run` on the solution's bytes, `prepare_prelude`,
  `intern_all_pins`, `build_index`, `par_compact(1)` (the frozen buffer, header and images: the
  solution's jobs run on a worker region over it, so this region stays the twin's driver state);
  returns `2^63 + k` for the solution's `k` records, or `1`.
* (the solution's jobs, `ca_check_b` on a worker region, `J = none`)
* mode `6`, `check_c3()`: the solution's index moved to the solution's rows
  (`index_to_solution`, con-ron's `thaw_tier` handing the index back), the challenge's records
  back (`cmp_restore`; the twin's `prelude_ix_dup` is the prelude's copy kept in `CDECL`),
  `prepare_prelude`, `side_records`, `solution_of` (the record mates), `build_index`, the flag
  `CTL[224] := 1`, `par_compact(0)`; returns `2^63 + k`.
* (the challenge's jobs in place, `ca_check_seq`, `J = some sol`)
-/

namespace L.Checker

open L L.Arena L.Front

/-- `cmp_stash()`: `DECL` (the prelude's records, then the challenge's) copied to `CDECL`; `DECL`
cut back to the prelude's `CTL[240]` records; the id tables emptied (`front_reset`). -/
-- con-ron: none — L keeps one parse result in `DECL`; the twin's driver holds two `ParseResultD` values
@[no_expose] def cmpStashL : FunDecl := lfn () locals (n, z) {
  if 576460752303423488 <= DECL.u64[0] { abort };
  n := 1 + 8 * DECL.u64[0];
  if len(CDECL.u64) < n { abort };
  if len(DECL.u64) < n { abort };
  copy!(CDECL.u64, 0, DECL.u64, 0, n);
  DECL.u64[0] := CTL.u64[240];
  z := call front_reset();
  return 0
}

/-- `cmp_restore()`: `DECL` := `CDECL` (the prelude's records and the challenge's, as the first
parse left them). -/
-- con-ron: none — L plumbing: the Rust's `prelude_ix_dup` (the prelude's copy for the challenge's preparation) and the second `ParseResultD`
@[no_expose] def cmpRestoreL : FunDecl := lfn () locals (n) {
  if 576460752303423488 <= CDECL.u64[0] { abort };
  n := 1 + 8 * CDECL.u64[0];
  if len(DECL.u64) < n { abort };
  if len(CDECL.u64) < n { abort };
  copy!(DECL.u64, 0, CDECL.u64, 0, n);
  return 0
}

/-- `check_c1()`: the stages to the challenge's parse, then `cmp_stash`. -/
-- con-ron: none — the Rust driver `compare_json` (h1, h2, h3), which the twin states as premises
@[no_expose] def checkC1L : FunDecl := lfn () locals (r, z) {
  z := call cap_check();
  z := call pb_check();
  z := call presize_tables();
  z := call intern_reserved_pins();
  z := call builtin_prelude();
  r := call front_run();
  if r != 0 { return 1 };
  z := call cmp_stash();
  return 9223372036854775808
}

/-- `check_c2()`: the solution's parse, preparation, the pins, its index and its frozen buffer. -/
-- con-ron: none — the Rust driver `compare_json` (h3S, h4S, h5, h6S, h7S), which the twin states as premises
@[no_expose] def checkC2L : FunDecl := lfn () locals (r, z, cnt) {
  r := call front_run();
  if r != 0 { return 1 };
  z := call prepare_prelude();
  z := call intern_all_pins();
  cnt := DECL.u64[0];
  z := call build_index(cnt);
  z := call par_compact(1);
  return 9223372036854775808 + cnt
}

/-- `check_c3()`: the solution's index moved out, the challenge's records back and prepared, its
side records, the record mates, its index, the flag, the buffer's header. -/
-- con-ron: none — the Rust driver `compare_json` (h8S's thaw, h4, hside, hsol, h6, h7), which the twin states as premises
@[no_expose] def checkC3L : FunDecl := lfn () locals (z, cnt) {
  cnt := DECL.u64[0];
  z := call index_to_solution(cnt);
  z := call cmp_restore();
  z := call prepare_prelude();
  cnt := DECL.u64[0];
  z := call side_records(cnt);
  z := call solution_of(cnt);
  z := call build_index(cnt);
  CTL.u64[⟪SOLC⟫] := 1;
  z := call par_compact(0);
  return 9223372036854775808 + cnt
}

/-- The compared run's entry functions. -/
def compareEntryProg : Prog :=
  [("cmp_stash", cmpStashL), ("cmp_restore", cmpRestoreL), ("check_c1", checkC1L),
   ("check_c2", checkC2L), ("check_c3", checkC3L)]

end L.Checker
