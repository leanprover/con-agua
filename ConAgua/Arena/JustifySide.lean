module

public import ConAgua.Arena.JustifyIface
import ConAgua.Census.Attr

@[expose] public section

/-!
# The comparison's driver steps: the move, the side records, the record mates (lane compare)

These run in the driver, between the solution's check phase and the challenge's index build
(con-ron's `compare_json.rs`: `prepare_d (C)` → `side_records` → `solution_of` → the challenge's
`check_phase`; docs/design/compare.md §0).

* `index_to_solution(cnt)`: the solution's stream index (built by `build_index(cnt)` over its
  `cnt` records) **moved** out of the stream index rows `EIX*`/`TIX*` into the solution's rows
  `SIX*`/`STX*` (same words), the stream rows zeroed, so the challenge's index is built from
  empty in the same arrays (con-ron: `thaw_tier` handing the index back; no twin function). Per
  name tag the copy runs over the rows of the persistent names, `2 · count` words (the name
  store's tier-0 node count): every key of the index is such a name (`IndexKeysIn`). A counter
  word (even index) at or above `2^32` aborts (the solution's rows are below it, `SolR.rows`).
  Then `CTL[225] := CTL[128]` (`next`), `CTL[226] := cnt` (`firsts.size`), `CTL[128] := 0`.
* `side_records(cnt)`: `sideRecordsGo` over the challenge's prepared records `DECL[0‥cnt)`, in
  place: a definition, theorem or opaque record (kinds `2`, `3`, `4`) whose name is no built-in
  axiom's (`builtin_axiom_name`) and whose value mentions `sorryAx` (pin `13`,
  `mentions_const`) becomes the axiom of its statement: its kind word set to `1` (an axiom
  record reads only the name, the universe parameters and the type, which stay).
* `solution_of(cnt)`: `solutionOf`'s record mates (`recordMatesGo` over `DECL[0‥cnt)`, from the
  empty map: the rows `MAT*` zero on entry): for each inductive block, each member's mates list
  becomes its old list followed by the block's names (`matesInsert`), a fresh tier-0 `EREC`
  slice (the scratch tier off). The solution's index is the moved one (`index_to_solution`).
-/

namespace L.Arena

open L.Front (DECL DLP)

/-! ## The move -/

/-- `sd_move_a()`: the rows of the `anonymous` names moved, `EIXA → SIXA`, `TIXA → STXA`, over the
words `0‥2 · count` (the tier-0 node count of `nanonCS`), the source words zeroed; a counter word
(even index) at or above `2^32` aborts. -/
-- con-ron: none — L plumbing of the solution's index (con-ron's `thaw_tier` hands the index back)
@[no_expose] def sdMoveAL : FunDecl := lfn () locals (i, n, v) {
  n := CTL.u64[⟪nanonCS.ca⟫];
  if 134217728 < n { abort };
  n := n << 1;
  i := 0;
  for i < n {
    v := EIXA.u64[i];
    if (i & 1) == 0 && (v >> 32) != 0 { abort };
    SIXA.u64[i] := v;
    EIXA.u64[i] := 0;
    v := TIXA.u64[i];
    if (i & 1) == 0 && (v >> 32) != 0 { abort };
    STXA.u64[i] := v;
    TIXA.u64[i] := 0
  };
  return 0
}

/-- `sd_move_s()`: the rows of the `str` names moved, `EIXS → SIXS`, `TIXS → STXS`, over the
words `0‥2 · count` (the tier-0 node count of `nstrCS`), the source words zeroed; a counter word
(even index) at or above `2^32` aborts. -/
-- con-ron: none — L plumbing of the solution's index (con-ron's `thaw_tier` hands the index back)
@[no_expose] def sdMoveSL : FunDecl := lfn () locals (i, n, v) {
  n := CTL.u64[⟪nstrCS.ca⟫];
  if 134217728 < n { abort };
  n := n << 1;
  i := 0;
  for i < n {
    v := EIXS.u64[i];
    if (i & 1) == 0 && (v >> 32) != 0 { abort };
    SIXS.u64[i] := v;
    EIXS.u64[i] := 0;
    v := TIXS.u64[i];
    if (i & 1) == 0 && (v >> 32) != 0 { abort };
    STXS.u64[i] := v;
    TIXS.u64[i] := 0
  };
  return 0
}

/-- `sd_move_n()`: the rows of the `num` names moved, `EIXN → SIXN`, `TIXN → STXN`, over the
words `0‥2 · count` (the tier-0 node count of `nnumCS`), the source words zeroed; a counter word
(even index) at or above `2^32` aborts. -/
-- con-ron: none — L plumbing of the solution's index (con-ron's `thaw_tier` hands the index back)
@[no_expose] def sdMoveNL : FunDecl := lfn () locals (i, n, v) {
  n := CTL.u64[⟪nnumCS.ca⟫];
  if 134217728 < n { abort };
  n := n << 1;
  i := 0;
  for i < n {
    v := EIXN.u64[i];
    if (i & 1) == 0 && (v >> 32) != 0 { abort };
    SIXN.u64[i] := v;
    EIXN.u64[i] := 0;
    v := TIXN.u64[i];
    if (i & 1) == 0 && (v >> 32) != 0 { abort };
    STXN.u64[i] := v;
    TIXN.u64[i] := 0
  };
  return 0
}

/-- `index_to_solution(cnt)`: the solution's index, built over its `cnt` records, moved into the
solution's rows; its `next` and record count into `CTL[225]`, `CTL[226]`; the stream index
empty (`CTL[128] := 0`). -/
-- con-ron: none — L plumbing of the solution's index (con-ron's `thaw_tier` hands the index back)
@[no_expose] def indexToSolutionL : FunDecl := lfn (cnt) locals (z) {
  z := call sd_move_a();
  z := call sd_move_s();
  z := call sd_move_n();
  CTL.u64[⟪SNEXTC⟫] := CTL.u64[128];
  CTL.u64[⟪SCNTC⟫] := cnt;
  CTL.u64[128] := 0;
  return 0
}

/-! ## The side records -/

/-- `builtin_axiom_name(n)`: `1` if the name handle `n` is one of the seven built-in axioms'
(`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`, `Lean.trustCompiler`,
`Lean.ofReduceNat`, `Lean.ofReduceBool`: pins `32`, `33`, `4`, `13`, `42`, `45`, `46`). -/
-- con-ron: ConRon/Arena/Justify.lean:33-43 ConRon.Arena.builtinAxiomName
@[no_expose, l_impl ConRon.Arena.builtinAxiomName]
def builtinAxiomNameL : FunDecl := lfn (n) locals () {
  if PINS.u64[0] == 0 { abort };
  if n == PINS.u64[33] || n == PINS.u64[34] || n == PINS.u64[5] || n == PINS.u64[14] ||
     n == PINS.u64[43] || n == PINS.u64[46] || n == PINS.u64[47] { return 1 };
  return 0
}

/-- `side_record(k)`: `sideRecord` of record `k`, in place: a definition, theorem or opaque record
(`sideRecordVal`) whose name is no built-in axiom's and whose value mentions `sorryAx` becomes an
axiom record (kind `1`). -/
-- con-ron: ConRon/Arena/Justify.lean:45-52 ConRon.Arena.sideRecordVal
-- con-ron: ConRon/Arena/Justify.lean:54-61 ConRon.Arena.sideRecord
@[no_expose, l_impl ConRon.Arena.sideRecordVal ConRon.Arena.sideRecord]
def sideRecordL : FunDecl := lfn (k) locals (t, b, sa, r) {
  t := DECL.u64[1 + 8 * k];
  if t == 2 || t == 3 || t == 4 {
    b := call builtin_axiom_name(DECL.u64[2 + 8 * k] & 4294967295);
    if b != 0 { return 0 };
    sa := call pin_at(13);
    r := call mentions_const(sa, DECL.u64[6 + 8 * k] & 4294967295);
    if r != 0 { DECL.u64[1 + 8 * k] := 1 };
    return 0
  };
  return 0
}

/-- `side_records(cnt)`: `sideRecordsGo` over the records `0‥cnt - 1`, in place. -/
-- con-ron: ConRon/Arena/Justify.lean:63-70 ConRon.Arena.sideRecordsGo
@[no_expose, l_impl ConRon.Arena.sideRecordsGo]
def sideRecordsL : FunDecl := lfn (cnt) locals (k, z) {
  k := 0;
  for k < cnt {
    z := call side_record(k)
  };
  return 0
}

/-! ## The record mates -/

/-- `sd_copy_prev(d, s, l)`: `EREC[d‥d + l) := EREC[s‥s + l)` (tier 0; a mates list's old
names). -/
-- con-ron: none — L plumbing of the mates' lists (the twin's `nidxAppend` copies a `List`)
@[no_expose] def sdCopyPrevL : FunDecl := lfn (d, s, l) locals (i) {
  i := 0;
  for i < l {
    EREC⟨0⟩[d + i] := EREC⟨0⟩[s + i]
  };
  return 0
}

/-- `sd_copy_names(d, bo, bl)`: the names of the inductive block's members `DLP[bo‥bo + bl)`
(record pointers into `DLP`) into `EREC[d‥d + bl)` (tier 0; the twin's `block.map (·.name)`). -/
-- con-ron: none — L plumbing of the mates' lists (the twin's `nidxAppend` copies a `List`)
@[no_expose] def sdCopyNamesL : FunDecl := lfn (d, bo, bl) locals (j, s) {
  j := 0;
  for j < bl {
    s := DLP.u64[bo + j];
    EREC⟨0⟩[d + j] := DLP.u64[s + ⟪CI.cv + CV.name⟫] & 4294967295
  };
  return 0
}

/-- `mates_insert(bo, bl, j)`: `matesInsert` over the block's members from `j`: each member's
mates list becomes its old list followed by the block's `bl` names, a fresh tier-0 slice. -/
-- con-ron: ConRon/Arena/Justify.lean:156-163 ConRon.Arena.matesInsert
@[no_expose, l_impl ConRon.Arena.matesInsert]
def matesInsertL : FunDecl := lfn (bo, bl, j) locals (s, b, o, l, d, z) {
  if bl <= j { return 0 };
  s := DLP.u64[bo + j];
  b := DLP.u64[s + ⟪CI.cv + CV.name⟫] & 4294967295;
  (o, l) := call mates_get(b);
  d := call erec_alloc(l + bl);
  if o != 0 { z := call sd_copy_prev(d, o - 1, l) };
  z := call sd_copy_names(d + l, bo, bl);
  z := call mates_set(b, d + 1, l + bl);
  z := call mates_insert(bo, bl, j + 1);
  return 0
}

/-- `solution_of(cnt)`: `solutionOf`'s record mates, `recordMatesGo` over the records
`0‥cnt - 1` (the rows `MAT*` empty on entry), with the scratch tier off (the lists persist). -/
-- con-ron: ConRon/Arena/Justify.lean:165-171 ConRon.Arena.recordMatesGo
-- con-ron: ConRon/Arena/Justify.lean:173-178 ConRon.Arena.solutionOf
@[no_expose, l_impl ConRon.Arena.recordMatesGo ConRon.Arena.solutionOf]
def solutionOfL : FunDecl := lfn (cnt) locals (k, z) {
  if CTL.u64[1] != 0 { abort };
  k := 0;
  for k < cnt {
    if DECL.u64[1 + 8 * k] == 6 {
      z := call mates_insert(DECL.u64[3 + 8 * k], DECL.u64[4 + 8 * k], 0)
    }
  };
  return 0
}

/-- This module's functions. -/
def justifySideProg : Prog :=
  [("sd_move_a", sdMoveAL), ("sd_move_s", sdMoveSL), ("sd_move_n", sdMoveNL),
   ("index_to_solution", indexToSolutionL),
   ("builtin_axiom_name", builtinAxiomNameL), ("side_record", sideRecordL),
   ("side_records", sideRecordsL),
   ("sd_copy_prev", sdCopyPrevL), ("sd_copy_names", sdCopyNamesL),
   ("mates_insert", matesInsertL), ("solution_of", solutionOfL)]

end L.Arena
