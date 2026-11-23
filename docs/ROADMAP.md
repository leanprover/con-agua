# Roadmap: parked work and known limits

The trusted base and the shape of the final theorem are described in `OVERVIEW.md` §2 (§2.3 "The
trusted base"). The roadmap of 2026-10-21 that stood here (inventory per phase, cost estimates,
lane plans) is history: `git show 4f9bfff9:docs/ROADMAP.md`.

## Parked

Measured and decided against for now; each needs a decision before a lane picks it up.

* **One-word slots in the cons tables** (lane memlay's lever `spk`, `git show
  4f9bfff9:docs/design/memlay.md`). Slot word `fp:16 | mark:1 | stamp:19 | index+1:28`: every table
  becomes a fingerprint table, a fingerprint hit runs the schema's match on the record, growth
  rehashes from the records. Peak RSS, the landed layout (load 3/4, growth in place, 32-bit handle
  fields) against prototype `rec` (the same plus one-word slots): Init 887 → 801 MB, app-lam
  1922 → 1280 MB (con-ron: 0.46 GB on Init). Instructions as with two-word slots (prototypes `rec`
  vs `rec16`: geomean 1.035 vs 1.061, cycles 1.074 vs 1.065). The 19-bit stamp holds 524 287
  scratch resets (Init uses 230 425), so it needs a stamp-wrap arm (vacate the tier-1 tables, as
  the twin's `clear` does at `EPOCH_MAX`; D39's wrap is the model). Estimate 3–5 days: the slot
  format through `ConsLib`/`ConsLibSpec`/`ConsLibRel`/`SlotGrow`/`StoreGrow`, the scratch stamp,
  and a growth obligation per schema.
* **`iw_copy` as a block copy** (lane blkcopy2, `git show 4f9bfff9:docs/design/blkcopy2.md` §4):
  saves 1.3 % instructions on `complete_c03d`, 1.0 % on `complete_c04a`, nothing on Init.
  `copyW` is indexed by fuel and 16 files depend on it, so a fuel-free `copyW` comes first.

## Ideas

Not measured or planned yet; recorded so they are not lost.

* **A verified compiler from L to WebAssembly** (user, 2026-10-25). L's memory model maps directly
  onto Wasm with the multi-memory feature (part of Wasm 3.0): one growable linear memory per word
  array (`memory.grow` for the arrays' growth, `memory.size` for their lengths), the descriptor
  table and the region layout disappear, and bounds checks become Wasm's own traps (a trap is never
  an accept). L's functions, first-order calls, locals and structured control flow have direct
  Wasm counterparts. The proof would replace Kraken's x64 semantics by a Wasm semantics in Lean;
  the L-level proofs and everything above them stay as they are. It would give a checker that runs
  in a browser or any Wasm runtime, with a trusted base of the Wasm engine instead of the x64
  assembler/linker and C harness.

* **A string literal's constructor spine as a loop** (lane ronsync8, after con-ron #169).
  `str_cons_spine` (`Arena/StrLit.lean`) recurses once per character, as the twin's
  `strLitConsSpine` (a `foldr`) does, so a literal's length is L's call depth; con-ron #169 made
  the Rust a loop from the last code point down (the twin unchanged, `spineOnto` proving the loop).
  In L a long literal reaches the stack's capacity and aborts (never an accept). Port it when an
  input needs it: a backward walk over the literal's UTF-8 bytes (or the code points collected
  first) consing onto the spine so far, its model proved against `spineOnto`'s shape.

## Known limits

* **`2^30` `app` nodes and `2^26` other nodes per table and tier** (con-ron task #133, lane
  ronsync: wide `app` handles `tier·2^31 + 2^30 + i`, narrow ones `tier·2^31 + tag·2^26 + i`;
  `X_push` aborts at the cap). con-ron has the same caps (`WIDE_CAP`, `IDX_CAP`,
  `arena/handle.rs`). Before #133 every table held `2^27`; measured then (lane nodecount, one
  `ca_start` run): tier 0 of the `app` table holds 5 210 486 nodes after Init and 89 678 848
  after Mathlib (the input 17.9× larger, the table 17.2×); next `lam` 8.15 M, `forallE` 5.40 M,
  `nstr` 2.23 M, `nnum` 1.96 M, `const` 1.41 M, every other table below 0.2 % of `2^27`; the
  scratch tier's largest high-water mark `app` at 7.3 M on Mathlib. With lams about a tenth of
  apps (Init's ratio), the first table to fill is now `lam` at `2^26`, at about 8× Mathlib's lam
  count, i.e. at roughly 5× the app count the old layout allowed (con-ron's own estimate,
  DESIGN #133). con-ron's counts are identical, store by store, on Init and Mathlib.
* **`2^32` words per array** (the ABI slot of `2^35` bytes, `Compiler/Abi.lean`). Behind the node
  cap (`EREC` reaches it at ~2300× Init). Raising it needs per-array slot sizes (ABI, compiler
  proof, harness): a uniform larger slot exceeds the x86-64 user address space.
* Every other capacity (scratch resets since D39, memo regions and stamps, bank generations, the
  pool's `2^40` words per tier, declaration counts, per-declaration counters and stacks) stays far
  below these two at 100× Mathlib (lane epochwrap's audit, `git show
  4f9bfff9:docs/design/epochwrap.md`).
