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

## Known limits

* **`2^27` nodes per table and tier** (handle `tag·2^28 + tier·2^27 + i`; `X_push` aborts at
  `c ≥ 2^27`). con-ron has the same cap (`IDX_CAP = 2^27`, `arena/handle.rs`). Both reach it at
  about 26× Init (app nodes) or 1.5× Mathlib: the binding capacity limit of the project.
  Measured (lane nodecount, one `ca_start` run, node counts read from `CTL`): tier 0 of the `app`
  table holds 5 210 486 nodes after Init (3.9 % of `2^27`) and 89 678 848 after Mathlib (66.8 %;
  the input is 17.9× larger, the table 17.2×). Next: `lam` 8.15 M (6.1 %), `forallE` 5.40 M
  (4.0 %), `nstr` 2.23 M, `nnum` 1.96 M, `const` 1.41 M (1.0–1.7 %), every other table below
  0.2 %. The scratch tier is far from the cap: its largest high-water mark (nonzero records
  left behind) is `app` at 7.3 M (5.4 %) on Mathlib, 0.39 M on Init. Assuming the tier-0 `app`
  count grows linearly with input size (Init to Mathlib: 0.96 × linear), it reaches `2^27` at
  about 1.5× Mathlib (≈ 9 GB of ndjson, ≈ 1.05 M declarations).
  con-ron's counts are identical, store by store, on Init and Mathlib (an instrumented con-ron,
  same day): theorem bodies are interned into tier 0 by the parse in both, before any theorem is
  recognised, so neither keeps more than the other.
  A cheaper lift (user idea, 2026-10-25): a non-uniform constructor encoding, e.g. tag prefix `0`
  for `app` and `1xxx` for the fifteen other kinds, leaves `app` 30 bits for tier and index
  (`2^30` per tier, 8×) while every other kind keeps `2^27`; still 32-bit handles, a branch on
  the top bit when decoding, and the same change in con-ron to stay a close twin.
  Lifting it means wider handles in both twins. Decision (user, 2026-10-25): keep it, matching
  the twin; "there is no need to surpass con-ron in scaling".
* **`2^32` words per array** (the ABI slot of `2^35` bytes, `Compiler/Abi.lean`). Behind the node
  cap (`EREC` reaches it at ~2300× Init). Raising it needs per-array slot sizes (ABI, compiler
  proof, harness): a uniform larger slot exceeds the x86-64 user address space.
* Every other capacity (scratch resets since D39, memo regions and stamps, bank generations, the
  pool's `2^40` words per tier, declaration counts, per-declaration counters and stacks) stays far
  below these two at 100× Mathlib (lane epochwrap's audit, `git show
  4f9bfff9:docs/design/epochwrap.md`).
