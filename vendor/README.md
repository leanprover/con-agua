# Vendored proofs

This directory holds Lean sources copied in from two upstream repos, so that
con-agua builds everything with one `lake build` on our pinned toolchain
(`leanprover/lean4:nightly-2026-09-21`). Both upstreams pin
`leanprover/lean4:v4.35.0`; we did not change their actual proof content
except where noted below.

Reference (read-only) clones used for copying:
`_tmp/ref/con-leche` (rev `103562ba1c46cee26f134d0435765adcb5d22486`) and
`_tmp/ref/con-ron` (rev `4c9eaf7`, its `proof/` directory). Both are
upstream `leanprover/con-leche` resp. the sibling `con-ron` repo. con-ron's
own pin of con-leche is the same `103562b` revision.

## vendor/con-leche — `ConLeche` lib

Source: `_tmp/ref/con-leche` (rev `103562b`), copied to `vendor/con-leche/`:

* `ConLeche.lean` (the repo-root aggregator module) and the whole `ConLeche/`
  tree (567 `.lean` files, ~236k lines): `Kernel`, `Verify`, `SetTheory`,
  `Term`, `SetModel`, `Semantics`, `Model`, `Cached`, `Driver`, `Frontend`
  (incl. `Frontend.Scan.*`, landed first — see history below), `PinGen`,
  `Complete`, `Challenge`.
* `pins/` (the committed pin-certificate dumps and the built-in-prelude
  `.ndjson`, ~2 MB) — needed verbatim by `ConLeche/Kernel/NatOpPins.lean`
  and `ConLeche/Frontend/Prelude.lean` (`include_str`, see below).
* `scripts/natop_prefix.json` only (256 KB data file, `include_str`'d by
  `ConLeche/PinGen.lean`) — the rest of `scripts/` (shell/python tooling)
  was not copied.

**Not copied** (per the task's "skip tests/fixtures/large data, skip
Rust/C/binaries", and because con-agua's proof chain does not need them):
`tests/` (28 MB, fixtures/test driver), `whitepaper/` (2.4 MB, its own
`WhitepaperFragment` lib, self-contained, not on our chain), `pinners/`,
`perf-data/`, the rest of `scripts/`, `bridge/lean4lean-model/` (a separate
nested Lake package bridging to `lean4lean`, unrelated to our chain), and
the top-level `Main.lean` / `PinDump.lean` (con-leche's CLI binary and the
pin-dump generator executable — entry points we don't need; nothing in
`ConLeche.*` imports them).

**Content changes to vendored `.lean` files: none.** Every `.lean` file
under `vendor/con-leche/` is byte-identical to the reference clone.

**`withPtrEq`**: not needed as a shim. It's used in several places in
`ConLeche.*` (`Cached/ExprNodes.lean`, `Cached/ExprOpsC.lean`,
`Kernel/Name.lean`, `Driver/OwnerParse.lean`, `Verify/Cached/ParInstall.lean`)
and all of them build unmodified on nightly-2026-09-21 — it was not in fact
removed upstream of this toolchain, so no vendored replacement was needed.

**Patches, all in our own `lakefile.toml`, none in vendored files:**

1. Per-lib `leanOptions = {autoImplicit = true, relaxedAutoImplicit = true}`
   on the `ConLeche` `[[lean_lib]]`. con-leche's own lakefile sets neither
   option (so its files rely on Lean's defaults, both `true`); con-agua's
   package-level `[leanOptions]` sets both `false`. Without the per-lib
   override, files such as `ConLeche/Frontend/Scan/Types.lean`'s
   `IdTable (α : Type)` API (`α` mentioned, never rebound) fail to elaborate.
2. `srcDir = "vendor/con-leche"`, `roots = ["ConLeche"]`,
   `globs = ["ConLeche.+"]` — the glob (not just `roots`) is needed so that
   orphan-looking modules (nothing in `ConLeche.*` imports `ConLeche.PinGen`
   or `ConLeche.Challenge`, same as upstream's own comments note for their
   own libs) still get built, matching "`lake build` builds everything".

**Pin files, vendored verbatim, no generation attempted**: con-leche's pin
mechanism (`pins/README.md`) tries several committed pin variants at
runtime and "accepts dumps from any Lean version" — it is data, not
toolchain-specific source, so the existing `pins/*.json` /
`pins/*.ndjson` files needed no regeneration for the new toolchain.

**`sorry`s**: `ConLeche/Challenge.lean` (upstream's own "challenge" half of
a comparator pair, deliberately not sorry-free, not in anyone's import
closure) has 2 pre-existing `sorry`s. These are upstream's, present
unchanged at rev `103562b`; con-agua adds none.

**Build**: `lake build ConLeche` builds clean, **zero errors**, on
`leanprover/lean4:nightly-2026-09-21`; only pre-existing upstream `sorry`
warnings.

**Build time**: `lake build ConLeche` from completely clean (`lake clean`,
`rm -rf .lake/build`; `Kraken` already materialized): **1134 jobs, ~1m57s
wall** (`user` ~13 min — this machine has 96 cores, so the parallel build
makes good use of them). The priority subset (`ConLeche.Frontend.Scan.*`
alone, 18 jobs) is ~16s of that once the rest is cached, or ~40s fully cold
(including fetching/building the `Kraken` dependency) — this is the subset
that landed and merged to `master` first, per the task's priority.

### History (two merges to `master` on this branch)

1. First landed only `ConLeche.Frontend.Scan.{Types,Fast,Naive,Equiv,Equiv/*}`
   (the byte scanner con-agua's Stage A needs first, `docs/survey.md` §1.4),
   with the same per-lib `leanOptions` patch. At that point a full
   standalone trial build of all of `ConLeche/` (con-leche's own lakefile,
   no `autoImplicit` override) got to 1105/1109 jobs, with the *only*
   failures being `ConLeche.Frontend.Prelude` / `ConLeche.Kernel.NatOpPins`
   — both from a missing `pins/` directory, not a source incompatibility.
2. Then the rest of `ConLeche` landed (this README's current state), adding
   `pins/` and `scripts/natop_prefix.json` so those two modules (and
   `ConLeche.PinGen`, which needs the latter) build too. No further source
   issues turned up.

## vendor/con-ron — `ConRon` lib

Source: `_tmp/ref/con-ron/proof/ConRon/` (rev `4c9eaf7`), copied to
`vendor/con-ron/ConRon/`.

See the `[[lean_lib]] name = "ConRon"` entries in `lakefile.toml` and the
module-by-module build report below for what builds and what is excluded.
