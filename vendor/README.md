# Vendored proofs

This directory holds Lean sources copied in from two upstream repos, so that
con-agua builds everything with one `lake build` on our pinned toolchain
(`leanprover/lean4:nightly-2026-10-20`, via a Kraken fork — see "Toolchain
switch" below; originally `nightly-2026-09-21`). Both upstreams pin
`leanprover/lean4:v4.35.0`; we did not change their actual proof content
except where noted below.

## Toolchain switch: nightly-2026-09-21 → nightly-2026-10-20 (Kraken fork)

Kraken's author recommended building against their fork
(`https://github.com/sgraf812/kraken`, branch `vcgen`, rev
`ba12834902fd19e837c97d0e5ea585d41348ee7e`, which has `Program.wp` vcgen
support) rather than upstream `AeneasVerif/kraken`. That fork sits on
`leanprover/lean4:nightly-2026-10-20`, so `lean-toolchain` and the `Kraken`
`[[require]]` in `lakefile.toml` both moved together. `lake update` re-pins
`lake-manifest.json`.

This surfaced real `grind`/compiler regressions between the two nightlies
(none are Aeneas/Mathlib-related):

1. **`withPtrEq` really did need vendoring** (the task's own prediction).
   Upstream Lean deprecated the old *safe* `withPtrEq (a b) (k) (h) : Bool :=
   k ()` (`@[implemented_by withPtrEqUnsafe]`) on 2026-09-21 in favor of a
   now-`unsafe def withPtrEq ... := withPtrEqUnsafe a b k h` — so it stopped
   being usable in a kernel-checked declaration (and, as a knock-on, using it
   anyway crashed the compiler's IR pass instead of giving a clean error —
   see `docs/gaps/withptreq-csimp-compiler-panic.lean`, a 15-line standalone
   reproducer). Fix: `vendor/con-leche/ConLeche/Util/PtrEq.lean` restores the
   *old* shape verbatim under `ConLeche.withPtrEq`, built from the still-public
   `withPtrEqUnsafe`. Three call sites changed to use it (one line each,
   `import all Init.Util` → `public import ConLeche.Util.PtrEq`, plus
   qualifying the two bare `withPtrEq` calls that needed it in a `public`
   declaration as `ConLeche.withPtrEq`): `ConLeche/Kernel/Name.lean`,
   `ConLeche/Driver/OwnerParse.lean`, `ConLeche/Verify/Cached/ParInstall.lean`.
   `ConLeche/Kernel/Expr.lean` also needed its `withPtrEqDecEq` call updated to
   a new signature upstream added alongside the deprecation (it now takes the
   caller's own safe `withPtrEq` plus a `∀ a b k h, withPtrEq a b k h = k ()`
   proof as explicit arguments, rather than assuming a single project-global
   one) — one line, `withPtrEqDecEq a b (...)` →
   `withPtrEqDecEq ConLeche.withPtrEq (fun _ _ _ _ => rfl) a b (...)`.

2. **One single-line `grind` fix landed**: `ConLeche/Verify/Cached/DiscC3.lean`,
   `iotaRecC_spec`'s `<;> finish` → `<;> finish [Expr.WScoped.of_not_hasFvar]`.
   The goal needed `rhs.hasFvar = false → WScoped d rhs` and `grind` no longer
   finds this itself via the `sym only [...]`-registered forward-chaining
   route (`Expr.WScoped.of_not_hasFvar`'s own `d` is unconstrained by its
   antecedent, so it can't be a `grind_pattern`; passing it straight to
   `finish` instead works fine).

3. **One `grind` regression did NOT get a one-line fix**:
   `ConLeche/Verify/Cached/KnotC.lean`'s five memo-wrapper proofs
   (`memoEI_{whnfCore,whnf,infer,inferIO}_spec`, `memoBI_defeq_spec`'s
   siblings) each do `<;> finish` after a `vcgen` that needs, among other
   things, a fact like `CSOK.whnfCoreCheap_hit`'s conclusion
   `Runs (...) r ∧ Expr.WScoped d r`. On nightly-2026-10-20, `grind`'s
   `grind_pattern`-triggered instance of that lemma still fires (confirmed via
   `set_option grind.debug true`-style diagnostics: `CSOK.whnfCoreCheap_hit`
   instance count 1) but the derived *conjunction* is not re-split into a
   usable `Expr.WScoped d r` fact — the negated goal `¬WScoped d x` is never
   contradicted. Splitting the lemma into two (one per conjunct, each its own
   `grind_pattern`) did not help either: the split-off `_wscoped` lemma itself
   fires (instance count 1) but *still* doesn't close the goal, so this is not
   merely "the conjunction isn't split", it looks like a deeper difference in
   how a `grind_pattern`-triggered instance feeds back into contradiction
   detection on this nightly. Tried and reverted: passing the `_hit` lemma
   directly as a `finish [...]` hint (changes grind's auto-derived trigger
   pattern for the worse — it drops the cache-read anchor term entirely),
   raising `finish`'s `gen` parameter, both of the above together. Not
   minimized to a standalone reproducer (would need a non-trivial amount of
   `CSOK`/memo-map scaffolding) — this is the one place a real investigation
   is still owed, filed here rather than attempted further.

   **Consequence**: `ConLeche.Verify.Cached.KnotC` and everything that
   transitively imports it — 124 modules, computed by script and listed in
   full in the `lakefile.toml` comment above the `ConLeche` `[[lean_lib]]` —
   do not build on this toolchain. That includes `ConLeche` (the bare
   aggregator), `ConLeche.MainTheorem`, essentially all of `ConLeche.Model.*`
   (~100 of 234 files; the untouched ~134 still build, just not via a single
   glob prefix — see the generated per-module `globs` list) and most of
   `ConLeche.Verify.Cached.*`. All are still vendored (every `.lean` file is
   present on disk, byte-identical to upstream except where noted above); they
   are simply not in the `ConLeche` lib's buildable `globs`/`roots`, which were
   regenerated (a short Python script, computing the transitive import closure
   of the still-good tier roots and checking it has zero edges into the
   excluded set — see the script's output process in this session; not
   committed as a file) as an exact per-module list rather than directory
   prefixes, specifically so the excluded ~124 don't get swept in by a
   broader "ConLeche.Verify.+"-style glob.

   This also blocks `ConRonBridge` (see below): the modules it needs from
   `ConLeche.Verify.Cached` (`GenRecC`, `NestPosC`, `BlockRunC`, `TargetRecC`)
   all transitively import `KnotC`.

**A Lake quirk found along the way** (unrelated to the toolchain bump, but
discovered while reworking the glob list): when a `lean_lib` has *both* a
bare-file module in its `roots` (e.g. `"ConLeche.Kernel.Basis"`, for
`ConLeche/Kernel/Basis.lean`, which sits beside a `ConLeche/Kernel/Basis/`
directory of further submodules) *and* a `globs` entry, that bare-file root
can silently fail to be scheduled as a build job at all — `lake build` reports
success for the whole library yet the bare file's `.olean` was never produced,
and a *separate* library that imports it then fails with "object file ... does
not exist" (not a source error). Workaround used throughout: every root here
is **also** listed verbatim (no `+`) in `globs`, which reliably schedules it.
We hit the same thing earlier for `ConRonArena`'s own root (`ConRon.Arena`,
fixed by dropping `ConRonArena`'s `globs` entirely, since that library's
`roots` already reaches everything it needs by import).

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

**Content changes to vendored `.lean` files**: five one-line/few-line patches,
all from the toolchain switch (see above), none from the original
nightly-2026-09-21 vendoring: `ConLeche/Kernel/Name.lean`,
`ConLeche/Kernel/Expr.lean`, `ConLeche/Driver/OwnerParse.lean`,
`ConLeche/Verify/Cached/ParInstall.lean` (all `withPtrEq`-related), and
`ConLeche/Verify/Cached/DiscC3.lean` (the one `grind` fix). Plus one new
vendored file, `ConLeche/Util/PtrEq.lean`. Every other `.lean` file under
`vendor/con-leche/` is still byte-identical to the reference clone.

**`withPtrEq`**: needed a shim after all, just not on the toolchain we
first targeted — see "Toolchain switch" above.

**Patches in our own `lakefile.toml` (none needed vendored-file edits for
these two):**

1. Per-lib `leanOptions = {autoImplicit = true, relaxedAutoImplicit = true}`
   on the `ConLeche` `[[lean_lib]]`. con-leche's own lakefile sets neither
   option (so its files rely on Lean's defaults, both `true`); con-agua's
   package-level `[leanOptions]` sets both `false`. Without the per-lib
   override, files such as `ConLeche/Frontend/Scan/Types.lean`'s
   `IdTable (α : Type)` API (`α` mentioned, never rebound) fail to elaborate.
2. `srcDir = "vendor/con-leche"`, `roots = []`, and an exact (non-`+`) `globs`
   entry per buildable module (~550, generated by script — see "Toolchain
   switch" above for why: a broad `"ConLeche.+"` glob would sweep in the
   ~124 `KnotC`-regression modules, and `roots`-only misses orphan modules
   nothing imports, same as upstream's own comments note for their own libs).

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
`leanprover/lean4:nightly-2026-10-20` (the Kraken fork's toolchain), for the
~550 modules in the `globs` list; only pre-existing upstream `sorry`
warnings. The ~124 modules excluded by the `KnotC` regression (see above)
are not built by this target but remain on disk.

**Build time**: `lake build` (the whole project: `ConAgua` + `ConLeche` +
`ConRonArena`) from completely clean (`lake clean`, `rm -rf .lake/build`,
including re-fetching `Kraken`): **560 jobs, ~44s wall** (`user` ~6 min —
96 cores). Reproduced twice. `ConLeche` alone is the bulk of that (~550 of
the 560 jobs). The priority subset (`ConLeche.Frontend.Scan.*`, 8 modules)
was ~16s of that once the rest is cached, or ~40s fully cold, back when it
was measured standalone on nightly-2026-09-21 (first landed/merged
separately, per the task's priority); it is included unchanged in the
current `globs` list.

### History (three merges to `master` on this branch)

1. First landed only `ConLeche.Frontend.Scan.{Types,Fast,Naive,Equiv,Equiv/*}`
   (the byte scanner con-agua's Stage A needs first, `docs/survey.md` §1.4),
   with the same per-lib `leanOptions` patch, on nightly-2026-09-21. At that
   point a full standalone trial build of all of `ConLeche/` (con-leche's own
   lakefile, no `autoImplicit` override) got to 1105/1109 jobs, with the
   *only* failures being `ConLeche.Frontend.Prelude` / `ConLeche.Kernel.NatOpPins`
   — both from a missing `pins/` directory, not a source incompatibility.
2. Then the rest of `ConLeche` landed on nightly-2026-09-21: 1134 jobs,
   zero errors, ~1m57s wall cold, after adding `pins/` and
   `scripts/natop_prefix.json`. No `withPtrEq` issue and no `grind` issue
   turned up on that toolchain.
3. Then the toolchain switch (this README's current state): nightly-2026-09-21
   → nightly-2026-10-20 via the Kraken fork, the `withPtrEq` shim, the one
   `grind` fix, the `KnotC`-regression exclusion (~124 modules), and
   `ConRonArena` joining `defaultTargets` (it was already vendored and
   buildable, just not yet wired into the default build).

## vendor/con-ron — `ConRon` lib

Source: `_tmp/ref/con-ron/proof/ConRon/` (rev `4c9eaf7`), copied verbatim (no
edits) to `vendor/con-ron/ConRon/`, plus the repo-root `ConRon.lean`
aggregator — 327 files total. con-ron's own `proof/lakefile.toml` defines
three relevant libs: `ConRon` (roots `["ConRon"]`, i.e. the bare aggregator —
this is actually the Aeneas-refinement tier, `ConRon.Generated` +
`ConRon.Refine.*`, task #97-SWAP's history in `ConRon.lean`'s own header
explains the confusing name), `ConRonArena` (`ConRon.Arena.*`, the arena
checker, (B) in DESIGN.md §8) and `ConRonBridge` (`ConRon.Bridge.*`,
Theorem 1, the bridge from (B) to con-leche's pure checker). We only define
`ConRonArena` and `ConRonBridge` (never the bare `"ConRon"` root, which pulls
in the Aeneas tier).

**Aeneas/Mathlib**: not needed by Arena or Bridge. Verified by grep (no
`import` of `Aeneas`, `Mathlib`, `ConRon.Refine`, `ConRon.Refine2` or
`ConRon.Generated` anywhere under `ConRon/Arena/` or `ConRon/Bridge/` — the
handful of hits for those strings are comments/docs, not import lines) and
by the successful build below with no Aeneas/Mathlib dependency declared at
all. This matches con-ron's own lakefile comments ("imports con-leche's
kernel types ... and nothing from `ConRon.Refine`" / "no `ConRon.Refine`, no
Aeneas, no Mathlib"). So the ~1 hour budget for "check whether Aeneas builds
on our nightly / Mathlib has a compatible revision" was not spent: it
genuinely wasn't needed for the modules we vendor as buildable.
`ConRon.Refine`, `ConRon.Refine2` and `ConRon.Generated` (the Aeneas-model
and Theorem-2 tiers) **are vendored** (the files are on disk under
`vendor/con-ron/ConRon/{Refine,Refine2,Generated}/`) but excluded from both
libs' `globs`/`roots` — they would need Aeneas (which in turn needs a
patched Lean build local to con-ron, `scripts/setup-aeneas-lean.sh`) and
Mathlib, neither attempted.

### `ConRonArena` — builds clean

`roots = ["ConRon.Arena"]`, no `globs` (see the Lake-quirk note above: adding
`globs = ["ConRon.Arena.+"]` here actively broke the build — it made the bare
`ConRon.Arena` root module not get scheduled, so the next library over
importing it failed with a missing-object-file error, even though
`lake build ConRonArena` itself reported success). `roots` alone reaches
everything via `ConRon/Arena.lean`'s own import list; the handful of
`*Test.lean` files under `ConRon/Arena/` (not imported by anything, an
orphan-module situation like the ones `globs` is normally for) are
consequently *not* built — which happens to match "skip tests".

One patch, `vendor/con-ron/ConRon/Arena/WFProofs.lean`, theorem
`Tbl.node?_push_eq` (around line 1269): `cases t; simp only [Tbl.push,
Tbl.node?, Tbl.size, Array.getElem?_push]` left an unsolved goal of the shape
`X = X` (both sides syntactically printed identically, but not
`Eq.refl`-closed by `simp only`'s own closing step on this nightly — likely
the same family of toolchain-vs-`simp`/instance-resolution change as the
`ConLeche` `grind` issues, not investigated further since one `rfl` fixes
it). Patch: appended `; rfl` to that one tactic block. One line changed.

Builds (and was already building, with the same one-line `WFProofs.lean`
patch, before the toolchain switch — this part of con-ron needed no new
fix for nightly-2026-10-20): **220 jobs, 0 errors, ~36s wall** with
`ConLeche`/`Kraken` already built, or ~2m with everything cold.

### `ConRonBridge` — does not build (not in `defaultTargets`)

`roots = ["ConRon.Bridge"]`, `globs = ["ConRon.Bridge.+"]` (con-ron's own
lakefile uses exactly this shape and comments that the tier's eighty-three
modules are siblings, not all reachable from the root — unlike Arena, this
one really does need the glob). Two independent blockers, confirmed on
nightly-2026-10-20, neither Aeneas/Mathlib:

1. `ConRon.Bridge.Inductives.BlockWF` and others import
   `ConLeche.Verify.Cached.{GenRecC,NestPosC,BlockRunC,TargetRecC}` directly,
   and *all four* transitively import `ConLeche.Verify.Cached.KnotC` (traced
   with the same reverse-import script used for the exclusion list above),
   which is the broken module (see "Toolchain switch" §3). This is not
   fixable by editing `vendor/con-ron/` at all — the fix has to land in
   `ConLeche/Verify/Cached/KnotC.lean` first.
2. Independently, `ConRon/Bridge/Specs.lean` itself fails: `internLam_spec`
   and three siblings (`vc6.1`-shaped cases, `Ext s₀.store (...).fst` goals
   about `internLam`/similar interning operations preserving the store's
   `Ext`tension invariant) hit `` `finish` failed `` the same way `KnotC`
   does — a derived fact fires (per diagnostics) but doesn't close the goal.
   Not investigated beyond confirming it's a separate failure from (1) (it
   doesn't go through `ConLeche` at all; `ConRon.Bridge.Rel`,
   `ConRon.Bridge.StoreNested`, `ConRon.Bridge.Promote.*` and
   `ConRon.Bridge.Grind` all build fine first).

Before the toolchain switch (on nightly-2026-09-21), `ConRonBridge` had
*different* residual failures (`ConRon.Bridge.Inductives.PosWalks`,
`ConRon.Bridge.Frontend.Lines`, `ConRon.Bridge.Core.Walks.Spine`, three
`finish`/`split`/type-mismatch failures, not yet investigated either) — so
it did not build cleanly even before the switch; the switch changed *which*
modules fail rather than newly breaking a working target. `lake build
ConRonBridge` remains a valid target to re-run and check progress against
either set of issues; it is intentionally left out of `defaultTargets` so
`lake build`'s plain invocation stays green.
