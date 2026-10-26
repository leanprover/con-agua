# Vendored proofs

The files under `vendor/con-ron/` and `vendor/con-leche/` are copied from
[con-ron](https://github.com/leanprover/con-ron) and
[con-leche](https://github.com/leanprover/con-leche), both licensed under the
Apache License 2.0, the same license as this repository (see [`LICENSE`](../LICENSE)).
Our changes to them are the patches in `vendor/patches/`.

This directory holds Lean sources copied in from two upstream repos, so that
con-agua builds everything with one `lake build` on our pinned toolchain
(`leanprover/lean4:nightly-2026-10-20`, via a Kraken fork — see "Toolchain
switch" below; originally `nightly-2026-09-21`). Both upstreams pin
`leanprover/lean4:v4.35.0`; we did not change their actual proof content
except where noted below.

## Layout: upstream revisions + a patch series

`vendor/UPSTREAM` names the vendored revisions of con-ron and con-leche. The
vendored file sets are fixed: con-ron's `proof/ConRon/**` and
`proof/ConRon.lean` (into `vendor/con-ron/`), con-leche's `ConLeche/**`,
`ConLeche.lean`, `pins/**` and `scripts/natop_prefix.json` (into
`vendor/con-leche/`). On top of the pristine files sit the patches
`vendor/patches/<repo>/NNNN-*.patch`, applied in order; each starts with a
description of why. `scripts/bump-con-ron.sh --check` verifies that
`vendor/` is exactly that; `--refresh-patches` rewrites the patches from
`vendor/` after an edit (keeping descriptions); `scripts/bump-con-ron.sh
<rev>` moves to a new con-ron revision (PLAN.md, "Bumping the twin").
The sections below describe each patch in detail; the revisions they name
are the ones of the first vendoring (con-ron `4c9eaf7`, con-leche `103562b`).

Bumps since (DESIGN.md has the details):
* 2026-10-21: con-ron `4c9eaf7` → `12752ca7`, con-leche `103562b` → `ae1f3198`
  (the eager tower keeps its memos). One conflict, `ConRon/Bridge/Core/Memo.lean`:
  `con-ron/0002` now adds `dsimp only` before `vcgen` in the new
  `enterEager_spec`/`leaveEager_spec` instead of in the removed
  `takeModeMemos_spec`/`putModeMemos_spec`.
* 2026-10-26: con-ron `12752ca7` → `ed864140`, con-leche `ae1f3198` → `0d2f467b`
  (con-leche tasks #362–#365, con-ron tasks #128–#131: projection tables leave the constants,
  no reserved projection-name shape, type pins with a boolean pin-variant loop, escaped display
  rendering). `con-ron/0002` conflicted in seven `ConRon/Bridge` files
  (`Checker/{Base,Basis,Split}`, `Inductives/{BlockTail,GenRec,Rel,StructInstall}`); resolved by
  taking upstream and re-applying the same three toolchain patterns (`try replace … :=
  AM.pure_bind_ok …`, `dsimp +instances only [IFEnv.restrictTo]` after the `restrictTo` simp).

Patches at the first vendoring:

| patch | what |
|---|---|
| `con-leche/0001-withptreq-shim.patch` | `ConLeche.withPtrEq` shim and its three call sites, `withPtrEqDecEq`'s new signature |
| `con-leche/0002-discc3-grind-finish.patch` | `iotaRecC_spec`: one lemma passed to `finish` |
| `con-leche/0003-knotc-vcgen-conj-split.patch` | five `CSOK.*_hit_ws` companion lemmas (the `vcgen` ∧-split) |
| `con-ron/0001-wfproofs-rfl.patch` | `Tbl.node?_push_eq`: a trailing `rfl` |
| `con-ron/0002-bridge-toolchain.patch` | the 31 `ConRon.Bridge` files (three toolchain changes, see "ConRonBridge") |

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

3. **The `KnotC` "grind regression" is a `vcgen` change** (fixed; this was
   the blocker for ~124 `ConLeche` modules and for `ConRonBridge`).
   Root cause: `vcgen` now splits a `∧` postcondition into one VC per
   conjunct (lean4#15487, "split a `∧` on the RHS of a `vcgen` entailment";
   nightly bisect: good nightly-2026-10-05, bad nightly-2026-10-06, still
   bad on nightly-2026-10-21; commit-level: 1e15c3fdf8 = #15487 fails, its
   parent c96933c169 passes, both built from source). `KnotC`'s memo-wrapper specs
   post `CSOK .. ∧ Runs .. r ∧ WScoped d r`, and the memo-hit lemmas
   `CSOK.{whnfCore,whnfCoreCheap,whnf,infer,inferIO}_hit` (conclusion
   `Runs .. r ∧ WScoped d r`) are `grind_pattern`-triggered by the `Runs`
   term. On v4.35.0 the whole conjunction was one VC, so that term was in the
   e-graph while `grind` proved `WScoped`; now the `WScoped` VC has no `Runs`
   term and the lemma cannot fire. (The "instance count 1" seen in the
   failing goal's diagnostics, which the first investigation read as "fires
   but the conjunction is not re-split", does not refer to that VC.)
   Standalone reproducer: `docs/gaps/vcgen-conj-split-grind-trigger.lean`.
   Fix (`ConLeche/Verify/Cached/KnotC.lean`, +40 lines, nothing removed):
   after each of the five `_hit` lemmas, a companion `CSOK.*_hit_ws` lemma
   stating just the `WScoped` conjunct (proved from `_hit`), with its own
   `grind_pattern [conleche_grind] … => CSOK mode env s, s.xC[i]?,
   Expr.WScoped d r` — the `WScoped` term *is* in that VC. No proof text
   changed. With this, all of `ConLeche` builds (incl. `MainTheorem`).

   The same `vcgen` change, plus two other toolchain changes, account for
   every `ConRonBridge` failure; see that section below.

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

**Content changes to vendored `.lean` files**: six small patches,
all from the toolchain switch (see above), none from the original
nightly-2026-09-21 vendoring: `ConLeche/Kernel/Name.lean`,
`ConLeche/Kernel/Expr.lean`, `ConLeche/Driver/OwnerParse.lean`,
`ConLeche/Verify/Cached/ParInstall.lean` (all `withPtrEq`-related),
`ConLeche/Verify/Cached/DiscC3.lean` (the one-line `grind` fix) and
`ConLeche/Verify/Cached/KnotC.lean` (five added companion lemmas, the
`vcgen` ∧-split fix). Plus one new
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
2. `srcDir = "vendor/con-leche"`, `roots = ["ConLeche"]`,
   `globs = ["ConLeche", "ConLeche.+"]` (everything; `roots`-only would miss
   orphan modules nothing imports, as upstream's own comments note; the root
   is repeated in `globs` because of the Lake quirk above). Until the `KnotC`
   fix this was an exact per-module list excluding the ~124 modules above
   `KnotC`.

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
`leanprover/lean4:nightly-2026-10-20` (the Kraken fork's toolchain), all
567 modules (1138 jobs incl. deps), including the bare `ConLeche`
aggregator, `ConLeche.MainTheorem` and the `Verify.Cached` capstone; only
the pre-existing upstream `sorry` warnings in `Challenge.lean`.

**Build time**: `lake build` (the whole project, default targets `ConAgua` +
`ConLeche` + `ConRonArena` + `ConRonBridge`) after `rm -rf .lake/build`
(Kraken already fetched): **1497 jobs, 1m52s wall** (`user` 17m49s, 96
cores), on nightly-2026-10-20 after the `KnotC`/Bridge fixes. Before them
(only ~550 `ConLeche` modules, no Bridge) it was 560 jobs, ~44s wall.

### History

1. First landed only `ConLeche.Frontend.Scan.{Types,Fast,Naive,Equiv,Equiv/*}`
   (the byte scanner con-agua's Stage A needed first),
   with the same per-lib `leanOptions` patch, on nightly-2026-09-21. At that
   point a full standalone trial build of all of `ConLeche/` (con-leche's own
   lakefile, no `autoImplicit` override) got to 1105/1109 jobs, with the
   *only* failures being `ConLeche.Frontend.Prelude` / `ConLeche.Kernel.NatOpPins`
   — both from a missing `pins/` directory, not a source incompatibility.
2. Then the rest of `ConLeche` landed on nightly-2026-09-21: 1134 jobs,
   zero errors, ~1m57s wall cold, after adding `pins/` and
   `scripts/natop_prefix.json`. No `withPtrEq` issue and no `grind` issue
   turned up on that toolchain.
3. Then the toolchain switch: nightly-2026-09-21
   → nightly-2026-10-20 via the Kraken fork, the `withPtrEq` shim, the one
   `grind` fix, the `KnotC`-regression exclusion (~124 modules), and
   `ConRonArena` joining `defaultTargets` (it was already vendored and
   buildable, just not yet wired into the default build).
4. Then (branch `bridge`, the current state) the `KnotC` root cause
   (lean4#15487) and fix, all of `ConLeche` re-enabled, and `ConRonBridge`
   fixed and added to `defaultTargets`.

## vendor/con-ron — `ConRon` lib

Source: `_tmp/ref/con-ron/proof/ConRon/` (rev `4c9eaf7`), copied verbatim
(edits: see the two lib sections below) to `vendor/con-ron/ConRon/`, plus the repo-root `ConRon.lean`
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

### `ConRonBridge` — builds clean (in `defaultTargets`)

`roots = ["ConRon.Bridge"]`, `globs = ["ConRon.Bridge.+"]` (con-ron's own
lakefile uses exactly this shape and comments that the tier's eighty-three
modules are siblings, not all reachable from the root — unlike Arena, this
one really does need the glob). **1424 jobs (incl. its `ConLeche`/`ConRonArena`
deps), 0 errors, no `sorryAx`** in any of the tier's `#print axioms` gates
(`Bridge/Axioms.lean`, `Bridge/*/Axioms.lean`).

It needed 31 files patched (~290 changed lines, every patch site marked
`-- con-agua patch` in the source; `git log -p` of the `bridge` merge has the
full diff). No theorem statement changed, no `sorry`, no new axiom. Every
failure traces to one of three toolchain changes between v4.35.0 and
nightly-2026-10-20 (some were already present on nightly-2026-09-21, which is
why this tier never built there either):

1. **`vcgen` splits a `∧` post into one VC per conjunct** (lean4#15487, see
   "Toolchain switch" §3). Two kinds of breakage:
   * `grind` lost a fact only derivable via a term in a *sibling* conjunct:
     `Bridge/Specs.lean` (`internLamE_spec_view`/`internForallEE_spec_view`:
     `EStore.internBind_spec` now passed as `→` forward lemma, so its
     hypotheses — the capacity guard, present in every VC — trigger it instead
     of the `StoreWF (..internBind..).1` term of one conjunct);
     `ExprOps/Leaves.lean` (two local companion lemmas,
     `SeenGrow.insert_of_leavesEq`/`SeenGrow.drop_insert_of_leavesEq`, keying
     the `LeavesEq.black` → `BlackA` chain on the `SeenGrow` VC itself);
     `ExprOps/Owed.lean` (`instLPGo_spec`: `→ Std.le_trans` added to the `sym`
     list, so the store-order chain `s₀ ≤ s₁ ≤ …` is closed transitively — the
     `Ext s₀ s'` conjunct that used to put `s₀ ≤ s'` in the e-graph is now a
     separate VC).
   * Explicit-term proofs `vcgen; subst_vars; exact ⟨rfl, h₁, …⟩` now face
     several goals (the `rfl` conjuncts already closed): rewritten as
     `all_goals subst_vars` + `all_goals first | rfl | exact h₁ | …` with the
     same terms, in `ExprOps/{MemoSpecs,Abs,Owed}.lean`,
     `Core/Walks/{InferSpine,BetaSpine}.lean`, `Core/Arms/{DefeqPeel,WhnfCore}.lean`.
2. **`do` elaboration of con-ron's Arena twin changed** (it got `MProd`
   states and `pure () >>=` on v4.35.0, which `Lines.lean`'s own comments
   attribute to the legacy `do` elaborator): loop states are `Prod`, not `MProd`, and a guard
   `if c then pure () else fail …; rest` no longer leaves a `pure () >>= rest`.
   `Frontend/Lines.lean` (four `forIn_sim` relations retyped `MProd`→`Prod`,
   one conjunct pair re-ordered so the destructuring names stay put);
   `replace z := AM.pure_bind_ok z` → `try replace …` where the bind is gone
   (`Checker/{Arms,Base,Basis,DeclVal,Split}.lean`,
   `Inductives/{BlockInstall,BlockTail,GenRec,StructInstall,SumInstall}.lean`;
   only the lines that fail were changed, checked one by one), and
   `obtain ⟨_, s, k, z⟩ := AM.bind_ok z'; obtain ⟨-, …⟩ := AM.pure_ok k` →
   `have z := z'` (`Inductives/{SumInstall,RecCheck,GenRec}.lean`);
   `Frontend/Chunks.lean`'s `simp only [pure_bind] at hrun` → `try …` (three).
3. **`simp`/`dsimp` no longer rewrite instance arguments** (new
   `Simp.Config.instances := false`): after `simp only [f]`, an `ite`'s
   `Decidable` instance still mentions the folded `f`, so a later
   `generalize`/`cases h : …`/`split`/`rw [ite_eq_left …]` sees an ill-typed
   motive, and `simp` leaves goals `X = X` that differ only in an instance.
   Fixes: an extra `dsimp +instances only [same lemmas]` (`Core/Walks/{PropRead,
   Stuck,IotaMajor}.lean`, `Checker/Split.lean`, `Frontend/Prepare.lean`), a
   trailing `rfl` (`Core/Walks/PropRead.lean`, `Checker/Hyp.lean`,
   `Inductives/RecCheck.lean`), `rw` → `exact` (`Inductives/PosWalks.lean`),
   `simp only [ite_eq_left h]` → `simp only [h', ite_true]`
   (`Inductives/Rel.lean`), a re-proof of `unfoldDefinition_eq` that decides
   the `if` before unfolding (`Core/Walks/Spine.lean`, 25 lines), and
   `dsimp only` before `vcgen` for two nested `{ s with caches := { … with … } }`
   posts whose `let __src` `vcgen` will not zeta (`Core/Memo.lean`, the same
   idiom the file already uses for `defeqSet_spec`). (The option
   `backward.dsimp.instances` did not help for `simp only` here; `dsimp
   +instances` did.)
