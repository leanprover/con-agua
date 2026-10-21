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

Source: `_tmp/ref/con-leche/ConLeche/Frontend/Scan/` (rev `103562b`), copied
byte-for-byte to `vendor/con-leche/ConLeche/Frontend/Scan/`:

* `Types.lean`, `Fast.lean`, `Naive.lean`
* `Equiv.lean`, `Equiv/{Kit,Scalars,Keys,Objects}.lean`

No content changes were made to any of these files. This is con-leche's
byte scanner (`ConLeche.Frontend.Scan.*`): the recogniser for the
lean4export NDJSON dialect, its naive `List UInt8` spec, and the proof that
they agree. It imports nothing outside `Std` (`Std.Data.HashMap.{Basic,Lemmas}`),
so it builds standalone. This is the subset con-agua's Stage A spike needs
first (`docs/survey.md` §1.4), hence it landed before the rest of ConLeche.

**Lakefile patch**: our package-level `[leanOptions]` sets
`autoImplicit = false, relaxedAutoImplicit = false` (con-agua's own style).
con-leche's lakefile sets neither, so its files rely on Lean's defaults
(`autoImplicit = true, relaxedAutoImplicit = true`) — e.g. `ConLeche/Frontend/Scan/Types.lean`'s
`IdTable (α : Type)` API functions mention `α` without rebinding it.
Rather than edit the vendored files, the `[[lean_lib]] name = "ConLeche"`
entry in the top-level `lakefile.toml` carries its own
`leanOptions = {autoImplicit = true, relaxedAutoImplicit = true}`, overriding
the package default for this lib only. No vendored `.lean` file was edited.

**`withPtrEq`**: not needed. It is used elsewhere in ConLeche
(`Cached/ExprNodes.lean`, `Cached/ExprOpsC.lean`, `Kernel/Name.lean`,
`Driver/OwnerParse.lean`, `Verify/Cached/ParInstall.lean`) but nowhere under
`Frontend/Scan/`, so this subset needed no `withPtrEq` shim.

**Build time**: `lake build ConLeche` (cold, including materializing and
building the `Kraken` dependency): **~40s** on this machine. The `ConLeche`
lib alone (18 jobs) took well under that once `Kraken` was already built.

**Compatibility check beyond the vendored subset** (not vendored, for
the record): a full standalone copy of all of `ConLeche/` (566 files,
~236k lines), built directly against nightly-2026-09-21 with con-leche's
own lakefile (no `autoImplicit` override), got to 1105/1109 jobs with
*zero* source incompatibilities — the only failures were
`ConLeche.Frontend.Prelude` and `ConLeche.Kernel.NatOpPins`, both of which
read a runtime pin-data file named after the toolchain
(`pins/leanprover-lean4-v4.35.0.prelude.ndjson`) that does not exist for
our nightly (see con-leche's `pins/README.md`). So: `withPtrEq` was *not*
in fact a problem anywhere we tried, and the rest of ConLeche is expected
to vendor cleanly later; the pins mechanism is the one real gap, to be
solved when we vendor more of ConLeche (either by generating a pin file for
our nightly, or by excluding `Frontend.Prelude`/`Kernel.NatOpPins` from the
globs, same as we exclude con-ron modules below).

## vendor/con-ron — `ConRon` lib

Source: `_tmp/ref/con-ron/proof/ConRon/` (rev `4c9eaf7`), copied to
`vendor/con-ron/ConRon/`.

See the `[[lean_lib]] name = "ConRon"` entries in `lakefile.toml` and the
module-by-module build report below for what builds and what is excluded.
