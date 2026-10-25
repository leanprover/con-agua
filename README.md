# con-agua – A Lean checker verified at the assembly level

This is a reimplementation of the external Lean checker [con-leche](
https://github.com/leanprover/con-leche), verified at the x86 assembly level.

This was written by AI under supervision from Joachim Breitner at the [Lean FRO](https://lean-fro.org/). This README is genuinely human written; the rest of the repository is not. The file [`OVERVIEW.md`](./OVERVIEW.md) contains a much more detailed, AI written exposition of the project.

## Goal

The `con-agua` checker joins [`con-ron`](https://github.com/leanprover/con-ron/) in providing extra assurance by reimplementing `con-leche` in a different setting. All three are proven to implement essentially the same consistent checking algorithm. But any such verification work leaves something left to be trusted:

* `con-leche`, written in Lean, in particular requires the Lean compiler and the Lean runtime with its bignum implementation to be correct.
* `con-ron`, written in Rust, in particular requires the Rust compiler as well as the Aeneas verification tool to be correct.
* `con-agua`, verified at the assembly level, in particular requires the Kraken x86 semantics to be correct.

A bug in any of these trusted components threatens the validity of that checker's result. But if you check your proof with all three of them, the likelihood of bugs existing in all three settings that can be exploited together diminishes.

## Usage

Run [`make`](./Makefile) and call `./checker FILE.ndjson`. Pass `--jobs=n` if you want parallel checking. See [`OVERVIEW.md`](./OVERVIEW.md) for more details.

## Architecture

We use the [Kraken](https://github.com/AeneasVerif/kraken) x86 semantics to prove that if the type checker in the assembly file [`checker.s`](./checker.s) accepts, then `con-leche` and `con-ron` accept too (up to resource limits). See [`EndToEnd.lean`](./ConAgua/Final/EndToEnd.lean) for the main theorems of this development.

The assembly is produced from code written in our own little ad-hoc low-level language [L](./ConAgua/L/) with a [verified compiler](./ConAgua/Compiler/). The L code is proven to simulate `con-leche` (via [`con-ron`’s Lean model](./vendor/con-ron/ConRon/Arena/), which already handles hash-consing and caching).

The small, trusted [`main.c`](./main.c) file reads the input and invokes the entry point of the assembly function. With `--jobs=n`, after parsing the input (using the verified assembly for that), it spawns threads and invokes the verified assembly once for each declaration group.

Again, more detail to be found in [`OVERVIEW.md`](./OVERVIEW.md).

## Contributions

Unsolicited PRs against this repo are unlikely to be useful; well-written issues with bug reports or feature requests are welcome.
