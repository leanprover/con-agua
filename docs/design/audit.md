# Lane audit: an independent review of the final theorem

(journal; 2026-10-24, on master `f9f965b6`)

Scope: `ConAgua.Final.checkerFile_accepts_remaining`, and `checkerFile_accepts`,
`checkerFile_model_exists`, `checkerFile_no_False` (`Checker/AsmFinal.lean`). I did not build them.
Read: PLAN.md, ROADMAP §3, `Final/{Statement,Abi,Remaining,Twin}.lean`, `Checker/AsmFinal.lean`,
`ConAguaAsm/Checker.lean`, `AsmFile/*`, `harness/main.c`, `harness/check_asm.py`,
docs/deviations.md, and Kraken's `Host`, `Eventually`, `Effects.All`, `Layout`, `Mem`, shift
semantics.

Added: `ConAgua/Audit/Final.lean` (built, in the `ConAgua` globs). It closes the two corollaries
(`checkerFile_model_exists_closed`, `checkerFile_no_False_closed`), pins the axiom ledger of the
final statements and of the con-ron/con-leche theorems the chain uses with `#guard_msgs`, and
proves that `jsonWithTheoremFalse` has an inhabitant, so that `TwinAccepts` is not trivially true
(`twinAccepts_not_trivial`).

## 1. Axioms

The cached build and a **fresh build** both give `[propext, Classical.choice, Quot.sound]` (and
`checkerStub_eq` just `[propext, Classical.choice]`). The fresh build is a separate worktree with
plain `lake`, an empty `LAKE_CACHE_DIR`, `LAKE_ARTIFACT_CACHE=false` and a Kraken copy without
`.lake`: 3546 jobs, 13 min wall / 133 CPU-min, nothing restored or replayed; `ConAgua/Audit/Final.lean`'s `#guard_msgs` pass there too. The theorems checked: the four finals,
`loopStage_checker`, `pipelineRefines_checker`, `checkerFile_eq`, `checkerStub_eq`,
`twinAccepts_{pure,model,no_False}`, `ConRon.Bridge.Arena.pooledAccepts_bridge`,
`ConRon.Bridge.Inductives.indSpec_of_bridge`, `ConLeche.Model.checkDeclsPure_sound_of`,
`ConLeche.Frontend.parseChunks_jsonWithTheoremFalse`. There is no `sorryAx` and no
`Lean.ofReduceBool`, so no `native_decide` is in the cone.

## 2. Vacuity

* `Ev` is Kraken's inductive `Eventually` over `step1`, where `Effects.All` maps `unimplemented`,
  `gp_unaligned`, `nonmem_load` and `nonmem_store` to `False`. A fault therefore never satisfies
  the postcondition, and the theorems also prove that the run terminates and returns to `ra`.
  The `require_*_access` checks are not checked (they pass). That only matters for runs that
  would fault on hardware, and a fault is never an accept.
* `Host` holds the side conditions on the program and its layout (unique labels, label sizes 0,
  positive sizes for the other instructions, no address `-1`, addresses determine offsets).
  `asm/checker.s` has 15731 `.text` labels and none is duplicated (awk). Layout sizes are a free
  function, so a `Host` with `prog = checkerFile` exists. There is no Lean witness for it.
* `AbiCall`: its conditions are independent constraints on a finite map (`ExtHashMap`) and on
  registers, and they do not contradict each other. The region size the stub needs is
  `7421703487488` bytes, equal to `ca_region_size`. There is no Lean witness for this either.
* `TwinAccepts` is not trivially true (`twinAccepts_not_trivial`, given a `SetTheory V`).
* The statement uses only `rdx` and `rax`. The trampoline restores `rsp`/`rbp`/`r14`/`r15`, and
  `compile_correct` proves it, but `checker_x64_accepts` throws that conjunct away.
  `rbx`/`r12`/`r13` do not occur in the file. `clang -O2 main.c` tests `rax`/`rdx` straight after
  the call.
* `[SetTheory V]` cannot be instantiated in Lean (it needs ω inaccessibles; con-leche's
  SetTheory/Core.lean says so). The model and no-`False` corollaries are therefore relative to
  such a model existing, and that is not visible in the x64 docstrings.
* The model statement reaches opaque constants: `ConLeche.Expr.hasStrLitGo` (a `partial def`),
  core `mixHash`, `String.hash`, `String.Internal.*` and `System.Platform.getNumBits`. The
  theorems hold for every value of these constants, so they do not affect soundness.

## 3. Trusted base, `main.c` against `AbiCall`

The registers are SysV `rdi, rsi, rdx, rcx, r8, r9` = `in, n, pins, np, base, ca_region_size`,
and `ca_res` comes back in `rax:rdx`. The buffers come from malloc and the region from a fresh
anonymous mmap, so they are disjoint and the region is zero. Without PINS, `pins = NULL` with
length 0, which satisfies `AbiCall` vacuously. `MADV_HUGEPAGE` does not change the contents.
Gaps:

* `slurp` uses `ftell`, then `fread(len)`. If the file grows between the two, the buffer holds
  only a prefix and the run accepts that prefix. Files where `ftell` reads 0 (`/proc`-like) read
  as empty. This is part of "buffer to stream".
* `check_asm.py` does not check branch and call targets ("the assembler's job"). The assembler
  and linker are trusted for label resolution.
* The docstring says "only the parser" is trusted. In fact the compiled Lean code of
  `parseAsmFile`, `programTerm`/`labelExpr` (which run `lbl`/`fnL` natively) and the derived
  `ToExpr Directive` is trusted too. The print-back check and the Kraken-parser cross-check
  reduce this risk.
* `harness/e2e.c` (it calls `ca_enter` with its own layout) is not covered by any theorem.
  `e2e.py` results come from `main.c`.

## 4. The file

`include_asm` reads the file with `IO.FS.readFile` at elaboration time. Lake's `needs` input file
puts its hash into `ConAguaAsm`'s trace. Cross-checks: `scripts/asm_file.py --check` says "both
parsers agree (206288 directives)", and `harness/check-asm.sh` says "[checker] OK: 190557
instructions match". Every shift count in the file is in `0..63`, every ALU immediate fits in
imm32, and Kraken models shifts by 0 like the hardware does. Byte-edit test (fresh tree, plain lake, own cache; and again in this worktree through the shared
cache): changing the stub's `$7421703487488` (line 6) to `…489` rebuilds `ConAguaAsm.Checker`
(5.9 s). `AsmFileEq` still builds, because `checkerFile_eq` relates the stub to `checkerStub`,
which is read from the file. The kernel then rejects `checkerStub_eq.piece_0` (AsmStubEq.lean:19).
Changing `addq $8, %rsp` to `$16` at line 22735 (`bm_clear`) fails `asm_file_eq` at
AsmFileEq.lean:23. Neither edit was served from the cache.

## 5. Deviations

`PipelineRefines checkerProg` is now a kernel theorem, so no deviation can make L accept more
than the twin: the proof would not go through. I found no Deliberate row that would allow it in
principle either. D32 and D33 are capacity guards (they only abort more), D28 is proved
(`parseChunks_single`), and D5 is harness-only. Hygiene: several rows appear twice (D11, D12,
D13–D17, D19, D20, D22 in both Temporary and Deliberate; D18, D21/D24/D26 copies), and D28 names
two different deviations.

## 6. Escapes

`grep` over `ConAgua`, `ConAguaAsm` and `vendor` finds no `WithoutChecking`, no `skipKernelTC`,
no `set_option debug`, no `axiom` and no `native_decide` use. The `addDecl` calls (AsmFile/Eq,
ListEq, PreludeSimProg) go through the kernel. `implemented_by` appears only in meta code
(`AsmLit.evalProgram`, `E2E.Dump`), in con-leche's `withPtrEq` shim (the kernel uses `k ()`), and
in core.

## Stale documentation

The doc of `Remaining.lean` still talks about "the `sorry`s the proved parts still rest on", and
the Statement docstring calls `PipelineRefines` "the named hypothesis the lanes are building".
Both are proved now.
