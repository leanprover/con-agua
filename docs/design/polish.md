# Lane polish: follow-ups of the audit

(journal; 2026-10-24, from master `fafcbd02`; the audit is docs/design/audit.md)

## Done

1. **Set theory caveat.** The docstrings of `checkerFile_model_exists`, `checkerFile_no_False`
   (`Checker/AsmFinal.lean`), `x64_model_exists`, `x64_no_False` (`Final/Statement.lean`) and the
   closed corollaries say plainly that `[ConLeche.SetTheory V]` (ZF⁻ plus an ω-chain of
   Grothendieck universes, con-leche's `SetTheory/Core.lean`) cannot be instantiated inside Lean,
   so the results are relative to ZFC + ω inaccessibles.
2. **Closed corollaries in the final file.** `checkerFile_model_exists_closed` and
   `checkerFile_no_False_closed` moved from `Audit/Final.lean` to `Final/Remaining.lean`, next to
   `checkerFile_accepts_remaining` (whose bare `#print axioms` became a `#guard_msgs`). The audit
   file keeps the ledger of the chain theorems and `twinAccepts_not_trivial`.
3. **Registers.** `RegsRestored r0 r` (`rsp` popped past the return address, `rbp`, `r14`, `r15`
   as at the call) in `Final/Statement.lean`; `checker_x64_accepts_regs` keeps
   `compile_correct`'s conjunct, `checker_x64_accepts` is now its weakening. From the stub:
   `sim_abiStub`'s decline continuation (`hdec`) now also gets the registers (the decline path is
   `mov rax, 0; mov rdx, 1; ret`), and `checker_x64_accepts_abi_regs` carries `RegsRestored dm.regs`
   through the stub (it writes only `rax`, `rdi`, `rsi`). Companion final theorem:
   `checkerFile_accepts_regs` (`Final/Remaining.lean`); the census theorem
   `checkerFile_accepts_remaining` keeps its name and shape.
4. **`harness/main.c`.** `slurp` reads with `read(2)` until EOF into a doubling buffer. A regular
   file must keep its size and mtime across the read and its size must equal the bytes read,
   otherwise exit 3 (this also rejects `/proc`-like files, whose `st_size` is 0). Pipes and
   character devices are read until EOF. Inputs of `2^63` bytes or more are rejected
   (`AbiCall`'s bound). Checked: same verdicts as the old harness on a few fixtures, a 512 KB
   pin file through a pipe (`/dev/stdin`) accepted, `/proc/self/status` rejected.
5. **Trusted base** (`Final/Statement.lean` "What is trusted", `docs/ROADMAP.md` §3, the
   `AsmFinal.lean` header): the compiled code of `parseAsmFile`, `programTerm`/`labelExpr` and
   Kraken's derived `ToExpr Directive` (mitigated by the print-back check and the Kraken-parser
   cross-check); label and branch-target resolution by the assembler/linker (`check_asm.py` does
   not compare targets); `harness/e2e.c` is not covered, only `main.c`.
6. **Stale docs.** `Remaining.lean`'s header (no `sorry`s left), Statement's "the lanes are
   building" (now: proved by `pipelineRefines_checker loopStage_checker`), ROADMAP §3 "How it
   composes" step 2.
7. **docs/deviations.md.** One row per deviation: D13–D17, D19, D20, D22 only under Deliberate;
   D11/D12 once (Temporary, "intent unclear"); the seven D18 rows merged into one (all
   `sl_cons`-built lists); the string-literal pool-word row (listed as D21, D24 and D26) is D24,
   D21 stays `proj_table_name`'s pool words (as `WhnfProj.lean` cites it); the `StubNames` D28 is
   now **D28b** (the `frontRun` D28, cited by the audit, keeps its id; `docs/design/stubs.md`
   updated). `scripts/gist_report.py` now accepts an id with a letter suffix (`D\d+[a-z]?`);
   checked by running a copy that writes to the scratchpad (not `--publish`).

## Cost note

`Final/Statement.lean` is imported by `Checker/Entry.lean`, so any edit to it (even a docstring)
rebuilds most of `ConAgua/Arena` and `ConAgua/Checker`. The edits were batched into one rebuild.
