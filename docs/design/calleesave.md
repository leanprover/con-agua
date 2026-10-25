# Lane calleesave: all callee-saved registers restored, as a theorem

## Task

The final theorems stated `RegsRestored` with `rsp`, `rbp`, `r14`, `r15` only. `rbx`, `r12`, `r13`
were covered by the remark "do not occur in checker.s (not a theorem)". The harness relies on all
System V callee-saved registers surviving each call.

## Routes considered

1. A generic theorem that the code generator never names `rbx`/`r12`/`r13`, carried through the
   simulation. The obstacle: Kraken's `Eventually` derivation can step through any instruction
   of the host program, so "the instructions of the file do not write R" alone does not give "R
   unchanged at Q". It needs a per-step contract, e.g. redefining `Ev` over a step relation that
   also keeps R. That changes every step lemma and ties the code generator (and future asm
   escapes) to never using these registers.
2. Reflection (`decide`) over the instruction lists. It has the same stopping-time problem, and a
   cost over 200k directives.
3. **The user's choice: save and restore in the entry stub.** The first plan was per-entry wrappers
   like the driver's (save area past the region). `ca_start_a` and `ca_check_b` tail-jump into
   `ca_enter`, so each would have to become a call-wrapper with a `drv_outcome`-sized proof.

## What landed: the shared trampoline saves them

Every entry runs through `ca_enter`, so the save is there:

```
ca_enter:  mov [rdi+S], r15; mov [rdi+S+8], rbx; mov [rdi+S+16], r12; mov [rdi+S+24], r13
           push rbp; push r14; push rdi          ; T on the machine stack instead of r15
           ...
ca_finish: mov rsp, rbp; pop r15                 ; r15 = T again, on every exit path
           mov rbx, [r15+S+8]; mov r12, [r15+S+16]; mov r13, [r15+S+24]; mov r15, [r15+S]
           pop r14; pop rbp; ret
```

`S = Tab.save tab np = Tab.args + 8 np`: the 32 bytes just past the table (`G.tabEnd`). Pushing
`T` instead of the caller's `r15` keeps the machine-stack window at 24 bytes (`AbiCall`
unchanged). It also avoids the problem that the error path's contract (`GPost`) does not keep
`r15`: the restore takes `T` back from the machine stack through `rbp`, which every exit keeps.

* `compile_correct_frame`/`compile_correct` take one new premise, `hsv`/`hsv64`: the 32 bytes past
  the table are mapped and apart from the L stack, the arrays and the 32-byte window. Their posts
  gain `CalleeKept` (`rbx`, `r12`, `r13`). `MemFrame` excludes the save area.
* Proof: `enter_core` is the old trampoline proof from the first push on, generalised over the
  saved words (`hfin` reads them back through `MemFrameT`, the old full frame).
  `compile_correct_frame` does the four stores and calls it. Nothing about the compiled
  functions' registers is used: the save area lies outside the layout, so `Pres` keeps it.
* The stubs discharge the premise from the layouts they build: the save area is in slot 0 (the
  table's), below `T + 2^31` (`abiTabOk` now requires table + 32 ≤ 2^31): `abi_harness`
  (`HarnessCall.hsv`), `seq_save`, `buf_save`. `AbiCall`, `ThreadsRun` and `BufCallH` are unchanged.
* `RegsRestored` gains `rbx`, `r12`, `r13`. The threads: `thread_chain` and
  `threadsRun_twinAcceptsPooled_regs` carry `RegsRestored` for entry 1 and every `ca_check_b`
  call, and `checkerFile_threads_regs` states it.
* `runKraken` (the `#guard` tests) maps the save area.

The driver's own save area (return address and caller's `r15` past the region) stays. It is
needed before and after the two `ca_enter` calls, so merging it into the trampoline's area would
not shorten `drv_outcome`.

## Measurements (2026-10-25)

* `Init` (`_tmp/fixtures/init/init435.ndjson`, `ca_start`, `perf stat -e instructions:u`):
  359 125 335 442 (master) against 359 125 311 840 (this branch). The difference is noise; the
  change adds 8 instructions per `ca_enter` call, 2 calls per run.
* Verdicts: master's and this branch's binary agree on all 675 fixtures (con-leche e2e and arena
  tests, `ca_start`; 426 accept, 243 error, 3 `ok 1`, 1 exhausted, 2 time out at 120 s in both).
  This branch with `--jobs=4` gives the same verdicts on all 675. `Init` accepts with `--jobs=8`.

## For asm escapes and the code generator

`FnSimAt`/`FunSim` are unchanged. A hand-written body (asmesc) or a new back end (leafgen) may use
`rbx`, `r12`, `r13` (and every other register except the contract's `rsp`, `rbp`, `r15`, `r14`
rules) freely. The only remaining obligation is the existing memory frame (`Pres`), which already
keeps the save area. The asmesc pilot (`ConAgua/AsmEsc/AppFindAsm.lean`) builds unchanged on top
of this branch.
