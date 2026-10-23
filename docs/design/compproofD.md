# Lane `compproofD`: compopt prototype D (+ the parts of C it needs), proved (journal)

Branch `compproofD`, worktree `_tmp/wt/compproofD`. Task: port lane `compopt`'s prototype D
(e43bfe52 + b8f108f2: arguments in registers, frameless leaves, return values straight into the
result registers) and the parts of C (c1e135be: leaf locals in registers, register compares) it
needs onto master, prove them (`compile_correct` stays sorry-free), measure, land.

## Measured first (before the proof)

C+D rebuilt on master 8e520465 without proofs (`compopt-asm`), `bench.py --set full --reps 3
--no-conron --no-ref` against master's `checkerAsm` (load ~23): **0.852× instructions, 0.919×
wall** (geometric mean of 18 fixtures, verdicts agree); Init 418.0 G → 356.5 G, 42.0 → 35.0 s.
Reported to the coordinator, who said to go ahead.

**6 registers instead of 9.** The prototype keeps locals and passes arguments in rdi r8 r9 r10
r11 rsi rbx r12 r13; rbx/r12/r13 are callee-saved for the C harness, so the trampoline had to
save them. The same code with only rdi r8–r11 rsi (no trampoline change for that), against the
9-register version of the final code generator, same run: 9 registers 0.852× instructions /
0.937× wall, 6 registers **0.855× / 0.932×**; Init 356.5 G / 32.6 s vs 358.5 G / 33.2 s. Within
noise: the coordinator chose 6 (smaller trampoline change, lane `abi`).

## The code generator (`Compile.lean`)

* `Ctx.leaf` (the function calls nothing) and `Ctx.alloc : List (Var × Reg64)` (locals kept in
  registers). `fnCtx` builds a body's context: a leaf with ≤ 6 parameters gets `leafAlloc fd`
  (the prototype's: most used locals first, a parameter keeps its argument register, the others
  take the free registers, non-result registers first) **if `allocOk` accepts it** (registers
  from `allocRegs`, no register twice, parameter `i` in `argRegs[i]`, no allocation with > 6
  parameters); otherwise `[]`. The heuristic is not part of the proof: only `allocOk` is.
* A local in a register: `compileE` (`mov rax, r`), `simpleOp` (the register as an operand),
  `cmpReg` (`cmp r, b`, in expressions and conditions), `setInPlace` (`op r, imm`), `x := e`
  (`mov r, b` for a simple `e`, else through `rax`; `mov [slot], imm` for a slot and a constant).
* `return es` (`retDirect`): if the results fit the registers and no value reads a result
  register written before it (`retOk`/`retSafe`), results 1, 2, … go straight into their
  registers (`valInto`), result 0 into `rax` last, the rest zeroed (`zeroRes`); otherwise the old
  path (temporaries, `loadRes`).
* Calls with ≤ 6 arguments: argument `i` into `argRegs[i]` (`compileRegArgs`); more: as before
  (temporaries, `rsi`). The callee stores the register parameters not kept in registers into
  their slots (`storeParams`). The trampoline loads the entry's (≤ 6) arguments from the table
  into the argument registers (`loadArgs`, after the existing `lea rsi`); **that is its only
  change** (no registers saved: rbx/r12/r13 are never written).
* Temporaries are counted exactly: `tempsE` does not count a simple right operand; `tempsS al nr`
  counts what `compileS` uses (a `retDirect` return: `tempsEs`; the fallback at least 1). The
  frame is `nlocals + tempsS` (smaller than before for every function); `frameWords` (what
  `Prog.wf` bounds) uses the upper bound `tempsSB` (`tempsS_le`).
* `frameless`: a leaf with every local in a register and no temporaries has no frame and no
  stack check (`label; body; ret`). 72 of the checker's 1753 functions.
* `fnBody` (parameters, zeroed locals, body, results) is shared by the framed and the frameless
  form; `entryNp p entry` names the trampoline's argument count (the `asm_lit` term uses it).

Dropped from C: the simple-operand shortcuts of `compileArgs` (only used by > 6-argument calls
and fallback returns now).

## The proof

* `Inv G ctx F σ s` (was `Inv G nl F`): `reg` (a local in register `r` holds its value), `frame`
  (the others in their slots), `slot` (a slot local `x < F`, instead of `nl ≤ F`), `al :
  AllocOk ctx` (registers of `allocRegs`, injective, none outside leaves), `lo` and `lo8 : leaf =
  false → lo + 8 ≤ rsp` (a frameless leaf knows only `lo ≤ rsp`, and makes no call). `Inv.ctx`
  moves it between contexts that differ only in `brk`.
* `EPost.keep`: an expression changes no register but rax/rcx/rdx; `Inv.ofE` replaces the 40
  `hI.only hG (hE.mem.mono …) hE.rsp hE.r15` sites. `TmpFit nl F t n` (`n = 0 ∨ nl + t + n ≤ F`)
  replaces `nl + t + temps ≤ F` (a frameless function has `F = 0`).
* `Conts.ret` asks for `MemRel` only (a direct return overwrites result registers that may hold
  locals). The direct return is proved with *ghost states* (`St.setReg`: the locals kept in the
  written register get the written value; `evalP_setReg`: a value that does not read the
  register evaluates as before) — `sim_retRegs`, `sim_zeroRes`.
* `FunSim` takes `ArgsIn` (≤ 6 arguments in `argRegs`, else at `rsi` as before); `sim_regArgs`
  (a caller is no leaf, so it has no register locals), `sim_callTail` (fuel, call, results:
  shared by both conventions). `sim_fnBody` (parameters via `sim_storeParams`/`sim_copy`,
  `sim_zeroLocals`, the body, `loadRes`) is used by `funSim`'s framed and frameless forms.
  `allocOk_spec`, `fnCtx_spec`: what the check gives.
* Step lemmas: `OpReads` gets a register case; `ev_cmpRO`, `ev_aluRI`, `ev_movMW`.
* `compile_correct`: same statement; the trampoline part splits its code at the argument loads
  (`sim_loadArgs`). `propext`, `Classical.choice`, `Quot.sound`.

Kernel note: `leafAlloc` first ranked the locals with `List.mergeSort` (well-founded recursion):
the compiled code computed the allocation, but the kernel could not reduce it, so the `asm_lit`
batch checks of `checkerAsm` failed ("declaration type mismatch"). It now uses a structural
insertion sort (`rankInsSort`), same order.

## Derived output and checks (after merging master b8d79ab8: slotgrow, abi)

* `checkerAsm` is rebuilt by `asm_lit` itself; `scripts/checker_prog.py --check`: up to date (no
  template change: the trampoline's argument count is `entryNp p entry` inside the `asm_lit` term).
  `harness/check-asm.sh`: OK (checker 195 781 instructions match; scan, store, walk OK).
* `compile_correct`, `checker_x64_accepts`, `checkerAsm_accepts`, `checkerAsm_eq`: `propext`,
  `Classical.choice`, `Quot.sound`.
* `Compiler/Tests.lean`: frames are smaller (`sum_to`: 2 words instead of 3), so the small-stack
  test now has 128 bytes hold five calls, not three.
* Verdicts: `bench.py --set all --reps 0`, the current checker program compiled by master's and by
  this compiler: **675 fixtures, 0 disagreements**. `scripts/e2e.py` (before the last merge):
  407/3/262 (`check`), 391/3/278 (`check_np`) as master; `whnf_core_loop` reports `error` instead
  of `timeout` (its 2^25 retry ends with a capacity error in under a second with master's compiler too;
  the same program with both compilers times out at the default capacity).

## Performance (final)

`bench.py --set full --reps 3 --no-conron --no-ref`, the current checker program, master's compiler
(base) vs this one (load ~22): **0.864× instructions, 0.912× wall** (geometric mean, 18
fixtures). Init (v4.35.0 export): 422.1 G → 363.0 G instructions (0.86×), 39.2 → 34.4 s.
c04a 28.3 → 24.5 G, app-lam 66.3 → 58.7 G / 12.8 → 11.7 s, c05b 22.5 → 19.6 G.
