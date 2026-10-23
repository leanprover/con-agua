# Lane `compproofT`: compopt2 prototypes P, T, E3, proved (journal)

Branch `compproofT`, worktree `_tmp/wt/compproofT`. Task: port lane compopt2's prototypes P
(592faf97, `if c abort` as one jcc), T (e9181dae, tail calls) and E3 (9a6603e1, leaf temporaries
in registers) onto master (the proved C+D, 99551fd7), measure each before proving, prove
(`compile_correct` stays sorry-free), regenerate the derived output, land each separately.

Measurement setup: `.s` files from the same checker program (`checker.prog` of master 99551fd7),
compiled by each compiler (`e2e-l asm`), `scripts/bench.py --no-build --set default --no-conron
--no-ref --cpus 90-91 --asm …` run from a separate worktree on master (`_tmp/wt/compproofT-bench`),
so that no build runs in the worktree being edited. Ratios are geometric means over the 13
fixtures of the default set.

## P: `if c abort` (proved)

`compileS (.ite c .abort .skip) = compileC ctx (path.ch 3) c true errorL 0`: one conditional
jump to `ca_error`, no `jmp`/labels around an abort block.

Proof (`SimStmt.lean`): `sim_ifAbort` is `sim_cond` with the jump target `errorL` (the
condition-true continuation is `Conts.err` with `Err.abort`, the fall-through is `Conts.normal`);
`compileS_ite` (the general `ite` equation, from `compileS.eq_7` with its non-overlap
hypothesis) keeps `sim_ite`'s proof as it was. ~25 lines.

Measured (bench, 3 rounds, load ~18): instructions 1.000×, cycles 1.003×, wall 0.982× (noise).
The executed instruction count does not change (the not-taken `jcc` replaces a taken one); the
code is 3% shorter (214 855 → 208 221 lines of `.s`).

## T: tail calls (proved)

`x⃗ := f(a⃗); return x⃗` (`tailCode`): when the function may make tail calls (`Ctx.tailF = some
F`, set by `fnCtx` for every function that calls: `F` is its frame, `nlocals + tempsS`), `x⃗` are
distinct (`nodupB`), `x⃗.length = ctx.nr` (every result of the function comes from `f`), `ctx.nr
≤ nrOf f` (`f` sets them all), and the arguments go in registers (≤ 6): arguments into
`argRegs`, `sub r14, 1; jc ca_exhausted`, `add rsp, 8F`, `jmp ca_f_f`. `f` returns to this
function's caller. (The prototype checked `es == xs.map .var` with `BEq Expr` and no `nodup`:
`a, a := f(); return a, a` would return `(r1, r1)` in L but leave `(r0, r1)` in the registers.
`retVars` is a structural check.) 752 sites in the checker.

Proof:
* `Conts.tail` (new exit, `SimStmt.lean`): if `ctx.tailF = some Fw` then `Fw = F` (the frame
  the statement runs in), and a run that returns `vs` continues at the caller's return address
  `ra`, the word above the frame, from any state with `MemRel`, `TPost G F d d'` (rsp = top + 8,
  rbp/r15 kept, fuel only down, `Pres` below the top) and `ResOut G ctx.nr vs`. `Conts.tail_fwd`
  passes it from a statement to its parts (`sim_seq`, `sim_ite`, `sim_while`: one line each).
* `sim_seq` takes `SimSTail` for the tail case (`compileS (.seq s t)` is `tailCode`'s code when
  it is `some`); `SimTail.lean` proves it (`sim_tail`): `sim_regArgs`, the fuel check, `ev_addRI`,
  `ev_jmp` to `f`'s label, then `FunSim` of `f` with the return address read above the frame
  (mapped: `MemRel.stack`). `FunSim` quantifies over the caller's `rsp` and return address, so the
  callee's simulation is used unchanged. Its return continuation is `Conts.tail` with the L run
  `x⃗ := f(a⃗); return x⃗` (`evalArgsP_vars`, `St.setLocs_loc_get`: distinct `x⃗` read back `r`).
* `sim_fnBody` gets `htail`/`htF`; `funSim` gives them: a frameless leaf has `tailF = none`; a
  framed function's `TPost` is the `FunSim` return (the return address at `d.rsp` is kept by
  `Pres`).

About 200 lines. Measured (bench, 3 rounds, load ~18): **P+T vs base: 0.992× instructions,
0.935× cycles, 0.939× wall** (c03d 0.490 → 0.432 s, let-ladder 1.27 → 1.17 s, beta-ladder 2.82 →
2.69 s, c04a 3.23 → 3.06 s).
