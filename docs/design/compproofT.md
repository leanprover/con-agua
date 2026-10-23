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

