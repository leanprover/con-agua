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

Checks (P+T, after merging master with asmfile): `asm/checker.s` regenerated (`asm_file.py`,
206 240 directives, was 208 108 after P), `checkerFile_eq` and the `Final/Statement.lean` axiom
guards pass (`propext`, `Classical.choice`, `Quot.sound`); `harness/check-asm.sh` OK (checker 190 509
instructions match). `scripts/e2e.py` (P+T): `check` 407 agree-accept / 3 agree-reject / 262 L
aborts / 2 timeouts / 1 memout, `check_np` 391/3/278/2/1, as master. Init (v4.35.0 export, 3 rounds,
load ~62): 363.0 G → 360.3 G instructions, wall 44.5 → 47.3 s (spread 13–24%: noise; T's gain is
in the deep recursions of the default set, not in Init).

## E3: leaf temporaries in registers (measured, not proved: dropped)

Port on branch `compproofT-e3` (commit "WIP compproofT-e3", unproved): `Ctx.tregs` = the
registers of `allocRegs` that hold no local of the leaf and are none of its `nr` result
registers (`tempRegs`); temporaries `t < tregs.length` live there (`Ctx.stTmp`/`ldTmp`); a leaf
is frameless if every local is in a register and `tempsS ≤ tregs.length`. Frameless functions
68 → 169 of 1753. The prototype also used `rbx`/`r12`/`r13` (which needs the trampoline to save
them); measured as `E3x` (uncommitted trampoline change) for comparison.

bench (default set, 5 rounds, load ~80, vs P+T): **E3 0.993× instructions, 0.998× cycles; E3x
0.984× / 0.999×** (c03d 3 878 → 3 876 M (E3) / 3 817 M (E3x), c04a 24 350 → 24 317 / 23 941 M).
An earlier run (5 rounds, load ~36): E3 0.993× instructions, 1.010× cycles. The instruction gain
is under 1% and the cycles do not move: the hot kernel leaves (`der_b`, the `*_find`s) have
more locals than free registers, so only small leaves gain. The proof would generalize `EPost`
(registers kept: all but scratch and the temporary registers from `t` on), `TmpFit`, the
temporary reads/writes of `sim_expr`/`sim_cond`/`sim_args`/`sim_loadRes`/the stores and
`AllocOk` (temporary registers disjoint from locals and results, distinct): medium cost for
nothing measurable. Not done; E2 not attempted either (see compopt2: its −6% instructions were
−1% cycles).
