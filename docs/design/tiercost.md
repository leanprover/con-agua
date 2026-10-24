# Lane `tiercost`: cheaper tiered array accesses (journal)

Branch `tiercost`, worktree `_tmp/wt/tiercost`. Goal: cut the cost of `A⟨t⟩[i]`
(`ld64t`/`st64t`/`len64t`, docs/design/tierarr.md) before tierswitch and tierpool put many more
accesses on that path.

## 1. Where the cost is (master and the tierswitch prototype)

Master's L code has **no tiered accesses yet** (`asm/checker.s`: 0 `tierDesc` sequences), so the
work below is measured on the prototypes: tierswitch's `_tmp/tierswitch/tier.s` (1021 sites) and
tierpool's `_tmp/tierpool/scratchc.s` (166 sites).

Each access today: `mov t → R; and R, 1; shl R, 12; add R, r15`, then `[R + len64 a]` /
`[R + base64 a]`. Exact dynamic profile (`asmprof`, block counts) of `tier.s` on `beta-ladder`:
408.8 M executed sites, so the `and/shl/add` alone are **6.7 % of all instructions** (18.42 G).
Sites by function: `app_push` 175 M, `lam_push` 87 M, `der_b` 40 M, `app_find` 31 M, `mk_app`
24 M. Tier operand: a parameter in a register (`rdi`) 308 M, a frame slot 60 M, `r11` 40 M. 51 %
of the sites use the same tier source as the previous site in the same straight-line run (only
`jae ca_error` in between).

## 2. Prototypes (unproved; asm rewriters in `_tmp/tiercost/`)

**A: paired split descriptor layout** (`relayout.py`). The word descriptors become two tables,
bases then lengths, both 8 bytes per id, and id `a` sits at position `π(a)` with
`π(a + 256) = π(a) + 1`:

```
base64 a = W + 8 π(a),  len64 a = W + 8 nw + 8 π(a)          (W = 16 + 16 nb)
K = nw - 256 (clamped to [0, 256]);  π(a) = 2a (a < K) | a + K (K ≤ a < 256)
                                        | 2(a - 256) + 1 (256 ≤ a < 256 + K) | a (else)
```

`π` is a permutation of `[0, nw)`, so the table keeps its size (`romBase` and everything after
unchanged); tiered ids (`a + 256 < nw`, i.e. `a < K`) are paired. A tiered access becomes
`mov t → R; and R, 1; cmp rax, [r15 + R*8 + len64 a]; …; mov rcx, [r15 + R*8 + base64 a]`:
two instructions less per site (scaled-index addressing, as `scanLoop` already uses with
scale 1). Plain accesses are unchanged (`[r15 + disp]`, new displacement).

**B: a tier register** (`tierreg2.py`). Per function, the tier local used most often that is never
assigned in the body (a parameter) is kept as `t & 1` in `rbx`: set after the prologue and after
every call (the callee may use `rbx` itself); its accesses lose `mov` and `and`, i.e. **no extra
instruction at all** over a plain access. `rbx` is callee-saved in the SysV ABI, so the entry
stub pushes/pops it. (A first version that refreshed after every assignment and chose by static
use count lost on `der_b`, where the tier local is assigned on each call: refreshes 192 M.)

**C: bit-valued locals.** A local whose every assignment is `e & 1` or a constant 0/1 (and that is
zeroed at entry) needs no `and`; in a register, no `mov` either (`[r15 + r11*8 + …]`). Small
(`der_b`).

A second dedicated register for B gained nothing (`beta-ladder` 17.408 G both).

## 3. Measurements

`instructions:u`, one run each (deterministic), G instructions. `base` = tierswitch's base
(master at 165a58ab), `tier` = tierswitch prototype; `pool*` = tierpool scratchc on its own
master.

| fixture | base | tier | tier+A | tier+A+B+C | ABC vs tier | ABC vs base |
|---|---:|---:|---:|---:|---:|---:|
| app-lam | 64.81 | 68.22 | 65.41 | 63.42 | −7.0 % | −2.1 % |
| beta-ladder | 17.44 | 18.42 | 17.60 | 17.02 | −7.6 % | −2.4 % |
| let-ladder | 9.274 | 9.766 | 9.339 | 9.027 | −7.6 % | −2.7 % |
| eager_open_nat_control | 25.80 | 27.00 | 25.83 | 24.96 | −7.5 % | −3.3 % |
| c04a_restart_70 | 26.03 | 26.60 | 25.80 | 25.31 | −4.9 % | −2.8 % |
| c03d_pi_depth_1030 | 4.318 | 4.613 | 4.396 | 4.228 | −8.4 % | −2.1 % |
| init435 | 372.9 | 367.0 | 358.9 | 354.5 | −3.4 % | −4.9 % |

With A+B+C, tierswitch's +5 % becomes −2 to −5 % against master. A alone takes back most of
tierswitch's cost (+0.9 % on beta-ladder); B adds another 2–3 %.

tierpool (`scratchc`): its tier is computed (`o >> 40`), so only A applies: init435 373.55 →
373.35 G (master 372.83), eager_open 25.868 → 25.856 G (master 25.803); the other fixtures move
< 0.01 %. Master with A (no tiered sites): beta-ladder 17.4280 → 17.4279 G (unchanged, as
expected).

Verdicts: see §4.
