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

**Verdicts**: `bench.py --set all --reps 0` with `base`, `tier`, `tier+A+B+C`, `pool+A+B+C`:
675 fixtures, **0 disagreements** (`_tmp/tiercost/verdicts.log`).

**Cycles and wall** (`bench.py --reps 5 --cpus 88,89`, five large fixtures, machine load ~100,
`_tmp/tiercost/bench_big.{log,json}`), geometric means against `base`:

| system | instructions | cycles (median) | wall |
|---|---:|---:|---:|
| base | 1.000 | 1.000 | 1.000 |
| tier | 1.032 | 0.995 | 0.997 |
| tier+A | 0.994 | 0.949 | 0.944 |
| tier+A+B+C | 0.969 | 0.933 | 0.927 |

## 4. Proof cost (estimate, for the go/no-go)

* **A** is local to the compiler: `Tab.base64`/`len64` get the `π` formula (piecewise; one lemma
  `base64 (tierA a t) = base64 a + 8 (t &&& 1)` under `a + tierOff < nw`, plus injectivity and
  the range `[W, romBase)` for the table-disjointness facts); `tierDesc` becomes `and R, 1` and the
  three tiered arms (and `warrDesc`) address `[r15 + R*8 + d]`. The stub writes descriptors through
  `Tab.base64`/`len64`, so it follows. `compile_correct`'s statement is unchanged.
* **B** adds an `Inv` field (`rbx = σ.loc x &&& 1` for the function's tier local), its
  preservation through every expression/statement case (no generated code writes `rbx` except
  the refreshes), the refresh after the prologue and after calls, and `push/pop rbx` in the
  stub. Larger: it touches every simulation lemma's register frame.
* **C** needs a syntactic "bit-valued local" check and its invariant; small gain, skip for now.

## 5. Side task: `str_close` on `scan!` (landed)

Lane blkcopy's draft (§7 of blkcopy.md): the loop skips plain bytes with
`scan!(IN.u8, j, len, strStopC)` and decodes only the stop byte. The three cases `finish` did not
close needed the post-scan facts at this iteration's `j` as concrete hypotheses instead of `∀ j`
ones: `hscan` (the scan over `src8`/`len8` is `scanN b strStopC j b.size`), `hk_le`, `hk_eq`
(`strCloseN_scan`), `hkN` (the `toNat` round trip), `hk_st` (a stop before the end is a quote,
a backslash or a control byte, from the new `scanN_stop`). `Compiler/Tests.lean`'s `Prog.wf`
guard now uses `Prog.tab scanProg 1 0` (the class table lives in the ROM). `long_line_5mib`:
673.3 M → 558.0 M instructions (−17 %). Verdicts: `--set all --reps 0`, 675 fixtures, 0
disagreements. ModelGen arms for the block primitives: not added (no `l_model` group uses a block
yet, and lane lmretro is editing `ModelGen.lean`; blkcopy §6 lists what they should be).

## 6. A, proved (landed)

* **Layout** (`Compiler/Compile.lean`): `Tab.wK = min (nw − tierOff) tierOff` (the arrays with both
  tiers in the table), `Tab.wpos` (the permutation of §2) and its inverse `Tab.wposInv`;
  `base64 a = 16 + 16 nb + 8 wpos a`, `len64 a = 16 + 16 nb + 8 nw + 8 wpos a`. The table keeps
  its size, so `romBase` and everything after it are unchanged. Facts: `wpos_lt`, `wposInv_wpos`,
  `wpos_wposInv`, `wposInv_lt`, `wK_spec`, `wpos_tier` (all by `grind` after unfolding).
* **WF**: a tiered access needs `a < tab.wK` (was `a + tierOff < nw`). That also says `a < tierOff`,
  which the pairing needs; no program has a tiered id ≥ 256.
* **Code**: `tierDesc r` is now only `and r, 1`; `ld64t`/`st64t`/`len64t` address
  `tdesc r d = [r15 + 8 r + d]`. Two instructions fewer per tiered access. Block operands
  (`copy!` with `D⟨t⟩`) keep a descriptor register: `tierBlk` = `and 1; shl 3; add r15` (once
  per block, so the simulation proofs of the copy loops did not change).
* **Proofs**: new step lemmas `ev_movRMt`, `ev_cmpRMt` (`addr_tdesc`, from Kraken's
  `AddrExpr.zeroExtend_interp_sib`); `tier_off` now `+ 8 (u & 1)`; `sim_tierDesc` (one
  instruction), `sim_ld64t_tail`, the `len64t` arm, `sim_st64t_tail`, `sim_tierBlk`/`sim_warrDesc`
  rewritten; the table-range side conditions take `wpos_lt`. Entry stub: `abiVals` writes the
  bases in `wpos` order (`wposInv`), then the lengths; `abiVals_getElem?` and the stub's
  descriptor facts in `Final/Abi.lean` follow. `compile_correct` and the final theorems unchanged
  (statements and axioms; `Audit/Final.lean` passes).
* `scripts/asmprof.py`: its table categories know the new layout.
* Verdicts: `--set all --reps 0`, 675 fixtures, 0 disagreements (master vs this). Effect on master: none in instructions (master has no tiered accesses yet; beta-ladder
  17.4279 G → 17.4277 G); `asm/checker.s` changes only in displacements. The gain arrives with
  tierswitch/tierpool (§3: −4 % on tierswitch's big fixtures).
* Proof cost, for planning B: about 3 h, all in `Compiler/` (Compile, Step, Rel, SimExpr,
  SimStore, SimBlock, AbiSim, Final/Abi), no change outside the compiler.

## 7. B, proved (branch; lands after tierswitch)

* **Register: `rsi`, not `rbx`.** `rbx` is callee-saved for the C harness, and saving it costs
  either C-stack room (`compile_correct` and the final theorems assume exactly 24 bytes below
  `rsp`) or a scratch word whose restore on the `ca_error` path needs `r15`, which `GPost` does
  not keep. `rsi` is the sixth argument register: in a leaf with at most 5 parameters no
  parameter arrives in it, it is not a result register, and leaves make no calls (the only other
  writer of `rsi`). So the tier local is limited to leaves with ≤ 5 parameters, and no local of
  such a function is allocated to `rsi` (`leafAlloc`, checked by `tregFree`). The stub and the
  trampoline are unchanged.
* **Choice** (`tregOf`): the parameter with the most uses as a tier (weighted `8^loop depth`,
  `Stmt.tierUses`), at least 2. It stays in its frame slot (no register; its non-tier uses read
  the slot as a memory operand), which keeps the ghost state of `return` (`St.setReg`) away from
  it.
* **Code:** `tregEntry` (`mov rsi, argreg; and rsi, 1`) at the start of `fnBody` (before the
  parameters are stored); `ld64t`/`st64t`/`len64t` whose tier is the tier local address
  `[r15 + 8 rsi + d]` with no tier code; a write of the tier local (`x := e`, `x := scan!(…)`)
  sets `rsi := rax & 1` (`tregSet`) before the store.
* **Proofs:** `Inv.tr` (`rsi = σ.loc x &&& 1`); `AllocOk.tleaf/talloc/trsi`; the `Inv`
  constructors take `hbx` (`rsi` unchanged when there is a tier local), filled by the auto-tactic
  `bx_keep` almost everywhere; `Inv.setLoc`/`setLocR`/`setReg` exclude the tier local,
  `Inv.setLocT` writes it; `sim_ld64t_core`/`sim_st64t_core` (the access from any register
  holding the tier), used by both the `tierDesc` path and the tier-local path; `sim_storeRax`
  and `sim_set` handle the write; `sim_fnBody` = `tregEntry` then `sim_fnBody0`; call sites
  get `ctx.treg = none` from `tleaf`. No change outside `Compiler/`; `compile_correct` and the
  final theorems unchanged.
