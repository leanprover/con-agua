# Lane `asmesc2`: the asm escape, and hand-written `mul_row`/`sub_row`

Lane of 2026-11-18, from master `9e83e46da`. Task: land the asm escape framework of lane asmesc
(`git show asmesc:docs/design/asmesc.md`, variant A) and proved hand-written x86 bodies for the
bignum inner loops `mul_row` and `sub_row` (measured by lane mulasm, `git show
mulasm:docs/design/mulasm.md`).

## Step 1: the framework (no behaviour change)

A table of hand-written bodies `X : AsmTab := List (Nat × Program)`, keyed by `nameCode f` (a
`Nat`, so that the kernel's lookup during `asm_lit` compares numbers, not strings; `nameCode` is
injective, `nameCode_inj`). `ConAgua/Compiler/Compile.lean`:

* `fnCode X tab t sk f fd`: `X`'s body for `f` if there is one, else `compileFn tab t sk f fd`;
* `compileFns X …`, `compileProgT X …` take the table; `compileProgX X tab p entry` is the whole
  program with the table; `compileProg tab p entry := compileProgX [] tab p entry`.

The proof (`ConAgua/Compiler/SimCall.lean`):

* `FnSimAt p G sk n f fd kf`: the per-function contract, i.e. the body of the old `FunSim` for one
  function whose code starts at `kf` (unchanged text).
* `FunSim p G X t sk n`: `FnSimAt` for every function at its code `fnCode X …`.
* `AsmOk p G X`: every body in `X` for a function `f` starts with `label (fnL f)` and meets
  `FnSimAt p G sk n f fd kf` for every `sk`, `n`, `fd = p.lookup f`, `kf`. `AsmOk.nil`.
* `fnCode_head` (from `AsmOk`) replaces `compileFn_head` at the call sites (`sim_callTail`,
  `sim_tail`, `enter_core`).
* `funSimC` (`SimFun.lean`) is the old `funSim` (compiled code meets `FnSimAt`); `funSim` splits on
  `X.lookup (nameCode f)`.
* `execSim_all`, `enter_core`, `compile_correct_frame`, `compile_correct`,
  `compile_correct_frame_ref` take `(X : AsmTab) (hX : AsmOk p G X)` and are about
  `compileProgX X`. The final chain (`Final/{ParAbi,SeqAbi,BufAbi}`) passes `[] (AsmOk.nil _ _)`;
  no statement in `Final/*` changes in this step.
* `asm_lit`/`asm_lit_fns` take an optional trailing `asm X`: the per-function equations are about
  `fnCode X …` and the whole-program one about `compileProgX X tab p entry`; without the clause,
  `X = []` and the statement is `compileProg tab p entry = name` as before.

`checker.s` is byte-identical (`asm_file.py --check`: up to date). The full build passes.

## Step 2: hand-written `mul_row`

**Code** (`ConAgua/AsmEsc/MulRowAsm.lean`, `mulRowAsm`). This is mulasm's variant B, changed in
two ways. The index counts up to `la` (`cmp`/`jb` at the loop's end), not from `-la` up to 0, so
the proof has no negative index. `adc` takes a zeroed register (`rcx`), not an immediate.
Prologue: `n < la` goes to `ca_error` (L's `abort 0`, a plain error), and `la = 0` returns at once.
Then decode both tags (tier bit, 40-bit index). Then check both windows against their tier's
length: `len - qb ≥ la` and `len - ob ≥ la`, with no wrap. Then take `la` units of fuel up front.
Any failed check goes to `ca_exhausted`, which the contract always allows. The row costs 11
instructions per limb: `mov`, `mul`, `add r,[mem]`, `adc`, `add`, `adc`, store, `mov`, `add`,
`cmp`, `jb`. The carry ripple keeps L's checks and per-step fuel (`n ≤ i` → `ca_error`;
`i ≥ len - ob` → `ca_error`, L's `oob`).

**Forms the routine relies on.** New in the trusted parser: `adcq %r, %r`
(`ConAgua/AsmFile/Parse.lean`, plus `adc` in `scripts/check_asm.py`'s `SUFFIXED`). Already parsed:
`mulq %r`, `addq MEM, %r`, `lea (%b,%i,8), %r`, `movq` loads and stores with an 8-scaled index,
`shrq $40`, `andq $1` / `andq %r, %r`, `subq %r, %r`, `cmpq`, `jCC`, `jmp`, `ret`. All are
baseline x86-64.

**Proof** (standard axioms only; MulRowL elaborates in 0.7 s and MulRowAsm in 3.3 s).
* `ConAgua/AsmEsc/Step.lean` (105 lines). Step lemmas: `add`/`sub` of registers with their carry,
  `adc`, `add r, [b + 8i]` with its carry, `lea d, [b + 8i]`. The compiler's `StepGen.lean` already
  had the scaled loads and stores, `mul`, the shifts and the ALU forms.
* `ConAgua/AsmEsc/MulRowL.lean` (370 lines). The L side. `mrStep`/`mrRows` give the row as a
  function of the memory. `mcLoop` gives the carry ripple at fuel `k`. `mrW1_run` and `mrW2_run`
  are proved by induction with `RunEq`'s step equations. Then `mulRow_run`: with the windows in
  their tiers and `la < F`, the run is the ripple after the row. Also `mulRow_run_abort` and
  `mulRow_run_zero`.
* `ConAgua/AsmEsc/MulRowAsm.lean` (706 lines). The machine side. `mr_row_step` and `mr_tail_step`
  cover one loop iteration each, against `mrStep`/`mcLoop`. The stores go through
  `MemRel.store64`/`Pres.store64`, the carries through `carry_eq`, `adc2_word` and `carry_word`.
  `mr_row` and `mr_tail` are the inductions, `mr_ret` the return. `mulRowAsm_sim` covers the
  prologue and composes: `FnSimAt p G sk n "mul_row" mulRow kf`, for every program declaring
  `mul_row` as `mulRow` and every table where `POOL` is tiered with small descriptor offsets.
* `ConAgua/Checker/AsmX.lean`: `checkerX = [(nameCode "mul_row", mulRowAsm checkerTab)]`.
  `ConAgua/Checker/AsmXOk.lean`: `checkerX_ok : AsmOkT checkerProgI checkerTab checkerX`. The
  inliner leaves `mul_row`, which calls nothing, unchanged (`checkerProgI_mulRow`).
* Proof pitfalls: `rw` on an `Ev` goal tries `rfl`, which unfolds `Eventually` until the heartbeat
  limit; use `ev_lbl` for label rewrites. `generalize` of `G.s …` breaks the link to terms that
  later lemmas produce; keep `G.s` and rewrite with equations.

**Final statements changed** (approved by the coordinator; the end-to-end statements, `Audit/*`
and the axiom guards are unchanged):
* `checkerFile_eq` (`Checker/AsmFileEq.lean`, generated from `checkerAsm_eq`):
  before `checkerFile = checkerStub ++ compileProg checkerTab checkerProgI "check"`,
  after `checkerFile = checkerStub ++ compileProgX checkerX checkerTab checkerProgI "check"`.
* `code_of_checkerFile_par` (`Final/DrvFinal.lean`): the same change in its conclusion.
* `abi_start_outcome`, `abiMode_outcome`, `abiA_outcome`, `abiA0_outcome` (`Final/ParAbi.lean`),
  `abiS_outcome` (`SeqAbi.lean`), `abiB_go`, `abiB_outcome` (`BufAbi.lean`), `drv_outcome`
  (`DrvAbi.lean`). Each gains `{X : AsmTab} (hAX : AsmOkT q tab X)` after `hok`, and its `hcode`
  changes from `Code (… compileProg tab q "check") k0` to `Code (… compileProgX X tab q "check") k0`.
  The callers in `DrvFinal`, `EndToEnd`, `VerdictFinal`, `ThreadsFinal` and `ThreadsVerdict` pass
  `checkerX_ok` (proofs only).

**Measured** (before proving; the regenerated `checker.s` is byte-identical to the measured
binary's assembly; AMD EPYC 9455, load 3-7, `cc -O2`, base master `9e83e46da`):

| | master | asm | Δ |
|---|---:|---:|---:|
| gf3 instructions | 97.96 G | 53.65 G | −45.2 % |
| gf3 wall (bench.py, 10 paired interleaved rounds) | 3.846 s | 2.790 s | −27.4 % [−27.7, −27.0], Wilcoxon p = 0.002 |
| Init instructions | 202.649 G | 202.648 G | −0.0003 % |
| per extra product 1024² (instructions) | 19.93 M | 7.38 M | −63 % |
| per extra product 8192² | 534.4 M | 187.6 M | −65 % |
| per extra product 13 × 9519 | 8.06 M | 3.36 M | −58 % |
| W1024 / W13x9519 / W8192 wall | | | −13.4 % / −10.7 % / −28.7 %, p = 0.002 each |

Correctness: mulasm's product fuzzer, 2100 of 2100 agree with master (700 good accepted, 1400
bad rejected). `diff-e2e.py --refs`: 740 agree, 0 REFDIFF, 0 unsound, 0 incomplete.

## Step 3: hand-written `sub_row`

**Code** (`ConAgua/AsmEsc/SubRowAsm.lean`, `subRowAsm`). The prologue is `mulRowAsm`'s, with the
same instruction indices. The row is 11 instructions per limb: load `t`, `rdx := 0`,
`sub rax, [a + 8i]`, `adc rdx, 0reg`, `sub rax, c`, `adc rdx, 0reg`, store, `c := rdx`, then the
index step. The borrow ripple does `sub 1` on the limb and takes the next borrow (`t = 0`) by
`adc`. The ripple keeps L's checks and per-step fuel, as in `mul_row`.

**Forms.** No new ones. `subq MEM, %r` was already parsed; its step lemma `ev_subRS` is new in
`Step.lean`.

**Proof** (standard axioms only). `SubRowL.lean` (334 lines) and `SubRowAsm.lean` (616 lines)
follow `mul_row`'s files lemma by lemma. They differ in the step function (`srStep`: `t - x - c`,
the borrow `u64(t < x) + u64(t - x < c)`, through `sbb2_word`), the ripple (`scLoop`, through
`borrow0_word`), and the locals' numbering. The shared kit stays in `MulRowAsm.lean`: the
register `rs` simp, `MrFr`, `ev_gen`, `ev_lbl`, `addr_idx`, `pool_desc`, `resOut_zero`, the carry
lemmas. Writing it took about 40 minutes, most of it adapting the copy. The program-specific
lemmas (`*_ret`, `*_tail_step`, `*_row_step` and the composition) cannot be shared as they are,
because their statements name the program's code. A template that takes the loop body and the
ripple step as parameters is the next step for the linear passes (add_n, sub_n, ...), whose
shapes differ from these two anyway: no prologue `n < la`, a carry in and a carry out, and the
output disjoint from the operands.

**Measured** (base: master with `mul_row` asm; the same machine and method as step 2):

| | with mul_row | + sub_row | Δ |
|---|---:|---:|---:|
| gf3 instructions | 53.650 G | 53.584 G | −0.12 % (gf3 is schoolbook) |
| gf3 wall | 2.721 s | 2.715 s | −0.22 % [−0.49, +0.05], p = 0.28 (not significant) |
| Init instructions | 202.6483 G | 202.6483 G | 0 |
| per extra product 1024² | 7.38 M | 6.43 M | −13 % |
| per extra product 8192² | 187.6 M | 159.1 M | −15 % |
| W1024 / W8192 wall | | | −1.7 % [−2.6, −0.8] (p = 0.006) / −3.2 % [−3.8, −2.7] (p = 0.002) |

Correctness: the product fuzzer, 2100 of 2100 agree with master (the sizes from 48 limbs up run
Karatsuba, and so `sub_row`). `diff-e2e.py --refs`: 740 agree, 0 REFDIFF. The regenerated
`checker.s` is byte-identical to the measured one.

## Step 4: the inliner leaves the hand-written functions alone

A body in `checkerX` only runs where the function is called. The inliner (`Compiler/Inline.lean`)
replaces calls of small leaves by their bodies, so for small hand-written leaves (the coming
`add_n`, `sub_n`, …) the asm would be dead code. So `envOf`, `inlRound` and `inlineProg` take an
exclusion list `ex : List Nat` of name codes, and `envOf S ex t p g` is `none` when `nameCode g`
is in `ex`. The correctness theorems (`envOf_sound`, `inlineProg_run`, `inlineProg_lookup`) hold
for every `ex`. Excluding a function only keeps a call as a call. `inl_round`, `inl_round_fns`
and `inl_round_eq` (`InlineLit.lean`) take `ex` after `S`.

The checker's list is `checkerXKeys` (`Checker/AsmKeys.lean`, a module with no bodies or proofs,
so that the inlined program does not depend on them). `checkerX_keys` states that it is
`checkerX`'s keys. With `mul_row` and `sub_row`, which are too large to be inlined anyway, the
change does nothing: `checker.s` is unchanged (`asm_file.py --check`).

## Step 5: carry-chain templates (for linleaf's `add_n`, `add_1`, `sub_n`, `sub_1`)

`ConAgua/AsmEsc/Chain2.lean` (`chain2Asm tab f sub`, two operand windows) and `Chain1.lean`
(`chain1Asm tab f sub`, one) are hand-written bodies for any leaf `f(o, oa[, ob], n, c)` that
computes `P[o + i] := A[oa + i] ± B[ob + i] ± carry` and returns the carry. `sub` chooses `adc`
or `sbb`. The carry stays in the carry flag across the loop, which is 6 instructions per limb:
load, `adc`/`sbb` from memory (or from a zero register), store, `inc`, `dec`, `jne`.

Up front: a carry in above 1, a window outside its tier, or too little fuel go to
`ca_exhausted`. `n = 0` returns the carry.

`chain{2,1}Asm_sim` prove `FnSimAt` for any L function satisfying `Chain{2,1}Spec`: for a carry
in `c ≤ 1` and `n < F`, when `n = 0` or the windows lie in their tiers, the run returns the pure
model `ch{2,1}Rows` (one `chStep` per limb). The model reads each limb from the current memory,
after the earlier limbs' stores, so the windows may overlap; in-place `o = oa` is covered. Each
leaf adds only an L-side proof of its `Chain*Spec`, once linleaf's bodies are on master.

Measured on a scratch build of linleaf `12cfef0a5` (the four leaves excluded from inlining;
master `acf6a18d5`; `M` master, `LL` the compiled leaves, `LA` the leaves in asm):

| | M | LL | LA |
|---|---:|---:|---:|
| gf3 instructions | 53.58 G | 44.63 G | 40.94 G (−8.3 % vs LL) |
| gf3 wall (load 10–25) | 2.721 s | 1.979 s | 1.901 s (−3.9 % [−5.3, −2.4] vs LL, p = 0.004) |
| Init instructions | 202.648 G | 202.654 G | 202.648 G |

Fuzzer 2100/2100 and `diff-e2e --refs` 740/0 for LL and LA. New forms when they land: `adcq`
and `sbbq` with a memory operand, `sbbq %r, %r`, `incq`, `decq`.

## Step 5b: the add/sub leaves wired in (after linleaf #308)

The L sides are in `ConAgua/AsmEsc/ChainL.lean`: `addN_spec`, `subN_spec` (`Chain2Spec`) and
`add1_spec`, `sub1_spec` (`Chain1Spec`) against linleaf's landed bodies. One loop lemma serves all
four: `chLoop_run`, over any per-limb step, with the model `gRows` (`ch{2,1}Rows_eq`). Each leaf
adds a body step lemma and its carry-word identity (`add_word` … `sub1_word`, `cw_tac`). The
four keys are in `checkerXKeys`, and the template bodies `chain{2,1}Asm checkerTab f sub` are in
`checkerX`, proved in `AsmXOk`.

New parser forms (`Parse.lean`, check-asm's `SUFFIXED` gains `sbb`), all of them used in
`checker.s`, so the check-asm gate covers each one:
* `add_n`: `adcq (%rbx,%r13,8), %rax`-style `adcq MEM, %r` (memory operand), `incq`, `decq`;
* `sub_n`: `sbbq MEM, %r`;
* `add_1`: `adcq %r, %r`; `sub_1`: `sbbq %r, %r`;
* all four: `incq %r13`, `decq %rcx` (they keep the carry flag across the loop).

Measured on the landed tree (base master `35c9d8d8f`, with div_submul):

| | master | leaves in asm |
|---|---:|---:|
| gf3 instructions | 44.67 G | 40.93 G (−8.37 %) |
| gf3 wall (10 paired rounds) | 1.989 s | 1.904 s (−4.15 % [−5.58, −2.72], p = 0.004) |

Fuzzers: products 2100/2100 and divisions 540/540, with the same verdicts as master.
`diff-e2e --refs`: 740 agree, 0 REFDIFF.

## Step 6: hand-written `div_submul`

`ConAgua/AsmEsc/DivSubmulAsm.lean` (`divSubmulAsm`): `R := R - q·b` on the `n + 1` limbs at `r`,
returning the borrow out of the top limb (Knuth D4).

Up front: both windows inside their tiers, and their indices with `n` below `2^40`, so that L's
per-limb tag decode `POOL⦃r + i⦄` keeps `r`'s tier (`tag_add`). Also the fuel for the row.

The row is 12 instructions per limb (`mov q; mul [b+8i]; add c; adc 0; load; sub lo; adc 0;
store; mov; add; cmp; jb`), against about 54 for the compiled code, which decodes the tag,
checks bounds and reloads the descriptor on every access. Then the top limb.

The L side is `DivSubmulL.lean` (`divSubmul_run`, against `dsRows`/`dsEnd`), the machine side
`divSubmulAsm_sim`. The only new step lemma is `ev_mulS` (`mul` with a memory operand); the
parser already reads `mulq MEM`.

Measured (base master `acf6a18d5`):
* per extra 2048÷1024-limb division: 60.6 M → 13.3 M instructions (−78 %); the 16-division file
  −32.1 % instructions, −15.5 % wall [−17.4, −13.6], p = 0.002 (the file is short, start-up
  dominated);
* gf3 −0.01 %, Init unchanged;
* correctness: a new division fuzzer (`Nat.div`/`Nat.mod`, 1–2000-limb operands, 540 cases:
  180 good accepted, 360 bad rejected, the same as master), `diff-e2e --refs` 740 agree, 0
  REFDIFF.

`nat_mad` (the decimal reader's multiply-add) was measured too, with its key in the exclusion
list: per extra 20000-digit literal, 8.29 M → 4.42 M instructions (−47 %). Its compiled loop
without inlining is 8.38 M. gf3 and Init are unchanged. It landed in Step 7.

## Step 7: hand-written `nat_mad`

`ConAgua/AsmEsc/NatMadAsm.lean` (`natMadAsm`): `R := R·w + y` in place on the `n` limbs at `o`,
returning the carry. This is the decimal reader's multiply-add (`L.Front.natMad`).

`n = 0` returns `y` at once. Otherwise, up front: the window inside its tier, its indices with
`n` below `2^40` (L reads limb `i` at the tagged address `o + i`, `tag_add`), and the fuel, else
`ca_exhausted`. The row is 9 instructions per limb: load, `mul %r9`, `add`/`adc` of the carry,
store, `mov`, `add`, `cmp`, `jb`.

The L side is `NatMadL.lean` (`natMad_run` against `nmRows`), the machine side `natMadAsm_sim`.
The key `natMadCode` is in `checkerXKeys`, so the caller (`nat_dec_big`) keeps the call instead of
inlining it. No new instruction forms.

Measured (base master `b0c36f046`, with the add/sub leaves):
* per extra 20000-digit literal (`N20kW` − `N20k`): 48.86 M → 25.62 M instructions (−47.6 %);
  the `N20kW` file −2.1 % instructions, wall within noise (−2.1 % [−6.9, +2.7]; the file runs
  0.1 s);
* gf3, Init, and the division microbenchmark (`D2k1k`, `D2k1kW`) unchanged (±0.0001 %);
* correctness: products fuzzer 2100 and division fuzzer 540 (both read large decimal literals),
  with the same verdicts as master; `diff-e2e --refs` 740 agree, 0 REFDIFF.

## Step 8: measured and skipped (`div_2by1`, `div_recip`)

**`nat_cmp`.** First measured on gf3 and Init (flat) and skipped. Taken up again in Step 9: the
scope is all bignum limb loops.

**`div_2by1`, `div_recip`.** Kraken models no `div` instruction, so a hand-written body would be
the same reciprocal algorithm with tighter register use, saving at most their own cost.
Instruction samples (`perf record -e instructions:u`, master `397623e1f`):
* division microbenchmark `D2k1kW`: `div_2by1` and `div_recip` together are about 140 k of
  1.6 G instructions (< 0.01 %; `div_submul` is the hot spot, 15 % of cycles);
* bigdiv's one-limb gcd (`g1`, 500 gcds at 22.7 k instructions each): about 1.1 M of the
  gcds' 11.4 M, so a hand-written pair would save at most about 5 % of a one-limb gcd;
* gf3 and Init: nothing measurable.
Skipped, since the gain is small.

## Step 9: hand-written `nat_cmp`

`ConAgua/AsmEsc/NatCmpAsm.lean` (`natCmpAsm`): `0`, `1` or `2` as the number at `oa` (`la` limbs)
is below, equal to or above the one at `ob` (`lb` limbs). Different lengths decide at once, and
`la = lb = 0` gives `1`.

Otherwise, up front: both windows inside their tiers and below `2^40` (L reads limb `k − 1` at
the tagged address `oa + k − 1`), and fuel for the whole loop, else `ca_exhausted`. The loop runs
from the top limb down, 8 instructions per limb (`sub`, two loads, `cmp`, `jb`, `ja`, `cmp`,
`jne`), against about 35 compiled. It leaves through one of three exits (`rax := 0/1/2`, `ret`).

L side: `NatCmpL.lean`.
* `natCmp_run` against the model `ncRes`.
* The `return` inside L's `while` is the signal `ncSig`; `ncW_run` proves the loop by induction.

Machine side: `nc_step` (one limb), `nc_loop` (induction), `nc_exit`, and `natCmpAsm_sim`.

Proof note: in the main theorem's large context, `obtain ⟨j, hj⟩ : ∃ j, la.toNat = j + 1` and
`generalize la.toNat - 1 = j` each ran away; `generalize` hit the heartbeat limit in `whnf`. A
plain `have` with `la.toNat - 1` passed directly elaborates at once, and the file takes 2 s.

The key `natCmpCode` is in `checkerXKeys`. No call site changes: the function was already a leaf
that no caller inlines. No new instruction forms.

Measured (base master `a98d69362`):
* microbenchmark `C1k`: 200 `Nat.ble` of two equal 1000-limb numbers (`2^64000 − i` twice, so
  the loop runs over every limb): 250.80 M → 245.60 M instructions, a saving of 26.0 k per
  compare (26 per limb);
* `C1kB` (the same operands against one whose top limb differs, so the loop stops at once),
  gf3 and Init: unchanged.

Correctness:
* `C1kF`: 60 equal-length compares that differ only in the lowest limb, through both orders
  of `Nat.ble` and `Nat.beq`. Accepted, with output identical to master.
* Product fuzzer 2100 and division fuzzer 540: the same verdicts as master. Their rejected
  cases compare equal-length numbers.
* `diff-e2e --refs`: 740 agree, 0 REFDIFF.

`div_add` after linleaf's #314: `checker.s` has `call ca_f_add_n` and `jmp ca_f_add_1` in
`div_add`, so the add-back runs the hand-written leaves. The division microbenchmark is unchanged
by #314 (per extra 2048÷1024-limb division 157.747 M before and 157.748 M after): the add-back
step is rare.

## Step 10: the bitwise and copy templates

`ConAgua/AsmEsc/BitAsm.lean` (programs) and `BitAsmSim.lean` (proofs):
* `bitAsm tab f op` serves linleaf's `bitNG op` (`and_n`, `or_n`, `xor_n`): it computes
  `P[o + i] := A[oa + i] op B[ob + i]` and returns `0`;
* `copyAsm tab f` serves `copy_n`.

Up front: each window inside its tier and the fuel, else `ca_exhausted`. `n = 0` returns `0`.
The loops are 6 and 5 instructions per limb (load, `and`/`or`/`xor` from memory, store, `add`,
`cmp`, `jb`).

L side: `BitL.lean`.
* `BitSpec` and `CopySpec`, proved for the landed bodies by `bitN_spec` and `copyN_spec`.
* One loop lemma without a carry: `g0Loop_run` over the model `g0Rows`.

Machine side: `b_step`, `b_loop`, `b_exit`, `bitAsm_sim`, and the `cp_*` lemmas with
`copyAsm_sim`. New step lemmas: `ev_andRS`, `ev_orRS`, `ev_xorRS` (memory operand) in
`AsmEsc/Step.lean`, and `ev_bitOpS` over the three. The forms `andq`/`orq`/`xorq MEM, %r` were
already in the parser and are now used in `checker.s`, so the check-asm gate covers them.

Measured on the landed tree (base master `fbf177187`, linleaf's bitwise group #316):
* gf3: 37.37 G → 32.56 G instructions (−12.87 %); wall −8.3 % [−12.7, −4.0], p = 0.006;
* Init unchanged;
* `B1k` (180 `land`/`lor`/`xor` of 1000-limb operands, each computed twice): −12.5 k instructions
  per operation (the operands are built by `Nat.sub`, which dominates).
