# Lane `lithash`: the literal hash, fast (journal)

Branch `lithash`, worktree `_tmp/wt/lithash`. Task: make `lit_hash(o, l)` (the FNV-1a hash over a
literal's limbs, `ConAgua/Arena/Store.lean`; called by `intern_lit`'s find and push) fast, in two
landings: (1) an unrolled L leaf, (2) a hand-written x86 body through the asm escape. The hash
value is unchanged (`hashN`, the twin's function); only how it is computed changes.

## Step 1: `lit_hash` as an unrolled leaf

Before, `lit_hash` (a 4-local leaf) was inlined into `intern_lit`, a non-leaf, so its loop ran on
the stack. Now it is

```
h := fnvBasis; sliceRes 0 1 4 5; q := fnvPrime;
hashLoop8: while 8 <= l { 8 × h := (h ^ POOL⟨t⟩[x + k]) * q; x += 8; l -= 8 };
hashTail:  for i < l { h := (h ^ POOL⟨t⟩[x + i]) * q };
return h
```

Its size (over the inliner's 80 nodes) keeps it a call, so the compiler compiles it as a leaf
with its locals in registers (about 9 instructions per limb in the unrolled body, 7 of them the
tiered access and its bound check).

**Variants measured** (`instructions:u`, gf3, base master `a98d69362`, 40.932 G; prototype emitter
patching `checkerProg` and keeping `lit_hash` out of the inliner):

| variant | gf3 | Δ |
|---|---:|---:|
| a leaf, not unrolled | 39.550 G | −1.38 G |
| 4 per round, `i` counting (`x + i + k`) | 37.823 G | −3.11 G |
| 4 per round, `x`, `l` moving (linleaf's prototype) | 37.477 G | −3.45 G |
| **8 per round, `x`, `l` moving** | 37.132 G | −3.80 G |

**Proof.** The model stays `hashN`; the loops are proved against `hashFrom p a h k` (the hash of
`k` limbs from pool position `a`, starting from `h`; `hashN_hashFrom`). One invariant `HashInv H`
serves both loops: what is left is `l - i` limbs from position `t · 2^40 + x + i`, and hashing
them from `h` gives `H`. The loads come out of `vcgen [step, L.evalE_spec, L.evalC_spec, …]` as
`Array.getD` (no bound proofs inside terms), and `tpool_tier` turns them into `tpool` reads. One
round is a lemma in the goal's shape (`hash_round8`, explicit rewrites), the tail step another
(`hash_step1`). `litHash_spec`'s statement and every caller's proof are unchanged.
`Store.lean` elaborates in about 2 s.

**Measured** (base master `6a44a928c`):

| | master | step 1 |
|---|---:|---:|
| gf3 instructions | 32.556 G | 28.756 G (−11.7 %) |
| Init instructions | 202.647 G | 202.635 G (−0.006 %) |

Verdicts: `diff-e2e.py --refs` 740 agree, 0 REFDIFF.

Wall time (12 paired interleaved rounds, load 35–58, unpinned): gf3 2.689 s → 2.302 s (medians),
mean −5.3 % [−19.1, +10.8], Wilcoxon p = 0.42: not significant on this machine; Init +0.9 %
[−7.7, +10.3], p = 0.91 (no change expected).

## Step 2: hand-written `lit_hash`

**Code** (`ConAgua/AsmEsc/LitHashAsm.lean`, `litHashAsm`). `l = 0` returns the offset basis at
once. Otherwise, up front: decode the tag (tier bit, 40-bit index `x`), then `x + l < 2^40`, the
window inside the tier (`len - x ≥ l`, no wrap) and `l` units of fuel; any failed check goes to
`ca_exhausted`, which the contract always allows (L's own `sliceRes` abort for a slice crossing a
tier becomes exhaustion there). The loop is 5 instructions per limb:

```
.L: xorq (%rdi), %rax; imulq %rsi, %rax; addq $8, %rdi; decq %r8; jne .L
```

(`rdi` the address of the next limb, `r8` the limbs left, `rsi` the FNV prime). The loop is
latency-bound (`xor` + `imul` per limb), so unrolling it would save instructions but hardly time.

**Forms.** None new: `xorq (%rdi), %rax` (ALU with a memory operand at offset 0), `imulq %r, %r`,
`decq` and `jne` were all parsed and in `checker.s` already; the check-asm gate passes.

**Proof** (standard axioms only; each file elaborates in about 1.5 s, under 1 GB).
* `ConAgua/AsmEsc/LitHashL.lean` (263 lines). The model `lhRows A x h r` (one FNV step per word of
  the tier array, from index `x`), `lhRows_add`. `hB8_run` (one round of `hashLoop8`), `hl8_run`
  and `hT_run` (the two loops, by induction on the rounds or limbs left), `sliceRes_run`, and
  `litHash_run`: at fuel `F > l`, with the window in its tier below `2^40` (or `l = 0`), the run
  returns `lhRows` of the window and leaves the state unchanged.
* `ConAgua/AsmEsc/LitHashAsm.lean` (330 lines). `lh_step` (one loop iteration: a load through
  `MemRel.get64` at the pointer, `xor`, `imul`, the pointer and count steps, the branch),
  `lh_loop` (induction on the limbs left), `lh_tail` (the return), and `litHashAsm_sim`
  (prologue and composition): `FnSimAt p G sk n "lit_hash" litHash kf`.
* `ConAgua/Checker/AsmKeys.lean` (`litHashCode`), `AsmX.lean` (`checkerX`), `AsmXOk.lean`
  (`nameCode_lit_hash`, `checkerProgI_litHash`, the arm of `checkerX_ok`).

**Measured** (base master `6a44a928c` + step 1; the landed `checker.s` gives the same counts as
the prototype up to 3 M instructions, `decq` instead of `subq $1`):

| | master | step 1 | step 2 |
|---|---:|---:|---:|
| gf3 instructions | 32.556 G | 28.756 G | 26.104 G (−9.2 % vs step 1, −19.8 % vs master) |
| Init instructions | 202.647 G | 202.635 G | 202.593 G (−0.03 % vs master) |

Wall, gf3 (30 paired interleaved rounds pinned to CPUs 92–93, load about 40, means of the paired
log ratios with 95 % intervals, Wilcoxon signed-rank, normal approximation): step 1 against master
−1.7 % [−9.8, +7.1], p = 0.75; step 2 against step 1 −6.7 % [−13.8, +0.9], p = 0.11; both against
master −8.3 % [−14.8, −1.4], p = 0.013 (medians 2.081 s → 2.087 s → 2.021 s). The machine is too
loaded for the per-step differences; instructions are the measure here.

Verdicts: `diff-e2e.py --refs` 740 agree, 0 REFDIFF (references from the verdict cache).

## What went wrong

* Scratch proofs in a **non-module** file (plain `import ConAgua.Arena.Store`) blew up: a
  `simp only [BinOp.eval, …]` over an L state and the `rfl` that `rw` tries afterwards took 4–17 GB
  (the memory watchdog killed one run at 17 GB), and a structural recursion with `Nat` as its first
  argument after the colon hit "(kernel) deep recursion" in its equation lemma. The same text in a
  `module` file with `import all ConAgua.Arena.Store` takes 0.9 GB and seconds. Scratch files are
  modules now, run under an RSS guard.
* In the run proofs, `rw` on a goal that contains the whole function body tries `rfl` at the end
  and evaluates the body; `rewrite` (no `rfl`) and small step lemmas (`seq_normal`,
  `set_const_run`) avoid it.
