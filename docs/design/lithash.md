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
