# Lane forloop: counted loops with a `Nat` index (pilot journal)

**Question** (lnext2.md §2 item 7, lconstructs.md ranks 2–3): a counted `for j < n { … }` in L, a
counted-loop rule proved once in L core, and an `l_model` option that models such loops by a `Nat`
index, as the first instance of `Nat`-valued models that could shrink the word ↔ `Nat` proof lines.
Estimated −1.6 to −2.5 k lines if all 64 counted loops are reproved. Base: master ff57e2c3. Pilot
first; scratch in `_tmp/forloop/` (`old/`: the master files, `IndRealIpo_B.lean`: the `Nat` model
variant below, `measure.sh`, `times*.txt`).

**Short answer: no-go**, for the `l_model` option and for a retrofit. The construct and the rule
already exist (lane lsugar, lconstructs.md §5: `for` in `Notation.lean`, `Triple.forUp`,
`Triple.forUp_pre`, `forUp_succ_toNat` in `L/For.lean`); what was left is the `Nat` index. Five loop
refinements restated over a `Nat` index save **−23 lines in all (−2 to −9 each, −4.6 on average)**,
against 47 lines for the lemmas they need, with no measurable change in elaboration time. Rolled
out over the remaining ~59 counted loops that is about −270 lines (−220 net) for ~15 h, and a
generated `Nat`-indexed model adds ~−2 lines per loop on top, for 10–16 h of generator work. Only
this journal lands; the pilot is on branch `forloop` (commits a01f6554, e646b1ed, e83e3008).

## 1. What was tried

**Variant A: the refinement states the index as a `Nat`, the model stays.** The loop model keeps
its word index; the refinement quantifies over `j : Nat` with `j ≤ n.toNat` and applies the model
at `UInt64.ofNat j`, so that the twin side reads `xs.drop j`, `xs[j]`, `decHL m q j` directly. A
small kit, `L/ForIdx.lean` (47 lines with documentation), turns the model's guard, exit and step
into `Nat` facts:

```lean
theorem forIdx_toNat (h : j ≤ n.toNat) : (UInt64.ofNat j).toNat = j
theorem forIdx_lt (h : j ≤ n.toNat) : UInt64.ofNat j < n ↔ j < n.toNat
theorem forIdx_exit (h : j ≤ n.toNat) (hn : ¬ UInt64.ofNat j < n) : j = n.toNat
theorem forIdx_sub (h : j ≤ n.toNat) : (n - UInt64.ofNat j).toNat = n.toNat - j
theorem forIdx_succ (j : Nat) : UInt64.ofNat j + 1 = UInt64.ofNat (j + 1)
theorem forIdx_add (h : a.toNat + j < 2 ^ 64) : (a + UInt64.ofNat j).toNat = a.toNat + j
theorem forIdx_zero : (UInt64.ofNat 0 : Word) = 0
```

**Variant B: the model itself takes a `Nat` index** (what `l_model … natfor` would generate),
tried on the hand model `ipoW` of `ind_params_ok`: `ipoW : Nat → Mem → Word → Word → Word → Nat →
Option Sig`, guard `j < l.toNat`, loads at `o + UInt64.ofNat j`, the next iteration at `j + 1`.

## 2. The pilot: five counted loops

Chosen to cover the kinds of loop refinement there are: generated `Option` models whose twin is a
`map`/`mapM` over `drop j` (`gftW_ok`, `gfcW_ok`), generated unified models whose twin recurses on
a list without an index (`cnaLoop_ref`) or receives the index (`ccsLoop_ref`, `classesCtors … c`),
and a hand model over `drop j` (`ipoW_ok`). Each loop refinement was restated (variant A) and its
one caller adjusted. Lines are the theorem's lines (loop refinement + caller); time is the
`Elab.async` "elaborating proof of" trace of the loop refinement, mean of three runs of
`lake env lean` on the whole file (master copy vs. converted copy, load average 50–115, so ±30 %
is noise).

| loop (file) | model | lines master → A | Δ | elaboration s, master → A |
|---|---|---:|---:|---:|
| `gftW_ok` (`IndInstallSpec/GfcW`) | generated, `Option` | 48 + 27 → 45 + 27 | −3 | 0.25 → 0.17 |
| `gfcW_ok` (`IndInstallSpec/GfcW`) | generated, `Option` | 68 + 44 → 66 + 44 | −2 | 0.32 → 0.25 |
| `cnaLoop_ref` (`IndT/RecGen23`) | generated, unified | 141 + 29 → 134 + 30 | −6 | 0.60 → 0.70 |
| `ccsLoop_ref` (`IndT/RecGen27`) | generated, unified | 159 + 46 → 156 + 46 | −3 | 1.88 → 1.30 |
| `ipoW_ok` (`IndRealIpo`) | hand, `Option` | 117 + 25 → 108 + 25 | −9 | 0.75 → 0.68 |
| **all five** | | 704 → 681 | **−23** | no measurable change |

Plus the kit (+47) and one import per file (+4): the pilot as a landing is **+28 lines**.

Variant B on `ipoW` (`_tmp/forloop/IndRealIpo_B.lean`): the refinement loses 3 more lines (the
guard is already `j < l.toNat`, the step already `j + 1`), but the loop's spec reads the L local `j`,
a word, so the model's arms must be restated at `x.toNat` for it (`ipoW_exitW`, `ipoW_indW`,
`ipoW_otherW`, +13 lines with `forUp_succ_toNat` and `UInt64.ofNat_toNat`). By hand: +12 lines
against A, +4 against master. Generated, those arms would cost nothing, leaving ~−2 to −3 lines per
loop over A. Spec time unchanged (`ipoLoop_spec` 0.89 → 0.87 s). The fuel stays in either variant
whenever the body calls a function whose model takes the fuel (`sortTeleW k`, `callW p k`, `tkE p
k`): all five loops here, so the model cannot drop to a plain well-founded recursion on `n - j`.

## 3. Why the estimate does not hold

* **The −25 to −40 per loop came from `find_rule`** (lconstructs.md §2, §5): a hand model with a
  step bound `K` and its re-indexing lemmas, replaced by a model on a `Nat` index. Generated loop
  models never had that: they recurse structurally on the fuel with one guarded equation per arm,
  and their refinements already follow them arm by arm. What a `Nat` index removes there is the
  index bookkeeping alone: `j.toNat ≤ n.toNat` from `j ≤ n`, the exit's `j.toNat = n.toNat`, the
  step's `(j + 1).toNat = j.toNat + 1` and `j + 1 ≤ n`, and `o + ofNat j.toNat = o + j` (4–11
  lines per loop here).
* **Part of it comes back.** Loads stay words (`o + UInt64.ofNat j`), so the address facts remain
  (`forIdx_add` instead of `UInt64.toNat_add`), and the libraries the refinements call are
  word-indexed (`rd_iwN`, `decHL_write`, a callee's refinement taking the index as a word, `cos_ref`
  in `ccsLoop_ref`): each needs `(UInt64.ofNat j).toNat = j` back (`rw [hjT]`), 1–3 lines per loop,
  and `UInt64.ofNat j` widens lines.
* **Where the twin has no index** (`classNodesAgree` recurses on the list `es`; the L side carries
  the remaining slice `PSlR … (eo + j) (el - j)`), the slice invariant stays in words and the gain is
  the bookkeeping only.
* **The word ↔ `Nat` lines are not loop indices.** 492 lines in `ConAgua/` state some
  `(x + 1).toNat = x.toNat + 1` (an upper bound for the step facts a `Nat` index removes, over all
  loops, hand and generated); the 32 k word ↔ `Nat` lines of lnext2.md §1.3 are addresses, field
  reads and values (`(r.headD 0).toNat`, `iwTop`, decoded lengths), which an index type does not
  touch.

## 4. Decision

* **`l_model … natfor`: no-go.** 10–16 h of generator work (a `Nat` loop parameter threaded through
  the loop's continuations, the loop spec at `(s₀.loc j).toNat` with word-view arms, the enclosing
  call at `e.toNat`) for ~−2 to −3 lines per loop over variant A, and only on loops whose
  refinement is reproved.
* **Retrofit of variant A: no-go.** ~−4.6 lines per loop, ~59 loops, ~15 min each: about −270
  lines (−220 net of the kit) for ~15 h, under 20 lines per hour, far below the 70 lines/h at which
  hashtpl.md stopped.
* **On touch: optional.** A new or rewritten counted-loop refinement whose twin indexes by `Nat`
  (`xs.drop j`, `xs[j]`, the index passed on) is a few lines shorter stated over `UInt64.ofNat j`
  with the kit (`ipoW_ok`: −9). The kit is on branch `forloop` (`L/ForIdx.lean` as of e83e3008); land it
  with the first such refinement, not on its own.
* The `Nat`-valued-model direction for the 32 k word ↔ `Nat` lines would have to start from
  values and addresses (models returning decoded `Nat` lengths and offsets, libraries indexed by
  `Nat`), not from loop indices; nothing here measures that.

No proof, L code, `checker.s` or statement changed on master.
