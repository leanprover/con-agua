# Lane scanfast: a fast NDJSON scanner (analysis, unproved prototypes, proof plan)

Question: why does L's scanner execute 2.4× con-ron's frontend instructions on `Init`, and how
fast can it get, faster than con-ron if possible, while keeping the scanner's behaviour proved?
Base: master 8dc00910 (`checker.s` unchanged by d6abfaec). Nothing landed but this journal.
Prototype sources, assembly, profiles and bench logs: `_tmp/scanfast/` (`proto/Fast.lean`, `p1.s` to
`p4.s`, `prof/`, `bench_*.log`, `threads.log`, `fuzz.py`).

Method. Instruction counts are exact: `scripts/asmprof.py`, or `perf stat instructions:u`, which
is deterministic. Inclusive costs come from `_tmp/scanfast/incl.py`: each function's own count
plus its callees', split by call counts. The apply functions are left out. Wall times and cycles
come from `bench.py`, interleaved over 5 rounds on CPUs 40–41. The 16-thread times come from
`_tmp/scanfast/threads.py`: base, P3, P4 and con-ron interleaved, 5 rounds, CPUs 48–63. The load
average was 5–20 during the runs (other lanes), so walls are noisy (spread up to ±25 % on
`Init`) and only differences of more than about 5 % mean anything.

## 1. Why 28 G against 11.8 G

`Init` (`init435.ndjson`) has 345.7 MB in 6.45 M lines:
* 27.7 M keys (81.9 MB of key text, 24 %);
* 20.2 M numbers (123.3 MB of digits, 36 %);
* 140.5 MB of everything else (quotes, colons, braces, string values).

5.19 M lines (80 %) are the single shape `{"app":{"arg":N,"fn":N},"ie":N}`. Six shapes (app, lam,
forallE, str name, num name, const) cover 98.8 % of the lines.

**The algorithm differs from con-ron's, not just the call overhead: L scans each line twice.**
`front_line` runs:
1. the validator `scan_line` → `scan_line_loop` → `scan_app`/`scan_binder`/…, which stores nothing;
2. then `apply_any` → `rec_line_loop`, a second walk over the members. On an expression line it
   gives up after the first key or two.
3. then `rec_expr_loop` → `expr_val` → `rec_obj`, a third walk that reads the values.

con-ron's `scan_line_fwd` makes one pass that builds the `LineRec`.

Inclusive instructions on `Init` (master, exact):

| part | instructions | per line |
|---|---:|---:|
| `front_line` in total (scanner part) | 26.97 G | 4,180 |
| ↳ validator `scan_line` | 11.83 G | 1,833 |
| ↳ `rec_line_loop` (name and level pass, gives up on expressions) | 2.23 G | 346 |
| ↳ `rec_expr_loop` (the expression record pass) | 12.26 G | 1,991 |
| ↳ `rec_decl_line` | 0.22 G | — |
| con-ron's whole frontend (lnext §1) | 11.8 G | 1,830 |

**L's validator alone costs as much as con-ron's whole frontend.** The record passes, 14.7 G, have
no counterpart in con-ron. `next_member` runs 88.0 M times for 40.6 M members plus closing braces:
40.6 M times in the validator and 47.4 M times in the record passes. `key_end`, `key_at` and
`value_at` run 62.2 M times for 27.7 M keys.

Bytes read per input byte:

| byte class | L master | con-ron | fast path (§2) |
|---|---|---|---|
| key text | 4× (`key_end` and `key_at`, in two passes) | 2× | ≈ 1/8: one 8-byte compare covers a key and its punctuation |
| digits | 3× (`skip_digits` in the validator; `skip_digits` and `read_nat` in the record pass) | 2× (`num_end`, `read_nat_at`) | 1× (P3), or one 8-byte load per number of up to 7 digits (P4) |
| structure, whitespace | 2× (`next_member`, `value_at`'s two `skip_ws`, in two passes) | 1× | inside the literal compares |
| **in total** | **≈ 2.8 byte reads per input byte, 78 instructions per input byte** | ≈ 1.6, 34 | ≈ 1, 6.8 (P4) |

What a call costs on top of that. The scanner's leaves are cheap per byte: `scan!` compiles to 6
instructions per byte through a class table. Per call they cost about 15–25 instructions of
prologue, bounds and result traffic:
* 144 M calls of `skip_ws` at 21 instructions;
* 62 M calls of `key_end` at 51;
* 41 M calls of `skip_digits` at 64.

The record loops (`rec_obj`, `rec_expr_loop`, `scan_line_loop`) are non-leaf functions with their
locals in the frame (lnext §3.1–3.2), at 125–150 instructions per call. con-ron inlines its leaves,
and it reads each value once.

The two-pass structure is a performance deviation from the twin that `docs/deviations.md` does not
list.

## 2. Prototypes (unproved; `_tmp/scanfast/proto/Fast.lean`)

All prototypes keep the proved scanner and add a **canonical-line fast path** in front of it. The
harness renames `front_line` to `front_line_slow` and adds a new `front_line(i)`, which calls
`fast_line(i)` first. `fast_line` recognises the exact bytes lean4export writes for a line shape:
* no whitespace, and keys in lean4export's order;
* numbers of 1–18 digits, `0` only alone;
* name strings of printable ASCII without `"` or `\`, and not empty;
* the line ends in `}` and a newline, and at least 160 bytes of input remain.

If the line matches, the fast path applies the record (`apply_expr`/`apply_rec`, with the
arguments `apply_any` would pass) and returns the next position. On anything else it returns `0`
(it declines), and `front_line_slow`, the master code, runs. The fast path never rejects, so the
set of rejected (malformed) inputs is unchanged by construction. A literal is compared 8 bytes at
a time: `(le64!(IN.u8, p) & mask) == "…"`, with a constant built in Lean.

| variant | what | `Init` instructions | scanner (inclusive) | per line |
|---|---|---:|---:|---:|
| base | master | 257.66 G | 26.97 G | 4,180 |
| P1 | fast path for app lines only, non-leaf (it calls `apply_expr`) | 237.57 G | — | — |
| P2 | the six shapes, non-leaf | 230.68 G | 4.02 G | 605 (`fast_line`) |
| P3 | P2 as a **leaf**: `fast_line` returns `(nx, kind, idx, a, c, d)` and `front_line` applies | 230.22 G | 3.56 G | 517 |
| P4 | P3 with **SWAR numbers**: one 8-byte load, a non-digit mask, the lowest set bit and a multiply give the length; Lemire's 3-multiply conversion gives the value (byte loop for 8 or more digits) | **229.01 G** | **2.35 G** | **330** |

In all of P2–P4 the fast path takes 6.377 M of the 6.453 M lines (98.8 %). The remaining 76 k
lines (thm, def, letE, proj, levels, …) cost 0.32 G in the old code.

**The scanner goes from 26.97 G to 2.35 G instructions (−91 %): 5× below con-ron's 11.8 G.**

What the steps show about the compiler:
* **P2 → P3 (leaf, −15 % per line).** The same code is 15 % cheaper per line once the function
  makes no calls, because its locals then live in registers. In P2 every digit costs about
  25 instructions of frame traffic; in P3 it costs 17.
* **P3 → P4 (SWAR, −36 % per line).** Numbers are 36 % of the bytes. The SWAR read handles a
  number of up to 7 digits in about 20 instructions.
* **Bounds checks.** What remains in P4 (330 per line) includes about 55 instructions of bounds
  checks: for each `le64!` a length reload, `cmp $8`, `sub`, `cmp` and `ja`, all dominated by the
  function's `len ≥ i + 160` guard. That is about 0.35 G. A compiler pass that drops checks dominated
  by a length guard would remove them, but it is not worth a lane on its own.

### Measurements

`bench.py --set init --reps 5 --cpus 40-41 --no-conron --no-ref` (load 12–20, `bench_init.log`):

| | instructions | cycles | wall (median) |
|---|---:|---:|---:|
| base `Init` | 257.66 G | 84.69 G | 19.14 s |
| P3 `Init` | 230.22 G (−10.6 %) | 77.76 G (−8.2 %) | 17.57 s |
| P4 `Init` | 229.01 G (−11.1 %) | 77.08 G (−9.0 %) | 17.41 s (−9.0 %) |
| P4 `init-prelude` | −21 % | −16 % | −14 % |

The cycles saved (7.6 G) are fewer than the instructions saved (28.6 G) would give at the
checker's average IPC of 3.0 (9.4 G): the old scanner ran at a higher IPC than the kernel.

`--set default` (13 fixtures, P4 against base, load 6–12, `bench_default.log`): geometric means
0.914 instructions, 0.949 cycles, 0.974 wall. `long_line_5mib` −25 % instructions,
`dag_tower_unfold` −24 %, `complete_c04a_restart_70` −4 %. The kernel-bound fixtures (beta-ladder,
let-ladder, c03d) change by 0.3–0.8 %.

**16 threads** (`Init --jobs=16`, CPUs 48–63, 5 interleaved rounds, load 5.6 rising to 18.7 during
the run, `threads.log`):

| | median | min | max |
|---|---:|---:|---:|
| base | 5.01 s | 4.83 | 5.30 |
| P3 | 3.50 s | 3.37 | 3.63 |
| P4 | **3.45 s** | 3.23 | 3.78 |
| con-ron `--jobs=16` | 3.50 s | 3.31 | 3.59 |

The gap to con-ron at 16 threads (1.5 s here; 1.3 s in lnext) closes completely. The scanner was
serial, so all of its saving shows in the wall time. The first round, at load 5.6, gives 4.83 /
3.23 / 3.31 s.

### Verdicts

On P4 (the variant whose verdicts were checked):
* `diff-e2e.py --bin p4.bin --refs --parallel 16`: 634 of 634 agree, REFDIFF 0. A first run showed
  599 REFDIFF ("con-ron error") from a transient reference failure; the rerun and the base binary
  both give 0.
* `--jobs 4`: 634 of 634 agree.

The fixtures are mostly canonical lean4export output, so they test the accepting fast path well
and the fallback less. A differential fuzz (`fuzz.py`) covers the fallback: P4 against master on
1,200 mutated files of four fixtures. One to three mutations per file, on lines of the six shapes:
* inserted space, tab or CR;
* a leading `0`;
* 8, 18, 19 or 20-digit numbers;
* swapped keys, a deleted byte, a random byte, a structural byte;
* other `binderInfo` values;
* escapes and UTF-8 in names, a DEL byte;
* duplicate keys;
* a missing final newline.

No difference in exit code or output. The outcomes were 420 accepted, 768 malformed, 10 rejected
and 2 declined.

## 3. Correctness criterion and proof plan

**What the scanner is proved against now.** The spec is con-leche's `scanLineFwd`
(`ConLeche/Frontend/Scan/Fast.lean`, which con-ron's `scan_fast.rs` ports). Three layers:
* **Validator.** `lineFwd_link : encLine (scanLineFwd b i) = lineFwdN b i`
  (`Scan/LineLink.lean`), an exact equality on both outcomes (accept with the next position, or
  `(0, 0)`). Below it, each L function's spec proves the code against its word model
  (`scanLine_spec` … `nextMember_spec`, `Scan/*.lean`).
* **Records.** On a line `scanLineFwd` accepts, `recLineN`/`exprLineN`/`declLineN` are the record's
  fields (`RecR`, `Front/FieldsLink.lean`, `FieldsExprLink.lean`, `FieldsDeclLink.lean`).
* **The line.** `frontLine_spec` proves `front_line` against the model `frontLineW`
  (`Front/Line.lean`). `frontLineW_refines` (`Front/LineRefine.lean`) turns it into "con-leche
  scans a record `r`, and con-ron's `applyLine st r` succeeds". The error side is
  `frontLineE_claim` (`Verdict/FrontRunE.lean`, over the generated `frontLineE`).

These are about 11.4 k lines in `Scan/` and 5.4 k in `Front/Fields*`/`Line*`.

**The fast path changes no spec.** The new `front_line` must satisfy the *same* `frontLine_spec`
statement, with `frontLineW` unchanged. Then `frontLineW_refines`, `front_run`'s proofs and the
end-to-end theorem are untouched. The fast path is a refinement of the existing models on the
lines it accepts. It needs no completeness argument: declining is always allowed, and the fallback
is the existing proved code. No speed idea here needs a change to the twin's model.

The lemmas, cheapest first:

| # | lemma | kind | size (estimate) |
|---|---|---|---|
| L1 | `le64_lit`: `p + 8 ≤ b.size → (le64 b p &&& msk n = lit s ↔ ∀ j < n, b[p+j] = s[j])` | once, library (next to the `ld8x8` lemmas) | 60–100 |
| L2 | `numBlk` loop: on exit `p' = numEndN b p`, `x = readNat` of `[p, p')`, and the guard (1–18 digits, no leading `0`) gives `slotNatN` ≠ 0 | once (P3) | 80–120 |
| L2′ | `swar_digits`: for `w = le64 b p`, the masked lowest-bit and multiply give the digit-run length `k ≤ 7`, and the 3-multiply conversion gives `Σ dⱼ·10^(k-1-j)` | once (P4 only); 64-bit arithmetic **without bv_decide**: split on `k` (8 cases), byte extraction lemmas, `omega`/`Nat` arithmetic | 250–400, the riskiest single lemma |
| L3 | `member_canon`: if the bytes at `p` are `"K":` with `K` a dialect key and the value starts at `p+|K|+3`, then `nextMemberN b p w = ⟨2, p, w, code K, p+|K|+3⟩` (`keyEndN` finds the quote, `keyAtN` gives the key's code, no whitespace in `valueAtN`) | once, plus one `decide` fact per key (15 keys) | 100 + 15 |
| L4 | per shape `fast_<shape>_sound`: `fastLineN b i = some (nx, k, idx, a, c, d)` with this shape gives `lineFwdN b i = (1, nx)`, `skipWsN b i = i`, `b[i] = '{'`, and `recLineN b (i+1)` / `exprLineN b (i+1)` equal to the fields. Proof: walk `lineN`/`objN` (validator) and `recN`/`exprN` (record pass) with their existing step lemmas (`recN_close`, …), L3 and L2. | 6 shapes | 100–150 each, 600–900 in total |
| L5 | `fast_line`'s spec against `fastLineN` | `l_model` (a leaf with three small loops; `ModelGen` knows `ld8x8`) | ≈ 100 by hand around the generator |
| L6 | the new `front_line`: `frontLine_spec` by cases on `fast_line`'s result (L4 rewrites `applyAnyW` to the `apply_rec`/`apply_expr` call; a decline is the old proof), plus a new arm in `frontLineE_claim` (the accepted case errs only in `apply_rec`/`apply_expr`, whose claims exist) | twice, local | ≈ 150 |

**Estimate.**
* **P3** (byte-loop numbers): 1.1–1.5 k new lines, and no existing proof changes except the two
  `front_line` theorems. At about 70 lines/h that is 16–22 h.
* **P4** adds L2′: 4–8 h, with a real risk that the bit proof is harder without `bv_decide`. It
  buys another 1.2 G instructions (3.56 → 2.35 G) but no measurable wall time at 16 threads
  (3.50 against 3.45 s, inside the noise).

A straight-line fast path is fine for the proofs. A data-driven variant (one L interpreter of
"literal or number" templates in ROM) would be proved once, but L4 is per shape in either form.
The generated code makes L5 cheap, so the interpreter buys little.

**Deviation note** for the landing lane: `docs/deviations.md` needs a `Deliberate` row. con-ron
scans every line with the generic recogniser. L first tries a canonical-form recogniser of six line
shapes and falls back to the twin's scanner. Effect: none (proved to give the twin's result
whenever it accepts; it never rejects). The existing two-pass split (§1) should get a row too
(effect: performance).

## 4. Alternatives, ranked by speed and by proof tractability

| rank | candidate | scanner on `Init` | proof | verdict |
|---:|---|---:|---|---|
| 1 | **Canonical fast path, byte-loop numbers (P3)** | 3.56 G (−87 %) | 1.1–1.5 k new lines (L1–L6); old proofs stay | **go** |
| 2 | P3 plus SWAR numbers (P4) | 2.35 G (−91 %) | + L2′ (bit arithmetic without bv_decide) | follow-up, only if the 1-thread cycles matter |
| 3 | One generic pass, mirroring con-ron: the `scan_*` loops return the fields and the record passes go | about 12 G (removes the 14.7 G of record passes; estimate from the inclusive profile) | rewrites `Scan/Records*` and `Front/Fields*` (about 8 k lines) against `scanLineFwd`'s record | no: con-ron parity at many times the proof cost of rank 1; the twin-shaped generic scanner stays as the fallback |
| 4 | Inlining plus non-leaf registers (lnext ranks 4 and 6) on the old scanner | −10 to −20 % of 27 G (estimate) | compiler, proved once | not for the scanner; P2 → P3 shows the leaf/non-leaf gap (15 %) the compiler rank 6 would close everywhere |
| 5 | Bounds checks dominated by a length guard (compiler) | −0.35 G on P4 | compiler, proved once | small; later |

Word-at-a-time *search* (finding `"`, `\`, `,`, `}` eight bytes at a time) does not pay here. Keys
and punctuation are literal in canonical lines, so the fast path compares them instead of searching
for them. Only name strings are searched, and they are short. For the fallback, the remaining 1.2 %
of lines cost 0.32 G.

## 5. Recommended next lane: `scanfast-p3`

1. Add `ConAgua/Scan/Fast.lean`: `fast_line`, the P3 code in `_tmp/scanfast/proto/Fast.lean`
   (`fastLeaf` with `numBlk`), and `front_line` as in `frontLineLeaf`. Rename the old body
   `front_line_slow` (`Front/Line.lean`).
2. Prove L1, L2, L3 and L5; then L4 for app first (80 % of lines), then lam/forallE, then str,
   num, const; then L6. Until a shape's L4 lands, `fast_line` declines that shape (a one-line
   change), so the lane can land shape by shape.
3. Gates: `diff-e2e --refs`, `--jobs 4`, `fuzz.py` against master, `bench.py --set init` and the
   16-thread run.

Expected: `Init` −10 % instructions, −8 % cycles at one thread, 16 threads at con-ron's wall
(−30 %).
