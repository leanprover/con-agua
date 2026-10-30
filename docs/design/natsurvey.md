# Lane natsurvey: where the word ↔ `Nat` proof lines are, and what could absorb them (analysis journal)

**Question** (work queue "improve L": make the L ↔ Lean-model simulation proofs smaller by moving
work into the verified compiler or the libraries once). lnext2.md §1.3 counts ~32 k proof lines of
word ↔ `Nat` reasoning; forloop.md §3–4 showed that loop indices are not where they are. Where are
they exactly (by kind, by file and library, generated or hand), and which recurring patterns could
be absorbed by (a) `Nat`-valued library specs, (b) a typed-view layer for packed records, (c)
generator support, (d) grind/simp sets, (e) an L feature proved once in the compiler? Prototype the
top candidates on 2–3 representative proofs, measure, rank.

Base: master 690629a6. **Only this journal lands.** Scripts and data in `_tmp/natsurvey/`
(`lib.py`: lnext2's parser, pointed at this master; `natlines.py`/`merged.py`: the kinds;
`shapes.py`, `haves.py`, `sizes.py`, `fam.py`, `lacc.py`: the recurring shapes; `pair.py`:
interleaved elaboration of a master copy and a prototype copy of one module; `rss.py`: peak RSS;
`*.orig.lean`: the master copies). The prototypes are on branch **`natsurvey-proto`** (kept, not
for landing; each commit holds one variant of its files):

| commit | what |
|---|---|
| 5bcf1f2d | `ispW_ok` (`Arena/WhnfIotaRefine2`): word arithmetic closed by `lia` |
| 40cfc6e6 | `caps_rel` (`Rom/CIReadRefCaps`): offsets by `lia`, the `comega` macro removed |
| 7511d90e | `top_move` (`Arena/SlotTop`): comparisons by `lia` |
| d2a6644d | `ispW_ok` with a bounded-array stub (`Mem.size64_lt`, a `sorry` stub) |
| 1de8c121 | `caps_rel` with the literal-offset simp kit (`off_toNat`) |
| 329d3aef | `cpMem_eq` (`IndSumSpec/ConsBlockRecsTF`), `rmMem_eq` (`IndSumSpec/TsrW`) with the kit |

**Short answer.**

* The 32.3 k lines are lines that *mention* the conversion: a third of them are statements (the
  twin is `Nat`-valued, L is word-valued, so every refinement names `x.toNat` in its statement and
  its decoders take `Nat` positions). They are spread over every family at 8–17 % of its proof
  lines; no family, file or library holds more than 1 % of them. All are hand-written: the
  generated program files hold none, and `l_model` emits no source lines.
* The one pattern that is both large in places and absorbable is **literal record offsets**:
  `(c + 9).toNat = c.toNat + 9`, stated as one `have` per offset, and then the custom dischargers
  that rewrite with those facts and clear them because `omega` slows down exponentially with them
  in context (`comega` and five more such dischargers). A five-line kit lemma, `off_toNat`, used as
  `simp (disch := omega) only [off_toNat]`, removes the facts and the workarounds. On three proofs:
  **−13, −23 and −16 lines** (−6 %, −74 %, −59 % of the theorem), **elaboration −59 %, −82 %,
  −98 %** (6.1 → 2.5 s, 6.6 → 1.2 s, 14.9 → 0.35 s), peak RSS 3.0 → 2.5 GB and 4.0 → 2.4 GB.
  Go, but it is small in total: −0.4 to −0.7 k lines.
* `lia` (grind's linear arithmetic, which knows `UInt64` wrap-around) as the closer for all word
  arithmetic removes 2–16 % of a dense theorem's lines but costs 0.06–0.17 s per call in a large
  context (grind preprocesses every hypothesis): elaboration ×2.4–4.3 on the pilots. No-go as a
  default.
* A memory with bounded arrays (L core) saves 1 % of a dense theorem (`ispW_ok` −2 lines);
  `Nat`-offset addressing `A[b + k]` in L would reach at most the ~1.1 k literal-offset lines the
  kit already reaches, at the price of a compiler proof, a generator change and every model
  touching a record; typed views and generator facts have nothing left to absorb (§3). No-go.

## 1. Where the lines are

Same matcher as lnext2 §1.3 (`patterns.py`, group "c wrap": `.toNat`, `toNat_`, `2 ^ 64`,
`UInt64.`, `BitVec.`, `< 2 ^ 32/62/63`, `.size`, `len64`, …; a line counted once), over the
non-generated proof lines of this master: **32,341 of 302,713 lines** (lnext2: 32,039). Each line
is given one kind, first match wins (`natlines.py`; the regexes are there):

| kind | lines | share | in statements | in proofs | refinement | spec | model eq. | other lemma |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| address arithmetic: `(q + k).toNat`, array index `[i.toNat]?`, `x < (m.arr64 A).size`, `toNat_add/sub/mul` | 7,847 | 24 % | 2,317 | 5,530 | 3,239 | 482 | 1,233 | 1,495 |
| record field decode: decoders at `Nat` positions (`decCI m q.toNat`, `iwN`, `hd?`, `hlist?`, `decHL`), results `(r.headD 0).toNat`, handle bits `>>> 28` | 5,851 | 18 % | 3,110 | 2,741 | 2,978 | 794 | 543 | 666 |
| overflow / range side conditions: `< 2 ^ 64`, `< 2 ^ 32`, `size < 2 ^ 63`, `Nat.mod_eq_of_lt`, `omega` steps | 4,299 | 13 % | 1,465 | 2,834 | 1,683 | 260 | 842 | 1,013 |
| length / count values: tops (`iwTop`, `spTop`, `erecTop`), `.length`, `x.toNat = n` | 3,088 | 10 % | 1,402 | 1,686 | 1,768 | 213 | 379 | 305 |
| other | 3,028 | 9 % | 986 | 2,042 | 1,262 | 217 | 456 | 540 |
| compiler and final theorem (`Compiler/`, `Final/`, `L/`, …: already proved once) | 2,714 | 8 % | 639 | 2,075 | 458 | 37 | 297 | 1,133 |
| constants and round trips: `(52 : Word).toNat`, `reduceToNat`, `UInt64.ofNat`, `toNat_ofNat_of_lt` | 2,630 | 8 % | 378 | 2,252 | 1,273 | 108 | 426 | 468 |
| comparisons: `lt_iff_toNat_lt`, `le_iff_toNat_le`, `toNat_inj`, `not_le` | 1,886 | 6 % | 193 | 1,693 | 858 | 54 | 328 | 470 |
| twin interface: `x.toNat` as a twin argument (`.run`, `decE`, `fe`) | 998 | 3 % | 663 | 335 | 566 | 255 | 27 | 70 |
| **all** | **32,341** | | **11,153** | **21,188** | 14,085 | 2,420 | 4,501 | 5,860 |

* **Statements are a third** (11.2 k lines: hypotheses and conclusions). They name the twin's
  `Nat` arguments and the decoders' `Nat` positions. They would move, not vanish, under any
  scheme that keeps L word-valued: a `Nat`-valued model would carry the same conversions in its
  L ⊑ model spec instead.
* **Generated vs hand.** All of these lines are hand-written. The generated program files
  (`Checker/Prog*`, `Asm*`, …) hold almost none, and `l_model`'s specs and models emit no source
  lines. 7.0 k of the lines sit in modules that contain an `l_model` (refinements and helpers next
  to a generated model).
* **By directory:** `Arena/` 22,338; `Front/` 2,701; `Compiler/` 1,881; `Scan/` 1,297; `Checker/`
  1,195; `Verdict/` 1,193; `Rom/` 903; `Final/` 456; `L/` 288. **By family** (`fam.py`) the share
  of a family's proof lines is 8–17 % nearly everywhere (`Front` 14 %, `Whnf*` 12 %, `Decl*` 9 %,
  `IndT` 12 %, `IndPosSpec` 10 %, `Scan` 17 %, `RecClassSpec` 15 %, `Rom` 14 %, `PromoteCIRef`
  17 %), higher only in the small table libraries (`Slot*` 25 %, `Pool*` 31 %). The densest
  file has 273 lines (`Arena/WhnfIotaRefine2`), the densest theorem 81 (`appLoop_ref`). Within
  theorems, the lines are 10–40 % of the lines of most theorems that have any. **There is no
  hotspot**: anything that absorbs them has to be a cross-cutting mechanism.

### 1.1 The recurring shapes (`shapes.py`, `haves.py`, `sizes.py`; checker side, 29.6 k lines)

| shape | lines |
|---|---:|
| `… < (m.arr64 A).size`, `len64` (any array-size mention) | 4,794 |
| — of which a size bound `(m.arr64 A).size < 2 ^ k` | 827 (597 in statements) |
| `< 2 ^ 64` no-overflow condition | 2,028 |
| global tops (`iwTop`, `spTop`, `erecTop`, `rdW (… CTL) k`) | 2,237 |
| comparison transport (`lt_iff_toNat_lt`, `le_iff_toNat_le`, `UInt64.not_le/not_lt`) | 1,839 |
| statement-only twin argument `x.toNat` | 1,668 |
| `(by omega)` / `by simp; omega` inline side goals | 1,260 |
| array access by `Nat` (`[i]?`, `.set!`, `[x.toNat]`) | 1,114 |
| literal-offset mention `(c + k).toNat` | 1,079 (965 in proofs) |
| — of which offset facts `(c + k).toNat = c.toNat + k` | 697 |
| `< 2 ^ 32` field-width bound | 1,066 |
| `rw [UInt64.toNat_add …] … omega` (the proof of an offset fact) | 1,064 |
| `UInt64.toNat_inj` | 881 |
| round trip `toNat_ofNat_of_lt` / `ofNat_toNat` | 857 |
| `(r.headD 0).toNat` (a result decoded) | 694 |
| constants `(k : Word).toNat = k`, `reduceToNat` | 717 |
| handle bits (`>>> 28`, `&&&`, tier/idx) | 525 |

The most frequent `have` statements over words (`haves.py`, normalized, 5,405 such `have`s):
`(x + k).toNat = x.toNat + k` **622**; `iwTop m < 2 ^ 64`-style word bounds 200; `(m.arr64 A).size <
2 ^ 63` 182; `(x + y).toNat = x.toNat + y.toNat` 123; size equalities across states 105;
`(1 : Word).toNat = 1` 88; `(l - 1).toNat = l.toNat - 1` 71. The literal offset facts sit in 397
theorems, 615 `have`s; 286 theorems have one, **111 have two or more (329 `have`s), 19 have five or
more**. The same lemma exists in local copies: 36 lemmas state `(a + b).toNat = a.toNat + b.toNat`
(`widx2`, `word_add_toNat` ×3, `toNat_add_small` ×2, `toNat_add_of_get`, …) and 20 state
`(x + 1).toNat = x.toNat + 1`.

L side (`lacc.py`, non-generated L code): array accesses `A[x + k]` with a literal offset
**1,826**, `A[x]` 1,201, `A[x + y]` 155, `A[other]` 188. The literal offset is the packed record:
a base word plus a field offset.

### 1.2 What a dense refinement does with them

Read in `ispW_ok` (`WhnfIotaRefine2`, 70 of 165 lines), `cns_ref` (`IndT/RecGen28`, 80 of 245),
`caps_rel` (`Rom/CIReadRefCaps`, 55 of 203), `top_move` (`SlotTop`, 47 of 109):

* **Facts that only feed `omega`.** `omega` does not know `(a + b).toNat` or `(a - b).toNat`
  (checked: it fails on `(so + j).toNat = so.toNat + j.toNat` from `so.toNat + j.toNat ≤ sz < 2 ^ 63`),
  nor that `x.toNat < 2 ^ 64`. So each no-wrap fact is a `have` (`hsoj`, `hn9 … hn12`, `hc1 …
  hc13`), each subtraction an explicit `toNat_sub_of_le` with its `le_iff_toNat_le` side goal, and
  each word comparison a `lt_iff_toNat_lt.mpr (by omega)`.
* **`omega` slows down with them.** With many chained `(c + k).toNat = c.toNat + k` equalities in
  context, `omega`'s equality elimination builds justifications exponential in their number. Three
  proofs carry a workaround that rewrites with the facts and clears them before each `omega`:
  `caps_rel`'s `comega` macro (">15 GB for the whole proof" before it, per its comment),
  `cpMem_eq` ("the module peak at ~10 GB") and `rmMem_eq`. There are six such dischargers, in five
  files (`CIReadRefCaps`, `ConsBlockRecsTF` ×2, `TsrW`, `ConsSumCtors`, `ClassFeR`); two of them
  also clear the facts. PLAN.md's memory note (CIReadRefCaps) is the same effect.
* **Size threading.** The array-size bound (`(m.arr64 SPN).size < 2 ^ 63`) is carried from state
  to state (`hspn₂ := by rw [hsz2]; exact hS.spn`) and passed to library lemmas (`SpineR.keep`).
* **Record writes and reads at offsets** (`cns_ref`'s 13-word record: `set64IW_get` chains with
  `ite_eq_right (by omega)` per field). The decoders on the twin side are already `Nat`-positioned
  (`decTM m p0`, `iwN m (nm.toNat + 9)`), so the gap is only `nm + 9` against `nm.toNat + 9`.

## 2. Prototypes

All measured with `pair.py`: a master copy and the prototype copy of the module elaborated in
alternation (`lake env lean`, profiler trace, "elaborating proof of"), 3 rounds, medians; load 8–14.
Lines are the theorem's code lines (no comments, no blanks), statement included.

### 2.1 `lia` as the closer for word arithmetic (candidate d)

`lia` (grind's linear integer arithmetic with its `UInt64` embedding: it knows `(a + b).toNat` modulo
`2 ^ 64` and the bounds of every word) proves all the no-wrap, subtraction and comparison facts above
in an empty context in 15–40 ms. In the pilots every such `have` that only fed `omega`, and every
`omega` that consumed one, became `lia`:

| theorem | `lia` calls | lines master → proto | elaboration s master → proto |
|---|---:|---:|---:|
| `ispW_ok` (hand loop over a spine slice) | 11 | 165 → 138 (−16 %) | 0.59 → 2.43 (×4.1) |
| `caps_rel` (15-word ROM record) | 57 | 203 → 191 (−6 %; file −22 with the macro) | 6.26 → 14.13 (×2.3) |
| `top_move` (table sweep, comparisons) | 11 | 109 → 107 (−2 %) | 0.39 → 1.08 (×2.8) |

The profile says why: in `ispW_ok`'s module, `grind simp` takes 1.08 s and `grind cutsat` 15 ms.
Each call preprocesses every hypothesis in the context, 0.06–0.17 s per call in a refinement's
context; there is no option to restrict grind to some hypotheses. Two `top_move` goals (a `≠` with
a successor) needed the old proof. Scaled by wrap density (the pilots are 36 % wrap lines, the
refinement layer 13 %), a rollout would remove ~3–5 k lines for +0.5 to +1.5 k module-seconds of
elaboration (+10–25 % of the build, which on CI is CPU-bound). **No-go as a default**; fine for a
handful of facts in a small context.

### 2.2 The literal-offset simp kit (candidates a + d)

One lemma, in the shape `simp` can use with the bound found by its discharger:

```lean
theorem off_toNat {b : Word} {k : Nat} (h : b.toNat + (OfNat.ofNat k : Nat) < 2 ^ 64) :
    (b + (no_index (OfNat.ofNat k) : Word)).toNat = b.toNat + (OfNat.ofNat k : Nat) := by
  change b.toNat + k < 2 ^ 64 at h
  show (b + UInt64.ofNat k).toNat = b.toNat + k
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']; omega
```

`simp (disch := omega) only [off_toNat]` rewrites every `(c + 9).toNat` of the goal to
`c.toNat + 9`, discharging `c.toNat + 9 < 2 ^ 64` from the room hypothesis in context. Two details:
the literal must be matched as `no_index (OfNat.ofNat k)`, and the right side must be the `Nat`
numeral `OfNat.ofNat k`, not the raw `k` (`omega` treats a raw `nat_lit 10` as an atom). The offset
`have`s go, and the rewrite-and-clear dischargers become
`(try simp (disch := omega) only [off_toNat]) <;> omega`:

| theorem | lines master → kit | elaboration s master → kit | file wall s | peak RSS |
|---|---:|---:|---:|---:|
| `caps_rel` | 203 → 190 (−6 %) | 6.09 → 2.48 (−59 %) | 9.3 → 4.0 | 2.48 → 2.34 GB |
| `cpMem_eq` (11-word record copy) | 31 → 8 (−74 %) | 6.60 → 1.19 (−82 %) | 14.1 → 11.3 | 3.02 → 2.51 GB |
| `rmMem_eq` (11-word record rebuild) | 27 → 11 (−59 %) | 14.93 → 0.35 (−98 %) | 18.0 → 3.6 | 3.98 → 2.40 GB |

File code lines, with a local copy of the kit in each (5 lines): −12, −18, −11; with the kit shared,
−17, −23, −16. `caps_rel`'s `comega` shrinks from a 4-line macro listing 13 names to one line. The
pilots' `set_option maxHeartbeats 2000000` were left in place; they may no longer be needed.

Where it does not help: `cns_ref` reuses each of its four offset facts in a dozen `omega`s inside
`set64IW_get` chains; there the `have`s are the cheaper form, and the kit would save the
`rw [hn9] at b9` steps only (about −4 lines, not prototyped). The kit pays where offsets are many
and each fact is used once or twice, and wherever `omega` chokes on chained facts.

**Rollout estimate.** The 111 theorems with two or more literal offset facts (329 `have`s), the
six rewrite-and-clear dischargers, and the 36 local copies of the add lemma: −0.4 to
−0.7 k lines, and seconds per theorem where the facts are many (19 theorems with five or more;
the three pilots gave −24 s of elaboration together). 6–10 h: the kit in a shared library module
(`off_toNat`, its variable-offset sibling under `a.toNat + b.toNat < 2 ^ 64`, and the
`set64`-at-offset read lemma in the same shape), then the 19 densest theorems and the six
dischargers, the rest on touch. **Go** (small).

### 2.3 Bounded arrays in the memory (candidate e, L core)

L's `Mem` lets an array have any length, so every proof that needs `x.toNat + k < 2 ^ 64` carries
`(m.arr64 A).size < 2 ^ 63` from an invariant and transports it across states. If `Mem`'s word arrays
had a type-level bound (a subtype field, `set!` keeps the size), `Mem.size64_lt : (m.arr64 A).size <
2 ^ 62` would hold for every memory. Simulated in `ispW_ok` with a `sorry` stub of that lemma: the
transports go (`hspn₂`, two uses of `hS.spn`), but `omega` still needs the bound in context, so one
`have := Mem.size64_lt m SPN` comes back: **165 → 163 lines (−1 %)**. (The pilot's
`grind [Mem.size64_lt]` arguments cost +1.8 s; with library lemmas such as `SpineR.keep` dropping
the parameter, time is unchanged.) The ceiling is the 827 size-bound lines, 597 of them statement
hypotheses, spread over 710 declarations (at most 6 in any one). **No-go** for proof size; a possible
statement clean-up some day.

### 2.4 Not prototyped

* **`Nat`-offset addressing in L (e).** `A[b + k]` with a literal `k` read at index `b.toNat + k`,
  out of bounds if that is ≥ the length; compiled as `cmp b, len − k; jae` and a displacement
  `[base + 8 b + 8 k]` (no extra instruction). Models would read `a[b.toNat + k]?` and guard
  `b.toNat + k < size`, so no offset fact would exist at all. But the ceiling is the 1,079 literal-
  offset lines, most of which the kit (§2.2) reaches without changing L; the cost is a compiler
  proof for the new index rule, `ModelGen` support, and new models for every function with one of
  the 1,826 sites, whose refinements would all have to be redone (a retrofit is out; on new code
  only). 25–40 h. **No-go.**
* **A typed-view layer for packed records (b).** The view exists already on the decode side:
  `decCI`, `decTM`, `decCaps`, `iwN`, `hd?`, `hlist?` are `Nat`-positioned and return twin values
  (the 3.9 k "decode" lines are mostly statements naming them). What is left between L and the
  view is the `b + k` ↔ `b.toNat + k` step, which is §2.2 or the L feature above. **No-go** as a
  separate layer.
* **Generator support (c).** A `Nat`-form guard (`nm.toNat + 9 < size`) cannot be emitted without
  knowing that `nm + 9` does not wrap, which is the L feature above. `Nat`-indexed loop models were
  measured by forloop.md: −2 to −3 lines per loop. **No-go.**
* **A `Nat`-valued library spec for record reads (a)** in the form the question suggests exists
  already for `IW` (`iwN_rdW_at` in `RecSim.lean`, 46 uses; `rd_iwN` in `CtxFields.lean`, 31 uses:
  "the word at `w + k` is `ofNat v` and `v < 2 ^ 64`"). Its siblings for `EREC`, `DLP` and `SPN` are
  the local copies counted in §1.1; they belong in the kit of §2.2.

## 3. Ranked recommendation

| rank | candidate | measured | estimate | cost | verdict |
|---:|---|---|---|---|---|
| 1 | literal-offset simp kit (`off_toNat`, `simp (disch := omega)`), and the add-lemma copies merged into it | −6 / −74 / −59 % lines, −59 / −82 / −98 % elaboration, −0.1 to −1.6 GB peak | −0.4 to −0.7 k lines; seconds per dense theorem | 6–10 h | **go**, small; densest first, the rest on touch |
| 2 | `lia` as the word-arithmetic closer | −16 / −6 / −2 % lines, elaboration ×4.1 / ×2.3 / ×2.8 | −3 to −5 k lines for +0.5 to +1.5 k module-s | 20–40 h | no-go as a default; local use only |
| 3 | bounded arrays in `Mem` (L core) | −1 % (`ispW_ok`) | ≤ −0.8 k lines, mostly hypotheses | 6–10 h, wide | no-go for size |
| 4 | `Nat`-offset addressing `A[b + k]` (compiler) | — | ≤ −1.1 k lines, overlapping rank 1 | 25–40 h + retrofit | no-go |
| 5 | typed record views; generator `Nat` facts | — | ≈ 0 beyond ranks 1 and 4 | — | no-go |

**Honest summary.** The 32 k lines are not one mechanism to move into the compiler: a third are
statements that name the twin's `Nat` values, and the rest is a thin layer (10–40 % of a theorem's
lines) of one-line bridges spread over every family. The one absorbable pattern, literal record
offsets, is worth one small kit, mainly for elaboration time and memory where `omega` meets many
offset facts; its line gain is in the hundreds. Larger reductions of the refinement layer would
have to come from its shape (refgen.md: the walk kit when touching a file), not from word ↔ `Nat`.

No proof, L code, `checker.s` or statement changed on master.

## 4. Rollout of rank 1 (lane offkit)

**The kit** is `ConAgua/L/WordOff.lean` (a `module`, imports only `L.Syntax`): `off_toNat` as
in §2.2, and `off_omega`, a macro for `(try simp (disch := omega) only [off_toNat]) <;> omega`
(`omega` after the goal's literal offsets are rewritten). Both are in namespace `L`. The variable-offset
sibling and the `set64`-at-offset read lemma of §2.2 were not needed by any site below and are not
added.

**Sites** (the 19 densest theorems by literal offset `have`s, `_tmp/offkit/dense2.py`, the six
dischargers among them; 615 such `have`s in 397 theorems, 13 with five or more, 19 with four or more):

| theorem | what changed |
|---|---|
| `caps_rel` (`Rom/CIReadRefCaps`) | 12 offset facts and the `comega` macro gone; `off_omega` everywhere |
| `cpMem_eq`, `riMem_eq` (`IndSumSpec/ConsBlockRecsTF`), `rmMem_eq` (`TsrW`), `ciRecMem_eq` (`ConsSumCtors`), `cfrMem_eq` (`ClassFeR`) | the rewrite-and-clear dischargers become `simp (disch := off_omega) only [rdW_set64_ne_er]`; 20 + 6 + 15 + 6 + 6 facts gone |
| `rule_rel` (`Rom/CIReadRefRule`) | 10 facts gone; uses as `off_toNat (by omega)` |
| `ci_rec`, `ci_ctor` (`Rom/CIReadRefCI`) | the `hpk` `∀` fact and 6 offset facts gone; the `omega`s that needed them are `off_omega` |
| `recRW_twin` (`Front/IndInstallRefine3`) | 4 facts gone (`hq1` stays: a hypothesis of a callee's statement mentions `(q1 + 1).toNat`) |
| `iccW_ok` (`WhnfIotaRefine6`), `projB_rel` (`PromoteCIRef/Proj`), `blockGo_ok'` (`Checker/HoistWalkRef`), `iirW_stage` (`IndInstallSpec/IcaW`) | 5, 4, 3, 4 facts gone |
| `rd2W_of`, `rd4W_of`, `rd5W_of` (`PromoteCIInfra`) | 8 facts gone (the family kept uniform) |
| `infer_decCV_words` (`InferLeaves`) | 4 facts and the helper `infer_toNat_add_small` (no other user) gone |
| `nty_ref` (`Verdict/PosNty`) | the 3 `key + k` facts gone; the nested `q + 1 + k` facts stay (`off_toNat`'s bound for `(q + 1) + 3` names `(q + 1).toNat`, which `omega` cannot bound) |

The `set_option maxHeartbeats` raises of `cpMem_eq` (2 M), `rmMem_eq` (2 M), `ci_rec` (4 M) and
`rule_rel` (8 M) are no longer needed and are removed.

**Skipped, measured:**

* `cns_ref` (`IndT/RecGen28`, 5 facts): without the four `nm + k` facts, 22 `omega`s needed
  `off_omega` and two still failed (the facts are reused inside `set64IW_get` chains, §2.2). Kept.
* `vgStore_facts` (`PromoteRecRef`, 5 facts): `−5` lines, but `simp (disch := omega)` over its
  ten goals took the theorem from 0.39 to 1.66 s (`pair.py`, 3 rounds). Kept.
* `cieW_ok` (`DeclCanonInfo`, 8 facts): its facts come from array reads (`toNat_add_of_get`), with no
  room bound `p.toNat + 1 < 2 ^ 64` in context for `omega`; the kit has nothing to discharge with.

**Measured** (`_tmp/offkit/measure.py`: each changed module's master text and branch text elaborated
in alternation, `lake env lean`, 3 rounds, medians, 4 modules at a time, load 17–24; dependencies are
the branch's oleans for both; lines are code lines without blanks and comments):

| module | lines | wall s | CPU s | peak RSS MB |
|---|---:|---:|---:|---:|
| `Arena/IndInstallSpec/IcaW` | 840 → 836 | 7.7 → 8.0 | 17.3 → 19.8 | 2529 → 2509 |
| `Arena/IndSumSpec/ConsBlockRecsTF` | 1014 → 984 | 12.7 → 10.4 | 23.5 → 16.8 | 3025 → 2486 |
| `Arena/IndSumSpec/ConsSumCtors` | 265 → 259 | 5.2 → 5.0 | 7.1 → 7.1 | 2252 → 2249 |
| `Arena/IndSumSpec/TsrW` | 554 → 537 | 18.2 → 3.1 | 24.4 → 6.1 | 3906 → 2382 |
| `Arena/InferLeaves` | 733 → 727 | 4.5 → 4.5 | 8.2 → 8.1 | 1954 → 1957 |
| `Arena/PromoteCIInfra` | 227 → 220 | 1.4 → 1.4 | 2.2 → 2.2 | 1796 → 1792 |
| `Arena/PromoteCIRef/Proj` | 613 → 609 | 3.0 → 2.9 | 5.7 → 5.4 | 2066 → 2066 |
| `Arena/RecGenSpec/ClassFeR` | 482 → 476 | 6.7 → 6.6 | 9.4 → 9.1 | 2358 → 2357 |
| `Arena/WhnfIotaRefine6` | 564 → 560 | 1.4 → 1.3 | 3.3 → 3.2 | 2217 → 2208 |
| `Checker/HoistWalkRef` | 722 → 717 | 1.4 → 1.4 | 2.6 → 2.6 | 2012 → 2019 |
| `Front/IndInstallRefine3` | 350 → 347 | 5.3 → 3.2 | 9.2 → 5.1 | 2713 → 2079 |
| `Rom/CIReadRefCI` | 416 → 404 | 3.0 → 2.6 | 5.6 → 5.0 | 2449 → 2364 |
| `Rom/CIReadRefCaps` | 378 → 358 | 6.3 → 3.3 | 7.8 → 5.1 | 2484 → 2368 |
| `Rom/CIReadRefRule` | 281 → 271 | 6.8 → 2.1 | 7.9 → 3.2 | 3079 → 2302 |
| `Verdict/PosNty` | 194 → 191 | 1.4 → 1.3 | 1.6 → 1.5 | 2580 → 2576 |
| **total (15 modules)** | **7633 → 7496 (−137)** | **84.8 → 57.1 (−27.7, −33 %)** | **135.8 → 100.4 (−35.4, −26 %)** | max **3906 → 2576** |

With the kit module (11 code lines) the net is −126 lines. `IcaW`'s +2.5 CPU-s is noise:
`iirW_stage` itself is 1.02 → 1.05 s (`pair.py`), the file 8.97 → 7.87 s wall in that run. The
gain is where §2.2 put it: the modules whose `omega`s met many chained offset facts (`TsrW`
−15 s, `CIReadRefRule` −4.7 s, `CIReadRefCaps` −3 s, `ConsBlockRecsTF` −2.3 s,
`IndInstallRefine3` −2.1 s) and their peak memory (−0.5 to −1.5 GB); elsewhere the change is lines only.
Line savings are at the low end of §2.2's estimate for the densest sites; the remaining 300-odd theorems
with one to three facts are left for "on touch" (`off_toNat (by omega)` in place of a `have`, or
`off_omega` in place of an `omega` that needed one).
