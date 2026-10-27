# Lane hashtpl: a leaner hash template, measured (journal)

**Question.** Does a leaner hash template pay, for the proofs (fewer lines, no raw bridges) and for
speed? The candidates came from two earlier journals: rank 5 of `lrecords.md` §2 (−4 to −7 k proof
lines, 30–50 h) and its §7.4 (the raw bridges stay while the stores' match and hash models read raw
words), and lever (b) of `perfgap.md` §4 (one bounds check per slot, key words through one record
load, region and stamp reads hoisted; estimated 3–5 % speed).

**Answer: no-go.** Both estimates were made before the library and the compiler changed under them,
and both are now too high:

* **Speed.** The template is already tight. The probes are short (1.0–1.3 slots per call), so the
  per-call header dominates, and everything L can still change in it is worth **0.34 % of the
  instructions** (measured with a prototype, §3). "One bounds check per slot" cannot be written in
  L: every `ld64`/`ld64t` is checked by the compiler, and L has no multi-word load. Even removing
  *every* bounds check in the 170 template functions would save 4.0 % of the instructions and
  HASHWALL of the wall time (upper bound, §3.3). That lever belongs to the compiler (§5).
* **Proofs.** The raw bridges are 145 lines in all, not thousands. The library already states the
  exact tables' facts at the field level (`ExactOK` over `fieldsL`/`kfld`, `ConsLibRel.lean`).
  An "exact kit" that also derives the remaining per-store obligations would save about
  **1.2 k lines net** (0.35 % of the proof lines) for 15–20 h. That is about 70 lines per hour,
  and almost no build time, because the instance modules take 1–2 s each (§2).

No pilot landed. Only this journal landed. §5 says what would pay instead.

Base: master 387d835c. Scratch: `_tmp/hashtpl/` (scripts, prototype `proto/Proto.lean`,
profiles `prof/`, bench logs).

## 1. The library and its instances

| part | files | lines |
|---|---|---:|
| cons tables: L templates, specs, relation | `ConsLib`, `ConsLibSpec`, `ConsLibRel` | 3 734 |
| memo tables: L templates and specs, relation | `MemoLib`, `MemoLibRel` | 2 051 |
| slot layout, growth | `SlotGrow`, `SlotGrowSpec`, `StoreGrow` | 816 |
| store relation library | `StoreLib`, `StoreRel`, `StoreFields` | 1 553 |
| **library** | 11 files | **8 154** |
| cons instances (`*Store.lean` + `*Refine.lean`, `Store.lean`/`LitRefine.lean`) | 38 files | 9 900 (7 809 non-blank) |
| memo instances | 37 `MemoSch` values (`X_find`, `X_put`, `X_clear`) | ~1 line each, no proof |

**Instances.** 21 cons schemas for 19 twin tables (`lit` has two finds). 14 are **exact**: the
slot's key word is the key itself, so a probe never reads the record (`app`, `lam`, `forall`,
`const`, `imax`, `max`: two handles packed in one word; `bvar`, `param`, `sort`, `succ`: one word;
`fvar`: two unpacked words; `zero`, `nanon`: no key). 7 are **fingerprint** tables: the key word is
the hash, and a hit runs the match on the record (`let`, `nnum`, `proj` inline; `lit`, `lit_str`,
`nstr`, `ls` through a match function over pool slices). The 37 memos share `MemoLib` without
per-instance proofs.

**Module time** (cold build of 8a84fd4e, `_tmp/buildtime/after-cold.log`, 7 503 s in all): library
51.6 s, cons instances 74.8 s (store 37.9 s, refine 36.9 s), together **1.7 %**. A plain
`lean -Dprofiler=true` run of the slowest instance modules (`LevelStore` 7.3 s and `SortStore`
6.6 s in the cold log) takes 1.3 s each, with no step above 0.2 s: the cold-log figures are
contention. Of the library modules, `ConsLibSpec` takes 12.3 s wall (70 s CPU, parallel: simp 34 s,
grind 8 s) and `MemoLib` 3.8 s. Nothing in this layer is slow.

**Proof lines of the cons instances, by kind** (`_tmp/hashtpl/scripts/decls.py`: top-level declarations
classified by name and statement; non-blank lines):

| kind | exact (13 files) | fingerprint (7) | all |
|---|---:|---:|---:|
| comments and docs | 1 057 | 635 | 1 692 |
| imports, `open`, attributes | 530 | 339 | 869 |
| `ConsOK` (the L fragments' obligations) | 484 | 232 | 716 |
| twin lenses (`Lens`, `withScr…`, `withPers…`) | 450 | 192 | 642 |
| query obligations (`MatchOK`, `HomeOK`, `NewOKR`) | 258 | 335 | 593 |
| word models (`…matchW`, node hashes, `mtM`) | 281 | 264 | 545 |
| schema (`…CS`) | 350 | 163 | 513 |
| schema facts (`…CS_wf`, `…Sch_wf`) | 339 | 83 | 422 |
| other lemmas | 204 | 457 | 661 |
| specs, tests, refinement theorems, L functions | 457 | 398 | 855 |
| **raw bridges** (`…_raw`, `fld_…0`) | **78** | **67** | **145** |
| **frames** (`RFrame`) | 63 | 76 | 139 |

Most `_raw` lemmas are `Iff.rfl` restatements (`ARecRel_raw`), and most `fld_X0` lemmas take two
lines.

## 2. The proof side

The rank-5 estimate (−4 to −7 k lines) assumed that fewer instance obligations (`RFrame`,
`ColFree`, `KMono`, `ConsKeyOK`) and one schema type for cons and memo tables would remove most of
the instance layer. Measured:

* `KMono` and `ConsKeyOK` already have no per-instance proofs (`ConsSch.kp_mono`,
  `ConsSch.WF.kframe`, `qkey_of` are generic). `ColFree` is used in 8 files, 20 lines.
* The exact tables' match and hash are already related to the record's fields once, in the
  library (`ExactOK.mt`, `ExactOK.hs` over `fieldsL`). Each instance proves them for its own raw
  model (`appCS_wf.ex`, about 15 lines).
* Cons and memo tables have different layouts and protocols: two-word slots with a tier slot base
  and records, against four-word slots with an epoch stamp and no records. A common schema would
  share the hash (`homeW`, already shared through `SlotGrow`) and little else. The memo instances
  have no proofs to save.

**What a leaner template could still remove** is an "exact kit": for the 14 exact tables, derive
`mc`, `mtM`, `hsM`, `vsM`, `recW` and the room test from a smaller descriptor (arrays, key width,
packing, hash), and give a generic record relation `fieldsL C m t i = enc a` (`enc` the twin key's
words). Then `ConsOK.match_`/`recs`/`room`, `ExactOK`, `RFrame`, `MatchOK`/`HomeOK`/`NewOKR`, the
raw bridges and the raw word models go. Each instance keeps its hash proof (`ihash`, `ihashG`), the
skip word, the twin key's encoding with its injectivity, the lens and the twin unfolding
(`internE_X_run`). From the table above: about 290 (`ConsOK`) + 250 (schema facts) + 260 (query
obligations) + 180 (models) + 175 (schema) + 78 (raw) + 63 (frames) + ~200 comments ≈ 1.5 k lines
removed from the exact stores, against ~300 lines of kit. **Net about 1.2 k lines (0.35 % of the
341.6 k proof lines), build time ±0 (the instance modules take 1–2 s each), for 15–20 h**, about
70 lines per hour. The 7 fingerprint tables do not fit the kit: their matches read pool slices.

Downstream proofs use the per-store relations by name (`ARecRel` in `ArenaRel`, `View`, `DerRel`,
`DerRelBase`, `ScratchRefine`), so each relation would stay as a definition equal to the kit's.

## 3. The speed side

### 3.1 Profile (exact counts, `scripts/asmprof.py`, Init `init435.ndjson`)

273.4 G instructions in all (perfgap measured 359 G on 1134dff6; tierswitch, memlay and leafgen
landed since). The template functions:

| | instructions | share | calls | per call |
|---|---:|---:|---:|---:|
| memo `X_find` (37) | 24.85 G | 9.09 % | 401 M | 62.0 |
| memo `X_put` | 14.16 G | 5.18 % | 171 M | 83.0 |
| memo `X_clear` | 1.41 G | 0.52 % | 56 M | 25.0 |
| cons `X_find` (21) | 15.59 G | 5.70 % | 233 M | 66.9 |
| cons `X_push` | 9.10 G | 3.33 % | 86 M | 105.6 |
| cons `intern_X` | 13.44 G | 4.91 % | 220 M | 61.1 |
| **all** | **78.5 G** | **28.7 %** | | |

The top ones are `ilm_find` (14.2 G, 59.7/call), `app_find` (11.5 G, 66.7), `intern_app` (10.5 G),
`ilm_put` (9.6 G), `app_push` (7.5 G).

**The probes are short.** Per-block counts (`_tmp/hashtpl/scripts/blk.py`): `ilm_find` reads 240.3 M slots in
238.5 M calls (1.01 per call), and 232.6 M of them are free (a miss at the first slot); hits are
2.4 %. `app_find` reads 225.8 M slots in 172.8 M calls (1.31 per call): 91 M hits, 82 M free
slots, 53 M advances. So the per-slot code runs about once per call, and the fixed header (stamp,
region, hash, key word) is most of the cost: in `ilm_find` the entry, the region header and the
hash are 43 of the 60 instructions.

### 3.2 What L can change, prototyped

`_tmp/hashtpl/proto/Proto.lean` rewrites `checkerProg` before compiling it (unproved; `lake env lean --run`, 3 s;
with no rule it reproduces `checker.s` byte for byte):

* **G**: the home hash computes `h * golden` once (`g := h * golden; j := mulhi(g ^ (g >> 32), n)`;
  126 functions; one fresh local).
* **W**: the probe wrap `j := (j + 1) * u64(j + 1 < n)` becomes `j += 1; if n <= j { j := 0 }`
  (equal for every word, so the models do not change).
* **M**: the memo find computes the slot address `(b + j) * 4` once per probe.

| variant | instructions | Δ |
|---|---:|---:|
| master | 273.416 G | |
| G | 273.099 G | −0.12 % |
| W | 273.034 G | −0.14 % |
| G + W | 272.718 G | −0.26 % |
| G + W + M | 272.489 G | **−0.34 %** |

The rest of the header is the compiler's code: each constant-index read (`CTL[cs]`, the region
header `A[0..2]`, `sa⟨t⟩[0..1]`, `CTL[62]`) costs a length compare, a branch, a base load and the
load. L cannot hoist the region and stamp reads further. The find reads each of them once already.
The put reads them again on a miss, because its callers probe right before it. Moving them into the
callers would change the interface of 37 memos and of every hand-proved caller.

### 3.3 Bounds checks, the compiler's part

Executed bounds checks on Init (`_tmp/hashtpl/scripts/bchk.py`: a `cmp` followed by `jae`/`jbe ca_error`, 2
instructions each):

| | constant index | variable index |
|---|---:|---:|
| template functions | 3.13 G | 2.29 G |
| the rest | 2.17 G | 6.80 G |

"One check per slot" would save at most half of the template's variable-index checks, about 1.1 G
checks, or 2.3 G instructions (0.8 %). It needs a multi-word load in L and the compiler, or a check
elimination in the compiler. The upper bound for the whole template is to delete all 2 446 checks of
the template functions from `checker.s` (`_tmp/hashtpl/scripts/nobounds.py`, unsound, measurement only):
262.588 G instructions, **−3.96 %**.

Wall time (`scripts/bench.py --set init --reps 5`, interleaved, `taskset` on two cores):

HASHBENCH

## 4. Decision

* **Speed: no-go at L level** (0.34 % of the instructions, and every probe loop's proof would
  change). The bounds-check lever is a compiler change (§5).
* **Proofs: no-go for the rank-5 rewrite.** The instance layer has no large raw-bridge share left
  to remove. The exact kit would save about 1.2 k lines for 15–20 h with no build-time gain. That
  is below the other open candidates in `lrecords.md` §2 (locals normal form, model-generator
  coverage). It can wait until a twin bump changes the exact tables anyway.
* Nothing landed but this journal. No deviation.

## 5. What would pay instead

* **Constant-index bounds checks in the compiler**: 5.3 G executed checks program-wide (10.6 G
  instructions, 3.9 %) compare a constant index against an array length that does not change
  after startup. If the compiler knew a minimum length per array (one check against the table's
  lengths at entry), it could drop them. This is not designed here. Like perfgap §4 (a), it would
  be a local simulation lemma in `Compiler/`, and it would help every function, not only the
  template.
* **Array base loads**: 7.6 G instructions (2.8 %) reload an array's base from the table before
  every access (`movq 848(%r15), %rcx`). Caching it within a straight-line block is the CSE of
  perfgap §4 (a).
* The exact kit (§2) when a twin bump touches the exact tables anyway.
