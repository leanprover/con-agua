# Lane lconstructs: L constructs shaped like the twin's code, measured and scoped

**Question.** Rank 3 of `lrecords.md` §2 estimated −5 to −12 k proof lines for 40–80 agent-hours from
constructs shaped like the twin's code: a tag `match`, error propagation, a bounded `for`. The user's
principle: L sits between x86 and Lean, and whatever the compiler (or L core) proves once is not
proved again per function. Wanted are features that make L code smaller or simpler, and features or
semantics that make the simulation proofs smaller. Error propagation is out: `abort` cannot be
caught in L, and the `Except` binds against the twin are already handled generically by `ErrClaim`.

Base: master 98c46a99. Scripts and prototype outside the repository, in `_tmp/lconstructs/`:
`lblocks.py` (extracts every `lfn`/`lblk`), `lshapes.py` (L shapes), `pshapes.py` (proof footprint,
reuses `_tmp/lrecords/measure.py`), `proto/` (the prototype files, checked in the lane's worktree).
No proof changed.

**Short answer.** The estimate does not hold. Without error propagation, which was the largest
part of it (the `Verdict/` glue), the twin-shaped constructs have a small proof footprint: the
proofs already reach tags, views and handle words through named functions (`e_view`, the `view_*`
lemmas, the handle API of records-api). What the constructs can do cheaply is make **L code
shorter and closer to the twin's text, with identical statements**, so that `checker.s` and every
proof stay as they are. Of the proof savings, only the counted loop has a clear one, and it comes
from a loop rule proved once plus models indexed by a `Nat`, not from the syntax.

| # | construct | go | L lines | proof lines | cost (h) | `checker.s` |
|---:|---|---|---:|---:|---:|---|
| 1 | `(t, i) := node R⟦h⟧`: the checked node read, as sugar | **go** | −306 | 0 | 4–6 | identical |
| 2 | `for j < n { … }` as sugar, plus the counted-loop rule `Triple.forUp` in L core | **go** | −60 to −100 | −25 to −40 per loop reproved | 5–8 | identical |
| 3 | `l_model` option: `for` loops modelled by a `Nat` index, specs by the rule | conditional (after 2's pilot) | 0 | −1.6 to −2.5 k if all 64 counted loops are reproved; on touch otherwise | 10–16, then 0.5–1 per loop | identical |
| 4 | `match h { APP(f, a) => … }` with a view model (`viewW`) | no-go now | about −50 | −0.6 to −1.0 k over 91 functions | 15–23, then 45–135 to convert | identical |
| 5 | jump table for tag dispatch | no-go | 0 | 0 | 25–40 | changes |
| 6 | structured multiple returns | no-go | 0 | 0 | – | – |
| 7 | memo sugar, generic probe/tail lemmas | no-go now | −280 | −0.4 k | 8–12 | identical |
| 8 | word block primitives (`eq!`, `fill!`, `find!`) | no-go for proofs | −30 | −0.5 to −0.9 k | 30–50 | changes |
| 9 | `call f(…)` without a result, guard sugar, sentinel sugar | no-go | ≈ 0 | 0 | – | changes (`call` without result) |

Go items 1 and 2 together: 9–14 h, about −370 to −400 L lines (2 % of L), no proof change, and the
loop rule for new and reproved loops. Item 3 is decided after a pilot.

## 1. Measurements

### 1.1 L shapes (`lshapes.py`)

1 808 blocks (1 554 `lfn`), 18 740 L lines, generated program files excluded.

| shape | in L today | written as | the twin's counterpart |
|---|---|---|---|
| checked node read ("view") | **102 sites in 91 functions** (60 of them `l_model`-generated), 4 lines each plus 125 field reads (533 lines); 46 sites preceded by a tag check | `t := ⟦h⟧.tier; i := ⟦h⟧.idx; if t != 0 && CTL.u64[1] == 0 { abort }; if R⟨t⟩.count <= i { abort }; f := R⟨t, i⟩.f; …` | `match ← view h with`, `viewApp`, `viewBind`, …: 222 sites |
| view by call | 87 calls of `e_view` | `(g, a, b, c) := call e_view(h)`, then a chain on `g` | the same `view` |
| node count checks in all | 250 (`R⟨t⟩.count <= i { abort }`); 148 of them inside tag chains | | |
| equality chains, ≥ 3 arms, one scrutinee | 100 chains, 508 arms; 24 directly on `h >> 28` (159 arms), most others on `e_view`'s tag `g`, on kind words (`k`) or characters (`c`, front end and scanners) | `if g == 4 { … }; if g == 5 { … }; …` (arms that return) or `else if` | `if tg == ETag.app then … else if …`, `match v with` |
| `while` loops | 194; 149 distinct outside tests and benchmarks | | `for`: 18 lines, `while`: 18, `all`/`any`(`M`): 45, `termination_by (fuel, _)`: 75, `size - i`: 10 |
| counted loops | **64 distinct** (59 bounded by a local, 5 by an expression), 19 with `break`/`return` | `while i < n { …; i += 1 }` | `for`, `List.find?`, `mapM`, `go (i + 1)` |
| other loops | 42 `while 0 == 0` (scanners, dispatch loops), 43 others (downward, probes, tag walks `while e >> 28 == 4`) | | recursion |
| loop bodies without calls | 38 read only, 23 storing (word compare, fill, copy, find, hash) | | |
| several results | 1 166 `return (…)`, 1 343 `(x, y, …) := call` (against 3 582 single-result calls) | | `let (a, b) ← …`: 308 |
| guards `if c { abort \| fail R }` | 1 115 | one line each | `fail`: 310 |
| sentinel propagation (`x := call f(…); if x == k { return … }`) | 310 | | `match ← f with \| none => …` |
| dummy-result calls (`z := call`, `u := call`) | 501 | | `let _ ← f` |
| memoised functions (find, hit return, re-find, put) | 70 | about 4 lines each | `match ← inst1Get k with`: 38 sites, 10 memos |

### 1.2 Proof footprint (`pshapes.py`)

Lines are non-generated proof lines matching the vocabulary; time is the cold build of
`_tmp/localsnf/cold-nf.log` (master e2f3ea22 with localsnf, 5 220 s of `ConAgua` module time)
spread over each module's proof lines, as `lrecords.md` §1.1 does.

| category | lines | files | time proxy |
|---|---:|---:|---:|
| tag case splits (`by_cases g : h >>> 28 = k`, their negations, `tag_iff` bridges) | 478 | 69 | 2 s |
| any `>>> 28` | 1 403 | 164 | 11 s |
| view checks (the scratch and count `by_cases`, `viewOK`, `view_*` lemmas) | 1 503 | 163 | 12 s |
| result positions `r.tail.headD …` | 4 464 | 544 | 60 s |
| first result `r.headD 0` | 11 878 | 791 | 161 s |
| loop vocabulary (loop specs, invariants, inductions) | 4 666 | 588 | 112 s |
| `cases h : … with \| none` on models | 3 784 | 520 | 35 s |

Declaration-level counts:

* **Hand loop specs** (a triple over `exec` on a loop block, by induction on the fuel): 118
  theorems, 1 649 lines, 65 files.
* **Refinements of generated loop models** (`fW.loopᵢ`, by induction on the fuel): 14 theorems,
  1 061 lines (`pisFull_ref` 206, `bphW_loop1_ok` 114, `isW_ok` 85, …). The hand-model loop
  refinements are more (`frW_rel`, `cnsW_okC`, …); the vocabulary does not separate them from other
  inductions.
* **The step does not wrap**, `(i + 1).toNat = i.toNat + 1`: 558 lines, and 17 local copies of the
  lemma.
* **Memo probe/tail lemmas** copied per memoised walk (`iprobe_ok`, `itail_ok`, `probe_ok`, …): 26
  lemmas, 536 lines, 16 files.

**Time.** The older profile (`_tmp/buildtime/prof/`, 57 slow modules, before localsnf) had 456 s of
2 855 s in 51 loop specs, led by the scanners (`lineLoop_spec` 49 s, `indTypeLoop_spec` 27 s, …).
After localsnf those modules are fast (`Scan.RecordsSpec` 6 s, `Front.Fields` 31 → 6 s). The loop
modules still slow are the `Nat` limb operations (`NatShl` 63 s, `NatMul` 33, `NatShr` 31, `NatDiv`
31, `NatAdd` 19, `NatSub` 14: 191 s, 3.7 % of the module time), and their cost is the digit
arithmetic in `grind` (the proof-style lessons), which no construct changes. The tag and view
categories cost under 1 % of the time by the proxy. So **no construct here is a time lever**; the
measurable effects are lines.

### 1.3 Where the per-site proof cost sits: two examples

* **A view arm** (`Arena/Inst1Refine.lean`, `iappArm_ok`): two `by_cases` on the scratch check and
  the count with long `simp only` lines, then `viewOK`, `view_app`, `viewApp_run`, `viewApp_ok`:
  about 7 lines per arm, of a 25-line arm proof. The tag dispatch (`igoOK_succ`, 90 lines) spends
  about 30 lines on `tag_iff` bridges and the negated tags that each later arm lemma takes
  (`instW.arm5 … g4 g5 g6 g0 hs hc he`).
* **A counted loop** (`find_rule`, 4 L lines): the hand model `findRuleW` with a step bound `K`,
  `frW_done`/`frW_step` to re-index it to `rc - i`, `uint64_succ_toNat`, the loop spec by fuel
  induction, the function spec, and `frW_rel` by induction on `K`: 107 lines for 4 lines of L.

## 2. Prototype (`_tmp/lconstructs/proto/`, checked on master 98c46a99)

**Sugar with identical statements** (`Notation2.lean`, `SugarTest.lean`). A copy of `Notation.lean`
with two statements and one function, `desugar : lstmt → MacroM (Array lstmt)`, which turns a sugar
statement into the plain statements it stands for, *at the syntax level*; `transBlock` splices them
into the block, so the block's `seq` nesting is today's.

```
(t, i) := node R⟦h⟧        -- t := ⟦h⟧.tier; i := ⟦h⟧.idx;
                            -- if t != 0 && CTL.u64[1] == 0 { abort }; if R⟨t⟩.count <= i { abort }
for j < n { body }          -- while j < n { body; j += 1 }
```

Four functions rewritten with them are equal to today's by `rfl`: `lsNode` (`LevelEquiv`),
`instApp` (`Inst1`), `findRuleLoop` (`WhnfIota`), `hashLoop` (`Store`). Equal terms compile to the
same code, so `checker.s` is unchanged by construction, and every spec and refinement that unfolds
the definition sees the same term. Two details found on the way: identifiers the macro introduces
(`tier`, `idx`, `count`, `CTL`) must be built with `mkIdent` (hygiene would rename them and the
accessor rules compare names), and a separator array is built with `TSepArray.ofElems`.

**The counted-loop rule** (`ForRule.lean`, 52 lines with documentation; the proof of the rule is 8
lines: induction on the fuel, `step_while`, one `vcgen`, `simp_all`):

```lean
def forS (j n : Var) (body : Stmt) : Stmt :=
  .while (.cmp .ult (.var j) (.var n)) (.seq body (.set j (.bin .add (.var j) (.const 1))))

def ForPost (I : St → Prop) (Q : Sig → St → Prop) (j : Var) : Sig → St → Prop
  | .normal, s => I (s.setLoc j (s.loc j + 1))   -- the invariant after `j += 1`
  | .brk, s => Q .normal s
  | .ret v, s => Q (.ret v) s

theorem Triple.forUp_at (hw : w = forS j n body) (I : St → Prop) (Q : Sig → St → Prop)
    (hexit : ∀ s, I s → ¬ s.loc j < s.loc n → Q .normal s)
    (hbody : ∀ k s₀, ⦃fun s => s = s₀ ∧ I s ∧ s.loc j < s.loc n⦄ step p (exec p k) body
      ⦃fun r s' => ForPost I Q j r s'; ⊤⦄) (k : Nat) (s₀ : St) (hI : I s₀) :
    ⦃fun s => s = s₀⦄ exec p k w ⦃Q; ⊤⦄
```

plus `forUp_succ_toNat : i < n → (i + 1).toNat = i.toNat + 1`.

**`find_rule` reproved** (`ForFindRule.lean` against the original declarations copied into
`ForFindRuleOld.lean`): the model `frN` indexed by a `Nat` (well-founded on `rc.toNat - i`, loads as
`rdW`), three guarded equations over the word index (`frN_end`, `frN_hit`, `frN_miss`), the loop
spec by `Triple.forUp_at` with `sym … => vcgen … <;> finish [frN_hit, frN_miss, ForPost]` (no
induction), the function spec unchanged in shape, and the refinement `frN_rel` by `fun_induction` on
the model, with the per-index facts in one helper `frN_at`.

| | original | prototype |
|---|---:|---:|
| lines (model, its lemmas, loop spec, function spec, refinement) | 107 | 70 (−35 %) |
| elaboration, CPU s (two runs each, `lake env lean`, profiler totals) | 0.96, 0.93 | 0.65, 0.64 |

What went: the step bound and its re-indexing (`frW_done`, `frW_step`), the no-wrap lemma (once in
L core), the fuel induction of the loop spec, and the `K = rc - i` bookkeeping in the refinement,
which now follows the model's own recursion (the twin's is on the list's `drop i`). The final
`findRule_refines` is unchanged. The time is too small to matter.

## 3. The candidates

### 3.1 `(t, i) := node R⟦h⟧` — go (sugar only)

* **Occurrence.** 102 sites in 91 functions, 4 lines each; the twin's `view`/`viewX`, 222 sites.
* **Syntax and semantics.** As in §2: a statement that expands, at the syntax level, to today's four
  statements. The aborts stay `abort` (code 0); a site that differs (a `fail R`, a tag check
  between, `eView`'s `4294967295 < h` guard) keeps its text. Optional variant
  `(t, i) := node R⟦h⟧ tag k` that adds the `h >> 28 != k` check the 46 tag-checked sites have.
* **Compiler.** None: the statements are today's. `checker.s` identical.
* **Model generator.** `l_model` reads the `lfn` text, so it must expand the sugar the same way: its
  `blockStmts` calls the shared `desugar`. The generated models are then today's, name for name; no
  refinement changes.
* **Saving and cost.** −306 L lines; 0 proof lines; 4–6 h (Notation and `desugar` 1–2 h, the
  `ModelGen` hook 1 h, a rewrite script over the 91 functions with a temporary `rfl` check per
  function, the gates and the OVERVIEW §5.1 example 1–2 h). L reads like the twin's `view`.

### 3.2 `for j < n { … }` and the counted-loop rule — go

* **Occurrence.** 64 distinct counted loops (19 with an early exit); 118 hand loop specs, 1 649
  lines; the no-wrap step on 558 lines.
* **Syntax and semantics.** `for j < n { body }` expands to `while j < n { body; j += 1 }` (§2); the
  macro rejects a body that assigns `j` or `n`. `n` is a local (59 of the 64); the 5 loops bounded
  by an expression (`len(IN.u8)`, a constant, `an && bn`) stay `while`. An initialising form
  `for j := a; j < n { … }` would save one more line where the initialisation is adjacent (in most
  named loop blocks it sits in the enclosing function).
* **Proof support, once.** `L/For.lean`: `forS`, `ForPost`, `Triple.forUp`, `Triple.forUp_at`,
  `forUp_succ_toNat` (the prototype's 52 lines). A hand loop spec of a `for` is then the invariant
  and one `vcgen` of the body, no induction.
* **Compiler.** None. `checker.s` identical (the four `rfl` checks of §2 include two loops).
* **Model generator.** The same `desugar` hook as 3.1: today's loop models, unchanged.
* **Saving and cost.** −60 to −100 L lines; per hand loop reproved −25 to −40 proof lines (the
  prototype's −37); 5–8 h (L core file with tests 2–3 h, sugar 1–2 h with 3.1's, a pilot on three
  hand loops — `find_rule`, `lit_hash`, `limbs_eq` — 2–3 h, measured as in §2).

### 3.3 `l_model` loops indexed by a `Nat` — conditional

* **What.** An option of `l_model` (`natfor`, off by default, so that no existing model or arm
  changes name): a `for` loop gets a model by well-founded recursion on `n.toNat - j` with the index
  as a `Nat`, its guarded equations over the word index (as `frN_end`/`frN_hit`/`frN_miss`), and its
  spec by `Triple.forUp_at` instead of the fuel induction. The fuel stays a parameter of the model
  when the body calls a member of the group.
* **Effect.** Refinements of the loop follow the model's recursion (`fun_induction`), which is the
  shape of the twin's index recursions and list traversals (`drop i`, `take i`, `mapM`); the step
  bound, the re-indexing and the no-wrap facts go. The generated loop specs (85 s of the
  generator's 2 400 s, `mgen.md`) lose their induction.
* **Saving and cost.** 10–16 h for the generator (the `while` path is the template; the loop's live
  locals and exit signal are as today), then 0.5–1 h per loop converted, −25 to −40 lines each.
  All 64 counted loops: −1.6 to −2.5 k lines for 40–80 h, about 30–50 lines per hour, below the
  70 lines/h at which `hashtpl.md` stopped. So: decide after 3.2's pilot, and then use it for new
  loops and for loops a twin bump or a performance change touches, not as a retrofit.

### 3.4 `match` on handle tags with a view model — no-go now

* **Occurrence.** Tag chains: 24 on `h >> 28` (159 arms) plus those on `e_view`'s `g`; the tag
  case splits in proofs, 478 lines; view checks, 1 503 lines.
* **Design.** `match h at (t, i) { APP(f, a) => { … }, LAM(ty, b) => { … }, _ => abort }` expanding
  to today's prologue and per-arm `if g == k { if R⟨t⟩.count <= i { abort }; … }`; the tag of each
  store would join the `TRec` row. As sugar alone it saves few lines (the count check shares a line
  with the arm today, as in `liftGo`). The proof saving needs the generator to model it as
  `match R.viewW m h with | none => none | some (f, a) => …` (one `none` arm instead of two aborts,
  arm lemmas guarded by `g = k` alone, without the negated earlier tags) and a lemma per store
  family `viewW_ok` relating `viewW` to the twin's `view` (repackaging `view_app`, `viewApp_ok`, …).
* **Why not now.** Changing what `l_model` emits renames the arms that refinements name, so it has to
  be opt-in, and the saving comes only when a function's refinement is re-threaded: 15–23 h up
  front plus 0.5–1.5 h for each of 91 functions, for −0.6 to −1.0 k lines: 10–20 lines per hour.
  Revisit if a twin bump rewrites the view-heavy walks anyway.

### 3.5 Jump table — no-go

Kraken has `jmp` through a register or memory, but the compiler's proof has no code addresses as
data (labels are symbolic), so a table of arm addresses is a new compiler case and new Kraken
reasoning (25–40 h). It changes no proof above L. The chains it would replace have at most 10
compares, ordered by frequency; whether that matters is a performance question (`perfgap.md`), not
a proof one.

### 3.6 Structured multiple returns — no-go

The compiler already passes results in registers by arity (`Stmt.nret`, `retRegs`), and L already
has `return (a, b)` and `(x, y) := call`. The proof cost is spec vocabulary (`r.headD 0`, 11.9 k
lines; `r.tail.headD 0`, 4.5 k lines), cheap per line; localsnf resolves `setLocs` of literal lists.
A typed result arity would let posts say `r = [a, b]`, but every spec and the generator's model
shapes would change for no time saving.

### 3.7 Measured, no-go

* **Memo sugar** (70 functions, −280 L lines) with generic probe/tail lemmas (26 copies, 536 lines,
  −0.4 k): 8–12 h, 35–50 lines per hour. Worth doing when the next memoised walk is written, as a
  proof-library lemma generic over the memo's schema and the twin's get/set pair.
* **Word block primitives.** Of the 61 loop bodies without calls, about 15 have a fixed shape: slice
  equality (`eqLoop`, `erSliceEqLoop`), bytes against constant data (`matchLitLoop`,
  `matchWordLoop`, `matchDlitLoop`, `pbCheck`), zero fill (`zeroLoop`, `shlZero`, `rzLoop`), a small
  find (`reservedContainsL`, `resContLoop`, `findRuleLoop`), copies (`copy0Loop`, `sputLoop`,
  `ncpLoop`). A primitive per shape (`eq!`, `fill!`, `find!`) would be a compiler case like `scan!`
  (blkcopy: 15–25 h each) and leave no loop spec at its uses: −0.5 to −0.9 k lines for 30–50 h. Not
  for proofs; possibly for speed. The three copies can use the existing `copy!` today.
* **`call f(…)` without a result** (501 dummy locals): a different statement (`Stmt.call []`), so
  `checker.s` changes; no proof saving.
* **Guard sugar** (`require c else R`, 1 115 sites) and **sentinel sugar** (310): one line today
  either way.

## 4. Plan

| batch | what | h | lines | `checker.s` |
|---|---|---:|---|---|
| A | `L/For.lean` (rule, `forS`, `ForPost`, `forUp_succ_toNat`, tests); `node` and `for` in `Notation.lean` through a shared `desugar`; `ModelGen`'s `blockStmts` calls it; tests: `rfl` against today's statements | 4–6 | +120 L core and tests | identical |
| B | rewrite the 91 `node` sites and the 59 counted loops by script, each function checked by a temporary `rfl` (not committed); OVERVIEW §5.1/§5.2 grammar and example | 3–5 | −370 to −400 L | identical (`asm_file.py --check`) |
| C | pilot: three hand loops (`find_rule`, `lit_hash`, `limbs_eq`) reproved with the rule and a `Nat` model; measure lines and time | 2–3 | about −100 | – |
| D | (conditional on C) `l_model … natfor`; use on new loops and on touch | 10–16 | −25 to −40 per loop | – |

A and B land separately (B touches many L files owned by other lanes; `--wide` is not needed since
no proof or statement changes, but B should go when few lanes edit L text). Order: A, B, C; D after
C's numbers. Expected: −370 to −400 L lines (2 %), −0.1 k proof lines from the pilot, then −25 to
−40 per loop as loops are touched. Rank 3's −5 to −12 k is withdrawn; the realistic figure is
−0.5 to −2.5 k over time, most of it from D.

## 5. Batches A–C done (lane lsugar)

**A, B (landed, #78).** `L/For.lean`: `forS`, `ForPost`, `Triple.forUp`, `Triple.forUp_at`,
`forUp_succ_toNat`; `Notation.lean`: `(t, i) := node R⟦h⟧` and `for j < n { … }` through one
`desugar` (at the syntax level), which `transBlock` and `l_model` (`declSyntax` → `desugarAll`)
both call. Two details beyond §2: `node` is a non-reserved token (`&"node"`; as a keyword it broke
identifiers named `node`), and `for` appends the step inside the body's right-nested `seq`
(`Stmt.snoc`, `step_snoc`), so `forS` is the term the notation writes for a body of any length.
The rewrite (script `_tmp/lsugar/rewrite.py`) took 102 node reads and 66 counted loops in 49 files
(test files of `while` itself, `ModelGenTest` and `Compiler/Tests`, kept as they were; the five
loops bounded by a literal stay `while`). Each of the 147 rewritten declarations was checked by a
temporary `example : f = f_lsOrig := rfl` in a full build, then the checks were removed. `checker.s`,
`pins.bin` and the generated program files are byte-identical (`asm_file.py --check`,
`checker_prog.py --check`, on master before and after dense-impl's D2). L lines: 19 288 → 18 886
(**−402**; `scripts/loc.py`). One gate surprise: `step`'s equation lemmas, realized in `For.lean`
and in `Front/Preserve.lean`, made `shake` credit `For` in nine modules; `For.lean` imports
`Preserve` so they are realized once.

**C, the pilot.** Three hand loop specs reproved with the rule; old and new declarations copied
into isolated files and elaborated three times each (`lake env lean`, profiler totals without
import; `_tmp/lsugar/pilot/`):

| loop | what changed | lines (old → new) | elaboration, s (old → new) |
|---|---|---:|---:|
| `find_rule` (`WhnfIotaRefine`, `WhnfIotaRecRefine2`) | fuel-bounded model `findRuleW` → `Nat`-indexed `frN`; loop spec by the rule; refinement and `frN_found` by `fun_induction` on the model | 127 → 79 (**−38 %**) | 1.45 → 0.98 (−32 %) |
| `lit_hash`'s `hashLoop` (`Store`) | loop spec by the rule (model `hashN` unchanged) | 11 → 10 | 1.24 → 1.27 (both specs) |
| `limbs_eq`'s `eqLoop` (`Store`) | loop spec by the rule (model `eqW` unchanged) | 13 → 12 | (with the above) |

For a hand spec the rule needed one more form, `Triple.forUp_pre`: over the loop's whole body (the
step included, post `LoopPost`), in the shape `⦃s = s₀ ∧ P s⦄ exec p k w ⦃Q⦄`, so that `hw` is
`rfl` against the named block (with `forS j n body`, Lean cannot infer `body` through `snoc`).

What the numbers say: **the rule alone saves almost nothing.** A fuel-induction loop spec is
already 6 lines (`induction` + `vcgen … ih`); the rule replaces the induction by an invariant that
must restate the frame (`s.mem = s₀.mem ∧ s.loc 0 = s₀.loc 0 ∧ …`), so `hashLoop` and `eqLoop`
come out even. The saving in `find_rule` comes from the **model**: a step bound `K` with its
re-indexing lemmas (`frW_done`, `frW_step`), the no-wrap bookkeeping, and refinements by induction
on `K` with `rc - i = K` threaded through, all replaced by a model on a `Nat` index whose own
recursion the refinements follow (`fun_induction`). Where a hand model already recurses on a `Nat`
(`hashN`) or well-founded on the word (`eqW`), there is nothing to remove.

**D (`l_model … natfor`): no-go now.** The generated loop models are fuel-indexed, like
`findRuleW`, so D would give the `find_rule` kind of saving (−40 to −50 lines per loop whose
refinement is reproved) — but only on reproving: the 14 refinements of generated loop models
(1 061 lines) and the hand-model ones are done and stable, and D costs 10–16 h before the first
saving. At about 45 lines per loop that is break-even after 15–25 reproved loops, and no lane plans
to reprove that many. Revisit when a twin bump or a performance change rewrites at least that many
counted loops with generated models; until then, new hand loops should use a `Nat`-indexed model
and `Triple.forUp_pre` directly (as `find_rule` now does), which needs no generator change.
