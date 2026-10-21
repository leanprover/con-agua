# con-agua design journal

Decisions, measurements and findings, newest section last. `PLAN.md` has the goal and the
milestones; `docs/survey.md` has the survey of the reference code.

## The language L (2026-10-21, lane `lang`)

Files: `ConAgua/L/{Syntax,Semantics,Notation,GrindAttr,Logic,Examples}.lean`.

### What L is

* **Values.** One type, `Word = UInt64`, with wrapping `+ - *`, `& | ^`, and shifts whose count
  is taken mod 64 (Lean's `UInt64` shifts and x64's `shl`/`shr` agree on this). No division:
  Kraken has no `div`; divide by a power of two with `>>`.
* **Expressions** (`Expr`): constants, locals, binary operators, `A.u8[i]` (a byte, zero-extended),
  `A.u64[i]`, `len(A.u8)`, `len(A.u64)`. No calls and no side effects, so evaluating one never
  touches the frame layout. Only array reads can fail.
* **Conditions** (`Cond`) are a separate type with unsigned (`<`, `<=`, …) and signed (`<ₛ`, `≤ₛ`)
  comparisons and short-circuit `&& || !`. Short-circuit matters: Rust's
  `while i < b.len() && is_ws(b[i])` must not read `b[len]`.
* **Statements** (`Stmt`): `x := e`, stores `A.u8[i] := e` / `A.u64[i] := e`, `;`, `if`, `while`,
  `break`, `return e`, `x := call f(args)`, `abort`, `skip`.
* **Functions** (`FunDecl`): `nparams`, `nlocals` (parameters first, other locals start at 0), a
  body. Falling off the end returns 0. A program (`Prog`) is a list of named functions.
* **Memory** (`Mem`): a fixed set of byte arrays and a fixed set of word arrays, each named by a
  static index (`ArrId`). Lengths are fixed for a run; a growable vector is a fixed-capacity array
  plus a length word, and growing past the capacity is an explicit `abort` in the program. A
  nonexistent array reads as empty, so every access to it is out of bounds. Byte arrays are
  writable too (the input buffer simply is never written).

Element widths: two families (u8 and u64), chosen by the syntax of the access, not by a
declaration. That keeps the semantics a total function of the AST and gives the compiler the
width statically.

### Semantics: a direct denotation into `StateT St (Except Err)`

`St = { mem : Mem, loc : Var → Word }`. `Err = outOfFuel | oob | noFun f | abort`. A function
returns a `Word`; every failure is an `Err`, so no failure can be mistaken for an answer.

Fuel is Kleene iteration:

```lean
def exec (p : Prog) : Nat → Stmt → M Sig
  | 0, _ => throw .outOfFuel
  | n + 1, s => step p (exec p n) s
```

`step p k` is structural recursion on the statement. It hands the next loop iteration
(`k (.while c s)`) and every callee body (`k fd.body`, via `invoke`/`callFn`) to `k`. Both
definitions are structural, so they have clean equation lemmas, reduce by `decide`/`rfl`, and run
under `#eval`/`#guard`. Fuel bounds the nesting of loop iterations and calls along a path.

Consequences:

* **Partial correctness needs no fuel reasoning.** A spec has exception post `⊤`; any `Err`
  (including `outOfFuel`) satisfies it. A loop spec is proved by `induction n` (fuel), not by a
  termination measure: the `zero` case throws, and the `succ` case is one iteration with the
  induction hypothesis for the rest. This is what the end-to-end argument needs: "the checker
  returned accept" implies "the model accepts"; "it ran out" is just not an answer.
* **One semantics.** There is no generated shallow copy and no `denote = shallow` proof per
  program. The compiler theorem is stated about the same `exec`.

Why not the alternatives:
* *Shallow functions generated per L function* would make verification conditions mention Lean
  variables instead of `s.loc 0`, but they need a generator and a per-program equality proof, and
  the compiler would still have to be proved against the deep syntax. The deep denotation turned
  out to be what `vcgen` handles well: one `vcgen [step, evalE, evalC, setLoc, ld8, ih]` per loop
  body, with verification conditions such as `UInt64.toNat (s.loc 0) < (s.mem.arr8 0).size`.
* *A global fuel counter in the state* breaks the frame conditions (`s' = s₀`) and makes the
  interpreter non-structural.
* *Explicit stack accounting in L* is unnecessary: stack exhaustion is an x64 outcome (below).

### Concrete syntax

`lfn (params) locals (more) { … }` builds a `FunDecl`; `lblk (vars) { … }` builds a `Stmt` with
the same numbering, and `⟪t⟫` splices a named block back in. Identifiers resolve to local indices
at macro-expansion time. `str_close` from `scan_fast.rs`:

```lean
def strCloseLoop : Stmt := lblk (j, c) {
  while j < len(IN.u8) {
    c := IN.u8[j];
    if c == '"' { return j }
    else if c == '\\' {
      if j + 1 < len(IN.u8) {
        if IN.u8[j + 1] < 32 { return 0 };
        j += 2
      } else { return 0 }
    } else if c < 32 { return 0 }
    else { j += 1 }
  }
}
def strClose : FunDecl := lfn (j) locals (c) { ⟪strCloseLoop⟫; return 0 }
```

### Proof recipe

Spec shape (con-ron Bridge/Specs style): `⦃fun s => s = s₀⦄ prog ⦃fun r s' => …; ⊤⦄`, real
preconditions as hypotheses about `s₀`, posts as equations about named model functions.

1. **Name every loop** with `lblk` and splice it. Its spec is about `exec p n W`, so the recursive
   call `k W` in the unfolded loop is literally the induction hypothesis.
2. **Loop spec**, post `s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr d = model …`, where `d` is what the
   function returns when the loop exits normally (`Sig.retOr` folds "returned v" and "fell
   through, then `return d`" into one equation). Proof:
   ```lean
     induction n generalizing s₀ with
     | zero => vcgen [exec] <;> grind
     | succ n ih =>
       rw [exec, step_while (w := strCloseLoop) rfl]
       sym only [lang_grind] => vcgen [step, evalE, evalC, setLoc, ld8, ih] <;> finish
   ```
3. A one-line corollary `…_step_spec` restates it for `step p (exec p n) W` (the form the enclosing
   body sees), via `Triple.step_exec`.
4. **Function spec** about `invoke p (exec p n) "f" [args]`, for all `n` and with word arguments
   (so a call site `call f(i + 1)` matches): `rw [invoke_eq _ hp]; simp only [callFn, F]; cases n`,
   then `vcgen [exec, step, evalE, loop_step_spec …]`. `hp : p.lookup "f" = some F` is a section
   variable; for a concrete program it is `rfl`.
5. **Model side**: one guarded equation per arm of the model function, registered with
   `grind_pattern [lang_grind]`. An arm whose next position is computed is stated with the next
   position as a variable: `strCloseN_esc (hk : k = j + 1) (hk' : k' = j + 2) … : strCloseN b j =
   strCloseN b k'`, pattern `strCloseN b j, b[j], b[k], strCloseN b k'`. The `b[j]` part of each
   pattern keeps `grind` from unrolling the model past the bytes the program has read. The
   `strCloseN b k'` part matches the induction hypothesis's term, whose argument is
   `toNat (s.loc 0 + 2)`, so the equation `k' = j + 2` is left to arithmetic.
6. From a triple to a run: `M.of_run` (after con-ron's `AM.of_run`); see `skipBraced_run`.

### Measurements (Examples.lean, nightly-2026-09-21)

| function | Rust lines | L lines | model + arm lemmas | spec + proof lines |
|---|---:|---:|---:|---:|
| `str_close` (`scan_fast.rs:792`) | 25 | 24 | 12 + 33 (7 arms, 1 bounds lemma) | loop 11, corollary 7, function 12 |
| `skip_braced` (`scan_fast.rs:1283`) | 28 | 26 | 17 + 35 (8 arms) | loop 13, corollary 8, function 13 |
| `find_byte` (toy) | | 11 | 4 + 12 | loop 11, corollary 7, function 13 |

The whole `ConAgua.L` library builds in about 7 s from clean (Examples about 5 s). Every proof is
`vcgen` plus `finish` with no hand-written verification-condition steps.

### Findings

* `vcgen` steps through `step`/`evalE`/`evalC` on concrete syntax by their equation lemmas;
  nothing extra is needed. It does not unfold a projection of a constant (`findByte.body`), so
  the function spec does `simp only [callFn, F]` first. (A known gap: "specs aren't found
  through projections".)
* An array read in `Option` form hit a `grind` timeout once the index was `(j + 1).toNat`:
  `docs/gaps/grind-getElem-map-toNat-timeout.lean`. The reads are now a `dite` in the monad
  (`L.ld8`), which `vcgen` splits, and the verification condition holds the bound and
  `arr[i.toNat]` directly.
* `grind` does not split on `Sig` by itself; `attribute [lang_grind cases] Sig` makes it.
* A loop spec's ghost arguments must be pinned by the precondition (`s = s₀`). With the
  invariant stated as `s.loc 0 = UInt64.ofNat i` for a ghost `i`, `vcgen` unified the
  induction hypothesis's `i` with the outer `i` through the postcondition.
* `vcgen … with finish [lang_grind]` failed on six verification conditions of `findLoop_spec`
  that both `vcgen … <;> grind [lang_grind]` and `sym only [lang_grind] => vcgen … <;> finish`
  prove. I could not reproduce this outside the project in a few tries, so there is no reproducer
  yet. Use the `sym only` form, as con-leche does.
* Per-declaration heartbeats count all `finish` calls of a theorem together. An unregistered
  recursive arm (no `k'` variable) made `grind` chain the model and time out on the whole loop.
  Each verification condition on its own was fast.

### Intended compiler (for the compiler lane)

**State correspondence.** Kraken's `dmem` (a partial byte map) holds exactly:
* the **descriptor table** at a base address `T`: for byte array `a`, `[T + 16a]` = base,
  `[T + 16a + 8]` = length; the word arrays follow at `T + 16·nbytes`, then a saved-`rsp` cell
  and the stack limit;
* each **array** as a region `[base, base + len·width)`, little-endian words;
* the **call stack** region `[lo, hi)`, provided by the caller.

The memory fact proved once in the compiler is "these regions are disjoint and inside `dmem`".
Out-of-region access cannot happen because every access is bounds-checked against the
descriptor first, so Kraken's `nonmem_load` (= `False`) never arises.

**Registers.** `r15` = `T` (pinned), `r14` = fuel counter (pinned), `rsp` = stack pointer,
`rax` = expression result, `rcx`/`rdx` = scratch (shift counts go through `cl`), `rbx` = holds
the left operand while the right one is evaluated (spilled to the stack in nested expressions).

**Frames.** On entry `sub rsp, 8·(nlocals + ntemps)`; local `x` is `[rsp + 8x]`; arguments are
pushed by the caller and copied in; result in `rax`. Before the `sub`, `lea rax, [rsp − frame]`;
`cmp rax, [T + limit]`; `jb exhausted` gives the stack check.

**Fuel.** `r14` starts at the harness's `N` and is decremented (`sub r14, 1; jb exhausted`) at
exactly the points where `step` calls `k`: every loop back-edge before re-testing the
condition, and every call. L's fuel is the nesting depth along the current path, while the x64
counter counts all events so far, so `r14 ≤` L's current fuel level always. Hence when the x64
code has not run out, L has not either, and their results agree.

**Outcomes.** `ld8 a i`: evaluate `i` into `rax`, `cmp rax, [r15 + 16a + 8]`, `jae error`,
`mov rcx, [r15 + 16a]`, `movzx eax, byte [rcx + rax]` (word arrays: `[rcx + 8·rax]`). `abort`
jumps to `error`. `exhausted` and `error` are global handlers that restore `rsp` from the saved
cell, set `rdx` to 1 resp. 2 and `ret` to the harness; a normal return has `rdx = 0`.

**Theorem shape.** For a well-formed `p` (static: indices `< nlocals`, call targets exist, arities
match, no `break` outside a loop; this check is still to be written), with `R m N d` relating
the L memory `m` to `d.dmem` (regions as above) and `r14 = N`:

```
Eventually (step1 Host.exe)
  (fun s => s.rdx = 1                                  -- exhausted (fuel or stack)
          ∨ OutcomeRel (run p N f args m) s)            -- ok (r, m') ↦ rdx = 0 ∧ rax = r ∧ R' m' s
  ⟨d, entry f⟩                                          -- error _ ↦ rdx = 2
```

So `run p N f args m` decides the x64 outcome up to exhaustion, and "x64 returned with
`rdx = 0`, `rax = r`" implies `run … = .ok (r, _)`, which the per-function L specs relate to the
model. Kraken's `Eventually` is inductive, so the theorem also says the x64 code halts.

**Proof plan.** By induction on fuel and then on the statement, one lemma per construct: the
compiled fragment of `s` with labels `brk`, `ret`, `exhausted`, `error` as its exits, stated as a
`Program.wp` triple in sgraf812's Kraken fork (branch `vcgen`, rev `ba12834`,
`_tmp/ref/kraken-vcgen`). That fork has `Program.wp` as a `Std.WP` instance, calls to declared
fragments (`FunDecls`, `callSpec_of_triple`), control-flow-graph invariants (`Program.WP.cfg`,
used in `Examples/WP/CallSwap.lean`) and framing by registers and regions. The `while` lemma is
a CFG invariant at the loop head, the call lemma is `callSpec_of_triple` with the callee's
induction hypothesis, and the expression lemmas are straight-line `kvcgen64` proofs.

### Open problems

* **USize.** con-leche's scanner works over `ByteArray`/`USize`. The models here use `Nat`
  positions over `Array UInt8`. Bridging needs `USize.size = 2^64`, which Lean cannot prove
  (`System.Platform.numBits`); it will be a hypothesis, discharged at the end as a platform fact.
  **Done** (lane `scan`, see below): `ConAgua/Scan/Link.lean`.
* **Several results.** A function returns one word. Rust functions returning enums or tuples
  (`ScanRes`, `Member`) must return them through a word array (or a packed word). A convention
  for result cells is still to be chosen.
* **Monadic arena functions.** For a function modelled in `StateT AState (Except CheckError)`
  the post can stay one equation: `(f x).run (abs s₀.mem) = .ok (decode r, abs s'.mem)`, with an
  abstraction function `abs : Mem → AState`. Not tried yet.
* **Named blocks.** `lblk (vars)` must repeat the enclosing function's variable list; nothing
  checks that they agree.
* **Boilerplate.** Each loop needs the `…_step_spec` corollary, and each model arm is a
  hand-written guarded lemma. A small generator for both might pay off once there are tens of
  functions.

### `sorry`s

None.

## Linking to con-leche, and more scan leaf functions (2026-10-21, lane `scan`)

Files: `ConAgua/Scan/{Link,Leaves}.lean`.

### Link: `strCloseN`/`skipBracedN` agree with con-leche's `strClose`/`skipBraced`

`ConAgua/Scan/Link.lean` proves `ConAgua.Scan.strClose_toNat_eq`/`skipBraced_toNat_eq`:
`(strClose b j).toNat = strCloseN b.data j.toNat` (and the `skipBraced` analogue), under
`h64 : System.Platform.numBits = 64` and `hsize : b.size < 2 ^ 64`. This is the missing link from
`L.Examples.skipBraced_run`'s `skipBracedN` to the real, vendored `ConLeche.Frontend.skipBraced`
(`USize` positions over `ByteArray`), completing Stage A's proof chain end to end.

* The proof is `fun_induction strClose b j`/`fun_induction skipBraced b i depth`, case for case
  the same split as con-leche's own `strClose_eq`/`skipBraced_eq`
  (`vendor/con-leche/ConLeche/Frontend/Scan/Equiv/{Scalars,Keys}.lean`) — unsurprising, since
  `strCloseN`/`skipBracedN` were written to mirror `strClose`/`skipBraced` arm for arm in the
  first place. Each case bridges `b.uget i h` to `b.data[i.toNat]` (`uget_eq`, `rfl`: `ByteArray`
  is a bare `Array UInt8` wrapper and `uget`/`GetElem` unfold to it definitionally) and then
  discharges with the already-proved `strCloseN_*`/`skipBracedN_*` arm lemmas from
  `L.Examples`.
* **Where `h64`/`hsize` are actually needed**: nowhere in the *positive* direction (`usizeInBounds`,
  `usizeStep`, `usize_step_of_lt` — all from con-leche, all unconditional: a position that is
  already inside the array never overflows, on any platform). They are needed in exactly one
  place, `usizeGe`: showing `¬ i < b.usize → b.size ≤ i.toNat`. `ByteArray.size : Nat` has no
  upper bound, so `b.usize.toNat` is `b.size % USize.size` in general — only `h64 + hsize` collapse
  that to `b.size` outright. (`str_close`'s OOB case and `skip_braced`'s OOB and the `exfalso`
  "`noProgress`" case all go through `usizeGe`.)
* Measured (`lake env lean`, cold): 264 lines, ~0.6 s.

### More `scan_fast.rs` leaf functions, `ConAgua/Scan/Leaves.lean`

Order per the task: `is_ws`/`skip_ws`, `skip_digits`, `newline_from`, `key_end`, `has_escape`,
`num_end` (`match_lit`/`scan_bool`/`utf8_decode`/`read_nat_at` not attempted this round — see
"Not done" below). Each is an `L` function close to the Rust, a `Nat`-position model in the
`findFrom`/`strCloseN` style (own model, not reusing con-leche directly — these have no vendored
Lean twin at this granularity beyond what `Link.lean` already covers), and a `vcgen`+`grind` spec
proof.

| function | Rust lines | L lines | vcgen+grind clean? |
|---|---:|---:|---|
| `is_ws`/`skip_ws` (`:96,107`) | 3+7 | 7 | yes |
| `skip_digits` (`:118`) | 7 | 7 | yes |
| `newline_from` (`:4072`) | 10 | 7 | yes |
| `key_end` (`:149`) | 14 | 9 | yes |
| `has_escape` (`:818`) | 10 | 7 | yes |
| `num_end` (`:733`) | 10 | 6 (+ call to `skip_digits`, no loop) | **no — `sorry`**, see below |

Whole-file build (`ConAgua.Scan.Leaves`, `lake env lean`, cold): ~2.5 s for all six.
`ConAgua.Scan.Link` + `ConAgua.Scan.Leaves` together add about 750 lines to the `ConAgua` lib;
the whole project (`lake build`, from a warm `.lake`) still finishes in well under a minute.

* **A control-flow deviation from the Rust, found on `is_ws`/`skip_ws`/`skip_digits`.** Rust's
  `while i < b.len() && is_ws(b[i])` — the very example DESIGN.md's "Expressions" section cites
  as the reason `Cond` has short-circuit `&&`/`||` — does not go through `vcgen`+`grind` as
  written: seven of the loop's verification conditions close, the eighth (the plain
  `i ≥ len` exit, nothing to do with the whitespace test at all) does not, even raising
  `finish`'s `liaSteps` two orders of magnitude. Reproducer:
  `docs/gaps/grind-and-or-while-cond.lean`. Workaround, used for `skip_ws`/`skip_digits`
  (`has_escape`'s `j < e` bound is written the same way): drop the `&&` and use the
  `findLoop`/`strCloseLoop` idiom instead — the array bound alone in the `while`, an explicit
  `return i` when the byte fails the test. Both shapes stop at the same position; only the
  `L` control flow differs, not the model.
* **`num_end` is the first function with a `sorry`.** It is the first leaf function that calls
  another (`skip_digits`) and then compares the CALL'S RESULT against a local the call left
  untouched (`if e == i`). Proving this needs `grind` to read `s'.loc 0` (`i`, unchanged) off the
  callee's own postcondition `s' = s₀` — a record-field projection through a *hypothesis*
  `t = { mem := _, loc := _ }`, which `grind`'s congruence closure never resolves (confirmed:
  `subst`ing the same hypothesis first makes the identical `finish` call succeed instantly, and a
  registered congruence lemma does not help either — `grind_pattern` refuses it, since the
  pattern cannot mention the hypothesis's own two implicit arguments). Reproducer:
  `docs/gaps/grind-state-eq-projection.lean`. No workaround found that keeps the house style
  (`sym only [lang_grind] => vcgen [...] <;> finish`); `numEnd_spec`'s `sorry` records this.
  Model (`numEndN`) and the rest of the proof (the `skip_digits` call's own spec, the `b[i]`
  bounds argument) are complete; only the final `finish` is missing.
* **Not done, this round**: `match_lit` (needs a second named array for the literal, or one `L`
  function per literal — `L` has no array-valued parameters — not attempted for time), and with
  it `scan_bool` (calls `match_lit` twice); `utf8_decode` (deeply nested multi-byte decode,
  `Option (List …)`-shaped — a different result-cell question than anything tried so far);
  `read_nat_at` (skipped per the task: `u64` accumulation is in scope for Theorem-2-style
  refinement but not for this spike).

### `sorry`s

* `ConAgua.Scan.Leaves.numEnd_spec`'s `succ` case: see "num_end" above and
  `docs/gaps/grind-state-eq-projection.lean`.
