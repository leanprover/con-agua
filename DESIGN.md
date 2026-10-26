# con-agua design journal

> **Frozen as history (2026-10-22).** New journal entries go to `docs/design/<lane>.md` (one file per lane; see `docs/design/README.md`).

Decisions, measurements and findings, newest section last. `OVERVIEW.md` describes the current
state. Citations of `docs/ROADMAP.md` (by section), `docs/survey.md`, `docs/proof-review.md` and lane
journals are to their versions before the docs prune of 2026-10-25: `git show 4f9bfff9:<path>`.

## The language L (2026-10-21, lane `lang`)

Files: `ConAgua/L/{Syntax,Semantics,Notation,GrindAttr,Logic,Examples}.lean`.

### What L is

* **Values.** One type, `Word = UInt64`, with wrapping `+ - *`, `& | ^`, and shifts whose count
  is taken mod 64 (Lean's `UInt64` shifts and x64's `shl`/`shr` agree on this). No division:
  Kraken has no `div`; divide by a power of two with `>>`.
* **Expressions** (`Expr`): constants, locals, binary operators, `A.u8[i]` (a byte, zero-extended),
  `A.u64[i]`, `len(A.u8)`, `len(A.u64)`; since lane `lext` also `mulhi(a, b)` (the high word of
  the 128-bit product), `u64(a < b)` (a comparison as `1`/`0`) and `D.c8[i]` (a byte of a
  constant byte string `D : List UInt8` that is part of the program). No calls and no side
  effects, so evaluating one never touches the frame layout. Only array reads can fail.
* **Conditions** (`Cond`) are a separate type with unsigned (`<`, `<=`, …) and signed (`<ₛ`, `≤ₛ`)
  comparisons and short-circuit `&& || !`. Short-circuit matters: Rust's
  `while i < b.len() && is_ws(b[i])` must not read `b[len]`.
* **Statements** (`Stmt`): `x := e`, stores `A.u8[i] := e` / `A.u64[i] := e`, `;`, `if`, `while`,
  `break`, `return e`, `x := call f(args)`, `abort`, `skip`; since lane `lext` also
  `return (e₁, e₂, …)` and `(x₁, x₂, …) := call f(args)` (several results).
* **Functions** (`FunDecl`): `nparams`, `nlocals` (parameters first, other locals start at 0), a
  body. A function returns a list of words; falling off the end returns `[]`, and a caller reads
  `0` for every result it asks for and does not get. A program (`Prog`) is a list of named
  functions.
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
2. **Loop spec**, post `s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [d] = [model …]`, where `d` is what the
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
  `docs/gaps/grind-getElem-map-toNat-timeout.lean` (fixed by nightly-2026-10-20; the reproducer
  was deleted in the docs prune of 2026-10-25). The reads are now a `dite` in the monad
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
  for result cells is still to be chosen. **Done** (lane `lext`): functions return lists of
  words, see "L extensions".
* **Monadic arena functions.** For a function modelled in `StateT AState (Except CheckError)`
  the post can stay one equation: `(f x).run (abs s₀.mem) = .ok (decode r, abs s'.mem)`, with an
  abstraction function `abs : Mem → AState`. Not tried yet.
* **Named blocks.** `lblk (vars)` must repeat the enclosing function's variable list; nothing
  checks that they agree. **Done** (lane `lext`): `⟪t⟫` checks it, see "L extensions".
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
| `is_ws`/`skip_ws` (`:96,107`) | 3+7 | 4 | yes |
| `skip_digits` (`:118`) | 7 | 4 | yes |
| `newline_from` (`:4072`) | 10 | 7 | yes |
| `key_end` (`:149`) | 14 | 9 | yes |
| `has_escape` (`:818`) | 10 | 7 | yes |
| `num_end` (`:733`) | 10 | 6 (+ call to `skip_digits`, no loop) | yes (since lane `lext`) |
| `match_lit` (`:132`, lane `lext`) | 11 | 9 | yes |
| `scan_bool` (`:716`, lane `lext`) | 11 | 7 (two calls of `match_lit`, three results) | yes |
| `utf8_decode` (`:917`, lane `lext`) | 66 | 48 (`utf8_char` 33, loop 9, entry 6) | yes; linked to `String.fromUTF8?` |
| `key_at`, `value_at` (`:183,704`, lane `stageb`) | 496 + 8 | 306 (dispatcher + six groups) + 8 | yes |
| `scan_string` + `unescape`, `hex4`/`hex3` (`:1087,991,845`, lane `stageb`) | 223 | 99 (validating only) | yes; linked to `String.fromUTF8?` |
| value scanners (`:1116-1282`, lane `stageb`) | 135 | 103 | yes |
| `next_member`, `slot_nat` (`:1339,1419`, lane `stageb`) | 81 | 28 + 6 | yes |
| record loops, object lists (`:1434-3730`, lane `stageb`) | 2149 | 995 | yes, generated; one generic model |
| `scan_line_loop`, `scan_line_fwd`, driver (`:3767,4044`, lane `stageb`) | 298 | 110 | yes |

Whole-file build (`ConAgua.Scan.Leaves`, `lake env lean`, cold): ~2.5 s for all six.
`ConAgua.Scan.Link` + `ConAgua.Scan.Leaves` together add about 750 lines to the `ConAgua` lib;
the whole project (`lake build`, from a warm `.lake`) still finishes in well under a minute.

* **`&&` in a `while` condition.** On nightly-2026-09-21, Rust's `while i < b.len() &&
  is_ws(b[i])` did not go through `vcgen`+`grind` (the plain `i ≥ len` exit did not close), and
  `skip_ws`/`skip_digits` were written with the bound alone and an early `return`. On
  nightly-2026-10-20 the reproducer passes; lane `lext` rewrote both loops in Rust's shape
  (and deleted the reproducer).
* **`num_end`** compares the result of a call (`skip_digits`) with a local the call left alone
  (`if e == i`). That needs `grind` to read `s'.loc 0` off the callee's frame condition
  `s' = s₀`, where `s₀` is a record literal: `docs/gaps/grind-state-eq-projection.lean`. It was
  a `sorry` until lane `lext` added `St.loc_of_eq_mk` to `lang_grind` (see "L extensions").
* **Not done, this round**: `match_lit` and `scan_bool` (done in lane `lext`, see "L
  extensions"); `utf8_decode` (deeply nested multi-byte decode,
  `Option (List …)`-shaped — a different result-cell question than anything tried so far);
  `read_nat_at` (skipped per the task: `u64` accumulation is in scope for Theorem-2-style
  refinement but not for this spike).

### `sorry`s

None (the `num_end` one is gone).

## The compiler (2026-10-21, lane `compiler`)

Files: `ConAgua/Compiler/*.lean` (compiler `Compile`, check `WF`, Kraken runner `Run`, tests
`Tests`, emitter `EmitScan`, benchmark `Bench`, proof: the rest), `ConAgua/Compiler/harness/run.c`,
the `skipbench` executable in `lakefile.toml`.
Toolchain: nightly-2026-10-20 with sgraf812/kraken `ba12834` (the `vcgen` branch).

### Shape

`compileProg tab p entry : Program` (Kraken's `List Directive`) is the trampoline followed by
`compileFn` of every function. One pass, no register allocation, no optimisation. `asmText` prints
it with Kraken's AT&T printer (`Kraken.X64.toATT`) for `as`/`clang`.

* **Expressions** go to `rax`. `bin op a b` evaluates `a`, stores it in a temporary slot,
  evaluates `b`, moves it to `rcx`, reloads `a` and applies `op` (`imul` for `*`, `shl`/`shr` by
  `cl`). `compileE e t` may write temporaries `t, t+1, …`; `tempsE e` bounds how many. A load
  `A.u8[i]` is `cmp rax, [r15 + len]; jae ca_error; mov rcx, [r15 + base]; movzx rax, byte
  [rcx + rax]`.
* **Conditions** compile to jumps: `compileC c pol l` jumps to `l` if `c` evaluates to `pol` and
  falls through otherwise, so `&&`/`||` short-circuit and `!` only flips `pol`.
* **Statements**: `if` and `while` as usual, with labels `.Lca_<fn>_<path><M>` where `path` is the
  node's position (lowercase letters; since lane `kernelasm` a `Nat` printed in decimal, digits
  `1 … 9` per level, root `0`: "Kernel-checked compiler output") and `M` an uppercase marker. Labels are therefore distinct
  without a counter, and `compileS` is a plain structural function. A loop back-edge is
  `sub r14, 1; jb ca_exhausted; jmp head`. `break` jumps to the loop exit (at function level: to
  the epilogue, which returns 0, as `L` does). `abort` jumps to `ca_error`.
* **Calls**: arguments are evaluated into temporaries `0 … n-1`, `rsi` points at them,
  `sub r14, 1; jb ca_exhausted; call ca_f_<f>`, then the result is stored from `rax`.
* **Functions**: `rax := rsp - [r15 + 8]` (the distance to the stack limit; no wrap-around as long
  as `rsp` stays above the limit); `cmp rax, 8F + 8; jb ca_exhausted` (the frame and the next
  call's return address); `sub rsp, 8F`; copy the parameters from `[rsi + 8i]`; zero the other
  locals; body; `.Z: rax := 0; .R: add rsp, 8F; ret`. `F = nlocals + tempsS body`.
* **Trampoline** `ca_enter(T, fuel)` (System V: `rdi`, `rsi`; result in `rax`, outcome in
  `rdx`): push `rbp`, `r14`, `r15`; `rbp := rsp`; `r15 := T`; `r14 := fuel`; `rsp := [T]`;
  `rsi := T + args`; burn one unit of fuel; call the entry function; `rdx := 0`. The exits
  `ca_exhausted` (`rdx := 1`) and `ca_error` (`rdx := 2`) and the normal return meet at
  `ca_finish`: `rsp := rbp`, pop, `ret`.

**Changes to the plan in "Intended compiler" above.** The saved stack pointer lives in `rbp`
(pinned, never written by L code) instead of a table cell; temporaries are fixed frame slots
instead of `rbx` plus pushes (so `rsp` is constant while a body runs and a local's address is
always `rsp + 8x`); arguments are passed by pointer (`rsi`) into the caller's temporaries; the
stack check compares `rsp - limit` with the frame size, which cannot wrap. The table is
`[T]` stack top, `[T+8]` stack limit, then base/length pairs of the byte arrays and of the word
arrays, then the entry arguments (`Tab`).

**Fuel.** `r14` counts every back-edge and call (including the trampoline's call), while `L`'s
fuel bounds only their nesting. The proof invariant is `r14 < n` while `exec p n` runs, so `L`
never runs out while the machine has fuel left; the machine may run out first.

### Testing

* `Tests.lean`: `#guard` differential tests, compiled code on Kraken's executable semantics
  (`Executable.eval` with Kraken's fake layout, `runKraken`) against `L.run`: `skip_braced` and
  `str_close` on small inputs, word arrays and stores, all operators, signed comparisons, short
  circuit, `break`, `abort`, out-of-bounds, recursion, fuel and stack exhaustion. They found a
  real bug (the temporaries of an `if` condition were not counted in the frame size, so the
  condition overwrote the return address).
* Native: `lake env lean --run ConAgua/Compiler/EmitScan.lean scan.s && cc -O2 -o run
  ConAgua/Compiler/harness/run.c scan.s`. `run FILE ARG…` calls `skip_braced` once;
  `run --lines FILE` calls `skip_braced(start + 1, 0)` for every line of a lean4export file and
  checks that it returns the end of the line. On con-leche's
  `tests/e2e/complete_c04a_restart_70.ndjson.gz` (9.1 MB, 126481 lines) every line agrees.
* Kraken's interpreter recurses once per executed straight-line block, so an infinite loop shows
  up as "deep recursion detected at interpreter" in `withAddresses`, not as a timeout.

### The correctness theorem (`ConAgua/Compiler/Main.lean`)

```lean
theorem compile_correct [Host] (p : Prog) (entry : FnName) (G : Layout) (hG : G.Ok)
    (hwf : Prog.wf G.tab p = true) (k0 : Nat) (hcode : Code (compileProg G.tab p entry) k0)
    (fd : FunDecl) (hentry : p.lookup entry = some fd)
    (args : List Word) (hargs : args.length = fd.nparams) (hnargs : G.nargs = args.length)
    (m : Mem) (N : Nat) (d : MachineData) (ra : Word)
    (hT : d.regs.rdi.toNat = G.T) (hN : d.regs.rsi.toNat = N)
    (hmem : MemRel G m d.dmem) (hroom : G.lo + 8 ≤ G.hi)
    (htop : rdW d.dmem (A G.T) = some (UInt64.ofNat G.hi))
    (hargv : ∀ i (h : i < args.length), rdW d.dmem (A (G.T + G.tab.args.toNat + 8 * i)) = some args[i])
    (hra : rdW d.dmem (A d.regs.rsp.toNat) = some ra)
    (hcs : ∀ x, d.regs.rsp.toNat - 24 ≤ x → x < d.regs.rsp.toNat + 8 →
      (d.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧ ¬ G.InArr x ∧ ¬ G.InTab x)
    (hcs24 : 24 ≤ d.regs.rsp.toNat) (hcs8 : d.regs.rsp.toNat + 8 < 2 ^ 64) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = d.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data))
      d (label enterL)
```

`Ev Q d pc` is Kraken's own judgment `Eventually (step1 Host.exe) Q ⟨d, pc⟩`: every run from `d`
at `pc` reaches a state satisfying `Q` (it is inductive, so the code also terminates).
`[Host]` is any host program and layout that contains the compiled program at index `k0`; the
addresses are never fixed. `G : Layout` is ghost data: the table address `T`, the base and
length of every array, the L stack `[lo, hi)` and the number of entry arguments; `G.Ok` says
the regions lie inside the address space and are pairwise disjoint. `MemRel G m d.dmem` says
the data memory holds L's memory `m` (every array's elements at its base), the table holds the
layout, and the L stack is mapped. The remaining hypotheses describe the call of
`ca_enter(T, N)`: the stack top in `[T]`, the arguments in the table, the return address `ra`,
three free words below it, all outside the other regions.

`OutcomeRel G (run p N entry args m) s` is `rdx = 0 ∧ rax = r ∧ MemRel G m' s.dmem` for
`.ok (r, m')`, `rdx = 2` for an error other than `outOfFuel`, and `False` for `outOfFuel`. So:
the machine returns to `ra` with the callee-saved registers restored, and either says
`exhausted` (`rdx = 1`, out of fuel or stack) or says exactly what `L.run p N` says with the
same fuel `N`. If L runs out of fuel, the machine says `exhausted`. "The machine said `rdx = 0`,
`rax = r`" therefore implies `run p N entry args m = .ok (r, m')`, which the per-function L specs
relate to the model.

### The proof

**Approach.** A forward simulation directly on Kraken's `Eventually (step1 Host.exe)`, in
continuation-passing style: each lemma assumes `Ev Q` at every exit the code can take and
concludes `Ev Q` at its entry. I did not use the fork's `Program.wp`/`vcgen`: `Program.wp` is the
weakest precondition of one fragment with its own labels, and its control-flow rule
(`Program.WP.cfg`) works by case analysis on a concrete list of labels. A generic compiler proof
has symbolic code (`compileS ctx path s` for any `s`) whose sub-fragments jump to labels outside
themselves (`break`, `return`, `ca_error`, `ca_exhausted`), calls of recursive functions whose
specs come from an induction on fuel, and loops whose back-edge re-enters the same code at a
smaller fuel; with `Ev` and continuations these are just hypotheses. From the fork I use `Host`
(an abstract layout with label lemmas such as `Host.label_eq`), `Host.step1_addrOf` (one
instruction at a known index) and the instruction semantics.

**Structure** (`ConAgua/Compiler/*.lean`):
* `Mem.lean`: words and bytes of Kraken's memory at natural-number addresses (`rdW`, `wrW`,
  disjointness as arithmetic).
* `Step.lean`: one lemma per instruction form the compiler emits (about 25), and the flags of
  `cmp`: `(cmpCC op).interp (cmpFlags a b) = op.eval a b` for all six comparisons (signed ones
  via `BitVec.ssubOverflow` and `bv_decide`).
* `Rel.lean`, `WF.lean`: `Layout`, `MemRel`, `Inv` (the current frame holds the locals),
  `Only a b d d'` (only bytes in `[a, b)` changed), the well-formedness check.
* `SimExpr.lean`: `sim_expr`, `sim_cond` (by induction on the expression/condition).
* `RunEq.lean`: one run equation per statement form of `L.step`.
* `SimStmt.lean`, `SimCall.lean`, `SimFun.lean`, `SimStore.lean`: statements (`SimS`, with the
  exits as a structure `Conts`), calls (`sim_call`, from the callee's `FunSim`), function bodies
  (`funSim`: stack check, parameters, zeroed locals, body, epilogue), array stores (the memory
  relation after a byte or word store).
* `Correct.lean`: `execSim_all`: by induction on the fuel `n`, `ExecSim n` (statements under
  `exec p n`) and `FunSim n`; inside, by induction on the statement. The machine fuel invariant
  is `r14 < n` under `exec p n` and `r14 ≤ n` under `step p (exec p n)`.
* `Main.lean`: the trampoline and `compile_correct`.

**Status.** Fully proved, no `sorry`; `#print axioms compile_correct` lists only `propext`,
`Classical.choice`, `Quot.sound` (an early version used `bv_decide` for the signed-comparison
flags, which adds a native-code axiom; those lemmas are now proved with `omega`). About 3400
lines of proof (`Mem` 108, `Step` 497, `Rel` 208, `SimExpr` 529, `RunEq` 217, `SimStmt` 402,
`SimCall` 297, `SimFun` 278, `SimStore` 433, `Correct` 71, `Main` 370) for 281 lines of
compiler. Expressions and conditions are about 500 lines, statements without calls 400, calls
and function bodies 600, array stores 430, the trampoline 370, the instruction lemmas 500. The
compiler modules build from scratch in about 15 s (the slowest, `Main`, 6 s).

**Static well-formedness** (`WF.lean`, `Prog.wf tab p`): locals in range, arrays exist in
`tab`, call targets exist with matching arity, distinct function names, frame and table offsets
below `2^28`. `L` itself gives every program a meaning; this is what the compiler needs. It
lives in the compiler, not in `ConAgua/L`; `scanProg` passes it (`#guard` in `Tests.lean`).

### Measurements (2026-10-21)

`perf stat -e instructions:u`, one run each, on con-leche's
`tests/e2e/complete_c04a_restart_70.ndjson.gz` (9.1 MB, 126481 lines): `skip_braced(start + 1, 0)`
on every line, each checked to return the end of the line.

| | total | harness alone | `skip_braced` | per byte |
|---|---:|---:|---:|---:|
| compiled L (`harness/run.c --lines`) | 513.8 M | 49.3 M | 464.5 M | 51 |
| con-leche's compiled Lean `skipBraced` (`lake exe skipbench`) | 411.6 M | 295.5 M | 116.1 M | 12.7 |

"Harness alone" is the same driver with the call replaced by its expected result (`run.c`
linked against a stub `ca_enter`; `skipbench FILE noop`). The naive compiler is about 4 times
the instructions of Lean's compiled code: every operand goes through `rax`, a temporary slot
and `rcx`, every local lives in memory, and every array access reloads base and length from the
table. con-ron's Rust could not be measured: there is no `cargo`/`rustc` on this machine.

### Findings

* `omega` ignores variables and hypotheses at a type synonym of `Nat` (`L.Var`, `L.ArrId`):
  `docs/gaps/omega-nat-synonym-hyp.lean`. Workaround: `simp only [L.Var, L.ArrId] at *` first
  (the `lomega` macro in `SimExpr.lean`).
* `omega` does not see through `UInt64` arithmetic (`(x - 1).toNat`) or through the projections
  of a structure literal (`{ s with dmem := … }.regs.rsp`); both need a rewrite first
  (`u64_sub_one_toNat`, `simp only [Reg64s.set64_…]`). The proofs state the machine state after
  a few instructions abstractly (`suffices H : ∀ s, s.regs.rsp.toNat = … → … → Ev Q s pc`) to
  keep the terms small.
* `lake env lean FILE` does not apply the package's `leanOptions`, so `autoImplicit` is on there
  and an unbound name silently becomes an implicit argument; check with `lake build` or
  `lake env lean -DautoImplicit=false`.
* Kraken's `Executable.eval` recurses once per straight-line block in the interpreter; an
  infinite loop in compiled code (a temporary overwriting the return address, found by the
  tests) showed up as "deep recursion detected" rather than a hang.

### `sorry`s (compiler lane)

None.

## The limb-pool bignum and the arena refinement (2026-10-21, lane `arena`)

Files: `ConAgua/Arena/{GrindAttr,Pool,Word,NatAdd,NatMul,Refine}.lean`. Milestone 3: `Nat.add`
and `Nat.mul` on a limb pool in L, proved, and the first refinement of L code against con-ron's
arena tier (`AM := StateT AState (Except CheckError)`). No `sorry`.

### `Nat` in the arena tier

* **Representation.** `AState` has no `Nat` field of its own. A `Nat` literal is a Lean `Nat`
  stored *inside* an interned expression node: `ENodeView.lit (.natVal n)`, table
  `ETables.lits : Tbl LitNode EIdx UInt64` with `LitNode { l : ConLeche.Literal }`
  (`Arena/Store.lean:300,352`); the node's cons-table key hashes the `Nat`. Other `Nat` fields
  (bvar index, `proj` index, `Name.num`, memo keys) are small counters, not literals.
* **Arithmetic.** All of it is in `Arena/Core.lean` and is Lean `Nat` arithmetic followed by
  `internE (.lit (.natVal _))`: `natOpResult` (`:1001`: `a - 1`, `a + b`, `a - b`, `a * b`,
  `a ^ b` below `2^24`, `/`, `%`, `gcd`, `land`, `lor`, `xor`, shifts, and `a = b`/`a ≤ b` to a
  `Bool` constant), `reduceNat`'s `Nat.succ` arm (`n + 1`, `:1242`), `natLitToConstructor` and
  `natPred?` (`n = k + 1`, intern `k`), `isNatZero` (`n == 0`), `strLitConsSpine` (`c.toNat`).
  In compiled Lean these are GMP calls (`lean_nat_add` …); the kernel's GMP acceleration of
  `Nat.add`/`Nat.mul`/`Nat.ble` … on literals applies only when a proof reduces such terms by
  `decide`/`rfl`, which none of the specs do. The Rust (`arena/core.rs:3009`) calls `ron::nat`
  instead; con-ron proves `ron::nat` against `Nat` at the Aeneas level
  (`proof/ConRon/Refine/Nat.lean`). The L pool functions replace both.
* **Simplest function with `Nat` arithmetic and the state:** an arm of `natOpResult`, one `Nat`
  operation and one `internE` (`isNatZero` and `rawNatLit?` only read). The `Nat.add` arm is the
  one refined below.

### Data refinement: the limb pool

* **Layout.** Word array `POOL` (0) holds all limbs; word `CTL[0]` (array 1) is the top `T`.
  `[0, T)` is in use and never written again; a function appends its result at `T` and moves
  `T` up. A number is a slice `(o, l)`: little-endian limbs, normalised (no trailing zero limb,
  con-ron's `Nat.WF`), so equal numbers have equal limb sequences.
* **Abstraction.** `pv p o l = Σ_{i<l} p[o+i] · wt i`, `wt i = 2^(64 i)` (`Pool.lean`). `wt` is
  a named function on purpose: `grind`'s ring solver treats `2 ^ (64 * i)` as "a ring term with
  unexpected instance", and `wt i` as an atom. Zero-extension past a short operand is
  `xv p o l k = Σ_{i<k} lv p o l i · wt i` with `lv` = con-ron's `limb`.
* **Invariant.** `PoolOK m`: both arrays exist, `T ≤ len POOL < 2^63` (so `la + lb` is a word).
  `SliceOK m o l`: `o + l ≤ T`. `Norm p o l`: no trailing zero limb.
* **Frames, all named predicates with `grind` patterns** (no `∀`, no `∃` in any post):
  `Agree p q t` (the pools agree below `t`), `Frame a m m'` (only word array `a` changed),
  `Grows m m'` (only the pool and the top changed, the pool below the old top did not, the top
  moved up). Every pool function posts `Grows s₀.mem s'.mem`.
* **Functions.** `nat_add(oa, la, ob, lb)` and `nat_mul(oa, la, ob, lb)` append the normalised
  result at the old top and return its length (the caller reads the offset, the old top,
  before the call). Posts: `pv P' T r = pv P oa la + pv P ob lb` (resp. `*`), `Norm P' T r`,
  `Agree P' P T`, `Frame POOL (m.set64 CTL 0 (T + r)) m'`, `Grows m m'`, `LocEq s' s₀`.
  Inputs need not be normalised. `nat_mul` is the in-place schoolbook product (zero `la` limbs,
  one multiply-accumulate row per limb of `b`), not con-ron's shift-and-add (which uses only
  `Vec::push` for its Aeneas proof). Helpers: `nat_limb` (con-ron's `limb`), `add_carry`
  (the two `overflowing_add`s), `nat_trim` (`norm`/`sig_len`), `mac_hi(x, y, t, c)` (the high
  word of `x * y + t + c`, con-ron's `u128` accumulator; uses `mulhi` and `u64(a < b)`).

### The refinement against `AM` (`Refine.lean`)

The refined function is `natOpResult`'s `Nat.add` arm verbatim,
`natAddArm a b := do let x ← internE (.lit (.natVal (a + b))); pure (some x)`. Its L twin
`nat_add_lit(oa, la, ob, lb)` is `o := CTL[0]; l := call nat_add(…); h := call intern_lit(o, l);
return h`.

```lean
theorem natAddLit_refines … (R : Mem → AState → Prop)
    (hpool : ∀ m a, R m a → PoolOK m) (hgrow : ∀ m m' a, R m a → Grows m m' → R m' a)
    (hI : /- intern_lit's spec, same shape -/) (hR : R s₀.mem a₀) (ha : SliceOK …) (hb : …) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nat_add_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (natAddArm A B) a₀ ∧ R s'.mem (AM.st (natAddArm A B) a₀) ∧
      AM.res (natAddArm A B) a₀ = some (decE (r.headD 0)); ⊤⦄
```

with `A = pv P oa la`, `B = pv P ob lb`. `natAddLit_run` turns it into a statement about `run`:
the L run returning `r` gives `(natAddArm A B).run a₀ = .ok (some (decE r), a')` with
`R m' a'`. What worked, and is the proposed shape for every arena function:

* **Run projections.** `AM.ok x a`, `AM.st x a`, `AM.res x a` (`match` on `x.run a` inside a
  named function). The post is three conjuncts about them: no `∃ a'`, no `fun`. `AM.ok_bind`,
  `AM.st_bind`, `AM.res_bind`, `AM.*_pure` are `grind` equations, so a `do` block is unfolded by
  `grind`, not by hand (`natAddArm`'s `bind`/`pure` went through without a step in the proof).
* **The arena state is a ghost.** `a₀` is a theorem parameter with `R s₀.mem a₀`; the L
  precondition stays `s = s₀`. A callee spec that needs it (`hI`) is passed to `vcgen` with
  `a₀` applied (`hI a₀ n`): a precondition-only argument would otherwise stay a metavariable.
* **An abstraction *relation*, not a function.** `AState`'s cons tables are `Std.HashMap`s, whose
  layout depends on the insertion history, so no function `Mem → AState` can produce the arena's
  state; equality of arena states is too fine. `R` is a parameter; the theorem uses only that it
  implies `PoolOK` and is stable under `Grows`. Milestone 4 defines `R` (lit nodes ↔ pool
  slices, node tables ↔ L tables) and proves `hI` for an L `intern_lit` over an open-addressing
  table. Until then `hI` is a hypothesis, not a `sorry`.
* Proof: `sym only [lang_grind, arena_grind] => vcgen [… natAdd_spec …, hI a₀ n] <;> finish
  [natAddArm, PoolOK, SliceOK]`, about 1.2 s, no hand-written step.

Not done: `natOpResult` itself reads fifteen pins first (`natPredName` …, each a state read that
may fail) and dispatches on `c`; refining it needs `R` to relate the pin table. The other arms
are the same shape (`nat_mul` is ready for the `*` arm).

### Measurements (nightly-2026-10-20)

| function | Rust lines (`ron/nat.rs`) | L lines | spec + proof lines | `lean` time |
|---|---:|---:|---:|---:|
| `nat_add` (+ `nat_limb`, `add_carry`, `nat_trim`) | 66 (`add`, `add_from`, `limb`, `norm`, `sig_len`, `copy_from`) | 41 | 119 | 7.1 s |
| `nat_mul` (+ `mac_hi`) | 77 (`mul`, `mul_from`, `mul_u64`, `mul_u64_from`, `shift_left`, `shl_onto`, `push_zeros`, `shl_bits_from`) | 41 | 153 | 15.8 s |
| `nat_add_lit` refinement + run corollary + run projections | – | 6 | 59 | 1.4 s |

L/Rust is 0.62 for add and 0.53 for mul (the Rust copies to trim and shift-adds, both for
Aeneas). Shared lemmas: `Pool.lean` 173 lines of theorems (frames, `pv`/`xv`/`lv` arms, carries),
`Word.lean` 20. Whole `ConAgua/Arena`: 1164 lines, about 25 s.

The interim `mul_hi` over 32-bit halves (before `mulhi`) was 11 L lines, a 50-line hand proof
(`omega` after naming the four partial products) and a `simp`-only spec proof: `grind` on its
verification condition explores the bit operations (1.3M lines of diagnostics) and fails.

### How automatic

* **`nat_trim`, `nat_limb`, `add_carry`, `mac_hi`, `nat_add`, the zero loop, the refinement:**
  the house form `sym only [lang_grind, arena_grind] => vcgen […] <;> finish`, with
  `finish (splits := 20)` where an invariant predicate is unfolded into ten conjuncts and
  `finish (gen := 20)` where the state is many `setLoc`s deep (commented).
* **The multiply-accumulate column loop and the row loop:** the house form failed (case splits
  exhausted even at 30, two minutes). What works: `vcgen`, `clear ih`, `simp only [St.setLoc,
  BinOp.eval, …]` on all hypotheses (this evaluates the frame: every local becomes a word
  expression in the loop's initial locals), `and_intros`, then `grind (splits := 40)` per
  conjunct; `maxHeartbeats 1000000`; 13 s. The single hard verification condition is the
  invariant step, a degree-3 polynomial identity modulo `pv_set_mid`, `mac_split`, `wt_succ`,
  `pv_succ`; `grind` proves it in isolation only with 40 splits, because the multi-pattern
  lemmas (`pv_succ`, `wt_succ`, `wt_add`) instantiate on every pair of `pv`/`wt` terms and each
  instance's arithmetic side condition is a case split.

### Findings

* **Loop bodies must be straight-line.** Each `if` in a loop body doubles the paths; with four
  (two limb reads, two carry tests) the add loop's `finish` timed out. Moving the reads and the
  carry into callees (`nat_limb`, `add_carry`, as the Rust has them) made it go through. Trying
  the branch-free carry `u64(x < y)` inline in the add loop (after `lext` landed it) timed out
  again, so `add_carry` stays; in `mac_hi` (no loop) `u64(…)` and `mulhi` went through at once.
* **Pure callees post `s' = s₀`** (an e-graph equality of states, fine for `grind`);
  memory-writing callees post `LocEq s' s₀` (now `L.LocEq`). `s'.loc = s₀.loc` alone fails:
  `grind` merges `s'.loc x` with `s₀.loc x` only if the latter term exists.
* **Frame as an equation is fragile.** `s'.mem = s₀.mem.setArr64 POOL (s'.mem.arr64 POOL)`
  needs `POOL < words.size` at every read-back, and `grind` lost it in the add loop. The named
  `Frame POOL m m'` with `Frame.set64`/`Frame.trans`/`Frame.arr64` patterns works.
* **Digit equations as named-function lemmas.** `adc_split`, `mac_split`, `mul_split`:
  `low + hi · 2^64 = …` with pattern on the named high part (`adcHi x y c`). `grind` derives
  the same equation in its linear-arithmetic module but does not pass it to the ring solver, so
  the step `V + c·wt i = …` failed: `docs/gaps/grind-arith-eq-not-in-ring.lean`.
* **`@[grind =]` versus explicit.** A `@[grind =]` (or `[lang_grind =]`) lemma failed where the
  same lemma passed as `grind [l]` succeeded (two `setLoc` layers):
  `docs/gaps/grind-attr-lemma-vs-explicit.lean`.
* **Invariants as named predicates** (`AddInv`, `MulBase`, `ColInv`, `RowInv`, `ZeroInv`) keep
  the induction hypothesis's patterns to one term; `finish [AddInv]` unfolds the goal instance.
  A ghost value that is only in a precondition (the row's starting value) had to be avoided:
  the column invariant states it as `a · b[0..j)` instead.
* **Module system.** `Refine.lean` imports con-ron's arena, whose files are not `module`s, so it
  is a plain file outside the `ConAgua` root; `lakefile.toml` builds it via `globs`.

### L extension requests (all served by lane `lext`)

1. `mulhi` (x64 `mul`, high word in `rdx`): used in `mac_hi`. The 32-bit-halves workaround is
   gone.
2. Comparisons as words (`u64(a < b)`): used in `mac_hi`; not in the add loop (see Findings).
3. Several results: not needed in the end (results are appended at the known top).
4. `LocEq` for callee frames: in `ConAgua/L/Logic.lean`; the arena lane's copy is gone.

### `sorry`s

None. `natAddLit_refines` assumes `intern_lit`'s spec (`hI`) and the two properties of the state
relation (`hpool`, `hgrow`) as hypotheses, for milestone 4 to discharge.

## L extensions (2026-10-21, lane `lext`)

Restored the section "Linking to con-leche, and more scan leaf functions" above, which the
compiler lane's merge (`43a0825`) dropped by accident.

### Proof support

* **Locals through a state equation.** `grind` does not project `loc` out of an equation
  `t = { mem := m, loc := l }`: `t.loc x` is an over-applied projection, and `grind` neither
  internalises `t.loc` nor accepts a pattern for `(St.mk m l).loc x` (it reduces it to `l x`).
  `Logic.lean` now has `St.loc_of_eq_mk (h : t = St.mk m l) : t.loc x = l x` in `lang_grind`,
  with the multi-pattern `t.loc x, St.mk m l`; the equation `h` is left to congruence closure.
  With it, `num_end`'s proof is the standard one-liner and its `sorry` is gone. A callee spec
  keeps the post `s' = s₀`. (The arena lane's suggestion, a named `LocEq s' s₀` with the pattern
  `LocEq s t, s.loc x`, would work too, but needs every spec to change; the lemma does not.)
  Reproducer, still failing without the lemma: `docs/gaps/grind-state-eq-projection.lean`.
* **`&&`/`||` in `while`**: fixed upstream (see above); `skip_ws`/`skip_digits` now use the
  Rust condition.
* **Callees that write memory** (arena request 4): `LocEq s t` (`s.loc = t.loc`) with the
  pattern `LocEq s t, s.loc x` (which creates `t.loc x`) and `LocEq.restore` (`callFn`
  restores the caller's locals). A callee spec posts `LocEq s' s₀ ∧ …`; with a plain
  `s'.loc = s₀.loc` the caller's read of its own local after the call does not close (checked on
  `bump`/`bumpUser` in `Examples.lean`, which now use `LocEq`).

### New expressions: `mulhi`, comparisons as words, constant data

Requests 1 and 2 of the arena lane, and constant data for `match_lit`.

* **`mulhi(a, b)`** (`BinOp.mulhi`, `a.toNat * b.toNat / 2^64`). Code: the usual binary-operator
  sequence ending in `mul rcx; mov rax, rdx` (`binCode`). Proof: `ev_mul` (Kraken's `mul` leaves
  the flags undefined, which the continuation takes for all flags) and a case split in the
  `bin` case of `sim_expr`.
* **`u64(a < b)`** (`Expr.cmpw c a b`, value `Cmp.evalW c a b = if c.eval a b then 1 else 0`),
  any of the six comparisons. Code: as a condition up to `cmp rax, rcx`, then
  `mov rax, 0; mov rdx, 1; cmovcc rax, rdx` (no branch; `mov` keeps the flags, and `cmovcc`
  needed only a register-register step lemma, `ev_cmov`). The condition code is the one jumps
  use, so `cmpCC_interp` does the rest.
* **`D.c8[i]`** (`Expr.ldc d i`, `oob` past the end). The byte string is part of the
  expression, so a spec needs no hypothesis about memory: `vcgen` sees `d[i.toNat]` for the
  concrete `d`. I considered (a) a second input array filled by the harness (no compiler work,
  but every spec would need `s.mem.arr8 LIT = …` and the end-to-end statement would have to
  trust the harness for the contents) and (b) a `.rodata` label in the code (Kraken's data
  memory is separate from the code, so the code cannot read its own bytes). Instead the table
  holds the program's constant data: `Tab.rom` (the concatenated byte strings, `Prog.rom p`,
  each once) sits after the array descriptors, padded to words, and the entry arguments move
  behind it (`Tab.args`). `ldc d i` compiles to `cmp rax, len d; jae ca_error;
  lea rcx, [r15 + romBase + romIdx d rom]; movzx rax, byte [rcx + rax]`. `MemRel` gained one
  field (the table holds `rom`), `Prog.wf` checks that each `d` occurs at `romIdx d rom` and that
  the table with the constant data stays below `2^28` bytes. `asmText` emits `ca_rom`/`ca_rom_len`
  in `.rodata`, and `harness/run.c` copies them into the table: the loader is trusted for these
  bytes as it is for the code.

Compiler proof: +150 lines in `SimExpr` (the `cmpw` case is the condition's `cmp` case plus three
instructions; `ldc` is `ld8` with `lea`), +35 in `Step`, +35 for the new `MemRel` field in `Rel`
and `SimStore`. `compile_correct` is unchanged in statement (the hypothesis `MemRel` now also
says the table holds the constant data); still no `sorry`, axioms `propext`, `Classical.choice`,
`Quot.sound`. Tests: `ext` in `Tests.lean` (all three, against `L.run` on Kraken's semantics).

### Several results

Arena request 3, and `utf8_decode`'s `(code point, length)`.

* **Semantics.** A function returns `List Word`: `Stmt.ret (es : List Expr)`, `Sig.ret (vs :
  List Word)`, `invoke … : M (List Word)`, `run … : Except Err (List Word × Mem)`.
  `Stmt.call (xs : List Var) f args` sets `xᵢ` to the `i`-th result, `0` past the end
  (`St.setLocs`, by `headD`/`tail`, so `grind` reads it with two `lang_grind` equations). Falling
  off the end returns `[]`. Notation: `return (a, b)`, `(x, y) := call f(…)`; `return e` and
  `x := call f(…)` are the one-element cases.
* **Specs.** A function spec's post is `r = [model]` (or `r = [m₁, m₂]`), a loop spec's
  `r.retOr [d] = [model]`. `lang_grind` now has `List.cons.injEq`: without it, `grind` does not
  get from `¬ [a] = [b]` to `¬ a = b`, and it lost the arithmetic behind `a = b` (four loop
  proofs failed). Every proof in `Examples`/`Leaves` changed only in its statement and in
  `evalArgs`/`setLocs` in the `vcgen` list.
* **Compiler.** Result `i` is returned in register `resReg i` = `rax`, `rdi`, `r8`, `r9`, `r10`,
  `r11` (at most six; none of them is used by L code otherwise, and the trampoline leaves them
  alone). `Tab.nres` is the number in use (`Prog.tab` takes the most any `return` gives or any
  call reads, at least 1), so single-result programs pay nothing extra on the fall-off path.
  `return es` evaluates `es` into temporaries (`compileArgs`, as for call arguments) and loads
  the result registers from them, zeroing those beyond `es.length` (`loadRes`). Falling off the
  end zeroes all `nres` of them. After a call, `storeRes xs` stores `resReg i` into `xᵢ`.
  `Prog.wf` checks `es.length ≤ nres`, `xs.length ≤ nres` and `nres ≤ 6`.
* **Proof.** The relation is `ResRel n vs R : ∀ i < n, rres R i = vs.getD i 0`; it replaces
  `rax = v` in the `return` exit of `Conts`, in `FunSim` and in `OutcomeRel`. New lemmas:
  `sim_loadRes`, `sim_storeRes` (inductions over the register list), `sim_ret` (moved to
  `SimCall`, since it now uses `sim_args`), register facts `rres_set64_resReg`/`rres_set64`/
  `ResRel.congr` (36-case `rfl`s). About +200 lines in `SimCall`, `SimFun`, `Rel`, `Main`.
  `compile_correct`'s statement changes only through `OutcomeRel` (results in the result
  registers); no `sorry`, same axioms. Tests: `wideProg` in `Tests.lean` (three results, fewer
  results than read, none, a register read twice).
* A `return e` now costs two more instructions (store to a temporary, reload into `rax`).

### Translations: `match_lit`, `scan_bool` (`ConAgua/Scan/Lit.lean`, `LitLink.lean`)

* `match_lit(b, i, lit)` takes the literal as a slice `(o, n)` of the constant byte string
  `LITS = "truefalse"` (`LITS.c8[o + k]`); `byte_at` is inlined. `scan_bool` returns
  `ScanRes<bool>` as `(ok, value, position)`, the error `ExpectedBool` at `i` as `(0, 0, i)`.
* Models: `matchLitN` (Rust's loop, `byte_at` as `Array.getD`), `scanBoolN : Option (Bool × Nat)`
  and `encBool` (the three words). The arm lemmas take the positions `i + k`, `o + k` as
  variables with an equation (patterns `b[j]`, `L[m]`), as in `strCloseN`; one more general
  lemma went into `lang_grind`: `UInt8.toUInt64_eq_iff` (the L code compares words, the model
  bytes).
* Link (`LitLink.lean`): `matchLitN` is a prefix test when the literal has no `0` byte
  (`matchLitN_eq_isPrefixOf`, `fun_induction`, 30 lines), which is con-leche's `matchLit_eq`;
  `scanBool_eq_N` rewrites con-leche's `scanBool` through the model, and `scanBool_run` is the
  end-to-end statement: whenever `run litProg fuel "scan_bool" [i]` returns `r`,
  `r = encScan (ConLeche.Frontend.scanBool b i)` and the memory is unchanged (under
  `numBits = 64`, `b.size < 2^64`, `i + 5 < 2^64`). Axioms: the standard three.
* Sizes: `match_lit` model 6 + arms 27 lines, loop spec 15, corollary 9, function spec 15;
  `scan_bool` model 9, spec 14; link 117 lines. Every L proof is `vcgen` + `finish`.
  `Lit.lean` builds in 2.9 s, `LitLink.lean` in 0.6 s. Differential tests on Kraken (all three
  results): `Tests.lean`.

### Translation: `utf8_decode` (`ConAgua/Scan/Utf8.lean`)

* The loop body (one code point) is a function `utf8_char(k, n) -> (code point, length)`, length
  `0` for invalid bytes; the loop `(cp, l) := call utf8_char(k, n)` stores `cp` into the word
  array `OUT` and the function returns `(1, count)` or `(0, 0)` (Rust: `Option<Vec<u32>>`; a
  `Vec` that would outgrow `OUT` is an out-of-bounds error here).
* The models compute with words exactly as the L code does: `utf8CharN` is Rust's branch
  structure on `UInt64` (bit operations included), `utf8LoopN` the loop over `Word` positions
  with the memory as an argument (`Mem.set64 OUT cnt cp`), so the post is
  `r.retOr [1, s'.loc 4] = encDecode (utf8LoopN …).1 ∧ s'.mem = (utf8LoopN …).2`. With the model
  in the same terms, `utf8_char`'s spec is one `vcgen` + `finish` that unfolds `utf8CharN`
  (about 20 paths, 6 s); the loop needs three arm lemmas, `utf8CharN_snd_le` (the length is at
  most 4, so `k + len` does not wrap) and two new `lang_grind` frame equations
  (`Mem.arr8_set64_apply`, `Mem.arr64_set8_apply`). The callee frame of `utf8_decode` is
  `LocEq` (it writes memory).
* A `#guard` runs con-ron's test `utf8_decode_agrees_with_the_toolchain` (17 byte strings)
  against `String.fromUTF8?`; `Tests.lean` runs the compiled code on Kraken.
* The model also stops when `OUT` is full (`cnt < len(OUT)`), where the L store fails; so the
  model's memory is exactly L's.

### `utf8_decode` against Lean's decoder (`ConAgua/Scan/Utf8Link.lean`)

con-leche validates string bodies with `String.fromUTF8?`, i.e. `ByteArray.utf8Decode?`, a loop
over `ByteArray.utf8DecodeChar?`, which classifies the lead byte by bit masks and checks overlong
forms, surrogates and the range after assembling the value (`assemble₂…₄`). Rust's decoder
(and so the L code) rejects `0xC0`, `0xC1` and `0xF5…` by the lead byte instead. The proof:

* lead-byte and continuation classes by `decide +kernel` over the 256 byte values (`pfb`,
  `cont_eq`; no `native_decide`);
* the assembled values on both sides as natural numbers (`v2W`…`v4L`: `&&& (2^k - 1)` is
  `% 2^k`, and `a <<< k ||| b` is `a * 2^k + b` for `b < 2^k`, `Nat.two_pow_add_eq_or_of_lt`);
* six cases on the lead byte for one code point (`decA`…`decF`, `utf8CharN_eq`);
* the loop by `fun_induction` on `utf8Decode?.go` (`loop_go`), with the writes to `OUT` as
  `writeCps`;
* `utf8Decode_run`: whenever `run utf8Prog fuel "utf8_decode" [j, e]` returns `r`, then if
  `String.fromUTF8? (b.extract j (min e len)) = some s` (and `OUT` has room) `r = [1, |s|]` and
  `OUT` starts with the code points of `s`; if it is `none`, `r = [0, 0]`. Axioms: the standard
  three.

677 lines, 9 s; written in an afternoon of the lane, with no `grind` (plain `simp`/`omega`/`rw`).
The word-level model made the L proofs trivial and moved all the bit arithmetic here, where it
is proved once against Lean's own decoder rather than against a Nat-level re-statement.

### Named blocks are checked

`lblk (j, c) { … }` now elaborates to `L.Notation.blk ["j", "c"] body` (`blk` is a reducible
identity, so `step_while (w := …) rfl`, `vcgen` and the compiler see the body as before), and
`⟪t⟫` in an `lfn`/`lblk` elaborates through `lsplice%`, which looks up the definition of `t`
and fails unless the block's variables are a prefix of the enclosing ones (they are numbered
by position). All 20 named blocks in the project (including the arena lane's) pass. The
`…_step_spec` corollaries remain: `vcgen` needs a spec about `step p (exec p n) W` itself, and
I found no way to pass `Triple.step_exec (loop_spec … (n + 1))` that it accepts (the loop spec
has hypotheses before the triple).

### Summary of lane `lext`

* L: `mulhi`, `u64(a < b)`, `D.c8[i]` (constant data), several results (`return (a, b)`,
  `(x, y) := call f(…)`), `LocEq` and `St.loc_of_eq_mk` in the proof support, checked named
  blocks. Every extension is in the compiler and its proof.
* Compiler: 281 → 369 lines. Proof (the eleven proof files): 3410 → 3794 lines (+384:
  `SimExpr` +141, `SimCall` +138, `Rel` +52, `Step` +32, `SimFun` +13, `SimStore` +16, …).
  `compile_correct` is still `sorry`-free with the standard axioms; its statement changed only
  in `OutcomeRel` (the results in the result registers) and in `MemRel` (the table holds the
  constant data).
* Translations: `match_lit`, `scan_bool` (linked to con-leche's `matchLit`/`scanBool`,
  `scanBool_run`), `utf8_decode` (linked to `String.fromUTF8?`, `utf8Decode_run`), and the
  `num_end` `sorry` is gone. No `sorry` anywhere in `ConAgua`.


## Global variables (2026-10-22, lane `lfeat`)

Counters, tops, epochs and flags have lived in the `CTL` word array (`CTL[62]`, `CTL[192]`,
`CTL[k + (t & 1)]`), with frames over `CTL` indices stated and proved by hand. L now has
**statically declared global word variables**, additively: no existing constructor, lemma name or
statement changed, and nothing has to migrate. Files: `L/{Syntax,Semantics,Logic,PureEval,
Notation,WriteSet,Examples}.lean`, `Compiler/{Compile,WF,WFFast,Run,Rel,SimExpr,RunEq,SimStmt,
SimStore,SimCall,Correct,Main,Tests,WFAll}.lean`, `scripts/e2e.c`, `Compiler/harness/run.c`; one
arm each in the other passes over L syntax (`Front/{Preserve,RunModel}`, `Rom/{Subst,PinRead,Stage}`,
`E2E/{Ser,Trace}`, `Checker/Prelude`), one field in `Arena/Frame.lean` (`wFr_wframe`), one
anonymous constructor in `Arena/IndDecStab.lean`.

### Design

* **Syntax.** `structure GVar where id : Nat` (a global is a number, as an array is);
  `Expr.glob g` and `Stmt.gset g e`, appended as the last constructors. Notation: an identifier
  that is not a local names a global, so `HTOP` reads it and `HTOP := e`, `HTOP += e` write it.
  Declare one as `abbrev HTOP : L.GVar := ⟨3⟩` (distinct globals need distinct numbers; a
  `GVar` cannot be confused with an `ArrId`, which a plain `Nat` could).
* **Semantics.** A separate store in the memory: `Mem.glob : GVar → Word` (default `0`), written
  by `Mem.setG`. A global access never fails (no bounds, no `oob`).
* **Proof support** (`lang_grind`): `Mem.setG_glob` (read after write, decided on the numbers
  `h.id = g.id`, which `grind` settles for literal globals; stating it over `GVar` equality left
  `grind` unable to refute `⟨1⟩ = ⟨0⟩`), every array/global non-interference equation in applied
  form (`(m.set64 a i v).glob g = m.glob g`: the unapplied form `(m.set64 a i v).glob = m.glob`
  is a partial application `grind` does not use, as with `St.loc`), `Expr.pval` of a global.
  `vcgen` needs `setG` in its list for a write (as `setLoc`).
* **Write sets by name** (`L/WriteSet.lean`). `closedG p G fs`: every function of the
  call-closed set `fs` writes only the globals in the list `G` (array stores unrestricted); then
  every run keeps the others, `GFrame G m m'` (`run_gframe`, `invoke_gframe`). For a caller's
  `vcgen`, `Triple.gframe hclosed hf spec` adds `GFrame G s₀.mem s.mem` to a callee's spec, and
  `GFrame.glob` (pattern `GFrame G m m', m'.glob g`) with `GVar.mem_cons` gives `grind` every
  untouched global: **the frame is by construction**, a callee's spec says nothing about
  globals it does not write. `closedW`/`closedA` (the array write sets) ignore globals: a
  `WFrame` gained one field, `setG` (closure under any global write), which `MemFrame`-based
  frames prove by `h` (`Arena/Frame.lean`, one line).
* **Compiler.** Global `g` is the word at `T + Tab.globOff g`: a **global area** in the
  descriptor table after the result area, before the entry arguments (`Tab.ng` words;
  `Prog.tab` takes one more than the largest global the program names). A read is
  `mov rax, [r15 + off]`, a write `compileE e; mov [r15 + off], rax`: two existing instruction
  forms, so no new step lemma. For `ng = 0` the code and the table are unchanged (every `Emit*`
  driver prints the same assembly). `Prog.wf`/`wfFast`: every global below `tab.ng`, and the
  table offsets with the area below `maxOff`.
* **The proof.** `MemRel` gained `glob` (the area holds `m.glob`); `Layout.InGlob`, `globAddr`;
  `MemRel.onlyG` (the old `onlyD` body, generalized to a memory with the same arrays and any
  globals the machine holds) gives `onlyD` (now also requiring the change to avoid the area) and
  `MemRel.storeG`; `Pres` allows changes in the area; `sim_expr`'s `glob` case is `len64`'s;
  `sim_gset` is `sim_set` with a table store (`Inv.storeG`, `Pres.storeG`). `compile_correct`'s
  statement is unchanged (`MemRel` now also says the area holds the globals; `InTab` covers it);
  no `sorry`, `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.
* **Harness.** `asmText` emits `ca_ng`; `scripts/e2e.c` sizes the table `+ ca_ng` (mmap zeroes
  the globals: `L.run` starts them at `0` too), `run.c` places the arguments after them.
  `runKraken` stores the memory's globals. `scripts/check-asm.sh` now builds with `scripts/lake`
  (scan 303, store 1313, walk 6794 instructions: OK).

### Measurements

* Compiler proof: **+173 lines** (`Rel` +77, `SimStore` +71, `SimExpr` +10, `SimStmt` +7, `RunEq`
  +6, `SimCall` +1, `Correct` +1; `Main`, `SimFun`, `Step`, `Mem` unchanged); compiler +41
  (`Compile` +33, `WF` +3, `WFFast` +1, `Run` +4). Build time (`lake env lean`, user s, machine
  shared): `Rel` 2.1 → 2.5, `SimStore` 3.0 → 3.6, the other compiler modules within noise;
  `L/WriteSet` 1.2 → 2.0 (the `closedG` induction).
* Tests (`Compiler/Tests.lean`, on Kraken against `L.run`): `globProg`, two globals across calls,
  in a condition and with `+=`, nine results (result area and global area side by side), the
  initial globals from the memory.
* **Demo** (`L/Examples.lean`, `bump`/`bump_user`): the two words a callee writes and the one its
  caller keeps across the call were `CTL.u64[0]`, `[1]`, `[2]`; now `LAST`, `CALLS`, `MARK`.
  Before (with the arena's `rdW`, `store_grind` and `arena_grind`): 48 non-blank lines, a size
  precondition on each spec, a hand-stated frame `CtlFrame` (the other `CTL` words and the size,
  with `rdW` and `getElem` forms and three patterns, 14 lines; the first attempt without the
  `getElem` form failed), and array lemmas in both `finish` calls. After: 31 non-blank lines
  (with the three declarations and the one-line write set `bump_closed : closedG … := by
  decide`), no precondition, no frame in `bump`'s spec, `finish` with no arguments. Both check
  in about 1 s.

### How to use

* Declare: `abbrev CNT : L.GVar := ⟨k⟩`, a number no other global of the program uses. Read
  `CNT`, write `CNT := e` / `CNT += e` in `lfn`. Pass `setG` to `vcgen`. A model reads
  `m.glob CNT`.
* Frames: prove `closedG prog [CNT, …] ["f", …] = true := by decide` for the function set, and pass
  `Triple.gframe hclosed (by decide) (f_spec …)` to the caller's `vcgen`. A run-level user gets
  `run_gframe`.
* A program with globals runs with `scripts/e2e.c`/`run.c` unchanged in use (`ca_ng` from the
  assembly).

### Migration notes (every lane)

Nothing has to change to keep building. If you write a function over L syntax by pattern
matching without a wildcard, it needs arms for `Expr.glob` and `Stmt.gset` (done for every one
on master); an anonymous `Mem` constructor needs the third field (`m.glob`); a `WFrame` instance
needs `setG _ _ _ _ h := h` if the frame does not look at globals. `Checker/Prelude.lean`'s
renaming copies globals unrenamed: a copied frontend function that uses a global would share it
with the original (none does).

### `sorry`s

None.

## Records (2026-10-22, lane `lfeat`)

Struct-of-arrays addressing by hand (`AREC.u64[i * 4 + t * 2 + 1]`) needs the injectivity of the
address (`Schema.ad_inj`) and bounds in every proof that reads after a write. L now has record
layouts as **surface syntax plus generic lemmas**: no new constructor, no change to the
semantics or the compiler (compiler-proof delta 0), so the choice of the smaller compiler delta
was free. Files: `L/{Syntax,Notation,Records,Examples}.lean`, tests in `Compiler/{Tests,WFAll}.lean`.

### Design

* **Declaration.** `structure Record where arr : ArrId; stride : Nat` and `structure Field where
  off : Nat`: `abbrev NODE : L.Record := ⟨1, 3⟩`, `abbrev NODE.tag : L.Field := ⟨0⟩`, … (offsets
  below the stride, distinct).
* **Syntax.** `NODE[i].tag` reads, `NODE[i].tag := e` writes (the field constant is
  `NODE.tag`, found by name). Both are `ld64`/`st64` of `NODE.arr` at the address expression
  `Record.at R i f = i * stride + off`, built by a named function.
* **Semantics** are those of the word access, so the address wraps around as `UInt64` (as the
  hand-written form does, and as the compiled code computes it).
* **Proof support** (`L/Records.lean`, all in `lang_grind`): `evalE_at` (pass it to `vcgen`
  next to `evalE`: the address is the named word `Record.ad R j f`, not arithmetic), `Mem.fld m R
  j f` (field `f` of record `j`, `0` out of bounds: what a model is stated with), `fld_getElem`
  (`vcgen`'s `arr[addr]` read is `Mem.fld`), **`fld_set64`** (a field after a field store is the
  stored word if it is the same record and field, else the old field, decided on record numbers
  and offsets), `fld_set64_ne`, `fld_setG`, `fld_set8` (other arrays, globals, byte stores),
  `Record.ad_inj` (distinct fields or records have distinct addresses), `Record.ad_lt` (a field's
  bound from a bound on the record number and room for the records). The only side condition is
  `Record.Ok R j` (`j * stride + stride < 2^64`: no wrap-around), which `grind` discharges from a
  bound on `j` (`j < 2^32` for any stride below `2^32`).

### Measurements

* Compiler and its proof: unchanged (0 lines). `L/Records.lean` 147 lines, 0.4 s.
* **Example** (`L/Examples.lean`, `node_mk`): a node `[tag, a, b]` written field by field, a field
  of another node read, three fields read back; the spec states the results and two frame facts
  over `Mem.fld`. Proof: the standard `vcgen [… evalE_at …] <;> finish`, no hint, 1.8 s. The
  same function with raw addresses (`NODES.u64[i * 3 + 1]`, the spec over `rdW … (j * 3 + 1)`,
  with `arena_grind`/`store_grind`) fails in `finish` after 11 s: `grind` cannot refute
  `i * 3 + 1 = j * 3 + 1` in `UInt64` without the injectivity lemma.
* Tests: `node_mk` on Kraken against `L.run`, and an out-of-bounds record.

### How to use

* Declare the layout and the fields as above; write `R[i].f` in `lfn`; pass `evalE_at` (and
  `ld64`/`st64`) to `vcgen`. State models with `m.fld R j f`. For a store library: its schema can
  become a `Record` (record number `i * 2 + t` for two tiers) with the field reads `Mem.fld`;
  `fld_set64` replaces the per-library `ad_inj` reasoning.
* No migration is forced; existing hand-written addressing keeps working.

### `sorry`s

None.

## Program well-formedness: guarded, and per function (2026-10-22, lane `lfeat`)

Two requests of the coordinator: `decide +kernel` on the structural `Prog.wf` is a trap
(`declArms_wf` used ~19 GB that way), and `checkerProg_wf` (`Prog.wf_of_wfFast` over 1566
functions) peaked at 12.2 GB and grows with the program.

* **The guard** (`Compiler/WF.lean`). `FunDecl.wf` and `Prog.wf` are now `kernelOpaque` of their
  former bodies (`FunDecl.wfSpec`, `Prog.wfSpec`): `kernelOpaque x := cond (Lean.opaqueId true) x
  x`. The kernel cannot reduce `Lean.opaqueId true` (an `opaque` constant), so neither the
  kernel nor `decide` gets past the `cond`, and `kernelOpaque_eq : kernelOpaque x = x` (by
  `cases` on the stuck Boolean) keeps every proof about them. `decide`/`decide +kernel` on
  `Prog.wf …` now fails at once ("failed to reduce"); compiled code (`#guard`) is unaffected.
  (`Lean.opaqueId` alone cannot be the wrapper: it has no equation, so nothing could be proved
  about a wrapped body.) Statements of `compile_correct` and of every `…_wf` theorem unchanged.
  Three sites decided `Prog.wf` directly and now go through `Prog.wf_of_wfFast`
  (`Scan/Validator.lean` `valProg_wf`, `Arena/DeclArmsCanon.lean`, `Arena/DeclArmsNat.lean`);
  `Arena/KnotWF.lean` (`FunDecl.wf` of some functions) through the new `Prog.funsWf_of_fast`.
* **Per function** (`Compiler/WFSplit.lean`, `prog_wf name : tab p`): separate kernel checks,
  none of which sees every body: the name tree as a literal and `progTree p = some tree`
  (names only); one `romOk tab d` per distinct byte string the program reads; one check per
  chunk of 32 functions (`FunDecl.wfTN`, the check without the constant data, plus each
  function's byte strings from the `romOk` facts, `FunOk`); the table bound; and the main
  theorem, `Prog.wf_of_parts'`, assembled from the chunks without evaluation. The table must be
  a literal: `tab_lit% e` evaluates `e` (compiled code) and inserts it. `Prog.rom` now puts the
  short strings first (`romSort`), so that finding `LITS` in the table no longer scans the 37 KB
  ROM. `scripts/checker_prog.py` emits `checkerTab := tab_lit% …` (with a `#guard` that it is
  `Prog.tab checkerProg …`) and `prog_wf checkerProg_wf : checkerTab checkerProg`.
* **Measurements** (`Checker/Prog.lean`, `lake env lean`, peak RSS by `VmHWM`): before 12.2 GB,
  45 s; after **6.3 GB**, 54–62 s. The file without any check is 2.9 GB. Of the rest, the
  largest single check is `romOk checkerTab romData` (≈ 13 s, ≈ 3 GB): the kernel evaluates
  `romData` (`encNames pinNames ++ …`, `Arena/Prelude.lean`) and compares 37 KB; it depends on
  the ROM, not on the number of functions. The name tree is ≈ 5 s, 1.2 GB (UTF-8 codes of 1566
  names; each name costs the kernel ≈ 5 ms); every chunk ≤ 0.7 s. Next steps if needed: a
  literal `romData` (lane `romload`) and per-module name trees. For a small program
  `Prog.wf_of_wfFast (by decide +kernel)` stays faster (`indProg_wf`: 5.0 s, +1.2 GB, against
  7.2 s, +0.7 GB split), so the other `…_wf` theorems keep it.
* `harness`/e2e: the ROM's byte order in the table changed (shortest string first); `asmText`
  and the drivers take it from `Prog.tab`. `scripts/e2e.py --only 'restart_7|basic|nat'`: same
  classes as on master (2 `l-error`s at `hoist_ok`, the rest blocked by the `strip_pis` stub).

### `sorry`s

None.

## The `lit` store, `intern_lit`, and the state relation (2026-10-21, lane `store`)

Files: `ConAgua/Arena/Store.lean` (L code, word-level models, `vcgen` specs),
`ConAgua/Arena/LitRefine.lean` (the relation `LitR`, the arena side, `natAddLit_refines_store`).
Milestone 4: `natAddLit_refines`' three hypotheses (`hpool`, `hgrow`, `hI`) are discharged;
`natAddLit_refines_store`/`natAddLit_run_store` have none. No `sorry`; axioms `propext`,
`Classical.choice`, `Quot.sound`.

### Representation

The arena's `lit` constructor is one `Tbl LitNode EIdx UInt64` per tier (`Arena/Store.lean:64`):
records, a derived column, a cons `Std.HashMap`. In L (word arrays, `Store.lean`):

* `REC` (array 2): four words per node, kind (`0` `natVal`, `1` `strVal`), pool offset, length,
  FNV-1a hash of the limbs (con-ron's `nat::hash64`). The two tiers are interleaved, node `i` of
  tier `t` at `REC[8i + 4t ..]`; `CTL[2 + t]` is the tier's node count, `CTL[1]` the scratch flag.
* `SLOT` (array 3): the cons table, open addressing with linear probing and wrap-around
  (con-ron's `HashMap2`), slot `j` of tier `t` at `SLOT[2j + t]`, `0` free, `i + 1` node `i`.
  Home slot: `home_index`'s multiply-xor finaliser, then `mulhi(x, n)` (Lemire's range
  reduction) instead of the power-of-two mask, so `n = len(SLOT)/2` is arbitrary. No deletion,
  so no tombstones and no epochs.
* **Fixed capacity, defined exhaustion.** No resize: `lit_push` aborts past a load of 3/4 or
  when `REC` is full (an L `abort`, never a result). At `2^27` nodes it aborts where the arena
  throws `native` (`Idx.idxCap`). The probe aborts after `n` steps (unreachable under the load
  limit).
* One set of L functions for both tiers (the tier is an argument); the handle is the arena's
  word, `0x80000000 + 0x8000000·t + i`.

Functions (`Store.lean`): `lit_hash(o, l)`, `limbs_eq(a, b, l)`, `lit_match(t, i, o, l, h)`,
`lit_find(t, o, l, h)` (returns `(found, node, slot, steps)`), `lit_push(t, o, l, h, j)`,
`intern_lit(o, l)` (con-ron's `EStore::intern_lit`: persistent probe, scratch probe if open,
append to the current tier). `#guard`s run them (sharing, both tiers, the load limit) and
`nat_add_lit` end to end.

### Specs: word-level models, then pure Lean

Every L spec is about L memory only, against a model that computes with words *exactly as the
L code does*: `eqW`, `matchW`, `probeW` index arrays with wrapping word arithmetic (`rdW a x =
a[x.toNat]?.getD 0`), and `internW m o l : Option (Word × Mem)` is the whole of `intern_lit`
(`none` where the L code aborts). Consequences:

* **No bound hypotheses** in `limbs_eq`, `lit_match`, `lit_find`, `lit_push`: an out-of-bounds
  read is an L error, and on success the model read the same word.
* **One equation per post**: `internLit_spec`'s post is `LocEq s' s₀ ∧ internW s₀.mem o l =
  some (r.headD 0, s'.mem)`.
* A loop that falls through to `abort` posts `r.retOr M = M` (`M` the model at entry), plus
  `r.retOr [0] ≠ []` so that the caller knows the result is not empty.
* All the arithmetic (no wrap-around, positions mod `n`) and all the arena reasoning live in
  pure lemmas in `LitRefine.lean`, proved by hand (`simp`/`omega`/`rw`, no `grind`).

### The relation `LitR`

`LitR m a` (`LitRefine.lean`): `PoolOK m`, sizes below `2^63`, `CTL[1] ≠ 0 ↔ a.store.scratchOn`,
and `TierRel m t (tier t's lits table)` for both tiers:
* the count is `tb.nodes.size` (≤ `idxCap`), node `i` of the L tier "is" `tb.nodes[i]`
  (`RecRel`: a `natVal n` is a **normalised slice below the pool top** with `pv = n` and its
  hash; a `strVal` is kind `1`, contents not represented);
* `tb.cons[k]? = some (handle of i)` for every node `i` with `nodes[i] = k`, and `none` for
  keys not among the nodes. This is "the same key → handle map": the layout of the arena's
  `Std.HashMap` is never mentioned;
* `SlotsOK`: slot values are `≤` the count, and node `i` sits in some slot reached from its home
  slot through occupied slots (the linear-probing invariant, with an `∃ d` per node).

The lemma chain: normalised slices are unique (`pv_len`, `pv_limbs`), so `lit_match` holds
exactly for the node equal to the literal (`matchW_iff`); the probe aborts, hits, or stops at a
free slot after non-matching nodes (`probe_cases`, induction on `n - d`); a hit is the
arena's cons hit at the same handle (`tier_hit`), a miss means absence (`tier_miss`), and the
append at the free slot is the arena's `Tbl.push` (`tier_push`; `tier_other` for the other
tier). `internE_lit_run` unfolds the arena's `internE (.lit l)` (persistent probe, scratch probe,
capacity test, append) into one equation, and `intern_correct` puts them together:
`internW m o l = some (w, m') → AM.ok … ∧ LitR m' (AM.st …) ∧ AM.res … = decE w`.
`LitR.grow` is `hgrow` (the pool agrees below the old top; records, slots and counts unchanged).

### Measurements (nightly-2026-10-20)

| | Rust lines | L lines | spec + proof lines | `lean` time | automation |
|---|---:|---:|---:|---:|---|
| `lit_hash`, `limbs_eq`, `lit_match`, `lit_find`, `lit_push`, `intern_lit` | 189 (`intern_lit` 40, `Tbl` 20, `HashMap2` probe/home/next/find_slot/insert_at 65 + resize 34, `hash64` 10, `literal_beq`/`hash`, `nat::beq` 20) | 55 | models 94 + arm lemmas 43, specs 143 | 4.3 s | every spec `vcgen` + `finish`, no hand step |
| `LitR`, arena side, table lemmas, `intern_correct`, `hgrow`, instantiation | – | – | 910 (+ 39 defs) | 2.1 s | by hand, `simp`/`omega`/`rw` |

L/Rust is 0.29 (0.37 without the resize the L table does not have). The L side went through at
the first attempt for every function: once the models compute with words like the code, the
verification conditions are equalities `grind` closes by the arm lemmas (`probeW_free`,
`probeW_hit`, `probeW_next`: patterns on the model and the slot read). The cost moved into the
pure part: about 90 lines for the probe (`probe_cases`), 170 for the append (`tier_push`,
`tier_other`), 135 for reading the memory after `lit_push` through six `set64`s, 165 for
`intern_correct` (four paths), 120 for unique normal forms.

### Findings

* **Models in words, specs without hypotheses.** The arena lane's specs carried bounds
  (`o + l ≤ size < 2^64`) to relate `Word` indices to `Nat` models. Modelling with the code's own
  word arithmetic needs none, and composes: `lit_find`'s spec is used by `intern_lit`'s
  `vcgen` call with no side condition.
* **A relation, not a function, and only the part that is used.** `LitR` says nothing about
  the rest of `AState` (other tables, memos, pins) or about the `lit` derived column, so every
  arena step that leaves the `lit` tables and the scratch flag alone preserves it for free.
* **Kernel deep recursion** from `simp only [Nat.add_zero]` on `(x * 0x9e37…).toNat + 0`:
  `docs/gaps/kernel-deep-recursion-simp-add-zero.lean`. `rw` works.
* `if_pos`/`if_neg`/`ite_cond_eq_true` are deprecated on this nightly
  (`ite_eq_left_of_eq_true`, …).

### Not done

* The scratch tier's lifecycle (`enableScratch`/`dropScratch` empty the tier: L would reset the
  count and clear the tier's slots, or stamp them as con-ron's `HashMap2` does).
* `strVal` contents (the string pool) and the derived column (`derOfLit` goes through Lean's
  opaque `mixHash`; an L twin needs con-ron's `mix_hash` and a matching Lean model).
* The other `natOpResult` arms (same shape: `nat_mul` is ready) and the pin reads before them.

### L extension requests

None this round.

## The store relation by `grind`, and a second store (2026-10-21, lane `store2`)

Files: `ConAgua/Arena/LitRefine.lean` (reworked), `ConAgua/Arena/StoreRel.lean` (what the two
relations share), `ConAgua/Arena/AppStore.lean`, `ConAgua/Arena/AppRefine.lean` (the second store),
`ConAgua/Arena/GrindAttr.lean` (`store_grind`). No `sorry`; axioms `propext`, `Classical.choice`,
`Quot.sound`.

### Part 1: `LitR` in the house style

`LitR`'s statement (`natAddLit_run_store`) is unchanged; its definition and every proof were
redone so that the steps are `grind [store_grind, …]`.

What changed, and why each change was needed for `grind`:

* **Words, not `Nat`, for node and slot indices.** The old relation read node fields as
  `fld m t i f = REC[8i + 4t + f]` with `Nat` indices, and every use went through a conversion
  lemma (`rdW_rec`, `rdW_slt`, `recW_toNat`, …) to meet the L models, which index with word
  arithmetic. Now the relation reads exactly the terms the models read,
  `rdW (m.arr64 REC) (i * 8 + t * 4 + 3)`, with `i t : Word`. `grind`'s `UInt64` arithmetic decides
  `i * 8 + t * 4 + 2 = c * 8 + t' * 4` from `i, c < 2^27`, `t, t' ≤ 1` by itself, so the
  conversion lemmas are gone.
* **One read-after-write equation.** `rdW ((m.set64 a k v).arr64 b) x = if b = a ∧ k = x ∧ … then
  v else rdW (m.arr64 b) x` (`rdW_set64`) gives one equation per array after `lit_push`
  (`pm_rec`, `pm_slot`, `pm_ctl`, `pm_pool`, sizes): 35 lines, all `grind [pushMem, rdW_set64]`,
  replacing 135 lines of `set!` reasoning.
* **The probe run is a named function.** `walkW n x e` is `lit_find`'s step taken `e` times, so
  the model's recursion and the invariant use the same term and no `mod` arithmetic appears
  (the old proof related `(home + e) % n` to the code's wrap-around step). `SlotsOK` keeps an
  `∃ d` per node: `grind` uses an `∃` under a `∀` in a hypothesis without help, and where the
  goal needs a witness (after the append) the proof names it (`rs[3]` for the new node, the old
  `d` for the others).
* **The probe result is a named predicate**, `ProbeOK m t o l h x rs` (a hit: a matching node in
  an occupied slot; a miss: a free slot of the run after non-matching nodes, `NoMatch`), in
  place of the old three-way `∨` of `∃`s. `probe_ok` is an induction whose three arms are
  `grind`.
* **The cons table as two `∃`-free clauses.** Each node's key maps to its handle `hdW t i`; each
  entry `x` points at a node with its key, at index `hix x`. The old "keys not among the nodes
  are absent" clause had a `∀` in its antecedent, which `grind` cannot use; the new one makes
  `tier_miss` a contradiction `grind` finds (entry → node with the key → it matches → it is on
  the run before the free slot → the probe would have stopped there).
* **Guarded equations for the arena's `match`.** `internE_lit_hitP`, `…_hitS`, `…_pushS`,
  `…_pushP`: one run equation per path, with the handle already the L word
  (`decE (hdW t (ofNat size))`). `intern_correct` splits `internW` along its four paths and
  closes each with `grind`.
* **Instantiate by hand what `grind` would instantiate everywhere.** The relation has five `∀`
  clauses; with all of them in context `grind` instantiates them on every word in sight and
  times out (`tier_hit` took 5.3 s before naming the two instances it needs, 0.2 s after). The
  proofs `clear` the clauses a step does not use and `have` the instances it does.

Not automated: the uniqueness of normalised slices (`pv_len`, `pv_limbs`, `pv_lt`, `pv_ge`, about
75 lines): induction over `pv` with `2^64`-digit arithmetic, where `grind`'s nonlinear
arithmetic does not reach (`wt` products and division by `wt k`). It is the `lit` key's own
fact, not the store's. `eqW_iff` is half `grind`: the step that instantiates the `∀` at the
current position after rewriting `(a + i).toNat` stays by hand.

| | lines | `lean` wall / user |
|---|---:|---:|
| `LitRefine.lean` before | 1183 | 2.1 s / 4.0 s |
| `LitRefine.lean` after | 843 | 5.5 s / 14.4 s |
| `LitRefine.lean` + `StoreRel.lean`, after part 2 | 753 + 151 | 5.4 s / 13.9 s, 0.8 s |

By section (after ← before): reading the store, generic reads and the memory after `lit_push`,
83 ← 223; the probe 77 ← 90 (the induction itself 25 ← 75, the rest are the new definitions
`walkW`, `NoMatch`, `ProbeOK`); match, hit, miss and append 145 ← 258; the arena paths and
`intern_correct` 139 ← 218; grow 54 ← 67; the relation's definitions 68 ← 47. Unchanged: pool
uniqueness 118 ← 123, the `natAddLit` instantiation 73. The proofs are shorter and their steps
are `grind`, at three times the CPU time (`tier_push` 4.2 s, `tier_other` 2.0 s,
`intern_correct` 1.8 s: `grind` on goals with a dozen `rdW` reads through `pushMem`, each an
`if`).

### Part 2: a second store, `app`

`internE (.app f a)` (`Arena/Monad.lean:231`, `internNodeE`) for the record `AppNode { f a : EIdx }`:
the simplest expression node with children. It differs from `lit` in three ways: the key is two
handle words (equality is word equality, no pool), there is no stored hash (a two-word FNV is
cheaper than a load), and the persistent probe is **skipped** when the scratch tier is open and
a child is a scratch handle (`EStore.persFindMaybe`/`eViewHasScratchChild`, the Rust's `sk`).
The L code does the same test (`((f | a) >> 27) & 1`), so no store invariant (`StoreWF`'s
"persistent nodes have persistent children") is needed to justify it.

* `AppStore.lean` (L, `module`): arrays `AREC` (4) and `ASLOT` (5), node `i` of tier `t` at
  `AREC[4i + 2t ..]`, the count at `CTL[4 + t]`; `app_find` (the probe, the match inline: two
  word comparisons under `&&`), `app_push`, `intern_app`; models `amatchW`, `aprobeW`,
  `ainternW`, `askipW`; `#guard`s for sharing, both tiers and the skip. Every spec went through
  at the first attempt with the house form.
* `AppRefine.lean`: `AppR m a` (scratch flag, `ATierRel` per tier, same shape as `TierRel`, with
  `ARecRel`: the two words are the children's handle words), the guarded arena paths (the
  persistent probe after the skip is a named function `pfA`), `aintern_correct`,
  `internApp_refines` (the triple, `intern_app` refines `internE (.app (decE f) (decE a))` for
  `f, a < 2^32` under `AppR`).
* `StoreRel.lean`: what turned out to be naturally shared, moved out of `LitRefine`: reads after a
  write (`rdW_set64`), the probe run (`walkW`, `homeW_lt`), handle words with a tag parameter
  (`hdW g t i`, `hix_hdW`, `mk_eq`, `word_decE`, the tier bit), `AM.of_run_ok`, `Tbl.push`'s
  fields. 151 lines.

Writing `AppRefine` was a rename of `LitRefine`'s store half (`REC`→`AREC`, stride 8→4,
`cnt`→`acnt`, `matchW`→`amatchW`); it needed four fixes, none conceptual: the count clause
needs `6 ≤ len CTL`; the home slot of an old node after the append (two reads through
`apushMem`, each an `if`) had to be stated as a lemma before the `grind` that uses it (timeout
otherwise); `AppR_push` needs `t ≤ 1`; the tier-bit lemma was first proved by `bv_decide`,
which adds native axioms, and is now `testBit` arithmetic.

| file | lines (non-blank) | `lean` wall / user |
|---|---:|---:|
| `AppStore.lean` | 301 (250) | 7.5 s / 8.9 s |
| `AppRefine.lean` | 474 (417) | 6.1 s / 11.6 s |
| `StoreRel.lean` (shared) | 151 (120) | 0.8 s / 1.0 s |

### Assessment: what a store library would save

Non-blank lines of each instance, by what they establish (headers and `#guard`s left out):

| | `lit` L side | `lit` relation | `app` L side | `app` relation |
|---|---:|---:|---:|---:|
| algorithm-specific | 177 | 204 | 10 | 31 |
| arena protocol (unfolding `internE`, four guarded paths, setters) | – | 74 | – | 73 |
| representation (record layout, probe/insert, key → handle) | 222 | 289 | 197 | 295 |
| instantiation (`natAddLit`) | – | 67 | – | – |

* **Algorithm-specific**, `lit`: FNV over the limbs and `limbs_eq` (L, with their loops), the
  uniqueness of normalised slices (`pv_len`, `pv_limbs`, 100 lines by hand), `NatRec`,
  `matchW_iff`, and the pool frame (`LitR.grow`, the relation refers to the pool). `app`: the
  hash expression, the two-word match, the skip (`skA`, `pfA`, `askipW_eq`), `ARecRel`,
  `amatchW_iff`. This is what a new constructor has to say.
* **Representation**: the probe model and its arm lemmas, the find/push specs, `pushMem` and its
  read equations, `NoMatch`/`ProbeOK`/`probe_ok`, `SlotsOK`/`TierRel`, `tier_hit`, `tier_miss`,
  `tier_push`, `tier_other`, the relation after the append, and `intern_correct`'s path
  structure. `app`'s copy differs from `lit`'s only in array ids, record width and count slot,
  the match function, the home slot of a node, and the skip in `intern_correct`. It is 81 % of
  the `app` instance (492 of 606 lines) and 49 % of `lit`'s.
* **Arena protocol**: per constructor, the same `simp` unfolding of `internNodeE` and four
  guarded equations; mechanical, but it names the constructor's `Tbl` field.

**A library parametric in a record schema** (array ids, width, count slot, a named match model
with its `match_iff` obligation, the node's home slot, the key relation) would hold the
representation half once. Estimate: about 600 lines once (one instance's 490 plus the
parameters), then per instance the schema and its obligations, about 60 lines, plus the
algorithm-specific part, plus the arena protocol (about 30 lines if it is made generic over a
`Tbl` lens). Per instance that saves about 470 of the 565 representation and protocol lines,
and most of the 20 s of CPU an instance costs (`app`: 8.9 s + 11.6 s). con-ron's arena has about 19 cons tables (10 expression constructors, 5 level, 3
name, 1 level list); with two done, the library pays for itself at the second further table.

Recommendation: build it before the third table, in two steps, the lower-risk half first.
1. **The relation half** (`TierRel`, `SlotsOK`, `probe_ok`, the tier lemmas, the append): ~290
   lines per instance, written twice now with only renamings. The match enters as a named
   model function and a `match_iff` lemma, which both instances already have in that form.
   Risk: `grind` over a schema whose fields are variables (array ids, strides) rather than
   numerals; the address disequalities (`i * 8 + t * 4 + f ≠ c * 8 + t' * 4 + g`) were decided
   from literal strides. A stride parameter with a hypothesis `f < w` should still be linear,
   but this is the first thing to test.
2. **The L half** (probe model, arm lemmas, find/push specs, ~200 lines per instance) is cheap
   to write and went through at the first attempt both times; L has no function values, so the
   code stays per instance (or is generated from the schema by a Lean function, which `vcgen`
   then has to see through). Leave it per instance until the relation half is done.
Not worth generalizing: the pool facts (only `lit` has them) and the skip (one line of L, one
lemma).

## The capstone: the first end-to-end theorems (2026-10-21, lane `capstone`)

File: `ConAgua/Capstone.lean` (built through the lakefile's glob, like `Arena.Refine`/
`Arena.LitRefine`: it imports `ConAgua.Arena.LitRefine`, a plain, non-`module` file, so it is one
too). Composes `compile_correct` (`Compiler/Main.lean`) with the scanner's and the arena's L-level
specs for the first time, for two functions.

### `skipBraced_x64`

```lean
theorem skipBraced_x64 [Host] (G : Layout) (hG : G.Ok) (hwf : Prog.wf G.tab scanProg = true)
    (hnres : 1 ≤ G.tab.nres) (k0 : Nat) (hcode : Code (compileProg G.tab scanProg "skip_braced") k0)
    (b : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 64)
    (i : USize) (depth : Nat) (hi : i.toNat ≤ b.size)
    (hd : depth + (b.size - i.toNat) < 2 ^ 64) (hnargs : G.nargs = 2)
    (N : Nat) (dm : MachineData) (ra : Word)
    (hT : dm.regs.rdi.toNat = G.T) (hN : dm.regs.rsi.toNat = N)
    (hmem : MemRel G { bytes := #[b.data] } dm.dmem) (hroom : G.lo + 8 ≤ G.hi)
    (htop : rdW dm.dmem (A G.T) = some (UInt64.ofNat G.hi))
    (hargv : ∀ j (h : j < 2), rdW dm.dmem (A (G.T + G.tab.args.toNat + 8 * j)) =
      some ([i.toUInt64, UInt64.ofNat depth] : List Word)[j])
    (hra : rdW dm.dmem (A dm.regs.rsp.toNat) = some ra)
    (hcs : ∀ x, dm.regs.rsp.toNat - 24 ≤ x → x < dm.regs.rsp.toNat + 8 →
      (dm.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧ ¬ G.InArr x ∧ ¬ G.InTab x)
    (hcs24 : 24 ≤ dm.regs.rsp.toNat) (hcs8 : dm.regs.rsp.toNat + 8 < 2 ^ 64) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = dm.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = dm.regs.rbp ∧ st.data.regs.r14 = dm.regs.r14 ∧ st.data.regs.r15 = dm.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨
          (st.data.regs.rdx = 0 ∧
            st.data.regs.rax = (ConLeche.Frontend.skipBraced b i depth).toUInt64 ∧
            MemRel G { bytes := #[b.data] } st.data.dmem)))
      dm (label enterL)
```

From a Kraken host holding the compiled `scanProg` (`[Host]`, `Code … k0`), a machine state `dm`
whose input region holds `b : ByteArray` (`MemRel`, the layout relation — `G` is the ghost
layout, exactly `compile_correct`'s) called with position `i` and depth counter `depth`
(`compile_correct`'s entry-argument cells, `hargv`) and `N` units of fuel: the run from
`ca_enter` returns to the caller with the callee-saved registers restored, and either reports
`exhausted` (`rdx = 1`, fuel or stack) or reports `rdx = 0` with `rax` the x64 word for
con-leche's own `ConLeche.Frontend.skipBraced b i depth` — the real `USize`-over-`ByteArray`
function (`vendor/con-leche/ConLeche/Frontend/Scan/Fast.lean:741`), not the `Nat`-position model
`skipBracedN` that the L-level specs (`L.Examples.skipBraced_spec`) are stated against. No `L`
notion appears in the conclusion except `MemRel`.

### `natAddLit_x64`

```lean
theorem natAddLit_x64 [Host] (G : L.Compiler.Layout) (hG : G.Ok)
    (hwf : Prog.wf G.tab storeProg = true)
    (hnres : 1 ≤ G.tab.nres) (k0 : Nat) (hcode : Code (compileProg G.tab storeProg "nat_add_lit") k0)
    (m : Mem) (a₀ : AState) (hR : LitR m a₀)
    (oa la ob lb : Word) (ha : SliceOK m oa la) (hb : SliceOK m ob lb) (hnargs : G.nargs = 4)
    (N : Nat) (dm : MachineData) (ra : Word)
    (hT : dm.regs.rdi.toNat = G.T) (hN : dm.regs.rsi.toNat = N)
    (hmem : MemRel G m dm.dmem) (hroom : G.lo + 8 ≤ G.hi)
    (htop : rdW dm.dmem (A G.T) = some (UInt64.ofNat G.hi))
    (hargv : ∀ j (h : j < 4), rdW dm.dmem (A (G.T + G.tab.args.toNat + 8 * j)) =
      some ([oa, la, ob, lb] : List Word)[j])
    (hra : rdW dm.dmem (A dm.regs.rsp.toNat) = some ra)
    (hcs : ∀ x, dm.regs.rsp.toNat - 24 ≤ x → x < dm.regs.rsp.toNat + 8 →
      (dm.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧ ¬ G.InArr x ∧ ¬ G.InTab x)
    (hcs24 : 24 ≤ dm.regs.rsp.toNat) (hcs8 : dm.regs.rsp.toNat + 8 < 2 ^ 64) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = dm.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = dm.regs.rbp ∧ st.data.regs.r14 = dm.regs.r14 ∧ st.data.regs.r15 = dm.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨ st.data.regs.rdx = 2 ∨
          (st.data.regs.rdx = 0 ∧ ∃ m' a',
            (natAddArm (pv (m.arr64 POOL) oa.toNat la.toNat) (pv (m.arr64 POOL) ob.toNat lb.toNat)).run a₀
              = .ok (some (decE st.data.regs.rax), a') ∧
            MemRel G m' st.data.dmem ∧ LitR m' a')))
      dm (label enterL)
```

From a Kraken host holding the compiled `storeProg`, a machine state `dm` related (via the
layout `G` and the store relation `LitR`, `Arena/LitRefine.lean`) to an arena state `a₀`, called
with pool slices `(oa, la)`/`(ob, lb)` denoting the two Nat summands (`pv`, the pool's decoding
function, playing the same role here that `MemRel` plays for the byte buffer above — it is how
"the two operands are these Nat values" is stated for an x64/pool state) and `N` units of fuel:
the run returns to the caller, and either reports `exhausted` (`rdx = 1`), reports that the limb
pool or the `lit` store had no room for the result (`rdx = 2`), or reports `rdx = 0` with the
result register the handle that the arena's `Nat.add` arm of `natOpResult` (`natAddArm`,
`Arena/Refine.lean`) returns when run on `a₀`, and the final memory related (`MemRel` + `LitR`
again) to that arm's final arena state `a'`.

### `validate_x64` (added 2026-10-21, lane `capB`)

`ConAgua/Capstone.lean` also composes `compile_correct` with Stage B's validator
(`ConAgua/Scan/ValidatorLink.lean`), in three theorems: a shared step `validate_x64_core`, and two
public ones that read its raw `L` run off differently.

```lean
theorem validate_x64 [Host] (G : Layout) (hG : G.Ok) (hwf : Prog.wf G.tab L.Scan.Validator.valProg = true)
    (hnres : 1 ≤ G.tab.nres) (k0 : Nat) (hcode : Code (compileProg G.tab L.Scan.Validator.valProg "validate") k0)
    (b : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63) (hnargs : G.nargs = 0)
    (N : Nat) (dm : MachineData) (ra : Word) /- … the same `compile_correct`-shaped hypotheses as
    `skipBraced_x64`/`natAddLit_x64` (`hT`, `hN`, `hmem`, `hroom`, `htop`, `hargv`, `hra`, `hcs`,
    `hcs24`, `hcs8`), with `hmem : MemRel G { bytes := #[b.data] } dm.dmem` -/ :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = dm.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = dm.regs.rbp ∧ st.data.regs.r14 = dm.regs.r14 ∧ st.data.regs.r15 = dm.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨ st.data.regs.rdx = 2 ∨
          (st.data.regs.rdx = 0 ∧
            st.data.regs.rax = UInt64.ofNat (ConAgua.Scan.LineLink.scanDriver b 0 0) ∧
            MemRel G { bytes := #[b.data] } st.data.dmem)))
      dm (label enterL)
```

From a Kraken host holding the compiled validator, run from `ca_enter` on a state whose input
region holds a buffer `b` with `N` units of fuel: the run returns to the caller with the
callee-saved registers restored, and either reports `exhausted` (`rdx = 1`), reports an `L` error
other than fuel (`rdx = 2` — unlike `skipBraced_x64`, Stage B has no `_noErr` theorem for
`validate`, so this is a real, open third outcome, not yet ruled out, not merely "the task's
shape assumed away"), or reports `rdx = 0` with `rax` exactly `scanLineFwd`'s own driver
(`ConAgua.Scan.LineLink.scanDriver`, built directly from con-leche's real
`ConLeche.Frontend.scanLineFwd` over `b`'s `ByteArray`/`USize` positions, with no intervening
`Nat`-model layer): `0` if every line of `b` scans, `n > 0` if line `n` is the first one that does
not; the input region is unchanged (the validator stores nothing). A second theorem,
`validate_x64_parseBytes`, states the same three-way split but with the `rdx = 0` case pushed
down one level further, to con-leche's own parser `ConLeche.Frontend.parseBytes`: if it parses
`b`, a normally-returning run finds `rax = 0`; if it instead finds `rax ≠ 0`, the parser fails at
that line or before — composing `validate_x64_core`'s raw `L` run equation with
`ConAgua.Scan.ValidatorLink.validate_accepts`/`validate_rejects`.

**Assumptions**, beyond `skipBraced_x64`'s (the layout relation, `[Host]`, `hwf`, `hnres`, `h64` —
all the same role here): none specific to the validator. Unlike `natAddLit_x64`'s `LitR`, no
arena-side state relation is needed (the validator only reads the byte buffer, `MemRel` alone).
The genuinely open item is the third outcome itself (`rdx = 2`): Stage B's 59 functions have no
proof, yet, that every array read they make is in bounds under the preconditions `scanLineFwd`'s
own correctness needs (the `…_noErr` treatment `skip_braced`/`str_close` got in "Mismatches"
below) — closing it is future work, not assumed away.

### Trusted / assumed

* **The layout relation** (`MemRel`, `Layout.Ok`): the array/table/stack regions are disjoint and
  in bounds, and the machine's data memory holds L's memory at those addresses — exactly
  `compile_correct`'s own trusted surface (Kraken's x64 semantics, the assembler/loader, the
  calling harness; see `PLAN.md`, "Trusted base").
* **`[Host]`**: an arbitrary host program containing the compiled code at `k0` (`Code`), i.e. the
  loader placed it there; not checked here.
* **`hwf`**: `Prog.wf G.tab p = true`, a decidable, concrete check once `G.tab` (the table shape)
  is fixed by a real loader; carried as a hypothesis, as in `compile_correct`.
* **`hnres : 1 ≤ G.tab.nres`**: both functions return one word; `Prog.wf` already forces this once
  `G.tab` is concrete (every `return`/call-result arity check in `Stmt.wf` is `≤ tab.nres`), but
  extracting it from `hwf` needs unfolding the whole compiled body, so it is a separate,
  independently-obvious hypothesis rather than a derivation.
* **`h64 : System.Platform.numBits = 64`** (`skipBraced_x64` only): the platform fact
  `Scan/Link.lean` needs to equate `USize` positions with `Nat` ones (`ByteArray.usize`'s wrap at
  `USize.size`); undischargeable in Lean, a hypothesis as everywhere else it is used.
* **`LitR`** (`natAddLit_x64` only): the arena/pool state relation from lane `store`/`store2`,
  itself not yet proved to hold of any concrete loader-produced state (milestone 4's remaining
  work, `natOpResult`'s dispatch and the other arms).

### Mismatches the composition found

* **`⦃P⦄ x ⦃Q; ⊤⦄` says nothing about *which* error a run raises.** Composing with
  `compile_correct`'s `rdx = 1 ∨ OutcomeRel …` needs, for the clean two-outcome shape the task
  describes, that the only reachable `Err` is `outOfFuel` (so `OutcomeRel` of every other error
  forces `rdx = 2`, which must not arise). Every existing spec in `ConAgua.L`/`ConAgua.Arena`
  states its error postcondition as `⊤`, which is compatible with *any* error, including ones
  that cannot actually happen — the fact is real but has to be proved separately. Fixed, for
  `skip_braced`/`str_close`, with small additions: a generic `Triple.step_exec'`/`M.of_run_err`
  (the `⊤`-free analogues of `Logic.lean`'s `Triple.step_exec`/`M.of_run`) and `…_noErr` restatements
  of `strCloseLoop_spec`/`strClose_spec`/`skipBracedLoop_spec`/`skipBraced_spec` with the error
  postcondition tightened to `(· = .outOfFuel)`, proved with the **exact same** `vcgen`/`finish`
  scripts as the originals (unchanged): the loop invariants that already discharge the bound for
  the success continuation discharge it for the `oob` continuation just as well (that branch's
  hypotheses contradict themselves). No existing theorem was changed.
* **This does not scale to `nat_add_lit`.** `nat_add`'s pool append and `intern_lit`'s node push
  (`lit_push`, `Store.lean`) each have a genuine, intentional `abort` the source code reaches
  when a capacity check fails (`len(POOL.u64) - top <= n`, `cnt ≥ 2^27`, the record array full,
  the `3/4` load limit) — "growing past capacity is an explicit abort in the program" (`PLAN.md`).
  Unlike `skip_braced`'s bound (implied by the loop invariant alone, so `vcgen` can reject the
  `oob` branch as self-contradictory), ruling these out needs a *quantitative* room hypothesis
  (e.g. `len(POOL.u64) - top > n`) for `nat_add`, and, for `intern_lit`'s probe (`lit_find`), a
  load-factor/pigeonhole argument (linear probing with wraparound visits all `n` slots once in
  `n` steps, so a free slot exists within budget whenever occupancy `< n`) that is not yet proved
  anywhere in the codebase and is well beyond a "small lemma". So `natAddLit_x64`, honestly, has
  **three** outcomes, not two: the task's shape ("exhausted, or the outcome matches …") does not
  hold for this function without that extra work. The theorem above states the three-way split
  explicitly (`rdx = 2` for the capacity-abort case) rather than assuming the gap away; closing
  it to two outcomes is future work (room/load-factor hypotheses plus the pigeonhole lemma,
  probably against `LitR`'s slot-occupancy fields directly).
* **`pv`/`POOL` in the conclusion.** The task asks for "no intermediate L notions … except where
  unavoidable (the layout relation)"; `natAddLit_x64`'s conclusion mentions `pv (m.arr64 POOL) …`
  to say what Nat values the pool slices `(oa, la)`/`(ob, lb)` denote. This is the same kind of
  "unavoidable" as `MemRel`: the arena's `natOpResult`/`natAddArm` take bare `Nat` operands, and
  L has no representation of a `Nat` other than a pool slice, so decoding the slice is required to
  state the operands at all (there is no `con-leche`-level value to substitute, unlike
  `skipBraced`'s `b`/`i`, which are already `ByteArray`/`USize`).
* **`validate_x64`'s open `rdx = 2`.** Of the four capstone theorems, only `skipBraced_x64` gets
  the two-outcome treatment: its `…_noErr` lemmas (above) prove the only reachable `Err` is
  `outOfFuel`. `natAddLit_x64`'s third outcome is a *proved* fact (a genuine, intentional `abort`
  on a capacity check). `validate_x64`'s third outcome is neither: nobody has shown Stage B's 59
  functions only ever raise `outOfFuel`, nor has anyone found a genuine `abort`/`oob` the
  compiled validator can actually reach — the theorem is honest about not knowing yet, rather
  than assuming either way.

### `sorry`s

None.

## The store library (2026-10-21, lane `storelib`)

Files: `ConAgua/Arena/StoreLib.lean` (the library), `ConAgua/Arena/LitRefine.lean` and
`ConAgua/Arena/AppRefine.lean` (ported onto it), `ConAgua/Arena/StoreRel.lean` (handles made
kind-generic: `decI`, `hix`, `mk_eq`, `word_decI`). The L code and its `vcgen` specs stay per
table, as decided after lane `store2`. The statements of `natAddLit_run_store`,
`internApp_refines` and `natAddLit_x64` are unchanged (`LitR`, `AppR` are redefined). No `sorry`;
axioms `propext`, `Classical.choice`, `Quot.sound`.

### The spike: parametric strides

Lane `store2` flagged the risk: `grind` decided the record-address disequalities
(`i * 8 + t * 4 + f ≠ c * 8 + t' * 4 + g`) from literal strides. With the stride a variable it
does not: `i * (2 * w) + t * w + f = c * (2 * w) + t' * w + g → i = c ∧ …` fails (nonlinear).
One hand-proved lemma fixes it: `Schema.ad_inj` (addresses are injective given `t ≤ 1`,
`i < 2^27`, `f < w ≤ 256`; 15 lines of `Nat` division). Given it, `grind` closes the generic
read-after-write goals as it closed the literal ones (`fld_pushG`, the frame of the other tier).

### Shape

* **`Schema`**: record array `ra`, slot array `sa`, width `w`, stride `st = 2w`, the `CTL` index
  `ca` of tier 0's count, the tag. `Schema.WF` (the stride, `w ≤ 256`, `2 ≤ ca`, distinct
  arrays, tag < 16) is `by decide` per instance. Named reads `fld`, `slotW`, `nSl`, `cntW`,
  `homeS`; for a concrete schema they are the L models' terms by `rfl` (`fld litSch m t i 3` is
  `rdW (m.arr64 REC) (i * 8 + t * 4 + 3)`), except field 0 (`+ 0`, one `simp` lemma).
* **The append** `pushG S m t vs j c`: the record written from a list of words (`wrRec`), the
  slot, the count. One read equation per array (`fld_pushG`, `pushG_slot`, `pushG_ctl`,
  `pushG_arr`, sizes). An instance's `pushMem` is `pushG` by one `simp` (`pushMem_eq`).
* **The probe**: `probeArm` is one step of every `*_find` model for a match function
  `mt : Word → Bool`; an instance proves `∀ j d, probeW … j d = probeArm … (probeW …) j d` by
  `rw [probeW]; rfl` and gets `ProbeOKG` (hit / miss with `NoMatchG`) from `probe_homeG`.
* **The relation**: `TierR S R hs m t tb` (count, capacity, record room, `R` per node, the key →
  handle map both ways, `SlotsOKG`) and `StoreR` (two tiers, the scratch flag), parametric in the
  record relation `R : Mem → Word → Word → α → Prop` and the node hash `hs`. Generic lemmas:
  `tierR_hit`, `tierR_miss`, `tierR_push`, `tierR_other`, `tierR_mono` (the pool frame of `lit`).
* **The arena protocol**: a `Lens` (the two tables in `AState` and the scratch flag, with six
  `rfl` laws), `protoRun` (the run of `internNodeE`/`internLNode`: persistent probe or skip,
  scratch probe, capacity, append), `internM` (the L model of every `intern_*`), and
  `intern_correctG`: `internM … = some (w, m')` and `op.run a = protoRun …` give
  `AM.ok op a ∧ StoreR … m' (AM.st op a) ∧ AM.res op a = decI w`.

An instance supplies: the schema; `R` and `hs`; `RFrame` (a node's relation and hash depend
on its own words and memory outside the table); per query `MatchOK` (on a node of the table the
match is key equality), `HomeOK` (a matching node has the query's hash) and `NewOK` (the record
the push writes holds the key); the unfolding of the arena operation to `protoRun`; the bridges
`probeW = probeArm …`, `pushOK → PushRoom`, `internW = internM …`.

Everything is stated with named predicates, conclusions are equations or conjunctions of named
predicates; the obligations are `∀` statements an instance proves once and the library
instantiates by hand (`grind` never sees them as hypotheses). What `store2` found still holds:
the five `∀` clauses of `TierR` are cleared before each `grind` that does not need them; one
`grind` in `tierR_push` timed out until `hrun` was cleared in the new-node branch.

### Port: before and after (nightly-2026-10-20, `lake env lean` per file, one run)

| file | lines (non-blank) before | after | `lean` wall / user before | after |
|---|---:|---:|---:|---:|
| `StoreRel.lean` | 151 (120) | 156 (120) | 1.1 s / 1.3 s | 1.1 s / 1.2 s |
| `StoreLib.lean` (new) | – | 698 (618) | – | 5.9 s / 9.9 s |
| `LitRefine.lean` | 753 (668) | 514 (444) | 6.8 s / 17.3 s | 2.0 s / 3.0 s |
| `AppRefine.lean` | 474 (417) | 230 (190) | 7.7 s / 14.4 s | 1.2 s / 1.4 s |
| total | 1378 (1205) | 1598 (1372) | 15.6 s / 33.0 s | 10.2 s / 15.5 s |

The library is 618 non-blank lines (schema and `ad_inj` 57 raw lines, reads 24, the append and
its read equations 110, the probe 64, the relation's definitions 65, hit/miss 41, the append
lemmas 101, the protocol and `intern_correctG` 197), close to `store2`'s estimate of 600. Two
instances do not repay it in lines (+167 non-blank overall), they do in CPU (−53 %): an
instance's relation file now checks in 1–2 s instead of 7–8 s, because the expensive `grind`
calls (`tier_push`, `tier_other`, `intern_correct`: a dozen `rdW` reads through `pushMem`) run
once, in the library. What is left in `LitRefine` is the `lit` key's own content: the uniqueness
of normalised slices (118 lines, by hand, unchanged), the pool frame (`LitR.grow`, now through
`tierR_mono`), `NatRec`, and the `natAddLit` instantiation (73, unchanged).

Changes the port needed: `LitR` is now `PoolOK m ∧ StoreR litSch …` (the old bounds
`len(REC), len(SLOT) < 2^63` were not needed); `ProbeOKG`'s miss case records that the free slot
is below the slot count (the old proofs got `0 < n` from the load limit in `pushOK`, which the
library's `PushRoom` does not have); `hix_hdW` lost two hypotheses it never used; handles are
`decI` (any `Idx` kind, `decE_eq : decE w = decI w` by `rfl`), since the level store's handles
are `LIdx`.

### The third table: level `succ`, written fresh on the library

`ConAgua/Arena/LevelStore.lean` (L, `module`): arrays `SREC` (6), `SSLOT` (7), one word per node
(the child's handle word), counts at `CTL[6 + t]`, tag `LTag.succ`; `succ_find`, `succ_push`,
`intern_succ`, their models and specs, `#guard`s (sharing, `succ (succ 0)`, the scratch tier).
`ConAgua/Arena/LevelRefine.lean`: `SuccR m a` (`StoreR succSch SRecRel shash` over
`a.store.lss.ls`'s two `succ` tables) and `internSucc_refines`: `intern_succ(u)` refines
`internLNode (.succ (decI u))` under `SuccR`, for `u < 2^32`. The level store has no scratch
skip (`LStore.find?` probes the persistent tier unconditionally), so `skB = false`, as for `lit`.

| | lines (non-blank) | `lean` wall / user | by hand |
|---|---:|---:|---|
| L code (3 functions) | 42 | | |
| models (`sprobeW`, `smatchW`, `spushMem`, `sinternW`, …) and probe arms | 53 | | |
| `vcgen` specs | 88 | | none: `vcgen` + `finish` |
| docs, `#guard`s | 48 | | |
| `LevelStore.lean` | 281 (231) | 3.4 s / 4.5 s | |
| lens, setters, `internLNode` unfolded to `protoRun` | 66 raw | | one `simp` case split, copied from `lit` |
| schema, `SRecRel`, `shash`, `SuccR`, frame | 31 raw | | `decide`, `simp` |
| `MatchOK`, `HomeOK`, `NewOK` | 36 raw | | one `grind` each, `NewOK` through `fld_pushG` |
| bridges (`probeArm`, `PushRoom`, `pushG`, `internM`) | 28 raw | | `rfl`, `simp`, `grind` |
| `sintern_correct`, `internSucc_refines` | 36 raw | | one application of `intern_correctG` |
| `LevelRefine.lean` | 197 (161) | 1.0 s / 1.2 s | |

Both files went through at the first attempt (no failed `grind`, no fix). Against the second
table before the library (`app`: relation 417 non-blank lines, 7.7 s / 14.4 s), the third table's
relation is 161 lines and 1.0 s; of those, about 100 are boilerplate a new table copies with
renaming (the lens and its setters, the unfolding of the arena operation, the bridges), about 40
say what the table is (schema, record relation, hash, the three obligations).

### Findings

* **Parametric strides need one lemma** (`docs/gaps/grind-parametric-stride-injectivity.lean`):
  `grind` does not decide the injectivity of `(i * 2 + t) * w + f` for a variable `w`.
  `Schema.ad_inj`, proved by hand and passed to `grind`, is enough for every generic proof.
* **Obligations as `∀` statements, instantiated by the library.** `RFrame`, `MatchOK`,
  `HomeOK`, `NewOK` are named predicates with a `∀` inside. The library's proofs `have` the
  instance they need and never give a whole obligation to `grind`; an instance proves each one
  by `intro` and one `grind`/`simp`.
* **A `Lens` with `rfl` laws** is what makes the arena side generic: the tables of a
  constructor sit at different depths (`a.store.pers.lits`, `a.store.lss.ls.pers.succs`), and
  `intern_correctG` only needs `get (set a t) = t` and the frame of the other table and the flag.
* **The run of the arena operation as one equation** (`… .run a = protoRun …`) replaced the four
  guarded per-path equations of each instance; the library derives the paths.
* **What stays per table:** the L code, models and specs (cheap, `vcgen` at the first attempt
  three times now), the arena unfolding (`simp` with the store's own operations), the key's
  meaning (`MatchOK`: trivial for handle keys, the pool uniqueness for `lit`).

### Recommendation for the remaining tables

The remaining 16 cons tables (8 expression constructors, 4 level, 3 name, 1 level list) sort
into four kinds by their key:
* **handle words only** (`sort`, `const`, `lam`/`forallE` records, `letE`, level `max`, `imax`,
  `param`): as `app` and `succ`, each about 230 lines of L side and 160 of relation, under 5 s of
  CPU, no new proof idea (`max`/`imax` are `app` with `LTag` and the level lens);
* **a handle and a `Nat`** (`bvar`, `fvar`, `proj`, name `num`): a `Nat` stored in a word needs a
  bound (`< 2^64`) in `MatchOK`/`NewOK` and in the refinement theorem's hypotheses, or a limb
  slice as for `lit`; small;
* **no fields** (`anonymous`, level `zero`): at most one node per tier; a schema with one dummy
  word works (`w = 0` is excluded by `Schema.WF`), or the table is a flag;
* **variable-length keys** (name `str`: string contents, as `lit`'s unrepresented `strVal` arm;
  the level list: `List LIdx`): a pool and a uniqueness lemma for the key, as `lit`'s
  `pv_len`/`pv_limbs`.
`lam`/`forallE` do not go through `internNodeE` (`internLamE`, `internForallEE`); their protocol
differs and needs its own unfolding to `protoRun`, or a second protocol in the library; check
before writing them.

The L side is now the larger half of a new table (231 of 392 lines). It went through at the first
attempt three times; generating it from the schema would need `vcgen` to see through a Lean
function producing L syntax, which nothing here has tried. Not worth it before the per-table L
code shows a bug the generated form would avoid. The next step that pays is a combined relation
over all tables of a store (`LitR ∧ AppR ∧ …` with the frame between them: each table's append
is `OutEq` for the others' arrays, which `pushG_arr` already gives).

### `sorry`s

None.

## More store-library tables (2026-10-21, lane `tables`)

Files: `ConAgua/Arena/{Zero,Max,Imax,Param,Sort,Const,Let}Store.lean`,
`ConAgua/Arena/{Zero,Max,Imax,Param,Sort,Const,Let}Refine.lean` (the level store's remaining four
constructors, then three expression handle-only kinds). Order per the task: the level store first
(`zero`, `max`, `imax`, `param`), then expression handle-only kinds (`sort`, `const`, `letE`). One
table per commit, each following the `succ`/`app` templates on `StoreLib.lean` exactly; `sort`
needed one small library generalisation (`isPersistent_decI`, below), every other table none. No
`sorry`.

### The level store: `zero`, `max`, `imax`

* **`zero`** (`ZeroStore.lean`/`ZeroRefine.lean`, arrays `ZREC`/`ZSLOT` = 8/9, counts at
  `CTL[8 + t]`, tag `0`): the fieldless case the recommendation flagged. `ZeroNode` has no
  fields, so there is at most one node per tier and the match function is the constant `true`
  (any node present *is* the `zero` node); the hash is the constant `zeroHashW`. Used a one-word
  dummy record (`w = 1`, the field written but never read) rather than `w = 0`, as the
  recommendation suggested — `Schema.WF` does not literally exclude `w = 0`, but a dummy field
  sidesteps having to check that a zero-stride schema's address function is still injective
  where it is used (it collapses to `S.ad t i f = f`, independent of `i`, which the generic
  proofs never needed to know is harmless since `fld`/`pushG` are simply never invoked at a
  field index there isn't one of). The record relation `ZRecRel`, `MatchOK` and `NewOK` are all
  `True`/`trivial`/`rfl`: `ZeroNode`'s only inhabitant makes every obligation about it hold by
  `cases` + `rfl` (`zeroNode_eq`). The L code keeps the full probe-loop shape (while loop,
  `abort` on exhaustion) with the match test written as the tautology `0 == 0`, rather than
  special-casing the loop away, so it needed no library change and no new proof idea — just an
  always-true arm instead of a real comparison.
* **`max`, `imax`** (`MaxStore.lean`/`ImaxStore.lean`, same file content up to systematic renaming
  and the tag/`CTL` base): the `app` shape exactly (`BinLNode { u v : LIdx }`, two handle fields,
  width 2), with no scratch skip (the level store's `LStore.find?` probes the persistent tier
  unconditionally, as for `succ`). Arrays `MREC`/`MSLOT` = 10/11 (`CTL[10 + t]`, tag `2`),
  `IREC`/`ISLOT` = 12/13 (`CTL[12 + t]`, tag `3`). Both went through at the first attempt once the
  usual off-by-one of a fresh `#guard` test fixture's `CTL` array length (it must reach
  `ca + 2`, not just the previous table's high-water mark) was caught by the evaluator, not a
  proof failure — see "Findings" below.
* **`param`** (`ParamStore.lean`/`ParamRefine.lean`, arrays `PREC`/`PSLOT` = 14/15,
  `CTL[14 + t]`, tag `4`): `ParamNode { n : NIdx }`, the `succ` shape (one handle field, width 1),
  but the handle is a **name** handle, not a level one. `word_decI`/`hix_hdW`/`isPersistent_decE`
  (`StoreRel.lean`) are already stated `{k : IdxKind}`-generically, so nothing there needed
  touching; the only change from `succ`'s template is the `Idx .name` instantiation of `Lens`
  and `decI`/`word_decI` at that kind. No scratch skip, as for every level node.

| table | L lines | spec lines | relation lines (non-blank) | `lean` user (Store + Refine) | clean? |
|---|---:|---:|---:|---:|---|
| `zero` | 38 | 87 | 140 | 2.8 + 0.9 = 3.7 s | yes, first attempt |
| `max` | 42 | 87 | 178 | 6.3 + 1.2 = 7.6 s | yes, first attempt |
| `imax` | 42 | 87 | 178 | 6.3 + 1.3 = 7.6 s | yes, except the `#guard` fixture fix below |
| `param` | 38 | 87 | 166 | 4.4 + 1.2 = 5.6 s | yes, first attempt |
| `sort` | 42 | 87 | 175 | 6.5 + 1.1 = 7.6 s | yes, needed one library generalisation (below) |
| `const` | 46 | 87 | 194 | 9.0 + 1.2 = 10.2 s | yes, after fixing two scripted-rename mistakes |
| `letE` | 48 | 87 | 218 | 11.6 + 1.3 = 12.9 s | yes, first attempt (written by hand, not scripted) |

"L lines" is the probe loop, `*_find`, `*_push` and `intern_*` function bodies only; "spec lines"
the three `vcgen` sections (`find`/`push`/`intern`) that prove them; "relation lines" the whole
`*Refine.lean` file (schema, record relation, the three query obligations, the bridges,
`*intern_correct`, the `*_refines` theorem). `max`/`imax` are heavier than `zero`/`param` only
because width 2 means two `fld_push*`-shaped equations instead of one in `*NewOK`, exactly as
`app` was heavier than `succ` before the library (`StoreLib.lean`'s own assessment).

### Findings

* **A fresh `#guard` fixture's `CTL` array must be sized for every table that exists in the
  project, not just the one under test.** `ImaxStore.lean`'s differential `#guard`s initially
  reused `MaxStore.lean`'s `imaxMem`-shaped literal (a `CTL` array long enough for `max`'s
  `CTL[10], CTL[11]` but not `imax`'s `CTL[12], CTL[13]`). `Mem.set64` is `Array.set!`, which is a
  silent no-op past the array's current length — so the write to `CTL[12 + t]` after a push
  simply vanished instead of erroring, and the two `#guard`s failed on the computed handles
  (0 and 1 where 0x30000000/0x30000001 were expected) rather than on a proof. Each table's own
  `*Mem`/`#guard` fixture is independent (one file, one local test memory), so this is purely a
  per-file bookkeeping hazard, not a library gap: fixed by widening the literal `CTL` array to
  `ca + 2` words. Nothing in the `vcgen` proofs or the library was at fault.
* Every other table in this round (`zero`, `max`, `param`) went through at the first attempt,
  with the same `sym only [lang_grind, arena_grind] => vcgen […] <;> finish […]` house form as
  `succ`/`app`, confirming the recommendation's estimate for "handle words only" tables: no new
  proof idea, each about 230 L-side lines and 160–180 relation lines, a few seconds of CPU.

### `sorry`s

None.

### The expression store: `sort`, `const`

Order per the task, continuing into expression handle-only kinds. Both are new arrays (next free
ids after the level store's `PREC`/`PSLOT` = 14/15): `sort` at `SOREC`/`SOSLOT` = 16/17
(`CTL[16 + t]`, tag `2`), `const` at `CREC`/`CSLOT` = 18/19 (`CTL[18 + t]`, tag `3`). Unlike the
level store, the expression store's `internE` has the scratch skip (`EStore.persFindMaybe`,
`eViewHasScratchChild`), so both tables are `app`'s shape (`skSo`/`skCe`, `so`/`ceskipW_eq`), not
`succ`'s.

* **`sort`** (`SortStore.lean`/`SortRefine.lean`): `SortNode { u : LIdx }`, one field, the
  `succ`/`param` L-side shape (a single-field probe and push) but with `app`'s single-field skip
  test (`eViewHasScratchChild (.sort u) = !u.isPersistent`, i.e. skip iff `u` is a scratch
  handle) grafted on, the way `app`'s two-field skip is. This needed one small library
  generalisation: `StoreRel.lean`'s `isPersistent_decE` was stated only for expression handles
  (`(decE w).isPersistent = …`), because it had only ever been used to decode an `app` child,
  which is itself an expression handle. `sort`'s child is a **level** handle, so the proof needed
  the same fact at `Idx .level`. Added `isPersistent_decI {k : IdxKind} (w) (hw) : (decI w :
  Idx k).isPersistent = ((w >>> 27) &&& 1 == 0)` (the old proof, with `decE` replaced by `decI`
  and the kind made a parameter) and restated `isPersistent_decE` as its one-line `.expr`
  specialisation (`rw [decE_eq]; exact isPersistent_decI w hw`), so `AppRefine.lean` is unchanged
  and still builds. `word_decI`/`hix_hdW`/`decI` were already `IdxKind`-generic from the
  `storelib` port (needed for the level store's handles); `isPersistent_decE` was the one fact
  that port missed generalising, because nothing before `sort` needed the skip test at a
  non-expression child.
* **`const`** (`ConstStore.lean`/`ConstRefine.lean`): `ConstNode { n : NIdx, us : LsIdx }`, the
  `app` shape at two fields, but a **mixed-kind** key — the two words decode to a name handle and
  a level-list handle, not two expression handles. The L code (the probe, the push, the skip
  test `((n | us) >>> 27) & 1`) is `app`'s verbatim, since L has no notion of handle kind at all
  (everything is a `Word`); only `ConstRefine.lean` differs from `AppRefine.lean`, decoding each
  field at its own kind (`decI (k := .name)`, `decI (k := .levels)`) instead of both at `.expr`,
  using the same `isPersistent_decI`/`word_decI` generalisations `sort` needed. No further
  library change.
* **Writing `ConstRefine.lean` as a scripted rename of `AppRefine.lean`+`ConstStore.lean` of
  `AppStore.lean`** (as `max`/`imax`/`param` were) was riskier than for same-kind tables, and
  caught two mechanical mistakes worth recording: (1) a blind `sed 's/decE f/…/'`-style text
  substitution also matched inside `isPersistent_decE f hf` (a different identifier, not an
  application of `decE` to `f`), mangling it into a nonsense token; (2) `sed 's/internApp\b/.../'`
  silently failed to rename `internApp_spec` because `\b` does not match between two word
  characters (`p` and `_` are both "word" characters to POSIX/GNU sed's `\b`), so the function
  name survived the rename pass undetected until the build caught the unknown identifier. Both
  are copy-renaming hazards, not proof problems; the fix in each case was a direct, targeted edit
  once the compiler pointed at the exact line. Neither recurred in `zero`→`max`→`imax`→`param`
  because those renames kept every field at the same handle kind (`LIdx`→`LIdx` or `LIdx`→`NIdx`
  wholesale, never splitting a two-field record across two different target kinds) and used
  `\b`-safe suffixes throughout.
* Both tables' `vcgen` specs (the L side) went through at the first attempt, as every table has so
  far: the skip test is a Word-level computation with no handle-kind content, so it is identical
  code to `app`'s regardless of what the two fields denote at the arena level.

### `sorry`s

None.

### `letE`: three same-kind handle fields, and L has no division

`LetNode { ty val body : EIdx }` (`LetStore.lean`/`LetRefine.lean`, arrays `LEREC`/`LESLOT` =
20/21, `CTL[20 + t]`, tag `7`): `app`'s shape at three fields instead of two, all three the same
kind (`EIdx`), so (unlike `const`) `LetRefine.lean` decodes every field with the ordinary `decE`/
`isPersistent_decE`, exactly as `app` does — no new kind-generality was needed here. Written by
hand rather than as a scripted rename of `ConstStore`/`ConstRefine` (three fields do not track
two renamed ones cleanly, and the const port's two rename mishaps argued for not repeating the
scripted-rename approach at a third field count); went through at the first attempt on both
files.

* **The one genuine new thing: a non-power-of-two record width.** `LEREC`'s stride is `2 * 3 = 6`
  words (three fields, two tiers). Every earlier table's width was a power of two (1, 2 or 4),
  so its room check read `len(REC.u64) >> shift <= c` (dividing by the stride via a shift); `6`
  is not a power of two, and **L has no division operator at all** (`PLAN.md`, "the language
  L": "No division: Kraken has no div; divide by a power of two with `>>`."). The fix is not a
  language or library change but a different, already-available arithmetic form of the same
  check: `len(LEREC.u64) < (c + 1) * 6` (multiplication, which L has), which is in fact a more
  direct match for `PushRoom`'s own definition (`S.st.toNat * (cnt + 1) ≤ size`) than the
  power-of-two tables' shifted form was — `lepushOK_room`'s proof is a plain `grind` with no
  `UInt64.toNat_shiftRight` conversion lemma, shorter than `app`'s/`const`'s equivalent.
* **Three-way skip test from the library's two-way lemma.** `eViewHasScratchChild (.letE ty val
  body)` is `if ty.isPersistent then (if val.isPersistent then !body.isPersistent else true) else
  true`, i.e. "`ty`, `val` or `body` is a scratch handle". The L side computes this as one word,
  `((ty | val | body) >>> 27) & 1`; relating the two needed `bit27_or` (`StoreRel.lean`) **twice**
  — `bit27_or ty val` then `bit27_or (ty ||| val) body`, matching `|||`'s left-associativity
  (`ty ||| val ||| body` parses as `(ty ||| val) ||| body`) — composed in the proof, not inside
  the library: no new lemma, `bit27_or` is already general enough.
* The record relation, `MatchOK`/`NewOK` and the frame obligation are `app`'s/`const`'s two-field
  versions with one more conjunct/clause each (`fld_let0`/`fld_let` cover field 0 and the general
  case exactly as `fld_app0`/`fld_app` did); nothing else differed in shape.

### `sorry`s

None.

### Not done this round, and why

Seven tables landed (`zero`, `max`, `imax`, `param`, `sort`, `const`, `letE`); `bvar`, `fvar`,
`proj` (a handle plus a `Nat` field each) were not attempted. Not because any attempt got stuck:
none was started. Reasons to flag before starting one, for whoever picks this up next:

* **A `Nat` field is not a handle.** Every table so far decodes a stored word back into a handle
  (`decI`/`decE`, with `word_decI`/`isPersistent_decI` for the bound `< 2^32`) and compares
  handles for the match/key. `bvar`'s `i : Nat`, `fvar`'s `idx : Nat`, `proj`'s `i : Nat` are
  plain de Bruijn/field indices with no such decoding — `MatchOK`/`NewOK` there compare a stored
  `Word` against `UInt64.ofNat n` directly, under a bound hypothesis (`n < 2^64`, as the
  recommendation says), which is a different (if probably easy) fact than anything the `MatchOK`/
  `NewOK` obligations have needed up to `letE`: every one of those was proved by `word_decI`/
  `decE_eq` plumbing, not by a `Nat`/`Word` roundtrip. `lit`'s `natLitToConstructor`/pool slice
  comparison is the nearest precedent in this codebase, but it goes through the limb pool, which
  `bvar`/`fvar`/`proj`'s single small `Nat` should not need.
* **`fvar`/`proj` mix a `Nat` and a handle in one record** (`fvar { idx : Nat, ty : EIdx }`,
  `proj { n : NIdx, i : Nat, e : EIdx }`), so their `MatchOK`/`NewOK` need *both* kinds of
  obligation at once, and their scratch-skip test (`eViewHasScratchChild`) reads only the handle
  field(s), not the `Nat` one — worth checking that `MatchOK`'s statement composes cleanly
  (conjunction of a `Nat` equality and a handle equality) before assuming it is "just like
  `const`'s two fields" with one relabelled.
* **Budget.** This lane landed seven tables across two sessions' worth of the allotted time
  (level store plus three expression handle-only kinds); `bvar`/`fvar`/`proj` are next in the
  task's own order, genuinely small per the recommendation ("small"), and a reasonable next
  increment, but starting a new proof idea with under the stated 45-minute budget per table
  remaining risked a half-finished table or a `sorry`, which `PLAN.md` rules out. Left out
  rather than rushed.

## The arena relation and the first cached walk (2026-10-21, lane `walk`)

Files: `ConAgua/Arena/{BVarStore,BVarRefine,Memo,MemoRel,Frame,ArenaRel}.lean` (part 1),
`ConAgua/Arena/{Walk,WalkRefine}.lean` (part 2). No `sorry`; axioms `propext`,
`Classical.choice`, `Quot.sound`.

### Part 1: one relation `ArenaR` for the whole memory

**Layout** (`ArenaRel.lean`'s header has the table): arrays 0–23 as before plus `bvar` at 22/23
(`CTL[22 + t]`, new this lane, the first table with a `Nat` field) and the walk memo `BMEMO` at
24 (`CTL[24]` = live stamp − 1, `CTL[25]` = live count). `ArenaR m a` is a `structure` of twelve
named relations: the eleven tables (`LitR` with the pool, `AppR`, `SortR`, `ConstR`, `LetR`,
`BVarR`, `ZeroR`, `SuccR`, `MaxR`, `ImaxR`, `ParamR`) and `MemoR m a.memos.bvarBC`.

**Frames.** `MemFrame A C m m'`: only word arrays `A` and `CTL` words `C` changed, sizes kept
(`Frame.lean`). One generic lemma, `storeR_frame`, moves a `StoreR` across a writer it is
`Apart` from, given the instance's `RLocal` (the record relation and hash read only the record
array, plus `[POOL]`/`[CTL 0]` for `lit`; one line per table). `internM_frame`: every
`intern_*` model is a `MemFrame [ra, sa] [ca, ca + 1]`, proved once for the library's `internM`.
On the arena side `protoRun_st`/`AM.st_proto`: an interning ends in `a`, `L.setP a t` or
`L.setS a t`, so every other table relation holds of the new state by definitional unfolding
(`exact` closes it, no lemma per pair of tables). `ArenaR.lift_X` (11, generated text, 12 lines
each) and `internX_refinesA` (11, the old proof plus three lines) lift every table; `ArenaR.grow`
and `natAddLit_refinesA` do the pool (`grows_frame`: `Grows` is `MemFrame [POOL] [0]`).

**Initial state.** `arenaR_init`: `ArenaR (initMem sizes) (AState.init EStore.empty)` for any 25
sizes with `CTL` ≥ 26 words and the pool below `2^63` words; `initMem` is all zeros (the memo's
"stamp − 1" encoding is what makes zero memory an empty memo). This closes the gap the capstone
noted (`LitR` was not shown for any state).

**Grind-friendliness.** No `∀`-clause of the table relations is given to `grind`: the frame
proofs go through `tierR_mono` with named equalities. `decide` on `Apart` for concrete schemas
timed out (`UInt64` list memberships through the elaborator's `whnf`, also with `+kernel`); a
`simp` with the array ids (macro `apart`) is immediate.

**The `bvar` table** (`BVarStore`/`BVarRefine`): `succ`'s shape (one word, no scratch skip; a
`bvar` has no child) in the expression store. The record relation is `(rdW …).toNat = k.i`, so a
stored word *is* the index and `MatchOK` is `UInt64.toNat_inj`, no bound hypothesis; the L
argument is a word `u` and the key `⟨u.toNat⟩` (indices ≥ `2^64` cannot be interned through L).
The file was a scripted rename of `LevelStore`; a rename leftover (`sfindLoop_spec`) collided
with `LevelStore` only when both were imported (`ArenaRel`), and so did `Memo`'s first `mprobeW`
with `MaxStore`'s. All specs passed at the first attempt.

**The memo** (`Memo.lean`, `MemoRel.lean`): con-ron's `HashMap2` with epoch stamps (`clear` is
`CTL[24] += 1`), four words per slot (stamp, key, value, unused: L has no division, so the slot
count is `len >> 2`), linear probing from `homeW key`, overwrite on a present key, abort past a
3/4 load or where the stamp would wrap. `MemoR m mp`: stamps ≤ the live stamp, live slots hold
distinct keys mapped by `mp` to their value, each entry of `mp` is in a live slot on its run
after live slots. Lemmas `memoR_hit`, `memoR_miss`, `memoR_set` (= `insert`), `memoR_clear`
(= `∅`), `memoR_frame`. The L specs (`memo_find`, `memo_set`, `memo_clear`) are `vcgen` +
`finish` at the first attempt; the relation lemmas are by hand plus small `grind`s (the
uniqueness clause was missing in the first draft: an overwrite needs it).

| file | lines | `lean` wall / user | by hand |
|---|---:|---:|---|
| `BVarStore.lean` (L, specs) | 282 | 3.4 s / 4.5 s | none |
| `BVarRefine.lean` | 194 | 0.9 s / 0.9 s | `MatchOK` by `toNat_inj` |
| `Memo.lean` (L 33 lines, models, specs) | 267 | 1.4 s / 2.8 s | none |
| `MemoRel.lean` | 428 | 1.3 s / 2.1 s | most (reads after the writes: 110 lines) |
| `Frame.lean` | 171 | 0.8 s / 0.8 s | all, short |
| `ArenaRel.lean` | 716 | 1.0 s / 3.3 s | generated per-table lifts (~400 lines) |

### Part 2: the first recursive walk with a cache, `bvarBoundMemo`

**Choice.** `bvarBoundGo`/`bvarBoundMemo` (`Arena/ExprOps.lean:1404`, Rust
`arena/expr_ops.rs:1981`): the exact loose-bvar bound, memoized per node in `bvarBC`, read-only
on the store, used by the checker on the saturated branch of `bvarB` (`looseBVarsBoundedFast`,
`instantiate1Lift`'s cutoff). It is the simplest walk with a cache: no interning, a `Nat` result.
`liftLooseBVars`/`instantiate1` intern their results and key the memo by `(EIdx, Nat)`; they are
the natural next step on the same scaffolding.

**L code** (`Walk.lean`, `module`), recursive as con-ron's Rust is: `bb_go(h)` (memo probe, then
`bb_node`, then `memo_set`), `bb_node(h)` (decode tag/tier/index, the arena `view`'s checks:
scratch handle with the scratch tier closed, index past the count, then dispatch: `bvar` `i + 1`,
`sort`/`const`/`lit` `0`, `app` and `letE` recursive), `bb_memo(h)` (clear, walk, clear).
`max` and the truncating `z - 1` are branch-free (`x + (y - x) * u64(x < y)`, `z - u64(0 < z)`),
so a loop-free body has one path per tag. `fvar`, `lam`, `forallE`, `proj` `abort`: their tables
are not in L yet, and an `abort` claims nothing, so the refinement covers every handle.

**Proof shape.**
* *L side* (`Walk.lean`): models `bbW`/`bbNodeW` (mutual on L fuel, with `match` on the callee
  results), and one guarded equation per arm whose right side names the continuation
  (`bbW (n+1) m h = bbK h (bbNodeW n m h)`, `bbNodeW (n+1) m h = appK₁ n a (bbW n m f)`, and
  `appK₁ n a (some (x, m₁)) = appK₂ x (bbW n m₁ a)` …). The first attempt stated the arms as
  `bbW n m f = some (x, m₁) → … → bbNodeW (n+1) m h = some …`; `grind_pattern` rejects those
  (`x`, `m₁` occur in no pattern). With the continuation form every variable is in the pattern
  `bbNodeW (n + 1) m h`, and the callee posts rewrite the continuation's argument. The two
  specs are `BbGoSpec n`/`BbNodeSpec n` (named, `unfold`ed before `vcgen`: a spec hidden behind
  a definition is not found), proved by one induction on fuel, each step one
  `sym only … => vcgen … <;> finish`. The first version, one function with nested `if`s for
  `max`, failed in eleven verification conditions; splitting `bb_node` out and the branch-free
  arithmetic made it go through.
* *Arena side* (`WalkRefine.lean`, by hand, no `grind`): handle words decode
  (`decE_tag`/`decE_idx`/`decE_pers`), the view under `ArenaR` (`view_tier`, `get_*`, `node_of`:
  the record relation gives the node and its children as words), `ArenaR.memo_set` (`memo_set` is
  `bvarBSet`: `memoR_set` plus the frame of everything else) and `ArenaR.memo_clear`; then
  `GoOK n`/`NodeOK n` by induction on the fuel (`goOK`): the model returning `r` from `m` related to
  `a` implies `(bvarBoundGo F (decE h)).run a = .ok (r.toNat, a')` with `ArenaR m' a'` for every
  arena fuel `F ≥ n`. The arena's inner `do` block is named (`bbNodeA`, `bbArm`) and shown equal
  to `bvarBoundGo`'s by `congr`.
* *End to end*: `bbMemo_refines` (the L triple with `AM.ok`/`AM.st`/`AM.res`), `bbMemo_run`, and
  `bbMemo_x64` (`Capstone.lean`): from `ca_enter` on a state with `MemRel` and `ArenaR`, with
  machine fuel `N ≤ F`: `rdx = 1` (fuel or stack), `rdx = 2` (an `abort`: unrepresented kind,
  dangling handle, full memo), or `rdx = 0` and `bvarBoundMemo F (decE h)` returns `rax.toNat` in
  a state related to the final memory. As for `natAddLit_x64`, three outcomes, not two.

**Deep recursion.** `bb_bench(n, k)` (`WalkBench.lean`, not proved, a driver) interns the left
spine `app (… (app b b) …) b` over `b = bvar k` with `n` applications and runs `bb_memo` on it;
`WalkEmit.lean` compiles `benchProg` (no byte arrays, 25 word arrays) and `harness/walk.c` runs it
on all-zero arrays sized for `n`. For `n = 10^6` (recursion 10^6 deep, through the `f` child):
`ok 8` with a 1 GiB stack (also for `n = 3·10^6`), `exhausted` (`rdx = 1`) with a 16 MiB stack, and
`exhausted` with fuel 1000. The smallest stack that suffices for `10^6` is 184,000,384 bytes:
184 bytes per level (the frames of `bb_go` and `bb_node` with their return addresses).

**Measurements** (`perf stat -e instructions:u`, one run each; "build" is the same run without
the walk: `k ≥ 2^63` for L, `walkbench N K build` for Lean):

| `n` | compiled L: build / build + walk / walk | con-ron's compiled Lean (`lake exe walkbench`): build / total / walk |
|---:|---|---|
| 10^5 | 40.8 M / 113.1 M / 72.3 M | 196.9 M / 306.8 M / 109.9 M |
| 10^6 | 422.9 M / 1146.0 M / 723.1 M | 1870.9 M / 2915.0 M / 1044.1 M |

About 720 instructions per node for the naive compiled L walk (three memo probes per `app`
node: its own miss, the `bvar` child's hit, the insert's re-probe), against about 1040 for
con-ron's arena compiled by Lean (`Std.HashMap`, boxed `Nat`s). Building the term through the L
stores costs a quarter of Lean's. con-ron's Rust could not be measured (no `cargo` here).

| | Rust lines | L lines | spec / relation lines | `lean` wall / user | automation |
|---|---:|---:|---:|---:|---|
| walk (`bb_go`, `bb_node`, `bb_memo`) | 87 (`bvar_bound_go`, `bvar_bound_memo`) | 49 | `Walk.lean` 366 (models 75, arms 90, specs 50) | 10.1 s / 11.0 s | specs: `vcgen` + `finish`; arm equations: `simp` |
| memo (`memo_find/set/clear`) | ≈ 110 (`HashMap2` index, probe, get, insert, clear; no resize) + 18 (`bvar_b_*`) | 33 | `Memo.lean` 267, `MemoRel.lean` 428 | 1.4 s, 1.3 s | specs automatic; relation by hand |
| arena refinement | – | – | `WalkRefine.lean` 481 | 0.9 s / 1.5 s | by hand, `simp`/`rw` |

L/Rust is 0.56 for the walk and about 0.3 for the memo (no resize, no generic code).

### Findings

* **Kraken's AT&T printer and binutils 2.46 disagree on `imul`**: the compiler's two-operand
  `imul rax, rcx` is printed `imulq %rcx, %rax, %rax`, which binutils 2.46 assembles as an APX
  instruction (EVEX, SIGILL here). The scanner never multiplies, so the walk is the first compiled
  program to hit it; every store (`homeW`, FNV) multiplies, so `natAddLit_x64`'s code would too.
  The printer and the assembler are trusted, so this is a trusted-base mismatch:
  `docs/gaps/kraken-att-imul-three-operand.lean` (not fixed upstream as of 2026-10-21, checked
  against `AeneasVerif/kraken` `main` and the `vcgen` fork). Fixed properly in lane `imul`, below
  (`asmText`'s `fixImul`, a `Directive`-level normalisation, not the textual patch this lane
  first used).
* `decide` on the frame side conditions (`Apart`, bounded `∀` over `List UInt64`) fails or times
  out: `docs/gaps/decide-uint64-list-ball.lean`; a `simp` with the ids (`apart`) works.
* `vcgen` does not see a spec behind a named predicate (`BbGoSpec p n`); `unfold` it first.
* Guarded equations must have every variable in a pattern; continuation functions
  (`appK₁ n a (some (x, m₁)) = …`) are the way to say "after the callee returned `some`".
* The house rule "loop bodies must be straight-line" holds for recursive bodies too: `if r < y`
  after two calls doubled the paths and failed; branch-free `u64(…)` arithmetic went through.

### L / compiler features

None added to `ConAgua/L` or `ConAgua/Compiler`. Needed and worked around: the `imul` printing
(above). Useful later: a statement `call f(…)` without a result (the walk assigns to a dummy
local).

### `sorry`s

None. (`vendor/con-leche/ConLeche/Challenge.lean`'s are vendored and pre-existing.)

## The `imul` fix and the asm/disassembly audit (2026-10-21, lane `imul`)

Files: `ConAgua/Compiler/Run.lean` (`fixImul`, `asmText`), `ConAgua/Arena/EmitStore.lean` (new,
emits `storeProg`), `scripts/check-asm.sh`, `scripts/check_asm.py`,
`docs/gaps/kraken-att-imul-three-operand.lean`.

**The fix.** The walk lane's finding (above) is real: Kraken's `.imul (some d) a b` is always
printed in three-operand AT&T syntax, which binutils 2.46 reads as the APX "new data destination"
form (EVEX-encoded) whenever it can, rather than the plain two-operand `imul` the compiler means.
The compiler's one `imul` (`Compile.lean`'s `binInstr .mul`) always has `d = a`
(`rax := rax * rcx`), and for that case `.imul (some a) a b` and `.imul none a b` are *the same
instruction* (`Kraken/X64/Semantics.lean`'s `.imul dst src1 src2` stores to `src1` when
`dst = none`); Kraken's own printer already writes `.imul none a b` in the two-operand form every
assembler accepts. So `asmText` now maps `fixImul` over `compileProg`'s `Directive`s before
printing, rewriting `.imul (some d) a b` to `.imul none a b` whenever `d = a` (a `BEq`/`DecidableEq`
check on `RegOrMem`, already derived) and leaving every other directive (including a `d ≠ a` three-
operand `imul`, not emitted here) untouched. This is a normalisation of what gets printed, not a
textual patch of the printed assembly; `compileProg` and `compile_correct` are unchanged.
`WalkEmit.lean`'s textual `fixImul : String → String` (a `String.replace`) is gone.

**The asm/disassembly audit, `scripts/check-asm.sh`.** The printer and the assembler sit outside
`compile_correct` (the theorem is about Kraken's own instruction semantics, which `as` must
realise faithfully for the proof to say anything about the real machine), so the `imul` mismatch
is one instance of a whole class of risk: nothing checks that the other ~25 instruction forms the
compiler emits (`Step.lean`'s count) survive printing and assembling unchanged. `check-asm.sh`
automates that check for every program the compiler proof covers (`scanProg`, `storeProg`, the
walk's `benchProg`, via `EmitScan.lean`/the new `EmitStore.lean`/`WalkEmit.lean`): it assembles the
printed `.s` with `as`, disassembles the object with `objdump -d`, and (`check_asm.py`) compares,
instruction by instruction:
* the raw opcode bytes' first byte against an APX prefix deny-list (EVEX `0x62`, REX2 `0xd5`):
  Kraken's `Instr`/`Operation` syntax has no APX case at all, so any instruction encoded this way
  is outside what the proof covers regardless of what text it disassembles to (an EVEX
  `imul %rcx,%rax,%rax` and the intended legacy one can disassemble to identical-looking text,
  which is why this check is on bytes, not text — it is what would have caught the `imul` bug
  before it was found by hand, since a text-only diff does not);
* mnemonic (normalising the conditional AT&T width suffix `objdump` elides when registers already
  disambiguate it, and `mov`'s `movabs` widening for a 64-bit immediate that doesn't fit a
  sign-extended 32-bit field — both benign, already-equivalent spellings, not printer bugs);
* operand count and kind (register/immediate/memory/branch-target);
* register names (exact), immediate and memory-displacement values (parsed and compared modulo
  `2^64`, so hex-vs-decimal and sign-extension display differences don't cause false positives),
  and a memory operand's base/index/scale registers (exact); a branch/call target is only checked
  for being a target (not a register/immediate/memory operand — the family of bug `imul` is), since
  resolving its address is the linker's job, not the printer's.

Run: `scripts/check-asm.sh` (rebuilds the three `Emit*` drivers, then checks each). Current
result: scan 303, store 1275, walk 3476 instructions, all matching; reverting `fixImul` makes the
walk check fail immediately with the APX-prefix diagnostic (checked by hand while developing the
script, not left reverted).

**Findings.**
* The three-operand `imul` was reproduced standalone (a bare Kraken `Directive`, no compiler):
  printed text, `as`/`objdump` showing the EVEX encoding (`62 f4 fc 18 af c1`), and a `SIGILL`
  (exit 132) running it, against the two-operand form's correct `48 0f af c1` and exit value; see
  `docs/gaps/kraken-att-imul-three-operand.lean`. Not fixed upstream: `AeneasVerif/kraken` `main`
  (`72f3a7a3`) has the identical printer code as the `vcgen` fork (`ba12834`).
  `fixImul`'s rewrite needs only `d = a`'s `DecidableEq`, already derived on `RegOrMem`.
* `mov`'s width suffix is not the only place the printer's and `objdump`'s AT&T text can
  legitimately differ while meaning the same instruction: a `mov`-immediate-to-register with a
  64-bit immediate that doesn't fit a sign-extended 32-bit field disassembles as `movabs`, a GNU
  assembler/objdump spelling for the same opcode choice (`B8+r`, not a `C7 /0` with a 32-bit
  immediate), not a bug. There is no such alternate encoding for an immediate-to-*memory* `mov`
  (the compiler's only one, `zeroLocals`, always writes `0`, so this never arises there).
* `Prog.tab storeProg 0 25` (no byte arrays, 25 word arrays — the arena's layout) is enough for
  `Prog.wf`; `EmitStore.lean` follows `WalkEmit.lean`'s shape. There is no C driver for
  `storeProg`/`nat_add_lit` (unlike `scanProg`'s `run.c` and the walk's `walk.c`); this lane only
  needed `asmText`'s output, not to execute it, so none was written.

**Addendum: closing the gap instead of normalising around it (2026-10-21, lane `capB`).** The fix
above left a small residual gap: `compile_correct` is a theorem about `compileProg`'s own
`.imul (some d) a b` (with `d = a`), while the *printed* assembly is `fixImul`'s rewritten
`.imul none a b` — the same instruction by Kraken's own semantics (`Semantics.lean`'s `.imul dst
src1 src2` stores to `src1` when `dst = none`; here `src1` already *is* `d`), but connected only
by the doc comment's argument, not a theorem, so `compile_correct` was not, strictly, a theorem
about the bytes `as`/`objdump` actually see. Closed by making the compiler emit the one-destination
form directly: `Compile.lean`'s `binInstr .mul` is now `i64 (.imul none (.reg (rr .rax)) (oR .rcx))`
(previously `.imul (some (.reg (rr .rax))) …`); `fixImul` and its use in `asmText` are gone
(`asmText` now prints `compileProg`'s own output verbatim). The compiler proof needed **no
change**: `Step.lean`'s `ev_bin` (the one lemma per `BinOp` that steps over `binInstr op`, `.mul`
included) already discharged its `.imul`-shaped verification condition by simp-unfolding
`Operation.interp`'s `.imul` case, and that unfolding is exactly as direct for `dst = none` (no
match to resolve: the `none` branch *is* `src1`) as it was for `dst = some src1` (a match that
happened to resolve to `src1` too) — so `L.Compiler.compile_correct` rebuilds unchanged, and
`#print axioms compile_correct` is still exactly `propext`, `Classical.choice`, `Quot.sound`.
`scripts/check-asm.sh` still passes, byte-for-byte identical to before (scan 303, store 1275, walk
3476 instructions, all matching — the printed text was already `fixImul`'s output, so making the
compiler itself emit it changes nothing printed, only what the proof is *about*); `run --lines` on
con-leche's `complete_c04a_restart_70.ndjson` (126481 lines) still reports 0 mismatches, and
`harness/walk.c` (whose `imul`-heavy memo hash was the original trigger) still runs correctly
(no `SIGILL`). `ConAgua/Arena/WalkEmit.lean`'s doc comment, the `fixImul` mentions in
`scripts/check-asm.sh`'s comment, and `docs/gaps/kraken-att-imul-three-operand.lean`'s cross-
reference were updated to match; the gap writeup itself is left as the historical record of the
bug.

### `sorry`s

None (no proof touched; `compile_correct` unaffected, `#print axioms` unchanged:
`propext`, `Classical.choice`, `Quot.sound`).

## Every term store in `ArenaR`, and the walk over every node (2026-10-21, lane `tables2`)

Files: `ConAgua/Arena/{FVar,Proj,Lam,Forall,NAnon,NStr,NNum,Ls}{Store,Refine}.lean`,
`ConAgua/Arena/PoolSlice.lean` (new), `ConAgua/Arena/ArenaRel.lean` (regenerated, `arena_build`),
`ConAgua/Arena/{Walk,WalkRefine,WalkBench,WalkEmit}.lean`, `ConAgua/Arena/harness/walk.c`. No
`sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`. `fvar`/`proj`, `lam`/`forallE` and the name store's
`anonymous`/`num` were written by three subagents in parallel worktrees, one file pair per table;
the variable-length keys and `ArenaR` in the lane's own worktree.

### Layout

The tables after `bvar`/the memo take arrays 25‥40 and count words `CTL[s + t]`, `s` the table's
slot array (25‥40 are free in `CTL`, the memo uses 24/25): `fvar` 25/26, `lam` 27/28, `forallE`
29/30, `proj` 31/32, name `anonymous` 33/34, name `str` 35/36, name `num` 37/38, level lists
39/40. `ArenaRel.lean`'s header has the whole table. `arenaR_init` now takes 41 arrays and a `CTL`
of at least 42 words.

### Variable-length keys: one pool for limbs, bytes and handle lists

The level-list key (`List LIdx`) and the name `str` key (`String`) live in `POOL`, the array the
`lit` store already keeps its limbs in, below the same top `CTL[0]`: a level list as its handle
words, a string as its UTF-8 bytes, one byte per word. The record holds the slice `(o, l)` and the
hash; the L code reuses `lit_hash` and `limbs_eq` unchanged (`ls_match` and `nstr_match` call
`limbs_eq`, `intern_ls`/`intern_nstr` call `lit_hash`). Because the pool is shared, the pool's
invariant `PoolOK` and its frame `Grows` are `lit`'s: `ArenaR.grow` keeps `LsR` and `NStrR` by
`LsR.grow`/`NStrR.grow` (slices below the old top do not move, `Agree.sliceL`), exactly as
`LitR.grow`. The caller of `intern_ls`/`intern_nstr` puts the words below the top first (the
refinement theorems take `SliceOK` and `sliceL pool o l = lsWords us` / `= strWords s`).

**What is shared with `lit` (measured).** `PoolSlice.lean` (57 non-blank lines) states a key as
a list of words: `sliceL p o l` (the slice as a `List Word`), `slice_key` ("the lengths agree and
`limbs_eq` holds" iff the two word lists are equal, for slices that do not wrap), `slice_key_hash`,
`Agree.sliceL`. A table adds its encoding and the encoding's injectivity: `lsWords_inj` (3 lines,
`Idx.word` is the structure's only field), `strWords_inj` (3 lines, `String.toByteArray_inj` and
`ByteArray.ext`). `lit` does not fit the statement: a `natVal` key is a *normalised* slice and its
uniqueness is about the value (`pv_len`, `pv_limbs`), so `lit` shares the two lemmas underneath
(`eqW_iff`, `hashN_congr`), not `slice_key`. Rewriting `lit` on `slice_key` would need the limbs of
a number as a list and the uniqueness of normalised limb lists; not done (no gain: the 118 lines of
`pv` facts stay either way).

One byte per word costs 8× the memory of packed strings; it keeps the comparison and the hash
`lit`'s and the key a word list. Packing (eight bytes per word, a length in bytes) is a later
optimisation of `nstr_match`/`lit_hash` with its own injectivity lemma.

### The tables

| table | key | L lines | spec lines | relation file (non-blank) | `lean` user Store + Refine | first attempt? |
|---|---|---:|---:|---:|---:|---|
| `fvar` | `Nat` + expression handle, skip on `ty` | 46 | 87 | 198 | 9.1 + 1.2 s | yes |
| `proj` | name handle + `Nat` + expression handle, width 3, skip on `n \| e` | 48 | 87 | 214 | 11.9 + 1.3 s | yes |
| `lam` | two expression handles, own protocol (`internLamE`) | 46 | 81 | 216 | 9.0 + 2.5 s | L side yes; the unfolding needed `repeat' split` |
| `forallE` | the same, its own array | 46 | 82 | 217 | 11.1 + 2.7 s | after `forallE_ne_lam` |
| name `anonymous` | none (the `zero` shape) | 38 | 87 | 144 | 2.9 + 1.0 s | yes |
| name `num` | name handle + `Nat` | 42 | 87 | 191 | 6.3 + 1.3 s | yes |
| level lists | `List LIdx` in the pool | 55 | 130 | 252 | 6.6 + 1.4 s | L side yes; relation: three small fixes (below) |
| name `str` | name handle + `String` in the pool | 60 | 133 | 274 | 8.0 + 1.5 s | L side yes; relation: two small fixes |

"L lines" are the function bodies (`*_match` for the pool tables, `*_find`, `*_push`,
`intern_*`); "spec lines" the `vcgen` sections. Every L spec, including the two pool tables'
`*_match` that call `limbs_eq`, went through with the house form at the first attempt (twenty
tables now). The fixes in the pool tables' relation files were all Lean API names or goal shapes,
not proof ideas: `List.ofFn_inj` does not exist (`List.ext_getElem_iff`), `List.map_injective_iff`
does not exist (`List.map_inj_right`), `String.bytes_inj` is deprecated (`String.toByteArray_inj`),
the name store's `internNNode` reads `s.store.ns` (`EStore.ns` has to be in the unfolding's `simp`
set, unlike the level store's `EStore.ls`), and `NewOK`'s goal after `simp` ends in `∧ True`.

**`lam`/`forallE`: a second protocol was not needed.** `internLamE` probes with `EStore.findBind`
(the skip `bindHasScratchChild`, then the scratch `findBind`), tests the capacity, and calls
`internBind`, which probes *again* before `pushBind`. The re-probe is the same term on the same
state, so its `cases` are the probe's own; `internE (.lam ty b)` unfolds to the library's
`protoRun` (16 lines, `app`'s is 14) with `(repeat' split) <;> first | rfl | simp_all […]` in place
of `app`'s `(try split) <;> simp_all […]`, and for `forallE` one lemma
`(ETag.forallE == ETag.lam) = false` (`pushBind`/`findBind` dispatch on the tag). After that
`intern_correctG` applies unchanged.

### `ArenaR` without quadratic text: `arena_build`

With 19 tables the old per-table lift lemmas (every other table's frame, one `have` each: 19 lines
per table, 360 for all) and the two memo writers (every table listed) grow quadratically. One
tactic replaces them: `arena_build hR, hf with tac` builds an `ArenaR` field by field, each field
by `first | tac | exact hR.<field>.frame _ _ _ _ hf _ (by apart)`. The written table's field is the
one `tac` closes (`exact hX`); for the memo writers `tac` is `exact memoR_set …`, for the pool
`first | exact LitR.grow … | exact LsR.grow … | exact NStrR.grow …`. A lift lemma is now five
lines, `ArenaR.memo_set`/`memo_clear` and `ArenaR.grow` one line each; `ArenaR.frame` (all `Apart`s
as hypotheses, unused) is gone. A failing `tac` on another field is a type mismatch, found before
`apart` runs; `ArenaRel.lean` checks in 1.7 s wall for 19 tables (11.5 s user, the `apart`s in
parallel; with all 19 tables 2.2 s wall, 18.8 s user). `ArenaRel.lean`'s table-dependent parts (imports, header, `RLocal`s, frames, fields,
`arena_build`, `arenaR_init`, lifts) were generated by a script from a table list (never
committed); since lane `exprops` the file is **maintained by hand** (no generator; a new table is
the five short pieces listed under Findings below); the `intern*_refinesA` theorems are written per
table.

### The walk over every node kind

`bb_node` now dispatches all ten tags: `fvar` (1) is `0` after the count check `CTL[26 + t]`,
`lam`/`forallE` (5, 6) recurse into both children and return `max x (y - 1)` (branch-free, as
`letE`'s body), `proj` (9) returns `bb_go` of its third word. Only an unknown tag (10‥15) aborts,
where the arena's `view` fails too; under `ArenaR` every handle the arena can view is walked.
The model gains four arms and the guarded equations `bbNodeW_fvar`/`_lam`/`_forall`/`_proj` (the
binder arms through one continuation pair `bindK₁`/`bindK₂`, shared by `lam` and `forallE`; `proj`
is `bbW n m e` directly). The refinement (`WalkRefine.lean`, +93 lines): `get_fvar`/`_lam`/
`_forall`/`_proj`, one lemma `bindArm_ok` for both binder arms, and four arms of `nodeOK_succ`;
it went through at the first attempt. `bbMemo_refines`, `bbMemo_run` and `bbMemo_x64` keep their
statements; the `rdx = 2` outcome no longer includes "a node kind not represented".

**One verification condition budget raised.** `bbNode_step` (`vcgen` + `finish` over the ten-way
dispatch, five of them with recursive calls) hit the default 200000 heartbeats; with
`set_option maxHeartbeats 1000000` it goes through unchanged, and `Walk.lean` checks in 18.9 s
(10.1 s before). Splitting `bb_node` by tag groups into two functions, as the walk lane split
`bb_go`/`bb_node`, would bring it back under the default; not done, the budget is the cheaper fix
while the file stays under 20 s.

**The compiled walk.** `WalkEmit`/`walk.c` now use the full 41-array layout (`CTL` 42 words, the
table at `T[2 + 2·41]` on). `scripts/check-asm.sh`: walk 6369 instructions (3476 before), all
matching. `walk N 3` (the `app` spine, `perf stat -e instructions:u`, one run): `10^5`: 113.1 M
total, 40.8 M build; `10^6`: 1146.0 M / 422.9 M, the same as before the new arms (the `app` test
comes second in the dispatch). `exhausted` with a 16 MiB stack and with fuel 1000, as before. A
`#guard` (`WalkBench.lean`) walks `lam (fvar 0 (sort u)) (forallE (bvar 1) (proj c 0 (bvar 3)))`
in the interpreter: `2`.

### Findings

* **Subagents per table work** when the layout, the file names and a name prefix are fixed up
  front: three parallel `sonnet` lanes delivered six tables with no collision; the merges
  conflicted only in `lakefile.toml`'s `globs` (adjacent-line edits), resolved by hand. One agent
  rewrote the glob line and duplicated two entries; check the list after each merge.
* **The quadratic `ArenaR` text is gone** (`arena_build`); adding a table to `ArenaR` is a field,
  an `RLocal` (3 lines), a frame (2), a lift (5) and its `intern*_refinesA` (18).
* **Pool-keyed tables need no new library piece**: `StoreLib` is unchanged by this lane; the pool
  tables' `RFrame`/`RLocal` read `POOL` and `CTL[0]` exactly as `lit`'s do.

### Not done

* `lit`'s `strVal` contents: with the string pool in place, a `strVal` node could be kind `1`
  over `strWords s` (a second `intern_lit` entry, the match testing the kind); `LitR` still says
  only "kind 1".
* The derived columns (hashes and flags through `mixHash`) and the scratch tier's lifecycle
  (`enableScratch`/`dropScratch`), as before.

### `sorry`s

None.

## Stage B: a line validator for lean4export (2026-10-21, lane `stageb`)

Files: `ConAgua/Scan/{Common,Key,Str,Values,Member,Records,Line,Validator}.lean` (L code, models,
specs), `ConAgua/Scan/{WordLink,LeafLink,KeyLink,ValuesLink,StrLink,RecordsLink,LineLink,
DriverLink,ValidatorLink}.lean` (models against con-leche), `ConAgua/Scan/EmitValidator.lean`
(assembly for `harness/run.c`), `ConAgua/Scan/Bench.lean` (the `valbench` exe), and
`docs/gaps/vcgen-have-before-induction.lean`. No `sorry`; the main theorems use only `propext`,
`Classical.choice`, `Quot.sound`.

### What is proved

`L.Scan.Validator.valProg` (59 L functions, entry `validate`) stores nothing: it checks a buffer
line by line and returns `0` (every line scans) or the number of the first line that does not.
`ConAgua/Scan/ValidatorLink.lean`, under `numBits = 64` and `b.size < 2 ^ 63`:

* `scanLine_run`: whenever `scan_line(i)` returns, it returns `(1, next)` exactly when
  con-leche's `scanLineFwd b i` is `.ok _ next`, and `(0, 0)` exactly when it is an error. So the
  line function accepts iff `scanLineFwd` does, with the same next position (`0` for a last line
  without a newline). Every check is kept: escapes, UTF-8, key sets, `seen` masks, duplicate and
  missing keys, JSON's alternation, leading zeros, `max`/`imax` with exactly two members,
  `binderInfo`/`hints` spellings, the `meta` header's balance, trailing bytes. There is no
  id-table lookup in `scanLineFwd` (indices are only read, not resolved), so nothing had to be
  given up.
* `validate_run'`: `validate()` returns `scanDriver b 0 0`, con-leche's `scanLineFwd` run over the
  buffer as `parseBytes` runs it (`feedChunk`, then `applyFinalLine` on the tail) without
  applying the lines; `validate_accepts`: if `parseBytes b` succeeds the validator returns `0`;
  `validate_rejects`: if it returns `n ≠ 0`, `parseBytes b` fails at line `n` or earlier.
* `valProg_wf`: the compiler's static check passes, so `compile_correct` applies.

All of this is partial correctness, as everywhere in this project: an L run that ends in an
error (fuel, an out-of-bounds read) gives no answer, and the compiled code reports it as
`exhausted`/`error`. con-ron's `feed_chunk` asks `newline_from` after a failed line, to tell a
malformed line from one a chunk boundary cut; on a whole buffer both branches end in the same
error at the same line (`applyFinalLine` scans the tail again), so `validate` does not ask.

### Structure

Three layers, as in Stage A, but the models compute with words (`UInt64` positions, compared
with `UInt64.ofNat b.size`, which is what `len(IN.u8)` evaluates to), as lane `lext` did for
`utf8_decode`: a model is con-leche's function with `USize` replaced by `UInt64` and the records
dropped, and every validator returns the position after what it read or `0` for failure. The
L proofs then see the same terms as the model; the arithmetic moves into the links, where
`USize → UInt64` is a ring and order isomorphism under `numBits = 64` (`WordLink`).

* **`next_member` and one generic record model.** Without the values they store, con-leche's 18
  record loops differ only in their key sets. `objN bit val mask` (`Member.lean`) is the slot
  loop for any key set: `bit k` is key `k`'s `seen` bit (`0`: not a key of this record), `val k
  ks v` scans its value, `mask` is the required bits; `objListN item` is the list of objects.
  The models of the 18 records are instances (`appBit`, `appVal b`, `3`, …); the L code keeps
  Rust's shape, one function per record with `next_member` factored out (Rust's deviation 3),
  and each is proved against its instance. The record L code, the instances and the proofs were
  generated from con-leche's loops by a script (`scripts/stageb/genrec.py`, see its `README`; the
  file was edited after generation and is hand-maintained since). `lam` and `forallE` share one L function and one instance,
  as Rust's `scan_binder_expr_loop` does.
* **`key_at`** follows con-leche's `keyAt` (first byte, length, unrolled compare): L has no
  slice type for Rust's `match_lit` against a `[u8; N]`. It is split into a dispatcher and six
  group functions (`key_at_g1`…`g6`): one 133-branch function did not get through `vcgen`.
* **`scan_string`** validates without storing (`Str.lean`). Rust and con-leche collect the
  unescaped bytes and validate them with `utf8_decode`/`String.fromUTF8?` at the end; the
  validator checks each escape as Rust does and validates each maximal raw run between escapes
  on its own (`utf8_valid`, the decode loop over `utf8_char` without the output). `StrLink.lean`
  proves this equivalent: `X ++ [c].utf8Encode ++ Y` is valid UTF-8 iff `X` and `Y` are (the
  position `|X|` holds a lead byte, so it is a character boundary; core's
  `Pos.Raw.isValidUTF8_extract_iff`), plus an induction relating con-leche's accumulator to the
  current raw run. The `\u` continuation is a helper `u_next`, and `scan_hints`' object branch is
  `hints_obj`/`hints_num`, to keep verification conditions short.
* Rust's `read_nat_at` fails past `u64` (its deviation 4); con-leche reads a `Nat` and never fails,
  so the validator does not read numbers at all. A value's end is checked (`num_end`), its value
  is not.

### Testing and measurements

`valbench FILE` (con-leche's compiled `scanLineFwd` with the validator's driver) and the
compiled validator under `harness/run.c` print the same verdict on all 492 con-leche e2e
fixtures, the 182 arena fixtures (3 files rejected by both), and 6000 random mutants of the
smaller fixtures (1–2 byte replacements, deletions, insertions from a set of JSON-relevant bytes;
5648 rejected by both, every rejection at the same line). `L.run` agrees with `scanLineFwd` on
con-leche's 59 scanner probes (`tests/ConLecheTests/ScanTests.lean`).

`perf stat -e instructions:u`, one run each, `complete_c04a_restart_70.ndjson` (9.1 MB, 126481
lines, accepted):

| | total | empty file | per byte |
|---|---:|---:|---:|
| compiled L validator (`run`) | 916.0 M | 0.15 M | 100 |
| con-leche's compiled `scanLineFwd` + driver (`valbench`) | 276.4 M | 2.7 M | 30 |

con-leche builds every record (allocations included) and still needs 3.3 times fewer
instructions: the naive compiler's cost (every operand through memory, table reloads per array
access, see "The compiler") and the call overhead of a validator that is mostly small functions.
On `long_line_5mib.ndjson` (one 5 MiB string): 797 M against 223 M.

Sizes (lines; build time with `lake env lean`, imports built; L lines are the `lfn`/`lblk`
bodies):

| file | Rust lines | L lines | file lines (L + models + specs/proofs) | build |
|---|---:|---:|---:|---:|
| `Key` (`key_at`, `value_at`) | 496 + 8 | 306 | 842 | 68 s |
| `Str` (`scan_string`, `unescape`, `hex4`/`hex3`, `utf8_valid`) | 223 | 99 | 649 | 12 s |
| `Values` (`slot_nat`, quoted nat, binder info, hints, nat list) | 135 | 103 | 637 | 8 s |
| `Member` (`next_member`, generic `objN`/`objListN`) | 81 | 28 | 418 | 4 s |
| `Records` (18 records, 4 lists) | 2149 | 995 | 2205 | 22 s (3 min CPU) |
| `Line` (`scan_line_loop`, `scan_line_fwd`, driver) | 298 | 110 | 511 | 136 s |
| `Validator` (program, `validate_run`, `Prog.wf`) | | | 122 | 3 s |
| links: `WordLink`/`LeafLink`/`KeyLink`/`ValuesLink`/`StrLink` | | | 109/240/583/419/750 | 0.4/0.4/3/4/2 s |
| links: `RecordsLink`/`LineLink`/`DriverLink`/`ValidatorLink` | | | 1124/556/202/73 | 34/7.5/0.5/1.6 s |

Totals: Rust about 3400 lines, L 1641, L-side files 5384 lines, links 4056 lines.

**How automatic.** Every L spec is `vcgen` + `finish` (the recipe of "Proof recipe"), with
guarded arm lemmas for the recursive models (`nextMemberN`, `objN`, `objListN`, `natListN`,
`unescN`, `lineN`, `validN`). The 22 record and list specs are one generated script each (about
40 lines with statement). The links are `fun_induction` on con-leche's functions; for the
records one generic theorem (`objN_link`) and one tactic macro (`obj_loop`) prove all 18 loops
(about 13 lines per record).

### Findings

* **Generation limit.** A function with a chain of calls with several results (`hex4`: four
  `byte_in`/`hex_val` pairs; a record loop after a five-result `next_member`) nests the state
  terms deeper than `grind`'s default generation limit (`gen := 8`), and `finish` fails or does
  not terminate. `sym (gen := 16) only [lang_grind] => …` (or 24) fixes it; `finish (gen := N)`
  inside `sym` is ignored. Also `St.setLocs_mem` (one equation for the memory after `setLocs`,
  `Common.lean`) instead of a chain through `St.setLocs_cons`.
* **Induction hypotheses as `grind` theorems.** With the loop spec's memory hypothesis
  `hm : s₀.mem.arr8 IN = b` as a separate argument, `grind` takes the induction hypothesis as a
  local theorem with pattern `St.mem #1` and instantiates it on every state of the
  verification condition. Putting it into the precondition (`⦃fun s => s = s₀ ∧ s.mem.arr8 IN =
  b⦄`) leaves no pattern. All new loop specs have this form.
* **Patterns on reads.** An arm lemma whose pattern mentions the model's `byteW b j` never fires
  if nothing creates that term; the pattern must mention the L side's read `b[j.toNat]` (as
  Stage A's arm lemmas do).
* A `have` before `induction` makes `vcgen` lose the induction hypothesis
  (`docs/gaps/vcgen-have-before-induction.lean`).
* Several heavy specs need `maxHeartbeats` (`indRec`, `indType`: 800000; `lineLoop`: 4000000;
  `unescapeLoop`: 1000000): the budget counts all `finish` calls of a theorem together.
* Cross-module `#eval`/`#guard` of an L program needs `meta import` of every module that defines
  one of its functions.

### `sorry`s

None.

## Limb-pool `Nat` ops: bitwise `land`/`lor`/`xor` (2026-10-21, lane `nat`)

Files: `ConAgua/Arena/NatBits.lean`. Milestone 3 continuation: `Nat.land`/`Nat.lor`/`Nat.xor` on
the limb pool, in the `nat_add`/`nat_mul` style (`ConAgua/Arena/NatAdd.lean`, `NatMul.lean`). No
`sorry`.

### The functions

`nat_land`/`nat_lor`/`nat_xor(oa, la, ob, lb)` (con-ron's `land`/`lor`/`xor` and their `*_from`
loops, `ron/nat.rs:658-703`): one pass combining limb `i` of each operand with `&`/`|`/`^`, the
shorter operand zero-extended (`nat_limb`, reused from `nat_add`), then `nat_trim`. `land`'s
result has `min la lb` limbs (so its loop never actually reads past either operand, but shares
`nat_limb` with the others for one loop shape); `lor`/`xor` have `max la lb`. Each needs its own
capacity check before the loop (`if len(POOL.u64) - top < n { abort }`, con-ron's own "no room"
style, con-ron's own `nat_mul`'s `<`, not `nat_add`'s `<=`: no carry limb here, the result is
exactly `n` limbs).

**Model.** `bv f p oa la ob lb k` is `xv` with a second zero-extended slice and a combinator `f`
instead of one read (`bv f p oa la ob lb (k+1) = bv f p oa la ob lb k + (f (lvW …) (lvW …)) * wt
k`, `lvW` being `lv` read back as a `Word` instead of a `Nat`, since `f` is a word operator). The
loop invariant (`BitInv`) is `AddInv`'s shape without a carry: the pool agrees with the entry
pool below `top`, the operands lie below it, and `pv` of the first `i` result limbs equals `bv`
of the first `i` operand limbs. Whether this limb-wise combine equals `Nat.land`/`Nat.lor`/
`Nat.xor` of the full values is left to `NatOpRefine.lean` (not written this round): a genuine
bitvector fact (splitting a number into base-`2^64` digits commutes with bitwise ops), not needed
for the L-side spec itself.

### Measurements (nightly-2026-10-20)

| function | Rust lines (`ron/nat.rs`) | L lines | spec + proof lines | `lean` time | automation |
|---|---:|---:|---:|---:|---|
| `nat_land`/`nat_lor`/`nat_xor` (+ loops, reusing `nat_limb`/`nat_trim`) | ~45 (`land`/`and_from`, `lor`/`or_from`, `xor`/`xor_from`) | ~45 | ~215 | 4.6 s | house form |
| `nat_cmp` (lane `nat2`; `beq`/`ble`/`blt` are tests of its code) | 52 (`cmp`, `cmp_from`, `beq`, `ble`, `blt`) | 16 | 137 | 6.8 s | house form; `finish (splits := 20)` in the loop; three pool lemmas by hand (`omega`) |
| `nat_sub` (+ `sub_borrow`; truncated; lane `nat2`) | 34 (`sub`, `sub_from`) | 25 | 117 | 7.7 s | house form, no hand step |
| `nat_shl` (`a <<< b`, `b` a slice; lane `nat2`) | 80 (`shift_left_nat`, `shift_left`, `shl_onto`, `shl_bits_from`, `push_zeros`, `push_zeros_nat`, `low_limb`) | 33 | 192 | 42 s | zero loop house form; shift loop and function `nat_mul`'s recipe (`simp` the frame, `grind (splits := 40)` per conjunct); word lemmas by hand |
| `nat_shr` (`a >>> b`, `b` a normalised slice; lane `nat2`) | 52 (`shift_right_nat`, `shift_right`, `shr_from`, `shr_bits_from`, `skip_index`) | 31 | 186 | 94 s | loop house form; function `nat_mul`'s recipe, 200k heartbeats per goal; word and division lemmas by hand |
| `nat_pow` (word exponent `< 2^25`; lane `nat2`) | 20 (`pow`, `one`) | 23 | 146 | 5.8 s | house form; `Grows.trans`, the exponent-bit and frame lemmas by hand |
| `nat_divmod` (`a / b`, `a % b`, `b` normalised; lane `nat2`) | 84 (`div_mod`, `div`, `modulo`, `dm_limbs`, `dm_bits`, `rev_copy_from`, `shl1_or`, `shl1_from`) | 94 | ~600 | 47 s (21 s wall) | four passes and three loops house form; function `nat_mul`'s recipe; the arithmetic lemmas by hand |
| `nat_gcd` (+ `gcd_step`; lane `nat2`) | 10 (`gcd`) | 13 | 120 | 1.9 s | house form; `Norm.of_agree` by hand |
| `natOpResult` arms `-` `pred` `*` `^` `/` `%` `gcd` `land` `lor` `xor` `shiftLeft` `shiftRight` `beq` `ble` under `ArenaR` (lane `nat2`) | – (`arena/core.rs` arms) | 50 (`topLit` 4, `nat_pred_lit` 9, `nat_pow_lit` 8, `nat_div_lit`/`nat_mod_lit`/`nat_gcd_lit` 15, `nat_beq_lit`/`nat_ble_lit` 14) | ~560 | 12.9 s (5.4 s wall) | house form throughout; `Grows.push1` by hand |

Whole file 307 lines. `lake build ConAgua` (full project) still green, 403 ms incremental.

### Findings

* **A combinator parameter must be a named constant, not `(· &&& ·)`.** The section notation
  elaborates sometimes to a lambda, sometimes to the point-free `HAnd.hAnd` (eta-equal, not
  syntactically equal); `grind`'s pattern matching saw both forms across the invariant and the
  code's own `BinOp.eval` unfolding and failed to connect them, even though the two are
  definitionally equal. Fix: `def andF : Word → Word → Word := fun a b => a &&& b` (ditto `orF`,
  `xorF`), used everywhere instead of the section, plus one `@[arena_grind =]` equation
  `andF a b = a &&& b` for the one place the code's own value needs to meet it.
* **The capacity bound is `≤`, not `<`, when there is no carry limb.** Copied `AddInv`'s
  `(s.loc 4).toNat + (s.loc 5).toNat < Pg.size` (strict, reserving the carry limb's slot) instead
  of `MulBase`'s `≤` (exact fit is fine): a loop entered at EXACTLY `top + n = size` could not
  establish the invariant even though the write is in bounds. One `finish` failure with a
  `size ≤ top + n` hypothesis alongside a `BitInv` goal needing `top + n ≤ size` was the tell.
* **An embedded `ite` in a postcondition's own subterm is fine; at the postcondition's own top
  level it is not** (the known gap, DESIGN.md "Known vcgen gaps"). `min`/`max` of the two
  operand lengths, written as `min`/`max`, made a loop-exit `finish` time out; the same value
  written as `if lb.toNat < la.toNat then lb.toNat else la.toNat` (matching the code's own `if`,
  as an ARGUMENT to `bv`, not the postcondition's own shape) went through at once. Suspect cause:
  `min`/`max` have no registered `grind` equation here (unlike `BinOp`/`Cmp`), so grind had
  nothing to unfold them with; the `ite` version is covered by the general `ite` handling that
  already works for arguments (only the top-level postcondition position is the known gap).
* **Forgetting the capacity check is a soundness bug, not a proof inconvenience.** The first
  draft of the three functions had no `if len(POOL.u64) - top < n { abort }` at all (unlike
  `nat_add`/`nat_mul`); nothing in the L type system catches a missing bounds check, only the
  `finish` failure trying to prove `PoolOK`'s consequences downstream caught it.

### `nat_cmp`/`nat_sub`: not landed, and why

`nat_cmp` (con-ron's `cmp`/`cmp_from`, comparing by length then by limb from the most significant
one down) was attempted and dropped after exceeding the lane's 45-minute budget by a wide margin.
The blocker: a hand-written recursive Lean model of `cmp_from` (`cmpFromN`), registered for
`grind` with a pattern keyed on an ABSTRACT loop counter `k` (`cmpFromN p oa ob k`, `0 < k` plus a
limb-comparison side condition), fires on EVERY `cmpFromN` term in sight — including the
unrelated "full-length" occurrence sitting next to the loop's "current position" occurrence in
the same invariant — and, because its own conclusion mentions a fresh `cmpFromN … (k - 1)` term,
re-fires on that, and the one after, with no concrete `k` to stop it: `finish` produced case
splits numbering in the hundreds of thousands before timing out. Scoping the pattern to `mergeW`
(a wrapper that also appears, narrower) cut it from unbounded to bounded but still wrong by a
wide margin once a genuine case split (which limb comparison holds) was needed; untangling it
needed a hand-written, non-`grind`-pattern step lemma that I did not finish deriving in budget.

**What it needs, for whoever picks it up:** state the loop invariant as the pool value comparison
directly (`cmpCode (pv Pg oa k) (pv Pg ob k)`, `cmpCode` a plain `Nat → Nat → Word`, no
recursion), using `pv_lt`/`wt_mono` (`ConAgua/Arena/LitRefine.lean`, general pool facts that
arguably belong in `Pool.lean` — a hook request for lane `exprops`, since `nat_cmp`'s loop needs
them and `Pool.lean` is theirs) for the "most significant limb decides" step; prove the per-step
transition as a HAND tactic (`rcases lt_trichotomy`, explicit `rw`s), not a registered `grind`
pattern, since the whole difficulty above is `grind`'s blind pattern search over a
decide-from-the-top recursion. `nat_sub` (con-ron's `sub`, truncated at `0`) needs `nat_cmp`'s
result (`Lt`/`Eq` ⇒ `0`, `Gt` ⇒ the ripple-borrow loop, the same shape as `nat_add`'s ripple
carry) first.

### `nat_pow`/`nat_shiftLeft`/`nat_shiftRight`: not attempted

Not started this round (time spent on bitwise ops and the `nat_cmp` attempt above). Notes for
whoever picks them up: `shift_left`/`shift_right` (`ron/nat.rs:351,427`) take a machine-word
amount (whole limbs pushed as zeros, then a sub-word shift `shl_bits_from`/`shr_bits_from` with
the `bits = 0` case special-cased, since shifting a 64-bit word by 64 is not `x >> 0`); the
`_nat`-amount wrappers (`shift_left_nat`/`shift_right_nat`) decode the shift amount from ANOTHER
pool slice first (con-ron's `to_u64`, failing over to "push `u64::MAX` zeros and recurse" for an
amount that does not fit a word, which an L pool simply runs out of room for — the existing
"fixed capacity, defined exhaustion" pattern handles it, no new idea needed). `nat_pow`
(`ron/nat.rs:547`, square-and-multiply, `e` from a word bounded by `2^24` the same way
`natOpResult` already enforces, `ron/nat.rs:541`) needs a bounded loop over the bits of `e`
(at most 24 iterations) calling `nat_mul` repeatedly, each call growing the pool; the per-call
`Grows` composes (`Grows` is transitive), but the invariant across iterations needs the loop's
own accumulator slice to be tracked by `(offset, length)` that moves each iteration, unlike every
other function here which is called once. Likely a full lane-day on its own.

### `sorry`s

None. The three bitwise functions are proved end to end against their word-level model; the
model's correctness against `Nat.land`/`Nat.lor`/`Nat.xor` is deferred (not a `sorry`, simply not
yet stated).

## The final theorem, and the audits behind it (2026-10-21, lane `final`)

Files: `ConAgua/Final/Twin.lean` (160 lines), `ConAgua/Final/Statement.lean` (200 lines). Both are
plain (non-`module`) files, since `Twin` imports `ConRonBridge`; they are in the lakefile's glob list.

### What landed

* `Twin.lean` restates the twin side of con-ron's `ConRon/Capstone.lean` without Aeneas:
  `SeqAccepts` (phase A, then one `checkPendingList` over all pending records from `s'.worker`,
  the x64 checker's single worker), `pooledAccepts_of_seq`, `TwinAccepts chunks` (the six stages
  from `AState.init EStore.empty`, at some pin list), `stages_frame` (con-ron's, with the stream
  named: `denoteDecls sE.store ds.toList = some (preparePrelude preC rc.decls).toList` and
  `ConLeche.Frontend.parseChunks chunks = .ok rc`), `twinAccepts_pure`, `twinAccepts_model`,
  `twinAccepts_no_False`. The proofs are con-ron's, unchanged except for the named stream; the
  two tier specs are discharged in place (`CoreSpec.of_core rfl`, `indSpec_of_bridge rfl hk`).
* `Statement.lean`: `ACCEPT`, `loadMem`, `PipelineRefines`, `HarnessCall`, `checker_x64_accepts`,
  `x64_model_exists`, `x64_no_False`, and `pipelineRefines_reject` (an always-rejecting `check`
  has `PipelineRefines`: the hypothesis is satisfiable). `#guard_msgs` checks both corollaries
  depend on `propext`, `Classical.choice`, `Quot.sound` only. Statements and the trusted base:
  `docs/ROADMAP.md` §3.
* The final theorem is parametric in the program `p`: the ROM (pins, prelude bytes) is part of
  `p`, and nothing about it is assumed. The proof of `checker_x64_accepts` is 20 lines: the shape
  of `natAddLit_x64`, with `PipelineRefines` in place of the run lemma.

### Decisions

* **Capacities are untrusted.** `PipelineRefines` quantifies over all array sizes, so `check` must
  check them at entry (`len8`/`len64`) and abort; the alternative, a size predicate the harness
  must satisfy, would put the sizes in the trusted base.
* **`N < 2^62`** is a premise of the theorem (the machine fuel in `rsi`), so the twin's `2^62`
  fuels can be matched by induction.
* **`ACCEPT = 0x414343455054`**, not a small number: a status word or a stale register never reads
  as accept.
* The corollaries are stated in con-leche's vocabulary (`parseChunks`, `preparePrelude`,
  `checkDeclsPure`, `Model`), with the pin list and the prelude existential.

### Audit: fuels (twin `vendor/con-ron/ConRon/Arena`, con-leche `vendor/con-leche`)

| fuel | where (value) | decrements | at zero | decision |
|---|---|---|---|---|
| `checkFuel` | `Core.lean:3616` (2^62) | one per knot level (`coreKnot` 3536–3608, `CoreIO.lean:33`) | `.internal` throw | not counted; `F ≥ n` |
| `whnfCoreLoopFuel`, `whnfLoopFuel`, `defeqLoopFuel` | `Core.lean:2185`, `2402`, `3263` (2^62) | per loop step | `.internal` throw | not counted |
| `lamsFuel` | `Core.lean:3034` (2^62) | per λ pair (`defeqLams` 3051) | falls back to `defeqLamsInner` | not counted (unreachable) |
| `peelFuel` | `Core.lean:2478` (2^24) | per binder (`inferLams` 2507, `inferPis` 2555, `defeqPeel` 2992) | hands the rest to the knot | **L counter** |
| `coreWalkFuel` | `Core.lean:87` (4·10^9) | per recursive call of every store walk (ExprOps, Canon, Promote, PropRead, Positivity, …) | `.internal` throw | **L counter** (no rank argument needed) |
| `storeFuel` | `Frontend/ExportC.lean:84` (`nodeCount + 1`) | per Π node | throw | **L counter** |
| `hoistClosure` | `NatOpGround.lean:308` (`ds.size`) | per record marked | throw | **L counter** |
| `whnfWalkFuel` | `Inductives/Positivity.lean:306` (`depth e + 1024`) | per `nestPos` call (1048) | `.notImplemented` decline, reachable | **L counter**, same value |
| `Level.defaultFuel` | con-leche `Kernel/Level.lean:142` (10^4) | per `leqCore` call, fresh per `leq` | **`none`** | **L counter**, three-way result |
| `unwrapIdDefs` | `PropRead.lean:155,163` (4) | per wrapper | **returns the term** | **L counter** |
| `idxCap` | `Handle.lean:98` (2^27 per constructor and tier) | store size | `.native` throw | L abort at the same size |

`none` from a level comparison is an answer at `Core.lean:1651,1656,2720,2724,2906`,
`BlockInstall.lean:300`, `BlockParts.lean:144,362`, `SumInstall.lean:109`, `RecCheck.lean:218`,
`ExportC.lean:345`; elsewhere it goes through `liftFueled` (`Core.lean:312`) to a decline.

### Audit: recovery points

One: `orElseAttempt` (`CheckerBase.lean:102`), called only from `checkDivModPinLoop`
(`DeclCheck.lean:613–631`). A throw other than `.native` inside `checkDivModPinAt` (a defeq at
`checkFuel` and the certificates' infer/defeq) resumes from the pre-attempt state with the next
variant; `.ok false` continues from the post-attempt state; the guards (619) and `divModEnvGuard`
run outside the attempt. No variant matching throws `.notImplemented` (decline, exit 2). All other
error matches (`Checker.lean:228–236, 247, 272–278, 286–291`, the frontend's `atLine` paths,
`Main.lean:262–297`) pass the error to a non-accept verdict. No thrown error is turned into
`false`/`none` anywhere else. Decision: L recovers nowhere (ROADMAP §3 (c)).

### Audit: hash bits and eager nesting

* Hash reads: `Store.lean:459–463` (names), `620–631` (levels), `736–741` (level lists),
  `1021–1031`, `1215–1255` (expressions): each feeds only a parent's hash. `bvarOfData`,
  `fvarOfData`, `lpOfData` read `w % 2^32` (`packData`, con-leche `Kernel/Expr.lean:162–178`).
  Handles hash by their word (`Handle.lean:88`). No `Std.HashMap` is iterated. `Bridge/` never
  names `mixHash`. Decision: no patch; relate `w % 2^32`.
* Eager nesting: the only entry is `defeqArg` (`Core.lean:2620`) from full-grade `inferApp`; the
  eager knot re-enters through `defeqLamsInner` (3040), `etaCert` (1617), `iotaCertsFullAux`
  (1303), all gated by `verifiedChecks`, which `.verifiedEager` keeps. Depth is unbounded in
  verified mode, 1 in trusted modes. `putModeMemos` restores the six tables wholesale (eager
  entries dropped); the other eight caches keep what the eager run added. Decision: a bank stack
  (ROADMAP §2 item 3).

### Measurements

`lake build ConAgua.Final.Statement` with everything else built: `Twin` and `Statement` under
1 s each (the proofs are compositions of existing lemmas).

### `sorry`s

None. `PipelineRefines` is a hypothesis of the theorems.

## The memo library, the view layer, derived ranges, `liftLooseBVars` and `instantiate1` (2026-10-21, lane `exprops`)

Files: `ConAgua/Arena/{MemoLib,MemoLibRel}.lean` (replace `Memo`/`MemoRel`), `{View,ViewL}.lean`,
`{ExprMk,DerRel}.lean`, `{Lift,LiftSpec,LiftRefine,LiftBench}.lean`,
`{Inst1,Inst1Spec,Inst1Refine,Inst1Bench}.lean`, `scripts/inst1_from_lift.py`; changed `ArenaRel`, `Frame`,
`Walk`, `WalkRefine`. No `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`.
`ArenaRel.lean` is maintained by hand from now on (no generator; see lane `tables2` above).

### Layout and the extension point

| arrays | `CTL` words | contents |
|---|---|---|
| 41 `LMEMO` | 42 (stamp − 1), 43 (count) | the `liftC` memo (`lfSch`), field `ArenaR.lmemo` |
| 42‥46 `ADER`, `LADER`, `FADER`, `LEDER`, `PJDER` | – | derived bvar ranges of `app`, `lam`, `forallE`, `letE`, `proj` (`DerR`) |
| 47 `IMEMO` | 44, 45 | the `inst1C` memo (`imSch`), field `ArenaR.imemo` |
| 48‥63 | 46‥63 | reserved for this lane |
| ≥ 64 | ≥ 64 | free for other lanes: `ArenaR.frame_ext` (stable), `arenaR_init` takes ≥ 64 arrays and a `CTL` of ≥ 64 words |

`ArenaR.frame_above` (arrays 42‥46, `CTL` ≥ 64) and `frame_ext` are proved once from `apart_hi`
(`Apart` by bounds) with `arena_build … using …` (the frame tactic is now a parameter).

### The memo library (`MemoLib.lean`, `MemoLibRel.lean`)

A memo is a schema `MemoSch` (slot array, `CTL` index of the stamp); four words per slot: stamp,
two key words, value. The L code is **generic in the schema**: `memoFindG S`, `memoPutG S`,
`memoClearG S` are Lean functions producing L functions (`S.arr.u64[…]`, `CTL.u64[⟪S.cs⟫]`), and
their `vcgen` specs are proved once for a variable `S` — at the first attempt (`vcgen` sees through
a symbolic array id). `set` is `find; put` with the probe result passed in (L calls by name, so a
generic `put` cannot call a generic `find`); a walk probes again after its recursion. The relation
`MemoRG S K dv m mp` relates the memo to `Std.HashMap κ ν` through a key codec `K` (two words per
key, `dk`/`ek` and one law `ek_dk`) and a value decoder; lemmas `memoRG_hit/miss/set/clear/frame/
zero`, all generic. An instance is a schema line and a codec (`bmKey`, `lfKey`: 6 lines each).

| file | lines (code) | `lean` wall / user |
|---|---:|---|
| `MemoLib.lean` (L 3 functions, 33 lines; models, specs) | 280 (189) | 4.6 s / 6.1 s |
| `MemoLibRel.lean` | 543 (456) | 1.4 s / 2.6 s |
| before: `Memo.lean` + `MemoRel.lean` (one table, by hand) | 267 + 428 | 1.4 s + 1.3 s |

`bvarBC` was ported (`bm_find`/`bm_put`/`bm_clear` = the library at `⟨24, 24⟩`): the walk's specs
went through unchanged in shape; `WalkRefine` changed in eight lines. The compiled walk
(`harness/walk.c`, `perf stat -e instructions:u`): 82.3 M per 10^5 `app` nodes (72.3 M before),
823.1 M per 10^6 (723.1 M): the second probe and the extra call cost 14 %. `check-asm.sh`: walk
6439 instructions, all matching.

### The view layer (`View.lean`, `ViewL.lean`)

The arena side every walk shares: handle decoding, and **one view lemma per tag** (`view_app`: under
`ArenaR`, `viewOK m h 4` and tag 4, `a.store.view (decE h) = some (.app (decE f) (decE a))` with
`f`, `a` the record's words, both below `2^32`). `ViewL.lean` has the L side (`tierW`, `idxW`,
`viewOK`, branch-free `maxW`, `predW`, `satSuccW`, `satPredW`). `WalkRefine.lean` now uses them:
565 → 372 lines (refinement per walk L line 10 → 6.3).

### Derived ranges: a finding, and `DerR` (`ExprMk.lean`, `DerRel.lean`)

**`liftLooseBVarsGo` (and `instantiate1Go`, `instantiateListGo`, `abstract*`) read the derived word
before anything else**: `bvarOfData (derived h) < satRange && … ≤ c` returns `h` unwalked. This is
not denotation-level: the cut-off and the walked paths leave different memos and, on a scratch
node with persistent children, may return different handles. So L must know the range field of
`derived h` exactly; `ArenaR` had no derived columns (ROADMAP §1, phase 0 "missing"). Done here
for the range field only (the hash is opaque, ROADMAP §2 item 10):

* the five compound tables keep the range in L (`XDER[2 i + t]`); a leaf's range is a function of
  its record (`satSucc i` for `bvar`, else `0`);
* `der_b(h)` (15 L lines) returns it, including the arena's `0` for a handle that does not view;
* `mk_app`, `mk_lam`, `mk_forall`, `mk_let`, `mk_proj` (59 L lines): children's ranges, `intern_*`,
  and on a new node (the table's count sum changed) the range at the new index. **The compound
  `intern_*` are internal from now on**; a node interned by them directly has no range;
* `DerR m a` (one `DerT2` per expression table) and `ArenaD := ArenaR ∧ DerR`; `derBW_ok`
  (`der_b` is `bvarOfData (a.store.derived (decE h))`), `mkX_ok` (each `mk_*` refines `internE`
  under `ArenaD`; one generic lemma `derMk` does the tail for all five), `internBVar_D`,
  `DerR.frameM`/`of_store`, `arenaD_init`.

| file | lines (code) | `lean` wall / user |
|---|---:|---|
| `ExprMk.lean` (L 74 lines, models, specs) | 342 (254) | 7.1 s / 19.7 s |
| `DerRel.lean` | 938 (793) | 1.1 s / 2.8 s |

### `liftLooseBVars` (`Lift.lean`, `LiftSpec.lean`, `LiftRefine.lean`)

`lift_go(h, c, k)` is the twin's dispatcher (cut-off by `der_b`, the view checks, `bvar` via
`intern_bvar(i + k)`, leaves return `h`), the five arms `lift_app` … `lift_proj` its `liftArm*`
(memo probe on `(h, c)`, children — bodies at `c + 1` —, `mk_*`, probe again, put),
`lift_entry(h, k, c)` is `liftLooseBVarsFast`. The models are mutual on fuel; the guarded
equations name first-order continuations. Theorems: `liftGo_spec`, `liftEntry_spec`
(`vcgen` + `finish`), `liftOK` (by induction on fuel, `LGoOK n ∧ LArmOK n` for every arena fuel
`F ≥ n`), `liftEntry_refines` (the triple with `AM.ok`/`AM.st`/`AM.res` under `ArenaD`) and
`liftEntry_run`. `LiftBench.lean`: four `#guard`s in the interpreter (lift equals the expected
term's handle, the cut-off returns the same handle).

| | Rust lines | L lines | proof lines (code) | `lean` wall / user |
|---|---:|---:|---|---|
| `lift_loose_bvars_go` + `_fast` | 142 | 93 (`lift_go` 24, arms 65, entry 4) | `Lift.lean` 478, `LiftSpec.lean` 131 | 26.9 s / 27.3 s, 3.1 s / 10.7 s |
| refinement | – | – | `LiftRefine.lean` **444**, i.e. **4.8 per L line** | 1.1 s / 1.9 s |

L/Rust is 0.65. The refinement is at the target (≤ 5; the walk was 10): the dispatcher is one
`by_cases` per tag with one view lemma each, an arm is `probe_ok` (hit/miss), the children (the
induction hypothesis), and `tail_ok` (`mk_*_ok` and the memo set). Not counted: the derived-range
infrastructure (`ExprMk`, `DerRel`), which every walk with a cut-off reuses.

### `instantiate1` on the same scaffolding (`Inst1.lean`, `Inst1Spec.lean`, `Inst1Refine.lean`)

`instantiate1Go`/`instantiate1Fast`: the derived-range cut-off, then the **tag** (leaves and
unknown tags return `h` unread), the `bvar` arm inline (`i = d`: `v`, `i > d`: `intern_bvar(i - 1)`),
five memoized arms on `inst1C` (`imSch`, a new `MemoSch` line and an `ArenaR` field) that probe
**before** viewing (the twin's order; the view checks follow the probe), the binders sharing the
twin's `instantiate1ArmBind`. New library pieces: the store's projections per tag
(`viewApp_ok`, `viewBind_lam`, … in `View.lean`, 85 lines). `Inst1.lean` and `Inst1Spec.lean`
were derived from `Lift.lean`/`LiftSpec.lean` by `scripts/inst1_from_lift.py` (renames, the view
checks after the probe, hand-written dispatcher and program in `scripts/inst1_templates.py`;
`--check` reproduces the committed files); they are maintained by hand from now on.

| | Rust lines | L lines | proof lines (code) | `lean` wall / user |
|---|---:|---:|---|---|
| `instantiate1_go` + `_fast` | ≈ 155 | 98 (`inst_go` 19, arms 75, entry 4) | `Inst1.lean` 446, `Inst1Spec.lean` 131 | 7.1 s / 7.5 s, 5.9 s / 20.9 s |
| refinement | – | – | `Inst1Refine.lean` **429**, **4.4 per L line** | 1.0 s / 2.0 s |

All specs went through at the first attempt with `finish (gen := 20) [viewOK, tierW, idxW]`; the
refinement needed only `simp` set fixes. The probe/tail helpers (`iprobe_ok`, `itail_ok`) are
copies of lift's for the other memo (60 lines); a version generic in the memo accessor would
remove them for the next four walks.

### Findings

* **`vcgen` with a symbolic array id works**: the memo library's L code is a Lean function of the
  schema and its specs are proved once. The same would make the per-table store L code generic
  (lane `storelib` judged it untried).
* **`finish` needs `(gen := 20)`** where three callee posts feed one model (`mk_let`, the lift arms);
  the default failed with no hint. Separately, a missing `[tierW, idxW]` made `finish` fail
  slowly (45 s per lemma); with it the lift arms take about 2 s each.
* **Continuations given as `fun` defeat `grind`'s matching** (it equated two lambdas and stopped);
  first-order continuations (`appK₁ n h c k aw`, …) as in lane `walk` work. A small example does
  not reproduce it.
* `omega` and `ArrId` (`abbrev … := Nat`): `docs/gaps/omega-nat-synonym-hyp.lean` again;
  `Nat.lt_of_le_of_lt`/`decide` instead.

### Not done

* `instantiateListGo`, `abstract1Go`, `instantiate1LiftGo`, `hasLooseBVar`: the same scaffolding
  (`DerR`, more `MemoSch` lines, `mk_*`); `instantiate1Lift` also needs `bvarBC` reads.
* `DerR` for the other leaf internings (`intern_fvar`, `intern_sort`, `intern_const`, `intern_lit`,
  incl. `natAddLit_refinesA`): each is `internBVar_D`'s proof with `zP` (range `0`).
* Compiled benchmarks of `lift_entry`/`inst_entry` (the programs are `liftProg`, `instProg`; not
  emitted).

### `sorry`s

None.

## The first records into the store: names and levels (2026-10-21, lane `front`)

Files: `ConAgua/Front/{Fields,FieldsLink}.lean` (the scanner's fields), `ConAgua/Front/{Apply,
StateDR}.lean` (the id tables and `parseNameEntryD`/`parseLevelEntryD`, written by a subagent),
`ConAgua/Front/{Line,LineRefine}.lean` (one line, end to end), `scripts/stageb/` (housekeeping
below). No `sorry`; `frontLine_refines` and `frontInit_refines` use only `propext`,
`Classical.choice`, `Quot.sound`. Stage B's files are unchanged.

**Housekeeping.** Stage B's generators are committed as `scripts/stageb/{parserec,genrec,genkey}.py`
(repo-relative paths; `scripts/stageb/README` says how to run them). `Records.lean`/`Key.lean` were
edited after generation (the six `key_at` groups and the hypothesis lists that follow, headers,
heartbeats), so they are hand-maintained; a rerun is a starting point to diff against.

### The fields: a second pass over an accepted line

The validator stays as it is (`scan_line`, all its theorems). A name or level line is read a second
time by `rec_line_loop(i)` (`Fields.lean`), which returns five words `(pl, idx, a, c, d)`: the kind
(`1` name `str`, `2` name `num`, `3`‥`6` `succ`/`max`/`imax`/`param`, `7` the header, `0` anything
else), the index, and the fields (for a `str` name: `pre` and the string body's byte range
`[c, d)`). The pass trusts the validator: no `seen` masks, no alternation, no key-set check, and it
stops with `pl = 0` at any other payload key. Numbers are read by `read_nat` (con-leche's
`readNat64` on words); one of more than 18 digits reads as `NONE = 2^64 - 1`, which the apply step
refuses (`readNatAt` is `readNat64` for at most 18 digits, so the link is definitional).

`FieldsLink.lean` relates each loop to con-leche's on its `ok` path only: `recLine_link`: if
`scanLineLoop b i w ik idx pl = .ok r e` and the words so far are related to `idx`/`pl`
(`ItemR`, `PlR`), then `rec_line_loop`'s result, if `pl ≠ 0`, is related to `r` (`RecR`). The error
branches of con-leche's loops are discharged by the `ok` hypothesis, so the link is one induction
per loop (`pair_link`, `strRec_link`, `numRec_link`, `recLine_link`), with no `objN`-style generic
model. A word read for a number `n` satisfies `ItemR x n := x ≠ NONE → x.toNat = n`; a string body
`StrOK b vs ve s := NoEsc b vs ve → String.fromUTF8? (b.extract vs ve) = some s` (an escaped string
is refused by the apply step, `has_escape`).

### The id tables and the apply step (`Apply.lean`, `StateDR.lean`)

`StateD`'s `IdTable`s are two dense word arrays, `NID` (64) and `LID` (65), above `ArenaR`'s
extension point: entry `i` is the
handle word `+ 1`, `0` unset. An id at or past the array's end aborts where the twin would use its
sparse overflow. `front_init`, `apply_nstr(i, pre, o, l)`, `apply_nnum(i, pre, x)`,
`apply_level(i, k, a, c)` intern through `intern_nanon`/`zero`/`nstr`/`nnum`/`succ`/`max`/
`imax`/`param` and guard the result `< 2^32` (so table entries can be passed on as handles without
a lemma about the store's results); `str_put(vs, ve)` copies input bytes to the pool top (one byte
per word, the name `str` table's key). `StateDR m st` (`TblR` per table: `get?` is the decoded
entry, entries `≤ 2^32`, sizes `< 2^63`); `ArenaR` is kept across writes to `NID`/`LID` by the
extension point's frame (`ArenaR.frame_ext`, via `ArenaR.frameT`). Each L function's spec is an
equation about a named `Option Mem` model (`applyNStrW`, …), and the refinement is proved on the model
(`applyNStrW_refines`, `applyNNumW_refines`, `applyLevelW_refines`, `frontInitW_refines`).

### One line end to end (`Line.lean`, `LineRefine.lean`)

`front_line(i)` = `scan_line(i)`; blank line → `(1, next)`; else `rec_line_loop` and `apply_rec`
(which dispatches on `pl`; `apply_str` does `has_escape`, `str_put`, `apply_nstr`). Expression and
declaration lines abort for now. `frontLine_refines`: under `ArenaR s₀.mem a₀`, `StateDR s₀.mem st`
and the buffer `b` in `IN`, if `front_line(i)` returns `(1, nx)` then `LineStep b i nx st a₀ m'`:
`scanLineFwd b i = .ok r q` with `q` the word `nx`, `applyLine st r` succeeds with `.inl st'`, and
`ArenaR m' (AM.st …)`, `StateDR m' st'`. The record `r` is con-leche's, so Stage B's links to
`scanLineFwd` apply unchanged.

### Measurements (`lake env lean`, one run)

| file | lines | L lines | user |
|---|---:|---:|---:|
| `Fields.lean` (L, models, `vcgen` specs) | 762 | 115 | 35.5 s |
| `FieldsLink.lean` | 809 | | 8.8 s |
| `Apply.lean` (L, models, specs, `#guard`s) | 503 | 77 | 4.8 s |
| `StateDR.lean` | 734 | | 2.6 s |
| `Line.lean` (L, model, specs) | 255 | 30 | 3.1 s |
| `LineRefine.lean` | 299 | | 1.2 s |

Every `vcgen` spec is `vcgen` + `finish`. Rust: `export_c.rs`'s name/level entries and the id
tables (~150 lines) plus the record values of `scan_fast.rs`'s name/level paths (~200).

### Findings

* **A second pass instead of value-carrying validators.** Rewriting the validator's loops to carry
  values would have meant new models and new links for all of them; the second pass needs links
  only on con-leche's `ok` path, where every error branch closes by `cases h`. The cost is reading
  name/level lines twice (they are short).
* **A monolithic dispatcher did not get through `finish`** (the first `front_line`, ~20 branches
  with seven calls): split into `front_line`/`apply_rec`/`apply_str`, each spec went through. Two
  things the split exposed: a callee spec needs `LocEq s' s₀` in its post for the caller's later
  reads of its own locals; and a callee whose return words are not fixed by its post (a list
  from an `Option` model) cannot be assigned to locals that the caller returns: return a constant
  and let the caller build the result.
* **Pass a callee spec without its state argument** to `vcgen` (`applyRec_spec … n`, not
  `… n s₀ hm`): an explicit `s₀` fixes the call state, which is never `s₀` itself.
* `rw [f]` with a definition's equation lemma for an overlapping `match` (`scanLineLoop`) produces
  side goals; `rw [f.eq_def]` does not.

### What an expression record will need

Binder data (`lam`/`forallE` names and binder info are dropped by con-leche, so nothing), the
`lit` store's `strVal` contents (a second `intern_lit` entry over the pool bytes, as `nstr`), the
derived columns (`derOfView`: the loose-bvar range and flags, and the opaque hash, ROADMAP §2
item 10), level lists for `const` (`intern_ls` over handle words `str_put`-like into the pool),
and natural-number literals (the limb-pool decimal parse). The fields pass extends by one arm per
expression key, with `ok`-path links of the same shape.

### Requests

* Strings with escapes abort; `unescape` into the pool (the `\u` arms need UTF-8 encoding
  against `String.utf8EncodeChar`) is the next piece for real files.

### `sorry`s

None.

## Limb-pool `Nat` ops, round 2: compare, sub, shifts, pow, div/mod, the arms (2026-10-21, lane `nat2`)

Files: `ConAgua/Arena/NatGrindAttr.lean`, `NatCmp.lean`, `NatSub.lean`, `NatShl.lean`, `NatShr.lean`, `NatPow.lean`, `NatDiv.lean`, `NatBitsNat.lean`, `NatGcd.lean`, `NatArms.lean`. Per-op numbers are in the lane `nat`
table above (`lean` user time of the file, one run).

### `nat_cmp`: a non-recursive model

`nat_cmp(oa, la, ob, lb)` returns con-ron's `Cmp` as a word (`0` `Lt`, `1` `Eq`, `2` `Gt`): the
lengths first (normalised operands), then the limbs from the top down. The spec is
`r = cmpW A B` with `cmpW a b = if a < b then 0 else if a = b then 1 else 2`, a plain function of
the two values, and the loop invariant is one linear equation: the limbs at `k` and above agree,
`pv a la + pv b k = pv b la + pv a k`. No model of `cmp_from` exists, so nothing recursive
reaches `grind`. The step "the top limb decides" is `pv_succ_lt`: from the program's own
comparison `p[ia] < p[ib]` (with `ia + 1 = oa + k`) to `pv p oa k < pv p ob k`, with the
multi-pattern `p[ia] < p[ib], pv p oa k, pv p ob k`. Its conclusion relates two terms that are
already there, so instantiation stops (28 instances in the loop's worst goal; lane `nat`'s
recursive model produced hundreds of thousands of case splits). The loop needs
`finish (splits := 20)`: each `pv_succ`/`pv_succ_lt` instance's index condition is a split.
`beq`/`ble`/`blt` are tests of the code (`cmpW_eq_one`, `cmpW_eq_two`, … as `grind` equations),
not functions.

* **A separate attribute for comparison facts.** `pv_lt_wt` (`pv p o k < wt k`) has the pattern
  `pv p o k` and fires on every prefix value; with it in `arena_grind`, `nat_sub`'s loop (which
  never compares) timed out. It and `pv_succ_lt`, `cmpW_*` are in `natcmp_grind`
  (`NatGrindAttr.lean`), which a proof adds to its `sym only [...]` list when it needs them.
  A second one, `natop_grind`, holds the broad lemmas of the shifts, `pow` and the division
  (`pv_one`, `pv_set_one`, `shr_val`, `pv_cons`, the `sh` facts, …): lemmas registered in
  `arena_grind` reach every later file, and in `nat_divmod`'s limb loop `shr_val` alone made 336
  useless instances (`nat_shr`'s quotient lemma, matching any `x / (S * wt w)`).
* `LitRefine.lean` has the same fact as `pv_lt` (and `pv_ge`, `pv_len`), but it is not a
  `module`, so module files cannot import it; `NatCmp.lean` proves its own `pv_lt_wt`,
  `pv_len_lt`.

### `nat_sub`: the final borrow decides

con-ron's `sub` compares first and runs the ripple borrow only when `a > b`. `nat_sub` runs the
ripple borrow over `max la lb` limbs (`nat_add`'s loop, `nat_limb` for both operands,
`sub_borrow` for the two `overflowing_sub`s) and lets the borrow out of the top limb decide: the
loop's equation is `R + B = A + c · wt n`, so `c = 0` gives `R = A - B` and `c = 1` gives
`A < B` (with `R < wt n`), and the result is `0`. It needs neither `nat_cmp` nor normalised
inputs. Two details: `bit_mul_wt` (`c.toNat * wt k = wt k` for a nonzero bit `c`, pattern
`c.toNat * wt k`), because the linear solver knows `c = 1` but the product stays an atom; and
both exits end with the same `CTL[0] := top + n` (`if c != 0 { n := 0 } else { n := trim }`):
a `return 0` that leaves `CTL[0]` alone fails `Frame POOL (m.set64 CTL 0 (top + 0)) m'`,
because `grind` does not see that writing the top's own value back changes nothing.

### `nat_shl`: a word amount, a branch-free bit shift

The amount is a slice `b`. With `a ≠ 0`, an amount of two or more limbs cannot fit any pool
(con-ron pushes `u64::MAX` zero limbs and runs out of memory), so it is an `abort`; otherwise
`k = b[0]` (or `0`), `k >> 6` zero limbs (`shlZero`), then one pass over `a` with a carry
(`shlLoop`), the carry limb, `nat_trim`. The bit shift needs no `s = 0` case:
`c' = (x >> 1) >> (63 - s)` is `x >> (64 - s)` for `s ≥ 1` and `0` for `s = 0`.

* **Digit equation over a named power.** `shl_split`:
  `((x << s) | c) + c' · 2^64 = x · sh s + c` for `c < sh s`, with `sh s = 2^s` named (an atom to
  the ring solver, as `wt`). Its proof is by hand (`Nat.shiftLeft_add_eq_or_of_lt`: the `|` is a
  `+` because the low `s` bits of `x << s` are zero).
* **The loop invariant uses `wt w * wt i`, not `wt (w + i)`** (`ShlInv`, `nat_mul`'s `ColInv`
  shape): `wt_add`'s pattern `wt k, wt i * wt j` then joins it with the `wt (w + i)` that
  `pv_set_succ` produces.
* **The amount.** `shamt`: `2^k = sh (k & 63) · wt (k >> 6)`, pattern `2 ^ k.toNat`; and
  `pv_one` (`pv p o 1 = p[o]`, pattern `pv p o 1, p[o]`): `pv_succ` alone needs a `pv p o 0`
  term, which the goal does not have, and without it the final `grind` ran out of heartbeats.
* The function proof is 35 of the file's 42 s (`maxHeartbeats 1000000`).

### `nat_shr`: the loop runs over the shifted slice

An amount of two or more limbs (`b` normalised) is at least `2^64`, so `a >>> b = 0` whenever
`la < 2^57` (every pool); `la ≥ 2^57` is an `abort`. Otherwise `k = b[0]`; if `w = k >> 6 ≥ la`
the result is `0`, else one pass over the slice `(oa + w, la - w)` (con-ron's `skip_index`
becomes `oa := oa + w`), limb `i` being `(x >> s) | ((y << 1) << (63 - s))`, branch-free as in
`nat_shl`, with `y` limb `i + 1` read by `nat_limb` (zero past the end) and carried into the next
iteration as `x`.

* **No division and no `w` in the loop.** `ShrInv`: `R_i · sh s + lowb x₀ s = xv i + lowb x_i s ·
  wt i`, `lowb x s = x % 2^s` named. Its digit equation `shr_split`:
  `out · sh s + lowb x s = x + lowb y s · 2^64`. The loop went through in the house form.
* **The division and the skipped limbs are three lemmas with patterns on the quotient**
  (`pv A / (S * wt w)` after `shamt` rewrites `2^k`): `shr_val` (pattern also `pv P o l, R * S`,
  binding the loop's result; `pv_append` splits off the skipped limbs), `shr_big_w`
  (`w ≥ la`), `shr_big_b` (two-limb amount, with `Norm`).
* **Cost.** The function proof is 90 of the file's 94 s: `nat_mul`'s recipe, but one
  `maxHeartbeats` for the whole theorem ran out (1M); with `set_option maxHeartbeats 200000 in
  grind …` per goal (and none for the theorem) every goal passes. The house form
  (`finish (gen := 25)`) fails on two goals (splits). Not tuned further.

### `nat_pow`: an accumulator that moves

Square-and-multiply from bit 24 down (25 iterations whatever `e`; squaring `1` is one limb),
each product a call of `nat_mul`, which appends it at the top. The accumulator is the last
product, so `nat_pow` returns `(o, l)` (two results) and the intermediate products stay below
the top as garbage, like con-ron's dropped `Vec`s but never freed. The loop invariant `PowInv`
names the entry memory `m₀` and keeps `Grows m₀ s.mem` (`Grows.trans`, pattern
`Grows m m', Grows m' m''`), `a`'s value (below `m₀`'s top, so `Agree.pv` carries it across each
call) and `pv o l = a ^ (e >> j)`. The step is `pow_step1`/`pow_step0`
(`a ^ (e >> j') = a^(e >> j) · a^(e >> j) · a` or without the `a`, keyed on
`(e >> j') & 1`); their patterns bind both powers, which are in the goal, so they do not chain.
Three small `grind` facts were needed for the entry, each found from the failing conjunct under
`nat_mul`'s recipe and then the house form went through: `pv_set_one`/`Norm.set_one` (a one-limb
slice just written; `pv_set_succ` needs a `pv p o 0` term), stated with `l = 1` as a hypothesis
because the length is `UInt64.toNat 1`, not the literal; `pow_shr25` (`a ^ (e >> 25) = 1`; the
equation `(e >> 25).toNat = 0` alone does not reach the power); `shr_of_zero` for the exit.

### `nat_divmod`: restoring shift-subtract, in place

Knuth D needs a 128-by-64 division for its quotient estimate, which L does not have; con-ron
itself does shift-subtract (`dm_limbs`/`dm_bits`), so `nat_divmod` does too, but in place:
con-ron allocates a new remainder per bit (`shl1_or`, `sub`), which in an append-only pool would
leave `64 · la` dead remainders behind. The quotient's `la` limbs and the remainder's `lb + 1`
limbs are reserved above the top; per bit, `div_step(r, n, ob, lb, bit)` runs three in-place
passes over the remainder (`div_shl1`: `R := 2R + bit`; `div_sub`: `R := R - b` with a borrow;
`div_add`, only on a borrow: `R := R + b`, the restore) and returns the quotient bit. `a / 0 = 0`,
`a % 0 = a` (the remainder is then `a`'s own slice, trimmed). Results: `(oq, lq, or, lr)`.

* **The in-place frame is `Off p q o n`** (the pools agree off `[o, o + n)`), with `grind`
  patterns for writing the next limb (`Off.set`), reading past the changed prefix (`Off.get`),
  slices below the region (`Off.pv_below`), `Off.trans` and `Agree.of_off`. The three passes went
  through in the house form at the first attempt, as did `div_step` (three calls, an `if`).
* **The bit loop's body had to be one call.** With the three calls and the `if` inline, the
  house form exhausted its splits and `nat_mul`'s recipe lost the frames (`and_intros` unfolds
  `Frame` into components). With `div_step` it is straight-line (the arena lane's finding again).
* **The bit loop's post is relative to its entry**: (`DBitPost`) `R₀ · 2^j₀ + x + q₀ · 2^j₀ · b = q · b + R +
  (x / 2^j₀) · 2^j₀`, with no other limb of `a` or of the quotient in it. The first version
  carried the whole dividend and quotient prefix through the bit loop (degree-3 terms
  `QU · 2^(64 - j) · b`) and failed; the relative post went through in the house form.
* **Pointer locals instead of index arithmetic.** The limb loop first read `a[oa + i - 1]` and
  wrote `q[top + i - 1]`; its invariant's `pv a (oa + i) (la - i)` then meets the read
  `a[(oa + i - 1).toNat]` only through linear arithmetic, which `grind` turns into case splits
  (theory combination); `pv_cons` with a free read index had 1759 instances. With locals `pa`,
  `pq` decremented before the read and the write, the read index and the slice offset are the same
  term, `pv_cons` (`pv p o k', pv p o' k, p[o]`) binds directly, and the loop went through.
  `pv_set_cons_off` prepends the written quotient limb to a slice read in the pool *before* the
  bit loop's in-place passes (pattern includes the `Off` fact), because the slice in the current
  pool is not a term yet. The exit (`i = la`, so `pa = oa`) is `pv_exit`, keyed on the loop
  condition `i < la`.
* **The quotient and the remainder** are `div_of_bounds`/`mod_of_bounds` (`Q · B ≤ A < Q · B + B`,
  pattern `A / B, Q · B`), in `natcmp_grind`: in `arena_grind` they fired on the bit loop's
  `x / 2^j` terms and broke it.
* **`maxHeartbeats`.** The function proof is `nat_mul`'s recipe with 400k heartbeats per goal and
  none for the theorem (as `nat_shr`).

### `land`/`lor`/`xor` are the `Nat` operations (`NatBitsNat.lean`)

Lane `nat` proved `nat_land`/`nat_lor`/`nat_xor` against `bv f`, the limb-wise combine, and left
"`bv` is `Nat.land`" open. `bitwise_split`: for an operation `op` given by its bits (`BitOp op g`:
bit `i` of `op x y` is `g (bit i of x) (bit i of y)`, `g false false = false`) and `x, y < 2^64`,
`op (x + 2^64 X) (y + 2^64 Y) = op x y + 2^64 · op X Y` (by `Nat.testBit`); by induction over the
limbs `op (xv a k + wt k · X) (xv b k + wt k · Y) = bv f … k + wt k · op X Y`; with
`pv a = xv a k + wt k · pv (a + k) (la - k)` the high parts vanish at the loop's length
(`land_bv`, `lor_bv`, `xor_bv`). 129 lines, by hand, 0.6 s. The operation is a parameter with
its bit lemma, not `Nat.bitwise g`: in a `module`, `Nat.land`'s body (`bitwise and`) is not
visible, only the public `Nat.testBit_and`/`_or`/`_xor`.

### `nat_gcd`: Euclid over `nat_divmod`

`while la != 0 { (oa, la, ob, lb) := call gcd_step(oa, la, ob, lb) }`, `gcd_step` returning
`(b % a, a)` (`nat_divmod`'s remainder slice and `a`'s). The invariant is `nat_pow`'s shape (two
moving slices, `Grows` from the entry memory, `Nat.gcd a b = G`); the step is
`Nat.gcd (b % a) a = Nat.gcd a b` (`gcd_step`, pattern on the left side), the exit
`gcd_zero_len` (`la = 0`). With the divmod call and four `setLoc`s inline in the loop body, the
house form hit `grind`'s term generation limit and `nat_mul`'s recipe lost the frames
(`and_intros` unfolds `Grows`); with the step as its own function, both went through at once
(again: loop bodies straight-line and shallow).

### The `natOpResult` arms under `ArenaR` (`NatArms.lean`)

Every arm whose result is a literal is `litArm F a b = do let x ← internE (.lit (.natVal
(F a b))); pure (some x)`, and each verbatim arm (`natSubArm`, …) unfolds to it. One generic
theorem covers the seven ops whose pool function appends at the top (`-`, `*`, `land`, `lor`,
`xor`, `shiftLeft`, `shiftRight`): `topLit f` is `natAddLit` with `f` for `nat_add` (written as
syntax, since the notation takes a literal function name), and `topLit_refines` is
`natAddLit_refines` with `f`'s spec as a hypothesis in `natAdd_spec`'s shape (`TopSpec p f F`).
Each instance is one line (`topLit_refinesA … natSub_top`); `TopSpec` for the bitwise ops and the
shifts is the pool function's spec rewritten under the binder (`simpa only [← land_bv]`,
`[← Nat.shiftLeft_eq]`, `[← Nat.shiftRight_eq_div_pow]`). The others are their own L functions:
`pred` writes a one-limb `1` at the top and subtracts it (`Grows.push1`: pushing a limb is
growing the pool, pattern on the two stores); `pow` returns `(0, 0)` for the arm's `none` (an
exponent above `2^24`; two or more limbs of a normalised `b` are at least `2^64`) and `(1, h)`
otherwise, decoded by `decOpt`; `/` and `%` take `nat_divmod`'s first or second slice. All under
`ArenaR` in `natArmProg` (`storeProg` and the pool functions), each proof in the house form at
the first or second attempt, 3.7 s for the file. The operands are normalised slices (as every
`lit` record's), which `nat_shr` and `nat_divmod` need for `b`.

`Nat.gcd` is `nat_gcd`'s slice interned. `Nat.beq`/`Nat.ble` intern a `const` node: the arm reads
the pins `boolTrueName`/`boolFalseName` and, inside `constE`, `emptyLevels`, which `ArenaR` does
not cover, so `nat_beq_lit(oa, la, ob, lb, t, f, us)` takes the three handles as arguments and
the theorem takes what the pin reads return as hypotheses (`boolTrueName.run a₀ = .ok (decI t,
a₀)`, …; they read the state and do not change it). The L side is `nat_cmp`'s code
(`if c != 1 { t := f }`, `c == 2` for `ble`) and `intern_const` (`internConst_refinesA`); the
house form went through with `constE` and the arm unfolded and `natcmp_grind` for `cmpW`.

Not done: `natOpResult`'s dispatch itself (it reads fifteen pins first; the pins are not in
`ArenaR`).

### `sorry`s

None.


## Expression lines, literals, escapes, and bytes → stores in one theorem (2026-10-21, lane `front2`)

Files (all `ConAgua/Front/`): `ExprIface` (the interface between the two passes), `FieldsExpr`/
`FieldsExprLink` (fields of expression lines), `ApplyExpr`/`ApplyExprRefine` (the expression id
table and `apply_expr`), `NatDec`/`NatDecLink` (decimal literals into the limb pool),
`Unescape`/`UnescapeLink` (string bodies with escapes into the pool), `Preserve` (what every L run
keeps), `Driver`/`DriverRefine` (the whole-buffer loop, generic), `FrontRun` (the instance and
the whole program). Four pieces were written by forks in parallel worktrees against interface
files written first (`ExprIface`, `DeclIface`); the interfaces held without change.

### What is proved

`frontAll_refines` (`FrontRun.lean`): for the program `frontAllProg` (the Stage B validator, the
fields passes, all stores, the apply steps, `front_line`, `front_run`), under `numBits = 64` and
`b.size < 2^63`, from a memory holding `b` in `IN` whose pool has fewer than `2^63` words and which
is related to an arena state `a₀` by `ArenaD` and to the blank parse state by `StateDR`: if
`front_run()` returns `0`, then `(parseBytes b).run a₀ = .ok (.ok (.ofState st'), a')` (con-ron's
whole-buffer parse accepts) and the final memory is related to `a'` by `ArenaD` and to `st'` by
`StateDR`. Only `propext`, `Classical.choice`, `Quot.sound`. No `sorry` in `ConAgua/Front`.

* **Expression lines.** `front_line` reads a line's fields with `rec_line_loop` (names, levels);
  if that finds no name/level payload, with `rec_expr_loop` (`apply_any`). All ten `ExprRec` kinds
  are read (con-leche has no `fvar`/`mdata` records); one generic member loop `rec_obj` serves the
  six sub-objects (`app`, `lam`, `forallE`, `letE`, `const`, `proj`), linked by one generic
  theorem (`objRec_link` over a value-carrying `VLoop`) and six ~9-line instances. `apply_expr`
  interns through `mk_app`/`mk_lam`/`mk_forall`/`mk_let`/`mk_proj` (the derived ranges) and
  `intern_bvar`/`sort`/`const`/`ls`/`lit`, into `EID` (array 66); `applyExprW_refines` against
  `parseExprEntryD`, one theorem over all kinds. The front invariant is now `ArenaD`
  (`ArenaR ∧ DerR`); the leaf interns keep `DerR` (`internSort_D`, `internConst_D`,
  `internLit_D`, `internLs_D` in `ApplyExprRefine.lean`: they belong next to `internBVar_D`).
* **`natVal` of any size.** `nat_dec(c, d)` reads the digits 19 at a time and folds each chunk
  in place (`limbs := limbs·10^k + chunk`, the local multiply-add `nat_mad`, a candidate for lane
  `nat`'s files); `natDecW_val` + `natValR_decN`: the slice is normalised and denotes con-leche's
  `readNatAt` (`readNat64` up to 18 digits, `readNat` beyond). `node_lit` = `nat_dec` +
  `intern_lit`.
* **Escapes.** `str_put_esc(vs, ve)` decodes `\" \\ \/ \b \f \n \r \t \uXXXX` (surrogate pairs
  too) into UTF-8 bytes in the pool; `strPutEsc_link`: on con-leche's `scanString` result the
  slice is `strWords s` (`\u` against `String.utf8EncodeChar`). `apply_str` (name `str` lines)
  goes through it; `NameR` now carries con-leche's `scanString` result (`StrR`) instead of
  `StrOK`.
* **Declaration lines** (axiom, def, thm, opaque, quot; second landing). Fields: `rec_decl_line`
  with one generic object loop `rec_decl_obj` (one generic link `dobj_link` for con-leche's five
  loops), eight words `DFld` (`DeclIface.lean`); `inductive` is recognised (`pl 25`, validated by
  Stage B's `scan_ind_decl`) and aborts in the apply step. Apply: `apply_decl` pushes an 8-word
  record to `DECL` (67, count in word 0) with the universe-parameter name handles in `DLP` (68);
  `StateDR` gets `decls : DeclsR`; `applyDeclW_refinesAM` against `applyLine st (.decl d)`
  (`processLineCoreD`, the arena state unchanged); unsafe axioms/opaques, a non-`safe` def and an
  unknown quot kind abort where con-ron declines. `front_line`'s `apply_any` tries name/level,
  expression, then declaration fields (`apply_dline`). `frontAll_refines` covers them.
* **The driver.** `front_run()` = `front_init()`, then `front_line(i)` while `i < len(IN)`:
  `0` when every line applied, else the number of the first line that does not scan. Its loop
  spec is generic in the models of `front_init`/`front_line` (`runW`); `runI_refines` relates
  the model to `feedChunk` + the final-line step of `parseBytes`, generic in the relation (`Inv`)
  and the line step (`LineStepI`). A last line without a newline is applied by `front_line`
  (next `0`) where `feedChunk` leaves it as the tail for `applyFinalLine`.

### Decisions and findings

* **What a driver can carry.** A callee's spec says nothing about the input bytes, so the loop
  could not re-establish `s.mem.arr8 IN = b` for the next call. `Preserve.lean` proves once, for
  any program without `st8` (`Prog.noSt8`, decided for `frontAllProg`), that every run keeps
  the byte arrays and every array's size, and restores the caller's locals (`Triple.keep`). L
  specs that the driver calls therefore take `(arr64 POOL).size < 2^63` instead of `PoolOK`
  (the code's own room checks supply the rest); the instance's line model includes "bytes
  unchanged" (`lineKW`), so the refinement can keep `m.arr8 IN = b` in its invariant.
* **Interfaces first.** Writing `ExprIface.lean` (pl codes, `ExprR`, `itemsN`/`listN`,
  `NatValR`, `StrR`) before forking the fields pass and the apply step let both be proved
  against the same relation without seeing each other; the merge was a lakefile conflict only.
* **Patterns cannot start at a variable function** (`lineW m i` with `lineW` a parameter):
  the arms of a generic model go through an auxiliary function applied to the `Option`
  (`runK … (lineW m i)`), whose arms match on `some (ok, nx, m')`.
* Forks' findings: `bv_decide` adds native axioms (caught by `#guard_msgs` on `#print axioms`)
  and needs a real import in `module` files; a generic loop over one tuple state does not unify
  with con-leche's curried loop (per-arity helpers); `finish` needs `NONE` unfolded;
  `parseExprEntryD` elaborates through a join point (`simp only [parseExprEntryD, exprOp,
  bind_assoc]`, not `rfl`); arm lemmas whose right side is a callee result take it as a variable
  with an equation hypothesis.
* Two `Inhabited (StateD ⊕ RecordVerdict)` instances in different files clash on import; it
  lives in `StateDR.lean` now.

### Measurements (`lake env lean`, user, one run)

| file | lines | L lines | user |
|---|---:|---:|---:|
| `FieldsExpr` | 484 | ~95 | 54 s |
| `FieldsExprLink` | 938 | | 14 s |
| `ApplyExpr` | 766 | ~55 | 9.8 s |
| `ApplyExprRefine` | 541 | | 1.5 s |
| `NatDec` / `NatDecLink` | 378 / 504 | ~45 | 6.9 / 2.5 s |
| `Unescape` / `UnescapeLink` | 418 / 721 | ~83 | 11.3 / 4.2 s |
| `Preserve` / `Driver` / `DriverRefine` | 184 / 178 / 186 | 18 | 1.3 / 1.2 / 0.8 s |
| `Line` / `LineRefine` / `FrontRun` | 311 / 335 / 224 | 45 | 3.7 / 1.2 / 8.0 s |
| `FieldsDecl` / `FieldsDeclSpec` / `FieldsDeclLink` | 383 / 331 / 1103 | 132 | 0.6 / 89 / 14 s |
| `ApplyDecl` / `ApplyDeclRefine` | 423 / 529 | 70 | 11.0 / 3.1 s |

Rust counterparts: `nat_decimal.rs` ~50 lines of code, `unescape_bytes`+`utf8_of` ~110, the
expression records of `scan_fast.rs`/`export_c.rs` ~400. `#guard`: the whole program accepts a
sample with a header, a name, a level and six expression kinds (a 30-digit literal), reports a
malformed line's number, aborts on an unbound id.

### Not done / requests

* **`strVal` lines abort**: the `lit` store's `RecRel` keeps a `strVal` as kind `1` without
  contents (`LitRefine.lean`). Request to lane `exprops`: a contents-carrying `strVal` record (the
  bytes as a pool slice, as `nstr`) and an `intern_lit` entry for it; `str_put_esc` already
  produces the slice.
* Inductive blocks abort (`validateIndD`/`installIndD` are not ported).
* **`frontAllProg` no longer passes the compiler's static check**: the declaration fields pass
  returns 8–9 words (`rec_decl_line`, `rec_decl_obj`, `d_member`, `decl_val`, `apply_dline`) and
  the compiler allows 6 (`maxRes`, `Compile.lean`). Request to lane `compiler`: `maxRes ≥ 10`; else
  the fields pass packs `pl`/`hk`/`flag` into one word. (The first landing's `frontAllProg_wf`,
  without declarations, held; it is removed.)
* A string compared as a literal (`safety`, quot `kind`) with an escape in it aborts (con-leche
  decodes it first).
* Ids at or past an id table's end abort (no sparse overflow).

* The decl fields' heavy specs (8–9-word results) needed `sym (gen := 16..24) (instances := 5000)`
  and up to 4M heartbeats; a failing attempt took 13–25 minutes, mostly printing goals. Writing
  callee posts as explicit lists of per-field model functions instead of `.enc` of a structure
  update, and inline conditions instead of a `Prop` wrapper with a `Decidable` instance, fixed it.
* Census links: `l_impl`/`refines_part` on `apply_decl`/`processLineCoreD`, `applyExprW_refines`,
  `natValR_decN`, `strPutEsc_link`, `rec_decl_line`.

### `sorry`s

None.

## The shared Lake artifact cache (2026-10-21, lane `cache`)

Ported from con-ron (`_tmp/ref/con-ron/CLAUDE.md`, "The shared Lake artifact cache", task
#97-CACHE), which hit the same problem first: ~1750 modules, full build ~2 min wall on 96 cores
and growing, every agent worktree under `_tmp/wt/` otherwise rebuilding from scratch.

### Mechanism

Lake 5 (this toolchain, `nightly-2026-10-20`) keeps a content-addressed local artifact cache
keyed by each module's *input hash* (source bytes, import artifact hashes, toolchain, options,
module name) — no absolute path in the key, so one cache directory serves every worktree and
branch and survives a worktree being deleted. Confirmed in the Lake source
(`~/.elan/toolchains/*nightly-2026-10-20*/src/lean/lake/Lake/Config/{Env,PackageConfig,Monad}.lean`,
`Lake/Build/Module.lean`):
* `LAKE_CACHE_DIR` picks the cache directory; with no override Lake falls back to
  `$ELAN_HOME/toolchains/<tc>/lake/cache`, a separate bind mount in the agent sandbox, so Lake
  cannot hard-link out of it and silently *copies* every restored artifact instead (con-ron's
  finding). **There is no lakefile.toml equivalent for the cache directory** — it's resolved
  once in `Env.compute`, from the process environment, before any lakefile is read.
* `Package.isArtifactCacheReadable` defaults to `true` and `Package.isArtifactCacheWritable`
  defaults to `false` (`Lake/Config/Monad.lean`) — i.e. **reading is automatic, writing is
  opt-in**, out of the box, with no lakefile.toml change needed. The env vars
  `LAKE_ARTIFACT_CACHE` / `LAKE_RESTORE_ARTIFACTS` (or, if we ever wanted to flip the default,
  the lakefile.toml options `enableArtifactCache` / `restoreAllArtifacts` on the root package)
  only matter for *writing*; we leave them unset in `lakefile.toml` and set them only on the one
  build that seeds the cache. `Module.lean`'s read path (`fetchCore`, the
  `isArtifactCacheWritable = false` branch) calls `fetchFromCache? … (restoreAll := true)`
  unconditionally, so a read-only build always restores full build-directory artifacts (not just
  cache-internal ones) when it hits a cache entry — this is the "hard-linked into `.lake/build`,
  0 bytes of disk" behaviour.

Since `LAKE_CACHE_DIR` can only be set by environment variable, and an agent's shell does not
keep env vars between tool calls (`PLAN.md` "Process rules"), the project does not rely on
anyone sourcing anything: **`scripts/lake`** is a wrapper that computes `git rev-parse
--show-toplevel`, exports `LAKE_CACHE_DIR="$root/_tmp/lake-cache"`, and `exec`s the real `lake`.
Every build, in every worktree, is `scripts/lake build …` instead of plain `lake build …` — no
sourcing, no persistence needed, just a different binary name. `git rev-parse --show-toplevel`
returns the *worktree's own* root, which only resolves to the one shared cache because
`scripts/new-worktree.sh` symlinks the worktree's `_tmp` to the main tree's `_tmp` (the same
"shared through a symlink" convention con-ron uses).

`scripts/new-worktree.sh <path-under-_tmp/wt> [<rev>]` wraps `git worktree add` and then:
* symlinks `_tmp` (hence `_tmp/lake-cache`) in from the main tree;
* symlinks `.lake/packages` in from the main tree too. Kraken (the one `[[require]]` in
  `lakefile.toml`) is a git dependency pinned by `rev`; its checkout and its own small build
  directory (`.lake/packages/Kraken/.lake/build`, ~25 MB, separate from the root workspace's
  `.lake/build` because it is a dependency package, not vendored source) are identical across
  every worktree on the same lakefile, so there is nothing a fresh worktree needs the network
  for. **Never `lake update` against the symlinked copy from a worktree** — that's shared
  mutable state; do it in the main tree.
It refuses a path outside `_tmp/wt/`, matching the "worktrees go in `_tmp/`" rule.

### Seeding

(The seed-on-landing policy that stood here was superseded on 2026-10-22: every `scripts/lake`
build writes to the cache, guarded; see "Cache incident".)

**GC**: the cache pins every artifact ever written to it, so it only grows (toolchain bumps,
renamed modules, abandoned lanes all leave orphans behind). There is no automatic eviction.
Check size with `du -sh _tmp/lake-cache`; clear it with `scripts/lake cache clean` (or
`rm -rf _tmp/lake-cache`, same effect, both just lose the cache, never the build). Worth doing
occasionally (say, after a toolchain bump) — not on every landing.

### Measurements (2026-10-21, this machine, concurrent with five other agent worktrees building)

| build | wall time | note |
|---|---:|---|
| main tree, plain `scripts/lake build`, stale `.lake/build` | 2m18s (1800 jobs) | brings master's own build dir current; this is the baseline "full build" |
| seed: `LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true scripts/lake build`, tree already current | 0.55s | pure hard-linking into `_tmp/lake-cache`, no re-elaboration |
| cache size after seeding | 1.7G in `_tmp/lake-cache` (apparent; see dedup note below) | |
| fresh worktree (`scripts/new-worktree.sh`, no `.lake/build`), `scripts/lake build` | 0.365s (1800 jobs) | all restored from cache, zero re-elaboration |

**Disk**: `du -sh` on the fresh worktree's `.lake/build` alone reports 1.7G — `du` cannot know a
directory's blocks are hard-linked elsewhere unless it's told to look. Passing all three
locations to one `du` invocation (`du -sch .lake/build _tmp/lake-cache _tmp/wt/cachetest/.lake/build`,
from the main tree) lets GNU `du` deduplicate by inode across them, same as the filesystem
itself does: the combined total is **3.3G — identical to the main tree's `.lake/build` alone**.
The cache and the fresh worktree's entire 1800-module build directory cost ~0 bytes of *marginal*
disk; `stat -c %h` on a sample olean shows `links=3` (main tree, cache, worktree, same inode).

## Cache incident (2026-10-22, lane `cachebug`)

**What happened.** Lane `integrate` (landing 3) found that `scripts/lake build` "completed" while
`ConAgua.Checker.Entry`'s olean lacked `L.Checker.indParamsOkL`, which its source defines; the trace
was a *synthetic* one (`inputs: []`), i.e. restored from the shared cache. Building without the cache
fixed it.

**Mechanism: a time-of-check/time-of-use gap in Lake, which the shared cache turns from a local glitch
into a project-wide one.** Lake (`nightly-2026-10-20`, `Lake/Build/Module.lean`) reads and hashes each
module's source in the `input` facet (`recFetchInput`) when the build *starts*; the input hash (source,
import olean hashes, options, toolchain) is fixed then. Lean reads the file again when the module is
actually compiled (`compileLeanModule`), after all its imports are built — in this project often
minutes later. If the file changes in between (an agent editing while a background build runs, a
`git checkout`/`stash`/`merge` in the worktree, `checker_prog.py` regenerating `Prog.lean`), Lake records
"input hash of text A -> olean of text B": in the local `.trace`, and with cache writes on
(`fetchCore`, `writeOutputs … (overwrite := true)`) in `_tmp/lake-cache/outputs/<pkg>/<hash>.json`.
Every later build of text A, in any worktree, then restores B's olean with a synthetic trace and no
elaboration — exactly the reported symptom. Reproduced in `_tmp/cachebug/repro` (two-module project,
`Slow` sleeps 6 s): start the build with `B.lean` defining `indParamsOkL`, revert it 3 s in, restore it;
`lake build` then says "completed", `#check indParamsOkL` fails, and a fresh copy of the project with
the same cache gets the stale olean with `synthetic: true, inputs: []`. If B's text had a broken proof
and A's a correct one, the broken proof would build green — in every worktree, and at `land.sh`.
Ruled out: in-place mutation of hard-linked files (every one of the 13147 artifacts in the cache hashes
to its own name — `_tmp/cachebug/HashCheck.lean`; Lake deletes outputs before compiling and never
rewrites an artifact; no worktree has hard-linked `.trace`/`.hash` files), and `restoreAllArtifacts`
(it only decides whether the files land in `.lake/build`). Writes being on by default since this
morning made the exposure much larger: before, only `land.sh`'s build in the (lock-protected) main tree
seeded the cache.

**Fix (`scripts/lake`, now Python).** A build through the wrapper
1. takes a per-worktree lock (`.lake/scripts-lake.lock`): one Lake build per worktree at a time (two
   builds in one `.lake/build` race on the same files);
2. snapshots `(mtime, size)` of every `*.lean` (plus lakefile, toolchain) in the worktree before and
   after; any difference means the build may have compiled something other than what it hashed;
3. writes the cache through a private *staging* cache: `artifacts/` is a symlink to the shared one
   (content-addressed, never rewritten, so sharing it cannot go wrong; hard-link restores stay
   instant), `outputs/` — the input-hash -> artifact mappings, the only part that can be wrong — is a
   copy (`cp -rp`, ~0.3 s for 12k mappings). Only when the sources did not change are the new mappings
   published into the shared `outputs/`, each atomically and never overwriting (`os.link`);
4. on a change: publishes nothing, deletes the changed modules' local state (trace, olean, `.hash`) so
   the next build cannot trust it either, and exits non-zero (3 when Lake itself succeeded) with the
   list of files. `LAKE_ARTIFACT_CACHE=false` builds get 1, 2 and 4 too (a poisoned local trace would
   otherwise be published later by `getArtifactsUsingTrace?`); `env`/`serve` pass straight through,
   read-only. Residual hole: plain `lake` in a worktree bypasses all of this (PLAN.md forbids it).
`land.sh` needs no change: it already treats any non-zero exit as a failed landing.

**Safety net.** `scripts/buildstats.py` (a cache-free build of master in `_tmp/wt/buildstats-run`) now
records its verdict in `_tmp/buildcheck.json` and shouts on failure; `census.py` and `gist_report.py`
show "last cache-free build of master: <commit>, OK/FAILED".

**Did anything bad land? No evidence of it, and nothing broken is on master.** A cache-free build of
master `163e687` (plain `lake`, empty private cache, 2474 jobs, 9 min) succeeds. Its 905 input-hash ->
output mappings that the old shared cache also had were compared: 879 identical, 26 differing only in
olean bytes (ilean, IR and C identical; the constants, their types and their `sorry` use, read back
from both oleans with `_tmp/cachebug/OleanCmp.lean`, identical) — Lean's olean output is not
bit-for-bit deterministic, not poisoning. So no module of current master was served a stale olean, and
every landed proof elaborates. What cannot be checked after the fact: an intermediate master state that
landed green through a poisoned entry and was fixed by a later landing, and census numbers taken from
such a state; the Entry case itself was caught (`checker_prog.py` saw a stub). The old cache was purged
anyway (entries for lane-only texts cannot be validated). The wrapper now uses a NEW directory,
`_tmp/lake-cache-v2`, seeded from that cache-free build: worktrees still on a branch with the old
wrapper keep writing unguarded into `_tmp/lake-cache` until they merge master, and must not pollute
the new one. Coordinator: `rm -rf _tmp/lake-cache` again once every lane has merged master.
Nondeterministic oleans mean a publish may find "same input, different bytes" mappings; the wrapper
keeps the first and notes the count.

## Cache misses between worktrees (2026-10-26, lane `gatecache`)

**Symptom.** The queue's gate build of consync's entry compiled 831 modules and hit the 50 min timeout
(`_tmp/mq/logs/20261026-092911-consync/gates/6-build.log`), although consync had built exactly that tree
(the queue merged it onto the master consync had merged; tree identical) and its own `gates.sh` build was
all replays. slownat and slownat2 took 51 and 46 min in the queue the same way.

**Not the cause.** Publishing and reading work: a branch built in one worktree (812 modules compiled,
35 min) builds in a second worktree that had master built in 11 s, 0 compiled. No absolute paths enter the
input hash (paths are only captions in the trace). The coordinator's reset (2026-10-25 21:20) was before
consync's last builds. consync did publish: 735 of the 831 modules the queue compiled have a mapping
published during consync's work (03:07-09:29) with the same `.ilean` -- under a *different input hash*.

**Mechanism.** A module's input hash contains the hashes of its imports' artifacts (`importAllArts`), so
it depends on which `.olean` *bytes* each import has. Lean's oleans are not byte-for-byte deterministic
(same input, same `.ilean`/`.c`, different `.olean`: e.g. `ConRon.Bridge.Frontend.Lines`, 24 MB; already
noted in "Cache incident"). And Lake (`getArtifacts?`, `Lake/Build/Common.lean`) takes a module's outputs
from the worktree's LOCAL trace when its input hash matches, before it looks at the cache's mapping; the
publish keeps the first mapping (no-clobber). So a worktree that compiled a module itself while another
compiled the same input (concurrent lanes on the same master, helper lanes merging each other, the queue),
or compiled it with the cache unreadable, or whose mapping a reset dropped and someone else re-published,
keeps its own olean variant forever: every module downstream gets input hashes nobody else has. That
worktree's builds are replays locally and publish mappings no other worktree can use; the queue, restoring
the canonical variants from the cache, misses everything downstream. Second cause: `LAKE_ARTIFACT_CACHE=false`
(the documented way to keep a build out of the cache) turned off cache READS too (Lake's
`Package.isArtifactCacheReadable` is `enableArtifactCache?.getD true`; `false` disables both): such a
build compiles everything it does not have locally, creating exactly such private variants.

**Reproduction** (`_tmp/wt/gatecache2`, master built from the cache): set the local trace of
`ConAgua.Checker.ParThreadTwin` to another olean variant of the same module (what a private compile
leaves behind). Old wrapper: its three dependents are compiled (and the next build says nothing: the
divergence is silent and permanent). New wrapper: "1 module(s) here had other outputs than the shared cache
has", 0 compiled, 14 s. Deleting `Inst1Emit`'s local state and building with `LAKE_ARTIFACT_CACHE=false`
compiled it five times although the cache had it.

**Fix (`scripts/lake`).** (1) Before every build (writing or not), under the worktree lock, the wrapper
compares each local module trace with the shared mapping for the same input hash and deletes the local
state of the modules that differ; Lake then restores the cache's outputs, and the downstream input hashes
are everyone's (~0.3 s for 1800 traces). (2) `LAKE_ARTIFACT_CACHE=false` is passed to Lake as *unset*:
reads on, writes off. Resets of the cache are no longer needed for correctness of hits; a dropped mapping
is re-published by the next writing build that has it locally.

**Queue (`scripts/mq.py`).** When the merge result's tree equals the entry's commit's tree and
`_tmp/mq/green/<commit>` exists, the steps the stamp covers among build, the closure checks and e2e are
not rerun (same tree, same result; the landing note says so). `_tmp/mq-log.csv` gets `built`/`jobs`: the
modules the gate build compiled, so misses show. The build gate's timeout is back to 90 min (it was raised
to 3 h as a stopgap).

## Does the relation scale? (2026-10-21, lane `scale`)

Question: does the L ⊑ twin relation (`ArenaR`, `ArenaD`, the `GoOK`-style specs) scale to all the
state the checker will have? Files: `ConAgua/Spike/{ScaleBase,ScaleFlat,ScaleNested,ScaleGrind,
WriteSet,WriteSetInst,TwinKeep}.lean` and `gen_scale.py` (the generator of the three `Scale*`
relation files). The spikes are not imported by `ConAgua` and have no `sorry`; check one with
`lake env lean ConAgua/Spike/<f>.lean` (`WriteSetInst` needs `lake build ConAgua.Spike.WriteSet`
first). No other file was changed.

**Verdict.** The relation scales if two things change now, before the core lands. (1) Specs must
carry their frames. Today a walk spec (`GoOK`, `LGoOK`, `IGoOK`) ends in `ArenaD m' a'` and says
nothing about the rest of the memory or the twin state, so every new state component would force
each existing walk to be re-proved or framed by hand. Lane `front2` already hand-wrote
`mkAppW_above`… for `Above64`. Both frames can be obtained cheaply and generically (experiments 2
and 3). (2) The relation should be bundled per tier and over projections of `AState`, not as one flat
structure over `AState`. The flat bundle's cost per writer grows faster than linearly (experiment 1),
and a group over `AState` gets no twin-side frame by definitional unfolding. Store and memo tables
fit the existing libraries. New ideas are needed for six components: the scratch-tier drop, the
mode-memo bank stack, tree-valued caches, the environment index's deletion, nested declaration
records, and `Readback`'s `Expr`-keyed memo. None of them threatens lockstep equality of the caches.

### Inventory

Lifetimes: **G** global (whole run), **D** per declaration (`flushCaches`/`enterScratch` …
`dropScratch`), **C** per top-level call (cleared at entry), **A** an argument value (not in
`AState`).

| component | type | life | mutation | L representation | relation clause | verdict |
|---|---|---|---|---|---|---|
| `store` persistent tier, 21 cons tables | `Tbl` (nodes, der, cons) | G | append | `StoreLib` open addressing | `StoreR`/`TierR` | **fits** (done) |
| `store` scratch tier | same | D | append; `enableScratch`/`dropScratch` empty it | same, tier 1 | `TierR … 1` | **needs X**: `SlotsOKG` requires every slot ≤ count, so a drop to count 0 must zero all scratch slots (O(capacity) × 21 tables per declaration). Use epoch-stamped slots for tier 1, as the memos have |
| `store.scratchOn` | `Bool` | D | set/reset | `CTL[1]` | in `StoreR` | fits |
| derived columns | `UInt64` per node | with node | append | range in `XDER`, leaf ranges from the record, hash opaque | `DerR` | fits (5 compound tables done) |
| `memos` (10 tables) | `HashMap (EIdx×Nat) EIdx`, `EIdx → Nat`, `LIdx → LIdx`, `LsIdx → LsIdx` | C | insert, clear (`Memos.empty` at `enterScratch`) | `MemoLib` (2 key words, 1 value word, epoch clear) | `MemoRG` | **fits** (3 done) |
| `caches`: `whnfCoreC`, `whnfCoreCheapC`, `whnfC`, `inferC`, `inferIOC`, `defeqC` | `EIdx → EIdx`, `(EIdx×EIdx) → Bool` | D | insert; `takeModeMemos`/`putModeMemos` around every eager `defeqE` | `MemoLib` in `D` banks; bank = eager depth | `MemoRG` for the live bank, plus "bank `i` relates the `i`-th saved `ModeMemos`" for the twin's saved values | **needs X**: bank-indexed dispatch (static code per bank from the generic schema; a depth word selects), and a depth-indexed frame in the knot specs ("banks below `d` unchanged"). The same code writes every bank, so this frame is semantic and the text frame (experiment 2) cannot give it |
| `caches`: `lvlEqC`, `lvlsEqC`, `constTyC`, `constValC`, `ruleRhsC` | handle pairs/triples → `Bool`/handle | D | insert | `MemoLib` (a triple of 32-bit handles packs into two words) | `MemoRG` | fits |
| `caches`: `readLC`, `readNC`, `readLsC` | `LIdx → Level`, `NIdx → Name`, `LsIdx → List Level` | D | insert | values are **trees**: a per-declaration tree heap, slot value = tree pointer | `MemoRG` with a value decoder that reads memory (`dv : Mem → Word → Option ν`; today `dv : Word → ν`) | **needs X**; the tree heap's lifetime is D, not the per-call scratch heap ROADMAP §2 item 5 plans for level algorithms |
| `flushCaches` | – | D | `caches := Caches.empty` (the twin no longer drops selectively; ROADMAP §2 item 2 is stale) | 14 epoch bumps | `memoRG_clear` | fits |
| `pins` | `Array NIdx` (51), `List NIdx`, 3 handles | G | filled once (`internAllPins`) | a fixed word array | `PinsR m a.pins` | fits |
| `fe : IFEnv` | `IEnv` (list) + `HashMap NIdx (Nat × IConstantInfo)` + `visibleBelow` | **A**, G | `push`; `popTemp` (erase or re-insert); `restrictTo` views live **at the same time** as the full one (`CheckDecl.lean:113,124,135`); `eraseInstalled` (`Promote.lean:345`) | one destructive index (name → counter, record pointer) and a `vis` word per view | `EnvR m vis fe`, stated through `find?` and `visibleBelow` (a view whose counter is `≥ vis` misses in both), plus the order of `consts` | **needs X**: deletion in an open-addressing table (tombstones), and `find?`-level extensionality |
| `IConstantInfo`, `IDeclaration` | nested: `List NIdx`, `List IRecRule` (each with `IRecRuleFire` lists), `IIndCaps` (lists, `PropWhen` = `List Name` **values**), `IProjTable` (`Array EIdx`, `List LIdx`) | G | built at install, immutable | record pool, bump-allocated, below a top | `decCI m p = some ci` (a recursive decoder); `PropWhen`'s names decoded through the store (`denoteN`) | **needs X**: nested decoders (`PoolSlice` covers flat slices only); the frame is `PoolSlice`'s `Agree` (the pool below the top never moves) |
| `pend : Array PendingCheck` | `ValueGroup` (kind, `IConstantVal`, handle), two `Nat` | A, phase A → B | push | pool records | decoder | fits once the record pool exists |
| pin sets `List INatOpPinSet` | 8 handles, `List EIdx`, a `String` (only in a decline message) | A, G | none | pool | decoder; the string is not represented (a decline claims nothing) | fits |
| `PMemo` (promotion) | 4 maps handle → handle | A, D | insert | 4 `MemoLib` instances | `MemoRG` on an argument | fits |
| walk-local memos: `wscopedBGo`, `fvarLeavesGo` (seen + an accumulator list in walk order), `leavesSubGo`, `constsResolveFGo`, `hasStrLitGo`, positivity's `mentionsAnyGo`/`nestOccGo`/`depthGo`/`replaceFVarsGo`, `RecCheck`, `StructParts`, `usedConstsGo` (a set + an array) | `HashMap`/`HashSet` of handles, lists/arrays | A, C | insert | `MemoLib` instances, scratch stacks | relation on the argument | fits |
| `Readback`'s `EMemo` | `HashMap ConLeche.Expr EIdx` (structural key) | A, per block | insert | keyed by ROM offset | – | **needs X**: equal trees at different ROM offsets miss in L where the twin hits. The store is unaffected (interning is idempotent), but the maps differ. Make the ROM hash-consed (offset equality = tree equality), or state the interner's spec without the memo |
| `NestState` (positivity) | `Array NestKey`, `List NestKey`, `Array NestCtorNf` | A, per run | push, linear search | scratch stacks | decoder | fits |
| transient `Level` trees | `ConLeche.Level` | per call | built by pure level algorithms | scratch tree heap | decoder | needs X (ROADMAP §2 item 5) |
| knot (`CoreFnsA`, mode, eager depth) | closures | – | – | one mutual group, mode word | `CoreOK n := ⋀ entry specs` for every `F ≥ n` | fits the `GoOK`/`ArmOK` pattern |
| fuels | `Nat` | – | – | L fuel; counters for the counted ones | `F ≥ n` | fits (below) |
| attempt snapshots (`orElseAttempt`) | `AState` copy | – | – | none: L aborts at the first throw | – | fits (ROADMAP §3 (c)) |
| `AState.worker` | – | phase B | drop + `Memos.empty` + `Caches.empty` | the drop and epoch clears | – | fits |

### The risks, with evidence

**(a) Proof performance of one big bundle (experiment 1, `ScaleBase`/`ScaleFlat`/`ScaleNested`).**
`gen_scale.py` writes `ArenaR`'s 22 fields plus `N` dummy `MemoRG` clauses (schemas at arrays
100+, all over `a.memos.fvarBC`), the `arena_build` macro for them, and the same eight writer lemmas
(five intern lifts, `memo_set`, `memo_clear`, `grow`). `lake env lean`, one run each (imports alone
0.6 s user):

| bundle | fields | user (8 writers) | per writer |
|---|---:|---:|---:|
| `ArenaR` (today) | 22 | 4.9 s | 0.55 s |
| flat | 44 | 10.5 s | 1.25 s |
| flat (`ScaleFlat`) | 66 | 18.5–25.7 s (two runs) | 2.3–3.1 s |
| flat | 110 | 44.4 s | 5.5 s |
| nested: `ArenaR` + two groups of 22 (`ScaleNested`) | 66 | 1.55 s | the core's 0.55 s (paid once in `ArenaRel`) + ~0.05 s |

The flat cost grows faster than linearly: each writer frames every field, and the `apart` simp set
grows with the number of array ids. Writers grow too (every intern, every memo/cache set and clear,
every bank operation, the environment push), so the flat total grows roughly with the square of
the component count. In the nested version a group's frame lemma is proved once, from array bounds
(`Grp.frame`: `∀ b ∈ A, b < lo ∨ hi ≤ b`), and every writer outside the group pays one application.
**Finding:** the first nested version did not compile. A group stated over `AState`
(`Grp m a`) is a structure, so `Grp m (appLens.setP a t)` is not definitionally `Grp m a`, although
nothing the group reads changed. A group must take the **projection** it reads (`Grp m a.memos.fvarBC`,
later `CoreR m a.caches`, `PinsR m a.pins`). Then the twin side of the frame is definitional unfolding,
as `AM.st_proto` already gives for tables.

**`grind` and the relation (`ScaleGrind`).** On a trivial goal (`y ≤ 5` and a read): no relation in
the context 3 ms; `hA : ArenaR m a` 3 ms; its 22 fields as opaque hypotheses 6 ms; two tables'
`StoreR`/`TierR` unfolded 48 ms; all 19 tables and 3 memos unfolded **532 ms**. Lane `store2`'s
finding generalises: kept opaque, the size of the relation costs `grind` nothing; unfolded, it costs
linearly in the `∀`-clauses, before any instance matches. Today no refinement proof gives `ArenaR`
to `grind` (`WalkRefine`, `LiftRefine`, `Inst1Refine` have no `grind`). The L-side specs are about
models, the refinements are by hand with named lemmas. Keep it that way.

**(b) Frames per function: the main risk.** The walk specs (`GoOK n`, `LGoOK n`, `IGoOK n`) say
`ArenaD m a → … → ∃ a', run = .ok (r, a') ∧ ArenaD m' a'`. A caller that holds another relation
(the front's `StateDR`, a future `CoreR m a.caches`, `EnvR`, a saved bank) learns nothing about it
from this. Without frames, every walk proof would be redone each time a component is added. Two
generic remedies, one per side:

* **L side: frames from the program text (experiment 2, `WriteSet.lean`, 165 lines, 1.2 s).**
  `Preserve.lean`'s induction, generalised: `closedW p A C fs` (a `Bool`) says every function of
  the call-closed set `fs` stores only into arrays of `A` and into `CTL` words of `C`. A `CTL` index
  must be a literal `k`, or `k + (e &&& 1)`, which can only be `k` or `k + 1`. `run_frame`: every
  run of `f ∈ fs` is a `MemFrame A C` (and keeps the byte arrays). Applied to `instProg`
  (`WriteSetInst.lean`; instantiate1, lift, the `mk_*`, six stores, 52 functions): the only stores
  the check rejects are the six `*_push` count stores `CTL[k + t]`, whose tier `t` is not bounded
  by the text. With those masked (`k + (t &&& 1)`, the spike's `maskS`), `closedW` holds by
  `decide +kernel` in 0.36 s. `instEntry_frame` gives `MemFrame` for every `inst_entry` run.
  `stateDR_instEntry` then carries the front's `StateDR` across it with no lemma about
  `inst_entry`. Lane `front2` proved `mkAppW_above`… by hand for the same purpose.
* **Twin side: frames by composition (experiment 3, `TwinKeep.lean`, 147 lines, 1.5 s).**
  `Keeps π op`: every successful run keeps `π a`. It is closed under `bind`, `ite` and `pure`.
  The store primitives (`internNodeE`, `internLamE`, `internForallEE`) are one macro each, and the
  reads (`derivedE`, `view*`, `inst1Get`) are one line. `keeps_inst1Go`: `instantiate1Go` keeps
  `cp a = (a.caches, a.pins)` at every fuel, by one induction with one term per arm (about 45
  lines per walk family, no `grind`). With the L frame and this, any `X m' (cp a')` follows from
  `X m (cp a)` when `X` reads only arrays outside the write set. con-ron's Theorem 1 uses the same
  architecture (`Bridge/Specs.lean`'s specs end in `s'.caches = s₀.caches ∧ s'.pins = s₀.pins`,
  and `CheckOK.mono` transports the whole invariant across an `ExprOps` call). The alternative is
  to add `cp a' = cp a` to each `GoOK` post (cheap if done from the start: the proofs build `a'`
  from `with`-updates).

**(c) Caches: lockstep equality is enough.** L caches as con-ron does (same keys, same
insert/clear points), and `MemoRG` relates the L table to the map extensionally (`mp[k]?`), so
layout is free. What would break equality, checked in the twin (`vendor/con-ron/ConRon/Arena/**`):
* **No eviction and no capacity behaviour other than abort.** The caches are uncapped (task #115
  removed `cacheCap`, `CoreState.lean:28–31`). The only capacity rule is `idxCap` → `.native`, an
  L abort. `clear_fit` (`Core.lean:3552`) is Rust layout only. L memos abort at 3/4 load. That is
  sound, but completeness needs capacities sized for the largest declaration (or a resize, which
  is layout only and keeps `MemoRG`).
* **No `HashMap` iteration, `size`, `fold` or `toList` on any memo, cache, index or argument map**
  (grep over the twin; `NestState.keys` is an `Array`, `ctorIx` is a `List.foldl`). No key or value
  carries `mixHash` (handles hash by their word; lane `final`'s audit). Handle values are
  allocation indices, the same in lockstep.
* **Deterministic skips L must copy:** `whnfCoreStuckTag`/`whnfStuckTag` read neither the memo nor
  the store; a `none` level verdict is never cached; `defeqE` runs on emptied mode tables (`takeModeMemos`)
  and puts the caller's back (`putModeMemos`), dropping what the eager run added.
* **The exceptions** (table above): `readLC`/`readNC`/`readLsC` hold trees, `Readback`'s `EMemo`
  is keyed by trees, and the environment index needs `erase`. None is a layout dependence. Each
  needs a representation choice that keeps equality.

**(d) Fuel across the knot.** Fits. L fuel decreases on every call and loop iteration. The twin's
knot fuel decreases only per knot level, and its loop and walk fuels are fresh constants (`2^62`,
or counted in L, lane `final`'s audit). So `n ≤ F` is preserved at every knot call, and "for every
`F ≥ n`" closes the induction. The knot needs one conjunction `CoreOK n` over the six entry points
at both modes (the eager slot runs `mode.toEager`). The bodies take it as their hypothesis, as
`IArmOK n` takes `IGoOK n`; each body is its own lemma.

**(e) Scratch tier and stale handles.** Handle-valued data (caches, environment, pending) is
related as words, so a dangling scratch handle breaks no clause. Only the view lemmas interpret a
handle, and after a drop both sides fail the view (L's count check against `CTL`). The gap is the
drop itself (`SlotsOKG`, table above).

**(f) Environment and declaration records.** Not in `AState`: `fe` is an argument everywhere, and
several views of one index are live at once. The relation must be per view (`EnvR m vis fe`) and
extensional through `find?`, and the core's specs must take it as a precondition with the
environment arrays outside their write set. Experiment 2 gives that for free once those arrays exist.

**(g) Per-declaration drop and epochs.** Fits: `flushCaches` is now a wholesale clear (14 epoch
bumps), `enterScratch` clears the 10 memos, `AState.worker` is both. The bank stack is the one
operation that is not a clear (above).

### Recommended changes now

1. **Specs carry frames.** Adopt `WriteSet.lean` into `ConAgua/L` (it generalises `Preserve`)
   and state every program predicate (`LiftProg`, `InstProg`, …) with its `closedW` fact (by
   `decide +kernel`). Write the tier of the 21 `*_push` count stores as `CTL[k + (t &&& 1)]` (or
   move the counts into table-owned arrays). On the twin side, prove `Keeps cp` per walk family, or
   add `cp a' = cp a` to the `GoOK` posts of the walks still to come.
2. **Bundle per tier, over projections.** `ArenaD` (store + memos + derived) stays the walk tier.
   Add `CoreR m a.caches` (with the banks), `PinsR m a.pins`, `EnvR m vis fe`, and argument
   relations (saved `ModeMemos`, `PMemo`, `pend`) as separate structures. Each takes the projection
   it reads, owns a disjoint array range, and has one group frame lemma from array bounds. Keep a flat
   bundle at about 25 fields or fewer (≈ 0.5 s per writer).
3. **Never unfold the relation for `grind`**; fields stay opaque named predicates.
4. **Library work before the core:** epoch-stamped scratch slots in `StoreLib`; `MemoLib` with a
   memory-reading value decoder (tree values), deletion (environment index), and a bank-indexed
   instance family; a nested record decoder over the pool.

**What to watch:** per-writer CPU of a bundle (split it above ~2 s); any twin change that iterates
or sizes a map, or caches a value that is not a word; the eager depth bound `D` (unbounded nesting
in `.verified` mode, abort beyond `D`); memo and table capacities against the twin's uncapped caches.

### `sorry`s

None.

## `hasLooseBVar`, `fvarRangeGo`/`Memo` (2026-10-21, lane `exprops2`)

Files: `ConAgua/Arena/HasLooseBVar.lean`, `{FVarRange,FVarRangeRefine}.lean`; `DerRel.lean`
(the missing leaf-interning `DerR` lemmas, `natAddLit_refinesD`); `View.lean` (`view_fvar_idx`);
`MemoLib.lean`/`MemoLibRel.lean` (`frSch`/`frSch_wf`); `ArenaRel.lean` (one new `ArenaR` field,
`fmemo`, reusing `bmKey`'s codec). Continues lane `exprops`'s remaining phase-4 expression walks
(ROADMAP §1, `arena/expr_ops.rs`). No `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`.

### The missing `DerR` leaf lemmas, and `natAddLit_refinesD`

`internBVar_D`'s proof (`DerRel.lean`) ported to the other four leaf kinds, with `zP` (range `0`)
in place of `bvP`: `internFVar_D`, `internSort_D`, `internConst_D`, `internLit_D`, plus four
`bvar_derX` helpers (`bvarOfData` of each leaf's packed derived word is `0`, by `bvarOfData_pack`
with the hash/fvar/level-param fields and `(by decide)`/`satSucc_lt` bounds). Also `DerR.grow`/
`ArenaD.grow` (a pool append's `Grows` only touches `POOL` and `CTL[0]`, disjoint from the derived
arrays `42‥46`, so `DerR.frameM` applies directly) and `natAddLit_refinesD`, `natAddLit_refinesA`'s
counterpart under `ArenaD` (`internLit_refinesD` first, the same shape as `internLit_refinesA`).

### `hasLooseBVar(h, i)`

con-leche's (and Lean4's) `Expr.hasLooseBVar e i := i < e.looseBVarRange`: a direct read of the
cached range field, no recursion. Unlike every other walk in this group, it has **no twin arena
function** in `ConRon.Arena.ExprOps` to refine against (con-ron's memoized `has_loose_bvar_b_go`
lives on the inductive-types side, `arena/inductives/struct_parts.rs`, threaded through an extra
context `T` not relevant to plain expressions), so it is refined directly against the range field
of `a.store.derived`, which `der_b` (`ExprMk.lean`) already computes exactly (`derBW_ok`).

### `fvarRangeGo`/`fvarRangeMemo`

con-ron's `fvar_range_go`/`_memo` (`arena/expr_ops.rs:2075,2146`, twin `Arena/ExprOps.lean:1483-
1563`): `1 +` the largest free-variable index under a handle, memoized in a new per-call memo
`fvarBC` (`frSch`, array 48 `FRMEMO`, `CTL[46]`/`[47]`, the next free slot after `inst1C`; `bmKey`'s
one-word-key codec reused unchanged). `Walk.lean`'s `bvarBoundGo`/`Memo` shape exactly (`fr_go`
probes the memo, `fr_node` decodes the handle and dispatches on the tag), with three differences
from `bvarBound`: the `bvar` arm returns `0` (not `i + 1`), the `fvar` arm returns `idx + 1` (not
`0`; needs `view_fvar_idx`, a `view_fvar` that pins the record's index word, since `view_fvar`
itself is only existential), and the binder/`letE` arms do **not** truncate the last child (`max`
throughout, no `satPredW`: a binder's own annotations are not descended into, ROADMAP's `ExprOps.lean`
note on `fvarRangeGo`). This is `abstract1`'s cutoff (`fvarB ≤ d`), the walk lane `exprops2` turns
to next.

**A finding: match-arm grouping must be textual, not just semantic.** The arena-side dispatcher
`frArm` (`FVarRangeRefine.lean`) must group and order its `match` arms exactly as the twin's own
`fvarRangeGo_succ` does (`.fvar` first, then `.bvar | .sort | .const | .lit` together) for
`fvarRangeGo_succ'`'s `congr` to close by `rfl`; a semantically equivalent but differently grouped
`match` (`.bvar` split out on its own) leaves a stray match-equality goal. Same lesson as lane
`exprops`'s "continuations given as `fun` defeat `grind`'s matching": these proofs lean on the
compiled match/do-notation being syntactically identical, not just extensionally so.

### Tables

| | Rust lines | L lines | spec lines | refinement lines | refinement / L | `lean` wall / user |
|---|---:|---:|---:|---:|---:|---|
| `has_loose_bvar` | – (no twin) | 5 (`der_b` call, compare) | `HasLooseBVar.lean` ≈ 20 | ≈ 20 (same file) | ≈ 4.0 | – |
| `fvar_range_go` + `_memo` | ≈ 115 | 76 (`fr_go` 6, `fr_node` 59, entry 4, `fr_set`/probe plumbing 7) | `FVarRange.lean` 439 | `FVarRangeRefine.lean` **366**, **4.8 per L line** | 4.8 | – |

(`lean` wall/user not separately timed this landing; the full project build, 1810 jobs, restores
from the shared Lake cache and rebuilds only the touched files in a few seconds.)

### Compiled benchmarks of `lift_entry`/`inst_entry`

`LiftBenchComp.lean`/`LiftEmit.lean`/`harness/lift.c` and `Inst1BenchComp.lean`/`Inst1Emit.lean`/
`harness/inst1.c`: `WalkBench.lean`/`WalkEmit.lean`/`harness/walk.c`'s shape exactly (not proved,
drivers), building the left-nested spine `app (… (app (bvar k) (bvar k)) …) (bvar k)` with `n`
applications through `mk_app` (not `intern_app`: the walk needs the derived range) and calling
`lift_entry`/`inst_entry` on it; `LiftBenchLean.lean`/`Inst1BenchLean.lean` are the "Lean-compiled
arena" baseline (`lake exe liftbenchlean`/`instbenchlean`, con-ron's `liftLooseBVarsFast`/
`instantiate1Fast`), `WalkBenchLean.lean`'s shape. The harnesses use one uniform array size (`8
(n + 16)` words per content array) rather than per-table exact sizing — a driver, not proved, so
generosity costs nothing but memory.

**Measurements** (`perf stat -e instructions:u`, one run each; "build" is the same run without the
walk: `k ≥ 2^63` for L, `… build` for Lean):

| `n` | compiled L: build / build + walk / walk | con-ron's compiled Lean: build / total / walk |
|---:|---|---|
| `lift_entry`, 10^5 | 79.8 M / 282.7 M / 202.9 M | 196.9 M / 549.0 M / 352.0 M |
| `lift_entry`, 10^6 | 800.1 M / 2833.2 M / 2033.0 M | 1870.9 M / 5276.3 M / 3405.4 M |
| `inst_entry`, 10^5 | 79.8 M / 281.6 M / 201.9 M | 197.0 M / 550.4 M / 353.4 M |
| `inst_entry`, 10^6 | 800.1 M / 2872.5 M / 2072.3 M | 1870.9 M / 5290.1 M / 3419.2 M |

About 2030‥2070 instructions per `app` node for the compiled L walks (two memo probes per node,
`mk_app`'s own tail write, the two-children recursion) against about 3400‥3420 for con-ron's arena
compiled by Lean — L/Lean ≈ 0.60, the same order as the plain `bvarBoundMemo` walk's 0.56‥0.66
(lane `walk`, `exprops`). Building the term through `mk_app` (the derived-range write on top of
`intern_app`) costs the same as the plain walk's build (79.8 M / 800.1 M at 10^5/10^6): the write
is folded into the count check already in the critical path, no measurable extra cost from `der_b`
itself (one more memory read, branch-free).

### Not done, and why: `instantiateListGo`/`Fast`, `abstract1Go`/`Fast`

Both need a genuinely new idea, not just `Lift`/`Inst1`'s scaffolding reused; neither is a
45-minute fix, so both are left for a session that can give them the design attention first.

* **`abstract1Go`'s cutoff is `fvarB ≤ d`, not `fvarRangeMemo` directly**
  (`ConRon.Arena.ExprOps.fvarB`): it reads the packed derived word's `fvarOfData` field in `O(1)`
  and falls back to the exact memoized `fvarRangeMemo` walk only on the saturated branch
  (`r == satRange`). `ExprMk.lean`/`DerRel.lean` chose, when the derived-range arrays were added
  (lane `exprops`'s first landing), to store **only the bvar-range field** per compound node
  (`XDER[2 i + t]`, one word), not the fvar-range field too — "L keeps only the range field (the
  hash is opaque)" is the module doc's phrase for it. So L has no array to read `fvarOfData` off
  of, and cannot replicate `fvarB`'s two-branch shape at all without a design extension: a second
  word per compound node (an `FVDER`-family of arrays, `ExprMk.lean`'s `mk_*` writing it the way
  `der_b`'s value is written now) plus a `DerR` field for it analogous to the bvar one. Only then
  does `abstract1`'s cutoff become an `O(1)` read, matching the twin exactly; short of that
  extension, any L cutoff would have to always recompute via `fr_memo`, which is a **different
  function** from `fvarB` (it always clears/re-fills the memo; `fvarB`'s cheap branch does not
  touch it at all), so the two do not obviously agree node-for-node on the resulting arena state
  without extra, unproven invariants about when the twin's packed field is actually saturated.
  Brief for the next session: add the fvar-range column (five more arrays or five wider ones,
  `42`‥`46`'s pattern doubled), extend `DerR`/`mk_*`/`der_b`'s sibling (`der_f`?) the way this
  landing did for the leaf internings, *then* `abstract1` is `Inst1.lean`'s shape with `fvarB`'s
  cutoff and the `fvar` arm comparing the index to `d` (no memo on that arm; `abs1C`'s key is
  `(h, k)`, the same shape as `inst1C`'s `(h, d)`).
* **`instantiateListGo`/`instantiateList` is two twins, not one, and the pure one changes its own
  argument between recursive calls.** Its cutoff (`bvarBRaw < satRange && bvarBRaw ≤ d`) is the
  same field `Inst1.lean` already reads, so that part is free. The complication is the
  substitution: con-ron represents it as an `Array EIdx` (push order; the innermost binder's
  argument first is the array's *last* entry), and the memoized `instantiateListGo`'s own `bvar`
  arm does not use its memo at all — it calls the **pure, unmemoized** `instantiateList` on a
  *shorter* suffix of the same array (`lastEidx vs (j - d)`), which the twin's own comment says is
  `O(1)` only because of the SAME cutoff tested again before the recursion (`instListCutoff vi d`,
  hoisted over the prefix copy). Porting this needs an L representation of "a growable list of
  handles" that a recursive function can pass a *shrinking suffix* of cheaply — the natural choice
  is a pool slice (offset, length) exactly as `LsStore.lean`/`PoolSlice.lean` already represent
  level-parameter lists, with `lastEidx`'s shrink becoming an O(1) offset/length adjustment (no
  copy, since the array only ever loses entries from the front in push order) — but that is a new
  piece of shared infrastructure (an `EIdx`-list-in-the-pool reader, with its own `DerR`-style
  frame lemmas), not a one-file port. Brief for the next session: build the pool-slice reader
  first (generic over the element width, the way `MemoLib.lean` generalised memos), then port
  `instantiateList` (no memo, recursion into a shrinking slice) and `instantiateListGo` (the
  memoized wrapper whose `bvar` arm calls the former) as two files following `Inst1.lean`'s split.

### `sorry`s

None.

## The relation's architecture: frames from the text, tiers over projections (2026-10-21, lane `arch`)

Lane `scale`'s "Recommended changes now", items 1–3, applied before the core builds on the shape.

### 1. Write sets from the program text (`L/WriteSet.lean`, `Arena/Frame.lean`, `Arena/WriteSets.lean`)

* `L/WriteSet.lean` (namespace `L`, a `module`): `closedW ctl p A C fs` (a `Bool`): every function
  of the call-closed set `fs` stores only into word arrays of `A` and into words of `C` of the
  control array `ctl` (index a literal `k` or `k + (e & 1)`), no byte stores. `run_frame` /
  `invoke_frame`: every run / call of `f ∈ fs` ends in `Fr m m'`, for any frame relation `Fr` that
  is reflexive and closed under the allowed stores (`WFrame`). `closedW_of_agree`: `closedW` reads
  only the lookups of `fs`, so a program predicate (`LiftProg p`) inherits the concrete program's
  write set. The spike's `Spike/WriteSet{,Inst}.lean` are removed (superseded).
* `Frame.lean`: the arena instance. `closedA p A C fs := closedW CTL p A C fs`;
  `run_memFrame` (→ `MemFrame A C m m'` and the same byte arrays), `invoke_memFrame` (the same as a
  triple, for a caller's `vcgen`); `Stable A C X` (a memory predicate every frame of `(A, C)`
  keeps) and **`run_keeps`**: a `Stable` predicate survives every run, with no lemma about the
  program.
* **The six (in fact 21) `*_push` count stores** now write `CTL[k + (t & 1)]`; the models
  (`apushMem`, …, `pushG`) write `CTL (k + (t &&& 1))`. `pushG_ctl` takes `t ≤ 1` (via
  `and_one_of_le`) and keeps its old right-hand side, so nothing downstream changed: every
  `*Store`/`*Refine` proof and the `#guard`s passed unchanged.
* Write sets, each `by decide +kernel` (≤ 0.5 s), in `WriteSets.lean`: `liftEntry_frame` (`LiftProg p` + `lift_entry`:
  `liftA` = arrays 41‥46 and the six expression tables of `mk_*`, `liftC` = `CTL` 42, 43 and their
  counts), `instEntry_frame` (`instA = 47 :: liftA`, `instC = 44 :: 45 :: liftC`), `bbMemo_frame`
  (`[24]`, `CTL` 24, 25), `frMemo_frame` (`[48]`, `CTL` 46, 47), `storeProg_frame` (`nat_add_lit`/`intern_lit`: pool, `lit`, `CTL` 0, 2, 3).
* Not replaced: front2's `mkAppW_above` … (`ApplyExprRefine.lean`) are frames of the **models**
  (`mkAppW m f x = some (r, m')`), not of runs. A text frame is about runs, and a model's `some`
  does not give a run (no termination argument), so these stay hand-written. A run-level user (any
  refinement theorem stated over `run`, e.g. `liftEntry_run`, `instEntry_run`, `bbMemo_run`) gets
  the frame for free.

**Migration notes (item 1).** (a) A new L program: give it a concrete `*Prog`, a function list
and its `(A, C)`, prove `closedA prog A C fns = true := by decide +kernel`, and for its program
predicate `closedW_of_agree prog_closed (by simp only [fns, List.forall_mem_cons, …]; exact
⟨hp.f₁.trans rfl, …⟩)` (pattern: `WriteSets.lean`). (b) A tier-indexed `CTL` store must
mask the tier: `CTL.u64[k + (t & 1)]`, or `closedW` rejects it. (c) To carry your relation `X`
across a run of `f`: `run_keeps (hp.closed …) (by decide) hX hrun hx` with `hX : Stable A C X`
(for `StateDR`: `fun m m' hf h => StateDR.frame hf (by decide) (by decide) (by decide) h`). (d)
`pushG_ctl` has a new hypothesis `t ≤ 1` (third explicit argument after `hS m t vs j c`).

### 3. The relation by tier, over projections (`ArenaRel.lean`, `Tiers.lean`)

* **`MemosR m a.memos`** (the four walk memos, 10 when complete) is now one nested field
  `ArenaR.memos` instead of four flat fields: `ArenaR` has 20 fields (19 tables and the memo
  group) and stays that size when the remaining six memos land (they go into `MemosR`, 10 fields).
  `DerR` (10 fields) is unchanged; `ArenaD = ArenaR ∧ DerR` stays the walks' tier.
* **Ownership lists and one group frame each**: `storeArrs`/`storeCtl` (the store tier),
  `memoArrs`/`memoCtl` (the memo tier), `arenaArrs`/`arenaCtl` (both). `MemosR.frame`,
  `ArenaR.frame` (a writer that avoids `arenaArrs`/`arenaCtl` keeps `ArenaR`; `frame_above` and
  `frame_ext` are now two-line corollaries), `ArenaR.stable` (for `run_keeps`), and
  `ArenaR.with_memos`: a memo writer keeps `ArenaR` given the new `MemosR` (built with
  `memos_build`, the memo tier's `arena_build`). The four memo set/clear lemmas
  (`ArenaR.memo_set`, `ArenaD.lmemo_set`, …) use it; `arena_build` frames the memo group with one
  `MemosR.frame` instead of four `memoRG_frame`s. `apart_own` turns an ownership list into the
  per-table `Apart`.
* **`Tiers.lean`**: `CoreR m a.caches` (arrays 96‥127, `CTL` 96‥127), `PinsR m a.pins` (128‥131),
  `EnvR m vis fe` (132‥143, `CTL` 128‥135) as stubs (no fields: they claim nothing), each with
  its group frame from the reserved range (`AvoidA`/`AvoidC`), and `CheckR m a vis fe` (the four
  tiers). **`CheckR.of_walk`**: a run with L write set below 64 whose twin side keeps `cp` keeps
  `CoreR`, `PinsR`, `EnvR`. `TierWalks.lean` lifts all four walk entries to `CheckR`
  (`liftEntry_runC`, `instEntry_runC`, `bbMemo_runC`, `frMemo_runC`) with no lemma about the
  walks: the L frame from `WriteSets.lean`, the twin frame from `Keeps.lean`. The memo-only walks
  keep the store too (`Keeps sp`), so `bbMemo_runC`/`frMemo_runC` also get `DerR`, which
  `bbMemo_run`/`frMemo_run` (`ArenaR` only) did not give.
* `ArenaR` and every group stay opaque to `grind` (structures, fields named in proofs).
* Lane `exprops` asked: `Walk.lean`'s `appK₁`/`bindK₁`/`letK₁` and `WalkRefine.lean`'s
  `appArm_ok`/`bindArm_ok`/`letArm_ok` are renamed `bbAppK₁`, …, `bbAppArm_ok`, …; every walk file
  can now be imported together.
* Finding: `omega` does not see through `abbrev ArrId := Nat` (`docs/gaps/omega-abbrev-nat.lean`).

### 2. Twin-side frames by composition (`Keeps.lean`)

`Keeps π op` (irreducible): every successful run keeps `π a`. Closed under `bind`/`pure`/`fail`
and, by `split`, under `if`/`match`. Primitives: the reads and `view` keep anything, the memo
writes keep any `MemoBlind` projection, the interns keep `cp a = (a.caches, a.pins)`. The tactic
`keeps_auto [arms] using ih, blind` does a walk's `succ` case: so each walk family is one
induction of 4 lines (`keeps_inst1Go`, `keeps_liftGo`; `keeps_bvarBoundGo`, `keeps_fvarRangeGo`
keep `sp = (store, caches, pins)`), and each entry 3 lines. This replaces adding `cp a' = cp a`
to the `GoOK` posts: the posts stay as they are, and a new walk proves its `Keeps` by the same
four lines. The spikes `Spike/TwinKeep.lean`, `Spike/WriteSet{,Inst}.lean` are removed.

### The memory map (every array and `CTL` word)

Word arrays (byte arrays are a separate id space: `IN` = byte array 0 is the input buffer).

| array | name | owner (relation) | meaning |
|---:|---|---|---|
| 0 | `POOL` | `ArenaR` (`lit`, `ls`, `nstr` read it) | limb pool: limbs, level lists' handles, names' bytes |
| 1 | `CTL` | – | control words (below) |
| 2, 3 | `REC`, `SLOT` | `ArenaR.lit` | expression `lit` records / cons slots |
| 4, 5 | `AREC`, `ASLOT` | `ArenaR.app` | expression `app` |
| 6, 7 | `SREC`, `SSLOT` | `ArenaR.succ` | level `succ` |
| 8, 9 | `ZREC`, `ZSLOT` | `ArenaR.zero` | level `zero` |
| 10, 11 | `MREC`, `MSLOT` | `ArenaR.max` | level `max` |
| 12, 13 | `IREC`, `ISLOT` | `ArenaR.imax` | level `imax` |
| 14, 15 | `PREC`, `PSLOT` | `ArenaR.param` | level `param` |
| 16, 17 | `SOREC`, `SOSLOT` | `ArenaR.sort` | expression `sort` |
| 18, 19 | `CREC`, `CSLOT` | `ArenaR.const` | expression `const` |
| 20, 21 | `LEREC`, `LESLOT` | `ArenaR.letE` | expression `letE` |
| 22, 23 | `BREC`, `BSLOT` | `ArenaR.bvar` | expression `bvar` |
| 24 | `BMEMO` | `MemosR.bvar` | `bvarBound` memo (`bvarBC`) |
| 25, 26 | `FVREC`, `FVSLOT` | `ArenaR.fvar` | expression `fvar` |
| 27, 28 | `LAREC`, `LASLOT` | `ArenaR.lam` | expression `lam` |
| 29, 30 | `FAREC`, `FASLOT` | `ArenaR.forallE` | expression `forallE` |
| 31, 32 | `PJREC`, `PJSLOT` | `ArenaR.proj` | expression `proj` |
| 33, 34 | `NAREC`, `NASLOT` | `ArenaR.nanon` | name `anonymous` |
| 35, 36 | `NSREC`, `NSSLOT` | `ArenaR.nstr` | name `str` |
| 37, 38 | `NNREC`, `NNSLOT` | `ArenaR.nnum` | name `num` |
| 39, 40 | `LSREC`, `LSSLOT` | `ArenaR.ls` | level lists |
| 41 | `LMEMO` | `MemosR.lift` | `liftLooseBVars` memo (`liftC`) |
| 42‥46 | `ADER`, `LADER`, `FADER`, `LEDER`, `PJDER` | `DerR` | derived bvar ranges of `app`, `lam`, `forallE`, `letE`, `proj` |
| 47 | `IMEMO` | `MemosR.inst1` | `instantiate1` memo (`inst1C`) |
| 48 | `FRMEMO` | `MemosR.fvar` | `fvarRange` memo (`fvarBC`) |
| 49‥55 | – | `MemosR` (reserved) | the other six walk memos |
| 56‥63 | – | reserved (store tier) | (the scratch epoch is `CTL[62]`, no array; lane `libs`) |
| 64, 65, 66 | `NID`, `LID`, `EID` | `StateDR` (front) | the export's name/level/expression id tables, dense part (lane `twinaudit`) |
| 67‥71 | `DECL`, `DLP`, `DIND`, `IFR`, `IFL` | `StateDR` (front) | declaration records, inductive lines |
| 72, 73, 74 | – | `StateDR` (`TblR`) | the id tables' sparse overflow (memo-library tables, `IdTable.lean`) |
| 75 | `HSEEN` | – (per call: `prepare_prelude`'s ground hoist; lane `front3`) | the hoist's expression visited set (memo library, `CTL[73‥74]`) |
| 76 | `HNIX` | – (per call, as `HSEEN`) | the hoist's name index, name handle ↦ first position (memo library, `CTL[75‥76]`) |
| 77‥95 | – | reserved (front) | |
| 96‥127 | – | `CoreR` (stub) | the 14 caches and the eager-depth banks |
| 128‥131 | – | `PinsR` (stub) | the pin table |
| 132‥143 | – | `EnvR` (stub) | the environment index |
| 144‥191 | – | argument relations (reserved) | `PMemo`, walk-local memos, `NestState` |
| 146‥149 | `PNM`, `PLM`, `PLSM`, `PEM` | `PMemoR` (`LoopR.pmemo`) | the promotion's four memos (names, levels, level lists, expressions; lane `decls2-promote`) |
| 192 | `LH` | levels' heap (per call, no relation: scratch) | level-algorithm heap, nodes `[tag, a, b]`, bump-allocated below `CTL[192]` (lane `levels`) |

`CTL` words:

| word | owner | meaning |
|---:|---|---|
| 0 | `ArenaR` (`PoolOK`) | pool top |
| 1 | `ArenaR` (every table) | scratch flag (`≠ 0`: scratch tier open) |
| `r`, `r + 1` for `r` = 2, 4, …, 22 | `ArenaR` | node counts of tiers 0, 1 of the table with record array `r` (2‥23) |
| 24, 25 | `MemosR.bvar` | `bvarBound` memo: stamp − 1, live count |
| `s`, `s + 1` for `s` = 26, 28, …, 40 | `ArenaR` | node counts of the table with slot array `s` (`fvar` … `ls`) |
| 42, 43 | `MemosR.lift` | lift memo: stamp − 1, live count |
| 44, 45 | `MemosR.inst1` | `instantiate1` memo |
| 46, 47 | `MemosR.fvar` | `fvarRange` memo |
| 48‥61 | `MemosR` (reserved) | the other six memos |
| 62 | `ArenaR` (every table, `StoreR`) | scratch slot base `B` (lane `libs`): tier-1 slots hold `B + i + 1`; `scratch_reset` adds `2^32` |
| 63 | reserved | |
| 64‥69 | `StateDR` (`TblR`) | stamp − 1, live count of the id tables' sparse maps (`NID`, `LID`, `EID`) |
| 70, 71, 72 | `StateDR` (`TblR`) | dense size of `NID`, `LID`, `EID` |
| 73, 74 | the ground hoist (lane `front3`) | `HSEEN`: stamp − 1, live count |
| 75, 76 | the ground hoist (lane `front3`) | `HNIX`: stamp − 1, live count |
| 77‥95 | reserved (front) | |
| 96‥127 | `CoreR` (stub) | cache stamps/counts, eager depth |
| 128‥135 | `EnvR` (stub) | environment counters |
| 136‥191 | argument relations (reserved) | |
| 140‥147 | `PMemoR` | stamp − 1, live count of `PNM`, `PLM`, `PLSM`, `PEM` (lane `decls2-promote`) |
| 192 | levels' heap (per call) | the heap top (lane `levels`) |
| 240 | `builtin_prelude` → `prepare_prelude` (lane `pipeline`) | the number of prelude records, `DECL[0‥P)` (the prelude's parse has no id tables of its own any more: arrays 208‥213 and `CTL[241‥249]` are free of it; 208 is `MCM`) |

A count store writes `CTL[k + (t & 1)]` (item 1). `arenaR_init` needs `CTL` ≥ 64 words; the
reserved tiers will raise that when they get fields.

### Measurements (`lake env lean`, user CPU, one run, this machine under load)

* The 21 `*Store.lean` and 19 `*Refine.lean` files: unchanged (±0.2 s each, +2 lines per store
  for the masked count), total 56 affected files 261 s before, 262 s after (noise).
* `ArenaRel.lean`: 975 → 1024 lines (the ownership lists, `MemosR`, `apart_own`, the group
  frames), 23.0 s → 22.9 s. A first version that proved the ownership side conditions twice per
  table cost 25.9 s; `ArenaR.frame` now goes through `with_memos`.
* Memo users (`WalkRefine`, `LiftRefine`, `Inst1Refine`, `FVarRangeRefine`): +3‥4 lines each,
  1.58/1.92/1.91/1.23 s → 1.23/1.57/1.65/1.2 s.
* New: `L/WriteSet.lean` 200 lines 1.0 s; `WriteSets.lean` 168 lines 2.2 s (five `decide +kernel`
  write sets); `Keeps.lean` 201 lines 16.8 s (`keeps_auto` on four walk families; the slowest is
  `instantiate1Go`, ≈ 6 s); `Tiers.lean` 100 lines 0.5 s; `TierWalks.lean` 70 lines 0.7 s.
  Removed: the spikes `WriteSet{,Inst}.lean`, `TwinKeep.lean` (373 lines).
* Lifting a walk to `CheckR`: about 8 lines (`TierWalks.lean`), none of which looks at the walk.

**Migration notes (items 2, 3).** (a) `hR.memo`/`.lmemo`/`.imemo`/`.fmemo` are now
`hR.memos.bvar`/`.lift`/`.inst1`/`.fvar`. A new memo: a field of `MemosR` (and its row in
`memoArrs`/`memoCtl` and the map above), not of `ArenaR`; `memos_build` and `MemosR.frame` get one
line each. A memo writer: `exact hR.with_memos hf (by apart) (by apart) (by memos_build hR.memos,
hf with exact memoRG_set …)` (pattern: `ArenaR.memo_set`, `WalkRefine.lean`). (b) A writer outside
the arena: `ArenaR.frame` with `∀ b ∈ A, b ∉ arenaArrs` (`by decide` for concrete `A`; for `CTL`
words above 63 `not_mem_arenaCtl`). (c) A new walk: prove `Keeps cp` (or `Keeps sp` if it interns
nothing) by `induction F` + `keeps_auto [arms] using ih, cp_blind` (`Keeps.lean`), its write set in
`WriteSets.lean`, and its `*_runC` in `TierWalks.lean` is three lines. (d) A new tier relation:
a structure over the projection it reads, arrays from its reserved range above, one `frame`
lemma from `AvoidA`/`AvoidC`, a field of `CheckR`. (e) `Walk.lean`'s continuations and
`WalkRefine.lean`'s arm lemmas are renamed with a `bb` prefix.

### `sorry`s

None. The stubs `CoreR`, `PinsR`, `EnvR` have no fields (they claim nothing yet).

## Progress census (2026-10-21, lane `census`)

Hard numbers for planning: `scripts/census.py` (PLAN.md, "Progress census"). Pieces:
`ConAgua/Census/Attr.lean` (the three attributes, an environment extension of links),
`ConAgua/Census/Main.lean` (`lake exe census`: targets and links as TSV), `scripts/census.py`
(weights, coverage, report), `scripts/census-rust.tsv` (Rust lines per cited twin, regenerated with
`--rust <con-ron checkout>` from the `Lean twin:`/`con-leche:` doc lines), `docs/progress.{md,csv}`.

### Decisions
* **Targets are computed, not listed.** Every `ConRon.*`/`ConLeche.*` definition reached from
  `ConAgua.Final.TwinAccepts` through definition values (not types, not proofs), walking through but
  not counting instances (and the functions `deriving` makes inside them), elaborator/compiler
  auxiliaries, projections, and `ConAgua`'s own glue predicates (`SeqAccepts`); not walking into type
  formers or `Prop`-valued definitions. Members of a well-founded mutual block are edges of each other
  (they call each other through `_mutual`, which names no member: without this the walk missed every
  `liftArm*`). Opaque (`partial`) definitions are followed through `@[implemented_by]`. ROM modules
  (con-leche's basis/axiom/pin data, `Frontend.PreludeText`) are not targets. 1350 targets; con-ron's
  own census counts 1632 arena definitions in all (some unreached, e.g. `Bench`, `Denote`).
* **Instances need `loadExts := true`** on `importModules` (and so `enableInitializersExecution`):
  without it the instance table is empty and every `instDecidableEq…` counts as a target.
* **Links by attribute, target names unresolved.** Most L files are `module` files that cannot import
  con-ron, so `@[l_impl T]` stores `T` as written; the tool reports a link whose `T` is not a target,
  an `l_impl` not on a `FunDecl` and a `refines` not on a theorem as bad links.
* **Proven = complete, sorry-free refinement; parts never count**, except where
  `COMPLETE_BY_PARTS` lists the arms that make up a target (`internE` = ten `refines_part` arms,
  `internLNode`, `internNNode`, `parseNameEntryD`). A target reached only through proven targets is
  proven ("covered": the store helpers under `internLNode`, the arms under `liftLooseBVarsFast`).
  Coverage does not apply to `written`: `frontRun` is linked to `parseBytes` but aborts on declaration
  lines, so `validateIndD` is not written.
* **Weights**: Lean code lines of the twin definition (no blanks, comments, doc comments, nested
  targets), and Rust lines of the con-ron functions citing it.

### Findings
* `ConAgua.Arena.Walk` and `ConAgua.Arena.Lift` both declare `L.Arena.appK₁.appK₂` (and the emitters
  each declare `main`): no module can import both walks. The census imports in greedy groups to
  work around it; the first lane that needs both must rename one.
* "Proven" is against the relation as it stands (`ArenaR` without derived columns, scratch flag,
  memos beyond `bvarBC`) and in the accept direction only (an L function that always aborts refines
  anything). The `refines`/`refines_part` choice is where completeness is recorded; it is a human
  judgement, so reviewers should check it.
* `internLit_refinesA` covers `.natVal` literals only, so `internE`/`internNodeE` are not complete;
  `internLamE`, `internForallEE`, `internLNode`, `internNNode`, `internLsNode` are.
* The Stage B scanner functions that return a record are refined in their validity and end position
  only (`refines_part … "validity"`); the position-valued ones (`skipWs`, `keyAt`, `strClose`, …) and
  `scanBool` are refined completely.

### Numbers at landing (master `59d93f8` + census)
1350 targets: 91 proven, 0 with `sorry`, 40 with L code only, 1219 nothing; by Lean lines 905 of
11902 proven (7.6 %), 1388 with L; by Rust lines 1413 of 30758 (4.6 %). 89 `refines_part` theorems
(among them all twelve `natOpResult` literal arms and 18 of the 19 store arms).
Per phase in `docs/progress.md`. The census takes about 30 s (the link pass imports the modules in a few groups; axioms come
from the oleans' precomputed tables).

## Levels: the scratch heap and the level algorithms (2026-10-21, lane `levels`)

Phase 3 (ROADMAP §1, `kernel/level.rs`): con-leche's pure `Level` algorithms that the twin runs on
read-back trees (`Level.isEquiv`, `leq`, `simplify`, `subst`, …), translated into L over a scratch
heap. Files: `ConAgua/Arena/Level*.lean` (other than the store files `LevelStore`/`LevelRefine`).

### The heap, and why the readback is free (`LevelHeap.lean`, `LevelHeapRel.lean`)

* **Pointers.** A level pointer is a word: below `2^32` a store handle (the level store's tags
  0‥4 in bits 31…28, tier bit 27, index), at or above `2^32` heap node `p - 2^32`. The heap is the
  word array `LH` (array **192**) of three-word nodes `[tag, a, b]` with the store's tags (`a` a
  name handle word for `param`; unused fields `0`), bump-allocated below the top `CTL[192]`.
  `lv_node(p)` views either kind (`abort` on a dangling pointer), `lh_mk(g, a, b)` allocates.
* **No readback, no tree cache.** The twin reads a handle back into a `Level` (`readLevelM`, cached
  in `readLC`) and runs the algorithm on the tree. L runs the algorithm on the handle itself and
  allocates heap nodes only for what the algorithm builds, so a store DAG is never copied, and
  `readLC`/`readNC`/`readLsC` need no L table: their rows equal `denoteL`/`denoteN` of the
  handle, which is all a refinement needs to know about them (lane `scale`'s "tree-valued caches"
  item is moot for levels). The heap is reset by the entry of each comparison (per call, ROADMAP
  §2 item 5), not per declaration.
* **The decoder is an inductive relation** `LvR N m p l` (a constructor per tag, children
  related recursively, `param` names through `N : Word → Name → Prop`, functional and injective:
  `NameRel`). It needs no fuel and holds only along finite views; `LvR.fn` (a pointer denotes one
  level) is an induction. Under `ArenaR`, `N` is the store's name readback; store handles are
  related through the store's tables, heap nodes through `LH`.
* **Growth.** `HeapExt m m'` ("every view of `m` is a view of `m'`") carries `LvR` (`LvR.mono`);
  `HeapFrame` (store arrays, `CTL` words other than 192, the heap below the top) implies it, and
  `lhMkW_ext` gives it for an allocation. The new node's view is the written one.
* `lv_eq(p, q)` is `Level.beq` (`decide (l = r)`): pointer equality first, then tags, `param`
  names by word (injectivity of `N`), children recursively. `lvEqW_ok` (`@[refines
  ConLeche.Level.beq]`).

Note for lane `libs` (MemoLib tree values, a per-declaration tree heap): the level algorithms do
not need it. Their heap is per call and holds intermediate trees; the readback caches it would
serve are not represented for levels at all (above). If the tree heap lands with the same node
shape, `lv_node` can view it as a third pointer kind.

Hypotheses left for the callers (no `sorry`): see `lvl_eq` below.

Request to lane `arch`: add `LH` (array 192) and `CTL[192]` (heap top) to the memory map, owner
`levels` (per call, no relation: the heap is scratch, nothing in `AState` corresponds to it).

### Per function

| function | Rust lines | L lines | spec lines (model + arms + spec) | refinement lines | `lean` user | automation |
|---|---:|---:|---:|---:|---|---|
| `lv_node` (view) | – (store `view` / tree match) | 23 | 50 | `HeapFrame.ext` 60 | | `vcgen` + `finish` |
| `lh_mk` | – (`Rc::new`) | 9 | 25 | `lhMkW_ext` + `lhMem_*` 110 | | `vcgen` + `finish`; frames by hand |
| `lv_eq` (`Level.beq`) | 19 (`beq`) | 11 | 70 | `lvEqW_ok` 115 | | `vcgen` + `finish (gen := 20)`; refinement by hand (cases per tag) |
| `lv_comb` (`combining`) | 10 | 13 | 70 | `combW_ok` 50 (+ allocation lemmas 27) | | as `lv_eq` |
| `lv_simp` (`simplify`) | 21 | 16 | 130 | `imaxW_ok` + `simpW_ok` 120 | | as `lv_eq` |
| `lv_nz` (`isNeverZero`) | 9 | 12 | 70 | `nzW_ok` 40 | | as `lv_eq` |
| `lv_subst` (`subst [k] [v]`, one key) | 24 (`subst`, `subst_go`) | 10 | 80 | `substW_ok` 60 | | as `lv_eq` |
| `lv_subsimp`, `lv_dist1`, `lv_dist2` (operand builders) | in `by_cases`, `imax_rules_distrib*` | 17 | 100 | `ssW_ok`, `dist1W_ok`, `dist2W_ok` 55 | | as `lv_eq` |
| `lv_leq` (`leqCore`) | 15 | 9 | | `leq_ok` 22 | | |
| `lv_rest` (`rest`) | 37 | 27 | | `rest_ok` 130 | | |
| `lv_imax`, `lv_imax_l`, `lv_imax_r` (`imaxRules`) | 88 (`imax_rules`, `by_cases_left/right`, `imax_rules_distrib*`) | 32 | | `imax_ok` + `imaxL_ok` + `imaxR_ok` 105 | | |
| `lv_cases`, `lv_cases_at` (`byCases`) | 19 | 15 | | `cases_ok` + `ca_ok` 65 | | |
| the comparison group (7 functions, one mutual model) | 159 | 83 | `LevelLeq` 474 (models, 49 arm lemmas), `LevelLeqSpec` 151 | `LevelLeqRel` 740 (incl. 30 equations of con-leche's arms, 60) | 3.7 + 35 s, 4.2 s | `vcgen` + `finish (gen := 20)`; refinement by hand |
| `lv_leq_top` (`leq`, `defaultFuel`) | 6 | 6 | 30 | `leqTopW_ok` 25 | | as `lv_eq` |
| `lv_equiv` (`isEquiv`) | 16 | 12 | 70 | `equivW_ok` 70 | | as `lv_eq` |
| `lv_equivs` (`isEquivList`, lists in `POOL`) | 20 | 7 | 50 | `equivsW_ok` + `LvsR` 75 | | as `lv_eq` |
| `lvl_eq` (`lvlEq?`: heap reset, then `lv_equiv`; the verdict cache not in L) | 33 (`lvl_eq_q`) | 5 | 25 | `lvlEq_refines` + `lvlEq?_run` + `lvlEq_run` 110; the view bridge (`lvNodeW_store`, `denoteL_lvR`) 190 | 1 s | `vcgen` + `finish`; bridge by hand |
| `lvls_eq`, `ls_node` (`lvlsEq?` on two level-list handles' `POOL` slices) | 33 | 15 | 60 | `lvlsEq_refines` + `lvsR_of_slice` + `lsNodeW_store` + runs 170 | 1 s | as `lvl_eq` |
| `lv_mem`, `lv_apd` (`allParamsDefined`; the parameter names a slice of a word array `A` the caller picks) | 12 | 18 | 90 | `memW_ok`, `apdW_ok`, `NmsR` 75 | 2.9 s | as `lv_eq`; L code generic in `A` |
| `lh_push`, `lv_zero` (`zeronessOf`: a flag and the names pushed on the heap) | 13 | 18 | 90 | `zeroW_ok` + `lhPushW_ext` + `NmsR` slices 150 | 1.8 s | as `lv_eq` |
| `lv_lookup`, `lv_substl` (`subst`, `subst.go` with lists: keys in `KA`, values in `VA`) | 24 | 25 | 110 | `lookupW_ok`, `substLW_ok`, `LvsAR` 110 | 5.9 s (file) | as `lv_eq`; generic in the arrays |
| `lv_spw`, `lv_substpw` (`substPW`: `bindZ.go` of `zeronessOf ∘ subst.go`) | 3 + `bind_z` | 15 | 70 | `spwW_ok`, `substPWW_ok`, `ZR.inter`, `PWR` 120 | (same file) | as `lv_eq` |
| total (files) | | 328 | `LevelHeap` 243, `LevelSimp` 291, `LevelSubst` 251, `LevelLeq` 474, `LevelLeqSpec` 151, `LevelEquiv` 358, `LevelApd` 120, `LevelZero` 120, `LevelSubstL` 230 | `LevelHeapRel` 470, `LevelSimpRel` 264, `LevelLeqRel` 740, `LevelEquivRel` 200, `LevelArena` 552, `LevelApd` 100, `LevelZero` 190, `LevelSubstL` 280 | | |

### The comparison (`LevelSubst`, `LevelLeq`, `LevelLeqSpec`, `LevelLeqRel`)

* **Encodings.** The answer `Option Bool` is a word (`0` none, `1` false, `2` true, `encO`).
  con-leche's fuel is the word argument `f`, decremented exactly where `leqCore`'s `fuel + 1`
  pattern is: **the `10^4` counter is exact** (ROADMAP §3 (b)), and at `0` the answer is `none`,
  which every caller sees. `diff : Int` is the biased word `d = diff + 2^32` (`DR`); the
  refinement keeps `|diff| + fuel ≤ 2^31`, true from the entry (`0`, `10^4`) since `diff` moves
  by one only where fuel is spent, so `d ± 1` never wraps.
* **One key, and lists.** `byCases` substitutes one parameter; `lv_subst(l, k, v)` is
  `subst [k] [v]` (`@[refines_part … "one key"]`). The list version `lv_substl` (`instLPGo`'s
  callers, phases 4–5) takes the keys as a slice of name words in an array `KA` and the values as
  a slice of level pointers in `VA` (`LvsAR`), both chosen by the caller (`LevelSubstL.lean`);
  `substPW` (`lv_substpw`) runs over a datum's name slice in `PA`. The arrays must not be the heap
  or `CTL`.
* **The model** is one mutual block (`leqW`, `restW`, `imaxRW`, `imaxLW`, `imaxRrW`, `casesW`,
  `caW` and 14 continuations), structural on the L fuel with the continuations ranked by a second
  component (`termination_by (n, k)`). The refinement is the same mutual induction: seven
  predicates (`LeqOK` … `CaOK`), one lemma each, with con-leche's overlapping `match` arms restated
  as guarded equations over the tags (`LevelEq.rest_*`, `im_*`, by `unfold; split <;> simp_all`).
* **The entries** (`LevelEquiv`, `LevelEquivRel`): `lv_leq_top` (`leq`: fuel word `10000`,
  bias `2^32`), `lv_equiv` (`isEquiv`, simplifying each side once where con-leche's `leq`
  simplifies again, to equal levels), `lv_equivs` (`isEquivList` over two `POOL` slices of level
  pointers, `LvsR`; a length mismatch answers `false` only after the common prefix compared
  `true`, as con-leche's). All three refinements went through at the first attempt.
* **Under `ArenaR`** (`LevelArena.lean`, not a `module`: it reads con-ron's store): L's view of
  a level handle is the arena's (`lvNodeW_store`, one case per tag over the five level tables'
  `StoreR`), so `denoteL` of a handle is related to its word (`denoteL_lvR`, by induction on
  `denoteLAux`'s fuel) with the name decoder `nameN` (the store's `denoteN` on handle words),
  which is a `NameRel` under con-ron's `NStoreWF` (`denoteN_inj`).
* **`lvl_eq(u, v)` refines `lvlEq?`** (`lvlEq_refines`, `lvlEq_run` from a run of `levelProg`).
  Hypotheses, as lane `nat2` did for pins: `NStoreWF` of the name store, the two readbacks
  defined, and the twin's caches holding what they claim (`ReadLCOK`: every `readLC` row is the
  readback; `LvlEqCOK`: a `lvlEqC` row at `(u, v)` is the verdict). L keeps neither cache: it
  recomputes, which the twin's cache returns unchanged; the twin's state after differs only in
  `caches` (`ArenaR.with_caches`), L's only in the heap (`HeapExt.memFrame`, write set
  `levelProg_closed`: `[LH]`, `CTL` `[192]`, by `decide +kernel`). When `CoreR` gets `lvlEqC`,
  the L cache goes in front of `lv_equiv` and `LvlEqCOK` becomes a field of the relation.
  `lvls_eq(us, vs)` (`lvlsEq?`) is the same over the two lists' `POOL` slices (`ls_node` reads a
  level-list record; `lvsR_of_slice` relates the slice to the readbacks), with `ReadLsCOK`,
  `LvlsEqCOK`.
* **Name lists and the zero-ness datum.** `allParamsDefined`'s parameter list is a slice of name
  words in an array the caller picks (`lvMemG A`, generic like the memo library's schemas;
  `NmsR`). `zeronessOf` returns `never` or `ifAllZero ps`: in L a flag and the name words pushed
  on the heap since the call (`lh_push`; `ZR`), which a caller copies into its record
  (`EnvRec.lean`'s `decPW` layout). `HeapExt` now also says the heap below the old top stays
  (`HeapExt.lh`, `top`), so a pushed slice survives later allocations (`NmsR.mono_lh`).
* **Inversion by tag** (`LvR.inv0` … `inv4`: from `lvG m p = t`, the level's constructor and the
  children's relations) replaced `cases` on the derivation, whose impossible branches made
  `simp_all` loop.

### Findings

* **Split large L functions.** `lv_imax` as one function (two `byCases` arms and four
  distribution arms, three re-reads of a child's view, 14 locals) gave `vcgen` verification
  conditions with ~5000 lines of context; `finish (gen := 20)` failed after 6 min CPU. Split into
  `lv_imax`/`lv_imax_l`/`lv_imax_r` (each a tail call to the next), the whole spec file
  (seven functions) takes 35 s. The model and the refinement follow the split one-to-one.
* `simp` on goals with `UInt64` literals such as `p - 4294967296 + 3` produced proofs on which the
  **kernel** hit "deep recursion" (elaboration was fine); stating the arithmetic once as lemmas
  (`heap_sub`, `heap_off`, `heap_below`) and using `rw` + `omega` avoids it. Likewise `decide`
  on `(1 : Word) ≠ 192`: use `simp`.
* `finish` failed on `lv_eq` (a wrong case split, no hint) until `(gen := 20)`, as lane `exprops`
  found for three callee posts.
* The refinements are short because the decoder is a relation: each is one induction on the L
  fuel and one `cases` on the argument's `LvR` derivation, whose constructor fixes the view's tag
  (`lv_fields`), and the twin's `match` reduces by `simp [Level.f]`. Allocations are three lemmas
  (`mk_succ`, `mk_max`, `mk_imax`). The first full drafts of `combW_ok`/`simpW_ok`/`nzW_ok` took
  three rounds of small fixes; no `grind` in the refinements.
* Two `match`es with the same arms but different auxiliary matchers (`simplify`'s `imax` arm and
  a restatement) are not syntactically equal; `cases` on the discriminant and `rfl` closes it.
* The model's view fields are named (`lvG`/`lvA`/`lvB` with `@[level_grind =]` equations to the
  `headD` projections the call's `setLocs` produces); a model that unfolded them in `finish`'s
  list confused `grind`.

### Census at the end of the lane

Phase 3: **16 of 16 targets proven** (0 before; 102 Lean / 291 Rust lines). Also `Level.beq`
(phase 0) and `lvlEq?`, `lvlsEq?` (phase 5, under the cache hypotheses above). Totals on master at
the last landing (all lanes): 267 of 1350 proven, 10.7 % of Lean lines, 7.3 % of Rust lines (91,
7.6 %, 4.6 % when the lane started).

### `sorry`s

None.

## Pins, the environment, the declaration loop (2026-10-21, lane `pinsenv`)

### The pin table (`Tiers.lean` `PinsR`, `Pins.lean`)

`PINS` (array 128) holds the twin's `Pins`: word 0 a ready flag, words `1‥51` the 51 name slots
(`PIN_*` at `1 + PIN_*`), 52‥54 `emptyLevels`/`zeroLevel`/`sortOne`, 55‥70 the 16 reserved names.
`PinsR m p := flag ≠ 0 → PinsFull m p` (sizes, words below `2^32`, every field `decI` of its
word). Every reader checks the flag and aborts on `0`, where the twin's empty table raises
`.internal`, so the relation claims nothing before the driver fills it, and all-zero memory is
related to `Pins.empty` (`PinsR.of_flag`). Frame: `PinsR.congr` (array 128 unchanged).

* `pin_at(i)` (flag, `i < 51`, word `1 + i`) refines `pinAt` (`pinAt_refines`, post: memory
  unchanged, `(pinAt i).run a = .ok (decI r, a)`); `pin_word(k)` the three interned values. The
  88 named readers (`pinNat`, …, Core's `natAddName`, `boolTrueName`, `emptyLevels`, …) are one
  line each (`PinSlotSpec`/`PinWordSpec`), generated.
* Twin side: `pinAt_run`, `pinEmptyLevels_run`, … (`simp` with the `StateT`/`Except` unfoldings;
  `rfl` alone does not see through the `do`).

### `natOpResult`, the whole dispatch (`NatArms.lean` `natOpResultL`, `PinsNatOp.lean`)

`nat_op_result(c, oa, la, ob, lb)` is in `natArmProg` (so lane `nat2`'s arm theorems apply
verbatim): the flag, then fifteen `c == PINS[k]` tests in the twin's order, each calling its arm;
`beq`/`ble` get `PINS[31]`, `PINS[32]`, `PINS[52]` (the pins nat2 took as arguments, whose
hypotheses `hT`/`hF`/`hE` are now discharged from `PinsFull`). Returns `(1, h)` / `(0, 0)`
(`decOpt`). `natOpResult_sel`: under `PinsFull` the twin runs as `natOpSel`, the same chain on
word equality (`decI_beq`: handle words below `2^32`). `natOpResultL_refines` (`@[refines
ConRon.Arena.natOpResult]`) is one `vcgen` over the sixteen arms with the arm specs as terms and
`finish`; it needs `maxHeartbeats 2000000` (≈ 17 s; the default runs out in `whnf` inside
`finish`, not a failing search). The conditional facts (`hok`/`hst`/`hres`: `natOpResult` =
`natOpSel` when the flag is set) are given as implications, so the flag-zero abort path needs no
case split.

### The environment (`Tiers.lean` `EnvR`, `EnvRec.lean`, `Env.lean`)

**Decision: the name → constant index is directly addressed by the name handle, not hashed.** A
name handle is `tag · 2^28 + tier · 2^27 + i` with `tag` ∈ {0, 1, 2} (`anonymous`, `str`, `num`),
so its row is words `4 i + 2 tier` and `+ 1` of `EIXA`/`EIXS`/`EIXN` (132 + `tag`): the counter
plus one (`0`: no row) and the record pointer. Lookup is two reads, `erase` writes `0`, there
are no tombstones, no probe sequences, no load factor, and the relation needs no hashing argument
(the one fact about a write is `rowC_rowSet`: rows of other names stay, from `rowIx_inj`). Cost:
two words per name *slot* in each tier (the arrays are sized like the name tables; an index past
the end is a capacity abort), against ≈ 3 words per *entry* at 3/4 load for open addressing; on
`Init` (~10^6 names, ~4·10^5 constants) both are tens of MB. So the env index needs no deletion
from lane `libs`' map library (note for `libs`: the env is not a client of deletion; tree-valued
caches and the bank stack still are).

* `ECON` (135): the record pointer of every constant by position, oldest first, `CTL[128]`
  entries; the twin's `env.consts` (newest first) is its reverse. `EREC` (136) is the record pool,
  `CTL[129]` its top (no writer yet: the installers build records there).
* **Records** (`EnvRec.lean`): `IConstantInfo`, `IDeclaration`, `ValueGroup` as word runs in a
  pool, lists as `(off, len)` slices of the same pool, rule lists as slices of 11-word records, an
  inductive block as a slice of record pointers; decoders `decCI`, `decDecl`, `decVG` (value
  relations, `Option`-valued; a handle word must be below `2^32`). Word `p + 1` of a constant
  record is always its index key (`ci.name`, `decCI_name`). `PropWhen`'s names are name handles
  in L, read back by a parameter `dn` (the consumers relate it to the store's `denoteN`); so
  `EnvR` and `CheckR` take `dn`.
* `EnvR dn m vis fe`: `fe.visibleBelow = vis`, every row's presence and counter is the twin's
  (`idx[n]?.map fst`), every present row's record decodes to the twin's constant, and the
  constants decode in order. Extensional through `idx[n]?`, so layout and history are free and
  `find?` (`EnvR.find?_eq`) and the raw row (`GenRec`'s `prev`) both follow.
* Refined (`@[refines]`): `IFEnv.find?` (`env_find`), `IFEnv.push` (`env_push`, the name read from
  the record), `IFEnv.popTemp` (`env_pop_temp`, the previous row passed as two words that decode,
  `prevD`), `IFEnv.restrictTo` (no code: `EnvR.restrictTo`). Also `env_erase` (`HashMap.erase` on
  the index, a step of `eraseInstalled`), `EnvR.init` (`mkIFEnv IEnv.empty` on zero memory), the
  generic `EnvR.setRow` and `EnvR.popLen`, and the write set `envProg_closed` (rows, `ECON`,
  `CTL[128]`: by `decide +kernel`, so every other tier survives an env write by its frame).
* Proof shape: L side `vcgen` + `finish` with the twin facts given as implications in the context
  (`key := fun ht hb … => EnvR.push …`); the twin side by hand (≈ 60 lines for `push`, the
  constants list by `List.range_succ` and `mapM_congr'`). Findings: `omega` hung (> 100 s, not a
  heartbeat timeout) on the 2^27/2^28 decomposition with `UInt64.toNat` atoms in context; stated
  over plain `Nat` (`nat_rowIx_inj`) it is instant. `split_ifs` is Mathlib (not here). The row
  index computed inline in each function made `finish` chase bit-vector normal forms; moving it
  into `env_ix(w)` with a spec `(tagW w, ixW w)` (two opaque words with `toNat` facts) fixed it.

## Library work before the core: the scratch lifecycle (2026-10-21, lane `libs`)

Lane `scale`'s recommended item 4, first half. Files: `StoreLib.lean`, `Store.lean` and the 18
other `*Store.lean`/`*Refine.lean` (the probe and the append, mechanically), `Frame.lean`
(`Apart`), `ArenaRel.lean` (`storeCtl` gets 62), new `Scratch.lean` (L) and `ScratchRefine.lean`.
No `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`.

### Epoch-stamped scratch slots: a slot base

`SlotsOKG` required every slot of a tier to be at most its count, so emptying the scratch tier
meant zeroing every scratch slot of 19 tables per declaration. Now a slot of tier `t` holds
`B t + i + 1` for node `i`, with `B 0 = 0` and `B 1 = CTL[62]` (`SCB`, `baseW m t =
CTL[62] * t`), and a slot word at or below the base reads free (`slotV`/`slotRd`). Raising `B` by
`2^32` empties the scratch tier of every table at once: old scratch slots hold at most `B + 2^27`.
For tier 0 nothing changes (`B 0 = 0`: `slotV … 0 x` is the raw word).

* **L, per table** (19 × 5 lines, by script): `*_find` loads `b := CTL.u64[62] * t`, tests
  `v <= b` instead of `v == 0` and continues with `v - b`; `*_push` stores `CTL.u64[62] * t + c +
  1`. Models take the base (`aprobeW … t f a b n j d`); the probe-arm lemmas state `sl[k] ≤ b` /
  `¬ sl[k] ≤ b` and `sl[k] - b - 1`. Every `vcgen` spec went through unchanged except for adding
  `ld64`/`baseW` to its lists. `#guard` memories need a `CTL` of 63+ words (and `harness/walk.c`
  now allocates 64).
* **The library**: `slotW` reads through the base; `pushG` writes `baseW m t + c + 1`; new
  `slotV_pushG`/`slotV_new`/`baseW_pushG` (`store_grind`) replace `pushG_slot` in the generic
  proofs (one lesson: state the slot read after an append over the **address** `j * 2 + t`, as
  `slotV … x`, so congruence closes the run arguments; a lemma over `slotW S m t j` with a
  condition `j' * 2 + t' = j * 2 + t` left `grind` without the injectivity it needs). `StoreR`'s
  first conjunct is now `count room ∧ CTL[62] < 2^63`; `Schema.WF` gets `scb` (`ca`, `ca + 1`
  avoid 1 and 62); `Apart` gets `SCB ∉ C`; `tierR_mono` takes `baseW m' t = baseW m t`.
* **`storeR_reset`** (library): a memory whose arrays, pool top and tier-0 count are unchanged,
  whose base rose by `2^32` from below `2^62`, tier-1 count `0` and flag `on'`, relates the same
  persistent table and `Tbl.empty`. No slot is read: the old `SlotsOKG` bound gives the
  freedom of every old slot against the new base.

### The bracket (`Scratch.lean`, `ScratchRefine.lean`)

* `scratch_reset(f)`: `B += 2^32` (abort at `B ≥ 2^62`: 2^30 declarations), `CTL[1] := f`, the
  19 tier-1 counts `:= 0`. `scratch_enter()` = reset(1) + the four walk memos' clears;
  `scratch_drop()` = reset(0). `@[l_impl]`: `enterScratch`, `dropScratch`,
  `EStore.enableScratch`/`dropScratch`.
* `ArenaD.reset`: under `ArenaD`, `resetMem m f` relates `{a with store := EStore.reset a.store (f
  != 0)}` (enable or drop: all four stores' scratch tables emptied and flags set): 19
  applications of `storeR_resetMem` (one line each, generated), the pool, the memo frame, the
  derived ranges (persistent unchanged, scratch empty). `ArenaD.enter` adds the four clears.
* `scratchEnter_refines`/`scratchDrop_refines` (`ArenaD`) and `…_refinesC` (`CheckR`: `CoreR` is a
  stub, so `flushCaches` is free for now; pins and environment by their frames).
  `scratchProg_closed`: write set `CTL` words only, `decide +kernel`.

### Measurements (`lake env lean`, user CPU, one run, machine under load)

| file | lines before → after | user s before → after |
|---|---:|---:|
| `StoreLib.lean` | 699 → 786 | 9.1 → 9.7 |
| `Store.lean` (`lit`) | 549 → 579 | 9.4 → 10.2 |
| `AppStore.lean` (typical table) | 303 → 307 | 8.9 → 11.3 |
| `AppRefine.lean` (typical relation) | 230 → 230 | 1.2 → 1.2 |
| `ArenaRel.lean` | 1024 → 1024 | 23.6 → 24.4 |
| `Scratch.lean` (new) | 165 | 4.9 |
| `ScratchRefine.lean` (new) | 347 | 1.4 |

Every table's L code grew by 3 lines (a base load, a free test, a subtraction), each relation file
by 0–4. The 19 tables were converted by a script (`*probeW` argument insertion, arm lemmas, L
loop, push); all 38 files built at the first attempt after the library was fixed.

### For the core lanes: how to use

* A **new table**: write `*_find` with `b := CTL.u64[62] * t` and the `v <= b` / `v := v - b`
  test, `*_push` with `CTL.u64[62] * t + c + 1`, the model with a base argument; pass
  `(baseW m t)` in the `probeArm` bridge and `(baseW m 0)`/`(baseW m 1)` in `internW`; add the
  table to `scratchCnts`/`scratch_reset` (its `ca + 1`) and one line to `ArenaD.reset`.
* The **declaration bracket**: call `scratch_enter` / `scratch_drop`; use `scratchEnter_refinesC`
  / `scratchDrop_refinesC`. When `CoreR` gets fields, `flushCaches` becomes the 14 caches' clears in
  `scratch_drop` (and `CheckR.of_bracket` needs the `CoreR` of the empty caches).
* **Tree heap (note for lane `levels`)**: lane `levels` built its own level heap (`LH`, array
  192, `CTL[192]`) with pointers that may be store handles, so `readLC` needs no L table. The library
  side for tree-valued memo entries is a memory-reading value relation (next section).

### `sorry`s

None.

## Library work before the core: memos with tree values, deletion and banks (2026-10-21, lane `libs`)

Lane `scale`'s item 4, second half. Files: `MemoLib.lean` (L: `X_erase`, `X_bank_enter`,
`X_bank_leave`), `MemoLibRel.lean` (the relation generalised), new `MemoBank.lean`,
`MemoTree.lean`; one argument added at the four `memoRG_hit` call sites (`WalkRefine`,
`LiftRefine`, `Inst1Refine`, `FVarRangeRefine`). No `sorry`; standard axioms.

### Tree-valued entries: `MemoRV`

`MemoRV S K VR m mp` replaces the word decoder `dv : Word → ν` by a **value relation that may read
memory**, `VR : Mem → Word → ν → Prop` (a live slot's word `w` denotes `mp`'s value: `MemoV VR m
w mp[k]?`). `MemoRG S K dv` is now `MemoRV` at `fun _ w v => v = dv w`, and its six lemmas are
one-line corollaries with the old statements (`memoRG_hit` takes `K.ok k1 k2` as a last argument,
see deletion). What an instance with a memory-reading relation proves once is `VStable S VR`
(the relation survives the memo's own writes); `memoRV_frame` takes the relation's transport
across any other writer (`HeapExt` for a growing heap).

The client (`MemoTree.lean`): values are lane `levels`' level pointers, decoded by `LvR N m p l`.
`lvNodeW_congr` (what `lvNodeW` reads: `LH`, the four level record arrays, `CTL` words below 16
and 192) gives `lvR_stable` for any schema outside them (`TreeSafe`; through `LvR.of_view`, since `HeapExt` now also frames every other array), and `memoRV_heapExt` carries
the memo across `lh_mk`. `lt_set`/`lt_hit` instantiate it for a test schema of `readLC`'s shape
(`ltSch`: array 100, `CTL[100]`, inside `CoreR`'s reserved range, not claimed by `CoreR`). Since
lane `levels`' pointers include store handles, `readLC` can store the handle itself; `readNC`
and `readLsC` take the same route once names and level lists have pointer decoders.

### Deletion: tombstones in `MemoLib`, no separate map library

Decision: `X_erase(j)` overwrites the first key word of the live slot `j` a probe found with
`TOMB = 2^64 − 1`; no valid key starts with it (`MemoKey.ok_tomb`), so the slot stays live for
probing and never matches. The relation's live/uniqueness clauses skip tombstone slots, and every
entry of `mp` is the decoding of its own encoding (a new clause, needed so that erasing one key
cannot strand another key with the same encoding: `lfKey`'s `Nat` cutoff is not injective).
`memoRV_erase`: find (a hit), then erase, is `mp.erase`. Tombstones are not reused (they go at
the next epoch `clear`), so they count against the 3/4 load limit. A separate open-addressing
map library was not worth it: the environment index, the one `erase` user ROADMAP named, is
directly addressed by the name handle (lane `pinsenv`, `Tiers.lean`: no hashing, no tombstones),
so erase has no client yet; it cost one L function (4 lines) and one lemma (~70 lines).

### Banks: generation-tagged keys (`MemoBank.lean`)

ROADMAP §2 item 3 proposed `D` banks selected by the eager depth, the new bank cleared by epoch on
entry. Built instead: **one memo per table, the generation in the key** (`genKey K`: `K` with
a generation `g < 2^32` in the high half of the second key word). The twin's table at
generation `g` is `Bank M g mp` (`mp[k]? = M[(k, g)]?`) of the memo's whole map `M`.
`X_bank_enter()` (`bankEnterG c`) allocates `G + 1` (`CTL[c]` the last generation, `CTL[c + 1]`
the current), aborts at `2^32`, and returns the caller's generation, which the caller keeps in an
L local and restores with `X_bank_leave(s)`. `bank_enter`: the new bank is empty
(`takeModeMemos`'s fresh tables, by `Fresh M G`), the caller's bank still holds its table (what
`putModeMemos` puts back), the memo relation is untouched (two `CTL` words written). `bank_put`:
`find; put` at the current generation is an insert in its bank, leaving others (`bank_other`).
Why not `D` banks: no static dispatch over `D` copies of the L code, no depth bound `D` (only the
generation bound per memo clear), and the bank relation is pure `HashMap` reasoning (20 lines).
The cost: entries of finished generations stay until `flushCaches` (capacity, not semantics).
The test instance `tbSch`/`tbKey` (`whnfCoreC`'s shape, `EIdx → EIdx`) and a `#guard` run store
under generation 0, enter, miss and store under 1, leave, and hit the generation-0 value.

### Measurements (`lake env lean`, user CPU, one run)

| file | lines before → after | user s before → after |
|---|---:|---:|
| `MemoLib.lean` | 292 → 379 | 6.1 → 6.8 |
| `MemoLibRel.lean` | 545 → 732 | 2.6 → 3.0 |
| `MemoBank.lean` (new) | 286 | 0.8 |
| `MemoTree.lean` (new) | 109 | 0.6 |
| walk users (`WalkRefine`, `LiftRefine`) | +0 | unchanged |

All new L specs (`memoEraseG_spec`, `bankEnterG_spec`, `bankLeaveG_spec`) went through `vcgen`
at the first attempt, generic in the schema; `memoRV_set`'s proof is `memoRG_set`'s with the
tombstone antecedent and the existential value.

### For the core lanes: how to use

* **A cache with handle values** (`constTyC`, `lvlEqC`, …): `MemoRG` as before (schema, key codec
  with `ok_tomb`, `dv`); nothing changed.
* **A cache with tree values** (`readLC`, …): `MemoRV S K VR`; prove `VStable S VR` once (for
  level pointers: `lvR_stable` with `TreeSafe S`), carry it across heap writers with
  `memoRV_frame` (`memoRV_heapExt`).
* **A mode memo** (`whnfCoreC`, `whnfCoreCheapC`, `whnfC`, `inferC`, `inferIOC`, `defeqC`): key codec
  `genKey K` (second key word below `2^32`; pack two handles into the first word), one bank counter
  pair `CTL[c]`, `CTL[c + 1]` shared by the six tables (one `X_bank_enter` per eager `defeqE`).
  State it as `MemoRV S (genKey K) VR m M ∧ BankW c m G g ∧ Fresh M G ∧ Bank M g a.caches.whnfCoreC`,
  and the saved tables as `Bank M gᵢ savedᵢ` on the knot's arguments; `bank_enter` on entry, the
  `Bank` of the saved generation on exit, `bank_put` for inserts, `bank_find` for
  lookups (key word `genW k2 g`).
* **Deletion**: `X_erase` at the slot of a `find` hit; `memoRV_erase`.

### `sorry`s

None.

### The declaration loop, top down (`Checker.lean`)

Phase A and phase B of the binary's fold (`installThenCheck`) are L code now, with the callees
that are not translated yet as **stubs** (L body `abort`, no census tag) whose refinement specs
are stated and proved with `sorry`. The skeleton's refinements are real proofs from those specs.
**Census tagging**: `refines_part T "skeleton, from the stub specs"`, so the skeleton counts as
written. Tagged `refines` (proof modulo `sorry`), the census's coverage rule made every target
below `installFold` "proven with `sorry`" — 769 of 1350, measured — which would read as progress
that is not there. (Note for lane `census`: coverage through a `sorry` target is a coverage
claim about callees that may have no L code at all; a `sorry` target probably should not cover.)
Update (lane `sync`): coverage now flows only from sorry-free targets, and the skeleton is tagged
`@[refines …]` again, so it counts as `sorry` and its callees keep their own status.

* L functions (all in one generic program `p` with lookups): `install_then_check()` →
  `install_fold_go`/`install_fold_next(i, cnt, vis)` (one record per call, recursion; a pair so
  that each body is small) → `install_decl_step(i, vis)` (the `And` pin, then the step; `false` is
  an `abort`) → `install_step(i, vis)` (`flushCaches; enterScratch; installStepGo`, then
  `is_none(vis, v2)` or `is_some(i, vis, v2, g)`, the two arms of `installStep` named
  `isNoneT`/`isSomeT` on the twin side) → `pend_push(g, i, v)`; phase B
  `check_pending_go`/`check_pending_next(j, cnt, vis)` → `check_pending(j, vis)` (the view of
  check `j` is its recorded `vis`, `EnvR.restrictTo`).
* Stubs (`sorry`'d specs, each the shape the real function must prove, over any program, with
  the view word as an argument when the spec would otherwise leave it a metavariable):
  `and_pin_ok(i)`, `install_step_go(i, vis)` (returns
  the new view and the value group as flag/record), `promote_vg(g, vis)`, `promote_new(k, vis,
  fresh)`, `check_value_group(vis, g)`. Lanes that translate these replace the stub and prove the
  spec; nothing in the skeleton changes unless the spec does.
* The bracket is lane `whnf`'s real code (landed meanwhile): `flush_caches()`, `scratch_enter()`,
  `scratch_drop()` refine `flushCaches`/`enterScratch`/`dropScratch` under `CheckR`, and write
  `CTL` words below 128 only, so `flush_loop`/`enter_loop`/`drop_loop` lift them to `LoopR`
  (`PendR.frameLo`, `LoopR.of_lo`); the skeleton's theorems take `BracketProg p` (their lookups).
* The relation threaded: `LoopR dn m a vis fe pend ds` = `CheckR` + `PendR` (pending checks:
  `PEND` 137, three words each, `CTL[130]` of them; the value group a record in `EREC`) +
  the front's `DeclsR` (`DECL`/`DLP`: the declarations are the front's records, record `i` =
  fold position `i`). `CheckR.frame_hi` (new, `Tiers.lean`): a writer of arrays ≥ 137 and `CTL`
  words ≥ 130 keeps `CheckR` (`EnvR`'s frame narrowed to the arrays it reads, 132‥136, `CTL[128]`).
  `PMemoR` (the promotion memo, arrays 144‥) is a field-less stub like `CoreR`.
* Errors: every twin `.error` result is an L `abort`; the posts are the `.ok` branch
  (`FoldOut`, `FoldPost`, `PendPost`).

Proof findings (the house form, `vcgen` + `finish`, with these adjustments):
* **Pin every precondition-only argument** of a callee spec (state, `fe`, `pend`, `pm`, `vg`,
  the view word when it is not an argument): left as `·` they stay metavariables and `finish`
  fails with an unreadable model. Twin states after a chain are static terms
  (`AM.st enterScratch (AM.st flushCaches a₀)`), so pinning works when each L function is one
  straight line; branches whose twin states differ go into separate L functions (`is_none`,
  `is_some`), and the twin's arms are named (`installStepK`).
* An index into the declarations is `dsAt ds i` (a plain function of the word), not `ds[i.toNat]`:
  the dependent bound proof blocks congruence between `ds[(loc 0).toNat]` and `ds[i.toNat]`, and
  `ds.getD` is unfolded by `sym` into a `dite`.
* **State the inner triple over the twin's pieces, assemble by hand.** Letting `grind` combine
  `AM.ok_bind`/`AM.st_bind` with a callee's post and a conditional rewrite failed repeatedly
  (`installStep`, `installFold`); a post listing the pieces (`AM.ok flushCaches a₀ ∧ … ∧ LoopR …`)
  goes through, and a 3-line `triple_post` with a run lemma (`installStep_ok`,
  `installFold_cons_ok`, `checkPending_ok`, `installThenCheck_ok`, each by `AM.run_of_ok` +
  `simp only [StateT.run_bind, exc_ok_bind, …]`) assembles the twin.
* Local-variable facts across several calls sometimes need help: `finish (gen := 20)` for four
  `LocEq` hops, or a stated `hloc`/`hmemL`/`hret` (the locals and memory after `setLocs`).
* `install_step_go`'s spec needed "flag ≠ 0 → value group ≠ none": a decoder that may fail must
  say so in the spec, or the L branch and the twin's `match` disagree.

### Measurements (`lake env lean`, one run, machine shared)

| file | lines | time | notes |
|---|---:|---:|---|
| `EnvRec.lean` | 145 | 0.7 s | decoders only |
| `Pins.lean` | 342 | 0.9 s | 88 generated reader theorems |
| `PinsNatOp.lean` | 158 | 17 s | the 16-arm `vcgen` (`maxHeartbeats 2000000`) |
| `Env.lean` | 791 | 2.4 s | rows, `find?`/`push`/`popTemp`/`erase`, `decide +kernel` write set |
| `Checker.lean` | 1076 | 12 s user | skeleton + stub specs |

L lines: `pin_at`/`pin_word` 9, `nat_op_result` 29, env 60, checker skeleton 75 (+ 5 stubs).

### `sorry`s (all in `Checker.lean`, the stub specs; each is the spec its lane must prove)

`andPinOk_spec`, `installStepGo_spec`, `promoteVG_spec`, `promoteNew_spec`,
`checkValueGroup_spec`. Nothing tagged
for the census uses them except through `refines_part`.

### Not done

* `internReservedPins` / `internAllPins`: they intern con-leche `Name`s and basis/pin-set `Expr`s
  (ROM data); they need the ROM interner (ROADMAP §2 item 11, phase 0) first. `PinsR` is the
  relation they will establish (flag word 0 set last).
* `eraseInstalled`/`indexPromoted`/`promoteNew` (they need `promoteCIList`); `env_erase` is the
  step they will loop. `mkIFEnv` beyond the empty environment.
* The record pool's writer (`CTL[129]` top): the installers will build constant records in `EREC`.

## The `lit` store's `strVal` arm, and expression lines accept strings (2026-10-21, lane `strlit`)

Files: `ConAgua/Arena/Store.lean`, `ConAgua/Arena/LitRefine.lean`, `ConAgua/Arena/ArenaRel.lean`
(the `lit` parts), `ConAgua/Arena/PoolSlice.lean`, `ConAgua/Arena/NStrRefine.lean` (dedup only),
`ConAgua/Front/ApplyExpr.lean`, `ConAgua/Front/ApplyExprRefine.lean`, `ConAgua/Front/Line.lean`,
`ConAgua/Front/FrontRun.lean` (threading only).

### What changed

The `lit` store's single combined node table (one `Tbl LitNode EIdx UInt64` per tier, shared by
`natVal` and `strVal`, con-ron's `Arena/Store.lean:302`) now represents `strVal` nodes fully: kind
`1`, a slice below the pool top holding the string's UTF-8 bytes (one byte per word, as the name
store's `str` table, `NStrStore.lean`/`NStrRefine.lean`), and the hash. Previously `RecRel`'s
`strVal` arm was just `kind = 1`, contents unrepresented (`DESIGN.md`'s "Not done", lane `store`).

* **`Store.lean`**: a full `strVal` arm (`matchWStr`, `litMatchStr`, `probeWStr`, `litFindStr`,
  `pushMemStr`, `litPushStr`, `internWStr`, `internLitStr`), duplicating the `natVal` arm's L
  functions rather than parametrising them by kind (as `NStrStore.lean` duplicates `lit`'s probe
  machinery for its own prefix check): simpler, and the two arms already shared nothing but
  `REC`/`SLOT`/`CTL[2+t]`/`lit_hash`/`limbs_eq`/`cnt`/`pushOK`/`nSlots`/`homeW`/`baseW`, which stay
  common. The hash is the plain slice hash (`lit_hash`, unmixed): a `natVal`/`strVal` collision in
  the same bucket costs one extra probe step, not correctness, since `litMatchStr` checks kind
  `1` where `litMatch` checks kind `0` (hardcoded, as before) — a `strVal` query never matches a
  `natVal` node and vice versa.
* **`LitRefine.lean`**: `StrRec` (the `strVal` record relation), `litMatchStrOK`/`litHomeOKStr`/
  `litNewOKStr` (the query's obligations), the bridges, `internStr_correct`, `internLitStr_refines`.
  The uniqueness argument for a `strVal` key is `slice_key`/`strWords_inj` (word-list equality),
  not the `natVal` arm's normalised-slice argument (`pv_len`/`pv_limbs`) — exactly the "name `str`
  table's pool-slice approach" the task pointed at. Since `PoolSlice.lean` (which has `slice_key`)
  already `import`s `LitRefine.lean` (for `eqW_iff`/`hashN_congr`, which `slice_key`'s proof needs),
  and `LitRefine.lean`'s own `strVal` arm now needs `slice_key` too, the slice-as-key layer
  (`sliceL`, `slice_key`, `slice_key_hash`, `strWords`, `strWords_inj`) moved **into**
  `LitRefine.lean` itself (next to `eqW_iff`); `PoolSlice.lean` is now a one-paragraph re-export
  (`import ConAgua.Arena.LitRefine`, no new content), and `NStrRefine.lean` dropped its own copy of
  `strWords`/`strWords_inj` in favour of the one now visible transitively. No other file needed to
  change: both downstream users (`LsRefine.lean`, `NStrRefine.lean`) already imported
  `PoolSlice.lean`, never `LitRefine.lean` directly.
* **`ArenaRel.lean`**: `internLitStr_refinesA`, and the existing `internLit_refinesA`'s census tag
  changed from `@[refines_part ConRon.Arena.internE "lit natVal"]` to `"lit"` (the label
  `COMPLETE_BY_PARTS` actually requires); both theorems carry that label now, so `internE`'s `lit`
  arm — and so all of `ConRon.Arena.internE`/`internNodeE` — is **proven** (`scripts/census.py
  --list internE`), not just `written`. `litLocal`'s `strVal` branch (a separate, pre-existing
  locality lemma, not part of my task's obligations but broken by the richer `RecRel`) needed the
  same pool/top rewrite the `natVal` branch already had.
* **Frontend** (`ApplyExpr.lean`): `node_lit_str` (`str_put_esc` then `intern_lit_str`, aborting
  where the body position is `0`, as `apply_str`'s name-line analogue does), wired into
  `expr_node`'s dispatch at kind `17` (previously the final catch-all `abort`). `ExprLookups`
  gained the five new store-function fields; the byte-level unescape chain
  (`byte_in`/`hex_val`/`hex4`/`hex3`/`esc_sur`/`esc_one`/`utf8_put`/`str_put_esc`) is threaded as
  **explicit hypotheses** through `nodeLitStr_spec`/`exprNode_spec`/`applyExpr_spec` instead, since
  `ScanLookups` (`Line.lean`) already carries them for the name-`str` line and the one call site
  (`applyAny`'s proof) already has that record in scope — no new structure needed there.
* **`ApplyExprRefine.lean`**: `internLitStr_D`, `node_lit_str` (mirrors `node_lit`'s shape exactly,
  using the already-proved, already-generic `ConAgua.Front.UnescapeLink.strPutEsc_link` in place of
  `natDecW_val`). `applyExprW_refines`'s tag changed from `@[refines_part … "every kind but
  strVal"]` to a plain `@[refines ConRon.Arena.Frontend.parseExprEntryD]`: **every** `ExprRec` kind
  is now covered, and the census agrees (`parseExprEntryD` is `proven`).
* **`frontAll_refines`'s coverage**: unchanged in substance (`applyLine`/`parseBytes` still abort
  on inductive declaration lines, out of scope here), but the label text's parenthetical dropped
  "strVal" — that part of "expr lines" is no longer a caveat. `exprProg`/`frontAllProg` needed the
  unescape chain added/deduplicated (`frontAllProg`'s `exprProg.filter` now also drops
  `byte_in`/`hex_val`/`hex4`/`hex3` — already supplied by `L.Scan.Validator.valProg` earlier in the
  list — and the four explicit `esc_*`/`utf8_put`/`str_put_esc` entries were dropped in favour of
  `exprProg`'s copy).

### Findings

* The two literal kinds share one cons table by design (con-ron's single `Tbl LitNode …`), so the
  `strVal` arm's L code could not just be `NStrStore.lean`'s pattern verbatim (a fresh pair of
  arrays): it had to reuse `REC`/`SLOT`/`CTL[2+t]`, differing from the `natVal` arm only in the
  record's kind word. Duplicating the match/probe/push functions (rather than adding a `kind`
  parameter to the existing ones) kept every already-proved `natVal` theorem untouched.
  `litPush`/`litPushStr` do share the room checks (`pushOK`, unparametrised by kind: capacity does
  not depend on content) and the node counter.
  `str_put_esc` already existed end to end (lane `store`'s "Not done" note named it directly, and a
  prior lane had already built `ConAgua.Front.UnescapeLink.strPutEsc_link`/`strPutEsc_spec`,
  apparently in anticipation) — the frontend half was mostly wiring, not new proof.
* Moving `sliceL`/`strWords` into `LitRefine.lean` was forced by the import DAG, not a style
  choice: `PoolSlice.lean` already imported `LitRefine.lean` (for `eqW_iff`/`hashN_congr`), so
  `LitRefine.lean` could not import `PoolSlice.lean` back for the same declarations its own
  `strVal` arm now needs.
* `grind [litMt, matchW, RecRel_strVal]`, the one-liner that dismissed the old (trivial) `strVal`
  case of `litMatchOK`, still works verbatim once `StrRec` is added to its argument list — the
  dismissal is still "kind `0` ≠ kind `1`", just through a richer hypothesis now.
## The core tier and the whnf family (2026-10-21, lane `whnf`)

Phase 5 (ROADMAP §1), top-down. Files: `CoreCaches.lean` (L), `Tiers.lean` (`CoreR`),
`CoreRefine.lean`; `Scratch.lean`/`ScratchRefine.lean` (`scratch_drop` now flushes).

### `CoreR`: eleven caches in L, three readback caches need none

`Caches` has fourteen tables and (since con-ron #127, vendored at 12752ca7) a second set of the six
mode memos for the eager tower, `eagerMemos`. Eleven tables are `MemoLib` memos (arrays 96‥106,
stamps/counts `CTL` 96‥113, 116‥119): the six **mode memos** `whnfCoreC`, `whnfCoreCheapC`,
`whnfC`, `inferC`, `inferIOC`, `defeqC`, each holding **both** sets, keyed by the knot mode's
**eager bit** in the high half of the second key word (`genW k2 eb`, `MemoBank.lean`'s codec);
the three constant caches `constTyC`, `constValC`, `ruleRhsC`; the two level-verdict caches
`lvlEqC`, `lvlsEqC`. Keys: a handle and `genW 0 eb` (`eKeyG`); `defeqC` the two handles and
`genW b eb` (`dKeyG`); the constant caches `(n, us)` (`pairKey`) and `(rec, ctor ∣ us << 32)`
(`rrKey`); the verdicts `(u, v)`. `readLC`/`readNC`/`readLsC` have no table: L makes no
readbacks; the twin's entries must be readbacks (`CoreS.readL`, `readLs`).

* `CoreRM m c M eb`: per mode memo a `ModeR` (memo relation over the map `M` of `(key, eb)`, the
  twin's field is bank `eb`, its `eagerMemos` table bank `1` outside the eager tower (`eb = 0`)
  and empty inside it); `CoreR m c := ∃ M, CoreRM m c M 0`. Inside the eager tower the plain set
  is the eager slot's local (`enterEager`'s `saved`): an eager run keeps bank `0` (`KeptAll`). An
  eager comparison moves nothing in L: the slot's key bit is the mode's
  (`((mode >> 1) & 1) << 32`). The first version (before the bump) mirrored
  `takeModeMemos`/`putModeMemos` with generation counters (`bank_enter`/`bank_leave`, `CTL[114]`,
  `CTL[115]`); con-ron's change made that unnecessary and it went.
* Handle-valued tables relate their words by `VH` (the entry is `decE w` and `w < 2^32`), so a hit
  returns a word the caller may compute with; `Bool` tables by `VB`.
* `flush_caches()`: the eleven `clear`s; `CoreR.flush` (any `CoreR`, no stamp about to wrap ⇒
  `CoreR` of `Caches.empty`, both sets), `flushCaches_refinesC`. The generic part (`clearsL`,
  `memoRV_clearsL`: a memo cleared in a run of clears is empty after it) is schema-generic.
* `scratch_drop()` = `flush_caches()`; `scratch_reset(0)`, as the twin's `dropScratch`
  (`flushCaches` first); `scratchDrop_refinesC` proves the caches part, `CheckR.of_bracket` takes
  the new `CoreR` and a `CTL` write set below 128.
* Probes and inserts (`CoreRefine.lean`): `ModeR.findE`/`setE` (one-handle mode memos), `findD`
  (`defeqC`), `memoRV_findP`/`findR` (constant caches).
* **Finding**: `MemoBank.lean`'s `lo_hi`, `genW_lo`, `genW_hi` were proved by `bv_decide`, which on
  this toolchain adds an axiom `…._native.bv_decide.ax_…`; anything built on the banks (then
  `scratchDrop_refinesC`) would have stopped counting as proven. Reproved by `toNat` arithmetic
  (`Nat.shiftLeft_add_eq_or_of_lt`, `Nat.and_two_pow_sub_one_eq_mod`), same statements.
* Finding: `decide +kernel` on membership in `coreSchs.flatMap (fun S => [S.cs, S.cs + 1])`
  (twenty words) ran out of memory (18 GB, killed); an explicit literal list and `simp` is instant.

### Every con-ron cache, and where L mirrors it

The rule (ROADMAP, "Known costs relative to con-ron"): a cache con-ron has must be in L, or L can
be asymptotically slower. con-ron at `_tmp/ref/con-ron` origin/HEAD (`proof/ConRon/Arena`):

| con-ron | lifetime | key → value | L | status |
|---|---|---|---|---|
| `Caches.whnfCoreC`, `whnfCoreCheapC`, `whnfC`, `inferC`, `inferIOC` | declaration | `EIdx → EIdx` | `wc`/`wk`/`wh`/`in`/`io` (arrays 96‥100) | relation `CoreRM` (lane `whnf`); the knot's probes: `whnf_core`/`whnf` this lane, `infer*` phase 7 |
| `Caches.defeqC` | declaration | `(EIdx × EIdx) → Bool` | `de` (101) | relation `CoreRM`; probe phase 6 |
| `Caches.eagerMemos` (the eager tower's six, con-ron #127) | declaration | as the six | the same six memos, key bit = the eager bit | relation done (`ModeR.stored`/`empty`) |
| `Caches.lvlEqC`, `lvlsEqC` | declaration | `(LIdx × LIdx) → Bool`, `(LsIdx × LsIdx) → Bool` | `lq`, `lsq` (105, 106) | done: `lvl_eq_c`/`lvls_eq_c` in front of lane `levels`' `lvl_eq`/`lvls_eq` (`CoreLevels.lean`) |
| `Caches.constTyC`, `constValC`, `ruleRhsC` | declaration | `(NIdx × LsIdx) → EIdx`, `(NIdx × NIdx × LsIdx) → EIdx` | `ct`, `cv`, `rr` (102‥104) | relation done; probes in `const_ty_at`/`const_val_at`/`rule_rhs_at` (this lane) |
| `Caches.readLC`, `readNC`, `readLsC` | declaration | handle → `Level`/`Name`/`List Level` | none needed: L makes no readbacks (the level algorithms run on handles, `LevelHeap.lean`) | the twin's entries are readbacks: `CoreS.readL`/`readLs` (an invariant, not a table) |
| `Memos.bvarBC`, `fvarBC`, `inst1C`, `liftC` | one top-level walk | `EIdx(×Nat) → …` | `bm`, `fm`, `if`, `lf` (24, 48, 47, 41) | done (lanes `walk`, `exprops`, `exprops2`) |
| `Memos.instLC`, `abs1C`, `inst1LC`, `instLPC`, `instLPLC`, `instLPLsC` | one top-level walk | `(EIdx × Nat) → EIdx`, level tables | arrays 49‥55 reserved in `MemosR` | to do with their walks (phase 4: `instantiateListGo`, `abstract1Go`, `instantiate1LiftGo`, `instLPGo`) |
| walk-local `memo`/`seen` arguments: `wscopedBGo`, `fvarLeavesGo`, `leavesSubGo` (ExprOps); `constsResolveFGo`, `hasStrLitGo` (CheckerBase); `mentionsAnyGo`, `nestOccGo`, `depthGo`, `replaceFVarsGo` (Positivity); `hasLooseBVarBGo`, `structUsedLaterGo`, `mentionsConstGo` (StructParts); `usedConstsGo` (NatOpGround, a `HashSet`) | one call | various | argument relations, arrays 144‥191 | to do with each walk: each needs an epoch-cleared memo of the library (`MemoLib`), not a recomputation |
| store cons tables (21), `IFEnv.idx` | run / declaration | node → handle, name → constant | `*SLOT` arrays, `EIXA/S/N` | done (`ArenaR`, `EnvR`) |

### The whnf family in L, top-down (`WhnfBase`, `WhnfSpine`, `WhnfCore`, `WhnfCoreSlot`, `WhnfIota`)

* **Arguments.** The twin's `mode`, `fe`, `depth` and the knot record `r` become a mode word
  (`decMode`), the environment view word `vis` (`EnvR`), a depth word; the record is the program:
  the knot's slots are L functions (`whnf_core`, `whnf`, `infer`, `infer_io`, `defeq`), refined
  against `coreKnot mode fe id F` for every `F ≥` the L fuel (`WhnfCoreSlot` …, `KnotOK`). A body
  at L fuel `n + 1` assumes the slots at every fuel up to `n` (`KnotUpTo`: a call inside a loop
  runs on less fuel than the body, and L has no fuel monotonicity lemma).
* **The spine stack.** `Array EIdx`/`List EIdx` values are slices of word array 144 (`SPN`), top
  `CTL[136]`; a callee puts the top back (`StackKept`), a slice-returning one leaves its slice
  (`StackGrew`); `SpineR` relates a slice to its array.
* **The relation and the post.** `CoreS dn m a vis fe M eb` (`ArenaD`, `CoreRM` at explicit maps,
  `PinsFull`, `EnvR`, the readback-cache invariants, `NStoreWF`); `CoreRef`/`CoreSpec`: the twin
  run succeeds, `CoreAfter` (the relation at some maps, the plain banks kept inside the eager
  tower, the stack kept), the result decodes, and the result words are valid handle words (`ResH`,
  `ResW`: `decE` truncates, and the caller computes with the word).
* **Stubs**: named L functions with abstract specs (`WhnfCallees`, `CoreCallees`, `IotaCallees`),
  the refinements take them as hypotheses, the stubs' own theorems are `sorry`.
* **The proof pattern** (`WhnfCoreSlot.lean`, also `CoreLevels.lean`): a callee's run depends on
  the caller's memory alone, so it is a function `callW p n f vs m` (`callW_spec`: every call
  meets its run). A caller's word-level model calls its callees through `callW`; the L spec is
  `vcgen` + `finish` with `callW_spec` as the callee spec (no callee proof needed); the
  refinement then applies each callee's own spec to its run (`CoreSpec.of_callW`) and threads
  `CoreAfter` (`CoreAfter.comp`). Loops get a named block and a model by fuel
  (`whnfCoreLoopB_spec`, `coreLoopW`), refined by induction (`coreLoopW_ok`).
* **Proved so far** (no `sorry` of their own; they assume the callees' specs): the knot's
  `whnfCore` slot one level up (`whnfCoreSlot_step`: stuck tags, both memos, hit and miss), the
  loop and the body (`whnfCoreLoop_refines`, `whnfCoreBody_refines`, `WhnfCoreLoop.lean`), the
  dispatcher `whnf_core_step` (`whnfCoreStep_refines`: one view lemma per tag, the app arm, the
  projection arm through its spec, ζ through `inst1`), the app arm `whnf_core_app` and its second
  half `whnf_core_app2` (`WhnfCoreStep.lean`), `proj_cert`; the `whnf` slot and loop
  (`whnf_refines`, `whnfLoop_refines`, `WhnfDeltaSlot.lean`, a sub-lane); five spine walks
  (`get_app_fn`, `pi_result`, `peel_pis`, `mk_app_n`, `mk_app_n_from`, `WhnfSpineRefine.lean`, a
  sub-lane); `lvl_eq_c`/`lvls_eq_c` completely, the flush.
* **Statement changes by the sub-lanes.** `mkAppN_refines`/`mkAppNFrom_refines` post a
  `MemFrame [AREC, ASLOT, ADER] [4, 5]` instead of `Grows` (the walk never touches the Nat-limb
  pool) and drop the `HW` of the result (a fresh handle's index bound is not established by the
  store's relation yet); `whnfLoop_refines` takes the step spec at every fuel up to `n`
  (`WhnfStepUpTo`), as `KnotUpTo`.
* **L code written** (sorry'd specs): `whnf_core_step`, `whnf_app`, `beta_peel`,
  `whnf_core_step_proj`, `reduce_proj_core`, `proj_cert`, `proj_lit_to_ctor` (`WhnfCore.lean`,
  177 L lines); the spine walks (`WhnfSpine.lean`, 124, exact `coreWalkFuel` counters); ι
  (`WhnfIota.lean`, 504 L lines: `iota_rec_at`, `prepare_major`, `major_to_ctor` with its K, η and
  `And` rescues, `lit_major_to_ctor`, `iota_certs_full`, `iota_index_ok`, `defeq_list`,
  `pi_residual`, `proof_irrel`, `rule_rhs_at`/`const_ty_at` with their caches, `find_rule`,
  `tower_slots_all`, `eta_projs`, `and_rescue_slots`, …; a sonnet sub-lane).
* **Findings.** (1) The lane `exprops` walks (`inst_entry`, `lift_entry`) refine their twins at
  every fuel `F ≥ n` but have no `coreWalkFuel` counter, while the core calls them at exactly
  `coreWalkFuel`: they need the counter (ROADMAP §3 (b)) before the core can call them; stubbed
  (`Inst1OK`). (2) `IFEnv.findProj?` interns the table name (`projTableName`: a `str` name with
  the bytes `projTable`): L needs those bytes as constant data; stubbed (`find_proj`). (3)
  `recFireLevels` substitutes levels and **interns** the results (`internLevel`): lane `levels`'
  heap results must be interned back into the level store, a walk that does not exist yet;
  stubbed. (4) `decE` truncates a word to 32 bits, so a spec whose result the caller computes
  with must state that the word is below `2^32`; the handle-valued caches carry it (`VH`).

### `sorry`s

* `WhnfBase.lean` `whnfCallees_stub`: the specs of the callees not written yet (`inst_list`,
  `inst_lp`, `str_lit_ctor`, `str_lit_supported`, the knot's `infer`/`infer_io`/`defeq` steps).
* `WhnfSpine.lean`: none. The two-loop walks are split into functions (`WhnfSpineArgs.lean`):
  `app_count` (the `get_app_fn` loop; the count is the fuel spent, and it returns the head),
  `app_fill`/`app_fill_n` (write the arguments/nodes without checks), and `get_app_args`/
  `get_app_spine` call them; each spec is `vcgen` + `finish` on a short chain. They need the
  stack's size below `2^63` (`CoreS.spn`); `head_and_args` also the top within the stack.
* `WhnfCore.lean`: `coreCallees_stub` (`inst1` at `coreWalkFuel`, `find_proj`, `fire_ok`,
  `iota_rec_at`; `ErecKept`: `find_proj`/`fire_ok` leave the record pool alone; `ProjSmall`: a
  projection table's counts are below `2^32` (L compares `an == np + nf` in words, the twin in
  `Nat`); `ProjFound`: a found table record decodes). `whnf_app`
  and `beta_peel` are proved (`WhnfCoreApp.lean`, sub-lanes: the loop as named blocks, one small
  spec each, fuel induction).
* `WhnfBase.lean` `supKeep_twin`: `strLitSupported` keeps every stored node's view (twin-side
  store monotonicity, true, unproved).
* `WhnfCoreProj.lean`: none of its own. `reduce_proj_core` is proved on its split into
  `_core`/`_head`/`_fire`/`_arg` (sub-lane); the inner two leave the argument slice on the stack, so
  their post is `GrowSpec` (`CoreSpec` with `StackGrew`); the outer one restores the top.
* `WhnfIota.lean`: `iotaCallees_stub`, `major_to_ctor`, `iota_rec_at` (both large: they need splitting,
  and `major_to_ctor`'s K and `And` arms leave a slice on the stack, so `CoreAfterG`). The other 24
  are proved (`WhnfIotaRefine{,2..6}.lean`, sub-lanes); the census-tagged statements instantiate the
  stub bundles (`iotaCallees_stub`, `whnfCallees_stub`, `coreCallees_stub`, `supKeep_twin`) and three
  new assumptions: `erecKeptInst_stub` (`inst_lp`/`inst_spine` leave `EREC` alone),
  `erecKeptKnot_stub` (the knot's slots and `major_to_ctor` do), `CoreS.lvl_den` (a sort node's level
  and the pinned zero level denote; a `CoreS` field would be the fix). L changes: `proof_irrel` calls
  the cached `lvl_eq_c` (the twin's `lvlEq?` fills the cache), `expr_view_ok` aborts on a dangling
  handle (the twin's `view` fails), `iota_certs_full_aux`/`iota_ctor_never_prop` split;
  `caps_never_zero`'s stub statement corrected (its twin runs readbacks). The first sub-lane's
  fixes to the L code: `const_ty_at`/`rule_rhs_at` probe
  the memo again after `inst_lp`, `defeq_list` compares the common prefix before the lengths (the
  twin's order of `defeq` calls), `iota_index_ok`/`iota_certs_full` restore the top,
  `inst_spine_pins` raises the top after each store, `and_rescue_slots` runs `fire_ok` first.
* `WhnfDelta.lean`: none of its own; the δ/Nat specs are proved (`WhnfDeltaRefine*.lean`, sub-lane)
  on two assumed facts: `natOpResultOK_stub` (`nat_op_result` refines `natOpResult` under `CoreS`;
  lane `nat2` proved it over its own program and `ArenaR`) and `whnfGrowsUpTo_stub` (a `whnf` call
  only grows the limb pool). The sub-lane's L changes: `nat_zero_ok` interns `Nat` first and
  `reduce_nat` runs `nat_lit_supported` unconditionally (the twin's `do` lifts both out of `&&`),
  `unfold_definition` restores the stack top, `raw_nat_lit`/`reduce_nat` abort on tags 10‥15 and
  `unfold_defn_at` on a non-tag-0 level list (the twin's `view` fails there); `reduce_nat` and
  `unfold_definition` are split into small functions.

### Lane `exprops4`'s walks as this lane's callees (open)

Lane `exprops4` refined `instantiateList` (on the spine stack, `InstListOK`), `abstract1`,
`hasFvar`, `bvarB`, `looseBVarsBounded`. To discharge this lane's stubs with them (`inst_list` in
`WhnfCallees`, `inst1` in `CoreCallees`): (1) `CoreS` must carry the `instLC` memo relation
(`MemosR`'s array 49), a new field and one more conjunct in every `CoreS` frame lemma; (2) their
refinements hold for twin fuel `≥` the L fuel, while the core calls them at exactly
`coreWalkFuel` with an L fuel up to `2^62`: the stub specs must gain `n ≤ coreWalkFuel`, which
the knot's fuels do not give, or the walks a `coreWalkFuel` counter (finding (1) above); (3) a
caller crossing `scratch_enter` re-establishes the `abs1C` relation (not cleared there; whnf does
not cross it). Not done yet.

### Lane `induct`'s stubs of this phase (adapters, `WhnfEntry.lean`)

Lane `induct` calls `whnf(vis, dep, e)`, `get_app_fn(fuel, e)`, `get_app_args(fuel, e)` (an `IW`
slice), `mk_app_n(f, off, len)` (an `IW` slice), `pi_result(fuel, e)` (`IndStubs.lean`). This
lane's functions of those names are used with their own conventions by lane `defeq` too (`whnf`
takes the mode word, the walks count `coreWalkFuel` themselves, slices are on the stack `SPN`), so
the names stay, and `WhnfEntry.lean` adds `induct`'s conventions under new names: `whnf_top`
(`l_impl ConRon.Arena.whnf`, the verified knot entry), `get_app_fn_f`, `pi_result_f` (abort unless
the fuel is `CWF`, the only fuel `induct` passes), `get_app_args_f` (the stack slice copied to a
fresh `IW` slice, the top put back), `mk_app_n_f` (the `IW` slice copied to the stack top).
**Request to lane `induct`**: rename the five call sites and stubs accordingly (`whnf` →
`whnf_top`, `get_app_fn` → `get_app_fn_f`, `get_app_args` → `get_app_args_f`, `mk_app_n` →
`mk_app_n_f`, `pi_result` → `pi_result_f`); the adapters' specs against `IndStubs`' `RelAM`
statements (bridging `StageR` and `CoreS`) are not written yet.

### Numbers (2026-10-21)

* Rust (con-ron's `whnf`/core, census phase 5): 1500 lines; L written for 720 of them, proved for
  68 at the last census (the proved bodies call sorry'd callees, so their Rust counts once those
  close).
* L: 1101 lines (`CoreCaches` 14, `CoreLevels` 26, spine 94, `WhnfCore` 186, `WhnfIota` 504,
  `WhnfDelta` 277). Refinement proofs: about 3600 lines for about 240 proved L lines, **15 proof
  lines per L line** (the callW pattern: model ~1, L spec ~1 (`vcgen` + `finish`), refinement
  ~10–13; most of the refinement is case splits on the callees' runs and threading `CoreAfter`).
* CPU (`lake env lean`, user): `WhnfCoreSlot` 10.5 s, `WhnfCoreStep` 8.0 s,
  `WhnfSpineRefine` 4.6 s, `WhnfDeltaSlot` 3.2 s, `CoreLevels` 3.1 s, the rest ≤ 2 s each: 33 s.
* Automation: every L spec is `vcgen` + `finish` (or `simp_all`) against `callW_spec`; no L
  spec needed a hand proof. The refinements are manual. Pattern breaks: a function with two loops
  in sequence (`get_app_args`) defeated `finish`; a dispatcher with eight arms needed `by_cases`
  per tag (`split_ifs` is Mathlib); `simp_all` on the dispatcher's VCs ran out of steps, `sym`
  + `finish` took 7 s.

## Any number of results (2026-10-21, lane `cresults`)

Files: `ConAgua/Compiler/{Compile,WF,Rel,SimStmt,SimStore,SimCall,SimFun,Main,Run,Tests}.lean`,
new `ConAgua/Compiler/WFAll.lean`, `WFAllBench.lean`; `ConAgua/Capstone.lean`
(`frontAllProg_wf`, `frontAll_run`, `frontAll_x64`); one line each in `ConAgua/Final/Statement.lean`
and `lakefile.toml`.

### The design: a result area in the table

Results `0 … 5` stay in `rax, rdi, r8 … r11`. Result `i ≥ 6` goes to the word at
`T + Tab.resOff i`, a **result area** in the table between the constant data and the entry
arguments (`Tab.nxres = nres - 6` words; `Tab.args` moves past it). `return` writes it through
`rcx` (`mov rcx, [rsp + tmp]; mov [r15 + off], rcx`, or `mov qword [r15 + off], 0` past the
returned values); a call reads it right after `call` (`mov rcx, [r15 + off]; mov [rsp + 8x], rcx`).
Between the callee's write and the caller's read only the epilogue (`add rsp; ret`) runs, so one
area serves every call. For `nres ≤ 6` the area is empty and the code is unchanged: every
`Emit*` driver on master (scan, store, walk, lift, inst1, validator) prints byte-identical
assembly before and after.

**Alternatives rejected.** Slots at the top of the callee's frame (at a fixed distance below the
return address, so the caller finds them below its `rsp`) need the frame size in the code that
compiles `return`, and the statement simulation (`SimS`) has a frame size `F` that the code does
not know (`ctx` has no `F`, and a statement's temporaries only bound `F` from below). Passing a
result pointer (like the argument pointer `rsi`) needs a saved register per frame. The table area
needs neither: its address is `r15` plus a constant.

**Proof.** `InTab` now covers the area (so `compile_correct`'s hypotheses read as before; `G.Ok`
makes it disjoint from the stack and the arrays). `MemRel` gains `res` (the area is mapped);
`Pres` also allows changes in the area (`InRes`); `MemRel.onlyD` keeps the relation under changes
outside the descriptors and constant data (`MemRel.only'` is its `InTab` instance, `only_res` the
area's). `ResRel` now speaks of the register results only (`i < maxRes`), `ResMem G vs d` of the
area, `ResOut = ResRel ∧ ResMem` replaces `ResRel` in `Conts.ret`, `FunSim` and `OutcomeRel`.
`sim_loadRes`/`sim_storeRes` handle both kinds per element (the post of `sim_loadRes` is an
`Only` over the area). `compile_correct`'s statement is unchanged except through `OutcomeRel`
(results 6… in the area at `Layout.resAddr i`); the capstone users changed by one token each
(`hres.1 0 … (by simp [maxRes])`). No `sorry`; `#print axioms compile_correct`: `propext`,
`Classical.choice`, `Quot.sound`. About +230 lines of proof (mostly `SimCall`), +25 of compiler.

`Prog.wf` no longer bounds `nres`; it requires the result area's offsets below `maxOff`
(`hTab` grew a `+ 8 * nxres`). `Prog.wfAuto p` is `Prog.wf` for the smallest table with every
array `p` names (`Prog.arrs`).

### Testing

* `Tests.lean`: `nineProg` (nine results, seven of nine read as nine, two of nine, the area
  used by three calls in a row; 10 results in use), against `L.run`; `runKraken` maps the area
  and `Outcome.ofState` reads it.
* `scripts/check-asm.sh`: scan 303, store 1313, walk 6743 instructions, OK. The compiled
  `frontAllProg` (`Prog.tab frontAllProg 1 69`, 47915 instructions, with result-area moves)
  passes `check_asm.py` too.
* `run --lines` (skip_braced) on `complete_c04a_restart_70`: 126481 lines, 0 mismatches; the
  compiled validator accepts it (`ok 0`), and gives the same verdicts as master on the 492 e2e
  fixtures (the assembly is identical).

### Every program's static check (`WFAll.lean`, `WFAllBench.lean`)

One `#guard Prog.wfAuto p` per program defined on master (60; the four benchmark programs in
`WFAllBench.lean`, whose modules clash with `NatBits` on import; the compiler's own test programs
in `Tests.lean`). All pass, `frontAllProg` included, except `L.Scan.Values.hintsProg`, a test
fragment that calls `skip_ws`/`hints_obj` without containing them (guarded as failing).
**New programs should get a line there.**

### The capstone: `frontAll_x64`

`frontAllProg_wf` (one byte array, 69 word arrays, `decide +kernel`) and `frontAll_x64`:
`compile_correct` composed with `frontAll_refines` (via `frontAll_run`, `M.of_run`). From a
Kraken host holding the compiled `frontAllProg`, run from `ca_enter` on a memory that holds `b`
in `IN` and is related to `a₀` by `ArenaD` and to the blank parse state by `StateDR`: the machine
reports exhausted, an error, or `rdx = 0`, and then `rax = 0` implies that con-ron's
`parseBytes b` accepts from `a₀` and the final machine memory holds an L memory related to its
final arena and parse states. Only `propext`, `Classical.choice`, `Quot.sound`.

### `sorry`s

None.

## Twin fingerprints and the bump machinery (2026-10-21, lane `sync`)

*Superseded in part (2026-10-22, "Census memory"): the fingerprints, the stale flag,
`--stale`/`--reviewed`/`--record` and `docs/twin-fingerprints.tsv` are gone; the patch series and
`scripts/bump-con-ron.sh` stay.*

Question: when con-ron moves, which of our L code and proofs must be looked at again? The census
links (`@[l_impl T]`, `@[refines T]`, `@[refines_part T]`) say which twin target `T` each piece
stands for; nothing noticed that `T` changed. Pieces: `ConAgua/Census/Main.lean` (fingerprints),
`scripts/census.py` (stale flag, `--stale`, `--reviewed`), `docs/twin-fingerprints.tsv` (the
lockfile), `vendor/UPSTREAM` + `vendor/patches/` (the vendored state as data),
`scripts/bump-con-ron.sh` (the bump). Workflow: PLAN.md, "Bumping the twin".

### Decisions
(The fingerprint design that stood here, its stale flag and review workflow, was dropped on
2026-10-22, "Census memory"; it is in git history.)
* **Patches as files, applied with `git apply --3way`.** Each patch carries the full blob ids of
  the old pristine files (the bump first writes those blobs into our object store), so a hunk whose
  context moved upstream becomes a real three-way merge, and a conflict is left with markers. The
  patch descriptions live in the patch preamble and survive `--refresh-patches`. `--check` is the
  gate that `vendor/` holds no unrecorded edit.

### con-ron bump to `12752ca7` (con-leche `ae1f3198`), 2026-10-21

**What changed upstream** (con-ron task #127, con-leche tasks #359/#361): the eager tower keeps its
memos. Before, every eager comparison (the knot's `defeqE` slot) ran on emptied mode memos
(`takeModeMemos`) and threw away what it learned (`putModeMemos`). Now `Caches` has a fifteenth
field `eagerMemos : ModeMemos`, the eager tower's own six mode memos, kept for the declaration;
`enterEager mode.eager` swaps them into the six fields (from a plain mode; at an eager mode
nothing moves) and returns the plain set, `leaveEager` stores the six back as the eager set and
restores the plain ones. `defeqE` now also memoizes its verdict (`defeqC` probe/insert on the
eager set). `takeModeMemos`/`putModeMemos` are gone; `Caches.empty`, `Caches.modeMemos`,
`ModeMemos.empty` are new or changed. (con-leche: `CState.eagerMemos`, `withEagerMemos`;
grind-ring-5 −30 % instructions.) Also task #359 (con-leche proofs only: cached loops unfold by
`f.eq_def`). Theorem 1 followed upstream; Theorem 2 is not vendored as buildable.

**Bump result.** All patches re-applied; one conflict, `Bridge/Core/Memo.lean`, where the new
`enterEager_spec`/`leaveEager_spec` replace the specs our patch touched; they needed the same
`dsimp only` before `vcgen` (nested `{ … with }`), now in `con-ron/0002`. The KnotC patch applied
with an offset. Everything builds, our code included, with no change: no L proof mentions the
new field, because `CoreR` relates the nine L caches to their twin fields and says nothing about
the others.

**Stale targets** (`scripts/census.py --stale`, 7):
* `flushCaches` (proven, lane `whnf`): `Caches.empty` now also empties `eagerMemos`. The proof
  still checks only because `CoreR` ignores the new field. **Lane `whnf` (and `libs`, owner of
  `MemoBank.lean`)**: the banked design (`bank_enter`/`bank_leave` = a fresh empty bank per eager
  comparison, dropped afterwards) no longer matches the twin. The twin now has exactly two
  mode-memo sets, plain and eager, both kept for the declaration and cleared by `flushCaches`;
  a nested eager comparison uses the same eager set. In L this is two fixed banks (generations
  0 and 1, or two array groups), with no generation counter. `CoreR` needs a clause for
  `eagerMemos`, `flush_caches` must clear the eager bank, and the `defeqE` slot (when it is
  written) probes and inserts `defeqC` on the eager bank. `MemoBank.lean`'s and
  `CoreCaches.lean`'s doc comments still describe take/put.
* `lvlEq?`, `lvlsEq?` (proven, lane `levels`): their own code is unchanged, but `readLevelM`/
  `readLevelsM` below them write `{ s.caches with readLC := … }`, and that changed because of the
  added field. Most likely no L change: review, then `--reviewed 'lvlsEq\?|lvlEq\?'`.
* `installStep`, `installDeclStep`, `checkPending`, `checkPendingList` (sorry, lane `pinsenv`):
  the same field-add, through `Caches.empty` (the per-declaration bracket) and the readbacks under
  the stubs. Check the bracket's `CoreR` use once lane `whnf` has extended `CoreR`.

### Census: coverage only from sorry-free targets (2026-10-21, lane `sync`)
At lane `pinsenv`'s request: a target proved only modulo `sorry` counts as `sorry` but covers none
of its callees (before, a top-down skeleton over stub specs made 769 targets "sorry" by coverage).
The skeleton's five theorems in `ConAgua/Arena/Checker.lean` are tagged `@[refines …]` again
(they were `refines_part … "skeleton, from the stub specs"` to work around it), so the census now
shows 13 targets proven with `sorry`.

## Inductive types and recursors, top down (2026-10-21, lane `induct`)

Phase 8 (ROADMAP §1, `arena/inductives/*.rs`, 7.2k Rust lines, 223 census targets): the whole
inductive-declaration check in L — `checkDecl`'s `.indDecl` arm, the recogniser (`blockParts?`),
the formers' stage, the constructors' stage, positivity (nested containers included), the
generated recursors and their check, the install — written top down against stubs for the
callees other lanes own, plus the frontend's inductive lines. Files: `ConAgua/Arena/Ind*.lean`,
`Rec*.lean`, `ConAgua/Front/Ind*.lean`.

### The interface first (`IndIface.lean`)

The twin threads rich values (lists, records, lists of lists, sums). One file fixed, before any
translation, how they live in L memory and how L functions call each other; eight sonnet workers
then translated one twin module group each, in parallel worktrees, against it alone (calls are by
name, so no module imports another), and a ninth (opus) did the frontend's inductive lines. The
interface held: the merge found one name mismatch (`cons_block_recs_t_f`/`_tf`) and five call
sites passing an `EREC` slice where the convention wants an `IW` copy (fixed by the lead).

* **The work pool `IW`** (array 200, top `CTL[200]`): every value the stage builds, bump-allocated
  (`iw_alloc`), immutable once built, reset at the stage's entry. Lists are `(off, len)` slices
  (`take`/`drop` are free), a list of composite values holds pointers to records; a table of the
  record layouts is in the file's doc, with an `Option`-valued decoder per record (`decBS`,
  `decMS`, `decRS`, `decCtx`, `decNK`, `decNS`, `decTM`, `decCS`, `decCR`, `decCC`, `decCG`, …).
* **Constants** stay `EREC` records (lane `pinsenv`'s `decCI` layout, the constant value inline at
  `p + 1`); a new one is allocated there (`erec_alloc`, `CTL[129]`); every list a function takes is
  an `IW` slice (`er_to_iw`, `cv_lps` copy a constant's level parameters).
* **Environments are view words** (`fe` → `vis`, `fe.restrictTo k` → `k`); a function returning
  an `IFEnv` returns the new view.
* **Per-call memos** (`mentionsAnyGo`, `nestOccGo`, `depthGo`, `replaceFVarsGo`, `replaceAppsGo`,
  `targetAbsGo`, `hasLooseBVarBGo`, `mentionsConstGo`): `MemoLib` schemas on arrays 201‥208
  (`CTL` 202‥217), cleared where the twin starts from `∅`; `replaceFVars` nests inside itself
  (through `nestHoleImg`), so it uses lane `libs`' banks (`CTL[218]`, `[219]`).
* **Naming and calling rule**: the L name is the twin's in snake case; parameters in the twin's
  order (`mode`, `checkFuel` dropped, lists two words, records one pointer); results flattened up
  to six words. With the rule, every module could call every other one without coordination.
* **Mode**: L implements `.verified` only. Fuels: `coreWalkFuel` and the positivity walk's fuel are
  explicit words (ROADMAP §3 (b)); every twin `fail` is `abort` (§3 (c)).
* **The stage relation and the refinement shape**: `StageR dn vis fe m a := CheckR dn m a vis fe ∧
  IWOK m`; `RefAM p f args pre op post` (from `pre`, a returning run keeps the locals, the twin's
  `op` succeeds, `post` relates the memories, the twin state after, the results and the twin's
  result); `KeepPost`/`EnvPost` the usual posts; `IWGrow` (the pools only grew).
* **Stubs** (`stubFns`, 36 callees of other lanes: `whnf`, `infer_type_core`, `is_def_eq_core`,
  `ensure_sort_core`, `check_constant_val`, `strip_pis`, `open_pis_at_fvars_f`, `get_app_fn`/`args`,
  `instantiate1_fast`, `abstract1_fast`, `inst_lp_fast`, `bvar_b`, `fvar_b`, … with their calling
  conventions in the doc: **requests to the owning lanes**). Their specs are `IndStubs.lean`, one
  `RefAM` statement each, for any program, proved by `sorry` (a caller's refinement through them
  inherits the `sorry`, the honest census status).
* `IndProg.lean`: the whole stage program (the modules, the library, the stubs, master's functions
  as stubs) passes the compiler's `Prog.wf` (every call resolves with the right arity, ≤ 6 results,
  distinct names) by `decide +kernel`. A results-count check (callers never read more results
  than the callee returns, Unit-valued callees aside) was run by `#eval` at the merge.

### Measurements (lines, `wc -l`; L lines inside `lfn` bodies)

| file | lines | L lines | twin functions (`l_impl`) | worker |
|---|---:|---:|---:|---|
| `IndIface` (layouts, decoders, library, stubs) | 808 | 243 | 1 (`nameNodup`) | lead |
| `IndParts` (BlockParts, FieldTele, BlockRec, `checkDecl`'s arm) | 868 | 541 | 29 | sonnet |
| `IndInstall` (BlockInstall, BlockTail) | 767 | 472 | 22 | sonnet |
| `IndSum` (SumInstall, StructInstall, StructParts) | 751 | 445 | 33 | sonnet |
| `IndPos` (Positivity: walks, readback) | 765 | 493 | 29 | sonnet |
| `IndPos2` (Positivity: `nestPos` block, root, seeds) | 921 | 602 | 23 | sonnet |
| `RecClass` (ClassRead, GenRec generator) | 686 | 467 | 24 | sonnet |
| `RecGen` (GenRec stage) | 907 | 595 | 25 | sonnet |
| `RecCheck` | 923 | 607 | 25 | sonnet |
| `Front/IndFields`, `Front/IndApply` (inductive lines) | 314 + 640 | 534 | 9 (+ scanners) | opus |

The stage is 4.2k L lines for 7.2k Rust lines (**0.58 L per Rust line**, the scanner's rate) and
~2.4k twin code lines; every module file builds in under 10 s (L definitions, `Prog.wf` by
`decide +kernel`, `#guard` runs of the stub-free paths). Wall time: the eight translations ran in
parallel, 20–32 min each (sonnet, 250–320k tokens each); the interface took the lead ~35 min.

### Proofs so far (bottom up)

* `IndLibSpec.lean` (518 lines): the slice library is recursive in the slice (lane `levels`'
  `lv_mem` shape) and specified by word models; `SlR` (the slice as an inductive relation of its
  words, no `Nat` offsets: no overflow side conditions) with `slR_of_decHL` from the `Option`
  decoders; **`sl_nodup` refines `nameNodup`**; `iw_alloc`, `rec2` specs; `CheckR.frame_iw` (a pool
  writer keeps every tier); growth lemmas; decoded-field read lemmas.
* `IndView.lean` (240 lines): **`e_view` refines `view`** (`eViewW` the word model, `ViewR` the
  view's words, `eViewW_ok` one case per tag over lane `exprops`' `View.lean` lemmas plus field
  lemmas for `sort`/`const`). Every function matching on a view goes through it.
* `IndPartsSpec.lean`: `block_shape_k` refines `BlockShape.k` (the exemplar for record
  projections). Workers continue per module (`*Spec.lean`).
* Census at this landing (master `dc2c9bd` + this lane): phase 8 **4 proven, 211 written, 8 todo**
  (the `todo` are `where`-helpers and constants with no code of their own, and `PropWhen.isNever`);
  before: 3 proven (covered `PropWhen` helpers), 0 written. Totals 286 proven / 13 sorry / 262
  written of 1352. The stale flags of phase 8 after con-ron's bump (`12752ca7`, the eager tower's
  memos inside `Core.lean`) were reviewed: the conventions of the core stubs did not change.

### Round 2–3: the proof template (second landing)

* **Model first, twin after** (`IndSumSpec.lean`, `structPsAtGo_refines`, `@[refines
  structPsAt.go]`, a recursion that interns, recurses and allocates): (1) a word model of the L
  function calling its callees' word models (`binternW`, `consW`, `allocW`) and itself at the L
  fuel, every match on a callee result a continuation def with `rfl` arm lemmas, the model
  returning exactly the L result list; (2) its `vcgen` spec with callee **model** specs only;
  (3) a relational lemma by fuel induction (`… = some (r, m') → ArenaR m a → ∃ xs a', twin.run a =
  .ok (xs, a') ∧ ArenaR m' a' ∧ IWGrow m m' ∧ decoding`); (4) the census theorem by `triple_post`.
  Workers who put twin values into `vcgen` (`RefAM`-shaped callee specs) hit unmatched callee
  specs and a grind arithmetic cap on every recursive function; the split made both go away.
* **Stubs as one opaque model** (`IndStubs.lean`): `opaque stubM (f : FnName) : Mem → List Word →
  Option (List Word × Mem)`; one `stubM_spec` (a call of any stub is its model) and one `RelAM`
  per stub (a model run from the stage relation is a twin run), all `sorry`. A stub enters a
  proof exactly as a translated callee.
* Library models: `IndCopy.lean` (`allocW`, `copyW`/`copyW_get` — what a copy leaves, Nat offsets —,
  `consW`/`consW_dec` — `x :: xs` decodes, the pool grew, `MemFrame [IW] [200]`), `IndView.lean`.
* Proved at this landing (phase 8, `@[refines]`, no `sorry`): `BlockShape.k`, `.numCtors`,
  `.rulePrefixAt`, `.majorIdxAt`, `numCtorsOf`, `ClassSlot.isMinor`, `NestFieldKind.flat`,
  `NestCtx.hiAt`, `nestKeyMap`, `structPsAt.go`, `structElimLevel`; partial (`refines_part`):
  `targetMajorAt` "hit", `targetCtorAt` "member"; outside phase 8: `view`, `nameNodup`. Census:
  phase 8 **14 proven** (incl. the three covered `PropWhen` helpers), 201 written, 8 todo; totals
  301 proven / 46 sorry / 260 written of 1352 (master `e983ae3` + this lane).
* Round-1 bugs the proofs found: `nestFrameMates.go` read `IndCaps.all` from `IW` (it is an `EREC`
  slice); five call sites passed `EREC` level-parameter slices to callees that read `IW`.
* Worker findings: callee specs must be cited up to their fuel argument (`spec p hx n`) — fixing
  later arguments makes `vcgen` find no spec; a wrapper at fuel `n + 1` calls its callee at `n`;
  `finish` needs `rdW_eq` to bridge `rdW` and `ld64`'s `a[i]`; a post `r.getD 1 0 = …` confuses
  grind (state `r = [a, b]`); intern results need an L guard `if 4294967296 <= b { abort }` (the
  store specs do not bound the word; the front does the same); no Mathlib tactics (`by_contra`,
  `set`).
* Helpers: from this landing on at most three at a time (PLAN.md "Fan-out").

### Findings

* **Interfaces first scales to eight workers**: a written calling rule (names, parameter and
  result flattening) plus record layouts let modules that call each other be written without
  seeing each other; `Prog.wf` on the assembled program is the cheap integration test.
* Conventions that a worker can get wrong silently: which array a slice lives in (five call sites
  passed `EREC` slices to callees that read `IW`); `Prog.wf` cannot see it. A typed slice (array
  in the type) would catch it at the decoder level; the refinement proofs will.
* `u64(c)` takes a single comparison (no `&&`/`||`), and `len` is a keyword (no variable of that
  name): both hit by several workers; worth a line in the L notation's doc.
* Lean `do` lifts every `(← …)` of a statement before it (no short circuit in `(← a) && (← b)`):
  the brief said so explicitly and the workers kept effects in order.
* `rw [decX] at h; simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h`
  destructures a record decoder (plain `simp [decX]` leaves the elaborated `match`).

### Requests

* Lanes owning the stubs (whnf/defeq/infer: `whnf`, `infer_type_core`, `ensure_sort_core`,
  `is_def_eq_core`; expr ops: `strip_pis`, `strip_lams`, `open_pis_at_fvars_f`, `get_app_fn`,
  `get_app_args`, `mk_app_n`, `fvar_type_d(s)`, `pi_result`, `inst_lp_fast`, `inst_pis_at_lift`,
  `instantiate1(_lift)_fast`, `abstract1_fast`, `bvar_b`, `fvar_b`, `has_fvar_fast`,
  `loose_bvars_bounded_fast`, `all_level_params_defined`; decls/pins: `check_constant_val`,
  `consts_resolve_ffast`, `is_proj_fn_shape`, `reserved_rec_name`, `rec_rule_bits`, `proj_table_name`,
  `basis_pin_hit`, `check_basis_decl`, `ind_params_ok`; stores: `intern_ls_iw`, `name_rec`,
  `name_rec_i`; levels: `lv_zero_caps`): the conventions in `IndIface.lean`'s `stubFns` doc, the
  specs in `IndStubs.lean`. A lane may change a convention; then grep the call sites.
* Lane `pinsenv`: `EnvR` must survive appends to `EREC` above its top (`erec_alloc` + record
  writes): every record `EnvR` decodes lies below `CTL[129]`. Today `EnvR.frame` forbids any
  `EREC` write. The declaration fold's `.indDecl` arm calls `check_ind_decl(vis, boff, blen, nP)`
  (`IndParts.lean`, the block an `EREC` slice of constant records).
* Lane `front`: inductive lines are translated (`Front/IndFields`, `IndApply`) but not hooked in:
  `DeclAt` needs the `.indDecl` case (`IndDeclAt`, `DIND` = array 69, `IFR`/`IFL` = 70, 71 scratch)
  and `apply_dline`'s pl-25 branch `z := call apply_ind_line(j)`; `frontAllProg` gains the two
  modules' functions (doc of `IndApply.lean`).
* Memory map additions: arrays 69‥71 (front, inductive lines), 200‥208 (`IW`, the eight walk
  memos), `CTL` 200‥219.

### Stale flags after the con-ron bump (reviewed by hand, census not run)

The census lists 28 phase-8 targets as stale after `4c9eaf7 → 12752ca7`. Every one has its own code
unchanged; what changed below them is only `readLevelM`/`readLevelsM` (`Monad.lean`), whose diff is
doc-comment line references only. False positives: to be cleared with `scripts/census.py
--reviewed` once the census runs again (lane `censusmem`'s memory guard). Also proved since the
second landing: `classOfMotiveVar` (through `sl_find`'s model, `findW_ok`); **`checkBlockDomsAt`
through the stubs** (`IndInstallSpec.lean`: model `domsW` calling `stubM "fvar_type_d"` and `stubM
"is_def_eq_core"`, the twin side from their `RelAM` statements — census status `sorry`, inherited
from the stubs only: the first skeleton function refined end to end through stubs; finding: a
stub may grow memory, so decoded argument slices are carried by `decHL_grow` and the caller passes
`off + len ≤ iwTop`); `IndCopy2.lean` (worker): models and `_dec` lemmas for `sl_snoc`,
`sl_append`, `er_copy`/`er_to_iw`, `rec2`‥`rec6`.

### `sorry`s

`IndStubs.lean`: the 34 stub specs (by design, above). No other.

## Phase 2 continued: the ROM, the pins, the declaration loop's callees (2026-10-21, lane `decls`)

### The ROM (`Rom.lean`, `RomPins.lean`)

con-ron interns con-leche **values** (the pinned names, basis blocks, axiom shapes, pin sets) at
startup and inside some checks. In L they are bytes of the program's constant data: one byte
string `rom` (`ldc`, `rom.c8[i]`), every ROM reader a function of `rom` (the program fixes it).

* **Encoding, no decoder.** `encName`, … serialise a value prefix first, in the twin's intern
  order (a node's tag byte, its children as the twin interns them, then its payload; numbers 8
  bytes little endian, strings their UTF-8 length and bytes). A reader's spec is stated at
  `rom.drop pos = enc x ++ rest` and proved by induction on `x`; the ROM's contents enter only
  through that equation, which for the program's ROM (`enc A ++ enc B ++ …`) is `List.drop_append`.
  No kernel evaluation of a decoder; `RomOK rom` (`length < 2^63`) is the one `decide` (0.8 s
  for the names).
* `rom_u64(i)`, `rom_put(i, l)` (ROM bytes to the pool top, `str_put`'s analogue: `Grows`, the
  slice is `strWords`), `rom_name(pos)`: **refines `internName`** (`romName_refines`, `@[refines]`):
  `ArenaD` kept, the store tier only written (`MemFrame StoreA StoreC`, arrays and `CTL` words
  below 64), the position after the encoding returned. Proof shape: the W-model (`romNameW`, one
  continuation per call, grind arm lemmas) for the L side, then a pure induction on the name
  over the front's `_A` lemmas (`nanon_A`, `nstr_A`, `nnum_A`).
* `rom_names_to(q, k, d)` (`internNameList`, the handles to `PINS[d ‥]`) and
  **`intern_reserved_pins()` refines `internReservedPins`** (`internReservedPins_refines`): from
  `ArenaD` (any pin table), with `encNames pinNames ++ encNames reservedBasisNameValues` at the
  offset `off` the program is built with: `PinsFull` for the twin's new table and the flag set,
  `ArenaD` kept, writes only the store tier and `PINS`. So **`PinsR` is established from the
  initial state** by one call. The twin's run is assembled from its six pieces
  (`internReservedPins_run`, `run_bind_ok`); `AM.st`/`AM.res` must be `local irreducible` there or
  `rfl`/`rw` time out unfolding the stores.
* Memo: `internExprGo`'s `EMemo` (per call, keyed by `Expr` value) is transparent (a memo hit is
  a re-intern of a present subtree, which changes nothing), but proving that needs "re-interning
  a denoted tree is the identity" on the twin side (the stores' `consP`/`consS`); the expression
  ROM reader is not written yet. Not mirrored, its cost is a re-walk of constant data at startup
  and in the rare pin checks.

### `EnvR` over the pool below its top (`Tiers.lean`, at lane `induct`'s request)

`EnvR`, `PendR` and `vgOut` decode records in **`erecP m` = `EREC` below `CTL[129]`**, not in
the whole array. A writer that allocates above the top (`erec_alloc`) and writes there keeps
every decoding: the decoders are stable under extension (`ArrExt`, `EnvRec.lean`: a successful
decode read only words that exist), `ErecGrow m m'` (top up, nothing below the old top changed)
gives `ArrExt (erecP m) (erecP m')`, and `EnvR.grow` carries the environment. `erecP_ext`:
a decoding in `erecP m` is one in `m.arr64 EREC` (callee specs of lanes `whnf`/`induct` that decode
in the whole array take it from there). `EnvR.frameN` now also keeps `CTL[129]`.

### The fold's `And` pin (`DeclAndPin.lean`)

`and_pin_ok(i)` **refines `andPinOk`** for every record kind the front produces (`DeclAt`:
axiom, definition, theorem, opaque, quotient): the name word of record `i` cut to its low 32
bits (`decI` reads only those, so no bound on the front's word is needed) against `PINS[12]`,
`PINS[49]`, `PINS[50]`. Tagged `refines_part … "one-constant records"`: the `indDecl` arm
(`canonEqList` against the interned `andPin`, ROM) waits for the front's inductive records. The
stub and its `sorry` are gone from `Checker.lean`; the skeleton theorems take `DeclCallees p`
(the callees' lookups). `LoopR`, `PendR`, `dsAt`, `vgOut` moved to `DeclBase.lean`.

### Levels, and what comes next

`rom_level(pos)` **refines `internLevel`** (`RomLevel.lean`, same shape as `rom_name`; the
`.max`/`.imax` arms one template). `internReservedPinsL` (the census link) is
`internReservedPinsAt 0`: the program's ROM starts with the two pin name lists.

Next, in order (designs settled, not written):
* `rom_levels` (`internLevels`): the level handles on a stack array `RSTK` (138, top `CTL[131]`),
  copied to the pool top, then `intern_ls`; a parameter's name writes the pool between levels.
* `rom_expr` with the twin's `EMemo` **mirrored exactly**: the encoder threads the list of
  compound subterms already interned in the current call and emits a back reference (tag + index)
  where the twin's memo hits; L keeps the handles in `RMEMO` (139, count `CTL[132]`), reset per
  call. The relation (memo keys = the encoder's list, `RMEMO[k]` the handle of entry `k`) needs
  no kernel evaluation of the ROM.
* constant records into `EREC` (`internCV`/`internCI`/`internCIList`), then `internAllPins`.
* `install_step_go` on lane `induct`'s conventions (`StageR`, `RefAM`, the stubs of
  `IndStubs.lean`); `LoopR` gets `IWOK`; the callees' frame for `PEND`/`DECL`/`DLP` from the text
  (`closedW` over a concrete `declProg`). `check_value_group` likewise.
* Stale: `installStep`, `installDeclStep`, `checkPending(List)` wait for lane `whnf`'s `CoreR`;
  `checkDecl`/`checkShapelessFormers` are lane `induct`'s L code. Not reviewed (census paused).

### The ROM interner, complete (`RomLevels`, `RomExpr`, `RomExprRef`, `RomItems`, `RomCI`, `Prelude`)

* **Level lists** (`rom_levels` refines `internLevels`, `rom_lvls_go` refines `internLevelList`):
  the handles go to a stack `RSTK` (138, top `CTL[131]`, a ROM-interner scratch) because a
  parameter's name writes the pool between two levels; then `stk_pool` copies them to the pool
  top and `intern_ls` interns the slice.
* **Expressions with the twin's memo mirrored exactly** (`rom_expr` refines `internExprGo`): the
  encoder `encExprM seen` threads the list of compound subterms the twin's `EMemo` holds and emits
  a back reference (tag `9`, index in `seen`) exactly where the memo hits; L keeps the handles in
  `RMEMO` (139, count `CTL[132]`). `MemoR` (count = `seen.length`, `RMEMO[k]` is `m[seen[k]]`,
  every key in `seen`) and `encExprM_seen` (the encoder adds only subterms, so a node is never in
  its own children's `seen`) are the whole argument. No tree comparison in L, no kernel evaluation.
* **Item streams** (`rom_items` refines `runItems`): every constant interner's store effect is a
  sequence of primitive interns (name, level, level list, expression, memo reset), so the ROM holds
  `encItems` of the twin's items and one L function runs any of them. `RomCI.lean`: `Sim x m is
  proj` (the twin's `x` runs to the state `runItems m is` reaches, `proj` of its result is the
  memo), compositional (`Sim.bind`), proved for `internNameList`, `internLevelList`,
  `internExprList`, `internCV`, `internCaps`, `internFire`, `internRule(s)`, `internCI`,
  `internCIList`; `SimZ` for fresh-memo blocks; `simZ_internAllPins`. The interned *values*
  (`IConstantInfo`s, pin variants) are not built: their consumers will read `EREC` records.
* **`intern_all_pins` refines `internAllPins`' store effect** (`refines_part … "the store effect"`),
  from `ArenaD` at a filled pin table (the pin reads in the walk need it; `PinsReadyP`, kept by
  every intern: `keeps_runItems` on `cp`).
* **The program's ROM** (`Prelude.lean`): `romData` = the pin names, then the walk's items
  (9542 bytes); `romData_len`, `allPins_fits`, `allPins_noProj` by `decide +kernel` (seconds).
  `internReservedPins_rom`, `internAllPins_rom`: the two startup stages for the program's ROM.
  **The ROM carries no `Nat`-operation pin variant** (`romPins = []`): the final theorem holds at
  every pin list, so this costs completeness (pinned `Nat.div`-family definitions are declined),
  never soundness. A real variant (con-leche's `natOpPinSets`, ~650 KB of proof terms per dump)
  needs a ROM loader that does not evaluate the data in the kernel.
* Finding: chained callee posts of the form `s' = s₀` (whole state) made `finish` take ~80 s and
  its proof term overflow the kernel's stack ("deep recursion"); `LocEq s' s₀ ∧ s'.mem = s₀.mem`
  is instant. Also a function with many arms is better split (`rom_expr` → `rom_ex_leaf`,
  `rom_ex_ref`, `rom_ex_one`, `rom_ex_two`, mutual by fuel, one step lemma each).

### Phase A's step and phase B's check in L (`DeclStep.lean`)

`install_step_go`, `check_decl` (an inductive block, kind `6`, is copied from the front's `DIND`
into `EREC` and checked by lane `induct`'s `check_ind_decl`; every other kind goes to the stub
`check_decl_const`), `install_header`, `install_value_guards`, `erec_ci`/`erec_vg` (records from
the front's), `check_value_group`, on lane `induct`'s conventions (`IW`, `EREC`, the view word, the
stub names of `IndStubs.lean`); `declStepProg_wf` (`Prog.wf` with lane `induct`'s whole stage).
The two Checker stubs are gone; their specs stay `sorry` until the callees' specs are in. To
prove them: `LoopR` gets `IWOK`, and the frame on `PEND`/`DECL`/`DLP` comes from the text
(`closedW` over `declStepProg`).

### `sorry`s

None new (the four remaining stub specs of `Checker.lean` are lane `pinsenv`'s).

## Census memory, and the fingerprints dropped (2026-10-22, lane `censusmem`)

The census took the machine down twice (the session has a 50 GB memory cap; the census was seen at
18 GB). Measured under a watchdog (tree RSS polled every 0.2 s, killed by pid at 8 GB): the target
pass alone (import `ConAgua.Final.Twin`, walk, fingerprints) peaks at 2.3 GB in 0.8 s, so the
fingerprints were not the cause (`Expr.hash` is cached in the `Expr`). The link pass was: it
imported all 165 modules, and on a module clash retried with fewer, all in one process. Lean never
frees an imported environment, a failed `importModules` leaks what it read, and (presumably) a re-import of an
olean whose fixed mmap address is taken reads it into the heap: about 2 GB more per attempt
(measured: root alone 2.3 GB, root plus one more import 4.2 GB; there are seven clash retries). Killed at 8 GB after 4 s.

* **Fix: one import per process.** `lake exe census ROOT MODULE...` is now a driver that runs
  itself (`IO.appPath`) as `--targets ROOT` and then once per link-group attempt as `--links
  MODULE...`, one child at a time. A child that hits a clash prints the modules to defer (`C`/`D`
  lines, exit 3) and the driver retries without them; the driver drops `L` lines of modules an
  earlier group printed. Same groups as before, same output: `docs/progress.md` regenerated
  identical at `c33ad06`. Peak 2.8 GB (python + lake + one child), about 38 s.
* **Guard.** `scripts/census.py` runs the exe with its output in temporary files and polls the
  resident memory of its process tree every 0.2 s; above `MEM_LIMIT_GB` (6) or after 600 s it
  kills that tree by pid and exits with an error. `CENSUS_PEAK=1` prints the peak.
* **Fingerprints dropped** (decision with the user): not how con-ron syncs, and per toolchain.
  Gone: the `F` lines, the stale flag and section of `docs/progress.md`, `--stale`, `--reviewed`,
  `--record`, `docs/twin-fingerprints.tsv`. `scripts/bump-con-ron.sh` now builds, runs the census
  and lists the changed upstream files. TODO: staleness by source citations (`con-ron:
  ConRon/Arena/File.lean:120-200 name` doc lines on our L code and proofs, a pure-Python gate like
  con-ron's `scripts/provenance.py`), a separate lane. The dashboard's stale card
  (`docs/dashboard.html`, `scripts/dashboard_data.py`) now reads an empty list.

## Provenance: citations instead of fingerprints (2026-10-22, lane `provenance`)

Which L code must be looked at again when con-ron moves, now that the census fingerprints are gone
("Census memory"). The answer is con-ron's own (`_tmp/ref/con-ron/scripts/provenance.py`, its
DESIGN §3.7 and §7): every ported item cites the twin source it stands for, and a pure-Python gate
diffs the cited text between two upstream revisions. Ours is `scripts/provenance.py` (~1000 lines,
stdlib only, reads `_tmp/ref/<repo>` with one `git cat-file --batch` per tree). Workflow: PLAN.md,
"Bumping the twin".

### Decisions
* **The citation.** A line in the declaration block (doc comment, attributes, `--` lines directly
  above the `def`): `con-ron: ConRon/Arena/Core.lean:3682-3688 ConRon.Arena.flushCaches` (or
  `con-leche: ConLeche/Frontend/Scan/Fast.lean:… ConLeche.Frontend.strClose`, or `con-ron: none —
  <reason>`), optionally followed by ` — <prose>`. The range is the whole block (doc comment and
  attributes to the next column-0 declaration), the name fully qualified, as in `@[l_impl]`. A
  line after `con-ron:` that starts with anything but `ConRon/`, `ConLeche/`, `none` is prose
  (`WhnfIota.lean`'s older `` con-leche: `CoreDefs.lean:51-58` `` notes) and is not checked.
* **Upstream paths and revisions, not the vendored tree.** The path is the vendored one
  (`vendor/con-ron/ConRon/…` = upstream `proof/ConRon/…`), the line numbers are upstream's at the
  revision in `vendor/UPSTREAM`, read from the reference clones. `update --old <rev>` is then a
  diff of two upstream commits that our patch series never enters, and the old text is always
  there (any commit the clone has). The patches move no line of cited code today, so `check`
  falls back to `vendor/` when a clone lacks the revision.
* **What must cite:** every `def`/`abbrev … : FunDecl :=` under `ConAgua/**` (`ConAgua/Spike/`
  exempt). Lean models of ours may cite; a citation anywhere is checked. Each `@[l_impl T]` target
  must have a citation naming `T`, so the attribute and the citation cannot drift; `annotate`
  writes the citations the attributes imply.
* **Format of the insertions** (merge friendliness): an item without a doc comment got a new
  one-line `/-- con-ron: … -/`; an item with one got a `-- con-ron: …` line right after it. Every
  edit of this lane to `ConAgua/**` is an inserted line.
* **Helpers below** (the gap a pure range diff has). con-ron needs nothing extra: its Rust and arena
  port every con-leche declaration one to one, each with its own citation, and `coverage` lists
  what is not cited. Our L functions inline twin helpers (`flush_caches` has no L function for
  `Caches.empty`). So `update` also diffs every declaration of the changed upstream files
  (comment-stripped), builds a textual call graph of the twin (identifiers resolved under the
  enclosing namespaces and the file's `open`s), and marks a cited item when an UNCITED declaration
  at most `--depth` calls below its twin (default 1) changed. Cited callees are not looked
  through: they get their own finding. Changed structures and inductives are reported as `TYPE`
  (a question for the relations, `CoreR` and friends), not followed: following them flags every
  function whose signature mentions `Caches`. Depth 3 gives 28 findings on the test below, nearly
  all through the uncited knot (`inferTypeCore → coreKnot → enterEager`), which is twin code no L
  function stands for yet.
* **Markers are a queue, not a red gate.** `update` puts `-- con-ron: CHANGED since <old> — …`
  under the citation; the owning lane re-checks and deletes it. `check` lists markers and passes;
  `check --strict` fails on them (con-ron fails; we land bumps with markers and let lanes drain).
* **Dashboard:** `update … --json FILE` writes `{old, new, counts, findings: [{kind, where, item,
  cites, note}], types}`; `bump-con-ron.sh` keeps it at `_tmp/bump-<short>/provenance.json`. The
  markers left on master are `check`'s `queue:` lines (`scripts/provenance.py check | grep
  '^queue:'`: file:line and the marker text).

### Numbers (master + this lane)
814 FunDecls: 716 cite twin code (622 citations generated from `@[l_impl]`, 127 FunDecls without the
attribute assigned by hand, by file: store `*_find`/`*_push` → `Tbl.find?`/`Tbl.push`, stubs and
pieces → the twin function they are part of), 98 `none` (memo library, limb arithmetic, scratch
arrays, ROM readers, compiler tests, benchmarks, examples). `check` 1.1 s, `update` 2.4 s.

### Test: `update --old 4c9eaf7` (the bump to `12752ca7`)
With the citations rewritten to their ranges at `4c9eaf7`: 3 MOVED (`flushCaches`, `enterScratch`,
`dropScratch`, Core.lean +18 lines), 0 CHANGED, `TYPE Caches`/`CState`/`ModeMemos`, 1 CALLEE:
`flushCachesL` (`Caches.empty` below `flushCaches`). Against the seven stale targets of the
fingerprint census: `flushCaches` found; `installStep`, `installDeclStep`, `checkPending(List)`
reach `Caches.empty` only through `flushCaches`, which is cited and flagged itself (the fix is
there); `lvlEq?`/`lvlsEq?` changed only by elaboration (`{ s.caches with … }` over the new field)
— here that is `TYPE Caches`, and their callees `readLevelM`/`readLevelsM` changed in comments
only (lane `induct` found the same by hand). Afterwards `check` passes at `12752ca7`.

### Migration notes (for every lane)
* New L code must carry a citation: write `@[l_impl T]` and run `scripts/provenance.py annotate`
  (or `locate T` and paste), or write `/-- con-ron: none — <why> -/` for plumbing.
* `scripts/provenance.py check` must pass before landing (a second; no build).
* A `-- con-ron: CHANGED since …` line on your code: compare your L code and proofs with the
  printed diff (or `git -C _tmp/ref/con-ron diff <old> <new> -- proof/<path>`), fix, delete the line.

## Phase 8 proofs, bottom up (2026-10-22, lane `indproofs`)

The lane proves the inductive stage's L code against the twin with lane `induct`'s template
(`IndSumSpec.lean`'s `struct_ps_at_go`: word model, `vcgen` spec with callee models, relational
lemma by fuel induction, census theorem by `triple_post`), leaves first, with three sonnet
helpers (`parts`: `IndParts`/`IndInstall`; `rec`: `Rec*`; `pos`: `IndPos*`) and the lead on
`IndSum` and the shared library.

### Shared pieces (lead)
* `IndMaster.lean`: master's callees under the stage relation, sorry-free — `internBVar_stage`,
  `internFVar_stage`, `internSort_stage`, `internConst_stage`, `mkApp/Lam/Forall/Let/Proj_stage`,
  `internParam/Zero/Max_stage` (from master's `_D`/`_ok`/`*intern_correct` lemmas and
  `StageR.of_walk`: a writer below array 64 and `CTL[64]` whose twin keeps caches and pins keeps
  `StageR`), `consW_stage` (`sl_cons`), `allocW_stage` (`iw_alloc`), `DerR.lvl` (`DerR` reads the
  expression tables only). With these a master callee enters a proof exactly as a stub does, but
  without `sorry`; no helper needed a `sorry`'d master stub.
* `IWOK` (part of `StageR`) now also carries `IW`/`EREC` lengths below `2^64` and `CTL[200]` in
  range: an allocation after a stub call needs them, and a stub's post (`KeepPost`) only carries
  `StageR`.
* `IndLibSpec`: `getW`/`getDW` (`sl_get`, `sl_getd`); `consW_dec`/`slCons_dec` are kind-generic.

### The template, and where it needed changes
* **Twins without equation lemmas.** Structural recursion that matches under a bind
  (`whnfTelescope`: `match ← view e', n with`) gets no equation lemma. Workaround
  (`IndSumSpec2.whnfTelescope_eq`): an own arm function (`wtArm`, the arms verbatim) and the
  unfolding `delta f; dsimp only [Nat.brecOn, Nat.brecOn.go, f._f]`, then `funext` under the
  two binds and `cases` on the view (`rfl` per arm). The matchers differ, so no plain `rfl`.
* **`while` loops become self-recursion** mirroring the twin's list recursion
  (`field_doms_resolve`, `idx_args_resolve`, and several in the helpers' modules); then the fuel
  induction applies directly. The recursion costs a call frame per element.
* **Handle bounds after an interning.** Master's intern models carry no `< 2^32` bound on the
  result; where the next callee needs `H r`, the L code gets the template's guard
  `if 4294967296 <= r { abort }` (a capacity abort; `whnf_telescope`, `param_levels_go`, and
  helpers' sites).
* Twins equal up to the error message (`checkStructDomsAt` vs `checkBlockDomsAt`): one
  `ok`-run transfer lemma by induction, the model reused (`sdomsW = domsW` with the results
  dropped).
* Pitfalls: a `local notation "V"` does not survive into the next `namespace` block (it becomes
  an auto-bound variable); `set` is Mathlib; `ViewR` uses `getD i 0`, models `tail.headD 0`.

### Numbers (first landing, 01:53)
* Census phase 8: **34 proven, 15 sorry (through stubs only), 166 written, 8 todo** (before: 15
  proven, 1 sorry, 199 written); totals 336 proven / 67 sorry of 1352.
* Lead (`IndSumSpec2.lean`, 1.3k lines): `check_struct_doms_at`, `field_doms_resolve`,
  `idx_args_resolve`, `struct_proj_arg_p`, `struct_ps_at`, `struct_proj_ps`, `whnf_telescope`,
  `param_levels_go`, `param_levels`. Helpers: see their landing lines below.
* Proof lines: ~6.4k added for ~40 `@[refines]` theorems over ~330 L lines, **~19 proof lines
  per L line** (the template's model + spec + relational lemma; the relational lemma is two thirds).
  Every spec file checks in 5–40 s; a `vcgen` spec is usually one `finish (gen := 20)`, the
  relational lemmas are hand-written case splits on the model's continuations.

### Landing 2 (02:20)
* Census phase 8: **46 proven, 26 sorry (through stubs), 143 written** (landing 1: 34 / 15 / 166).
* Lead: `struct_proj_guards_col`/`_row` (rewritten recursive; `used` read with the twin's
  `getD _ false` — the round-1 `sl_get` aborted out of range where the twin does not),
  `check_sum_tele_slow`, `check_sum_tele` (`IndSumSpec3.lean`), and in `IndMaster`: `erec_alloc`
  (`erAllocW`), `wrER`, `StageR.erec` (lane `decls`' `EnvR.grow`), `erRec_stage`, `cv_new`
  (`cvNew_stage`: the copied record decodes as `{cv with type := ty}`, `decCV_copy`); the
  `viewSort` bridge (`viewSort_of_view`); `struct_ps_at` under `StageR`.
* `decRL` (every slice-returning stub post) carries the pool-top bound, at helper `rec`'s request:
  without it a stub-returned slice cannot be kept decoded across a later growing callee, nor
  passed to `sl_cons`.
* Master callees without a stage lemma yet, `sorry`'d as stubs in `IndStubs.lean` by helpers:
  `pin_word(53)` (`zeroLevel`), `lvl_eq`. Both need `PinsR`/level-relation work, not a stub.

### Landing 3 (03:00): round-1 helpers done
* Census phase 8: **55 proven, 30 sorry (through stubs), 130 written** (start of lane: 15 / 1 / 199);
  totals 362 proven / 81 sorry of 1352.
* Lead since landing 2: `struct_ctor_resid_ok` (`IndSumSpec4.lean`; `hd` guarded below `2^32`).
* Helper `parts` (11 functions, ~4.5k proof lines, `IndPartsSpec2‥6`): `BlockShape.nIdxs`,
  `.memberNames`, `.lps`, `.allCtors`, `BlockParts.complete`, `piBinders`, `blockCounts?`,
  `recTargetOf`, `blockRecNamesUnreserved`, `blockRecLpsOk` (with an `sl_eq` model),
  `checkShapelessFormers`, `checkShapeless`, `BlockShape.withSort` (through `lvl_eq`). **Bug:**
  `member_names_copy` read `EREC[member]` (a member record's word 0 is the `cvT` pointer).
* Helper `rec` (21 tags, ~4.3k lines): the `RecClass` readers and generators (`classBinder`,
  `ClassGen.binder`, `exprGetD`, `fvarHead`, `closeLams`, `ClassGen.slotVar`/`.motVar`,
  `classRecOf`, `ClassRead.motiveSlot`/`.classes`/`.recCls`, `ClassGen.ihParts`), `classMinorSlot`,
  `classLeafAt`, `classStreamRecs`, `abstractPrefix(List)`, `targetHoles`, `targetPinTys`,
  `targetPiDomsWith`, `targetCtorAt` (now whole). **Bug:** `class_gen_ih_parts` read
  `IW[g+3+t]` for the class record pointer instead of `IW[IW[g+3]+t]`.
* Helper `pos` (~6.2k lines): `nestKindsFlat`, `nestBlockOf`, `nestResHead`, `nestCtorEntry`,
  `instPisWith`, `closeTelescope`, `nestCanonSub`, `nestFrameMates(.go)`, the memo walks
  `mentionsAnyGo`/`Const`, `nestOccGo`/`nestOcc`, `replaceAppsGo`/`replaceApps`, `depthGo`/`depth`,
  `whnfWalkFuel`, `memberIdxAt?`, `phApp`, `appHole`, `nestPhs`, `nestCanonCrest`.
* **Hypotheses beyond the stage relation** (preconditions a caller must discharge, listed so they
  are not forgotten): the memo walks take memo well-formedness (`maMR`, `rpMR`, `dpMR`, `noMR`;
  stubs give no frame, so it cannot be carried across a stub call — helper `pos` suggests putting it
  into `StageR`); `class_read_rec_cls` takes `hstab` (records stay decodable as the pool grows),
  `class_stream_recs` `RecsOK`, `class_read_classes` `SlotsExt` (records below the tops); several
  take slice bounds. A generic "decoders below the tops are stable under `IWGrow`" lemma (one per
  decoder today: `decHL_grow`, `decBL_grow`, `decCVp_grow`, helper `rec`'s `decCK_grow`,
  `decNL_grow`) would discharge most.
* L code: ~20 loops became self-recursion, ~15 handle/overflow guards after master interns
  (no bound lemma; master has `mkAppW_hw` for `mk_app` only).
* Cross-helper lemma-name clashes surfaced only when one file imported two helpers' files;
  `IndAll.lean` (imports every spec file, in the lakefile) now catches them.
* Round 2 (running): helpers `memo` (`IndSum`'s memo walks), `install` (`IndInstall`), `recb`
  (rest of `RecGen`/`RecCheck`).

### Landing 4 (03:20)
* Lead: `struct_proj_bodies_go`, `struct_proj_bodies` (`IndSumSpec6.lean`; the `struct_proj_arg_p`
  result guarded below `2^32`; `structProjBodiesGo` has its equation lemma, the view's arms by
  `tag_iff`/`eViewW_head6S`).
* File sizes (coordinator's build statistics): `IndPos2Spec`, `RecClassSpec`, `IndSumSpec2` split
  by pure moves into `IndPos2SpecA‥D`, `RecClassSpecA/B`, `IndSumSpec2A` (the old module imports
  its parts, names unchanged); every spec file is now below 1.4k lines.

### Landing 5 (03:45): round 2, and the lane's totals
* Census phase 8: **58 proven, 38 sorry (through stubs), 119 written, 8 todo** (lane start: 15 / 1
  / 199); totals 411 proven / 90 sorry of 1352.
* Round 2: helper `memo` — `mentionsConstGo`/`mentionsConst` (sorry-free), `hasLooseBVarBIns/Go/Fast`,
  `structUsedLaterGo`/`structUsedLater`/`structUsedLaterList` (`IndSumSpec5`, `IndSumSpec7`; memo
  relation `MemoRV` with values exactly `0`/`1`, since L tests `r1 == 1`); helper `recb` —
  `targetMajorDefault` (through a new `intern_nanon` stub) and eight `RecGen`/`RecCheck` pieces
  (`RecGenSpec2`, `RecCheckSpec2`); helper `install` — `IndInstall` pieces as `refines_part`
  (`checkBlockPositivity` init/member, `blockCapsAt` pieces, `checkBlockInds` piece,
  `checkBlockAgree` one-member body; `IndInstallSpec2‥4`). **Bug** (fixed by the lead):
  `check_block_agree` opened member 0's telescope and aborted on `ok0 = 0` also for an empty
  `rest`, where the twin does nothing.
* **Lane totals.** ~95 `@[refines]`/`@[refines_part]` theorems (89 + 6) over ~100 L functions;
  24.8k proof lines (spec files, `IndMaster`, library lemmas) against ~1.3k L lines proved, so
  **~19 proof lines per L line**, flat across modules; the relational lemma is about two thirds.
  L code: 778 lines added / 356 removed (loops to recursion, guards, two new helpers per loop on
  average). Wall time 2 h 47 min (lead), 7 sonnet helpers (3 in round 1 ≈ 2 h each, 3 in round 2
  ≈ 40 min each, plus `memo`), at most 3 at a time; each spec file checks in 5–60 s, `IndAll` (all
  of them) ~1 min of wall time on the shared cache.
* **Automation.** `vcgen` + one `finish (gen := 20)` proves almost every L-side spec unchanged
  from the template (≈ 25 % of the lines); the relational lemmas are hand-written case splits on
  the model's continuations (`cases h : callee …`, the callee's `_stage`/`RelAM` fact, the twin's
  run rewritten step by step). `grind` was not used on twin values at all.
* **Template changes, all rounds:** twins with no equation lemma (unfold by `Nat.brecOn` and an
  own arm function, `whnfTelescope_eq`, helper `memo`'s `hbArm`); loops become self-recursion;
  handle guards after master interns; master callees through `IndMaster`'s `_stage` lemmas instead
  of stubs; `IWOK` and `decRL` strengthened so allocations and stub-returned slices survive later
  calls; stability of decoded records across pool growth (one `_grow` lemma per decoder; a few
  helpers took a stability hypothesis instead, listed under landing 3).
* **Next** (lane or successor): an `env_push` word model under `StageR` (unblocks
  `consSumCtors`, `checkStructProjTable`, `classFeR`; `envPush_refines` exists but has no memory
  frame); `lv_leq_top`/`lvl_eq` under `StageR` (unblocks `checkStructFieldSortsI`,
  `blockLargeElimAllowed`, removes the `lvl_eq` stub); a generic decoder-stability lemma; memo
  well-formedness inside `StageR` (helper `pos`'s suggestion); then the remaining parents
  (`checkSumCtor(s)`, `sumRules`, `checkBlock*`, the `nest*` positivity block, `genRecCheck`).

### The frontend's inductive lines: hooked (2026-10-22, lane `front`)

The front's proven chain (`frontRun_refines` → `parseBytes`, `frontLine_refines` → `applyLine`,
`processLineCoreD` by parts) now covers `inductive` lines, without `sorry` and without a spec
hypothesis. Decisions:

* **The hook reads the block where the line scanner found it.** `decl_val` (`FieldsDecl.lean`)
  keeps an `inductive` member's value position in the `nm` field (`dnameN`), and `apply_dline`
  calls `apply_ind(nm)` at `pl = 25` (not `apply_ind_line`, which re-finds the first member: the
  link would need `next_member` ↔ `scanLineLoop` for the first member). `DeclR`'s `.ind` arm says
  the block scans there (`scanIndDecl b v = .ok (.ind …) e`), proved in `declLine_link`.
* **A fuel-indexed model under a fuel-free one: `runF`** (`RunModel.lean`). The apply step's
  models (`validateW`, `installW`, … ~40 of them) carry the interpreter's fuel; the line's model
  (`applyDLineW`, `frontLineW`, the driver's `lineKW`) does not. `applyDLineW p` takes
  `apply_ind`'s *run* in `p` as the model (`runF p "apply_ind" [nm] m`, `Classical.choose` of a
  successful run). It is well defined because the interpreter is monotone in its fuel
  (`exec_mono`, via `step_mono`: `step p k` is monotone in the continuation `k`) and a call's run
  does not depend on the caller's locals (`invoke_loc`); `runF_spec` is the callee spec, and the
  refinement goes back to the fuel-indexed model through `applyInd_spec` (`runF_some`). So the
  line models gained a `Prog` parameter.
* **`DIND` is `DLP`** (array 68), not a new array 69: one pool for the declarations' universe
  parameters and the blocks' constant records, so `DeclAt`/`decl_push` stay as they are.
  `DeclAt` is unchanged (lane `decls`' `DeclsR` relies on `indDecl` being `False` there); the
  front's relation is `DeclsF`/`DeclAtF` (`StateDR.lean`), whose `.indDecl` arm is `IndDeclAt`:
  the block decodes (`decCIs`, lane `pinsenv`'s `decCI` layout) in the pool truncated at a top
  `t` (`trunc`, so later appends keep it).
* **`vi_k_expected` compares with a heap `zero`** (`lh_mk(0,0,0)`, `lv_equiv`), which agrees with
  the twin's `Level.isEquiv _ .zero` only on a well-formed name store: the apply step needs
  `StateOK`. The driver's invariant `FrontInv` now carries con-ron's bridge invariant `TwinOK`
  (`StateOK`, scratch off, `PinsOK`, `PersStateD`, `StateDRel` to con-leche's state), kept per line
  by `ConRon.Bridge.Frontend.applyLine_run` and established by `StateD_init_run`; so
  `frontRun_refines`/`frontAll_refines`/`frontAll_run`/`frontAll_x64` take `StateOK a₀`,
  `a₀.store.scratchOn = false` and `PinsOK a₀`.
* **Scratch arrays**: `IFR`/`IFL` (70, 71) below `2^62` words (`StateDR.ifs`), the level heap at
  192: `frontAllProg_wf` is over 193 word arrays, `frontMemOf` has 224.
* Census: `frontLine_refines` is `@[refines applyLine]`, `frontRun_refines` `@[refines
  parseBytes]`; `processLineCoreD` is `COMPLETE_BY_PARTS` ("axiom, def, thm, opaque, quot",
  "inductive"); new `@[refines]`: `validateIndD`, `installIndD`, `parseRuleD`, `piResultD`,
  `indPiTeleLen`, `piSortTeleLen?`, `storeFuel`; parts: `parseCVD` (`ind_cv`), `viewN`
  (`name_rec_pre`), `scanIndDecl` (`ind_fields`).

Files: `IndRel`, `IndAlloc`, `IndApplySpec{,2,3}`, `IndApplyRefine{,2‥9}`, `IndValidTwin`,
`IndInstallRefine{,2‥5}`, `IndApplyTwin`, `IndFields{Spec,Link,Link2,Link3}`, `RunModel`,
`IndTest` (the `Unit` block through `front_run` of `frontAllProg`).

### `sorry`s
None but stubs': `IndStubs.lean`'s stub specs (now incl. `lvl_eq` and `intern_nanon`, master
callees without a stage model), and two stub-level statements in `IndSumSpec5.lean` (helper
`memo`): `bvarBCwf_spec` (`bvar_b` at `CWF` answers as the twin's `bvarB` at any plentiful fuel —
provable about the twin once `bvar_b` lands) and `stubHbFrame` (`bvar_b`, `strip_pis` leave the `hb`
memo alone — a write-set fact for the owning lanes).

## The fvar-range derived column (2026-10-21, lane `exprops3`)

Files: `ViewL.lean` (`packBF`, `packBF_bvar`, `packBF_fvar`), `ExprMk.lean` (`der_f`, packed `mk_*`),
`DerRel.lean` (`fvP`, packed `cP`, `derFW_ok`, the `fvar_der*` lemmas). No `sorry`.

* **No new arrays.** The five compound `XDER` words (42‥46) now hold both ranges, `packBF b f =
  b + f * 32768` (bvar range in bits 0‥14, fvar range in bits 15‥29). The earlier brief ("five more
  arrays or five wider ones") is settled for wider ones: array ids 49‥55 stay free, `CTL` untouched.
  `der_b` reads `& 32767`, `der_f` reads `>> 15` (`packBF_bvar`/`packBF_fvar`, `omega`).
* `der_f(h)`: `fvar` reads its own index from `FVREC` (`satSucc`, like `der_b`'s `bvar` arm reads
  `BREC`), the five compound tags read the packed word, every other tag is `0`. `mk_*` write
  `packBF (bvar range) (fvar range)`; the fvar range is a plain `max` of the children (a binder or
  `letE` does not shift an fvar, so no `satPred`; `derOfBind`/`derOfLet`).
* `DerR` keeps its 10 fields: `zP`/`bvP` gained the fvar conjunct, `fvar` has its own `fvP`
  (`fvarOfData = satSucc idx`), `cP` relates the packed word. `derFW_ok`: `derFW m h =
  fvarOfData (a.store.derived (decE h))`; `derBW_ok` re-proved for the mask.
* `mkLam/Forall/Let_spec` are now slow (`finish (gen := 40)` with `maxHeartbeats 0`; minutes under
  load). A future pass should split the arithmetic out of `finish`.

### Not done (carry over)

* `abstract1Go`: the cut-off is `fvarB ≤ d` where `fvarB` falls back to `fr_memo` on the saturated
  branch (not the raw field read of `lift`/`inst1`). L: `fvar_b(h) = x := der_f(h); if x == 32767
  { x := fr_memo(h) }`. Its refinement needs `DerR` kept across `fr_memo`: a model-level write set
  for `frW`/`frNodeW` (induction, `msetG_frame frSch` at each miss; `frNodeW_app` … exist). The memo
  `abs1C` (key `(h, k)`, `lfKey`) is array 49, `CTL[48/49]`: do NOT add it to `MemosR` without also
  clearing it in `scratch_enter` (`Scratch.lean` lists the four memo clears; `enterScratch` sets
  `Memos.empty`); a separate `Abs1R`/`ArenaA := ArenaD ∧ Abs1R` tier avoids that. The `fvar` leaf
  arm needs `.viewFVarIdx` (not `.view`): `getFVarIdx` is `(fvars.node? idx).map (·.idx)`, so a
  `viewFVarIdx_tier` + `view_fvaridx` pair copying `view_tier`/`view_fvar_idx` suffices. Draft
  (model, L code, specs, dispatcher, five arm proofs, entry) was written and the model/L/specs
  built, then lost in the machine restart; `Inst1*.lean` with `d ↦ k`, `v ↦ d` is the template.
* `instantiateListGo`/`instantiateList`: untouched (pool-slice reader; `PoolSlice.lean` already has
  the word-slice lemmas).

## `ExprMk` fast again; `abstract1`; `instantiateList` (2026-10-22, lane `exprops4`)

### `ExprMk.lean` build time

The packed `mk_*` stores (`x + (y - x) * u64(x < y) + (… ) * 32768`, lane `exprops3`) made
`finish` unfold `maxW`/`satPredW`/`packBF` and case-split on their comparisons inside every spec,
on top of the three-deep `der_b` result chain through `setLocs`: `mkLet_spec` alone ran > 10 min.
Fix: three equations naming the *evaluated L expressions* (`maxW_L`: `BinOp.add.eval x
(BinOp.mul.eval (BinOp.sub.eval y x) (Cmp.ult.evalW x y)) = maxW x y`; `satPredW_L`; `packBF_L`,
`rfl`), passed to `finish` in place of the unfolds. `finish` then matches the store word against
the model's `packBF (maxW …) …` with no arithmetic. `(gen := 20)` is still needed (default 8
fails on all five: depth of the `setLocs` chain); `maxHeartbeats 0` removed. Statements unchanged.

| `lake env lean ConAgua/Arena/ExprMk.lean` | real | user |
|---|---:|---:|
| before (gen 40, unfolded arithmetic; machine loaded) | 14 min 33 s | 14 min 58 s |
| after (named store arithmetic, gen 20) | 10.8 s | 20.6 s |
| (default gen 8: fails, 2 min 53 s user) | | |

Lesson (adds to PLAN.md's proof-style list): a value an L expression computes inline should be
matched by an equation on its *evaluated* form (`BinOp.*.eval`, `Cmp.*.evalW`), not by unfolding
the model's arithmetic; the latter costs a case split per comparison, per goal.

### `abstract1Go`/`abstract1Fast` (`Abs1.lean`, `Abs1Spec.lean`, `Abs1Refine.lean`)

`abs_entry(e, d, k)` refines `abstract1Fast F e d k` under `ArenaA` (`absEntry_refines`,
`absEntry_run`; axioms `propext`, `Classical.choice`, `Quot.sound`, **no `sorry`**), and
`ab_fvb(h)` refines `fvarB` (`abFvb_refines`). Census: `abstract1Go` and its five arms, `abstract1Fast`,
`fvarB` proven. `Inst1*.lean` with `d ↦ k`, `v ↦ d`, plus:

* **`ab_fvb`** (`fvarB`): `der_b`'s second result; on `32767` alone, `fr_memo`. Model `fvbW n`
  (`fvbN n` is `fr_memo` at its own fuel, `none` at `0`, so the spec holds at every fuel).
* **`ab_node`**: the cut-off has a memory effect (`fr_memo`), so `abs_go` is `x := ab_fvb(h); if x
  <= d { return h }; return ab_node(h, k, d)` and the dispatch is its own L function, with
  `absNodeA` naming the twin's `else` branch (`abstract1Go_succ'` by `rfl`). Three specs by fuel
  (`AbsGoSpec`/`AbsNodeSpec`/`AbsArmSpec`), three refinement statements (`AGoOK`/`ANodeOK`/`AArmOK`).
* **Rebuild on change** (`internRebuilt*`): L `if x == f && y == a { r := h } else { r := call
  mk_app(x, y) }`; models `rbAppW` … with guarded `_same`/`_new` equations; `rb_ok` relates both
  branches. The twin compares `decE x == decE f`: equal words give equal handles, and on the `new`
  branch `mk_*`'s own guard (`(x ||| y) >>> 32 = 0`, `mkAppW_lt` …) bounds the results, so with the
  view's bound on the children `decE_inj` gives the converse. No result-bound invariant needed.
* **The memo tier `ArenaA := ArenaD ∧ AbsR`** (`AbsR := MemoRG abSch lfKey decE m a.memos.abs1C`;
  `abSch = ⟨49, 48⟩`, array 49 `ABMEMO`, `CTL[48]`/`[49]`), kept out of `MemosR` as the exprops3
  brief says. It survives: the `mk_*` and `intern_bvar` by their model frames (`mkAppW_frameA` …,
  `binternW_frameA`: no write to 49 or `CTL[48]`) and by `Keeps (·.memos.abs1C) (internE v)`
  (`prim_keeps`); `fr_memo` by `frW_frame` (the model writes only `FRMEMO`, `CTL[46‥47]`; an
  induction with `FrOK` combinators for the continuations — `split at` on `frNodeW`'s `if` chain
  runs into simp's step limit, hence `by_cases` per tag over `FVarRange.lean`'s guarded equations)
  and on the twin by `Keeps fsp (fvarRangeMemo F e)` (`fsp a = (a.store, a.memos.abs1C)`, the
  `keeps_auto` recipe with a `fvarBSet` lemma for `fsp`, which is not `MemoBlind`).
* Callers that cross `scratch_enter` must re-establish `AbsR` (its memo is not cleared there); all
  current callers are the walk's own entry, which clears it first.
* Heartbeats: the five arm steps in `Abs1Spec.lean` need `maxHeartbeats 1000000` (the
  rebuild's `if`/`else` doubles the tail; `finish (gen := 20)` as `Inst1Spec.lean`).

| `abstract1` | Rust lines | L lines | spec lines | refinement lines | `lean` user |
|---|---:|---:|---:|---:|---:|
| `Abs1.lean` (models, L, go/node steps) | | 140 (L code) | 708 (file) | | 2.8 s |
| `Abs1Spec.lean` (arm steps, entry) | | | 174 | | 57 s |
| `Abs1Refine.lean` | | | | 1100 | 2.7 s |

### `instantiateList`/`instantiateListGo`/`instantiateListFast` (`InstList{,Spec,Refine}.lean`)

`inst_list(e, o, l, d)` refines `instantiateListFast F (decE e) vs d` under `ArenaL`
(`instList_refines`; axioms `propext`, `Classical.choice`, `Quot.sound`, **no `sorry`**), for any
`vs` with `SpineR m o l vs` (`WhnfBase.lean`'s stack-slice relation) and `o + l < 2^64`; the post
also says the stack array is unchanged. Both twins in L: the pure walk `il_go` + six arms
(`instantiateList`, `instListArm*`) and the memo walk `ilg_go` + five arms (`instantiateListGo`,
`instListGoArm*`), `Inst1*.lean`'s shape.

* **The pool-slice reader is the spine stack**, not the Nat-limb pool: the interface was already
  fixed by lane `whnf` (`InstListOK`, `inst_list(e, off, cnt, d)` over `SPN`, array 144, which
  `CoreS` sizes below `2^63`), and the callers in `WhnfCore`/`Infer`/`DefEq` already pass stack
  slices. L names array 144 `ILSPN` (a `module` file cannot import `WhnfBase.lean`).
* **The shrinking suffix** (`lastEidx vs q`) is the slice `(o + (l - q), q)`: `spineR_last`
  (from `lastEidx_toList`: `eidxCopyUpto` from `xs.size - k` is `drop`), `spineR_entry` for
  `vs[size - 1 - q]`, `slice_word` for the offset arithmetic. No copy, `O(1)`, as the twin's
  comment wants.
* **The slice survives the walk** because nothing the walk writes is array 144: every
  statement's post carries `m'.arr64 ILSPN = m.arr64 ILSPN` (from the `mk*W_frameA` frames of
  `Abs1Refine.lean`, the memo's frames), and `SpineR.of_spn` moves the slice across.
* **The memo tier `ArenaL := ArenaD ∧ ILR`** (`instLC` on array 50 `ILMEMO`, `CTL[50]`/`[51]`),
  `ArenaA`'s pattern; the pure walk carries it too (the memo walk calls it).
* **Hand-off to lane `whnf`** (`InstListOK`, a stub in `whnfCallees_stub`): what is left is the
  bridge from `CoreS` to `ArenaL` and back. `CoreS` has `ArenaD`; it lacks `ILR` (`instLC` is not
  in `MemosR`), so either `CoreS` gains an `ILR` conjunct (kept by every other writer's frame: array
  50 and `CTL[50]` are written by `inst_list` alone) or a variant of the entry lemma starts from
  any memory (the entry clears the memo first; `memoRG_clear` currently assumes a prior `MemoRG`).
  Census tag on `instList_refines`; `instantiateListFast` is phase 4.

| `instantiateList` | L lines (code) | file lines | `lean` user |
|---|---:|---:|---:|
| `InstList.lean` (models, L, dispatcher steps) | 230 | 935 | 4.5 s |
| `InstListSpec.lean` (arm steps, entry) | | 273 | 34 s |
| `InstListRefine.lean` | | 979 | 2.7 s |

**The L fuel against `coreWalkFuel`.** All three refinements here are "at every twin fuel `F ≥`
the L fuel `n`". The stub interfaces of lanes `whnf`/`defeq` (`InstListOK`, `HasFvarOK`) state the
twin at `coreWalkFuel` (4·10⁹) with no bound on `n`; the bridge needs `n ≤ coreWalkFuel` (the L
fuel of the top-level run bounds every nested call's), as the whnf slots already assume `n ≤ F`.

### `abstractRangeGo`/`abstractRangeFast` (`ArRange{,Spec,Refine}.lean`), `hasFvarFast` (`HasFvar{,Refine}.lean`)

* `ar_entry(e, d, k, c)` refines `abstractRangeFast F e d k c` under `ArenaA`
  (`arEntry_refines`, **no `sorry`**). `abstract1`'s files with the range `(d, k)` and the cursor
  `c` (memo key `(h, c)`, the same `abs1C`, `ab_fvb`, rebuild, `ArenaA`, probe/tail lemmas reused).
  Generated from the `Abs1*` files by a renaming script (`k ↦ c`, `k` appended after `d`), then the
  `fvar` arm and the entry by hand. The `fvar` arm checks `d + k` and `c + (d + k - 1 - i)` for
  wrap (capacities: the twin is over `Nat`; `dk_toNat`, `rng_iff`, `rng_word`). Entry: `k = 0` is
  `e` (no clear), else clear, walk, clear.
* `has_fvar_fast(f, e)` and `has_fvar(e)` (the two stub interfaces' names) refine `hasFvarFast F e`
  (`hasFvarFast_refines`, `hasFvar_refines`): `ab_fvb` and `u64(x != 0)`; `f` is unused.

| | file lines | `lean` user |
|---|---:|---:|
| `ArRange.lean` | 581 | 3.9 s |
| `ArRangeSpec.lean` | 173 | 64 s |
| `ArRangeRefine.lean` | 480 | 1.2 s |
| `HasFvar.lean` + `HasFvarRefine.lean` | 149 | < 2 s |

### `bvarB`, `looseBVarsBoundedFast` (`BvarB{,Refine}.lean`)

`bvar_b(f, e)` refines `bvarB F e`, `loose_bvars_bounded_fast(f, k, e)` refines
`looseBVarsBoundedFast F k e`, both under `ArenaD` (**no `sorry`**; the stub interfaces' names and
arities of lanes `decls`/`indproofs`, `f` unused). `fvarB`'s proof for the bvar range: `der_b`, on
`32767` `bb_memo` (`bbMemoW_correct`, `ArenaR`); `DerR` across `bb_memo` by `bbW_frame` (the
`frW_frame` induction renamed: `BMEMO`, `CTL[24‥25]`) and `keeps_bvarBoundMemo`.

Census, phase 4, after this lane: 62 proven / 1 sorry / 1 written / 49 todo (before `abstract1`
landed: 36 proven / 74 todo, counted after it). Left in phase 4 (todo): `instantiate1LiftGo`/`Fast`,
`instLPGo`/`Fast`, `leavesSubGo`, `wscopedBGo`/`Fast`, `fvarLeavesGo`/`Fast`, `stripLams`/`stripPis`,
`substLevelList`/`substLMemoAt`/`substLsMemoAt`, `leafGuard`/`leafMem`, `fvarTypeD`, `takeEidx`
(the twin's own helpers `internRebuilt*`, `eidxCopyUpto`, `lastEidx` stay todo: inlined in L, reached
from walks not yet ported).
## Definitional equality, inference, the knot: L code top down (2026-10-22, lane `defeq`)

Phases 6 and 7 (ROADMAP §1): con-ron's `Arena/Core.lean:2439-3675` and the helpers it reaches
(`:240-460`, `:838-875`, `:1360-1640`) in L, written top down against stubs. Files:
`DefEq.lean` (46 functions, 825 lines in `lfn` bodies), `Infer.lean` (24, 432), `Knot.lean` (7,
43; the stub specs), `KnotWF.lean` (the closure check). 1300 L lines for ~4400 Rust lines of the
infer/defeq/knot part (census phases 6–7), ~0.3 L per Rust line (the twin's arm structure is
denser than the Rust).

### Shape
* **Slots.** `infer`, `infer_io`, `defeq` are the knot's slots (memos `in`/`io`/`de`, arrays 99‥101,
  key bit = the mode's eager bit, probe → body → re-probe → put, as lane `whnf`'s `whnf`/`whnf_core`);
  their specs are `InferSlot`/`InferIOSlot`/`DefeqSlot` (`WhnfBase.lean`), unchanged.
  **`defeq_e(mode, …)` is `defeq(mode | 2, …)`**: the twin's `defeqE` at level `F + 1` is the `defeq`
  slot of `coreKnot mode.toEager` at `F + 1` on the eager memo set, and with lane `whnf`'s bank bit
  in the key nothing moves (`enterEager`/`leaveEager` have no L code).
* **The io view.** `infer_body_io` calls `infer_io` wherever the twin's io body calls `r.infer`
  (`CoreFnsA.ioView`); `infer_proj(mode, io, …)` is shared and takes the grade as a word.
* **Entry points** at the verified mode, with lane `induct`'s/`decls`' conventions:
  `infer_type_core(vis, dep, e)`, `is_def_eq_core(vis, dep, a, b)`, `ensure_sort_core(vis, dep,
  t)` (one call each to the slot at mode `0`). In a whole program they replace `IndIface.lean`'s
  `stub`s of the same names; `IndStubs.lean`'s `RelAM` statements stay the spec they must meet
  (their `stubM` becomes these functions' models when proved).
* **Stacks.** Lists are `SPN` slices (lane `whnf`). The telescopes (`infer_lams`, `infer_pis`) keep
  a second list growing in step with `fvs` while knot calls run in between: **the binder stack
  `BSTK` = array 145, top `CTL[137]`** (claimed here; outside every tier of `CoreS`, which
  `CoreS.frame` already allows). Memory map: add array 145 / `CTL[137]`.
* **Fuels.** `defeqLoopFuel` and `lamsFuel` (`2^62`) are uncounted `while` loops; `peelFuel`
  (`2^24`) is the exact counter `peel` in `defeq_peel`, `infer_lams`, `infer_pis` (ROADMAP §3 (b)).
* **Lifted binds.** Lean's `do` runs every `(← …)` of a statement before the statement, also
  under `&&`/`||`: `defeqBody`'s `isBoolTrue b`/`hasFvarFast a`, `defeqOffset`'s two `isNatZero`,
  `propIrrel`'s four readers, `defeqStuck`'s `strLitSupported`, `lazyDeltaStep`'s two unfolds. L calls
  all of them unconditionally, in the twin's order.
* **Literal equality** (`quickDefEq`'s `l₁ == l₂`) is `lit_eq`: kind, length, `limbs_eq` on the pool
  slices (not handle equality: the twin's store is not known to be duplicate-free across tiers).
* Splits for the proofs: `lazy_delta_step` = dispatcher + `lds_left`/`lds_right`/`lds_both`;
  `defeq_body` + `defeq_tail`; `defeq_stuck` + `stuck_str`/`stuck_app`; `struct_eta_cert_with` +
  `struct_eta_cert_go`; `infer_proj` + `infer_proj_at` + `proj_type_at`; `infer_spine_arg`.

### Findings (for lane `whnf`)
* `defeq_list` (`WhnfIota.lean`) returns `0` at once on a length mismatch; the twin's `defEqList`
  compares the common prefix first (`defeq` calls with effects, and possibly a throw). Not a
  refinement of `defEqList` when lengths differ (`iota_index_ok` can pass different lengths). This
  lane uses its own `defeq_lst` (the twin's recursion) and `defeq_list_rev` (`defeqSpine`).
* `proof_irrel` (`WhnfIota.lean`) calls `lvl_eq`, not the cached `lvl_eq_c`: the twin's `lvlEq?`
  writes `lvlEqC`, so `CoreRM`'s `lq` relation breaks across it. This lane calls `proof_irrel`
  (`propIrrel`'s slow arm is `proofIrrel` verbatim), so the fix is one word there.
* `reduce_proj_fire` tests `an == np + nf` on words (wraps for huge `np + nf`); `eta_ctor_shape`
  here uses `nf ≤ an ∧ an - nf = np`.
* `reserved_contains` is defined twice (`IndIface.lean`'s `reservedContains`, `WhnfIota.lean`'s
  `reservedContainsL`): a whole program must pick one.
* Master was broken at `WhnfSpineRefine.lean:769` since lane `exprops3`'s packed derived word
  (`mkAppW` posts `packBF … …`): fixed by lane `indproofs` and here at the same time (the
  `derPutW` argument), one line.

### `sorry`s
* `Knot.lean` `defeqCallees_stub`: `has_fvar`, `not_proof_fast`, `is_proof_fast` (phase 2
  `PropRead`), `abstract1`, `abstract_range` (phase 4), `field_sort_zero` (levels:
  `Level.isEquiv (Level.subst ks vs fs) .zero` on the heap). The slots' induction steps
  (`WhnfCallees.inferStep`/`inferIOStep`/`defeqStep`, lane `whnf`'s stub) are this lane's to prove
  next; nothing is proved yet.

### The slots one level up (`KnotSlot.lean`, helper `defeq-slots`)
* `infer_refines`, `inferIO_refines`, `defeq_refines`: `InferSlot`/`InferIOSlot`/`DefeqSlot p (n + 1)`
  from `KnotUpTo p n` and the body's spec at L-fuel `n` (`InferBodySpec`, `InferIOBodySpec`,
  `DefeqBodySpec`: hypotheses, the shape of `WhnfLoopSpec`). Copies of lane `whnf`'s `whnf_refines`;
  new lemmas `CoreS.set_in`/`set_io`/`set_de`, `ModeR.setD` (the `Bool` memo), `KeptAll.inf`/`io`/`de`,
  `knot_{infer,inferIO,defeq}_{hit,miss}`, the model `memoSlotD` (a hit answers `u64(v != 0)`).
* **The eager slot needs no relation change.** `DefeqESlot p (n + 1)` from `DefeqSlot p n`
  (`defeqE_refines`). From an eager mode `defeqE` is `defeq` (`knot_defeqE_eager`); from a plain
  mode it is the `defeq` slot of `coreKnot mode.toEager … (F + 1)` on the entered caches `enterC`,
  then `leaveC` (`knot_defeqE_plain`). `CoreS … M 0` on `a` is `CoreS … M 1` on `enterC a.caches` at
  the same maps (`ModeR.enter`: the stored eager tables are bank 1, the empty slot is `∅`); after the
  run, `KeptAll M M' 1` gives the plain banks back, so `CoreS … M' 0` holds on the left state
  (`ModeR.leave`, `CoreS.leave`). The outer `KeptAll` at `eb = 0` is vacuous. `SlotPre`'s
  `eb = (mode >>> 1) &&& 1` is met by the inner call at `mode ||| 2`.
* Entry points from the slots at mode 0: `inferTypeCore_refines`, `isDefEqCore_refines`,
  `ensureSortCore_refines` (the last from `EnsureSortSpec`, a hypothesis: `ensure_sort` has no proof
  yet); `call1W`/`CoreSpec.of_call1W` for one-call forwarders. Tagged `refines_part` (they rest on
  slot hypotheses until the knot induction ties them).
* What is left for `WhnfCallees.inferStep`/`inferIOStep`/`defeqStep`: the three body specs. No
  `sorry`; ~880 lines, 5.8 s CPU.

### The leaf inference functions (`InferLeaves.lean`, helper `defeq-slots`)
* `ensureSort_refines : KnotUpTo p n → EnsureSortSpec p (n + 1)` (from the `whnf` slot and
  `view_sort_f`); `ensureSortCore_refines` now takes only `KnotUpTo` (KnotSlot's old one is
  `ensureSortCore_of_spec`). `defeqArg_refines` (the two slots, `is_eager_reduce` as the
  hypothesis `IsEagerReduceH`). `inferLamResult_refines` (`Abstract1OK`; `mk_forall` under
  `CoreS`: `mkForall_core`, with `mkForallW_hw`/`_frame`, `keeps_cpl_internForall`).
* Clause fragments, copied from `inferBody` and proved equal to its arm (`inferBody_const`,
  `inferBody_lit`, `inferBodyIO_lit`): `inferLitT` (`inferLit_refines`, callees as
  `InferLitCallees`: `nat_lit_supported`/`const_e` are lane `whnf`'s `sorry`s, `str_lit_supported`
  its stub) and `inferConstT` (`inferConst_refines`, `ConstTyAtOK` a hypothesis: `const_ty_at`
  is a `sorry` in `WhnfIota.lean`). `inferBodyIO`'s `.const` arm reads `viewLsLen`, a different
  fragment, not done.
* **L change**: `infer_const` called `const_ty_at` with the looked-up name `n`; the twin's
  `constTyAt cv us` keys its cache by `cv.name`, the record's own name word (`p + 1`), and `EnvR`
  does not promise `cv.name = n`. It now passes `EREC[p + 1]`. Lane `whnf`'s `iota` call site
  (`WhnfIota.lean:733`, `const_ty_at(cj, …)`) has the same gap.
* Gap: a guarded model equation with the callee's run as a hypothesis (`callW … = some (r, m₁) →
  W … = …`) was not instantiated by `finish` in `ensure_sort`; the `memoSlotW` shape (the run as
  an argument of the model, `W (callW …)`) was. All models here use that shape.
* Merged master into `defeq-slots` (WhnfCoreApp's `mkAppW_hw` fix). No `sorry`; ~875 lines,
  5.2 s CPU.

### The inference bodies (`InferBody*.lean`, helper `defeq-infer`)
* **`InferBodySpec p n` and `InferIOBodySpec p n` are theorems** (`inferBody_refines`,
  `inferBodyIO_refines`, `InferBodyDisp.lean`), hence `inferSlot_step`/`inferIOSlot_step`
  (`WhnfCallees.inferStep`/`inferIOStep`), from `KnotUpTo p n`, the programs (`InferAllProg`) and
  `InferCallees`: `inst1`, `inst_list`, `abs_entry`, `ar_entry`, `const_ty_at`, the `infer_lit`
  callees, `is_eager_reduce`, **`infer_proj` (`InferProjOK`, not proved: the table's `structSort`
  must denote for `lvl_eq_c`'s refinement, an environment invariant nobody states yet)**, and two
  binder-stack facts below. Both specs now carry `n ≤ 2^62` (KnotSlot.lean).
* Every clause is proved: `infer_let`, `infer_lam_io`, `infer_forall_io` (`InferBodyLet`), the
  spines (`InferBodySpine`, `InferBodySpineF`: loops as named blocks, fuel models, `SpPost`), the
  telescopes (`InferBodyBind`, `InferBodyBindPi`: `lamsFull_ref`/`pisFull_ref`, `TelPost`), the
  interning leaves under `CoreS` (`InferBodyIntern`: `CoreS.of_level` for level nodes via
  `LStore.intern_ext`).
* **The binder stack is not in `CoreAfter`.** `StackKept` covers `SPN`/`CTL[136]` only, so the
  telescopes assume `BStkCallees` (`infer`, `whnf`, `inst_list`, `ar_entry`, `ensure_sort` keep
  `BSTK` below `CTL[137]` and `CTL[137]`) and `BStkCap` (`BSTK` has fewer than `2^63` words under
  `CoreS`). To discharge them: a field `bstk` in `CoreS` (as `spn`) and `BKept` in `StackKept`,
  proved by every core body (lane `whnf`'s files construct both about 15 times).
* **L changes** (Infer.lean): `infer_lam_io`/`infer_forall_io` abort at `d + 1 = 0`;
  `infer_lam`/`infer_forall` abort at `d ≥ 2^63` (depth capacities: the twin's depth is a `Nat`);
  `infer_spine`/`infer_spine_io` abort when `CTL[136]` is past the stack (so the empty accumulator
  is a slice; `head_and_args` at an `app` handle needs no such bound, `headAndArgs_app`).
* Proof style: `vcgen` + `simp_all` for the specs (`finish` blew up on `List.cons.injEq` with six
  calls), `ld64_rdW_spec`/`st64_spec` instead of unfolding `ld64`/`st64` (a read's bound proof as
  an argument blocks `simp_all`). **Kernel deep recursion**: `simp` (`↓reduceIte`) on a goal holding
  `inferLams …`/`inferPis …` at the literal `peelFuel` made the kernel unfold the structural
  recursion; `rw [if_pos rfl]` instead. ~4400 lines, ~29 s CPU.

## Phase 2, round 3: the step's specs, promotion, the pin variants (2026-10-22, lane `decls2`)

### The stale loop targets (`installStep`, `installDeclStep`, `checkPending`, `checkPendingList`)

Reviewed against the twin at `vendor/UPSTREAM` and lane `whnf`'s `CoreR`, which now carries both
sets of mode memos (`CoreRM m c M eb`, the eager tower's `eagerMemos` as bank `1`): the L code
(`Checker.lean`) is the twin's line for line, and the skeleton's proofs go through lane `whnf`'s
`flushCaches_refinesC`/`scratchEnter_refinesC`/`scratchDrop_refinesC` against the new `CoreR`
(`flush_loop`, `enter_loop`, `drop_loop` build on master). The flag came from the dropped
fingerprint census: these four reach the changed `Caches.empty` only through `flushCaches`, which
is cited and was fixed by lane `whnf` (DESIGN, "Provenance", the `update --old 4c9eaf7` test).
Nothing left to do; no marker on them.

`LoopR` now carries `IWOK` (lane `induct`'s pool bounds), so the step's callees, which run on
`StageR = CheckR ∧ IWOK`, can be called from it (`IWOK.frame`: kept by any frame that leaves `IW`,
`EREC`, `CTL[129]`, `CTL[200]` alone — the bracket's and `pend_push`'s). The two step specs moved
to `DeclStepSpec.lean`.

### The ROM's pin variants: does declining `Nat.div` decline everything?

**Yes, for every realistic input.** Without a pin variant `checkDivModPin` runs its variant loop
over `[]` and declines (`notImplemented`) at the install of *any* of the eight pin-certified
operations (`natDivModNames`: `Nat.div`, `Nat.mod`, `Nat.gcd`, `Nat.land`, `Nat.lor`, `Nat.xor`,
`Nat.shiftLeft`, `Nat.shiftRight`), not only `Nat.div`. Measured on con-leche's 498 e2e fixtures
(`_tmp/ref/con-leche/tests/e2e`, expectations from `e2e-expected.txt`; a scan of the `def`/
`opaque` records by name): of 313 accepting fixtures, **21 (6.7 %) define one of the eight** and
would become declines; every one of the fixtures that declares `String` or `Char` (`str_lit`,
`str_proj`, …) defines `Nat.div` and `Nat.mod` — a string literal's type cone reaches them on this
toolchain — and so does every whole-module export (`Init` itself, `Std`, Mathlib) and every file
using `/`, `%`, `Fin`/`UInt*` arithmetic or `toString`. What still accepts is pure-logic and
hand-built cones (the other 292 fixtures). So the L checker as it stands is complete only for
inputs that never meet these operations: a real completeness gap, still no soundness issue (the
final theorem holds at every pin list).

**What embedding one variant costs** (the repository toolchain's, con-leche's first, `pins/
leanprover-lean4-nightly-nightly-2026-09-10.json`, which also covers v4.35.0):
* Data: 16 terms, **42 036** share-table entries (8 pins 900, 8 certificate lists 41 136; the
  largest blobs 5–8k entries). The ROM encoding (`encItems [] (itemsPinSet v0)`, the memo mirrored
  by back references) is **490 465 bytes**, against **9 542** today (the walk's items without
  variants: 7 942). The three committed variants together ≈ 1.5 MB.
* Generating it: `#eval` (interpreter) of the encoder ≈ 30 s (the `seen` list is quadratic).
* **The kernel cannot check it the current way.** The ROM's correctness enters through
  `romData = … ++ encItems [] (itemsAllPins romPins)` and `decide +kernel` side conditions
  (`romData_len`, `allPins_fits`, `allPins_noProj`), i.e. the kernel evaluates the encoder on the
  variant. Measured (`decide +kernel` of `(encItems [] [.ex blob]).length < 2^63`): `Nat.land`'s
  pin (7 entries, 76 bytes) 0.26 s; `Nat.div`'s pin (277 entries, 3.6 KB) **4.2 s**; `Nat.gcd`'s
  first certificate (1061 entries, 13.6 KB) **111 s** — growth ≈ entries^2.4 (structural `Expr`
  equality on the unshared trees behind the `seen` membership tests). Extrapolated quadratically
  over the 16 blobs: ≥ 6 h of kernel time per variant; really more. Not buildable.
* Build time otherwise: none to speak of (a 490 KB literal; the x64 binary grows by the same).

**Recommendation: a decoder-side ROM loader, so the kernel never evaluates the variant.** The pin
list is free in the final theorem, so the L checker need not prove *which* variant its ROM holds,
only that it interns *some* list `P` the way `internAllPins P` does:
1. A total decoder `decRom : List UInt8 → List NatOpPinSet` (fuel-bounded, garbage decodes to
   anything), and the ROM readers' specs restated over it: "if `rom_items` returns, the twin's
   `internAllPins (decRom bytes)` ran to the related state". Proved once by induction, for all
   bytes; no evaluation of the data. `P := decRom romBytes` is then simply the program's pin list.
2. The memo: without the encoder's canonical back references, L may re-intern a subterm the
   twin's `EMemo` hits; the handles agree by hash-consing, so the one new lemma is the one lane
   `decls` avoided — "re-interning a denoted tree returns its handle and changes nothing" (store
   `consP`/`consS`), and `MemoR` relaxed to tolerate duplicate keys.
3. The bytes: generated by an untrusted `#eval` script into a committed file, embedded with
   `include_str`; the kernel only checks the length bound (`String.length` of the literal, linear).
4. Cost estimate: the decoder and the restated reader specs ~1–1.5k proof lines (the five reader
   files are 3.5k lines today; their arm lemmas carry over, the induction changes from "on `x`
   with `enc x`" to "on the fuel with `dec`"), the re-intern lemma ~300 lines. Not cheap, so
   **not implemented this round**; it is the one piece of work between the L checker and
   accepting ordinary Lean files. The pin-variant check itself (`checkDivModPin`, the certificate
   loop) is lane `decls2`'s translation work either way.

### `check_value_group` refines `checkValueGroup` (`DeclCvg.lean`, `DeclStepSpec.lean`)

**`checkValueGroup_spec` is proved** (`@[refines ConRon.Arena.checkValueGroup]`), through the
stubs of the core and the walks (`infer_type_core`, `ensure_sort_core`, `is_def_eq_core`,
`loose_bvars_bounded_fast`, `has_fvar_fast`, `all_level_params_defined`, `consts_resolve_ffast`)
and one stage spec of a master function (`lvl_eq_c`, below). On lane `indproofs`' template: word
models (`cvgW`, `ivgW`, `cvLpsW`, `pinWordW`, `iwResetW`; continuations with `rfl` arm lemmas),
`vcgen` specs with callee *models* only (each one `finish (gen := 20)`, < 1 s), relational lemmas
(`ivgW_ok`: `install_value_guards` refines `installValueGuards`; `cvgW_ok`), the spec assembled
with `M.of_run` from two triples of the same run.

* **The loop's relation through stubs: frames from the text.** `LoopR` = the stage relation
  (`StageR = CheckR ∧ IWOK`, now a field `iw`) + `PendR` + the front's `DeclsR`. A stub's post
  (`KeepPost`) says nothing about `PEND`/`DECL`/`DLP`/`CTL[130]`, so these come from the program
  text: `cvgProg` (this lane's functions, lane `induct`'s library and stubs, the real `pin_word`,
  lane `whnf`'s `lvl_eq_c` + lane `levels`' `lvl_eq` and its 17 helpers), `cvgFns` (its 37
  reached functions), `cvgProg_closed : closedA cvgProg stepA stepC cvgFns` (`decide +kernel`,
  0.8 s; `stepA` = every array but 137/67/68, `stepC` = every `CTL` word below 1024 but 130).
  `CvgProg p` (lookups agree on `cvgFns`) is a field of the skeleton's `DeclCallees`.
  `LoopR.of_step`: the stage relation after, a frame of `(stepA, stepC)`, the records only
  extended (`IWGrow.erecPExt`) ⇒ `LoopR` after. The same shape serves `install_step_go`.
* `check_value_group` now calls lane `whnf`'s **cached** `lvl_eq_c` (the twin's `lvlEq?` reads and
  fills `lvlEqC`); lane `induct`'s `lvl_eq_fueled`/`lvl_eq_true` call the uncached `lvl_eq`, so
  under an exact `CoreR` their L runs leave `lvlEqC` behind the twin's (and pay the algorithm on
  every repeat). **Request to lane `induct`/`indproofs`**: call `lvl_eq_c`; their
  `lvlEqStub_spec` ("`lvl_eq` refines `lvlEq?`") is not true of the real `lvl_eq`.
* The skeleton threads `mode = .verified` (L implements that mode only; the final theorem uses
  it).
* Numbers: `DeclCvg.lean` 730 lines (models + specs ≈ 330, relational ≈ 400), 7.1 s user;
  `DeclStepSpec.lean` 0.6 s. For 30 L lines (`check_value_group`, `install_value_guards`): ≈ 25
  proof lines per L line, two thirds in the relational lemmas (case splits on the model's
  continuations, the twin's `do` blocks unfolded by `simp only [StateT.run_bind, hrun…,
  exc_ok_bind']`). Finding: an `if c then do …` without `else` in the twin duplicates the
  continuation into both branches after `simp`; state the continuation once as a hypothesis
  (`tail`) and close both branches with it.

### `checkDecl`'s one-constant arms in L (`DeclArms*.lean`, helper `decls2-arms`)

`check_decl` dispatches on the record's kind: `1`–`5` to `check_decl_axiom/defn/thm/opaque/quot(i,
vis)` (kind `6` to lane `induct`'s `check_ind_decl` as before; the stub `check_decl_const` is gone).
Translated in full, 109 L functions, 90 tagged `@[l_impl]` (no proofs yet):
* `DeclArmsCanon.lean` (471 lines, 283 L): `Canon.lean` (`canonNames*`, `canonNameMap`,
  `canonLevel(s|List)Eq`, `canonExprEq`, `IConstantVal`/`IConstantInfo.canonEq`, `canonRulesEq`,
  `canonEqList`), `toConstantVal`, `ci_eq` (the twin's derived record equality).
* `DeclArmsNat.lean` (1114, 721): the structural-`Nat` gate (`natOpGuard`, `natOpDeps`,
  `natOpStoredOkAll`, `natOpEquations`, `substConst0Pairs`, `certifyNatEqs`) and the whole
  `Nat.div`-family pin gate (`checkDivModPin`, its variant loop, the eleven `divModCertStmts`).
* `DeclArms.lean` (607, 363): `checkConstantVal` (real, replacing lane `induct`'s stub of that name
  in `declStepProg` via `indProgArms`), `checkDefnVal`/`ThmVal`/`OpaqueVal`, `stdAxiomOk`,
  `trustCompilerOk`, `ofReduceAxOk`, `checkReducePin`, `checkBasisDecl`, `quotPinHit`, the arms.
* ROM values are stubs (`romStubs`), conventions: `rom_basis_decls(kind)`/`rom_basis_decls_a(kind)`
  → an `IW` slice of `EREC` constant records (kind 0 `eqK`, 1 `natK`, 2 `emptyK`, 3 `falseK`, 4
  `quotK`); `rom_ci(id)` → an `EREC` record (0 `eqA`, 1 `natA`, 2‥4 `iff*A`, 5‥7 `nonempty*A`);
  `rom_cv(id)` → an `EREC` constant value (0 `propextA`, 1 `choiceA`, 2 `trueCvA`, 3
  `trueIntroCvA`, 4 `trustCompilerA`, 5 `boolCvA`, 6/7 `reduce{Nat,Bool}CvA`, 8/9
  `ofReduce{Nat,Bool}A`); `rom_expr(id)` (0/1 `reduce{Nat,Bool}DeclPin`); `rom_pin_sets()` → the
  variant records (24 words: 8 pins, 8 proof slices; empty today). Master functions lane
  `induct`'s program lacks are stubs too (`intern_succ`, `intern_nnum`, `const_e`,
  `nat_lit_supported`). Next for the ROM: build these records from ROM items (the interned
  *values* `RomCI.lean` does not build yet).
* Completeness: an error inside one pin variant's attempt aborts (the twin's `orElseAttempt`
  restores and tries the next); nothing today (no variants). Finding: `canonExprEq` compares
  literals by handle, which needs each literal interned once (the stores' hash-consing).
* `DeclArms.lean` takes 79 s user (`lake env lean`; the `#guard` runs and the closure check),
  the others 8.4 s and 3.7 s.

### `install_step_go` refines `installStepGo` (`DeclStepGo.lean`, `DeclHeader.lean`, `DeclRec.lean`)

**`installStepGo_spec` is proved** (`@[refines ConRon.Arena.installStepGo]`) through one new
`sorry`, `checkDecl_loop` (`check_decl` at the loop's relation: its arms are this lane's
`DeclArms*` and lane `induct`'s code, unproved), and the stubs.
* L change: the three value arms are one function `install_value(i, vis, ck, vk)` (constant
  record kind, value-group kind), so its call closure is the arm's alone and its write set comes
  from the text (`ivProg`, `ivFns`: 25 functions, `ivProg_closed` by `decide +kernel`); `pin_in`
  now aborts on an empty pin table (the twin's pin reads raise `.internal` there; before, L went on
  with `0`s — a refinement gap the proof found).
* `install_step_go`'s model calls `check_decl` and `install_value` through `callW` (lane `whnf`'s
  pattern: the callee's run as a function of the memory), so their *run-level* specs at `LoopR`
  (frames included) apply to the model's runs (`triple_of_callW`); its `vcgen` spec is one
  `finish`. The relational lemma `istgW_ok` is one case per record kind (`DeclAt` fixes the kind
  word); the pinned-name tests are `pin_in` against the twin's `natOpNames ++ natDivModNames` /
  `reduceOpNames` (`natOpNames_run` …: the twin's lists are `PINS[15‥29]`/`PINS[44‥45]`,
  `contains_pins`: `contains` is word equality on handle words).
* `install_value`: `ivW` (model; `env_push` also through `callW`, because its spec needs the name
  word's bound, which only the relational lemma has), `ivW_gen`/`ivW_ok` against the arm's twin
  `ivT` (the header, the guards but for a theorem, the push, the group), `installValue_loop`
  (model + text frame + `LoopR.of_step`).
* Helpers: `decls2-header` (`DeclHeader.lean`: `install_header` refines `installHeader`,
  `@[refines]`, models of `env_find`/`reserved_contains`; 508 lines, 5.8 s) and `decls2-rec`
  (`DeclRec.lean`: `erec_ci`, `erec_vg`, `env_push` models, specs and `_ok` lemmas, no `sorry`;
  672 lines, 9.1 s). `DeclStepGo.lean` 893 lines, 6.3 s.
* For ≈ 120 L lines (`install_step_go`, `install_value`, `install_header`, `erec_ci`, `erec_vg`,
  `dlp_copy`, `pin_in`, `env_push`'s model): ≈ 2.1k proof lines, ≈ 17 per L line. Every `vcgen`
  spec is one `finish (gen := 20)` and passed at the first or second attempt; the work is in the
  relational lemmas (case splits, `ArrExt`/`IWGrow` bookkeeping across the record pool).
* The relation behind it all is `StageR` at the callee and `LoopR.of_step` around it: the step's
  callees never see `PEND`/`DECL`/`DLP`, the text says they do not write them.


### Promotion in L (`Promote*.lean`, helper `decls2-promote`)

`promoteVG_spec` is **proved**; `promoteN`, `promoteL`, `promoteLs`, `promoteE`, `promoteVG` are
`@[refines]` with no `sorry` (axioms `propext`, `Classical.choice`, `Quot.sound`). All promotion
L code is in `Promote.lean` (374 L lines, incl. `promote_ci` and its arms, `erase_installed`,
`index_promoted`, `promote_new`, with `#guard` runs in `PromoteTest.lean`); ≈ 6.0k proof lines in
16 files.
* **`internPersistent` as a flag bracket**: `pi_X` saves `CTL[1]`, clears it, calls the ordinary
  `intern_*`/`mk_*`, restores it. `ArenaR` reads `CTL[1]` only in each table's flag clause, so the
  transient state is related; twin side, `internPersistentX v = internX v` at cleared flags (the
  four stores' flags agree, the children persistent). One interner per kind, no copies.
* The four `PMemo` maps are memos on arrays 146‥149 (`PNM`, `PLM`, `PLSM`, `PEM`), `CTL` 140‥147,
  epoch-cleared per declaration; `PMemoR` is the real relation, and `LoopR` carries
  `pmemo : ∃ pm, PMemoR m pm`. `stepA`/`stepC` exclude them (the step's texts still check).
* Records are written after their parts (`promote_vg`, `promote_cv`), so later writes sit above
  every part and the decodings survive (`ErecGrow`/`ArrExt`). `pci_defn`/`pci_ind`/`pci_rec` still
  allocate first: restructure before proving `promote_ci`.
* Findings: a word loaded inside a call argument (`call f(A.u64[i])`) makes `finish` fail; load it
  into a local first. `decide` times out on membership in long write-set lists; `simp` with the
  ids unfolded works. L copies an inductive's `sortZ` name handles (as the twin does) instead of
  promoting them: whether they still decode after the drop is the consumers' question.
* `PromoteProg.lean` 17 s user (lookups over 140 entries), the rest ≤ 8 s.

Census at landing 4: phase 2 **136 proven, 11 sorry, 93 written, 91 todo**; proven Rust lines
745 of 6512 (was 370 at the lane's start); totals 526 proven of 1352.

### `sorry`s (lane `decls2`)

* `DeclCvg.lean` `lvlEqCStage_spec`: `lvl_eq_c` under `StageR`. Lane `whnf`'s `lvlEqC_refines`
  proves it under `CoreS`, whose readback-cache invariants and `NStoreWF` `StageR` lacks (the same
  gap as lane `indproofs`' `lvlEqStub_spec`); closes when `StageR` carries `CoreS`'s extras.
* `DeclStepGo.lean` `checkDecl_loop`: `check_decl` at the loop's relation (the arms' proofs;
  for kind `6` also the front's `DeclAt` for inductive records and lane `induct`'s
  `check_ind_decl`).
* `Checker.lean` `promoteNew_spec`: `promote_new` (L code written; `promote_ci`'s arms, the erase
  and re-index loops need specs).

Census (`--no-build`, this lane before landing 2, against master's last `docs/progress.md`): phase 2
**130 proven, 8 sorry, 82 written, 111 todo** (was 130 / 5 / 5 / 191); Rust lines with L code
4341 of 6512 (was 1001).

## Slow declarations (2026-10-22, lane `perf1`)

The build-statistics watch list (`docs/buildstats.md`) names every step over 20 s; this lane takes
the ones no other lane owns. Times are single-threaded `lake env lean` runs on an idle core unless
said otherwise.

### `Prog.wf` by `decide +kernel`: string comparisons (`ConAgua/Compiler/WFFast.lean`)

- **Cause.** `Prog.wf` looks every call target up by `p.lookup f` and checks
  `decide (p.map (·.1)).Nodup`, both on `String`s. In the kernel a `String` comparison unfolds
  `String.decEq` down to the UTF-8 byte lists of both literals, and `Nodup`'s `Decidable` instance
  is itself costly (even `(List.range 477).Nodup` takes 9.5 s). `declStepProg` has 477 functions and
  1305 calls: `Nodup` 28 s plus the lookups 27 s; `indProg` the same minus 14 functions. Both grow
  quadratically with the program.
- **Fix.** `Prog.wfFast`: each name becomes a `Nat` once (`nameCode`, bijective base-257 over the
  UTF-8 bytes, injective), the names go into a binary search tree keyed by that code (`progTree`;
  `NTree.insert` fails on a duplicate, which gives `Nodup`), and `Stmt.wfT` looks targets up in
  the tree. Key comparisons are `Nat.decLt`/`Nat.decEq`, which the kernel does on literals with
  GMP. `Prog.wf_of_wfFast : wfFast tab p = true → wf tab p = true` (no ordering invariant needed:
  `find` follows the same path as `insert`). Every `_wf` theorem keeps its statement and becomes
  `Prog.wf_of_wfFast (by decide +kernel)`: `indProg_wf`, `declStepProg_wf`, `frontAllProg_wf`,
  the per-module `indParts_wf` … `recCheck_wf`, `libFns_wf`, `indApply_wf`, `indFields_wf`.
- **Before/after.** `declStepProg_wf` 54.1 s → 4.3 s (module 55 s → 4.4 s), `indProg_wf` 53.8 s →
  ~4 s (module 54 s → 4.2 s), `indPos2_wf` 11 s, `recCheck_wf` 9.7 s, `frontAllProg_wf` 8.7 s, the
  other per-module checks 5–8 s: each module now builds in under 2 s (Capstone 6.8 s in all).
  Of the remaining 4.3 s, about half is `progTree` (mostly the UTF-8 expansion of the literals).
- Not done: `KnotWF.defeqInferFns_wf` (4.5 s) states `FunDecl.wf`/`Nodup` directly rather than
  `Prog.wf`; `closedA` (write sets) also looks names up by string and could use the same tree.

### `natShr_spec` (`ConAgua/Arena/NatShr.lean:241`): a loose multi-pattern

- **Cause.** Of the 168 goals vcgen leaves, one (`lb = 1`, `w < la`: the quotient) took 52 s and
  one (`lb = 0`, the same) 5 s; the other 166 together 20 s. Grind diagnostics on the slow goal:
  600 instances of `shr_val`, 626 of `pv_succ`, 842 case splits. `shr_val`'s pattern
  `pv P oa la / (S * wt w), pv P o l, R * S` binds `o`, `l`, `R` by any `pv P _ _` and any product,
  and every instance adds case splits on its hypotheses.
- **Fix.** `shr_small`, the quotient in the shape the loop's post (`ShrPost`) and the amount give:
  `pv P oa la / 2 ^ pv Q ob lb = pv R t r` from `pv Q ob lb = k.toNat`, the skip `w = k >> 6 < la`
  and `pv R t r * sh s + lowb (lv P o l 0) s = pv P o l` (`s = k &&& 63`). Its pattern
  `pv P oa la / 2 ^ pv Q ob lb, pv R t r * sh (k &&& 63).toNat, lowb (lv P o l 0) (k &&& 63).toNat`
  binds every variable by a term of the post, so it fires about once; `shr_val` is now only its
  proof step (no pattern). No statement changed.
- **Before/after.** `natShr_spec` 60.9 s → no profiler step over 1 s; the slow goal 52 s → < 2 s;
  module 111 s → 25 s (Lake, contended); grind in the whole file 7.9 s.

Census at landing 3 (`--no-build`): phase 2 **130 proven, 11 sorry, 79 written** (`installStepGo`,
`installHeader`, `installValueGuards`, `checkValueGroup` now `sorry` — through stubs only); bad
links 0 (`@[l_impl]` moved off the ROM readers, which are functions of the ROM, onto
`romExprL`/`internAllPinsL` at the program's ROM).

### `decE` (`ConAgua/Scan/Utf8Link.lean:239`): `simp` under a `dite` with proof-carrying branches

- **Cause.** `assemble₄` is `if h₁ : r < 0x10000 then none else if h₂ : 0x10ffff < r then none else
  some ⟨r, proof(h₁, h₂)⟩`. `simp only [UInt32.lt_iff_toNat_lt, hv, UInt32.reduceToNat]` rewrote both
  conditions under the binders, so the `Char.valid` proof became `Eq.mpr_not (… hv …) h` casts; any
  leaf proof that then rewrote with `hr`/`hs` made the kernel spend 6 s (uncontended; 21.9 s in the
  contended build) checking them. Each of the three leaves alone costs the full 6 s; with all three
  `sorry`ed, nothing. `decD` (same shape, smaller numbers) is cheap.
- **Fix.** Leave the `dite`s alone: two `iff`s (`e1`, `e2`: the `UInt32` condition iff its `Nat`
  form, by `UInt32.lt_iff_toNat_lt` and `v4L`), case on the `Nat` form and step through the `dite`s
  with `dite_eq_left`/`dite_eq_right`. Same statement.
- **Before/after.** `decE` 6 s → under 0.1 s; module 38 s (contended) → 2.3 s.

### `keyAtG2_spec` (`ConAgua/Scan/Key.lean:678`): short-circuit chains multiply the paths (`L/PureEval.lean`)

- **Cause.** `step` evaluates `if c then S else T` by `evalC c`, and `evalC (.and p q)` is
  `if (← evalC p) then evalC q else return false`: `vcgen` follows `T` once per exit of the chain.
  `keyAtG2`'s `kl == 9` arm is four 8-byte `&&` chains in a row (`if A₁ {return}; …; return 0`), so
  the last tail is reached on ~9⁴ paths. `vcgen` took 26 s uncontended (47.6 s in the build).
- **Fix.** `L/PureEval.lean`: `Expr.pval`/`Cond.pval`, the value of an expression/condition in a
  state with reads past the end as `0`, and `evalE_spec`/`evalC_spec`
  (`⦃s = s₀⦄ evalC c ⦃b s' => s' = s₀ ∧ b = Cond.pval s₀ c; ⊤⦄`, by induction; a throwing run meets
  `⊤`). With them in `vcgen`'s list instead of `evalE`/`evalC`, each `if` is one split. The VCs then
  hold `Cond.pval` of concrete conditions; `finish` unfolds them one E-matching generation per level
  and fails even at `gen := 32`, so the proof is `vcgen`; `simp only [Cond.pval, Expr.pval, …] at *`;
  `grind (splits := 40)` (recipe in the module doc). Same statement.
- **Before/after.** File prefix through `keyAtG2_spec`, uncontended: 54 s → 15 s; `keyAtG2_spec`'s
  `vcgen` 26 s → 1.4 s, largest `grind` 7.8 s; module 100 s (contended) → 17 s (Lake).
- The same cause is behind `Scan.Line` (`lineLoop_spec`, `||` chains over the key code).

### `Scan.Line` (117 s): not fixed, diagnosis

- Nearly all of it is `lineLoop_spec` (108 s uncontended): `vcgen` takes 1 s and leaves 89 goals;
  `finish` on them takes the rest (~1.2 s each, part of it shown as `sym`'s own time). With the
  `finish`es replaced by `sorry` the theorem takes under 2 s.
- `L.evalC_spec` does not help here: the `||` chains over the key code `k` become disjunctive
  hypotheses, and `finish` then needs more case splits than the separate paths cost (85 s with 5
  goals failing at the default split limit; 139 s with `splits := 24`, one goal 55 s). With
  `[grind norm]` on the `pval` equations `finish` sees the unfolded conditions, so the remaining
  cost is the splitting itself.
- What should work: the PLAN recipe, one named block per arm group of the dispatch (the six
  `else if k == …` groups), each with its own spec, so that each goal sees one arm's callee posts
  instead of all of them. That changes the L code's shape (not its behaviour), so it is left to the
  owner of `Scan/Line.lean`.

### `Scan/Records.lean` split (2270 lines)

Pure move, as in `Front/FieldsDecl*`: `Records.lean` keeps the L code and the models (1357
lines), `RecordsSpec.lean` the `specs` section (941 lines, same namespace, names and statements;
it repeats the local `attribute [local lang_grind] boolEndN`). `Scan/Line.lean` and the root
import `RecordsSpec`.

### Landing 2 (lane `defeq`)
* Merged helpers `defeq-slots` (KnotSlot, InferLeaves). The phase-4 callees landed by lane
  `exprops4` replace three stub names: `abstract1` → `abs_entry`, `abstract_range` → `ar_entry`;
  `has_fvar`, `inst_list` already had the right names. `DefeqCallees` keeps their `CoreS`-at-
  `coreWalkFuel` form as an assumption (the refinements are under `ArenaA` at every `F ≥ n`): the
  bridge (L fuel `≤ coreWalkFuel`, `AbsR` across `scratch_enter`, `ArenaA` from `CoreS`) is next.
* `infer_const` passes the record's own name `EREC[p + 1]` to `const_ty_at` (the twin keys
  `constTyC` by `cv.name`; `EnvR` does not promise `cv.name = n`). Lane `whnf`: the same gap at
  `WhnfIota.lean`'s `const_ty_at(cj, …)` call.

### Landing 3: the defeq leaves (`DefEqLeaves.lean`, `DefEqLeaves2.lean`, helper `defeq-leaves`)
* `@[refines]`, no `sorry`: `is_bool_true`, `head_is_proj`, `io_neutral`, `is_eager_reduce`,
  `is_nat_zero`, `head_hint` (`decHintR`), `unfoldable_head`, `same_const_heads`, `nat_pred`
  (`decOptR`; the `nat_pred_lit` arm interns: `CoreK` = `CoreS` + stack kept, `internLit_core`);
  `hint_lt` = `hintLtW`, equal to `ReducibilityHint.lt` of the decoded hints; `refines_part`:
  `er_slice_eq` (`decide (l1 = l2)` on decoded `EREC` slices), `lit_eq` (`l₁ == l₂`).
* ~1940 proof lines for ~180 L lines (10.5 per L line). CPU: `DefEqLeaves` 150 s (`same_const_heads`
  alone ~2 min: several node reads in one function slow `grind`; four specs raise
  `maxHeartbeats`, commented), `DefEqLeaves2` 17 s. Own grind attribute `defeq_grind`
  (`DefEqGrindAttr.lean`).
* Copies of `WhnfCoreApp.lean`'s `cpl`/`keeps_cpl_internNodeE`/`CoreS.arena_frame` live in
  `DefEqLeaves2` (`cplL`, …) from when that file did not build; replace by an import.
* Lesson: a word model reads memory after a callee returns, where the L code reads it (`callW_spec`
  says nothing about memory kept), else `finish` fails.

## Phase 8 proofs, round 3 (2026-10-22, lane `indproofs2`)

Continues lane `indproofs` (above): the shared pieces its "Next" list named, the two helper-introduced
`sorry`s, then the parents, with three helpers (`front`: the frontend's inductive lines and their
hook; `rec`: `RecClass`/`RecGen`/`RecCheck`; `pos`: `IndPos`/`IndPos2`).

### Landing 1
* **The stubs' write set** (`IndStubs.lean`, `stubM_memoFrame`): every stub (and the two master
  callees still stubbed, `lvl_eq`, `intern_nanon`) leaves the stage's per-call memos (arrays
  201‥208, `CTL[202‥219]`) alone and keeps every array's size. One stub-contract statement
  (`sorry` like `stubM_spec`, for the owning lanes) instead of helper `memo`'s per-use
  `stubHbFrame`, which is now a corollary; with it a memo relation (`maMR`, `hbMR`, …) is carried
  across any stub call, so a parent can discharge its callees' memo well-formedness (helper `pos`'s
  request; memo relations relate memory to a twin map that is not in `AState`, so they cannot live
  in `StageR`).
* **`bvar_b` is real** (`IndSumSpec5.lean`, `bvbW_stage`): lane `exprops4`'s `bvarBL` under the stage
  relation (its model `bvbW` refines `bvarB` at every twin fuel `F + 1 ≥ n`, writes only `BMEMO`
  and `CTL[24]`, `CTL[25]`, keeps the twin's store, caches and pins). The `hb` walks' model calls
  `bvbW`, their specs take `BvbProg p`; `bvar_b` moved from `stubFns` to `masterFns`. Helper
  `memo`'s `bvarBCwf_spec` (`sorry`) is gone. Census: **`hasLooseBVarBGo`, `hasLooseBVarBFast`
  proven** (were `sorry`). `stubHbFrame` remains for `strip_pis` (a stub). `IndStubs`' `bvarB_spec`
  (`RelAM` for the stub) still serves `RecGenSpec2`/`RecCheckSpec2`, to be switched.
* **The generic decoder-stability lemma** (`IndDecStab.lean`): `OMono f` (a reader is monotone under
  pool extension; one line per decoder from the combinators `OMono.bind`/`mapM`/`decAt`/`decPL`
  and the readers, by a `repeat' (first | apply … )` over the do-block), `truncM m` (both pools cut
  at their tops), `DecB f m x := f (truncM m) = some x`, and `DecB.stab : ∀ m', IWGrow m m' →
  f m' = some x` — exactly lane `indproofs`' `hstab` hypotheses — plus `DecB.grow`, `DecB.get`.
  `DecB` facts come from bounds: `decHL_decB`, `decNL_decB`, `decRL_decB` (every stub slice post),
  `iwN/iwH/iwB_truncM` for record words below the top. Every decoder of `IndIface.lean` has its
  `_mono`; the per-decoder `_grow` lemmas are instances (`decHL_grow'`).
* **Tried and dropped: the core's invariants inside `StageR`.** A real core callee (`lvl_eq_c`,
  later `whnf`, `is_def_eq_core`) runs under `CoreS`, which adds to `CheckR` the full pins, the
  readback caches holding readbacks (`ReadLCOK`, `ReadLsCOK`), `NStoreWF` and two capacities. A
  `StageX` conjunct in `StageR` was carried through the stage cheaply (level interns: `LsExt` by
  `EStore.internLevel_ext`; expression interns keep `lss`; IW/EREC writers by frame; 13 call sites
  patched), but the declaration loop's relation `LoopR` (lane `decls2`'s `DeclBase.lean`) must then
  carry it too, and `enterScratch` (`Checker.lean`'s `enter_loop`) keeps `ReadLCOK` only if the
  level stores are well formed (`LsWF`: a cached scratch handle survives `enableScratch` only when
  the scratch tier was empty) — not provable from `CheckR`. So `StageX` needs `LsWF` (and its
  preservation by every intern, con-ron's `*_wf` lemmas) in both `StageR` and `LoopR`: a joint
  step with lanes `decls2`/`whnf`, not done; `lvl_eq` and `lvl_eq_c` stay stubs (lane `decls2`'s
  `lvlEqCStage_spec` has the same gap). The patch is kept out of the tree (no dead code).
* Census (`--no-build --list`, this branch on master `1ffa2b1`): phase 8 **60 proven, 36 sorry,
  119 written, 8 todo** (lane start 58 / 38 / 119 / 8).

### Landing 4: the inference bodies (helper `defeq-infer`); a request to lane `whnf`
* `inferBody_refines`, `inferBodyIO_refines`: `InferBodySpec p n`/`InferIOBodySpec p n` are
  theorems from `KnotUpTo p n` and `InferCallees` (callee hypotheses); with `KnotSlot.lean` they give
  the slot steps `inferSlot_step`/`inferIOSlot_step`. Files `InferBody{Intern,Let,Spine,SpineF,Bind,
  BindPi,Disp}.lean` (~4.4k lines, 28 s CPU in all). Left in `InferCallees`: the stubs (`Inst1OK`,
  `InstListOK`, `Abstract1OK`, `AbstractRangeOK`, `ConstTyAtOK`, `InferLitCallees`), `IsEagerReduceH`
  (now proved in `DefEqLeaves`: to be plugged in), **`InferProjOK`** (`lvl_eq_c` on the table's
  `structSort` needs a readback of it: an `EnvR` invariant "every level a stored table names has a
  `denoteL`" is missing), and **`BStkCallees`/`BStkCap`**.
* **Request to lane `whnf` (owner of `CoreS`/`StackKept`):** the binder stack (array 145, top
  `CTL[137]`) must be (1) bounded in `CoreS` (a field `bstk : (m.arr64 145).size < 2 ^ 63`, like
  `spn`) and (2) kept by every core run (`StackKept` gains "`CTL[137]` and `BSTK` below it unchanged").
  Every core function already keeps it (only `infer_lams`/`infer_pis` write it, and restore the
  top); the change touches ~15 constructions of `CoreS`/`StackKept` in the whnf files. Until then
  the two facts are hypotheses here.
* L changes: depth-capacity aborts (`d + 1 == 0` in the io binder clauses, `d ≥ 2^63` in
  `infer_lam`/`infer_forall`: the word depth must not wrap where the twin's `Nat` does not); the
  spines abort when `CTL[136]` is past `SPN`'s end.
## The pin data as an input (2026-10-22, lane `romload`)

**Decision (user, via the coordinator):** the `Nat`-operation pin variants (con-leche's
`NatOpPinSet`s) are **an input of the checker, like the export file**: the harness loads a
pin-data buffer into byte array `1` (`PB`), L decodes it at run time, and the final theorem holds
at whatever pin list the bytes decode to; bytes that do not decode make `check` abort (decline).
This replaces lane `decls2`'s "decoder-side ROM loader" and avoids its kernel evaluation of the
data (≥ 6 h per variant): the kernel never sees the pin data at all, and the program `p` does not
depend on it.

### Does it compose with the final theorem? (checked)

* `TwinAccepts [b]` already quantifies the pin list (`∃ pins …, internAllPins pins sD = .ok …`),
  and con-leche's soundness holds at every list: `Model.checkDeclsPure_sound_of` needs only
  `μ.isVerified = true` (`vendor/con-leche/ConLeche/Model/Fold.lean:221`); the model never reads a
  pin or a proof blob, the certificate *statements* are hand-pinned in con-leche's checker and
  shared by every variant (`NatOpPinSet.lean`'s module doc). `twinAccepts_model`/`no_False` take
  the pins from `TwinAccepts` and pass them through unchanged.
* **Shape change** (`ConAgua/Final/Statement.lean`): `loadMem b pb s8 s64` puts `pb` in byte array
  `1`; `PipelineRefines p` quantifies `∀ pb` (with `pb.size < 2^63`), and the three theorems take
  `pb` and `hpb`. Nothing else changes: `TwinAccepts [b]` is about the input only. The obligation
  for the pipeline proof is that `check`'s pin stage, run on `pb`, refines `internAllPins P` for
  the list `P` it decoded (`∃ P` in the stage's post).
* **What else assumes "the real pins"? Nothing in the theorem.** Places that mention a pin list:
  (1) the e2e reference `e2e-ref` runs the twin "at the program's pin list" (`romPins = []` so far):
  it must run at the list the buffer decodes to, i.e. `natOpPinSets.take 1` for the generated
  buffer (lane `e2e`); (2) ROADMAP §3 (c)'s single-toolchain decision: a buffer may hold several
  variants; L's "no recovery" (abort where the twin's `orElseAttempt` would try the next variant)
  stays a completeness loss only; (3) **the prelude is not free in `TwinAccepts`**:
  `builtinPreludeE` is the twin's fixed function on the twin's fixed prelude bytes, so L's prelude
  bytes must equal them (a proof obligation of lane `prelude`, not a soundness question; making
  the prelude an input too would need `TwinAccepts` to quantify the prelude bytes; con-leche's
  side, `stages_frame`, already holds at any `preC`). Not a soundness subtlety: a pin list only
  enables a `Nat` operation's literal fast path after the stored definition is defeq to the
  variant's pin and the variant's certificates check against con-leche's own statements.
* Trusted base: unchanged in kind. The loader now also loads the pin-data file into byte array
  `1` (`hmem`'s layout); its contents are untrusted (any `pb`), and so is the generator.

### The buffer (`ConAgua/Rom/PinStream.lean`, `ConAgua/Rom/Gen.lean`)

`pinBuffer pins = romData ++ encPinSets pins`: the startup data the twin interns *exactly*
(`romData`, `Prelude.lean`: pin names, basis blocks, axiom shapes; 9 542 bytes), then the variant
count and per variant the eight pins (`encExprM []` each: fresh memo, as `internExpr`) and the eight
certificate lists (length, then the expressions at one memo, as `internExprList`).
`lake exe romgen OUT` writes it for `natOpPinSets.take 1` (con-leche's repository-toolchain variant):
**500 540 bytes** (490 998 of pin data), **1.1 s** natively. Expression literals: tag `3` is now a
`natVal` below `2^64` (the pins use `0`, `1`, `2`); a string literal is tag `11` (no reader).

Why the startup data is in the buffer too: one reader family. `check` first compares
`PB[0 ‥ |romData|)` with its own copy (`romData`, the program's constant data) and aborts on a
difference; after that every reader reads `PB`. The readers' proofs stay the ROM proofs: a
**substitution lemma** (a program that never stores to byte array `PB` runs exactly as the program
with every `ld8 PB i` replaced by `ldc bs i`, `bs` the buffer) turns the real program into one whose
readers are literally `romName bs`, `romExpr bs`, … (`rom := bs`). The startup part keeps its
encoder-direction proofs (`bs = romData ++ rest` by the prefix check); the pin part needs the
decoder direction: "the reader returned ⇒ the bytes are `encExprM seen e ++ rest` for some `e`",
then the existing specs apply. Two run-time checks make that true for every byte string:
* names: every string byte below `128` (ASCII, so the bytes are some `String`'s UTF-8);
* canonical back references: the encoder writes a compound subterm out only when the twin's memo
  misses; on arbitrary bytes L would re-intern a subterm the twin's memo hits. L keeps the handles
  of the current memo in a hash set (`RSET`, the memo library's schema) and aborts when an
  explicitly encoded compound node's handle is already in it; con-ron's `denoteE_inj` turns that
  into "the twin's memo misses". (A linear scan of `RMEMO` instead would cost ≈ 1.3·10^8 steps per
  run on this buffer: Σ n²/2 over the memo calls.)

Memory map additions: byte array `1` = `PB`; word array `150` = `RSET` (`CTL[148]`, `CTL[149]`
its stamp and count); `CTL[150]`, `CTL[151]` the variant list (`EREC` offset, count).

For lane `e2e`: the harness loads the pin-data file into byte array `1` (`_tmp/romload/pins.bin`,
from `lake exe romgen`), and the program has `nb = 2`.

### Landing 2 (lane `indproofs2`)
* **`IndSim.lean`: composing relational lemmas.** `Sim mo op a Q` (the model's result `mo` is
  simulated by the twin run `op` from `a`, `Q` after); `Sim.bindK` composes one callee with the
  twin's `>>=` through the template's continuation defs (`K none = none`, `K (some (r, m₁)) = body`,
  both `rfl`), `Sim.bind_twin` a twin-only step (a pin read), `Sim.run` gives the census form
  (`AM.ok`, the post at `AM.res`/`AM.st`). Plus the blocks every wrapper repeated: `pinZero_stage`
  (`pin_word(53)` is `zeroLevel`, 9 lines at each of 5 sites before) and `StageR.lt64` (a slice end
  `≤ iwTop` is `< 2^64` by `IWOK`; most lemmas carry both as hypotheses).
* **`struct_proj_guards` refines `structProjGuards`** (`IndSumSpec8.lean`, the `Sim` pilot; `sorry`
  status through `strip_pis` in `structUsedLaterList`). **`cons_sum_ctors` refines
  `consSumCtors`** (`IndSumSpec9.lean`, sorry-free: `ctor_info_rec` + lane `decls2`'s `env_push`;
  the constructor list taken as `DecB`, so it stays decoded across the pushes and its constants
  decode in `erecP`, which `env_push` reads). L changes: `cons_sum_ctors` loop → self-recursion;
  `ctor_info_rec` aborts unless the copied name word is a handle (`env_push`'s spec needs it).
  `env_push` enters the model as `callW p n "env_push"` (its spec has a precondition, which
  `vcgen` cannot discharge — the known gap), turned into `envPushW` in the relational lemma by
  `triple_of_callW`, as lane `decls2` does.
* **Proof cost, measured.** The pilots: `structProjGuards` 7 L lines / 212 proof lines,
  `consSumCtors` + `ctor_info_rec` 20 / 328 — still ~20–30 per L line on wrappers. Where the lines
  go: (1) **program-lookup hypotheses**, 15–20 lines per section, repeated in the spec section
  and the census section of every file (a bundle `structure XProg (p) : Prop` per module, as lanes
  `exprops4`/`decls2` have — `BvbProg`, `RecProg`, `CvgProg` — would make them one line; not
  retrofitted, every existing statement would change); (2) **record writes**: decoding a freshly
  written `EREC`/`IW` record is ~80 lines per record kind (`ciRec_stage`, `cvNew_stage`), mostly
  index arithmetic on `wrER`/`set64` reads (a generic "`wrER` at the top decodes as the decoder of
  the word list" would remove it; `decCV_shift` is a start); (3) **the twin side of each callee**,
  `cases h : callee … | none | some` plus rewriting the twin bind — what `Sim.bindK` removes (the
  pilot's relational lemma is 45 lines for 4 callees, against ~15 per callee before); (4) the
  `vcgen` spec is cheap (5–10 lines) and was never the problem. The generic decoder lemma
  (landing 1) replaces the per-decoder `_grow` lemmas and `hstab` hypotheses at no cost per use.
* Census (this branch on master `9c9e5b6`+): phase 8 **61 proven, 37 sorry, 117 written, 8 todo**.
* Note for lane `whnf`: `scripts/provenance.py check` reports 9 uncited FunDecls in
  `WhnfDelta.lean` (master).

## End-to-end runs (2026-10-22, lane `e2e`)

Files: `ConAgua/E2E/{Ser,Dump,Check,Trace,Main,Ref}.lean`, `scripts/e2e.c`, `scripts/e2e.py`,
`docs/e2e.{md,csv}`; three executables in `lakefile.toml` (`e2e-l`, `e2e-ref`, `con-ron-lean`).
The L code is ahead of the proofs; this lane runs it on real inputs to find bugs before the
proofs do. `scripts/e2e.py` (niced, memory-guarded, every run with a timeout, about 5 minutes
on 12 jobs; never a merge gate) does everything and writes `docs/e2e.md`; `--csv` appends a line
per entry to `docs/e2e.csv`.

### The assembly: from the lanes' modules, through text

* **No hand-maintained list.** `ConAgua/E2E/Dump.lean` collects every binding of an L function
  name to a `FunDecl` in the `ConAgua` modules: each constant of type `Prog` (first binding of a
  name wins, as in `List.lookup`), and each `p.lookup "f" = some d` with a closed `d` in the type
  of any constant (the lanes' `…Prog p` structures and lookup hypotheses; this finds functions no
  `Prog` list contains). Lookups parametric in the ROM (`NameProg rom p`, …) are instantiated at
  `L.Rom.romData`. A body that is a bare `abort` is a stub.
* **Through text** (`Ser.lean`), because the modules cannot all be imported into one file: some
  define the same declaration (below). `e2e.py` imports every module except executables in as few
  closures as the clashes allow (four dumps today, ~5 s each), merges the dumps, and writes the
  program reachable from the entries as one file; `e2e-l asm` reads it, checks `Prog.wf`, and
  prints `asmText`; `scripts/e2e.c` is the driver (byte array 0 = the file, every word array
  `CA_WORDS` words, mapped lazily; prints `accept` only on `rdx = 0 ∧ rax = ACCEPT`).
* **Missing functions.** A called name with no binding or only `abort` stubs becomes an e2e stub
  with its own code: compiled, `DIAG.u64[0] := code; abort` (`DIAG` = one word array past every
  array the program names; the harness reads it after `rdx = 2`); under `L.run`, a call of the
  undefined `__missing_<name>` (the error `noFun` names it). A call whose argument count differs
  from the callee's parameters is redirected to a stub `__arity_<callee>_<n>` (so `Prog.wf` holds
  and a run that reaches it says so). Names bound to different bodies: the most common binding is
  used and the conflict is reported.
* **The entry** (`Check.lean`): `check()` is `TwinAccepts`' pipeline: `pb_check` (the pin-data
  buffer in byte array 1 starts with `romData`; lane `romload`), `intern_reserved_pins`,
  `builtin_prelude`, `front_run` (`≠ 0`: return `1`, the frontend's reject), `prepare_prelude`,
  `intern_all_pins` (lane romload's `internAllPinsPB`, bound explicitly: three bodies carry the
  name on master), `install_then_check`, `return ACCEPT`. The harness loads `lake exe romgen`'s
  buffer (`natOpPinSets.take 1`, the single latest-toolchain variant) and the reference runs at
  the same list (`e2e-ref --pins=1`). `builtin_prelude` and
  `prepare_prelude` have no L code, so every run of `check` stops there; `check_np()` is the same
  pipeline without the two prelude stages, a test entry whose reference is the twin's pipeline
  without them (`e2e-ref --no-prelude`). Not in `check` yet: the capacity checks at entry (in L a
  too-small array aborts on its first out-of-bounds access, so the test runs are sound without
  them; the proof needs them) and `AState.worker` between the phases (the twin's
  `installThenCheck` has none either).
* **E2E patches** (`Check.lean`, listed in the report): a hook a lane has specified but not made
  yet, so that the code behind it runs now. One today: `apply_dline` with the inductive line's
  `pl == 25` hook to `apply_ind_line` (`IndApply.lean`'s header; DESIGN.md lane `indproofs`). Its
  534 lines of unproved L run on every inductive fixture.

### The reference and the classes

* `e2e-ref FILE [--no-prelude]` (`Ref.lean`): the vendored twin compiled by Lean, the stages of
  `TwinAccepts` on the whole file as one buffer (`parseBytes`), `.verified`, at the empty pin
  list (the program's ROM carries no pin variant, `L.Rom.romPins = []`). `con-ron-lean` (con-ron's
  own driver) is built too; `--no-pins` gives the same verdicts on the fixtures tried. Reference
  verdicts are cached by fixture hash and the vendored revision.
* Fixtures: con-leche's 493 e2e fixtures (the `.gz` ones decompressed) and the 182 arena tests.
* Classes (`L` = compiled `check`/`check_np`): `agree-accept`; `agree-reject` (L's frontend says
  reject, the twin rejects at a line); `agree-reject (L aborts)` (both non-accept; L stopped by an
  `abort`, which is how every twin error is translated); `agree-reject, stage differs`;
  `missing` (the run reached a stub; the histogram counts the first stub each fixture reaches);
  `l-error` (L aborts, the twin accepts: a bug or a capacity); `DISAGREE-accept` (L accepts, the
  twin does not: **a soundness bug**), `DISAGREE-reject`; `l-exhausted`/`l-timeout`/`l-memout`.
  An `error` is retried once with every array 8 times larger (`BIG_WORDS`).
* **Where it stops.** `ConAgua/E2E/Trace.lean` is a second, tracing interpreter (mutable frames,
  no fuel): on an `abort` it reports the call stack and which `abort` of the function's body it
  was (`abort #k`, pre-order from 0). `e2e.py` traces every L error on fixtures up to 1 MiB. Verdicts
  come from the compiled code and from `L.run` (on fixtures up to 20 KB), never from the tracer;
  a fixture where compiled code and `L.run` differ is listed separately (a compiler or harness
  bug).

### Per-function differential tests (`e2e-diff`, `Diff.lean`)

From one fixture, the twin's state after `internReservedPins`, `parseBytes`, `internAllPins` and
L's memory after `e2e_front()` (the same stages): first the stores (node counts of all 19 cons
tables, both tiers: what `ArenaR` relates), then up to 200 persistent expression handles, evenly
over the ten expression tags, through `whnf`, `whnf_core` and `infer` on both sides (verified mode,
the empty environment, depth 0), each from the same two states: agreement is the same handle word
(`decE`) and equal store counts after. Under `L.run` the pin stage alone takes about 2 minutes (the
interpreter copies the arrays a callee writes), so `e2e.py` runs `e2e-diff` on 24 fixtures and
`L.run` on 12, spread over the files up to 20 KB (`--diff-sample`, `--interp-sample`); a full run
takes about 17 minutes on 12 jobs. The comparison caught the e2e assembly's own mistake on its first
run (an older `intern_all_pins` body: the stores differed on all 634 fixtures).

### First results (master `3b96365`, 675 fixtures)

1209 functions with L code reachable from the entries, 47 stubs. `check`: all 675 stop at
`builtin_prelude`. `check_np`: 1 agree-accept (`long_line_5mib`: the frontend and the fold on a
file without declarations to check), 38 agree-reject (35 by an `abort`; every one at the same
stage as the twin: the inductive validation `validate_ind_d`/`vi_rec`/`vi_ctor` where the twin
rejects at the line, `install_decl_step`'s `And` pin where it rejects at the declaration), 635
missing (`basis_pin_hit` 552, `is_proj_fn_shape` 81, `rom_basis_decls` 2), 1 l-error (below), no
disagreement. Compiled code and `L.run` agree on every fixture both ran. So far, wherever the
twin's frontend accepts a file, L's does too (the unproved inductive lines included; the one
exception is item 5 below), and the fold stops at its first stub on the first inductive or
projection-shaped declaration. `e2e-diff`: the stores agree on all 22 sampled fixtures; `whnf`
and `whnf_core` agree on 4317 of 4408 handles, both fail on 88, and 3 reach a stub (`find_proj`,
`inst1`); `infer` (the empty environment: most terms name constants) agrees on 29 and both fail on
the rest; no disagreement.

### Bugs found by e2e

Owners as in `docs/lanes.json`; reproducers are `scripts/e2e.py --only <fixture>` and, for the
assembly items, `docs/e2e.md`'s "Assembly" section (any run).

1. **Modules that cannot be imported together** (one Lean file assembling the checker is
   impossible until fixed; the e2e assembly works around it through text). At master `3b96365`:
   `Arena/DeclValRef.lean` (decls2) vs `Arena/DefEqLeaves.lean` (defeq), `decCI_defn`'s
   auxiliary `_proof_1_6`, and vs `Arena/InferLeaves.lean` (defeq), `L.Arena.toNat_add_small`;
   `Arena/WhnfCoreProj.lean` (whnf) vs `Arena/InstListRefine.lean` (exprops4),
   `L.Arena.SpineR.of_spn`, and vs `DefEqLeaves` (defeq), `L.Arena.lsNodeW_viewLen`;
   `Arena/PromoteRec.lean` (decls2) vs `Arena/Walk.lean` (done), `L.Arena.clrK`. Fixed during the
   day: `InferLeaves`/`DeclCvg` (`decCV_words`), `WhnfCoreLoop`/`InferLeaves` (`coreRef_congr`),
   `WhnfDeltaRefine`/`InferBodyLet` (`CoreSpec.zero`), `PromoteERef`/`DefEqLeaves2` (`lit_rec`).
   (`LiftBench`/`NatBits`, `L.Arena.bv`, is the known benchmark clash.) The current list is in
   `docs/e2e.md`.
2. **Arity mismatches between call sites and definitions** (each would fail `Prog.wf`):
   lane induct's call sites (now indproofs2) still call `get_app_fn(f, e)`, `get_app_args(f, e)`,
   `pi_result(f, e)`, `whnf(vis, dep, e)` — the whnf lane's functions take `(e)`, `(e)`, `(e)`,
   `(mode, vis, dep, e)`; the adapters `get_app_fn_f`, `get_app_args_f`, `pi_result_f`,
   `whnf_top` exist (`WhnfEntry.lean`), the renames at about 25 call sites do not (owner:
   indproofs2). `fab_scope_ok` (`WhnfIota.lean`, whnf) calls `loose_bvars_bounded_fast` with 2
   arguments; exprops4's (`BvarB.lean`) takes 3 `(f, k, h)` (owner: whnf).
3. **One name, several bodies**: `intern_all_pins` has three (`internAllPinsPB` in
   `L.Rom.romProgPB`, an older one through `PinProg`, and `internAllPins_rom`'s ROM version; owner
   romload: retire the old lookups). `reserved_contains` is `reservedContains` (`IndIface.lean`, induct;
   `DeclHeader.lean`'s lookups, decls2) and `reservedContainsL` (`WhnfIota.lean`, whnf; also
   `KnotWF.lean`). Pick one (owners: whnf, decls2).
4. **Stub names that look implemented under another name and convention**: `abstract1_fast(4)`
   and `instantiate1_fast(4)` (decls2's stubs) vs exprops4's `abs_entry(3)`, `inst_entry(3)`;
   `inst1(3)` (defeq's stub) vs `inst_entry(3)`. The extra argument is the walk fuel of lane
   induct's convention. Owners: decls2, defeq (rename or adapter). `inst1` is what stops `whnf` on
   a beta-redex in `e2e-diff` (136 handles over the fixtures in an unsampled run).
5. *(Fixed by lane `twinaudit`: the id tables are `IdTable`s now.)* **Sparse export ids** (`e2e/rounds_huge_gaps`, ids up to `3·10^15`): the frontend's id tables
   are dense arrays (`NID`/`LID`/`EID`, lane front's design), so `name_fresh` aborts at its
   capacity check where the twin's hash maps accept. A completeness loss, not a soundness one;
   owner front (a hash-mapped id table, or accept the loss and say so).
## Phase 2, round 4: the `checkDecl` arms' proofs (2026-10-22, lane `decls3`)

### `lvl_eq_c` everywhere in lane `induct`'s code (request of lane `decls2`, done here)

`lvl_eq_fueled`, `lvl_eq_true` (`IndIface.lean`), `block_shape_with_sort` and `block_shape`
(`IndParts.lean`) and `RecCheck.lean`'s call called the uncached `lvl_eq`, which leaves the twin's
`lvlEqC` behind. They call lane `whnf`'s `lvl_eq_c` now (one word each); `masterFns` gains a
`lvl_eq_c` stub (the closure check); the stub spec `lvlEqStub_spec` (`IndStubs.lean`) speaks of
`lvl_eq_c`, and lane `decls2`'s duplicate `lvlEqCStage_spec` is gone (one `sorry` fewer;
`DeclCvg.lean` uses the stub spec). Proofs touched: `IndInstallSpec3` (`lveW`), `IndPartsSpec4`
(`wsW`), names only. **For lane `indproofs2`**: these are your files; the change is mechanical
(`"lvl_eq"` → `"lvl_eq_c"` in `stubM`), merge it as is. `Front/IndApply.lean` still calls `lvl_eq`
(the frontend's validation; not checked against the cache).

### The value checks (`DeclValSpec.lean`, `DeclValRef.lean`)

L change: the value checks take the arm's constant record `c` (built by `erec_ci` with the kind
the twin pushes: `defnInfo`, `thmInfo`, `axiomInfo` for an opaque) and push it; `ci_new` and the
hint copy are gone. `check_constant_val` is `install_header` (lane `decls2`'s, proved) then the
type's sort, as the twin's `checkConstantVal` is `installHeader` then `inferTypeCore`/`ensureSortCore`
(`checkConstantVal_eq`: the twin's `do` duplicates its continuations into every `if` branch, so the
equation needs `ite_bindAM`/`fail_bindAM`). `check_opaque_val` is `check_defn_val`'s text (one model
`dvW`, one tail lemma `dvT`). **Refined**: `checkConstantVal`, `checkDefnVal`, `checkThmVal`,
`checkOpaqueVal` (through the core's stubs and `lvl_eq_c`'s: census `sorry`).

### `erec_ci` for every record kind (`DeclRec.lean`)

`erecCiW_core` is lane `decls2`'s `erecCiW_ok` without the record kind (the kind word, the
constant value whenever the record has one, the value word, the hint); `erecCiW_ok` follows from it,
and `erecCiW_okA` gives `axiomInfo cv` for an axiom or quotient record (`erec_ci(i, 0)`), which the
axiom and quotient arms build.

### Sorry-free leaves (`DeclBasisSpec.lean`)

`pin_at` as a word model (`pinAtW`, `pinAtW_ok`); **`ofReduceOp`**, **`installBasisDecl`**,
**`installBasisDecls`** refined without `sorry` (the basis list an `IW` slice of record pointers,
decoded below the tops: lane `indproofs2`'s `DecB`; the recursion through `callW`, the fuel
induction on the run). L change: words loaded into locals before a call (`install_basis_decl(s)`),
the finding of lane `decls2`.

Census at landing 1 (`--no-build`): phase 2 **139 proven, 15 sorry, 86 written, 91 todo** (lane
start 136 / 11 / 93 / 91); totals 558 proven / 71 sorry of 1352.

### Landing 2 (lane `romload`): the readers over `PB`, the decoder direction

* **L code** (`ConAgua/Rom/PinRead.lean`): `pb_check`, the ROM readers over `PB` (`FunDecl.toPB` of
  the ROM readers; `rom_u64`, `rom_put` written out), `intern_pin_sets` (+ `rom_exprs_to`,
  `rom_pins_to`, `rom_lists_to`, `rom_sets_to`), `rom_pin_sets`, `intern_all_pins` over `PB`
  (`internAllPinsPB`); all in `romProgPB`. Changes to the ROM readers (`Rom*.lean`): names' bytes
  must be ASCII (`rom_put`), `natVal` literals below `2^64` (tag `3`, `rom_lit`), `rom_u64` also
  checks `i + 8 < i`, the canonical-encoding check in `memo_push` (`RSET`, cleared with the memo).
* **Models read only bytes that are there**: `romB` reads `255` (no tag) past the end, and every
  `u64` read records `u64OK` (its range check) in the model. Then "the model returned" implies "the
  bytes are an encoding", with no end-position bookkeeping.
* **Proofs**: `Subst.lean` (helper, 350 lines: the substitution lemma, `triple_subPB`,
  `run_subPB`); `Dec.lean` (helper, 491 lines: names, levels, level lists in the decoder
  direction; `rom_levels` now aborts on a count ≥ `2^60`); `PinReadSpec.lean` (helper, 513 lines:
  the new functions compute their models, `pb_check`'s prefix); `DecExpr.lean` (600 lines:
  `romExprW_dec`, every expression the reader returns from is the canonical `encExprM seen e`;
  `canon_miss` is the canonicity argument); `RsetR` (RomExprRef.lean: `RSET` holds every memo
  handle; `ExprPost` now carries it). The encoder-direction proofs were adapted (literal arm,
  `u64OK`, the set). No `sorry`.
* **Test** (`lake exe romtest BUF`, `ConAgua/Rom/Test.lean`): runs `pb_check`,
  `intern_reserved_pins`, `intern_all_pins` over `PB` in the L interpreter on the generated buffer
  and the twin's `internReservedPins`, `internAllPins (natOpPinSets.take 1)`: **all 26 interned
  pin/certificate handles agree** (the store numbering is the twin's). 55 s interpreted.
* For lane `e2e`: to read the pins, bind `romProgPB`'s entries before the ROM readers, and call
  `pb_check()` first in `check()`; `e2e-ref --pins=1` is then the reference.
* Next: `internPinSetsW_dec` (the variant list in the decoder direction, `PinSetsR` the records'
  relation; helper `romload-sets`), then the stage theorem for the real program via `triple_subPB`.

### Landing 3 (interim: helpers `rec`, `pos` merged at their current heads)
* Helper `rec`: `classNPcOf`, `blockNestedBit` (proven), `classReadMinor`, `classReadSlot(s)`,
  `classRead`, `targetMajorAt` (`sorry` through stubs); its own composition helper `RSim`
  (`RecSim.lean`) and `RecStab.lean`. Helper `pos`: `NestCtx.rootHoles`, `nestHoleAt` (proven),
  `fvMapAt`, `nestHoleImg`, `replaceFVars(Go)`, `nestContainer` (through `mk_app_n`'s stub),
  `nestUniform`/`nestOccAny` pieces. L changes by both: loops to self-recursion, handle guards.
* Lemma-name clashes between the two helpers' files (`rec2/4/5_specW`, `frK*`, `rowPW_eq`,
  `iwN_grow`) were renamed on `pos`'s side at the merge (`posRec*_specW`, `pfrK*`, …); `IndAll`
  caught them.
* Census: phase 8 **65 proven, 47 sorry, 103 written, 8 todo**.

### Landing 4: helper `pos` done; lane `whnf`'s entry points
* Helper `pos` (5 h, with one fork of its own): all of `IndPos` (`NestCtx.rootHoles`, `nestHoleAt`
  sorry-free; `nestContainer`, `fvMapAt`, `nestHoleImg`, `replaceFVarsGo`/`replaceFVars` — one
  strong induction on the exec fuel, the banked memo as `RfInv` —, `nestCrest` through stubs), and
  11 of 23 `IndPos2` targets (`nestArity`, `piDomsOcc` sorry-free; `nestCtorNf`, `nestSeedOf`,
  `nestHoles`, `nestWalkStack`, `nestGroupCtors`, `nestRootCanon`, `nestUniformOk`, `nestUniform`,
  `nestInstType` through stubs). Open: `nestGrowGroup` (a WIP outside the tree), `nestAcceptGroup`,
  the `nestPos` block (`nestFields`, `nestCtors`, `nestFrame`, `nestContNew/Key`, `nestCont`,
  `nestPos`), `nestRoot`, `nestSeeds`. Hypotheses its parents must discharge: `RfInv` before the
  banked walk, a well-formed `replace_apps` memo (`hMstage`), record/slice bounds (`CtorSums`,
  `CtxIn`, `CtxSl`, `HSl`, `FMOk`, `CVSl`). L: ten loops to self-recursion, handle guards after
  `intern_sort`, `intern_const`, `replace_apps`; no bugs found. ~7.2k proof lines for ~420 L lines.
* **Lane `whnf`'s hand-off done**: the stage's call sites and stubs use `whnf_top`,
  `get_app_fn_f`, `get_app_args_f`, `mk_app_n_f`, `pi_result_f` (`WhnfEntry.lean`'s conventions);
  their specs are still `IndStubs`' `sorry`'d `RelAM` statements (the adapters' `StageR` specs need
  the `CoreS` bridge, landing 1's "tried and dropped").
* Helper `parts` started (IndParts/IndInstall, stub-free leaves first).
* Census: phase 8 **67 proven, 57 sorry, 91 written, 8 todo**.
### The ROM stubs' specs (`DeclRomStubs.lean`), for lane `romload`

The arms read con-leche values the twin interns at the point of use. Their L readers are the
stubs `rom_ci(id)`, `rom_cv(id)`, `rom_expr(id)`, `rom_basis_decls(kind)`, `rom_basis_decls_a(kind)`
(`romStubs`, lane `decls2`'s ids). Their specs are stated in lane `induct`'s stub shape (`stubM` +
`RelAM`, `sorry`): from `StageR`, the twin's `romCiT id` (`eqA`, `natA`, the `Iff`/`Nonempty`
families), `romCvT id`, `romExprT id`, `BasisKind.decls`/`declsA (basisOfW kind)` runs, `StageR`
after at the same environment, the pools grown, and the result **decoded below the tops**
(`DecB`: a record (`decRCI`, `decRCV`), a handle (`decW0E`), an `IW` slice of record pointers
(`decRBlk`)). **For lane `romload`**: these are the statements the real readers must prove; the
values all come from the startup data (`romData`), which `PB`'s prefix check makes the program's
own. `rom_pin_sets()` (the variants, `CTL[150]`/`CTL[151]`) has no spec yet: see "The definition
arm and the pins" below.

### Through the stubs: the reduce family (`DeclReduceSpec.lean`)

**Refined**: `reduceOpCvA`, `ofReducePinA`, `reduceDeclPin` (one model `selW` for "read a pin,
pick one of two ROM ids"; through the ROM stubs), `reducePinGuard` (through `rom_expr`'s and the
walks' stubs), and **sorry-free** `reduceCertVar` (pin reads, `const_e`, `intern_fvar`; L gained a
handle guard after `const_e`) with `constE_stage` (`const_e` under `StageR`, from lane `whnf`'s
`constE_spec`). Name clashes met: `DeclCvg.decCV_words` (renamed `decCV_slice`; lane `whnf`'s
`WhnfDeltaRefine` has its own), `PromoteRec.clrK` (renamed `pmClrK`; `Walk.lean` has one).

### `checkDecl` at the loop's relation (`DeclArmLoop.lean`, `DeclCheckLoop.lean`)

* **The arms' text.** `armText` (the arms' modules, the real master callees they reach,
  `cvgProg`, `ivProg`, then the step's program) and `armFns`; `armText_closed :
  closedA armText stepA stepC armFns` by `decide +kernel`. `ArmProg p` (agreement on `armFns`)
  gives the frame; the callees' lookup structures (`ValProg`, `RecProg`, …) are separate
  hypotheses (`CheckDeclProg`), as in `DeclCallees` — deriving them from `ArmProg` needs
  `rfl` on lookups through a ~600-entry program, which times out in the elaborator.
* **`check_decl_thm` refines the `.thmDecl` arm** at `LoopR` (`checkDeclThm_loop`: model with
  `callW` for `check_constant_val`/`check_thm_val`, their census theorems on the runs, the text's
  frame, `LoopR.of_step`).
* **`checkDecl_loop` is proved** from the five arms' specs (`ArmSpec`): the dispatcher's model,
  `DeclAt` fixing the kind word, the inductive branch unreachable under the front's records. The
  theorem arm's spec is proved; the axiom, definition, opaque and quotient arms' specs are
  `sorry` (`checkDeclAxiom_loop`, …) until the canonical comparisons (helper `decls3-canon`), the
  `Nat` gate (helper `decls3-nat`) and the ROM readers are in. `CheckDeclSpec` (the statement)
  lives in `DeclStepGo.lean` and is threaded into `installStepGo_spec` as a hypothesis (no import
  cycle); `Checker.lean`'s `DeclCallees` gains `cd : CheckDeclProg p`.
* **The definition arm and the pins.** `CheckDeclSpec` quantifies the pin list `pins`, and nothing
  in `LoopR` relates it to the memory: true today only because `rom_pin_sets` is an aborting stub
  (every `Nat.div`-family install declines in L). Once lane `romload` loads variants from `PB`,
  the loop's relation needs "the variant records (`CTL[150]`, `CTL[151]`) decode to `pins`", and
  the definition arm's spec takes it.

### `lvl_eq_c` under the stage relation (`DeclLvlStage.lean`): what is left

`lvlEqC_stage` (sorry-free): from `StageR`, **`TwinOK`** (the readback caches hold readbacks,
`NStoreWF`, the `EREC`/`SPN` sizes below `2^63`), a filled pin table and the two levels'
denotations, a `lvl_eq_c` run is an `lvlEq?` run with `StageR` and `TwinOK` after and the pools
untouched (its write set from the text, `lvlText_closed`). So the stub spec `lvlEqStub_spec`
(`sorry`) reduces to two missing facts, both cross-lane:
1. **`StageR` must carry `TwinOK`** (lanes `indproofs2`, `whnf2`): a conjunct about the twin state
   (and two sizes), kept by every memory-only step for free, by interns through "the store only
   grows" (`denoteL` stable under extension; `NStoreWF` by the name interns), by `flushCaches`
   (empty caches) and the scratch bracket (whnf's `CoreS` lemmas). Changing `StageR`'s shape
   touches every anonymous `⟨CheckR, IWOK⟩` in 35 files; not done here.
2. **The compared handles denote** (`denoteL a.store.ls (decI u) = some _`): the callers get `u`
   from `ensure_sort_core` (a stub whose post `decW0L` says nothing about denotation) and the zero
   level from `PinsFull` — lane `whnf`'s open `CoreS.lvl_den`. A store invariant "every level
   handle in the store denotes" would serve both.
`DeclLvlStage` is not in `DeclAll` (own lakefile entry): importing it brings `WhnfIotaRefine`'s
`frW` and `FVarRange`'s `frW` together (a clash between lanes `whnf2` and `exprops`).

### `sorry`s (lane `decls3`, at landing 2)

* `DeclCheckLoop.lean`: `checkDeclAxiom_loop`, `checkDeclDefn_loop`, `checkDeclOpaque_loop`,
  `checkDeclQuot_loop` (the four arms' specs; replace lane `decls2`'s single `checkDecl_loop`
  `sorry`, which is now a proof).
* `DeclRomStubs.lean`: `romCi_spec`, `romCv_spec`, `romExpr_spec`, `romBasisDecls_spec`,
  `romBasisDeclsA_spec` (the ROM readers; lane `romload`).
* `IndStubs.lean` `lvlEqStub_spec` now speaks of `lvl_eq_c`; lane `decls2`'s `lvlEqCStage_spec`
  is gone (see `DeclLvlStage` above for what is left).
* Unchanged: `Checker.lean` `promoteNew_spec` (helper `decls3-promote` running).

Census at landing 2 (`--no-build`): phase 2 **142 proven, 19 sorry, 80 written, 90 todo**.
### Landing 3 (lane `romload`): the pin stage, proved; numbers

* **The stage theorems** (`ConAgua/Rom/Stage.lean`, for the real program `P`, whose pin readers
  read byte array `PB`; all sorry-free, axioms `propext`, `Classical.choice`, `Quot.sound`):
  * `pbCheck_PB`: a returning `pb_check()` means the buffer `bs` is `romData ++ rest`.
  * `internReservedPins_PB`: `intern_reserved_pins()` over `PB` refines `internReservedPins`.
  * **`internAllPins_PB`**: `intern_all_pins()` over `PB` refines **`internAllPins P` for the pin
    list `P` the buffer decodes to** (`∃ pins ips a', (internAllPins pins).run a₀ = .ok (ips, a') ∧
    ArenaD s'.mem a' ∧ PinSetsR s'.mem ips ∧ StateOK a' ∧ RsetR s'.mem`). `PinSetsR`
    (`ConAgua/Rom/PinSets.lean`, helper `romload-sets`, 802 lines: `internPinSetsW_dec`) says the
    24-word `EREC` records listed at `CTL[150]`/`CTL[151]` hold `ips`; that is what
    `rom_pin_sets()` and `check_div_mod_pin_loop` read.
  * Proof route: `triple_subPB` (the run over `PB` is the run of the substituted program, readers
    at `rom := bs`), the startup items in the encoder direction (`internAllPinsW_fixed`:
    `internAllPins = internAllPins [] >>= fun _ => internPinSets pins`), the variant list in the
    decoder direction.
* **Obligations this leaves to the pipeline composition** (`PipelineRefines`): the hypotheses of
  `internAllPins_PB`: `PinProg bs (P.subPB bs)` (the assembled program's lookups; the readers by
  `romName_subPB` etc., every other function by `lookup_subPB_noPB`, a syntactic check), the twin
  facts `StateOK`/`PinsOK`/`PersPins`/scratch off at that point (as in `stages_frame`), `RsetR`
  (true on the loaded all-zero memory, `RsetR_zero`, and kept by every stage that leaves `RSET`,
  `RMEMO`, `CTL[132]`, `CTL[148]` alone: `RsetR.frame`), `pb_check()` called before the first
  reader; and downstream, `PinSetsR` kept from `intern_all_pins` to the declaration loop (the
  records lie below `CTL[129]`; every later `EREC` write is above it, `ErecGrow`).
* **e2e (the twin, `e2e-ref --pins=N`, on con-leche's 313 accepting e2e fixtures, gz ones
  unpacked)**: with no pins 292 accept (the 21 declines lane `decls2` counted); with the repository
  toolchain's variant only (`romgen OUT 1`) **296**; with all three committed variants
  (`romgen OUT 3`, 1 423 897 bytes) **313/313**. Most of the 21 fixtures were exported by older
  toolchains (v4.33), so the single-variant decision of ROADMAP §3 (c) keeps 17 of them declined;
  since the pin data is now an input, the harness can simply load the three-variant buffer
  (completeness only: with several variants L's "no recovery" in `check_div_mod_pin_loop` aborts
  where the twin would try the next variant after an *error*; a "not defeq" moves on in both).
  The L checker itself does not accept any fixture yet (lane `e2e`: missing functions); what is
  tested end to end in L is the pin stage: `romtest` (L interpreter vs the twin) **26/26** handles
  equal on the 1-variant buffer (55 s) and **78/78** on the 3-variant buffer (580 s). Buffers:
  `_tmp/romload/pins.bin`, `_tmp/romload/pins3.bin`.
* Sizes: `ConAgua/Rom/` 3 336 lines (Subst 351, PinRead 214, PinReadSpec 513, Dec 491, DecExpr
  600, PinSets 802, Stage ~230, PinStream/Gen/Test 170); edits to `Rom*.lean` ≈ +400 lines.
  Build: every new file under 10 s; `Rom.lean` 3.4 s.
* Not done: the census link of `internPinSets` itself (only `internAllPins` gets a
  `refines_part`); a spec of `rom_pin_sets()` against `PinSetsR` (the consumers' lane will want
  it: `er_to_iw` of the record list); the e2e program does not bind the `PB` readers yet
  (lane `e2e`, see landing 2).


### Landing 5: helper `rec` done
* Helper `rec` (5.5 h): 12 whole `@[refines]` — `targetMajorAt`, `blockNestedBit`,
  `targetMajorPins`, `targetOutsideInst`, `classReadMinor`, `classNPcOf`, `classReadSlot(s)`,
  `classRead`, `classConstOk`, `classRuleOk`, `classFormerTy` (most through stubs:
  `inst_lp_fast`, `mk_app_n_f`, `infer_type_core`, `open_pis_at_fvars_f`, `fvar_type_d`). Own
  helpers `RecSim.lean` (`RSim`), `RecStab.lean` (`RecsDec`, from which `classRead` derives its
  callee's `hstab`). **Bugs** (L): `class_read` computed `IW[rc0+1] - nP` unguarded (wraps when
  `rP < nP`; the twin's `Nat` subtraction truncates) — now truncated in `class_read_n_slots`;
  `class_read_slots` the same on `d - np` (`class_read_slots_snoc`). Handle guards after
  `intern_fvar`, `intern_bvar`, `intern_const`. ~5.3k proof lines for ~300 L lines.
* Open in Rec*: `classFieldsOf`, `ClassGen.*`, `classGenRecTy/Rule`, `classRecTy(s)Ok`,
  `classRulesOk`, `classRecsRulesOk`, `classFeR`, `targetAbs(Go)` (helper `rec2`, running);
  `auxRuleFire` needs a `view_ls` word model; `targetParamsDefEq`, `targetClassMatch`,
  `targetCtorsOf`, `targetRecPins`, `targetK53`, `class*Agree`, `classCtor(s)Of`, `classMajors`,
  `classSeeds`, `checkBlockClasses`, `genRecCheck` wait on other lanes' callees.
* Census: phase 8 **67 proven, 62 sorry, 86 written, 8 todo**.
### The middle layer (`DefEqMid*.lean`, helper `defeq-mid`)
* Refined, no `sorry` (eight files, ~5800 lines, ~98 s CPU): `defeq_no_fvars`, `lazy_fold_ok`,
  `bool_true_shortcut`, `try_unfold_proj_app`, `delta_quick`, `defeq_offset`, `defeq_lams_inner`
  (`DefEqMid`); `defeq_lst`, `defeq_list_rev` (`DefEqMidLoops`); `defeq_peel`, `defeq_binders`
  (`DefEqMidPeel`); `defeq_lams` (`DefEqMidLams`); `quick_defeq` (`DefEqMidQuick`, closes
  `QuickDefeqSpec`); `defeq_spine` (`DefEqMidSpine`); `lds_left`/`lds_right`/`lds_both`,
  `lazy_delta_step` (`DefEqMidLazy`); `lazy_delta_reduction` (`DefEqMidLazy2`). Each at L fuel
  `n + 1` from `KnotUpTo p n`, against `coreKnot (decMode mode) fe id F`, `F ≥ n`.
* **L split for the proofs** (same semantics, new functions with citations): `peel_leaf`,
  `peel_dom`, `peel_step(2)`, `peel_push`; `lams_open`, `lams_inst`, `lam_pair`; `quick_sort`,
  `quick_forall`, `quick_lam`; `spine_head`, `defeq_spine2`, `spine_cmp`; `lds_unfold2`,
  `lds_same`; `lazy_nat`, `lazy_iter`; the loops of `defeq_lst`, `defeq_list_rev`, `defeq_peel`,
  `defeq_lams`, `lazy_delta_reduction` as named blocks. `defeq_binders` pushes through
  `peel_push`. Node reads go through `e_view`.
* **L fixes** (words the twin reads differently): `spine_cmp` takes any `lvls_eq_c` word `≥ 2` as
  `some true` and `lds_same` any hint kind `≥ 2` as regular (`decO`/`decHintW`'s readings);
  `lazy_nat`/`lazy_iter` normalise a verdict word to `0`/`1`, and `lazy_iter` continues only on a
  step answer `0` (any other word but `1`, `2` is `.unknown`, as `decDS`).
* **Hypotheses** (`LazyCallees`): `InstListOK`, `Inst1OK`, `HasFvarOK`; `NatPredW` (`nat_pred`
  with `ResW`: `natPred_refines` proves `ResH` only); `UnfoldDefOK`, `ReduceNatSpec` (lane `whnf`'s
  theorems are `sorry`); `StoreDenotes` (a stored sort's level and a stored constant's level list
  read back, which `lvl(s)_eq_c`'s refinements take as hypotheses). Depth `< 2^63` throughout.
* The twin's `defeqPeel`, `defeqLams`, `lazyDeltaReduction` get no equation lemmas in the
  heartbeat budget; their one-level unfoldings are stated with the recursion abstracted
  (`peelLvl`, `lamsLvl`, `lazyLvl`) and proved by `delta` + `rfl`, as con-ron's bridge does.
* Findings: (1) `finish (gen := N)` did not raise the term-generation limit here (the diagnostics
  still said `gen := 8`); `sym (gen := 80) (instances := 5000) only [...]` did, and made the
  specs with three or more calls and 4–5-tuple results pass. (2) A multi-pattern arm lemma whose
  only binding of a variable is its right side is never instantiated: state the callee's run as
  a hypothesis instead (`lamsW_inner`). (3) `omega` with `2^24` and `2^64` produced a proof the
  kernel rejects (deep recursion), `docs/gaps/omega-kernel-deep-recursion-2pow24.lean`; stated
  with the `@[noinline]` `peelFuel` it is an atom and fine.

## Phase 5 finished: ι, the verified walks in the core, the stubs (2026-10-22, lane `whnf2`)

### Landing 1: `CoreS` carries the walk memos and the binder stack bound
* **`CoreS.memos : CoreMemos m`**: arrays 49 (`abs1C`) and 50 (`instLC`) hold well-formed memos
  (`MemoRG` at *some* map). `instantiateListFast`, `abstract1Fast` and `abstractRangeFast` clear
  their memo on entry and exit, so the twin's map never matters to a caller; what L needs is that
  its epoch-bump clear starts from a well-formed memo (`memoRG_clear` assumes one). Stated over
  the memory alone, the invariant survives every writer that avoids arrays 49/50 and `CTL[48]`/
  `CTL[50]` (`CoreMemos.frame`, `frame_hi`), whatever the twin state does: no twin-side frame
  needed. A walk call replaces the twin's map by any map (the first clear overwrites it).
* **`CoreS.bstk`**: lane `defeq`'s binder stack (array 145) below `2^63` (their request, part 1;
  part 2, `StackKept` keeping `BSTK`, is not done yet).
* Construction sites (19, also in lane `defeq`'s `KnotSlot`, `DefEqLeaves2`, `InferBodyIntern`):
  two more terms each; `arena_frame`/`arenaFrame` gain two auto-param avoidance hypotheses
  (`:= by decide`), so their callers are unchanged; `CoreS.of_proj` now takes `mk_proj`'s fine
  frame (`mkProjW_frameA`; the ROM's `StoreA` frame is all of arrays 0‥63); `CoreS.of_level`'s
  counts are below 42 (was 64). `WhnfIotaRefine`'s `frW` is now `findRuleW` (it clashed with
  `FVarRange.frW` once the walks are imported).
* Provenance: the nine split functions of `WhnfDelta.lean` had no citation (`check` failed on
  master); cited.


### Landing 6: the frontend hook (helper `front`)
* The front's chain covers `inductive` lines with no `sorry`: `validate_ind_d`/`install_ind_d`
  refine `validateIndD`/`installIndD`, `apply_ind` the `.ind` arm of `processLineCoreD` (now in
  `COMPLETE_BY_PARTS`), and `frontLine_refines` is `@[refines applyLine]`, `frontRun_refines`
  `@[refines parseBytes]` (the "(inductive lines abort)" labels are gone). Details in helper
  `front`'s own section above (route via `apply_ind` in `decl_val`, `Prog`-indexed line models,
  `FrontInv` carrying con-ron's `StateOK`/`PinsOK`/scratch-off: new hypotheses of the capstone on
  `a₀`, `DIND` = `DLP`). ~9.9k lines, 6.25 h.
* Census: **parseBytes, applyLine, processLineCoreD, validateIndD, installIndD proven**; totals
  586 proven / 105 sorry / 244 written / 417 todo of 1352 (before this landing 537 / 104 / 279 /
  432); phase 8 unchanged at 67 / 62.

## The checker as one program (2026-10-22, lane `integrate`)

Lane `e2e` assembled the checker through a text dump because the lanes' modules could not be
imported together and disagreed at call sites. This lane makes it one Lean program:
`L.Checker.checkerProg` (`ConAgua/Checker/Prog.lean`), assembled by import.

### Migration notes (integrate)

Every edit in another lane's file is a rename or a call-site fix; no statement changed meaning.
Merge master and adapt new uses:

* **Declaration renames** (they made modules impossible to import together; the side renamed is
  the one with fewer uses):
  `WhnfIotaRefine3`: `arW` → `iotaArW` (clashed with `ArRange.arW`);
  `DefEqMidPeel`: `internFVar_core` → `peel_internFVar_core`, `keeps_cpl_internFVar` →
  `peel_keeps_cpl_internFVar`, `pushK` → `peelPushK`, `word_add_toNat` → `peel_word_add_toNat`
  (and the use in `DefEqMidLams`);
  `DefEqLeaves`: `lsNodeW_viewLen` → `defeq_lsNodeW_viewLen` (use in `DefEqMidPeel`),
  `view_lit_nat` → `defeq_view_lit_nat`;
  `DefEqMidQuick`: `eViewW_head` → `quick_eViewW_head`;
  `InferLeaves`: `toNat_add_small` → `infer_toNat_add_small`, `decCV_words` → `infer_decCV_words`;
  `InferBodyLet`: `CoreSpec.zero` → `CoreSpec.zeroLet` (uses in `InferBody{Bind,BindPi,Disp,Spine,SpineF}`);
  `InferBodyBind`: `lamsW` → `inferLamsW`;
  `WhnfCoreLoop`: `coreRef_congr` → `whnf_coreRef_congr`;
  `WhnfCoreProj`: `SpineR.of_spn` → `SpineR.of_spn_core`;
  `WhnfDeltaRefine2`: `viewLs_run` → `whnf_viewLs_run`;
  `DeclValRef`: `decCI_defn` → `decls_decCI_defn`;
  `PromoteLsRef`: `viewLs_run` → `promote_viewLs_run`, `lsNodeW_view` → `promote_lsNodeW_view`;
  `PromoteERef`: `lit_rec` → `promote_lit_rec`.
  Left: `LiftBench`/`NatBits` (`L.Arena.bv`), benchmarks only (not imported by the checker).
* **Call sites.** `fab_scope_ok` (`WhnfIota.lean`) calls `loose_bvars_bounded_fast(4000000000,
  0, fab)` (lane exprops4's `(fuel, k, e)`); `LooseBVarsBoundedFastOK` and `fsW`
  (`WhnfIotaRefine3`) take the fuel word `4000000000` too. (indproofs2's `get_app_fn`/`get_app_args`/
  `pi_result`/`whnf` call sites were already fixed on master.)
* **One name, one body.** `reserved_contains`: the whnf/knot/defeq loop version
  (`reservedContainsL`) is now the L function **`reserved_contains_w`** (`WhnfIota.lean`'s calls
  and `IotaProg` field, `KnotWF.lean`, `DefEq.lean`'s three calls); `reserved_contains` is
  `IndIface.reservedContains` (lanes induct/decls). `intern_all_pins`: `L.Rom.internAllPinsPB`;
  the ROM-only versions (`RomCI.internAllPinsAt`, `Prelude.internAllPinsL`) are bound as
  **`intern_all_pins_rom`** in their theorems (dead in the checker: lane romload may delete them).
* **Adapters** (`ConAgua/Checker/Entry.lean`): `abstract1_fast(f, e, d, k)` → `abs_entry(e, d, k)`,
  `instantiate1_fast(f, e, v, d)` → `inst_entry(e, v, d)`, `inst1(e, v, d)` → `inst_entry(e, v,
  d)` (lane exprops4's entries; the fuel is unused). The stub specs of these names
  (`IotaInst1OK`, lane induct's `RelAM`s) are now about the adapters: discharge them from
  `instEntry_refines`/`absEntry_refines`.
* **The inductive line hook**: lane indproofs2 landed it in `Line.lean` (with its proofs) while
  this lane worked; the checker takes `L.Front.applyDLine`, and e2e's patch is gone.
* **`rom_expr_pin(id)`** (landing 2): lane decls' stub `rom_expr(id)` (the reduce pins,
  `DeclArms.lean`'s two calls, `DeclRomStubs.romExpr_spec`, `DeclReduceSpec`, `romStubs`) had
  the same name and arity as romload's ROM expression reader `rom_expr(pos)`, so the assembled
  checker silently called the reader at position 0/1. Renamed; the generator cannot see such a
  clash (stubs are not bindings), so a stub's name must not be an existing function's.
* **New rule: one name, one body, project-wide.** `scripts/checker_prog.py` fails if two non-stub
  bindings of a name (any `Prog` constant, any `p.lookup "f" = some d` in a type) differ, or a
  call's argument count differs from the callee's; it also needs every module importable together.
  Run it (`--check` to verify `Prog.lean` is current) when you add or rename an L function.

### Landing 1: `checkerProg`, the prelude stages, `check`'s entry

* **`ConAgua/Checker/Prog.lean`** (generated by `scripts/checker_prog.py`; `--check` says whether
  it is current): `checkerProg`, 1419 functions reachable from `check`, each the lanes' own
  `FunDecl` constant, imported (110 modules); `checkerProg_wf : Prog.wf checkerTab checkerProg`
  by `Prog.wf_of_wfFast (by decide +kernel)` (35 s with the file's `#guard`). `Prog.wf` includes
  "every called name defined exactly once with the caller's arity" (`Nodup` of the names, every call
  resolved). The generator imports all 391 non-benchmark modules in one closure (the clash list is
  empty), asks `ConAgua/Checker/Sources.lean` for each binding's Lean term, and fails on two bodies
  for one name or an arity mismatch. Called functions with no L code are `abortStub n`, listed in
  `checkerStubs` (35).
* **`ConAgua/Checker/Entry.lean`**: `check()` (moved from `E2E/Check.lean`), now first
  `cap_check()`: every word array below `2^63` words and `CTL` at least 256 words, else abort
  (ROADMAP §3's requirement; `arenaR_init`'s `64 ≤ |CTL|`, its pool bound). Not checkable in L:
  an array of `2^64` words or more (`len` is mod `2^64`); `MemRel` in the final theorem rules
  such arrays out, `PipelineRefines` (any `s64`) does not yet: it needs a size premise.
  Also the adapters, `is_proj_fn_shape` (`NIdx.isProjFnShape`: the
  `num`/`str` views, the pool bytes of `proj`/`projTable`) and `basis_pin_hit` (`basisPinHit`:
  per kind, `rom_basis_decls(kind)`, the name pre-filter on the records' word 1, then
  `canon_eq_list`).
* **`ConAgua/Checker/Prelude.lean`**: `builtin_prelude()` runs **the frontend's own L code on
  the prelude**: `preFn` renames a frontend function onto byte array `PRE` (2; the bytes copied
  from the program constant `preludeBytes`, `preludeBytes_eq : preludeBytes =
  preludeText.data.toList` by the kernel, 15 s) and the id tables `PNID`/`PLID`/`PEID`
  (208‥210, so the stream's parse starts with empty id tables, as the twin's second `parseBytes`).
  The generator copies the 129 functions reachable from `front_run` that touch the input or the
  id tables (`pre_<name>`). `DECL`/`DLP`/`DIND` are shared: the prelude's records first, their
  count in `CTL[240]`. `prepare_prelude()` is `frontOf` on `DECL` (each prelude record replaced by
  the stream's first record declaring its key, which leaves the stream), then `hoist_ok`: the
  ground hoist must be the identity (no pinned `Nat` operation's `natOpDeps` ground first declared
  after it), else abort (a decline; the twin would reorder), then `DECL` rewritten in that order.
  Proof obligations (no theorem yet): `preFn` preserves the frontend's refinement with the arrays
  renamed; `frontRun_refines` from a `DECL` that already holds records; the two stages'
  refinements.
* **e2e** (`scripts/e2e.py`): the program is `checkerProg` plus `E2E/Check.lean`'s test entries
  (`L.E2E.writeChecker`); `--text-dump` keeps the old assembly as a fallback. Byte arrays from 2
  on get `CA_WORDS` bytes in the harness (and under `L.run`). A second reference: con-ron's Rust
  binary (`nix develop` in a worktree of `_tmp/ref/con-ron` at `vendor/UPSTREAM`'s revision,
  `cargo build --release -p con-ron`, `_tmp/ref/con-ron-integrate/target/release/con-ron`;
  `$CON_RON` overrides), run as `con-ron --jobs=1 --pins P` with `P` the same single pin variant
  in its `con-ron-pins/1` format (written by `ConRon.Dump.dumpPins`, now built as a root of
  `ConRonArena`); and `instructions:u` of compiled `check` vs con-ron on fixtures both accept.
### Landing 3: the opaque arm, the axiom tests (`DeclBasisSpec2`, `DeclReduceSpec2`, `DeclReducePin`, `DeclArmOpaque`, `DeclAxiomSpec*`)

* **Refined** (through the ROM stubs and, for `checkReducePin`, the core's and the walks' stubs):
  `checkBasisDecl`, `reduceStoredOk`, `reduceElemOk`, `checkReducePin`, `ofReduceAxOk`,
  `trustCompilerOk`, `stdAxiomOk`; **sorry-free**: `IConstantVal.matchesPin` (helper
  `decls3-canon`'s `cv_eq`: word equality is the derived `decide (cv = pin)`, `matchesPin_eq`).
* **The opaque arm at the loop's relation is proved** (`checkDeclOpaque_loop'`): the pushed view
  `vis2` for `check_reduce_pin`, which runs its gate at the pre-insertion view: `StageR.restrict`
  (the stage relation at another view of the same index, `EnvR.restrictTo`) and back, no frame
  argument needed. `CheckDeclProg` gains `crp`; `checkDecl_loop` and the skeleton's
  `DeclCallees` take **`DnInj dn`** (the name decoding injective: comparing constant records reads
  `PropWhen`'s names through it; the top level's `dn` is the store's `denoteN`).
* **The twin's nested matches, flattened.** `trustCompilerOk`/`stdAxiomOk` nest `match fe.find? (←
  name) with | some (.ctorInfo cv 2 2) => … | _ => pure false` three deep. A relational lemma
  cannot rewrite with a lemma about such a `match` (the auxiliary matcher of the lemma is not the
  definition's), so: the shape test as a partial function (`fpShape k a b ci : Option
  IConstantVal`), one clause `clausePT fe n k a b T` (match on `(fe.find? n).bind (fpShape …)`),
  and one equation per twin function proving it equals the chain of clauses
  (`trustCompilerOk_eq`, `stdAxiomOk_eq`: `congr`/`funext` through the binds, `cases` on the
  stored constant at each clause; generated, ~100 lines). The L clause (`find_pinned`) is then
  proved once against `clausePT` (`fpW_ok`: the kind and count words against the shape,
  `fp_fail`/`fp_pass`).
* L changes: `std_axiom_ok`'s two families are one function `std_ax_family(vis, q, s1, s2, s3, i1,
  i2, i3, c2, c3, cvid)` (one model; the inline version ran `finish` out of instances); a handle
  guard after `reduce_cert_var` (`is_def_eq_core`'s spec); words loaded into locals before calls
  in `of_reduce_ax_ok`. Note on `finish`: `(instances := 5000)` is a valid config item (the default
  `1000` ran out on an 11-parameter function).
* Helper `decls3-canon` merged in interim (record equalities `cv_eq`/`ci_eq`/`find_is`, `ci_to_cv`,
  stage lemmas for `intern_nanon`/`intern_nnum`/`intern_succ`); its `rdW_grow` renamed
  `cnRdW_grow` (clash with `IndPos2SpecA`).

`sorry`s now (lane `decls3`): `checkDeclAxiom_loop`, `checkDeclDefn_loop`, `checkDeclQuot_loop`
(the opaque arm's is proved), the five ROM stub specs, `lvlEqStub_spec` (lane `induct`'s, now on
`lvl_eq_c`), `promoteNew_spec` (helper running).

Census at landing 3 (`--no-build`): phase 2 **145 proven, 26 sorry, 71 written, 89 todo**.

### Landing 6: the stuck/irrelevance side (`DefEqStuck*.lean`, helper `defeq-top`)
* Refined (no `sorry`, ~4.9k lines, 81 s CPU): `prop_irrel`, `eta_cert`, `eta_ctor_shape`, the
  structure-η certificate (`struct_eta_cert*`), `struct_unit_cert`, `stuck_irrel`, `stuck_str`,
  `stuck_app`, `defeq_stuck`, `defeq_proj_pair`, `lazy_delta_proj_reduction`, `defeq_tail`.
  Hypotheses (`StuckCallees`): `DefeqLstOK`, `LazyDeltaStepH` (both proved by `defeq-mid`: to be
  plugged in), `ProofIrrelOK` (lane whnf's `proofIrrel_refines` has two more premises, `n ≤ 2^62`
  and the eager bit: add them here when plugging), `ReduceProjCoreH`, `Inst1OK`,
  `TowerSlotsAllOK`, `StrLit*`, `SupKeep`, `ReservedContainsOK`, `LvlsEqCH` (needs the "stored
  level lists denote" invariant, as `InferProjOK`).
* L: `eta_cert_body` aborts on depth wrap; `defeq_stuck`'s constant arm reads a level verdict
  `≠ 1` as true (`decO`); proof splits as listed in the helper's commits; one test per `if` took
  `defeq_stuck`'s spec from ~2 min to 3 s.
* Merge with lane `integrate`: duplicate top-level names between helper files clash in
  `scripts/checker_prog.py` (`decDS`, `decOptR_*`, `growRef_*`, the `Inhabited DeltaStepA`
  instance, now in `DefEq.lean`): the stuck files' copies are suffixed `S`. `Checker/Prog.lean`
  regenerated (1467 functions).
* Left for the lane: `defeq_body` itself, plugging the proved specs into the hypotheses, the knot
  induction (`KnotUpTo p n → KnotOK p (n + 1)`), `infer_proj`, and the `CoreS` invariants above.

### Landing 2: exact walk counters, the walks and `nat_op_result` under `CoreS`, `major_to_ctor`
* **Exact `coreWalkFuel` counters** (helper `whnf2-walks`, ROADMAP §3 (b)): `fr_go`/`fr_memo`,
  `bb_go`/`bb_memo`, `inst_go`, `il_go`/`ilg_go`, `abs_go`/`ab_node`, `ar_*` take the twin's depth
  counter as an L argument (`if f == 0 { abort }`, children at `f - 1`; `abstract1`'s cut-off
  `ab_fvb(h, f - 1)`, as the twin's `fvarB fuel h` at the decremented fuel). The entries keep their
  arity and start at `4000000000` (`coreWalkFuel_toNat`); `bvar_b`/`loose_bvars_bounded_fast`/
  `has_fvar_fast` use their (formerly unused) `f`. Statements: twin at exactly `c.toNat`, any L
  fuel; the bb/fr walks also at any `F` with `c.toNat ≤ F ∨ n ≤ F` (`*_correctF`, `bvbW_okF`), which
  lane `indproofs2`'s counter-less `has_loose_b_var_b_go` needs (its `bvbW_stage`; `IndSumSpec5`
  adapted minimally; that walk itself still has no exact counter: lane `indproofs2`'s).
* **Result words.** `CoreSpec`'s default post wants the result *word* below `2^32` (callers compute
  with it; `decE` truncates). The four entries (`inst_entry`, `inst_list`, `abs_entry`,
  `ar_entry`) return `r & 4294967295` and post `(r.headD 0).toNat < 2^32`; the Boolean ones post
  `≤ 1`; `reduce_nat_op` normalises `nat_op_result`'s pair (`u64(rf != 0)`, `rh & 4294967295`):
  the same values under `decE`/`decOpt`, one `and` each.
* **`CoreWalks.lean`**: `CoreS.of_walk` (an L frame below 64, `cpl` kept, the walk memos given),
  `Keeps cpl` for every core walk (`keepsL_auto`, `cpl`'s primitives; the memo probes under
  `with_reducible`, else unification unfolds `instLGet` against `inst1Get` and times out), and the
  bridges `instListOK_core` (`WhnfCallees.instList`), `inst1_core` (`CoreCallees.inst1`: one
  `FunDecl`, `instEntry`, at the two names `inst_entry`/`inst1`), `lbb_core` (`IotaCallees`;
  `fab_scope_ok` now passes the counter), and lane `defeq`'s `abs1_core`, `absRange_core`,
  `hasFvar_core` (`Knot.lean`'s `Abstract1OK`, `AbstractRangeOK`, `HasFvarOK`, same statements).
  The walk-memo trick: the twin's run from `a₀` *is* its run from `a₀` with `instLC`/`abs1C`
  replaced by `CoreMemos`' map (the entry clears it first: `rfl`), and `ArenaD` does not read those
  memos (`ArenaD.memo_irrel`); `ar_entry` at `k = 0` changes nothing and is a separate case.
  The stub bundles still carry these fields (`whnfCallees_stub` …): replacing them needs program
  hypotheses (`InstListProg p`, …) on every census-tagged theorem; done together with the knot.
* **`nat_op_result` under `CoreS`** (first assumed fact, gone): `CoreAgree.lean`'s
  `exec_agree`/`invoke_agree` (programs agreeing on a call-closed set run it alike; `closedW` is the
  closure witness) move lane `pinsenv`'s `natOpResultL_refines` from `natArmProg` to any `p` with
  `WhnfDeltaProg'.natAgree` (new field; `natClosed` now a theorem); `CoreNatOp.lean`'s `LeafOp`
  (a twin step interning only `lit`/`const` leaves keeps `cpl` and carries `DerR` at any memory)
  gives the rest. `natOpResultOK_stub` deleted.
* **`major_to_ctor`** (helper `whnf2-m2c`): split into 12 L functions (`WhnfM2C.lean`: head,
  constructor, the constant view, the three arms and their halves, a shared type check), proved
  (`WhnfM2CRefine{,2..5}.lean`, `majorToCtor_refines'`, axioms `propext`/`Classical.choice`/
  `Quot.sound`; new hypothesis `ProofIrrelOK`, the statement of `proofIrrel_refines`, which rests
  on `CoreS.lvl_den`). `major_to_ctor` puts `CTL[136]` back. The tagged `majorToCtor_refines` and
  `prepareMajor_refines` now live in `WhnfM2CRefine5` (import order). ~150 L lines, 2634 proof
  lines; `WhnfM2CRefine` 33 s user, the rest 1–3 s.
* **`iota_rec_at`** (helper `whnf2-rec`): split into nine L functions (`WhnfIotaRec.lean`:
  head, constructor/rule lookup, major, the verified-checks block and its comparison, the result),
  proved (`WhnfIotaRecRefine{,2,3}.lean`, `iotaRecAt_refines'`, three standard axioms). New named
  hypotheses (not `sorry`): `ErecKeptRec` (the iota callees leave the record pool alone),
  `LvlsEqDen` (a successful `lvls_eq_c` under `CoreS` reads both lists back), `RecShape` (a stored
  recursor has `rP ≤ mI + 1` and plain rules `ctorParams ≤ rP`: an environment invariant, like
  `CoreS.lvl_den`). L fixes against the twin: a nested rule's pins are copied from `EREC` to the
  stack before `rec_fire_args`; `lvls_eq` → the cached `lvls_eq_c` read as `liftFueled` (`0` aborts);
  `const_ty_at` keyed on the stored constructor name; `peel_pis` before the level-count test;
  word-overflow-free arity tests; the spurious `len(SPN) < so + rP` abort removed; the stack top
  restored. ~116 L lines, ~2940 proof lines, 26 s user.
* Merging: lane `integrate` renamed `reserved_contains` → `reserved_contains_w` (one body per name),
  the m2c pieces follow; lemma-name clashes with lane `defeq`'s files renamed on this side
  (`*_m2c`, `*_rec`, `exec_agreeOn`); `ConAgua/Checker/Prog.lean` regenerated
  (`scripts/checker_prog.py`, `--check` clean).
* Census, phase 5: **67 proven / 23 sorry / 28 written / 24 todo** (start: 62 / 26 / 29 / 25);
  phase 4: 63 proven (+1). The `iota` targets stay "sorry": the tagged statements instantiate the
  stub bundles (`iotaCallees_stub`, `whnfCallees_stub`, `coreCallees_stub`, the knot).

## The id tables as the twin's `IdTable`; the deviations list (2026-10-22, lane `twinaudit`)

### Landing 1: dense array plus sparse overflow (`Front/IdTable.lean`)

The front's id tables were dense word arrays (`NID`/`LID`/`EID`, entry `h + 1`, `0` unset) that
aborted on an id at or past the array's end, where con-ron's `StateD` keeps con-leche's `IdTable`
(`Scan/Types.lean:330`): a dense `Array` grown by `push` at its frontier and a `Std.HashMap Nat`
for gaps and out-of-order ids. `e2e/rounds_huge_gaps` (ids up to `3·10^15`) was declined (e2e
item 5). Now each table `b` is

* the dense part: array `b` with its size in `CTL[b + 6]` (`70‥72`), entry `i < size` the handle
  word itself (no `+ 1`);
* the sparse part: a memo-library table (`MemoLib.lean`, one-word keys, value = handle word) at
  array `b + 8` (`72‥74`), stamp/count `CTL[2b − 64]`, `CTL[2b − 63]` (`64‥69`).

`tbl_get`/`tbl_fresh`/`tbl_put` are generic in the table (`tblGetG b fnd`, the memo's `find`/`put`
spliced in as `⟪.call …⟫`), with one `vcgen` proof each; `name_get`, `level_get`, `expr_get`,
`*_fresh`, `name_put`, `level_put`, `expr_put` are instances. `tbl_put` is `IdTable.insert`
arm for arm: at the frontier a push (when below the array's capacity), below it an overwrite,
past it the sparse map. The `apply_*` functions and `front_init` call `*_put` instead of writing
`ID[i] := h + 1`; their models are unchanged (`putK` now ends in `tblPutW`).

The relation `TblR m b t` (was `TblR (m.arr64 b) t`): the dense entries below the size are `t`'s
(handle words below `2^32`), and some `sp` with `MemoRV (spS b) idKey hVR m sp` gives `t.get?` at
every id word at or above the size. Lemmas: `TblR.read`/`fresh` (same statements as before),
`TblR.put` (one per `insert` arm: `memoRV_set` for the sparse one), `TblR.frame`/`frameD`,
`TblR.zero`; `tblOK_congr`/`tblW_congr` take a `TblSame m m' b` (the two arrays and the two `CTL`
words the reads see; `TblSame.of_eq`, `of_frame`, `of_frameD`). `StateDR.frame`,
`StateDR.put{Name,Level,Expr}` and `levelFinish` take the frame's arrays outside `idArrs` and
`CTL` words outside `idCtl` (default tactic `tctl`); `StateDR.putX` takes `tblPutW m₁ X i w =
some m₂` instead of the bound `i < size`; `ArenaD.setT` is `ArenaD.putT`; `Above64`
(`ApplyExprRefine.lean`) also fixes the `CTL` words `≥ 64`. Nothing else changed: every
refinement (`frontAll_refines`, `applyNStr_refines`, …, the inductive lines' `IndApply*`) is
sorry-free as before, and `#guard`s cover ids past the dense array, out of order, and a rebound
sparse id. `frontAllProg` runs `rounds_huge_gaps` to `front_run = 0` (`#eval`, 4096-word arrays).

Differences from the twin that remain (listed in `docs/deviations.md`): the id word `NONE =
TOMB = 2^64 − 1` is refused on the sparse path (ids past 18 digits already were); the dense array
stops at its capacity (the ids go sparse, up to the memo's 3/4 load); `IdTable.bound`'s
`sparse.isEmpty` shortcut is not mirrored (the memo's count is not tied to the map's emptiness;
`tbl_fresh` probes one slot when the map is empty).

`scripts/e2e.py` caps `e2e-diff`'s dense id arrays at `DIFF_BIG_WORDS` (they were sized to the
largest id). For lane `integrate`: test memories need arrays up to `74` and `CTL` up to word `72`
(`frontMem`, `exprMem`, `declMem` are 75 × 128 words now).

The checker program (lane `integrate`'s `checkerProg`): the prelude parse's copies (`preFn`) rename
the sparse arrays `72‥74` to `211‥213` and the `CTL` words `64‥72` to `241‥249`
(`Checker/Prelude.lean`, `preCtl`; `scripts/checker_prog.py`'s `TOUCH` copies every function that
touches them); `wordArrays` is 214. `checkerProg` was extended by hand (the generator stops at
import clashes between other lanes' modules on master); a rerun of the generator gives the same
bindings. `scripts/e2e.py --only huge`: `rounds_huge_gaps` now gets through the front on x64 and
stops at the stub `rom_basis_decls` (it aborted in `name_fresh` before).

**For other lanes** (mechanical): `TblR (m.arr64 NID) t` → `TblR m NID t`; a frame proof
`rw [hf.1 NID …]; exact h.names` → `h.names.frame hf (.inl rfl) (by simp [..., idArrs]) (by simp)`;
`lkW_congr` takes a `TblSame` (`IExt.tbl`).

### Landing 2: the deviations audit (`docs/deviations.md`), and a PLAN.md rule

Every place where L deliberately does something else than its twin (beyond fuel and fixed
capacities) is now a row of `docs/deviations.md`: where, what the twin does, what L does, the
effect (completeness / performance / none), the owner, a proposed fix. Sources: this journal
(grep for "for now", "aborts", "deviat", "simplif", "not represented", …), `docs/progress.md`'s
partial refinements, the L code's comments, `docs/e2e.md`. First count: 17 open (5
completeness, 5 performance, 7 none), 13 fixed (among them the id tables, landing 1, and
`iota_rec_at`'s `lvls_eq`, fixed by lane `whnf2` meanwhile).

The work queue, by priority:
* **D1 (decls3): `and_pin_ok` has no `indDecl` arm.** The twin's `andPinOk` checks an inductive
  block that names `And`/`And.intro`/`And.rec` against the pinned block; L reads the record's name
  word (unset for kind-6 records) and answers "free". Harmless while the declaration loop never
  sees an inductive record, a soundness gap as soon as it does (the front produces them since
  indproofs2's landing 6). Must land before the loop accepts kind-6 records.
* D4 (decls3): `check_div_mod_pin_loop` aborts inside an attempt where `orElseAttempt` recovers;
  then D5 (integrate): load all three pin variants in the e2e harness.
* D7 (indproofs2): `target_class_match` calls the uncached `lvls_eq`; call `lvls_eq_c`.
* D2, D3, D6: exotic inputs (numbers past 18 digits, escaped `safety` strings, unusual pin data).
* D8 (`tbl_fresh` probes where `IdTable.bound` tests `sparse.isEmpty`), D10‥D12 (append-only
  pools, byte-per-word strings, no memo compaction): performance.

Trivial fixes made here: stale comments that still described fixed deviations
(`Front/Line.lean`'s header, `Front/ApplyExpr.lean`'s `strVal`/`natVal` note,
`Arena/LevelEquiv.lean`'s "`lvlEqC` not represented"). Not touched, for the lanes editing them:
`Arena/Prelude.lean:12` and `Arena/DeclArmsNat.lean:28,1073` still say the ROM has no `Nat`
pin variant "for now" (lanes `integrate`, `decls3`).

PLAN.md, process rules: a deviation gets its row in `docs/deviations.md` in the commit that
introduces it; the coordinator reviews the list at each batch of landings.

### Landing 3: six phase-5 targets sorry-free on the real walks (`WhnfTagged.lean`)
* A dependency scan (each tagged theorem's transitive constants that are `sorry`'d theorems) showed
  which stub *fields* each tagged statement really used. `beta_peel`, `iota_certs_full(_aux)` used
  only `WhnfCallees.instList`; `pi_residual`, `inst_spine`, `iota_index_ok` only
  `IotaCallees.inst1`. Their primed theorems now take `InstListOK p` / `IotaInst1OK p` instead of
  the bundles, and the tagged ones live in `WhnfTagged.lean` (after `CoreWalks.lean`), given the
  walks' programs `CoreWalkProg p`: **sorry-free** (`pi_residual` newly tagged).
* Census, phase 5: **79 proven / 19 sorry / 20 written / 24 todo**; phase 4: 65 proven, 0 sorry.
* What the remaining phase-5 `sorry`s wait for (scan): `instLP` (`const_ty_at`, `rule_rhs_at`,
  `inst_spine_pins`, `rec_fire_args`: the phase-4 `instLPFast` walk is not written),
  `wscoped_bfast`/`leaf_guard` (`fab_scope_ok`), `find_proj`/`fire_ok`/`ProjFound`
  (`tower_slots_all`, `and_rescue_slots`, the projection arm), the string-literal stubs and
  `supKeep_twin` (`lit_major_to_ctor`, `proj_lit_to_ctor`), `CoreS.lvl_den` (`proof_irrel`), the
  knot's `infer`/`defeq` steps (`WhnfCallees.inferStep` …; lane `defeq`), `erecKept*`, and
  `whnfGrowsUpTo_stub` (`reduce_nat`).

### Open handoffs (lane `whnf2` closing)
* **`whnfGrowsUpTo_stub`** (the second assumed fact) stays. A `whnf` call must leave the limb pool
  below its old top alone and the top no lower (`reduce_nat_op` holds the first literal's pool slice
  across the second `whnf`). Three routes were weighed: (1) a write-set argument (`closedW` with the
  pool outside the write set) fails because the `Nat` arithmetic does write the pool (above the
  top), and its frame holds only under argument preconditions a text check cannot see; (2) re-reading
  the first literal after the second `whnf` needs the twin's store to keep every node's view across
  `whnf` (a `Keeps`-style induction over the whole knot, ~150 twin definitions); (3) carrying the
  growth in the core's post: `CoreAfter` (or `StackKept`) gains `PoolGrew m₀ m` (pool below `m₀`'s
  top unchanged, top no lower, sizes equal), proved at the leaves from frames avoiding `POOL`/
  `CTL[0]` and from the `Nat` functions' `Grows`, and composed by `CoreAfter.trans`/`comp`. Route
  (3) is the one; it touches every explicit `StackKept`/`CoreAfter` construction and destructuring
  (~300 sites, about half in lane `defeq`'s files), so it should be done together with lane
  `defeq`'s request part 2 (`StackKept` keeps `BSTK`, array 145 / `CTL[137]`), in one sweep when
  `defeq` is between landings. Suggested shape: `StackKept m m'` becomes a `structure` with named
  fields (`top`, `size`, `below`, `bstk`, `pool`) so that later additions do not move projections.
* **`CoreS.lvl_den`** (`proof_irrel`): needs "every stored level handle reads back", a store
  invariant the twin's WF gives but `CoreS` does not carry; adding it means maintaining it at every
  level-node and sort-node interning (`CoreS.of_level`, `arena_frame`).
* Remaining stub fields whose L code does not exist: `instLP` (phase 4 `instLPFast`),
  `strLitCtor`/`strLitSupported`, `find_proj`/`fire_ok` (+ `ProjFound`, `ProjSmall`),
  `wscoped_bfast`, `leaf_guard`, `caps_never_zero`, `rec_fire_levels`; `supKeep_twin`,
  `erecKeptInst_stub` (its `inst_spine` half is provable now from `instEntry_frame`; `inst_lp`'s is
  not), `erecKeptKnot_stub` and the knot steps (lane `defeq`). The new named hypotheses of the iota
  proofs (`ErecKeptRec`, `LvlsEqDen`, `RecShape`, `ProofIrrelOKM`) are listed above.

### The knot tied (`DefEqBody.lean`, `DefEqKnot.lean`, helper `defeq-knot`)
* `defeqBody_refines`: `DefeqBodySpec p n` is a theorem (from `DefeqBodyCallees` = `StuckCallees` +
  `LazyCallees`); `defeqSlot_step` = `defeq_refines` on it. The twin side is split once
  (`defeqBodyRestT`, `defeqBody_eq` by `rfl`); the proof is the `callW` chain of ten calls, 356
  lines, ~8 s CPU. `DefeqBodySpec` gains `n ≤ 2^62` (`defeq_refines` has it).
* L changes in `defeq_body`: it aborts at `d ≥ 2^63` (as `infer_lam`: `quick_defeq` and the lazy
  loop need the bound, the slots do not carry it); `if lk != 2 { return lk }` became two tests
  `lk == 0`/`lk == 1` (`decLR` reads any other word as `.unknown`; `Res3` does not bound `lk`).
* Hypothesis shapes adjusted to the proved theorems: `ProofIrrelOK` (and `proofIrrel_at`) take
  `n ≤ 2^62` and the eager bit, `propIrrel_refines` takes `n ≤ 2^62`; `LazyDeltaStepH` takes
  `d < 2^63`, threaded through `ldprW_ok`/`ldpr_refines`/`ldpr_at`/`projPair_refines`/`projPair_at`/
  `defeqTail_refines`; `LazyCallees.reduceNat` is `∀ n, n ≤ 2^62 → ReduceNatSpec p n`.
* Plugged (`DefEqKnot.lean`, one wrapper each): `lazyDeltaStepH_of`, `defeqLstOK_of`,
  `isEagerReduceH_of`, `reduceNat_of` (lane `whnf`'s `reduceNat_refines'`, over its
  `NatOpResultOK`/`WhnfGrowsUpTo`), `proofIrrelOK_of` (lane `whnf`'s `proofIrrel_refines`; it uses
  `CoreS.lvl_den`, a `sorry`, so `ProofIrrelOK` stays a field).
* **The knot**: `knot_step : KnotUpTo p n → KnotOK p (n + 1)`, `knot_all : ∀ n, KnotOK p n`
  (fuel `0` by `CoreSpec.zeroLet`), both over `KnotAllProg p` (lookups) and ONE structure
  `KnotCallees p`; no `sorry` (axioms: `propext`, `Classical.choice`, `Quot.sound`).
  `whnfCallees_of` gives lane `whnf`'s `WhnfCallees` (its `inferStep`/`inferIOStep`/`defeqStep`
  are the slot steps; `instLP` an argument). No circularity: no lane `whnf` proof uses those three
  fields.
* `KnotCallees`' fields, and why each is left: `whnfCoreStep`, `whnfStep` (lane `whnf`'s
  `whnfCoreSlot_step` and `whnf_refines` chain are proved over `whnfCallees_stub`/
  `coreCallees_stub` instantiated inline: `knotWhnfCore_twin`/`knotWhnf_twin` give them modulo
  those `sorry`s; taking the bundles as hypotheses there would make them plain fields here);
  `defeq` (`DefeqCallees`: `has_fvar` and the phase-4 walks need the `CoreS` bridge,
  `not/is_proof_fast`, `field_sort_zero`); `proofIrrel` (above); `inst1`, `instList`
  (stubs); `reservedContains`, `towerSlots`, `strLitSupported`, `strLitCtor`, `supKeep`, `store`
  (no proofs yet); `lvlsEqC` (the "stored level lists denote" invariant); `reduceProjCore` and
  `unfold` (lane `whnf`'s proofs take all of `WhnfCallees`, which holds the steps proved here:
  generalize them to the fields they use, `instLP`, to plug); `natPred` (`natPred_refines` posts
  `ResH`, the hypothesis `ResW`); `natOpResult`, `whnfGrows` (lane `whnf`'s); `constTy`, `lit`,
  `bstk`, `bcap`, `proj` (the inference side, landing 4).
### `field_sort_zero`, `NatPredW` (`InferFieldSort*.lean`, helper `defeq2-fsz`)
* **`field_sort_zero(po, pl, us, fs)` has L code** (`fieldSortZeroL`): `ls_node(us)`, heap reset
  (`CTL[192] := 0`, as `lvl_eq`), `lv_substl(fs, po, pl, o, k)` with `lv_lookup` at `KA = EREC`,
  `VA = POOL` (the binding `lvLookupG EREC POOL`; `inst_lp`/`caps_never_zero` can share it),
  `lh_mk(0, 0, 0)` for `zero`, `lv_equiv`, answer `u64(r == 2)`. Model `fszW`, spec
  `fieldSortZero_spec` (`vcgen` + `finish`), refinement `fszW_ok`, and
  **`fieldSortZero_core : FieldSortZeroProg p → FieldSortZeroOK p`** (`refines_part inferProj`;
  axioms `propext`, `Classical.choice`, `Quot.sound`). No deviation (aborts: `ls_node` on a
  dangling list, which the twin also fails on; the heap's capacity).
* **`FieldSortZeroOK` strengthened** (`Knot.lean`): the caller supplies `ReadNCOK a₀` (new: the
  twin's `readNC` rows are readbacks; `CoreS` has `readL`/`readLs` but no name counterpart, and
  `readNameM` answers a cached row unchecked), `∃ ks, lps.mapM (denoteN a₀.store.ns) = some ks`,
  `∃ ls, denoteLs a₀.store.lss (decI us) = some ls`, `∃ l, denoteL a₀.store.ls (decI fs) = some l`.
  Proposed: a `readN : ReadNCOK a` field in `CoreS` (kept by every core body as `readL` is); the
  same hypothesis will be needed by `caps_never_zero` (`capsNeverZeroPW` reads names too).
* **`NatPredW p` is a theorem**: `natPredW_of : NatPredProg p → NatPredW p`
  (`InferFieldSortNat.lean`). `natPred_refines` now posts `ResW` (new arguments: `LitInternHW`,
  discharged by `WhnfDeltaRefine3`'s `internW_hw` as `litInternHW`); `internLit_core` gives the
  handle word bound (`InternSpecW`), `natPredLit_refines_hw` is `natPredLit_refines` with it.

### `infer_proj` (`InferProj.lean`, `InferProj2.lean`, helper `defeq2-proj`)
* **`InferProjOK p` is a theorem**: `inferProj_refines : InferProjProg p → InferProjCallees p →
  InferProjOK p` (`@[refines inferProj]`), both grades through one lemma (`inferProj_grade`, the
  record `R` and its first call as parameters). Pieces: `projTypeAt_refines`
  (`@[refines IProjEntry.typeAt]`: `inst_lp`, the push of `pe` at the top, `inst_list`),
  `inferProjAt_refines` (`refines_part`, the twin past the lookup copied as `projAtT`;
  `inferProj_hit` equates). Models in the callW shape; specs by `vcgen` + `simp_all`. No `sorry`.
* **Hypotheses** (`InferProjCallees`): `CoreDen`; lane `whnf`'s `FindProjOK`, `ProjFound`,
  `ErecKept`, `InstLPOK`; new **`ErecKeptProj`** (`lvl_eq_c` and `field_sort_zero` keep `EREC`:
  `infer_proj_at`/`proj_type_at` read the table's words after them; both write only `LH`,
  `CTL[192]` and the `lq` memo, frames their proofs build but do not export). `inst_list` from
  `CoreWalkProg` (`InferProjProg.walk`), `field_sort_zero` from `fieldSortZero_core`.
* **Twin facts proved**: `findProj?` keeps level-list readbacks (`findProj?_lss`, via
  `EStore.internName_ext`) and hits only below the field count (`findProj?_lt`); `lvlEq?` keeps the
  store (`lvlEq?_store`). The subject's level list is read back (`CoreDen.constLs`) at the view
  before the lookup and carried across it.
* **L changes** (Infer.lean, same semantics on every run): `infer_proj` reads the head's name and
  level words (`cT`, `cu`) once, before `find_proj` (it re-read `CREC` after the call, which no
  spec says `find_proj` keeps); `infer_proj_at` tests `2 <= ok` for `lvl_eq_c`'s `some true`
  (was `ok == 2`; `decO` reads every word `≥ 2` as `some true`, as `spine_cmp`).

### Landing 4: the quotient and axiom arms; `and_pin_ok`'s inductive arm in L

* **`checkDecl_loop`: every arm's spec is proved but the definition arm's** (`DeclArmQuot.lean`,
  `DeclArmAxiom.lean`; `@[refines_part checkDecl "one-constant records"]`). The quotient arm
  (`quot_pin_hit`: the pinned block's constant at the record's slot, `ci_to_cv`, `cv_canon_eq`) and
  the axiom arm (`Quot.sound` against the block's slot 4 by `ci_canon_eq`, the constant check,
  `std_axiom_ok`/`trust_compiler_ok`/`of_reduce_ax_ok` then the push, `propext`/`choice` declining,
  `sorryAx` skipped) at `LoopR` through the arms' text (now covering both: real interns
  `intern_zero/succ/sort/nanon/nnum` in `armMasterFns`; `closedA` by `decide +kernel`, 8 s).
* **Hypotheses instead of the helper's not-yet-landed specs**: `CvCanonSpec p` / `CiCanonSpec p`
  (fields of `QuotProg`/`AxProg`, inside `CheckDeclProg`): the `RefAM` statements of `cv_canon_eq`,
  `ci_canon_eq`. Helper `decls3-canon` proves the canonical comparisons; its `canon_expr_eq` takes a
  literal-injectivity hypothesis (`LitInj`), which these statements will gain when its specs land.
* **`and_pin_ok` has the inductive arm in L** (`and_block_named` over the block's records in
  `DLP`, then for a two-parameter block `canon_eq_list` of the block (copied by
  `ind_block_to_erec`, `er_to_iw`) against `rom_and_pin()`, a new ROM stub with spec
  `romAndPin_spec`). The proof stays `refines_part … "one-constant records"`: `LoopR` still holds
  the one-constant `DeclsR`; the inductive arm becomes provable once the loop's relation takes the
  front's `DeclsF` (lane `indproofs2`'s `DeclAtF`/`IndDeclAt`, now on master) and `canon_eq_list`
  is in.
* **For every lane that changes L code reached from `check`**: rerun `scripts/checker_prog.py`
  (regenerates `ConAgua/Checker/Prog.lean`, lane `integrate`'s whole program); a stale file fails
  `checkerProg_wf` in the kernel.

`sorry`s now (lane `decls3`): `checkDeclDefn_loop`; the six ROM stub specs (`romAndPin_spec` new);
`lvlEqStub_spec`; `promoteNew_spec` (helper running). Census at landing 4: phase 2 **146 proven,
26 sorry, 73 written, 86 todo**.


### Landing 2: the ROM constant records (helper `integrate-romci`)

`ConAgua/Rom/CIEnc.lean` (encoder), `CIRead.lean` (L readers), `CIReadTest.lean`: the con-leche
constants the `checkDecl` arms intern at the point of use (the basis blocks in both forms, the
eight `rom_ci` constants, the ten `rom_cv` values, the two reduce pins) are a structured region of
`romData` (`ciOff`, between the reserved names and the item stream: a table of 30 offsets, then
the entries; numbers as 8 bytes, names/levels/expressions with romload's encoders, each part in the
twin's intern order). `rom_basis_decls(kind)`, `rom_basis_decls_a(kind)`, `rom_ci(id)`,
`rom_cv(id)`, `rom_expr_pin(id)` read it from `PB` (after `pb_check`) and write `decCI`/`decCV`
records (`L.Rom.romCIProg`). `romData` grows from 9542 to 20649 bytes (regenerate `romgen`
buffers). Test: an `#eval` (3 s) decodes every entry to the twin's value, handle for handle. The
five `RelAM` specs of `DeclRomStubs.lean` stay `sorry` (now about real code). Small difference:
the reader interns the `sortZ` names the twin keeps as values (only `Quot`'s `u`, already
interned as a level parameter).

### Landing 2 also: `ind_params_ok`; e2e results on `checkerProg` (675 fixtures)

* `ind_params_ok(nP, off, len)` (`indParamsOk`) in L (`Checker/Entry.lean`). `basis_pin_hit`
  reads the block as `check_decl` builds it: an `EREC` slice (`ind_block_to_erec`), not the
  `IW` slice `IndIface.lean`'s interface note says; copied to `IW` (`er_to_iw`) for
  `canon_eq_list`. (Lane indproofs2: the note and `IndStubs`' specs say `IW`.)
* **`check`** (the real pipeline, prelude included): 3 agree-reject, 40 agree-reject (L aborts),
  630 stop at a stub — all at **`strip_pis`** (lane induct's interface stub, the next blocker;
  then `all_level_params_defined` on 129 in `check_np`) — and 2 l-error, both `hoist_ok`'s
  decline (`natop_order`, `natop_before_ble`: deviation D18). No disagreement. Every fixture's
  prelude now parses, prepares and passes `basis_pin_hit` (the five basis blocks match the ROM's).
  `rounds_huge_gaps` passes the front (lane twinaudit's id tables).
* **Three references:** con-ron's Rust binary and `e2e-ref` agree on all 675 fixtures (405
  accept, 206 reject, 55 decline, 4 error; 2 time out in both; one is a con-ron abort `-6` where
  `e2e-ref` runs out of memory). `instructions:u` (L vs con-ron) needs fixtures L accepts: none
  yet (the measurement is in `e2e.py`, `docs/e2e.md` shows it once there are).
* `e2e-diff` unchanged (stores agree on 22/22; `whnf`/`whnf_core` agree on 4318 of 4408 handles,
  no disagreement).

### `sorry`s and open obligations (lane `integrate`)
No new `sorry`. Open: the refinements of `builtin_prelude` (through `preFn`), `prepare_prelude`
(`frontOf`, `hoist_ok`), `cap_check`'s use in `PipelineRefines` (and its missing size premise for
arrays of `2^64` words or more), `basis_pin_hit`, `ind_params_ok`, `is_proj_fn_shape` (specs
already stated with `sorry` in `IndStubs.lean` for the last three), the adapters (from
`instEntry_refines`/`absEntry_refines`), the ROM readers (`DeclRomStubs.lean`'s five `RelAM`s).

### Landing 3: `rom_and_pin`; a stale shared-cache artifact

* `rom_and_pin()` (lane decls3's new stub for `and_pin_ok`'s inductive arm, which made every
  fixture's prelude `And` block decline) reads ROM slot 30 (`encBlock andPin`; `CIReadTest` checks
  it against `andPinDecls`). `check` is back at `strip_pis` on every fixture that reaches the fold.
* **The shared Lake cache restored a stale `ConAgua.Checker.Entry` olean** (a `synthetic` trace,
  `inputs: []`, built from an older `Entry.lean` without `indParamsOkL`): `scripts/lake build`
  said "completed" while `#check L.Checker.indParamsOkL` failed, and `checker_prog.py` then saw
  `ind_params_ok` as a stub. Plain `lake` with `LAKE_CACHE_DIR=` rebuilt it correctly. Not
  investigated further (coordinator: the cache key of a module restored with an empty `inputs` list).

## Phases 6–7: discharging `KnotCallees` (2026-10-22, lane `defeq2`)

### Landing 1: the real walks, the plain plugs, `StoreDen`
* **`KnotCallees` lost twelve fields** (`DefEqKnot.lean`): `inst1`, `instList` and `DefeqCallees`'
  `hasFvar`/`abstract1`/`abstractRange` are lane `whnf2`'s `CoreWalks` bridges (new program field
  `KnotAllProg.walks : CoreWalkProg p`); `fieldSortZero` is `fieldSortZero_core`, `natPred` is
  `natPredW_of` (helper `defeq2-fsz`, above); `natOpResult` is `natOpResultOK_of_agree`;
  `reservedContains` is `reservedContainsOK_of` (from `callW_reservedContains`); `bcap` is
  `CoreS.bstk`; `lit`'s `natLitSup`/`constE` are lane `whnf`'s proofs; `lvlsEqC` is
  `lvlsEqCH_of` (below). `defeqCallees_stub` (a `sorry`) is gone. `KnotWF`'s closure list uses the
  real `field_sort_zero` and `inst1`; `Checker/Prog.lean` regenerated.
* **`StoreDen m a fe`** (`StoreDen.lean`): the one store invariant the level readers need, because the
  twin compares levels on their readbacks and L on handles: a `sort` node's level, a `const`
  node's level list, the zero pin, the `readNC` cache's rows, and a projection table record's
  structure sort, field sorts and level-parameter names read back. `CoreDen` (`CoreDen.lean`) is
  "`CoreS` implies `StoreDen`": a `KnotCallees` field now (`den`), replacing `StoreDenotes`
  (`StoreDenotes.of_den`). **Proposal (for lane `whnf3`, after its `StackKept` sweep): a field
  `den : StoreDen m a fe` in `CoreS`**, which also closes `CoreS.lvl_den` (`⟨hS.den.sort,
  hS.den.zero⟩`), `LvlsEqDen` (the iota lists are stored constants' or the rule's), and
  `ReadNCOK` (helper `defeq2-fsz`'s proposal). Maintenance: the store only grows inside the core,
  so old handles keep their readbacks; the view clauses need a proof only where a `sort`/`const`
  node is interned, `readN` where `readNameM` caches, `proj` where `EREC` is written (outside the
  core). Until then `CoreDen` stays a named hypothesis.
* **`LvlsEqCH` restated with the two readbacks** and proved (`lvlsEqCH_of`): its two callers
  compare stored constants' lists. `struct_eta_cert_go`/`_tail`/`_wtb` take "some `const` node at
  the call's state has this list" (`∃ x c, a.store.view x = some (.const c us)`); across
  `tower_slots_all` (which interns name nodes) the node is still there: `towerSlotsAll` keeps the
  store minus its level/name part (`noLss`, `keeps_noLss_towerSlotsAll`, `constLs_after_tower`).
* `KnotCallees` now: `whnfCoreStep`, `whnfStep` (lane `whnf`'s steps over its stubs),
  `notProofFast`, `isProofFast` (helper `defeq2-prop` writing `PropRead` in L), `proofIrrel`
  (`CoreS.lvl_den`), `towerSlots`, `strLitSupported`, `strLitCtor`, `supKeep`, `reduceProjCore`,
  `unfold`, `whnfGrows` (lane `whnf`'s/`whnf3`'s), `den`, `constTy` (`inst_lp`), `bstk` (after
  `whnf3`'s `StackKept` structure), `proj` (helper `defeq2-proj`: `infer_proj`).
### Landing 5 (lane `decls3`): helpers `promote` and `canon` merged

* **`promoteNew_spec` proved** (helper `decls3-promote`, `PromoteCI*.lean`, 30 files): the constant
  records' promotion (`promote_ci` and its parts, the erase/re-index loops) refines the twin's
  14 steps `promoteNList` … `promoteNew` (`PromoteCITags.lean`). Statement change: `k.toNat ≤
  vis.toNat` (the twin's `c - 1` truncates; the callers pass `k = v2 - vis` or `0`). L: records are
  written after their parts (`erec_rd*`/`erec_wr*`, `pci_mk`, `rec_block`).
* **The canonical comparisons proved** (helper `decls3-canon`): `canon_name_map`, `canon_level_eq`
  (and lists), `canon_expr_eq`, `canon_names(_go)`, `cv_canon_eq`, `canon_rules_eq`, `ci_canon_eq`,
  `canon_eq_list`, `cv_eq`, `ci_eq`, `find_is`, `ci_to_cv`. Extra hypotheses their callers must
  supply: `LitInj` (the store hash-conses literals: L compares literal handles, the twin values),
  `PoolSmall`, `DnInj` (`ci_eq` only); records decoded in `erecP m`. `CvCanonSpec`/`CiCanonSpec` in
  the quotient and axiom arms are to be replaced by these.
* Name clashes after merging (both helpers and master): renamed on the helpers' side (`pm*`, `cn*`).
  A whole-tree clash check (every `.olean`'s constant names; `_tmp/decls3-logs/clash/Clash.lean`)
  found them at once where `checker_prog.py` reports one per run.

### Landing 6 (lane `decls3`): `all_level_params_defined` in L

`DeclApd.lean`: `all_level_params_defined(o, l, e)` (the twin's `allLevelParamsDefined`,
`CheckerBase.lean`), `alpd_go` (the memoized DAG walk, fuel per recursion level as the twin's),
`alpd_ls` (a `const`'s level list, read in `POOL` via `ls_node`); lane `levels`' `lv_apd`/`lv_mem`
bound at `A = IW` (the parameters are `cv_lps`'s `IW` slice; handles compare as names). **Memory
map addition**: word array `151` = `APDM` (walk-local memo, cleared at each call), `CTL[152]`,
`CTL[153]` its stamp − 1 and live count. The memo aborts at 3/4 load where the twin's `HashMap`
grows (the memo library's capacity rule, as every L memo). Refinement: not yet (the stub specs in
`DeclCvg`/`DeclHeader` still use `stubM "all_level_params_defined"`).


### Landing 2: `PropRead` in L (helper `defeq2-prop`), `infer_proj` (helper `defeq2-proj`)
* **`not_proof_fast`/`is_proof_fast` have L code and proofs** (`PropRead.lean`: 18 L functions;
  `PropReadLoops`, `PropReadW`, `PropReadRefine{,2,3,4}`; ~3600 lines, ~35 s CPU):
  `notProofFast_core`/`isProofFast_core` (`@[refines]`, as are the sub-walks `typeSortPW`,
  `headTypePW`, `proofPW`, `peelPisW`, `unwrapIdDefs`, `lamProj?`, …). The `PropWhen` datum is
  three words `(k, o, c)`: `0` none, `1` `never`, `2` `ifAllZero` with the names in `LH[o, o+c)`;
  both readers reset the level heap on entry. Exact walk fuel: a new `app_count_at(e, f)` gives
  `getAppFn` and `numArgs` at fuel `f`. `Level.substPW` on heap names: `spwW_ok_lh`, a variant
  of lane `levels`' `spwW_ok`. Hypotheses: `CoreDen` (plus `ConstLpsDen`, now the new
  `StoreDen.constLps`: a stored constant's level-parameter names read back) and lane whnf's
  `FindProjOK`, `ErecKept`, `ProjFound` (lane `whnf3`). No deviation.
* **`infer_proj`**: see the helper's section above. L changes: `infer_proj` reads the head's
  name and levels before `find_proj` (no spec says `find_proj` keeps `CREC`); `infer_proj_at`
  tests `2 <= ok` (`decO`'s reading). New hypothesis `ErecKeptProj` (`lvl_eq_c` and
  `field_sort_zero` keep `EREC`; to come from lane `whnf3`'s write-set argument, `CoreErec`).
* `KnotCallees` now: `whnfCoreStep`, `whnfStep`, `proofIrrel`, `towerSlots`, `findProj`,
  `erecKept`, `projFound`, `reduceProjCore`, `unfold`, `constTy`, `instLP`, `whnfGrows` (lane
  `whnf3`); `strLitSupported`, `strLitCtor`, `supKeep` (helper `defeq2-str`, running); `den`
  (the `CoreS` field, lane `whnf3`); `bstk` (after the `StackKept` sweep); `erecProj`.
* Merging: lemma-name clashes renamed on this side (`hslice?_bound_fsz`, `projBodyW`);
  `scripts/checker_prog.py` dumps modules it does not build: build `ConAgua.Rom.CIRead` first, or
  `rom_ci` comes out as a stub and `checkerProg_wf` fails on `reduce_decl_pin`'s arity.
## Phase 5 continued: the stacks and the pool in `CoreAfter`, the record pool from the text (2026-10-22, lane `whnf3`)

### Landing 1: `strip_pis`, `strip_lams` (helper `whnf3-walks`)
* L code only (`StripTele.lean`, lane induct's convention `(ok, off, len, body)`, the domains an
  `IW` slice), to unblock e2e (`check` stopped at the stub on 630/675 fixtures). Refinements later.
  New modules must be listed in `lakefile.toml`'s `globs` (the generator dumps built modules only).

### Landing 2: `StackKept` carries the binder stack and the limb pool (with lane `defeq`)
* **Shape** (agreed with lane `defeq`, its request part 2 and whnf2's open handoff route (3)):
  `StackKept m m'` and `StackGrew m m'` are structures with fields `top`, `size`, `below` (the old
  three conjuncts), `bstk : BKept m m'` (binder stack `BSTK` = 145 below `CTL[137]` kept, top and
  size equal; `bTop`/`BKept` moved from `InferBodyBind.lean` to `WhnfBase.lean`) and
  `pool : PoolGrew m m'` (pool below `m`'s top `CTL[0]` unchanged, top no lower, size equal). So
  `CoreAfter` carries both, and they compose with `trans`.
* **Construction**: `StackKept.of_frame hf` (auto-params `SPN`/`BSTK`/`POOL ∉ A`, `136`/`137`/`0 ∉ C`
  by `decide`), `.of_frame_range`, `.of_grows`/`.of_frame_grows` (a `Grows` then a frame),
  `.of_spnFrame`/`StackGrew.of_spnFrame` (pushes on the spine stack), `StackKept.restore`
  (now also takes the `BKept`/`PoolGrew` of the run) and `.restoreG` (a grew-run, top put back).
  `CoreS.frame` now avoids arrays `≥ 146`/`CTL ≥ 138` (it posts `StackKept`); the old range is
  `CoreS.frameS` (CoreS only: the telescopes' `BSTK` pushes).
* **The telescopes** (`InferBodyBind`, `InferBodyBindPi`, lane `defeq`'s): `TelPost` gains `lo`
  and "`BSTK` below `lo` kept, size equal, pool grew"; `tPush_step` posts them; `tops_restore`
  builds the restored `StackKept` (both tops) directly. `BStkCallees`/`BStkCap` stay as lane
  `defeq`'s hypotheses; both follow from the callees' `CoreAfter` now (`hSt.bstk`, `CoreS.bstk`).
* **The `Nat` arms keep the pool**: every arm refinement is generic in the relation, so
  `nat_op_result` refines at `ArenaP m₀ = ArenaR ∧ PoolGrew m₀` (`PinsNatOp.lean`:
  `natOpResultL_refinesR` over `NatArmsR R`, the tagged `natOpResultL_refines` its `ArenaR`
  instance; `CoreNatOp.lean`: `natArmsR_pool`, `intern_lit`/`intern_const` from their text write
  sets). `nat_pred_lit`/`nat_succ_lit` likewise (`callW_natPredLit`/`callW_natSuccLit` post
  `PoolGrew`).
* **`whnfGrowsUpTo_stub` is gone**: `reduce_nat_op` reads the first literal's slice across the
  second `whnf` through that call's `CoreAfter` (`hSt.pool`, `PoolGrew.slice`).
* About 300 sites, 40 files (whnf and defeq); one-line shapes mostly (`.2.1` → `.size`,
  `⟨t, s, b⟩` → `of_frame`); loops with an explicit "kept below the start" invariant
  (`peelFull_ref`, `appFull_ref`, `spioFull_ref`, `spFull_ref`, `lamsFull_ref`, `pisFull_ref`)
  gained `BKept m₀ m`/`PoolGrew m₀ m` (or the `BSTK`-below-`lo` triple) in their invariant.

### The record pool from the program text (`CoreErec.lean`)
* `ErecKept`, `ErecKeptInst`, `ErecKeptKnot`, `ErecKeptRec` ("a call of `f` leaves `EREC`") are
  facts about the text: no function the core reaches stores into `EREC`. `coreFns` (the call
  closure of `coreRoots` in `checkerProg`, a literal list regenerated by `scripts/core_fns.py`, 443 functions) and
  `closedA p coreErecA coreErecC coreFns` (all arrays but `EREC`, every `CTL` word below 256);
  `callW_erec_closed`; `ErecKept*.of_closed`. At `checkerProg` it is
  `L.Checker.checkerProg_coreErec` (`decide +kernel`, 74 s). `erecKeptInst_stub` and
  `erecKeptKnot_stub` deleted; the tagged `instSpinePins_refines`, `recFireArgs_refines`,
  `majorToCtor_refines`, `prepareMajor_refines`, `iotaRecAt_refines` take `hcl` instead (and
  `iotaRecAt_refines` no longer takes `ErecKeptRec`). When a stub of the closure gets code that
  calls new functions, regenerate `coreFns`.

### Landing 3: the binder stack and `EREC` from lane `whnf3`'s sweep
* **`BStkCallees` is gone**: the telescopes (`InferBodyBind`, `InferBodyBindPi`) read the binder
  stack's preservation off each callee's `CoreAfter` (`StackKept.bstk`, `CoreAfter.bkept`);
  `BStkCap` is `CoreS.bstk`. `KnotCallees.bstk` removed.
* **`ErecKept`, `ErecKeptProj` from the core's write set** (`erecKept_of`, `erecKeptProj_of`:
  `callW_erec_closed`), the program hypothesis `KnotAllProg.hcl : closedA p coreErecA coreErecC
  coreFns`. `KnotCallees.erecKept`/`erecProj` removed.
* `KnotCallees` left (14): `whnfCoreStep`, `whnfStep`, `findProj`, `projFound`, `proofIrrel`,
  `towerSlots`, `reduceProjCore`, `unfold`, `constTy`, `instLP`, `den` (lane `whnf3`'s next
  landings: `find_proj`/`fire_ok`, the `instLP` family, `CoreS.den`); `strLitSupported`,
  `strLitCtor`, `supKeep` (helper `defeq2-str`).

### String literals in L (`StrLit*.lean`, helper `defeq2-str`)
* **L code** (`StrLit.lean`, 389 lines): `str_lit_supported` and its seven stages `str_sup_1…7`
  (one per tested declaration, the suffixes of the twin's chain), the tests `string_ty_ok`,
  `char_ty_ok` (one body), `list_ty_ok`, `list_nil_ty_ok`, `list_cons_ty_ok`,
  `char_of_nat_ty_ok`, `string_of_list_ty_ok`; `str_cv` (`toConstantVal`, including the
  projection-table arm that interns `Sort 1`); `str_param_sort`, `str_ls1` (`internLsNode [u]`:
  the word at the pool top, then `intern_ls`); `str_lit_ctor` = `str_ctor_pre` (the
  literal-independent prefix) + `str_cons_spine` (recursion over the characters, as the twin's)
  + `String.ofList`. Characters are decoded from the pool's UTF-8 byte words by
  `str_utf8_char` (`utf8_char` reading `POOL.u64[k] & 255`), linked to Lean's decoder through
  lane `lext`'s `utf8CharN_eq`: non-ASCII is handled, no deviation. A character's literal is
  `rom_lit(c)`. `abortStubs` lose `str_lit_ctor`, `str_lit_supported` (`Checker/Prog.lean`
  regenerated: 1574 functions, 26 stubs).
* **Proofs**: `strLitCtor_core : StrLitProg p → StrLitCtorOK p` (`StrLitCtor.lean`),
  `strLitSupported_core : StrLitProg p → StrLitSupportedOK p` (`StrLitSup.lean`),
  `supKeep_of : ∀ fe, SupKeep fe` (`StrLitKeep.lean`: `VMono`, a twin-side "every stored view is
  kept" predicate closed under bind/if/match). No new hypotheses. `WhnfBase.lean`'s
  `supKeep_twin` (a `sorry`) is now redundant: its users should take `supKeep_of` (a Whnf file:
  lane `whnf3`'s). `KnotCallees.strLitSupported`/`strLitCtor`/`supKeep` can be plugged with
  these three (`KnotAllProg` needs `StrLitProg`'s lookups; `KnotWF`'s closure list still stubs
  `str_lit_*`).
* **New leaves under `CoreS`** (`StrLitBase.lean`): `CoreS.of_ls` (a level-list interning: the
  list tables only grow, `LsStore.view_intern_mono`), `internParam_core`, `internZero_core`,
  `internW_core`/`romLitW_core` (a `lit` interning from a pool slice), and `callW` wrappers
  `param_call`, `succ_call`, `zero_call`, `sort_call`, `bvar_call`, `const_call`,
  `constE_call`, `app_call`, `romLit_call`, `ls1_call`, all in the `CoreRef` shape for
  `coreRef_bind` chains. `StrLitCv.lean`: `cv_call`. `StrLitTy.lean`: the `∀`-type tail
  `faEqT`/`faEqW_ok`, `cref_run`.
* **Finding**: `str_lit_ctor` reads the literal's record *after* the prefix interning, so the
  record and the bytes are read at the memory the spine runs on and the twin-side view of `h`
  carries over by `VMono` alone; reading it first would have needed pool/record frames through
  every `CoreRef` (which keeps only `CoreS`).
* Deviation D24 (performance): `str_ls1` and `rom_lit` leave their pushed word at the pool top
  even when the node exists.
* Numbers: 389 L lines, 3524 proof lines (`StrLitList` 954, `StrLitChar` 478, `StrLitCtor` 467,
  `StrLitSup` 455, `StrLitBase` 437, `StrLitCv` 247, `StrLitTy` 213, `StrLitKeep` 147,
  `StrLitUtf8` 126); user CPU per module ≤ 10 s except `StrLitChar` (~28 s, the
  `string_of_list_ty_ok` spec at `maxHeartbeats 2000000`). 12:04–12:56, sub-helpers
  `-keep`, `-utf8`, `-list`, `-sup`.

### Landing 4: string literals plugged (helper `defeq2-str`, section above)
* `KnotCallees.strLitSupported`, `strLitCtor`, `supKeep` removed: `strLitSupported_core`,
  `strLitCtor_core` (program field `KnotAllProg.str : StrLitProg p`) and `supKeep_of`.
  Lane `whnf`'s `supKeep_twin` (`WhnfBase.lean`, a `sorry`) can now be `supKeep_of` (lane
  `whnf3`'s file). `StrLitBase` adapted to the `StackKept` structure (helper `defeq2-strfix`).
* `KnotCallees` left (11), all lane `whnf3`'s: `whnfCoreStep`, `whnfStep`, `findProj`,
  `projFound`, `proofIrrel`, `towerSlots`, `reduceProjCore`, `unfold`, `constTy`, `instLP`, `den`.


### Landing 8: helpers `parts` and `rec2` done
* Helper `parts` (3.2 h): `blockSplitRecs`, `blockSplitCtors`, `blockSplit` (sorry-free),
  `ctorMember?`, `blockGroups`, `blockRecNameSetOk`, `blockMemberCounts?`, `blockShape?`,
  `blockParts?`, `piDomsMentionAny`, `blockRawRec`, `BlockShape.nestCtx`, `blockNestCtx` (through
  stubs). L: capacity guards, `block_shape_nest_ctx` read its inputs after writing the new
  record — moved before the allocation (a latent bug, harmless while the allocation was fresh
  memory); D18 (`sl_cons`-built slices, quadratic) added to docs/deviations.md. Open:
  `blockLargeElimAllowed` (needs `lv_nz`/`readLevelM` under `StageR`, the `CoreS` bridge again),
  `checkBlock*`, `consBlock*`, `checkAbsCtorSorts*`, `blockCapsAt` (needs a `RelAM` for
  `lv_zero_caps`). ~6.75k proof lines.
* Helper `rec2` (3.4 h): `classFieldsOf` (the `nest_occ` memo carried across stubs by
  `stubM_memoFrame`), `ClassGen.major/motiveTy/minorTy/prefixBinders`, `classGenRecTy`,
  `classRecTyOk`, `classRecTysOk`, `classGenRule` (through stubs). Open: `classRulesOk`,
  `classRecsRulesOk` (loops), `classFeR`, `targetAbs(Go)`. Its overflow guards (`d + bl < d`,
  `rP + nF`, …) are capacity aborts (word arithmetic the twin does in `Nat`), not rows of
  docs/deviations.md. ~5.4k proof lines.
* `ConAgua/Checker/Prog.lean` (lane `integrate`'s generated whole program) gained the 29 helper
  functions the two helpers' rewrites introduced, by hand: `scripts/checker_prog.py` currently
  stops on an import clash between `PropReadW` and `PromoteCI` (`L.Arena.armK.eq_1`, not this
  lane's). `checkerProg_wf` holds.
* Census: phase 8 **72 proven, 79 sorry, 64 written, 8 todo**; totals 670 proven / 124 sorry of 1352.

### Landing 3: the helpers' walks and the projection lookups (helpers `whnf3-walks`, `whnf3-proj`)
* **`wscoped_bfast`, `leaf_guard`** (helper `whnf3-walks`; `WalkScope`, `WalkLeaves`,
  `WalkScopeRefine`, `WalkLeavesRefine`, `WalkCore`, 2.4k lines): `wscopedBGo`+arms,
  `wscopedBFast`, `fvarLeavesGo`+arms, `fvarLeavesFast`, `leafMem`, `leavesSubGo`+arms,
  `leafGuard` refined sorry-free, exact `coreWalkFuel` counters; `WscopedBFastOK`/`LeafGuardOK`
  proved under `CoreS` (`wscoped_core`, `leafGuard_core`, from `WsProg`/`LgProg`). The walk-local
  maps are epoch-cleared memo-library tables: arrays 151 (`wscopedB`, key `(h, d)`), 152
  (`fvarLeaves`' `seen`), 153 (`leavesSub`), stamp/count `CTL` 152‥157; the leaf list is array 154
  (`LVS`, newest first, `LeafR`). `CoreMemos` carries their well-formedness (`WalkMemos`), so
  `CoreMemos.frame`/`frame_hi`, `CoreS.frame` and `arena_frame` gained avoidance auto-params;
  `CoreS.frameSM`/`frameS`/`frameM`/`frame` (memos given / derived; spine stack written / kept).
  `finish (instances := 5000) (gen := 12)` was needed on the memo-miss paths.
* L code only (refinements open): `instantiate1_lift_fast` + arms (`WalkLift.lean`, memo
  `inst1LC` = array 51, `CTL` 52/53), `inst_pis_at_lift`, `fvar_type_d`, `fvar_type_ds`
  (`TeleLift.lean`, lane induct's conventions). The `instantiate1Lift` proof will need an exact
  counter in lane exprops' `lift_entry` and array 51's memo well-formedness in `CoreS`/`StageR`.
* **`proj_table_name`, `find_proj`, `fire_ok`** (L by this lane, proofs helper `whnf3-proj`;
  `WhnfProj.lean`, `WhnfProjRefine{,2,3}.lean`, ~1200 proof lines): `projTableName`,
  `IFEnv.findProj?`, `IProjEntry.fireOk` refined. `CoreS.of_name` carries `CoreS` across name
  interning (twin step `NameStep`, `NStoreWF` from con-ron's `NStore.intern_spec`, the `ViewOK`
  from L's validity check of `t`: D22); the nine pool bytes are a `Grows` (D21);
  `FindProjOK`, `ProjFound` and the `find_proj` half of `ErecKept` proved. `fire_ok`: on master
  `FieldSortZeroOK` (lane defeq2) now asks for the readbacks, so `fireOk_refines` proves
  `FireOkOKD` (`FireOkOK` with `us` reading back) from two named hypotheses, `ProjSortDen`
  (structure sort, zero level) and `FireDen` (name cache, level parameters, guards); both follow
  from lane defeq2's `StoreDen` once `CoreS` carries it, and `FireOkOKD`'s `us` from
  `StoreDen.constLs` at the callers.
* Clashes fixed for `scripts/checker_prog.py`: `PropReadW`'s `armK` → `propArmK` (vs
  `PromoteCI`), `WhnfProjRefine2`'s `projA` → `projWA` (vs `Promote`). `Checker/Prog.lean`
  regenerated: 13 stubs; `coreFns` regenerated (498 functions).
* Not in this landing: helper `whnf3-lp`'s `instLP` family (branch `whnf3-lp`, on `whnf3-next`):
  its `lv_lookup`/`lv_spw` bindings (keys on the spine stack, `lvLookupG SPN POOL`,
  `lvSpwG EREC`) clash with lane defeq2's (`lvLookupG EREC POOL`, `lvSpwG LH`): one name, two
  bodies. To be unified on defeq2's convention first.
* Census at landing 3: phase 4 **81 proven / 0 sorry / 11 written / 21 todo** (lane start 65 / 0 /
  0 / 48); phase 5 80 / 19 / 20 / 23 (start 79 / 19 / 20 / 24).

### Landing 5: `find_proj` facts from lane `whnf3`
* `KnotCallees.findProj`/`projFound` removed: `findProj_refines`, `projFound` (program field
  `KnotAllProg.projp : ProjProg p`). `towerSlots` still a field: lane `whnf3`'s
  `towerSlotsAll_refines'` takes all of `CoreCallees` but uses only `findProj` (`tsW_ok`).
* **Bindings for lane `whnf3`'s `instLP` family**: this lane binds `lv_lookup` to
  `lvLookupG EREC POOL` (keys an `EREC` name slice, values a `POOL` level slice: `field_sort_zero`,
  `PropRead`) and `lv_spw` to `PropRead`'s heap variant; one name, one body project-wide, so a
  different instance needs its own name.
* `KnotCallees` left (8, after lane `whnf3` landing 4 gave `towerSlots`): `whnfCoreStep`, `whnfStep`, `proofIrrel`,
  `reduceProjCore`, `unfold`, `constTy`, `instLP`, `den`.

### Landing 4: `tower_slots_all` on the real `find_proj`; the plan for `CoreS.den`
* `tsW_ok`/`towerSlotsAll_refines'` take `FindProjOK`/`ProjFound` instead of all of
  `CoreCallees` (lane defeq2's request); the tagged `towerSlotsAll_refines`
  (`WhnfProjRefine3.lean`) uses `findProj_refines`/`projFound` and is sorry-free given `ProjProg p`.
* **`CoreS.den : StoreDen m a fe`** (lane defeq2's invariant; it closes `CoreS.lvl_den`,
  `LvlsEqDen`, `ProjSortDen`, `FireDen`, `CoreDen`) is not added yet. What it takes:
  memory-only frames keep it when `EREC` is kept (`frameSM`/`frameS`/`frameM`/`frame_stk`: all
  avoid 136); cache-only steps (`setMemo`, the slots' memo writes, `lvl_eq_c`) when `readNC`,
  `pins` and the store are unchanged; store steps (`arena_frame`, `of_walk`, `of_app`, …, about 70
  call sites) need the sort/const views of the new state: for a frame avoiding the `sort` and
  `const` tables (`SOREC`/`SOSLOT`, `CREC`/`CSLOT`, `CTL` 16‥19) with `cpl` kept, the views are
  determined by those arrays under `ArenaR` (`view_sort`/`view_const` and their converse, to be
  written), so `StoreDen` transfers; the interning of a `sort` or `const` node (`of_const`, the
  inference's `Sort`/`imax` results, `nat_op_result`'s `Bool` constants at the pinned empty list)
  needs the new level or list to read back, which the callers know from where it came (a stored
  view, or con-ron's `LStore.intern_spec`/`LsStore.intern_spec` on reading-back children).
* Helper `whnf3-lp`'s `instLP` family (branch `whnf3-next`): the L code and the level-substitution
  proofs (`capsNeverZero`, `substLevelsAt`, `substParamLevels`, `recFireLevels`, `internLevel`, at
  `ArenaD`, on `StoreWF a.store` and the readback caches) keep the keys on the spine stack
  (`lvLookupG SPN POOL`) and the `PropWhen` names in `EREC` (`lvSpwG EREC`), which clash by name
  with lane defeq2's `lv_lookup`/`lv_spw`; they need their own names (and so their own copies of
  `lv_substl`/`lv_substpw`, which call those names) before they can land. D23 (no `lp` cutoff in
  L's derived words) blocks `InstLPOK`: either an `lp` bit in `DerR` or `StoreWF` in `CoreS`.

## The whnf side of the knot finished (2026-10-22, lane `whnf4`)

### Landing 1: helper `whnf3-lp`'s `instLP` family (branch `whnf3-next`)
* The family's level substitution gets its own names (`LevelSubstLP.lean`): `lp_lookup`
  (`lvLookupG SPN POOL`'s body), `lp_substl`, `lp_spw` (names in `EREC`), `lp_substpw`, each
  calling the family's names; the models (`lookupW SPN POOL`, `substLW SPN POOL`,
  `spwW SPN POOL EREC`, `substPWW …`) and their refinements are lane `levels`' generic ones, only
  the four call specs are restated (copies of `LevelSubstL`'s). Lane `defeq2`'s `lv_lookup`/
  `lv_spw` bindings are untouched. Not unified into one parametric function: L calls name their
  callee literally (`call f(…)`), so a parametric body would need a renaming of statements and
  specs proved through it; four 10-line copies are cheaper.
* L code of the walk (`lp_go` and its arms, the three memos, `inst_lp`, `inst_lp_fast`,
  `rec_fire_levels`, `caps_never_zero`) now in `checkerProg` (`Checker/Prog.lean`: 1690
  functions, 9 stubs, was 13); `coreFns` 533 functions (was 498), `checkerProg_coreErec` holds.
  Refinements as landed by the helper: `recFireLevels`, `capsNeverZero`, `substLevelsAt`,
  `substParamLevels`, `internLevel`, `internLsNode` (ArenaD level). Open: the walk itself
  (`InstLPOK`), blocked by D23.

### Helper `whnf4-knot`: `KnotCallees` down to leaves
* **No slot steps in lane `whnf`'s bundles.** `WhnfCallees` lost `inferStep`/`inferIOStep`/
  `defeqStep` (no proof used them); it is now `instList`, `instLP`, `strLitCtor`,
  `strLitSupported`, all built in `DefEqKnot.lean` (`KnotCallees.whnfC`). Narrowed further:
  `constTyAt_refines'`, `ruleRhsAt_refines'`, the `unfoldDefinition_refines'` chain and
  `whnfStep_refines'` take `InstLPOK`; `projLitToCtor_refines'`, `reduceProjCore_refines'`,
  `whnfCoreStepProj_refines'` take the two string-literal facts, `ProjCallees` and `ProjSmall`.
  **`ProjCallees`** (`findProj`, `fireOk`, `erec`, `projFound`; `CoreCallees` extends it) is what
  `major_to_ctor`/`and_rescue_slots` take, so `CoreCallees.iota` (from `iotaRecAt_refines'`, which
  calls `majorToCtor_refines'`) is not circular.
* **Primed `whnf_core` chain** over `(WhnfCallees, CoreCallees, ∀ fe, SupKeep fe)`:
  `whnfApp_refines'`, `coreApp(2)_refines`, `whnfCoreStep_refines'`, `coreLoopW_ok`,
  `whnfCoreLoop_refines'`, `whnfCoreBody_refines'`, `whnfCoreSlot_step`; the tagged statements
  are unchanged and instantiate the stubs. `proofIrrel_refines'` takes `LvlDen` (`CoreS.lvl_den`'s
  statement as a hypothesis; `LvlDen.of_den : CoreDen → LvlDen`); the tagged `proofIrrel_refines`
  still uses the `CoreS.lvl_den` stub.
* **`KnotCallees` fields gone** (now theorems in `DefEqKnot.lean`): `whnfCoreStep`, `whnfStep`,
  `proofIrrel`, `reduceProjCore`, `unfold`, `constTy`. New bundles there: `whnfC`, `projC`,
  `iotaC` (walks `iotaInst1OK`, `lbbOK`, `wscoped_core`, `leafGuard_core`, `findProj_refines`,
  `litToCtorIfNat_refines`), `iota`, `coreC`; `supKeep_of` for `SupKeep`. `KnotAllProg` gains
  `core`, `iotaRec`, `m2c`, `ws`, `lg` (lookups).
* **`KnotCallees` now** (8, all leaves without a proof under `CoreS`): `den`, `instLP`, `fireOk`
  (lane `whnf3`'s `fireOk_refines` gives `FireOkOKD`: needs the universe list to read back and
  `FireDen`'s guards past `numFields`, which `StoreDen.proj` does not give), `projSmall`,
  `capsNeverZero`, `recFireLevels` (proved at `ArenaD` on `StoreWF`, D23), `lvlsEqDen`,
  `recShape`. `knot_all` and the derived fields use only `propext`, `Classical.choice`,
  `Quot.sound`.
* Numbers: 22 files, +323/−172 lines; `DefEqKnot.lean` 313 lines. Rebuild of the touched cone up
  to `DefEqKnot` + `KnotWF`: ~5 min wall, ~12 CPU-min (`WhnfBase` changed, so every whnf/defeq/infer
  module elaborates once); per module: `WhnfDeltaRefine2` 10 s, `WhnfCoreLoop` 8 s,
  `WhnfIotaRefine4` 5 s, `WhnfCoreProj` 4 s, `DefEqKnot` 1.2 s.

### Helper `whnf4-leaves`: `projSmall` and `fireOk` discharged
* **`projSmall` gone, by an L change with no deviation.** `reduce_proj_fire` tested the twin's
  `args.length = numParams + numFields` (`Nat`) as `an == np + nf` (`u64`), equal only if the sum
  does not wrap, hence `ProjSmall` (counts below `2^32`, a loader invariant `CoreS` cannot give: it
  quantified over every record that decodes). It now tests `nf <= an && an - nf == np`, which is
  the `Nat` equation for any words; then `np + i < an` (from `i < nf`), so the argument index does
  not wrap either. `fire_cond_iff`, `rpFire_refines` adjusted; `ProjSmall`, `CoreCallees.projSmall`
  and the `hps` parameters of the `reduce_proj_*` chain removed. `Checker/Prog.lean`/`coreFns`
  unchanged (same names; the body is looked up by name).
* **`fireOk` from `CoreDen`** (`fireOk_core`, `WhnfProjRefine3.lean`; `KnotCallees.fireOk` in
  `DefEqKnot.lean`; new program field `KnotAllProg.fire : FireProg p`). **`FireOkOK` restated**
  with two hypotheses its callers can supply, and `FireDen`'s guard clause narrowed to match:
  - `i.toNat < tbl.numFields`: the twin's `findProj?` only answers an entry below `numFields`
    (`findProj?_lt`), and both callers (`reduce_proj_core`, `and_rescue_slots`) call `fire_ok` on
    `find_proj`'s answer. So `FireDen` no longer asks for the guards past `numFields` (the old
    gap to `StoreDen.proj`): at `i ≥ numFields` the twin would read the `default` level handle,
    which reads back only under con-ron's `StoreWF` (and a non-empty persistent level tier).
  - `us` is a stored `const` node's list (`∃ h c, a₀.store.view h = some (.const c (decI us))`),
    as for `LvlsEqCH`; `StoreDen.constLs` then gives `FireOkOKD`'s readback. `reduce_proj_head`
    has the node (`view_const_words`); `m2c_and` has it from its prefix (`PreRun.cview`), and
    `and_rescue_slots`' loop carries it from slot to slot: neither the twin's `findProj?` (it
    interns names only) nor `fireOk` (it writes the readback and verdict caches only) changes an
    expression node's view (`ProjView.lean`: `findProj?_eview`, `fireOk_store`, and the readers'
    `readLevelM_store` … `lvlEq?_store'`, unconditional). `AndRescueSlotsOK` gained the same
    hypothesis.
  - `ProjSortDen`/`FireDen` are now theorems over `CoreDen` (`projSortDen_of`, `fireDen_of`).
  `InferProj2`'s copy of `findProj?_lt` removed (one lemma, in `ProjView.lean`).
* **Left in `KnotCallees` (6)**: `den`, `instLP` (not this helper's), and:
  - `capsNeverZero`: the twin reads back the inductive's level parameters and the universe
    arguments (`capsNeverZero`), so a provable statement needs both readbacks, as
    `FieldSortZeroOK` has them, plus the `PropWhen` datum's names related by the name store
    (`PWR (nameN ns)`, what `capsNeverZeroW_run` takes) rather than by `dn` (`decPWw`): nothing in
    `CoreS` ties `dn` to `denoteN`. The callers cannot supply the `us` readback: in `iota_case3`
    `us` is the recursor head's list, viewed many core calls earlier, and `CoreAfter` does not
    say that the twin's store only grew (`Ext`), so no view or readback survives those calls.
    Needed: `Ext a a'` in `CoreAfter` (or `CoreS.den` plus `StoreWF`), and `dn` agreeing with
    `denoteN` on the record pool's names.
  - `recFireLevels`: `recFireLevelsW_ok` needs `StoreWF a.store` (it interns the substituted
    levels and the list; `slpW_ok`/`sleW_ok`), which `CoreS` does not carry (D23), plus the same
    readbacks as above.
  - `lvlsEqDen`: its second list `cmpL` is `rec_fire_levels`' freshly interned result; that it
    reads back is again `StoreWF` (the interning keeps readbacks), or a `RecFireLevelsOK` whose
    post says so (a `CoreSpec` post speaks of result words only). The first list `usj` is a
    stored `const` node's (`StoreDen.constLs`).
  - `recShape`: an invariant of the installed environment (`rP ≤ mI + 1`, plain rules'
    `ctorParams ≤ rP`), not of the store: `EnvR` decodes records but bounds nothing. It could
    go by an L change instead: the twin uses `args.take rP` (`recFireArgs_take`), so L could
    clamp the prefix to the spine (`min rP sn`) where it now reads `rP` words of the stack;
    that touches lane `whnf`'s `iota_rec_*` proofs (`WhnfIotaRecRefine2/3`), not done here.
* Numbers: 12 files, +~400/−~95 lines; new `ProjView.lean` 250 lines. After merging master: the touched cone plus `Checker/Prog`, `Checker/CoreErec` 5.2 min wall, 24 CPU-min. Rebuild of the cone
  up to `DefEqKnot` + `KnotWF` after the `WhnfCore.lean` change: 5.2 min wall, 14.8 CPU-min
  (everything downstream of `WhnfCore` elaborates once); `WhnfCoreProj` ~5 s.

### Helper `whnf4-rs`: `recShape` removed by an L change
* **The L change (no deviation; it now matches the twin for any recursor).** The twin reads the
  spine `args` (`mI + 1` words) only through `List.take`/`drop`, which clamp. L read a fixed `rP`
  or `ctorParams` words, which was right only under `RecShape` (`rP ≤ mI + 1`, plain rules'
  `ctorParams ≤ rP`). Now:
  - `inst_spine_pins(po, pl, us, ao, an, rP, pvo, pvc)` takes the spine length `an`, reads
    `min an rP` words and starts the index at `rP - 1` (the twin's `instSpine (args.take rP)
    (rP - 1)`). It refines `instSpinePins lps us args rP` for any `args` (`ispLen`, `ispLen_take`).
  - `rec_fire_args(…, ao, an, rP, ctorParams)`: the nested arm passes `an` on. The plain arm
    returns `(ao, min ctorParams an)`, the twin's `args.take ctorParams` of the whole spine, not of
    its `rP` prefix (that was the second half of `RecShape`). The `ctorParams ≤ rP` hypothesis of
    `recFireArgs_refines'` is gone.
  - `iota_rec_cmp` passes `an = mI + 1` (`EREC[recP + 5] + 1`). `iota_rec_fire2` caps `rP` at `mI + 1`
    before `mk_app_n` (`rpLen`, written as arithmetic, `rP - (rP - mI - 1) * u64(mI < rP)`: an L
    `if` here left `decide` hypotheses that `simp_all` did not use in the spec). `iota_rec_vck`'s index
    slice starts at `so + min rP mI` (`rP - ixLen rP mI`; it was `so + rP`, past the spine when
    `rP > mI`). Its length `ixLen mI rP` was already the twin's `(args.take mI).drop rP`.
* **Proofs.** `SpineR.take` and `instSpinePins_take` moved to `WhnfIotaRefine2.lean`.
  `recFireArgs_take` is no longer used and was deleted. The `rP ≤ sn` and plain-rule hypotheses
  are dropped from `iotaRecCmp/Vck/Fam/Fire2/Fire/Major_refines'`. The pieces get `mI + 1 = sn`,
  which they already had. `RecShape` is gone from `iotaRecC/At_refines'` and from `KnotCallees`,
  which now has 5 fields: `den`, `instLP`, `capsNeverZero`, `recFireLevels`, `lvlsEqDen`.
  `Checker/Prog.lean` is unchanged (same names and the same callees, so `coreFns` is unchanged too).
* Numbers: 8 files, +263/−205 lines. `scripts/lake build ConAgua` after the change took 4.8 min
  wall (the cone from `WhnfIota` up).

### Landing 9: helper `pos2`; vacuous memo hypotheses untagged
* Helper `pos2` (3 h): word models, specs and relational lemmas for the rest of `IndPos2`
  (`nestGrowGroup`, `nestAcceptGroup`, the `nestPos` block `nestFields`/`nestCtors`/`nestFrame`/
  `nestContNew`/`nestContKey`/`nestCont`/`nestPos`, `nestRoot`, `nestSeeds`; L: `nest_root`,
  `nest_seeds` to self-recursion, `nest_seeds_fuel` split out and added to `checkerProg`).
* **Finding (lead's review): a family of vacuous hypotheses.** Its census theorems take
  `PosMemo dn vis fe`, which says *every* memory in the stage relation carries well-formed memos
  (`∀ m a, StageR dn vis fe m a → ∃ mp, noMR m mp`, likewise `dp`, `hb`, `rp`, `RfInv`). `StageR`
  says nothing about arrays 201‥208, so this is false (a memory with garbage in a memo array is
  still in `StageR`), and a theorem assuming it proves nothing. Helper `pos`'s landing-4 theorems
  had the same pattern (`hMstage`, `hMra`, `hMno`): `nestCanonCrest`, `nestRootCanon`,
  `nestUniformOk`, `nestUniform`, `nestInstType`, `nestGrowGroup`, `nestCrest`, `nestSeedOf`.
  **All of them are untagged** (kept as lemmas, with a comment; the census shows them `written`),
  25 tags in all. The fix is to thread the memo relation of the *current* memory through the posts
  (as `hasLooseBVarBGo_refines` and the `mentionsAnyGo` walks do: the memo relation in the pre,
  `∃ mp', …MR m' mp'` in the post, `stubM_memoFrame` across stubs) instead of quantifying over all
  stage states; or to add "the memos are well formed" (a memory-only `∃ mp` form, plus a weak
  form that holds for zeroed memory and gives `MemoRV` after a clear) to `StageR` and `LoopR`.
* Census (master `e49af3c`+ this lane): phase 8 **73 proven, 72 sorry, 70 written, 8 todo**
  (the untagging moved ~8 targets from `sorry` back to `written`); totals 703 proven / 116 sorry.
### What discharging `CvCanonSpec`/`CiCanonSpec` needs (lane `decls3`, open)

Canon's theorems (`cvCanonEq_refines`, `ciCanonEq_refines`) take, beyond `StageR` and the records'
decodings, `PoolSmall m` and `LitInj a`. `PoolSmall` follows from `StageR` (`LitR`'s `PoolOK`:
the pool is below `2^63`), and decoding in `erA m` transfers to `erecP m` (`ArrExt.decCV`/`decCI`
with `erecP_ext`). **`LitInj a` does not follow from `StageR`**: it is con-ron's
`EWFAt.view_inj` (the twin store's cons maps are consistent and the tiers fresh), i.e. a
consequence of `StateOK a`. So the arms need `StateOK` at the comparison: carried by `LoopR` (the
twin's `FoldOK` has it) and kept across the arms' earlier callees (`find_pinned`'s reads keep the
state; `rom_ci`'s interns need con-ron's `intern*` well-formedness lemmas, or a `StateOK` clause in
the ROM stubs' `KeepPost`). This is the same gap as `lvlEqStub_spec`'s `TwinOK`: the stage
relation should carry the twin's well-formedness (`StateOK`, which gives `NStoreWF` too).

### Landing 9 (lane `decls3`): `all_level_params_defined` refines the twin (helper `decls3-apd`)

`DeclApdSpec.lean` (word models, `vcgen` specs), `DeclApdRef.lean` (relational):
`allLevelParamsDefined_refines` (`@[refines]`, `RefAM … (KeepPost dn vis fe decW0B)`, through
`ApdProg p`) and `alpdGo_refines` (twin fuel `f.toNat`), sorry-free. Extra premises the stub
spec does not have, which the callers (`DeclCvg`, `DeclHeader`, `DeclReduceSpec`, `RecGenSpec3/4`)
must supply before the `stubM "all_level_params_defined"` uses can go: `ApdEnv a`
(`NStoreWF` and `StoreDen`'s level fields — again the twin's well-formedness the stage relation
lacks, as for `LitInj`/`TwinOK`), the parameter names read back, and some memo in `APDM` on
entry. The memo-hit bug (the probe depth returned as the value) was found by this spec.

### Landing 10: helper `rec3`
* Helper `rec3` (73 min): sorry-free `targetAbsGo`/`targetAbs` (the `ta` memo of the current
  memory threaded through pre and post), `classFeR`, `ClassRead.classes`; through stubs
  `classRulesOk`, `classRecsRulesOk`, `auxRuleFire` (with `PoolSmall`, lane decls3's), and
  `classStreamRecs`. The hypotheses `RecsOK` (class_stream_recs) and `SlotsExt`
  (class_read_classes) are now derived from `DecB` inputs plus the caller's slice bound
  (`rec3RecsOK_of_decB`, `rec3SlotsExt_of_decB`); `CVExt`/`CKExt` accept an empty slice at any
  offset (and `decCV_copy`/`cvNew_stage`/`decCVp_grow`'s matching hypothesis likewise). L: loops
  to self-recursion, `target_abs_node`'s arms inlined, a capacity abort on `nP + |slots| + nF`, a
  name-handle guard in `class_fe_r_rec`; D18 extended. ~2.6k proof lines for ~170 L lines.
* Census: phase 8 **78 proven, 75 sorry, 64 written, 6 todo**; totals 718 proven / 119 sorry.

### Landing 10 (lane `decls3`): the definition arm through its gates

* **L**: `check_decl_defn` now calls two gate functions, `defn_nat_gate(vis, w, n)` (the
  structural-`Nat` gate, `checkDecl`'s lines 104-119) and `defn_div_gate(vis, w, n)` (the
  `Nat.div`-family pin gate, lines 123-124); the code is unchanged, only split.
* **Twin**: `natGateT`, `divGateT` (`DeclArmDefn.lean`) and `checkDecl_defn_eq`: the arm is
  `checkConstantVal; let fe2 ← checkDefnVal; natGateT; divGateT; pure fe2` (the twin's `do` join
  points distributed: `bind_assoc`, case splits, `fail_bindAM`).
* **Proof**: `cdfW_ok`/`checkDeclDefn_loop'` at the loop's relation through `DefnProg p pins`:
  `NatGateSpec`, `DivGateSpec` (`RefAM` of the gate against the twin fragment, pre `StageR ∧
  PinSetsR m pins`, post `KeepPost ∧ PinSetsR ∧ MemFrame stepA stepC`), for helpers
  `decls3-nat`/`decls3-divmod`. `PinSetsR.grow`/`.step`: the variant list survives the step
  (`stepC` now excludes `CTL[150]`, `CTL[151]`; every closed text still checks).
* **Open**: `checkDeclDefn_loop` stays `sorry` until the loop's relation carries the variant list
  (`PinSetsR m pins`: `LoopR` gains `pins`, or the chain `CheckDeclSpec` → `installStepGo_spec`
  → `Checker.lean` threads it) and the two gate specs are proved.
### Helper `whnf4-d23`: the level-parameter bit mirrored (deviation D23 fixed)

The twin's derived records carry a level-parameter bit (`lpOfData` of the expression word,
`LDer.hasParam` of levels and level lists), and `instLPGo`/`instLPFast` cut off on it before any
readback. L now keeps the same bit for every node, **stored when the node is pushed** (the twin
computes `derOfView` before `Tbl.push`), so it is the twin's stored bit even for a node whose
child dangled when it was interned (no `StoreWF` needed).

* **Layout** (`LpCol.lean`). Compound tables: bit 30 of the existing `XDER` words 42‥46
  (`packBFL b f l = packBF b f + l * 2^30`; `der_f` now masks `(x >> 15) & 32767`), written by
  `mk_*` as the `or` of the children's bits. Seven new word arrays, one word per node at
  `2 i + t` like the records: 55 `SHP` (`succ`), 56 `MHP` (`max`), 57 `IHP` (`imax`), 58 `LSHP`
  (level lists), 59 `SOLP` (`sort`), 60 `CLP` (`const`), 61 `FVLP` (`fvar`), written by the
  table's own `*_push` from the children's bits read on the memory before the push (a named block
  spliced into the push: `hpBlkS`, `hpBlkM1/2`, `lsBlkC`, `lpBlkF`, the loop `hpLoopLs`, each with
  its spec; push specs stay one `vcgen`). `zero`, `param`, `bvar`, `lit` have constant bits and
  no column. The pushes check `c < len(COL) >> 1` with the other room checks (fixed capacity).
  No `CTL` word was added. Record syntax (lane `lfeat`) was not used: the column index `2 i + t`
  has the tier as a run-time offset, and `R[i].f` needs a constant field; the columns are
  addressed exactly as the record arrays of the same tables.
* **Read models.** `lvlHPW m u` (level handle), `lsHPW m us` (level list), `lsOrW m o k` (the
  `or` over a pool slice, `ls_push`'s loop), `exprLPW m h` (expression; `der_b`'s new third
  result): tier check, tag, count check, then the column (`0` for a handle that does not view,
  the twin's `default`).
* **Models of the interning.** `xinternW` keeps its name and spec; `xinternW_eq` now says
  `internMD` (`internM` plus the column write, `LpColRel.lean`), `xinternW_eqK` (given the count
  words, i.e. `StoreR`) says `mkK COL … (internM …)`, `xinternW_frame` is the frame
  `MemFrame [REC, SLOT, COL] [ca, ca+1]`. The `x*_correct` lemmas kept their statements
  (proved through `mkK_split` and the store frame); new `x*_hp`/`x*_lp` lemmas carry the column
  across the interning (`colMk`, the `derMk` of any lens), from a hypothesis `hb` that the bit
  written is the twin's.
* **Relation.** Nine new `ArenaR` fields (`ArenaRel.lean`): `zeroHp`, `paramHp`
  (`ConstT2`: `hpW = 0`/`1` on every node), `succHp`, `maxHp`, `imaxHp`, `lsHp` (`ColT2 … hpW`),
  `sortLp`, `constLp`, `fvarLp` (`ColT2 … lpW`); `ColT2 L A f m a`: as many derived records as
  nodes, and `A[2 i + t] = f (derAt i)`. The columns are in `storeArrs`, so `ArenaR.frame` covers
  them; `arena_build` frames them by `ColT2.frameAp`. `lift_x` takes `XR m' a' ∧ col m' a'`.
  `DerR`: `bvP` and the new `zlP` (`lit`) add `lpOfData d = false`, `cP` packs the bit
  (`packBFL … (lpW d)`). `DerRel.lean` was split (`DerRelBase.lean`: the relation and the reads;
  names unchanged).
* **The interface** (`DerRelBase.lean`):
  `theorem derLW_ok (m : Mem) (a : AState) (hR : ArenaR m a) (hD : DerR m a) (h : Word)
  (hh : h.toNat < 2 ^ 32) : exprLPW m h = lpW (a.store.derived (decE h))`, with
  `lpW d = b2w (lpOfData d)` (`1`/`0`) and `derB_spec`'s post
  `r.tail.tail.headD 0 = exprLPW s₀.mem h`. Level side (`ArenaRel.lean`): `lvlHPW_ok`,
  `lsHPW_ok`, `lsOrW_ok`, `lvlHPW_or`.
* **The cut-off** (`InstLP.lean`): `lp_go` calls `der_b(h)` after the fuel test and returns `h`
  when the bit is `0` (`instLPGo_succ`'s `if !(lpOfData der) then pure h`); `inst_lp_core`
  calls `der_b(e)` first and returns `e & 0xffffffff` before `ls_node(us)` and the memo clears
  (`instLPFast`). The walk's refinement (`InstLPOK`) is not part of this helper.
* **Ripple.** 72 files vs master (+2862 / −1040 lines, most of it the new files and the
  per-table column lemmas). Site changes were mechanical: frames gained the column (`lvArrs`,
  `lArrs`, `lsArrs`, `eArrs`, `rflArrs`, `natA`, the `MemFrame [CREC, CSLOT, CLP]` of
  `intern_const`), `b < 42` level/ls frame conditions became `b < 42 ∨ (54 < b ∧ b < 64)`
  (`stage_of_level`, `CoreS.of_level`, `CoreS.of_ls`), `vg_arrs`/`pnew_arrs`/`LoopR.of_frame`
  allow 55‥63, `pi_lens` takes `b < 42 ∨ 46 < b`, five anonymous `ArenaR` constructors gained the
  fields, test memories and the emitted benches have 62 word arrays (`WalkBench`, `*Emit`).
  Moved, not duplicated: `cnt_tier`, `idxW_hdW`, `derPutW_frame`, `ix_ne`, `cnt2_eq` (to
  `LpColRel.lean`), `decI_tag`/`decI_idx`/`decI_tag_eq` (from `PromoteNRef.lean`), `sliceL_succ`
  (to `LitRefine.lean`), `tierW_le` (to `LpCol.lean`), `mkK`/`derPutW`/`cnt2` and the five
  `XDER` ids (to `LpCol.lean`), the seven `*Local` lemmas (to their `*Refine.lean`).
  `DefEqMidLams.lean`'s local `lpW` was renamed `lpeelW` (name clash).
* **Numbers.** New: `LpCol.lean` 427 lines (L: six blocks, 60 L lines; models, block specs,
  `packBFL` lemmas), `LpColRel.lean` 677 (generic column relation, `internMD`, `colMk`).
  L changed: the seven pushes (+1 block call, +1 room check, +1 store each), `der_b` (+2 arms,
  third result), `mk_*` (+1 result, `lp` term), `lp_go`/`inst_lp_core` (+2 lines each).
  `lake env lean` wall times: `LpCol` 15.9 s (`lpBlkF_spec` needs `maxHeartbeats 1000000`),
  `ExprMk` 19.9 s (`derB_spec` the same), `LpColRel` 1.2 s, `DerRelBase` 0.8 s, `ArenaRel`
  4.9 s, `SortStore` 5.4 s, `LsStore` 3.4 s. `Checker/Prog.lean` regenerated (unchanged: 1692
  functions, 9 stubs), `coreFns` 533. No new `sorry`, no axiom.
* **Left.** `InstLPOK` (the walk's refinement) on `derLW_ok`; the e2e harness needs no change
  (all word arrays are allocated alike).


### Landing 11: helper `posmemo` — the positivity theorems honest again
* `IndPosMemo.lean`: `PosMR m` (the five walk memos — `nest_occ`, `depth`, `replace_apps`,
  `has_loose_bvar_b`, the banked `replace_fvars` (`RfInv`) — well formed in *this* memory),
  `MFr S T m m'` (a frame writing only memo arrays `S`, control words `T`), `PosMR.fr` (across any
  writer that leaves the memos alone: stubs via `stubM_memoFrame`, interns, IW/EREC records),
  `PosMR.setNo/Dp/Rp/Hb/Rf/Cr` (across a walk: its own post plus its frame for the others).
  The 22 tags removed in landing 9 are restored: every theorem now takes `PosMR s₀.mem` (or the one
  memo relation it needs) and returns `PosMR s'.mem`; `PosMemo`/`hMstage`/`hMra`/`hMno` are gone.
  Frames for ~40 word models by a small tactic macro `mfr_auto` (a departure from PLAN's "no
  custom tactics", as `Keeps.lean`'s `prim_keeps` is; it only sequences `MemFrame` lemmas). No L
  changes. ~1.5k lines, 65 min.
* Census: phase 8 **78 proven, 92 sorry, 47 written, 6 todo** (the re-tagged theorems go through
  stubs); totals 718 proven / 136 sorry.

### Landing 6: `CoreS.den` (coordinator's request after lane `whnf3`)
* **`CoreS` carries `den : StoreDen m a fe`** (`WhnfBase.lean`). `StoreDen` grew to: sort levels,
  const level lists, the zero and empty-list pins, the `readNC` rows, a constant's level-parameter
  names (`constLps`), projection tables' levels (`proj`), and **`lvlAll`: every level handle with
  a view reads back** (a cons hit of a level interning returns an old handle; without `lvlAll` its
  readback would need a rank argument).
* **How it is kept** (all construction sites, ~25 explicit, ~35 lemmas): memory-only frames and
  cache writes by `StoreDen.frameE`/`caches` (`EREC` kept, the store unchanged); interning a node
  that is neither `sort` nor `const` by `StoreDen.of_arena` — the `sort`/`const` tables are
  determined by their memory under `ArenaR` (`scTabs_eq`), so a writer that avoids `SOREC`/`CREC`
  and `CTL` 1, 16‥19 (`arena_frame`'s new auto-params) keeps their views — or, from the twin run,
  by `internNodeE_sc`/`internE_pure_views` (a push adds only a view of the pushed kind); interning
  a `sort u`/`const c us` by `StoreDen.of_internSort`/`of_internConst` given `u`/`us` reads back
  (`CoreS.arena_frameD`, `of_const` now take the run and that readback); level interning by
  `lvlAll_internLNode` (helper `defeq2-lvl`, `StoreDenLvl.lean`: under `ArenaR`, a hit's handle has
  the probed view, a push's readback is its children's at the old fuel); name and list interning
  by `LsExt` (`NameStep.son`, `LsStep.son`, `lsExt_of_tables`); `nat_op_result`'s leaves by a third
  clause of `LeafStep` (new `sort`/`const` views are `const c emptyLevels` only).
* **Readbacks across knot calls.** `CoreAfter` says nothing about the twin's store growing, so a
  level read before a knot call (the domain sort of a `∀`, the binder sorts on `BSTK`) is not known
  to read back at the `imax` after it. L now checks with `lv_node` that both `imax` arguments (and
  the codomain sort) are stored levels (`lvl_live`, `Infer.lean`; deviation D25), and `lvlAll`
  gives their readbacks (`lvlLive_call`; `lview_of_lvNodeW` moved from `DeclCanonView` to
  `LevelView.lean`). The `M2C` arms carry the type head's list as a view (forward-view lemmas:
  `internNodeE_fwd`, `etaFabArgsE_fwd`, `view_after_noLss` for `towerSlotsAll`, `andRescueSlots`,
  `capsNeverZeroPW`).
* **Discharged**: `CoreS.lvl_den` (was a `sorry`), `CoreDen` (`coreDen_of`), `ProjSortDen`
  (`projSortDen_of`), `ProofIrrelOK` (`proofIrrelOK_of` now sorry-free); `KnotCallees.den` and
  `.proofIrrel` removed. Still open for lane `whnf4`: `FireDen` quantifies over every field index
  (`StoreDen.proj` gives `i < numFields`), `LvlsEqDen` (from `StoreDen.constLs` at its callers).
* For other lanes building `CoreS` from outside the core: `TwinOK` (`DeclLvlStage.lean`) gained
  `den` and the `fe` parameter.
### Landing 11 (lane `decls3`): the loop's relation carries the pin variants

* **`LoopR pins dn m a vis fe pend ds`** (new first parameter) has a field `pinsets : PinSetsR m pins`
  (lane `romload`'s relation of the variant records at `CTL[150]`/`CTL[151]`). Every step keeps it
  (`DeclPins.lean`: `RecGrow` — the record pool only grew — from `IWGrow`, from `ArrExt` of
  `erecP` at an in-bounds top, or from an unchanged `EREC`; `stepC` excludes `CTL[150..151]`); the
  promotion and the bracket's frames show it directly. The theorems of the loop now take `pins`
  where they mention `LoopR` (mechanical; `FoldOut`, `IstgPost`, `PendPost`, `CPGoSpec`,
  `CPNextSpec` gained the argument).
* **`checkDeclDefn_loop` is proved** from `checkDeclDefn_loop'` and `CheckDeclProg.defn : ∀ pins,
  DefnProg p pins` (the two gates' specs). `checkDecl_loop` has no `sorry` of its own now; it rests
  on `CheckDeclProg`'s spec fields (`CvCanonSpec`, `CiCanonSpec`, `DefnProg`) and the callees' stub
  specs. Whoever establishes `LoopR` at the loop's entry (the pipeline) supplies `PinSetsR` from
  `internAllPins_PB`'s post.


### Landing 7: the level tables only grow (`LvlCnt` in `PoolGrew`); D25 fixed
* **`PoolGrew` gained `lvl : LvlCnt m m'`** (`WhnfBase.lean`): the scratch flag `CTL[1]` is kept
  and the level tables' counts (`CTL` 6‥15) do not drop. Being a field of `PoolGrew`, it rides on
  every `StackKept`/`StackGrew`/`TelPost`/`CoreAfter` lane `whnf3` already threads; the only new
  obligations are at writers of those words: frames get it by an auto-param `LvlFree C`
  (`lvl_free`, `LvlFree.of_ge` for generic frames above 16); a level interning
  (`CoreS.of_level`, now taking `hlc`) by `lvlCnt_of_arena` (`LvlGrow.lean`: the counts are the
  twin tables' sizes under `ArenaR`, and `LStore.intern` only pushes, `LTGrow.internLNode`).
* **Why a memory fact suffices.** A level stays stored: `lv_node` accepts it after a run if it did
  before (`lvNodeW_mono`), so `lview_of_lvNodeW` and `StoreDen.lvlAll` read it back at the later
  state (`lvl_den_later`, `lvNodeW_of_den`). The twin side needs no `Ext` in `CoreAfter`.
* **D25 fixed**: `lvl_live` is gone; `infer_forall_io` carries the domain sort across its four calls
  (`lvl_den_later`), `infer_pis`'s loop carries "every binder sort on `BSTK` is stored"
  (`lvNodeW m ws[i] ≠ []`, a new hypothesis of `pisFull_ref`/`inferPisLeaf_refines`/
  `pisOut_ref`), and `ensure_sort`'s answer is a stored sort's level (`ensureSort_view`).

### Landing 12: helper `sum` — `IndSum` complete
* Helper `sum` (2 h): `sumRules`, `checkStructFieldSortsI`, `checkSumCtor` (precondition: the
  pre-block environment is `fe.restrictTo vis0`), `checkSumCtors`, `checkStructProjTable` (with
  its `_scoped` helper and `er_from_iw`; lane decls2's `env_find`/`env_push`), all through stubs.
  New stub contract `lvLeqTopStub_spec` (`lv_leq_top`: `Level.leq` on the readbacks, `sorry`, like
  `lvl_eq_c`'s; the real one needs the `CoreS` bridge of landing 1). Program bundles `SumProg`,
  `TblProg`. L: four loops to self-recursion, `check_field_sort_bound` split off, a handle guard
  after `intern_const`, D18 extended to `check_sum_ctors`. ~2.9k proof lines for ~205 L lines
  (**~14 per L line**, down from ~19, with `Sim`, `DecB`, program bundles).
* Census: phase 8 **78 proven, 97 sorry, 42 written, 6 todo**; totals 719 proven / 140 sorry.

### Landing 8: level lists too (`StoreDen.lsAll`, list counts in `LvlCnt`)
* **`StoreDen.lsAll : LsAll a`**: every valid level-list handle reads back (the list twin of
  `lvlAll`); `StoreDen.mono` takes it as its last argument. Kept by name/level steps (`LsAll.congr`,
  `LsAll.of_ext`) and by list interning (`lsAll_internLsNode`: given the elements read back, the
  new store has `LsAll` and the new handle reads back).
* **`LvlCnt` covers the list table counts** (`CTL` 40, 41; `lvlCtlW`), so `LvlFree.of_ge` now needs
  `42 ≤ x`. A list interning gets it from `lvlCnt_internLsNode` (`LsTables` only push); `CoreS.of_ls`
  takes `hlsa`/`hlc` and uses `StackKept.of_frameL`; `ls1_call` now needs its element to read back.
* **Why**: a list stays stored after a run (`lsNodeW_mono`), so `ls_den_later`/`lsNodeW_of_den`
  read it back later — what whnf4's `instLP`/`LvlsEqDen` need for constants' level lists.

### Landing 9 (defeq2): `KnotCallees.lvlsEqDen` gone
* `LvlsEqDen` (a successful `lvls_eq_c` compares lists that read back) was stronger than needed and
  not provable on a memo hit. Instead `lvlsEqC_refines` no longer asks its lists to read back: on a
  hit the twin reads nothing; on a miss `ls_node` read both handles, so they are stored
  (`lsNodeW_view`, moved to `LevelArena.lean`) and read back by `StoreDen.lsAll`.
* Model fix: `lvlsEqW` is `none` when a handle's `lsNodeW` is `[]` (`ls_node` aborts there; the
  model used to compare an empty slice).
* `LvlsEqDen` and its `hden` threading through `WhnfIotaRecRefine*` are removed; `iotaRecAt_refines`
  and `LvlsEqCH`'s callers drop the readback hypotheses' use. `KnotCallees` has 3 fields left.
### Landing 12 (lane `decls3`): helpers `nat` and `divmod`, the definition arm's gates

* **Structural-`Nat` gate** (helper `decls3-nat`, `DeclNat*.lean`, ~8 h): `natOpNames`,
  `natDivModNames`, `natOpDeps(Stored)`, `natLitSupported`, `natOpGuard`, `boolCtorOk`, `natOpCod`,
  `natOpTyPinned`, `natOpStoredOk(All)`, `natAp1/2`, the per-operation equation builders,
  `natOpEquations`, `substConst0(Pairs)`, `certifyNatEqs`; `natGateSpec : NatGateSpec p pins` from
  `NatSubProg' p`, the gate's lookups and its text's agreement with `armText` (`natGateFns`,
  closed by `decide`). L split for tractable `vcgen` (unrolled name loops, `nat_op_pins*`,
  `nat_op_bool_ctors`, `nat_eq_*`, `defn_nat_cert`).
* **`Nat.div`-family pin gate** (helper `decls3-divmod`, `DeclDivMod*.lean`, ~3.5 h): every
  function from `div_mod_slot` to `check_div_mod_pin_at` `@[refines]`; `check_div_mod_pin_loop`,
  `check_div_mod_pin` `refines_part … (D4)` (a returning L loop is a twin run without recovery);
  `romPinSets_ref` (`PinSetsR` → the `IW` list); `divGateSpecD`. `DivGateSpec` now takes `DnInj
  dn` (`div_mod_env_guard`'s `find_is`). L: `cert_ctx` split, `rec2`/`rec3` slices.
* **`checkDeclDefn_loop`** composes them: `CheckDeclProg` gained the gates' program facts
  (`natSub`, `natGate`, `natCert`, `natText`, `dm`, `dgClosed`) and two walk specs still open as
  fields: `subst0` (now discharged: `substC0_of`, from `DeclNatSub`.s `sc0_ref`) and
  `substAll` (`SubstCAll`, `subst_const_all`, not yet proved).
* Clashes on merging (helpers vs canon vs master): renamed on the helpers' side (`nt*`, `dm*`,
  `CertCtxR`); `DeclNatBase`'s interning lemmas ported to master's `*_eqK`/`mkK_split` pushes.
* Census: phase 2 **206 proven, 50 sorry, 35 written, 40 todo** (the `sorry` count includes
  functions now proved through upstream stub specs: `isDefEqCore_spec`, `stubM_spec`, the ROM
  readers).


### Landing 10 (defeq2): `KnotCallees.capsNeverZero` discharged (`capsNeverZeroOK_of`)
* **`StoreDen dn m a fe`** takes the record decoder `dn` and gains `dnN`: `dn` agrees with the
  name store (`dn` is the store's `denoteN` at the declaration's start, and names only grow, so
  `mono` keeps it). It relates an inductive's `PropWhen` datum (`decPWw`, through `dn`) to the
  twin's readbacks (`PWR (nameN ns)`, `pwR_of_decPWw`). `TwinOK` (`DeclLvlStage.lean`) takes `dn` too.
* The universe arguments need no readback hypothesis: `caps_never_zero` calls `ls_node(us)`, which
  aborts on a handle not stored (model fix: `capsNeverZeroW` is `none` there), so `StoreDen.lsAll`
  reads the list back. The level parameters do: `CapsNeverZeroOK` now asks them to read back, and
  its callers (`iccW_ok`, `m2cEta_ok`, `m2cArms_ok`, now taking the family's `fe.find?`) get
  them from `StoreDen.constLps`.
* `CapsNeverZeroCore.lean`: `CoreS.frame_lhs` (a writer of `LH`/`SPN` keeps `CoreS`),
  `StackKept.of_lhsFrame`, and the proof. `KnotAllProg` gained `caps : LvSubProg p`;
  `KnotCallees` has 2 fields left (`instLP`, `recFireLevels`, both whnf4's).

### Landing 6: helper `whnf4-ilp`'s level arms (for lane `defeq2`'s `recFireLevels`)
* `InstLPWalk`, `InstLPWalkBase`, `InstLPWalkGo`, `InstLPWalkArms` (the walk's models and specs,
  no refinement yet) and `InstLPLevel`, `InstLPLevel2` (under `CoreS`: `lvInternW_core`,
  `lvSubIntW_core` with `SubOut`/`ILWEnv`, `slsElemW_core`, `spnLs_core`) from the helper's
  commit `8c21b5d`, adapted to master's `LvlCnt` (list counts) and `CoreS.of_ls`'s `hlsa`/`hlc`.
  The WIP `InstLPWalkLet` is not landed. No L change. Globals rule: the instLP family uses only
  existing slots (`CTL[136]` spine top, `CTL[192]` level-heap top, MemoLib schemas `CTL[54‥59]`).
### Helper `whnf4-ilp`: `InstLPOK` proved, `KnotCallees` gone
* **Theorem.** `instLP_refines (p) (hp : ILWEntryProg p) : InstLPOK p` (`InstLPEntry.lean`,
  `@[refines ConRon.Arena.instLPFast]`), sorry-free, on nothing but `CoreS`. `KnotCallees` is
  removed: `KnotAllProg` gains `ilw : ILWEntryProg p`, `KnotAllProg.instLP := instLP_refines p
  hq.ilw`, the bundle theorems are renamed `KnotCallees.*` → `KnotAllProg.*` (`infer` → `inferC`:
  a field of that name exists). The knot (`knot_all`) now takes only `KnotAllProg p`.
* **No `StoreWF`, no readback hypothesis.** The level arms (helper `whnf4-ilp-lev`,
  `InstLPLevel*.lean`) re-prove `lv_intern`/`lv_sub_int` under `CoreS` by the node-by-node
  induction, keeping `LvlStep`/`StoreDen.lvlAll` (`lvlAll_internLNode`) instead of con-ron's
  `internLevel_spec`. The universe arguments read back by `StoreDen.lsAll` (`ls_node(us)` aborts on
  a handle not stored; the model now says so). The keys: a new L function **`keys_ok(o, l)`**
  checks each key word on the spine stack to be a stored name handle (tag, scratch tier, count);
  under `ArenaR` such a handle views (`viewN_anon/str/num`), under `CoreS.nwf` it reads back
  (con-ron's `denoteN_of_view`) — `keysOkW_names`. It runs past the cut-off (where the twin's
  `readNamesM` runs) and aborts exactly where `readNamesM` fails (a cached name reads back by
  `StoreDen.readN`, so a cache hit is a stored name): no deviation.
* **Other L changes (no deviation; same values).** `lp_go`'s `const` arm reads the name word before
  `sls_memo` (the twin has it from the view; no frame of `sls_memo` over `CREC` needed).
  `lp_let`'s third child and rebuild moved to **`lp_let_tail`**, its rebuild to **`lp_rb_let`**
  (helper `whnf4-ilp-let`: `finish` on the 3-child body needed `(instances := 5000)` even then).
  `Checker/Prog.lean` regenerated (1720 functions, 9 stubs), `coreFns` 536.
* **The walk memos in `CoreMemos`.** `inst_lp_core` clears arrays 52‥54 by an epoch bump, sound only
  on a well-formed memo: `WalkMemos` gains a fourth conjunct `LPMemos` (`WhnfBase.lean`, with
  `coreLpSch`/`coreLplSch`/`coreLplsSch`, `ilKey`, `VI` moved there); `WalkMemos.frame`/
  `CoreMemos.frame` gain auto-params `hLA`/`hLC` (`decide` on concrete write sets; the abstract
  ones in `CoreS.of_level`, `CoreS.of_ls`, `WhnfProjRefine`, `CoreS.arena_frame(D)`,
  `CoreS.arenaFrame` pass them), `CoreMemos.frameLP` for the walk's own memo writes;
  projections `.2.2.2.2` → `.2.2.2.2.1` in `WalkCore.lean`, `RecFireCore.lean` (`CoreS.ctl136`).
* **Proof structure.** Models with every callee through `callW` (`InstLPWalk.lean`: one `vcgen`
  per function; `lp_go`'s dispatch by guarded equations `ilwDispW_*`; specs split into
  `InstLPWalkGo`/`Arms`/`Let` for build parallelism). The walk's invariants (`InstLPWalkBase`):
  `ILWMemo` (the three memos hold the twin's maps, level values read back), `ILWEnv` (keys on the
  stack below its top, values a pool slice below its top), `ILWGrow`; `ILWStep T a … r` (the twin's
  run, `CoreAfter`, the invariants) with `ILWStep.bind`, `ilw_arm` (probe + write around a body),
  `ilw_rebuild` (`internRebuilt*`); `ilwGo_ok` (`@[refines instLPGo]`) by induction on the L fuel
  over all smaller fuels (`ilwGo_succ`); the entry `ilwCore_ok` (cut-off, `ls_node`, `keys_ok`, the
  clears `ilw_clears`, the walk, the clears); `inst_lp` (`ekCopyW_slice`: the record-pool slice
  lands on the stack; the top put back).
* **Also.** `RecFireEnv.lean`'s `decRule_fire` renamed `decRule_fireE` (clashed with
  `PromoteCIRef2`'s at `checker_prog.py`'s import check).
* **Numbers.** New: `InstLPWalk` 641 lines, `InstLPWalkBase` 317, `InstLPWalkStep` 139,
  `InstLPWalkRef` 182, `InstLPWalkRef2` 274, `InstLPWalkRef3` 342, `InstLPKeys` 170,
  `InstLPEntry` 387, `InstLPWalkGo`/`Arms`/`Let` 39/60/38, `InstLPLevel`/`2` 421/316 (helper);
  ~3300 lines. Elaboration: `InstLPWalkGo` 52 s, `InstLPWalkArms` 14 s, `InstLPWalkLet` ~6 s, the
  rest ~1 s each. Rebuild after the `WhnfBase` change: ~10 min wall (`DefEqKnot` cone); full
  `scripts/lake build ConAgua` ~20 min wall.

## Phase 2, round 5: the twin's well-formedness, the real ROM readers (2026-10-22, lane `decls4`)

### Landing 1: `StateOK` from the twin's fold; canon in the arms; the ROM readers as callees; `subst_const_all`

* **The twin's store well-formedness, without touching `StageR`.** Canon's comparisons
  (`cvCanonEq_refines`, `ciCanonEq_refines`, `canonEqList_refines`) compare literal handles where the
  twin compares values; that needs `LitInj a`, a fact about the twin state alone (con-ron's
  `EWFAt.view_inj` under `StateOK`). No memory relation can give it, and `StageR` relates memories to
  states without saying anything about the state's own invariants. So it is carried on the twin
  side: **`TwinFold pins ds fe pend a`** (`DeclTwin.lean`) is con-ron's `installFold_bridge`
  induction invariant (`FoldOK` at some `env` with unique names, the pins and the records denote, the
  pin sets, records and pending groups persistent), and **`TwinFold.step`** is that induction's step
  (`installStep_split`, `andPinOk_run`, `checkDecl_nodup`/`SplitInstall.nodup`, all con-ron's),
  applied to the twin run each L step refines. Pure twin reasoning, ~150 lines.
  - Threading: `FoldGoSpec`/`FoldNextSpec`/`installThenCheck_refines` take `TwinFold` (the pipeline
    supplies it from `stages_frame`: `FoldOK` at the start, `NodupNames Env.empty`, `PinsDenote`,
    `PersPinSets`, `PersDecl`, `denoteDecls`); `installDeclStep_refines` takes `TwinFold` and passes
    `StateOK` of the state after `andPinOk` (`TwinFold.andPinAM`); `installStep_*` and
    `installStepGo_spec` take `StateOK` and pass it through the bracket's opening
    (`TwinFold.enterAM`: `EStore.enableScratch_wf`); `CheckDeclSpec` and `ArmSpec` take `StateOK a₀`.
    `LoopR` is unchanged.
  - In the arms: after the ROM read `BasisKind.decls_run` (con-ron) keeps `StateOK`, after
    `ci_to_cv` our `toConstantVal_stateOK` (the `.projInfo` arm's three interns), and
    `StateOK.view_inj` gives `LitInj`; `PoolSmall` from `StageR` (`poolSmall_of_stage`).
  - **Discharged**: `CvCanonSpec` (quotient arm) and `CiCanonSpec` (axiom arm, `Quot.sound`) are
    gone; the arms use canon's theorems directly.
  - **Not discharged: `lvlEqStub_spec`'s gap** (`TwinOK` at `lvl_eq_c`'s callers). Its callers
    (`DeclCvg`, lane `induct`'s files) call `lvl_eq_c` after core stubs (`infer_type_core`,
    `ensure_sort_core`), whose posts are `KeepPost`: `TwinOK`'s caches (`ReadLCOK`, `ReadLsCOK`),
    `CoreMemos` and `StoreDen` at the state after a core call are not derivable from the twin's fold
    (they are `CoreS` facts). They come with the knot: when the core's stub specs become the real
    `CoreS`-carrying ones (lanes `defeq2`/`whnf4`), `StageR.coreS` + their posts give `TwinOK`.
* **The ROM readers as real callees.** The arms' models called `stubM "rom_*"` and used the six
  `sorry`'d `RelAM` specs of `DeclRomStubs.lean`, which no proof of the real readers (lane
  `integrate`'s `CIRead.lean`) could ever discharge (`stubM` is opaque). They now call
  `callW p n "rom_*"` and take **`L.Rom.RomRefs p`** (`ConAgua/Rom/CIReadSpec.lean`: the six
  refinements in `CallRef` shape, same pre/twin values/posts as before) as a field of their program
  bundles (`RedProg.rom`, `QuotProg.rom`, `DmProg7.lRom`, and the explicit `hR` of
  `checkBasisDecl_refines`, `reduce*_refines`). `RomRefs p` is `romRefs_of (RomReady p)`: the
  program's readers are `romCIProg` over a buffer starting with `romData` (`RomCIProg`), i.e. the
  substituted program `P.subPB bs` after `pb_check` (`triple_subPB`, as lane `romload`'s stage
  theorems). `romRefs_of` is `sorry` (helper `decls4-rom` proving it). The six `RelAM` stub specs are
  deleted. Models changed (fuel and program threaded): `selW`, `fpcW`/`fpcK1`, `tcoK4`, `famK6`,
  `reo*`.
* **`subst_const_all` refines `substConstAll`** (helper `decls4-sca`, 18 min, `DeclNatSubAll.lean`,
  418 lines, sorry-free, `@[refines]`): `CheckDeclProg.substAll` is gone (`substCAll_of`).
* Helpers running: `decls4-rom` (the ROM readers' proofs), `decls4-andpin` (`and_pin_ok`'s inductive
  arm: `and_block_named`, `ind_block_to_erec`, the canonical comparison against `rom_and_pin`).
* Census (`scripts/census.py`): phase 2 **218 proven, 40 sorry, 33 written, 40 todo** (lane start,
  master `b678e1d`: 206 / 50 / 35 / 40); totals 758 proven / 154 sorry of 1352. Caveat: targets
  through the ROM readers now rest on the hypothesis `RomRefs p` (a program fact, `romRefs_of`,
  `sorry` until the helper lands) instead of `sorry`'d stub specs.

### Landing 13: helper `install`; the lane's close
* Helper `install` (4.75 h): whole `@[refines]` for `checkBlockTele(s)`, `checkBlockAgree`,
  `consBlockCtors` (no new stub), `blockCapsAt`, `consBlockInds`, `checkBlockInds` (through the new
  `lvZeroCaps_spec` contract: `lv_zero_caps(l)` now *returns* the three `PropWhen` words, the caller
  writes the record), `checkBlockIdxSorts`, `checkAbsCtorSorts(All)`, `checkBlockRec`,
  `checkBlockCtors` (through "pending" contracts for `check_struct_field_sorts_i`, `gen_rec_check`,
  `check_sum_ctors` — **follow-up**: the first and third are proven since landing 12; replace those
  two contracts by the real refinements). **Bugs** (L, fixed): `check_block_agree` opened member 0's
  telescope once where the twin re-opens per member; `block_caps_at` computed `ruleK` from the raw
  `isProp` word (wrong for words other than 0/1); `block_caps_at` wrote its record across calls
  below the record pool's top (now computes all fields, then `ind_info_rec` writes the record).
  Open: `checkBlockPositivity` (needs `nestRoot_refines`' preconditions `UCtx`, `CssAt`, `NSB`,
  `PosMR`, fuel), `checkBlockTables`, `checkBlockPass`, `checkBlockTail`, `checkBlock`,
  `blockLargeElimAllowed`. ~4.3k proof lines for ~230 L lines.
* `lv_zero_caps`: lane defeq2's `CapsNeverZeroCore.lean` proves it under `CoreS`; using it for the
  stage needs the `StageR`→`CoreS` bridge (landing 1, "tried and dropped") — the next structural
  step for this lane's successor, together with `lvl_eq_c`, `lv_leq_top` and the whnf adapters.
* Census: phase 8 **79 proven, 108 sorry, 30 written, 6 todo** (lane start 58 / 38 / 119 / 8);
  totals 767 proven / 165 sorry / 149 written of 1352 (lane start 411 / 90).
### For the coordinator and lane `indproofs3`: `StageR` is not changed by `decls4`

`decls4` did not put `StateOK` into `StageR` and will not: it is a fact about the twin state alone, kept
by no memory frame, so it travels on the twin side (`TwinFold`, landing 1). What `lvl_eq_c`,
`lv_leq_top`, `lv_zero_caps` need at their callers is `TwinOK` (`DeclLvlStage.lean`: `ReadLCOK`,
`ReadLsCOK`, `NStoreWF`, `CoreMemos`, `StoreDen dn m a fe`, the sizes): `CoreS` facts, true after core
calls only if the core stubs' posts say so. Suggested single sweep (lane `indproofs3`): a field
`twin : TwinOK dn m a fe` in `StageR` (or `StageR' := StageR ∧ TwinOK`, migrated per file), with
every core stub spec's `KeepPost` carrying it (from `CoreS` via `StageR.coreS`/`CoreS.checkR`).
`StateOK` need not be in it (the callers get it from `TwinFold`). The only `decls4` files involved
are `DeclCvg.lean`'s `lvl_eq_c` call sites; `indproofs3` may edit them.


### Landing 11 (defeq2): `KnotCallees.recFireLevels` discharged (`recFireLevelsOK_of`)
* **Statement**: `RecFireLevelsOK` now asks that what `rec_fire_levels` reads back does so:
  the recursor's level parameters, and the fire datum at its words (`FireCore`: a plain rule's
  constructor parameters, a nested rule's stored levels). `us` needs nothing (`ls_node` aborts).
* **Where the facts come from**: `FireEnv fe lps rule cvj` (the recursor and the constructor are
  environment constants, the rule one of the recursor's) is state-free, so it threads from
  `iota_rec_c` (`fe.find?`) through `iota_rec_major`, `iota_rec_fire`, `iota_rec_fire2` to
  `iota_rec_fam`, where `lpsDen_of`/`fireCore_of` (`RecFireEnv.lean`) turn it into readbacks at the
  current state through `StoreDen.constLps` and the new field **`StoreDen.recRules`** (a stored
  recursor's nested rules' levels read back; kept by `mono`, an obligation where `TwinOK` is built).
* **Proof** (`RecFireCore.lean`): `recFireLevelsW_ok`'s steps under `CoreS` with lane `whnf4`'s level
  arms: `sleElemW_core` (`lvSubIntW_core` per stored level), `slpElemW_core`/`slpOne_core`
  (`lvInternW_core` on a hit, the parameter node by `liNode_core` on a miss), `spnLs_core`, the top
  put back (`StackKept.restoreG`). `CoreS.ctl136` (the walk memos' counters lie above `CTL[136]`).
  `KnotAllProg.caps` became `ls : LsProg p`. **`KnotCallees` has one field left: `instLP`.**

## Phase 8 proofs, round 4 (2026-10-22, lane `indproofs3`)

Continues lane `indproofs2` (above): the generated whole program regenerated, the two "pending"
callee contracts replaced by the proven refinements, the open block functions, the `StageR`→`CoreS`
bridge (`StageT`), and the `Rec*` targets.

### Landing 1: `Checker/Prog.lean` regenerated
`scripts/checker_prog.py` runs again (the import clash of indproofs2's landing 8 is gone): the hand
extension matched the generator up to order. Note: the generator only sees modules with an olean
in the worktree (`e2e.all_modules`), so a fresh worktree needs `scripts/lake build ConAgua` first —
otherwise it fails with "`builtin_prelude` calls `pre_front_run`, but `front_run` is not a copied
frontend function".

### Landing 2: the pending contracts gone
* `checkStructFieldSortsI_pending` and `checkSumCtors_pending` (both `sorry`) are deleted. Their
  users (`checkBlockIdxSorts`, `checkAbsCtorSorts(All)`, `checkBlockCtors`) now call
  `installSimFsorts` (IndInstallSpec17) and `installSimSumCtors` (IndInstallSpec22): `Sim` facts on
  the callee's run, proved from `IndSumSpec11`'s `fsortsW_ok` and `IndSumSpec13`'s `sctsW_ok`.
  Program bundles `IdxProg`, `AbsProg` (the `L.Ind` one), `CtorsProg` gain `sum : SumProg p`.
* **Every hypothesis is discharged by the caller.** `fsortsW_ok` needs `nP + j < 2^64`:
  `check_block_idx_sorts_one` already aborted on the wrap; `check_abs_ctor_sorts_one` now does too
  (`if hi + nF < hi { abort }`, a capacity abort). `sctsW_ok` needed `nP + nIdx < 2^64` and
  `nP + nF < 2^64` for every constructor, which no caller could establish (they are not facts of
  the decoded records): `check_sum_ctors` now aborts on either wrap, and the two hypotheses are gone
  from `sctsW_ok`/`checkSumCtors_refines`. The twin's `fe₀` (`fe.restrictTo vis0`) is `fe` at
  `vis0 = vis` by `EnvR.vis` from the stage relation.

### Helper `decls4-andpin`: `and_pin_ok`'s inductive arm refines `andPinOk`

* `DeclAndPinInd.lean`: `and_block_named` (`andBlockNamed_specW`, model `abnW`) and `abnW_eq`: it is
  `blockAndNamed (andHs m) block` on the block the front's record decodes to (`IndDeclAt`'s cut
  pool `trunc`), `andHs` the three pin words `andPinNameHs` reads (`andPinNameHs_runW`).
* `DeclAndPinIndDec.lean`: `FrontCI`/`FrontBlock` (an inductive with empty `all`/`ctors` and a
  name-free `sortZ`, a constructor, a recursor with plain rules: what `installIndD` pushes) and
  `decCI_reloc`: a relocated copy (word `2` the level parameters, word `7` a recursor's rules, every
  other word shifted, `ShR`) decodes to the same constant at any name decoder. The copy keeps a
  record's other slices as they are, so it is only right for front-shaped constants.
* `DeclAndPinIndCopy.lean`/`Copy2.lean`: word models and specs of `dind_copy`, `ind_rec_copy`,
  `ind_copy_go`, `ind_block_to_erec`; `ErW W m m'` (an `EREC` writer changing below the old top only
  `W`); `indBlockToErec_ok`: `StageR` kept, `IWGrow`, frame `[EREC] [129]`, the result an `EREC`
  slice decoding (`decCIs`, `erecP`) to the block. Robust record decodings (`RecRob`: in every array
  agreeing on the record's words) survive the later slot writes.
* **L change**: `dind_copy` aborts on a non-empty source at word `0` (the pool's top word, never a
  record's or a slice's place; `IndDeclAt`'s `trunc` reads it as `0`). Only non-front data hits it.
* `DeclAndPinIndRef.lean`: `andpW` (all of `and_pin_ok`), `andpW_ind_ok`, `andPinOkInd_refines`
  (`RefAM … (andPinOk (.indDecl block nP)) (KeepPost … decW0B)`, pre `StageR ∧ IndDeclAt ∧
  FrontBlock ∧ StateOK ∧` `DECL`/`DLP` below `2^63`), `andPinOkF_refines` (every `DeclAtF`
  record; `basisDecl` has no front record). Hypotheses: `RomAndPinRef p dn vis fe` (helper
  `decls4-rom`), `AndPinIndProg p` (lookups, `CanonProg`). Both tagged `refines_part`:
  `FrontBlock` of the front's blocks is not proved yet (lane front: a `DeclsF` clause, or from
  `installIndD`'s constants). `StateOK` after `andPinDecls`: con-ron's `internCIList_sstep`.

### Landing 3: `StageT`, the core's write set, the entry points under `StageT`
Coordinated with the coordinator (and lane `decls4`'s note: `decls4` does not change `StageR`):
`StageR` keeps its shape; **`StageT`** (`ConAgua/Arena/IndTwin.lean`) is a separate relation by
named components — `stage : StageR`, `twin : TwinOK` (lane `decls4`'s `DeclLvlStage.lean`: the
readback caches, `NStoreWF`, `StoreDen` incl. lane `defeq2`'s new `recRules`, the walk memos, three
capacities), `flag : pinW m 0 ≠ 0` — and a file migrates to it only where a core callee is reached.
* `StageT.core`: `StageT` is `CoreS` (eager bit `0`), so every `CoreS`-level refinement applies.
* **The core's write set from the text**: `CoreStageClosed p` (no function the stage's core entry
  points reach writes `IW`, `EREC`, `PINS`, `CTL[129]`, `CTL[200]`), decided for `checkerProg` in
  `ConAgua/Checker/IndCore.lean` (`decide +kernel`, as lane `whnf3`'s `CoreErec`). With it
  `StageT.of_core`: a core run's `CoreAfter` is `StageT` after and the pools are unchanged
  (`IWGrow`); `StageT.sim_core` turns any `CoreSpec` into a `Sim` on the call's run.
* **The entry points as `Sim` facts under `StageT`** (the "whnf adapters"; each replaces the
  `IndStubs` contract of the same name for a caller carrying `StageT`), sorry-free:
  `whnfTop_simT` (`whnf_top`, from the knot's `whnf` slot; the adapter `whnfTopL` had no spec
  before), `inferTypeCore_simT`, `isDefEqCore_simT`, `ensureSortCore_simT` (from `KnotSlot`'s and
  `InferLeaves`' entry refinements), `lvlEqC_simT` (lane `whnf`'s `lvlEqC_refines`). Program
  hypotheses: `KnotEntryProg p`, `p.lookup "whnf_top"`, `∀ n, KnotOK p n` (lanes `whnf4`/`defeq2`'s
  `knot_all`), `CoreStageClosed p`; L fuel `n ≤ 2^62` (the twin's `checkFuel`). `lvlEqC_simT` takes
  the two handles' readbacks, which a caller gets from `StoreDen.lvlAll`/`.sort`/`.zero`.
* **Frames by component**: `TwinOK.frame_iw` (no part of `TwinOK` reads `IW`/`CTL[200]`, so every
  pool writer keeps it), `StageT.of_iw` (a pool writer's `StageR` lemma + its frame), and
  `StageT.of_coreRef` (a master callee's `StageR` lemma + its `CoreS` refinement `CoreRef`, at a
  frame that leaves `PINS` alone); instances `internSort_stageT`, `internFVar_stageT` (from
  `IndMaster`'s `_stage` and `InferBodyIntern`'s `_core`).
* **Not done, and why** (the migration's open ends, in the order a successor meets them):
  1. *The stage's entry.* `StageT` at `check_ind_decl` must come from the declaration loop: `LoopR`
     carries neither `TwinOK` nor the flag. `decls4`'s `TwinFold` gives `StateOK` at the arm, but
     `TwinOK`'s caches/`StoreDen`/memos are `CoreS` facts after the previous declaration's core
     calls; the loop's arms run their core callees through stubs with `KeepPost` posts, so nothing
     carries them yet. Until the loop does, every stage theorem stated under `StageT` has a
     hypothesis its top caller cannot discharge (not vacuous: true in every state the checker
     reaches, by the twin's own invariants).
  2. *Stubs under `StageT`.* A stage function with a stub callee (`fvar_type_d`, `strip_pis`,
     `open_pis_at_fvars_f`, …) cannot move to `StageT` while the stub's contract only gives `StageR`
     after. Either the stubs get L code (9 of them still abort in `checkerProg`: `lv_zero_caps`,
     `name_rec`, `name_rec_i`, `rec_rule_bits`, `reserved_rec_name`, `open_pis_at_fvars_f`,
     `intern_ls_iw`, `fvar_b`, `consts_resolve_ffast`) or one generic `sorry`'d contract "a stub
     keeps `TwinOK`" in the style of `stubM_memoFrame`.
  3. *Record-pool writers.* `StoreDen.proj` quantifies over every `EREC` offset that decodes as a
     projection table (`decTbl (m.arr64 EREC) q`), so appending a record can break it;
     `StoreDen.frameE` needs `EREC` unchanged. `erec_alloc`/`cv_new`/`env_push` need `proj`
     restricted to records below `CTL[129]` (owner: lane `defeq2`, `StoreDen.lean`) or a per-writer
     argument.
  4. *`lv_leq_top`, `lv_zero_caps`, `blockLargeElimAllowed`.* `lv_leq_top` has a heap-level relation
     (`leqTopW_ok`, `LvR`); under `StageT` it needs `denoteL_lvR` at the two handles and the
     `readLevelM` runs (`readLevelM_run'`, `CoreS.withReadLC`) — the same pattern as `lvlEqC_simT`,
     not done. `lv_zero_caps` has no L code (an `abortStub` in `checkerProg`). `blockLargeElimAllowed`
     (`lv_nz` on the result sort) would follow the same pattern; its readback of `resSort` needs
     the shape's result sort to be a `sort` view's level (`StoreDen.sort`), which
     `blockShape?`'s refinement does not record yet.
* **A hypothesis no caller could discharge, removed.** `numCtorsOf_refines`,
  `blockShapeNumCtors_refines` and `blockShapeAllCtors_refines` (lane `indproofs`' helper `parts`)
  took `hsmall : ∀ i v, iwN m i = some v → v + 3 < 2^64`, a statement about *every* `IW` word that
  `StageR` does not give. It is only needed at the decoded member pointers, where `decMS` already
  reads `IW[v + 3]`, so `v + 3 < size < 2^64`: `numCtorsOfW_ok` now takes the pool's size bound
  (`IWOK`) instead, and the three census theorems follow.

## Kernel-checked compiler output (2026-10-22, lane `kernelasm`)

Goal: take the Lean compiler and runtime out of the trusted base. `compile_correct` is about the
term `compileProg tab p entry`, but the instructions that got printed came from *running*
`compileProg` as compiled Lean code. Now the checker's code is a literal term `checkerAsm`, the
kernel checks `checkerAsm_eq : compileProg checkerTab checkerProg "check" = checkerAsm`, and the
harness prints `checkerAsm`.

Files: `ConAgua/Compiler/AsmLit.lean` (the `asm_lit`/`asm_lit_fns` commands), `ConAgua/Checker/
{Asm,AsmPart0..3,AsmFinal,AsmEmit}.lean` (`Asm*` generated by `scripts/checker_prog.py` except
`AsmFinal`/`AsmEmit`), `Compile.lean` (numeric label paths, `Tab.romLen`), `Run.lean`
(`asmTextOf`), `scripts/check-asm.sh`, `scripts/e2e.c`, one bullet in `Final/Statement.lean`.

### The approach: per-function `Eq.refl` against a string-free literal

* **The literal.** `asm_lit` evaluates each function's code by compiled code (`progCode`, one
  evaluation per module), turns it into a term with Kraken's derived `ToExpr`, and replaces every
  label string by the term that names it: `lbl f n m`, `fnL g`, `errorL`, … — so the kernel never
  computes a string — and every `Int64` by `Int64.ofInt i` (the generator's own form). A function's
  code is a balanced `++` tree of list literals of ≤ 64 directives (a long list literal is a term
  of linear depth). How the literal was found does not matter: the kernel checks it.
* **Per function** `checkerAsm.f<i> := lit` and `checkerAsm.f<i>_eq : compileFn checkerTab f fd =
  checkerAsm.f<i>`, proved by `Eq.refl` handed to the kernel directly (no `Meta` defeq, no
  `decide`): the kernel evaluates `compileFn` on one function and compares. The trampoline likewise.
* **Composition** without evaluation: `checkerAsm := tramp ++ (f0 ++ (f1 ++ … ++ []))`, and
  `checkerAsm_eq` from the per-function equations by `List.flatMap_cons`, `congrArg`, `congr`,
  `Eq.trans` (one step per function; `checkerProg` unfolds to its list literal by delta).
* **Split** over `AsmPart0 … AsmPart3` (`asm_lit_fns checkerAsm : tab p lo hi`; `asm_lit` skips
  what is already declared), so Lake checks the four quarters in parallel (`ASM_PARTS` in
  `scripts/checker_prog.py`; the ranges follow the number of functions, so the files are
  regenerated with `Prog.lean`. A stale part fails the build at `checkerAsm_eq`).
* **The final theorems** (`Checker/AsmFinal.lean`; `Final/Statement.lean` cannot import the
  checker: `Checker/Entry` imports it): `checkerAsm_accepts`, `checkerAsm_model_exists`,
  `checkerAsm_no_False` are `checker_x64_accepts` & co. at `p := checkerProg` with the code
  hypothesis `hcode : Code checkerAsm k0` and `G.tab = checkerTab`; `Prog.wf` (`checkerProg_wf`),
  the entry (`checkerProg.lookup "check" = some checkL`, `rfl`, 0.2 s) and `nres` are discharged.
  `PipelineRefines checkerProg` stays a hypothesis. Axioms: `propext`, `Classical.choice`,
  `Quot.sound`.
* **The harness** prints from the literal: `lake env lean --run ConAgua/Checker/AsmEmit.lean
  OUT.s` (`asmTextOf checkerTab checkerAsm`, plus `ca_nb`/`ca_nw` and `ca_diag = -1` for
  `scripts/e2e.c`, which now reads the DIAG array only if `ca_diag < ca_nw`; `checkerProg`'s stubs
  just abort, so a stub reads as `error`, not `missing N`). `scripts/check-asm.sh` assembles and
  disassembles it: **312899 instructions match** (1717 functions after merging master; 312401 at 1714). On the e2e fixtures and arena tests of
  `_tmp/e2e/lfeat` the binary gives the same verdicts as the `e2e-l asm` build (every one stops at a
  stub on master: `error` here, `missing 26`/`error` there).

**Trusted base now**: Kraken's x64 semantics; the printer (`asmTextOf`, Kraken's `toATT`) and the
assembler, checked against each other on every printed file by `check-asm.sh` (disassembly
against the printed text, which is printed from the kernel-checked literal); the loader and the
harness (`HarnessCall`, `MemRel`); buffer to stream. Not the Lean compiler/runtime that runs
`compileProg` (the generator's evaluation is only a hint the kernel checks). The printer runs as
compiled Lean code over a literal (no compiler logic in it except printing).

### Changes to the code generator (needed for the kernel)

* **Numeric label paths.** A label was `".Lca_" ++ f ++ "_" ++ path ++ m` with `path` built by
  `path ++ "l"` etc. The kernel evaluates `String.append` through `ByteArray`s: **≈ 19 ms per
  label** (200 equations `".Lca_" ++ "intern_level_succ" ++ "_" ++ "lrlrlcpq" ++ "H" = …` by `rfl`:
  3.9 s of type checking). Now `path : Path := Nat`, child `d` is `Path.ch path d = 10 * path + d`
  (`d ∈ 1 … 9`: `l r c t e b` became `1 … 6`, `p q n` `7 8 9`), root `0`, and `lbl f path m :=
  ".Lca_" ++ f ++ "_" ++ toString path ++ m`. The literal keeps `lbl "f" 1342 "X"`; the kernel
  compares `Nat`s (GMP). Label distinctness was never part of the proof (it is the `Host`'s
  assumption about its program), so the proof changed in 6 lines (`path : String` → `Path`, `""`
  → `0`). Printed labels change (`.Lca_f_lrcX` → `.Lca_f_123X`); the instructions do not.
* **`Tab.romLen`** (with `romLen_eq : romLen = rom.length`, defaults `rom.length`/`by rfl`):
  `Tab.romWords := (romLen + 7) / 8`. The offsets past the constant data (`resOff`, `globOff`,
  `args`) used `rom.length`; `checkerTab.nres = 9 > 6`, so every epilogue writes the result area,
  and the kernel counted the 37 KB ROM once per function: **≈ 5.8 s per function** (100 functions:
  579 s; a copy of the table without the ROM: 93 ms for three functions that took 17.3 s).
  `tab_lit%` emits `romLen` as a literal with `Eq.refl` (counted once, where `checkerTab` is
  defined). Proof changes: four `simp only [Tab.romWords]; omega` became `Tab.rom_length_le`.

### Measurements (`lake env lean`, kernel time by `Environment.addDeclCore` around each check, peak RSS of the process)

| program | functions | instructions | kernel (`Eq.refl`) | per instruction |
|---|---:|---:|---:|---:|
| `scanProg` | 2 | 316 | 74 ms | 0.23 ms |
| `storeProg` | 11 | 1371 | 345 ms | 0.25 ms |
| `checkerProg` | 1714 | 329590 | 168 s | 0.51 ms |

* Per function on the checker: small functions (60–80 instructions) 10–50 ms; large ones grow a
  little faster than linearly (`pre_scan_line_loop` 1424 instructions 1.9 s, `pre_scan_ind_type`
  1172: 1.8 s, `cap_check`, 2396 instructions, under 1.5 s). Outliers are `ldc` of the big ROM strings: `romIdx` scans
  the ROM byte by byte: `pb_check` (81 instructions, a 21 KB string at offset 15787) **12.4 s**,
  `builtin_prelude` (15.7 KB at 87) 4.0 s; and `intern_all_pins` 3.5 s.
* **`cbv`** (the toolchain's `Lean.Meta.Tactic.Cbv`, with `lbl`/`fnL` `@[cbv_opaque]`): it works
  and its normal form is usable as a literal, but costs more on both sides: `scanProg` 686 ms of
  `cbv` + 147 ms kernel (rfl: 74 ms), `storeProg` 732 ms + 815 ms (rfl: 345 ms); its proof records
  every rewrite and congruence step, ≈ 2.4× the kernel time of `Eq.refl`, which only unfolds.
  With `checkerTab` it stops at `maxSteps` (call-by-value evaluates the table literal and its
  ROM); it would need `@[cbv_opaque] checkerTab` plus `cbv_eval` lemmas for its fields. Not
  pursued. Plain `decide`/elaborator `rfl` were not needed: the proof term is built directly, so
  `Meta` never unifies the two sides.
* **Whole checker in one module**: 236 s wall, kernel 182 s, compiling the literal definitions
  (LCNF/IR) ≈ 45 s, evaluating the code 2 s (61 s when each function was evaluated by its own
  `evalExpr`), peak **8.0 GB** (importing `Checker.Prog` alone takes ≈ 2.9 GB). `Elab.async`
  does not parallelise the kernel checks of one command. **Four parts**: parts + `Asm` built in
  142 s wall (279 s CPU), largest process 6.6 GB.
* **Extrapolation**: cost is linear in the instructions (≈ 0.5 ms kernel + ≈ 0.15 ms compile per
  instruction at the checker's function sizes) plus the `ldc`-of-a-large-string outliers. Twice
  the checker is ≈ 6 kernel-minutes, i.e. about 2.5 min wall with four parts or less with more
  parts (each part costs ≈ 3 GB for the import). It scales.
* Not done (cheap if needed): the `ldc` outliers (≈ 20 s of 168) could go by a per-string
  `romIdx` table in `Tab` (like `romLen`); the generated literal could mirror the code
  generator's `++` structure so the kernel never normalises an append (the remaining per-function
  superlinearity).

### `sorry`s

None.
### The ROM constant readers refine the twin (helper `decls4-rom`)

`romRefs_of` (moved from `CIReadSpec.lean` to `ConAgua/Rom/CIReadRefs.lean`, above the proofs)
is proved except for the quotient blocks: `rom_ci`, `rom_cv`, `rom_expr_pin`, `rom_and_pin`
(`@[refines]` of `eqA` … `ofReduceBoolA`, the reduce pins, `andPinDecls`) and `rom_basis_decls(_a)`
for kinds `0‥3` sorry-free (axioms `propext`, `Classical.choice`, `Quot.sound`).
* **Shape.** Word models through `callW` (`CIReadRefW.lean`, no model recursive, every spec one
  `vcgen`; `finish (gen := 30)`). The invariant `RInv m₀ a₀ T m a` (`CIReadRefBase.lean`):
  `ArenaD`, the twin keeping `cp`, writes only to `ExprA`/`ExprC`, `EREC`, `IW` and their tops,
  `IWGrow` from the entry, `IWOK`, the pool top `T`; `RInv.stage` gives `StageR` back at the
  entry's environment. A record is decoded by **`Holds SE SI f m x`** ("`f` gives `x` in every
  memory agreeing with `m` on the `EREC` words `SE` and the `IW` words `SI`"): it survives every
  later write outside its words (`Holds.keep`, `EKeep`), and at the end is `DecB` (`Holds.decB`).
  The ROM side reuses `romNameW_ok`, `romExprW_ok` (`MemoR` at a fresh memo); the region's layout
  is `slot_pos` (`ciTable`, `flatten_drop`), the values' fit is `decide +kernel` (< 1 s).
* **L changes.** `rci_fresh` also resets the level stack top `CTL[131]` (`rom_levels` needs
  `stkTop < 2^61`, which nothing in `StageR` bounds; nothing holds the stack between two ROM
  reads). `rci_ci`'s kind arms return instead of falling through (the merged paths made its
  `vcgen` spec run out of simp steps). `Checker/Prog.lean` unchanged (same names), `checkerProg_wf`
  builds. `scripts/checker_prog.py` stops at an unrelated, pre-existing problem
  (`builtin_prelude` calls `pre_front_run`).
* **Open (`sorry`): `romBasisRef_quot`, `romBasisARef_quot`** (kind `4`). `Quot`'s `sortZ` is
  `.ifAllZero [u]`: `decCaps` reads `u`'s handle back through `dn`, and nothing in `StageR`
  relates `dn` to the store, so the statement is false at `dn := fun _ => none`. It needs a
  hypothesis such as "`dn` reads back the store's names" (and the reader interns `u` where the twin
  keeps it as a value: a no-op on the store only because `u` is already a level parameter, which
  the proof would have to show). Every other pinned constant has `sortZ = .never` or
  `.ifAllZero []` (`capsFits`).
* `CIReadRefCaps.lean` elaborates in ~70 s (one 200-line proof, many `omega`s in a large context).

### Landing 3 (lane `decls4`): helpers `rom` and `andpin` merged; numbers

* **ROM readers** (helper `decls4-rom`, 84 min, `ConAgua/Rom/CIReadRef*.lean`, ~3.3k lines):
  `romCiRef_of`, `romCvRef_of`, `romExprPinRef_of`, `romAndPinRef_of` sorry-free (`@[refines]`),
  `rom_basis_decls(_a)` for kinds 0–3. **Open** (`romBasisRef_quot`, `romBasisARef_quot`, `sorry`):
  kind 4 (`quotK`), whose `Quot` carries `sortZ = .ifAllZero [u]`, read back through `dn`; false at an
  arbitrary `dn` under `StageR`. It needs "`dn` is the store's name readback" (`StoreDen.dnN`), which
  lane `indproofs3`'s `StageT := StageR ∧ TwinOK` will carry: restate the kind-4 refinement at
  `StageT` then. L changes: `rci_fresh` also resets the level stack `CTL[131]` (nothing lives on it
  between two ROM reads), `rci_ci`'s kind arms return directly (vcgen step limit).
  `CIReadRefCaps` elaborates in 67–88 s (watch list).
* **`and_pin_ok`'s inductive arm** (helper `decls4-andpin`, 53 min, `DeclAndPinInd*.lean`, ~1.9k
  lines, sorry-free): `and_block_named`, `ind_block_to_erec` (first spec), `andPinOkInd_refines`,
  `andPinOkF_refines` (every front record kind, `DeclAtF`), `refines_part`: they assume
  `FrontBlock` (the front's blocks have the shape the twin's `installIndD` pushes), not yet proved
  of the front; and the loop's relation does not carry `DeclsF` yet. Deliberate deviation D27
  (`dind_copy`'s word-0 guard).
* Census: phase 2 **237 proven, 40 sorry, 14 written, 40 todo** (lane start 206 / 50 / 35 / 40);
  totals 789 proven / 165 sorry of 1352. The phase-2 `sorry`s left go through the core's stub specs
  (`isDefEqCore_spec`, `inferTypeCore_spec`, `ensureSortCore_spec`, `whnf_spec`; the knot) and
  `lvl_eq_c`'s `TwinOK` gap (lane `indproofs3`).

### Lane `whnf4` closing
* `KnotCallees` is gone: `knot_all` needs only `KnotAllProg p` (program lookups). Lane `whnf4` (with
  helpers `whnf4-knot`, `-leaves`, `-rs`, `-d23`, `-ilp`) discharged `whnfCoreStep`, `whnfStep`,
  `proofIrrel`, `reduceProjCore`, `unfold`, `constTy`, `projSmall`, `fireOk`, `recShape`,
  `instLP`; lane `defeq2` `den`, `lvlsEqDen`, `capsNeverZero`, `recFireLevels`. D23 fixed (F15).
  The census-tagged whnf statements still instantiate the stub bundles (`whnfCallees_stub`,
  `coreCallees_stub`, `iotaCallees_stub`); re-stating them through `DefEqKnot`'s bundles is
  the next step for the census (not done here).
## Generated models and specs (2026-10-22, lane `modelgen`)

Recommendation 1 of `docs/proof-review.md`: generate, from an L function's text, the word model
(the second copy of the L code), its continuations and guarded equations, and the `vcgen` spec
with its proof. Piloted on finished, untouched code: the phase-4 walks (`Lift*`, `Inst1*`) and the
level files (`Level*`).

### The mechanism: `l_model` (`L/ModelGen.lean`, a command, ~1150 lines of meta code)

```
l_model liftGo_spec (p : Prog) (hp : LiftProg p)
  fns [hp.go ↦ liftW, hp.app ↦ liftAppW, …]
  specs [derB_spec p hp.derb n, memoFindG_spec lfSch p _ hp.lff n, mkApp_spec … n, …]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW] gen 20 heartbeats 1000000
```

* **Input.** For each member of a (mutually recursive) group, a proof `p.lookup "f" = some F` and
  the model's name; the specs of the callees as terms (the same terms a hand proof gives `vcgen`).
  The command reads `F`'s `lfn` text back from the file (declaration range, re-parsed), so it has
  the locals' names and the leaf terms as written (`CTL`, `⟪S.cs⟫`).
* **Callee models come from the callees' specs**, not from a registry: the post of each spec term
  is analysed (six shapes: effectful `F = some (r.headD 0, s'.mem)`; pure results
  `r.headD 0 = F₀ ∧ …` with the memory unchanged; a result list `r ≠ [] ∧ r = F`; memory only
  `F = some s'.mem`; total memory update with side conditions `G ∧ s'.mem = F`; read-only
  `F = some (r.headD 0)`). So any hand-written or generated spec in the PLAN's shape is a callee.
* **Translation** is symbolic execution of the statement list: locals are inlined, `abort` is
  `none`, a load is `rdW`, a store `Mem.set64`, a call to a group member is its model at fuel `n`,
  `x := call f(…); return x` is a tail call, and the code after an effectful call becomes a
  first-order continuation `fW.kᵢ` over the locals it reads (`| none => none | some (x, m₁) => …`,
  the PLAN's named-continuation style). The code after an `if` whose branches both fall through
  becomes a join point (a named function of the locals and the memory) instead of a copy.
  Identical continuations of a group are shared (the five lift arms share one "find; put; return"
  tail, the hand code's `lsetK`). `fold [tierW, idxW]` folds named word functions back in, and
  `fold [lvG, lvA, lvB]` the named results of a list callee.
* **Output.** The models (structural recursion on the fuel; well-founded on `(n, depth)` when
  continuations call the group's models, as `LevelLeq.lean` does by hand; no fuel argument for a
  single non-recursive function, as the hand `lhMkW`/`dist1W`); one **guarded equation**
  `fW.armᵢ` per non-`none` leaf of each model's and continuation's `if` tree (the path conditions
  as hypotheses, proved by the equation lemma and `ite_eq_left/right`) with a `grind_pattern` per
  attribute; the **spec** as a conjunction over the group, a step theorem `name.stepᵢ` per member
  (`vcgen` with only the callees that member calls, then `finish`) and the fuel induction.

### Pilot: what was replaced, lines and time

| file | lines before | after | what changed |
|---|---:|---:|---|
| `Lift.lean` | 591 | 219 | models, 10 continuations, 33 hand equations, 22 patterns, `liftGo_step` → one `l_model` |
| `LiftSpec.lean` | 171 | 56 | 5 arm steps, the induction, the entry's model/eqs/spec → one `l_model` |
| `LiftRefine.lean` | 521 | 526 | equation names (`liftW_app` → `liftW.arm4`, …), `tail_ok` over the shared continuation (+6) |
| `Inst1.lean` | 550 | 193 | as `Lift.lean` |
| `Inst1Spec.lean` | 174 | 60 | as `LiftSpec.lean` |
| `Inst1Refine.lean` | 519 | 524 | as `LiftRefine.lean` |
| `LevelSimp.lean` | 294 | 123 | `combW`, `simpW` (+`imaxW`, `simpK₁/₂`), `nzW`, 21 equations, 3 specs → three `l_model` |
| `LevelSimpRel.lean` | 264 | 273 | `imaxW_ok` over the generated join point (+9), names |
| **total** | **3084** | **1974** | **−1110 (−36 %)**; the generator is +1150 once |

Per function the hand-written part that remains is the L text, the program bundle and one
`l_model` (10–15 lines with the callee spec list). The refinements were adapted mechanically: the
dispatcher proofs (`lgoOK_succ`, `igoOK_succ`) kept their `by_cases` skeleton and dead-branch
lines (`rw [liftW] at hb; simp […] at hb` works on the generated model), only the equation names
and their hypothesis lists changed (the generated arm takes every path condition, e.g.
`liftW.arm4 n m h c k hcut hs g0 g4 hc` for the hand `liftW_app n m h c k hcut (vok 4 hc) g4`).
No theorem used outside these files changed (`liftEntry_refines`, `liftEntry_run`,
`instEntry_refines`, `instEntry_run`, `LiftProg`, `InstProg`, `liftProg`, `instProg`,
`lvComb/Simp/Nz_spec`, `combW_ok`, `simpW_ok`, `nzW_ok` keep their statements; the entries'
`liftEntryW`/`instEntryW` now take the fuel of their own call, `n + 1`, which only the two
refinement files read).

**Build time** (CPU seconds of `lake env lean` per file, old and new interleaved, two runs each,
load average 65–157, so ±15 %): `Lift` + `LiftSpec` 99 → 85, `Inst1` + `Inst1Spec` 45 → 56,
`LevelSimp` 7.6 → 6.2, the refinements unchanged (1–2.5 each); in total about the same (157 →
152). The generated specs pass each step only the callees it calls; the generated arm equations
carry more hypotheses than the hand ones (every path condition), which costs `finish` a little
(`Inst1`). The model/spec files now elaborate their steps in parallel (one theorem per member).

### What the generator does not handle (yet), from a dry run over all 43 level functions

Besides the 3 replaced, 28 more level functions were generated and their specs proved by the
standard script in a scratch copy (`LevelSubst` 4, `LevelZero` 2, `LevelHeap` `lh_mk`/`lv_eq`,
`LevelEquiv` 5, `LevelLeq`'s group of 7 in one `l_model` with `heartbeats 4000000`,
`LevelIntern` 5), 25 s for the `LevelLeq` group. Not handled:

* **several results**: `return (a, b, c)` (`lv_node`, `ls_node`, `lp_lookup`, `lv_lookup`) and
  callees whose post has `r.tail.headD 0` inside the model (`lookupW … = some (r.headD 0,
  r.tail.headD 0)`, so `lp_substl`, `lp_spw`, `lv_substl`, `lv_spw`): a list-valued model kind and
  a two-word continuation binder would cover them;
* **loops and named blocks** (`succ_find`'s `⟪sfindLoop⟫`, `succ_push`'s `⟪hpBlkS⟫`): a `while`
  needs its own fuel-recursive model and loop spec;
* **parameterized `FunDecl`s and models with Lean parameters** (`lvMemG A`, `lvSpwG PA`,
  `memoFindG S`, the generic `substLW KA VA`): the lookup must be `some F` for a constant `F`;
* **callee posts with extra facts** (`succ_push`'s `spushOK m t = true ∧ r = [scnt m t] ∧ …`).

Shape differences that matter for **retrofitting** (none of them for new code):

* the generated model is the L text, not a hand abstraction: `lhMkW` has a guard
  `(m.arr64 CTL).size ≤ 192` the L code does not have (a store out of bounds aborts, which the
  generated model does not model); `imaxW`'s two tests merged with `∧` are a nested `if` and a
  join point; the memo's `r ≠ []` becomes a `none` branch unless `noguard`;
* names are positional (`fW.kᵢ`, `fW.armᵢ`) and arm hypotheses are the raw path conditions (no
  `viewOK` bundling); a refinement written against hand names needs renames;
* **models used by other lanes' files cannot be swapped in place**: `zeroW` (7 files), `eqK` (6),
  `lvSubIntW` (5), `equivW`, `caW` (3 each), … are unfolded or rewritten by `Decl*`/`Ind*`/`Whnf*`
  proofs, and the level models call each other (`dist1W` is fuel-free by hand and generated, but
  `caW` in `LevelLeq` takes it as a callee), so replacing one cascades. That is why only
  `LevelSimp` (internal to the `Level*` files) was replaced.

### Recommendation

Use `l_model` for **new** L code: write the `lfn`, list the callee specs, and write the relational
proof against the generated `fW.armᵢ`/`fW.kᵢ.armᵢ` (look them up with `#check`, or `trace`). This
removes the model, continuations, `_some` equations, guarded equations, `grind_pattern`s and the
spec proofs (in the pilot 63 % of the model/spec files, 36 % of model + spec + refinement).
Do not retrofit finished code whose models other files read; retrofit only where the models are
internal (as `LevelSimp`), or when a function is rewritten anyway. Next steps, in order of value:
several results (a list model kind), `while` loops with a generated loop spec, `FunDecl`
parameters, optional names for arms (`l_model … arms [cut, bvar_lt, …]`) so refinements read
better, and generating the callee facts in `Sim` form (recommendation 2) from the same arms.
