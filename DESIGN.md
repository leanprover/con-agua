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
  node's position (lowercase letters) and `M` an uppercase marker. Labels are therefore distinct
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
emits `storeProg`), `harness/check-asm.sh`, `harness/check_asm.py`,
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

**The asm/disassembly audit, `harness/check-asm.sh`.** The printer and the assembler sit outside
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

Run: `harness/check-asm.sh` (rebuilds the three `Emit*` drivers, then checks each). Current
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

### `sorry`s

None (no proof touched; `compile_correct` unaffected, `#print axioms` unchanged:
`propext`, `Classical.choice`, `Quot.sound`).

## Every term store in `ArenaR`, and the walk over every node (2026-10-21, lane `tables2`)

Files: `ConAgua/Arena/{FVar,Proj,NAnon,NStr,NNum,Ls}{Store,Refine}.lean` (part 1; `lam`/`forallE`
and the walk follow),
`ConAgua/Arena/PoolSlice.lean` (new), `ConAgua/Arena/ArenaRel.lean` (regenerated, `arena_build`),
`ConAgua/Arena/WalkRefine.lean`. `fvar`/`proj`, `lam`/`forallE` and the name store's
`anonymous`/`num` were written by three subagents in parallel worktrees, one file pair per table;
the variable-length keys and `ArenaR` in the lane's own worktree.

### Layout

The tables after `bvar`/the memo take (or reserve) arrays 25‥40 and count words `CTL[s + t]`, `s` the table's
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
parallel). `ArenaRel.lean`'s table-dependent parts (imports, header, `RLocal`s, frames, fields,
`arena_build`, `arenaR_init`, lifts) are generated by a script from a table list (not committed;
the output is ordinary Lean); the `intern*_refinesA` theorems are written per table.
