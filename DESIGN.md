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

Files: `ConAgua/Arena/**`. (Work in progress; the full write-up follows when the proofs land.)

### L extension requests

Each request names the workaround used meanwhile.

1. **`mulhi`: the high word of the unsigned 64×64→128 product**, as a `BinOp`
   (`mulhi a b = (a.toNat * b.toNat / 2^64)`, a `Word`). x64 `mul r/m64` leaves exactly this in
   `rdx` (and the low word, L's existing wrapping `*`, in `rax`), so the compiler case is
   `mov rcx, <b>; mul rcx; mov rax, rdx` (`rdx` is already scratch). con-ron's
   `mul_u64_from` (`ron/nat.rs:497`) needs it once per limb product (`u128` there).
   Workaround: an L function `mulhi(x, y)` over 32-bit halves (four products, nine L lines,
   one hand-proved arithmetic lemma).
2. **A comparison as a word (`setcc`)**: an `Expr` form `cmpw c a b` with value `1`/`0`
   (x64 `cmp; setb al; movzx eax, al`). The carry of a word addition is then
   `c' := (s <ᵤ x) | (s2 <ᵤ s)` with no branch. Each `if` doubles the paths `vcgen` explores
   in a loop body, and a loop body with four ifs (two limb reads, two carry tests) already
   exceeded `grind`'s budget. Workaround: the carry is an L function `add_carry(x, y, c)`
   (and the limb read `nat_limb(o, l, i)`, as in the Rust), so the loop body is straight-line
   code with calls.
3. **Several results** (`return (a, b)` into named locals of the caller), for functions that
   produce a slice `(offset, length)` or a `(low, high)` word pair. Workaround: a function
   that appends to the pool returns the length; the offset is the old pool top, which the
   caller reads before the call.
4. *(Not a language feature, a note for the logic.)* A callee spec should post
   `LocEq s' s₀` (a named predicate for `s'.loc = s₀.loc`, with the `grind` pattern
   `LocEq s t, s.loc x`), not `s'.loc = s₀.loc` or `s' = s₀`: `grind` cannot read
   `s'.loc x` back through a function or structure equation unless the term `s₀.loc x`
   already exists (`docs/gaps/grind-state-eq-projection.lean`). With `LocEq` the
   `num_end` `sorry` of `ConAgua/Scan/Leaves.lean` may go away too.

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

