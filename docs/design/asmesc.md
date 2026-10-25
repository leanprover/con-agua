# Lane `asmesc`: escaping to assembly (scoping, with a proved pilot)

Branch `asmesc` (pilot code in `ConAgua/AsmEsc/`, not built by `ConAgua`), scratch `_tmp/asmesc`.
Base: master 4f9bfff9 (`checker.s` at the root). Init = `init435.ndjson`, harness `main.c` with
the embedded pins.

**Verdict.** Variant (A), a hand-written body for an L function proved against the compiler's own
per-function contract, is cheap and composes with `compile_correct` without changing its
statement. The pilot, `app_find`, is **proved** (no `sorry`, standard axioms, 2 s to elaborate,
~2 h of agent time) and saves **10.4 G instructions (2.9%) and ~1.5% of the cycles on Init** by
itself. Recommendation: land the leaf back end (lane leafgen) first, then add the escape
framework (~1.5 lane-days) and asm for three templates (ConsLib exact find, ConsLib push, MemoLib
find/put), which carry most of the hash-table gap. Nothing new becomes trusted.

## 1. Composition: what the compiler proof asks of a function's code

The whole interface between a function's code and the rest of the proof is `FunSim`
(`Compiler/SimCall.lean`): `execSim_all` proves it for every function from `ExecSim` of the
bodies, and `sim_callTail`/`sim_tail` (calls and tail calls) only *use* it, together with the fact
that the code starts with `label (fnL f)` (`compileFn_head`). The pilot names its body
`FnSimAt p G n f fd kf` (`AppFindAsm.lean`); `funSim_iff` shows `FunSim p G t n ↔ ∀ f fd kf,
lookup → Code (compileFn …) kf → FnSimAt p G n f fd kf` by `Iff.rfl`. The contract, for every
fuel `n`:

* **Pre:** entered at `label (fnL f)`; the return address at `[rsp]`; the arguments in `argRegs`
  (`rdi r8 r9 r10 r11 rsi`, at most six) or at `[rsi + 8i]`; `G.lo ≤ rsp`, `rsp + 8 ≤ G.hi` (the
  L stack); `r15 = T`; `MemRel G σ.mem d.dmem` (L's memory in the layout); `r14 < n` (machine fuel
  below L fuel).
* **Normal return (only if L returns):** if `(invoke p (exec p n) f vs).run σ = .ok (r, σ')` then
  every run reaches `ra` with `MemRel G σ'.mem`, `rsp + 8`, `rbp` and `r15` unchanged, `r14` not
  increased, the first `Stmt.nret fd.body` results in `rax rdi r8 r9 r10 r11` (then the table's
  result area), and memory changed only in the L stack below `rsp`, the arrays, the result area
  and the globals (`Pres`). Everything else (flags, all other registers) is scratch.
* **`ca_error`:** allowed only when L's run is an error other than `outOfFuel` (`GPost`: `rbp`,
  `Pres`).
* **`ca_exhausted`:** allowed **always** (`GPost` only). This is the escape hatch: hand-written
  code may give up on anything it does not want to handle; it reads as `rdx = 1`, never accept
  (`OutcomeRel` already allows it).
* **Termination:** `Ev` is inductive, so every path must end. A loop either has its own variant
  or does what the compiled code does: `sub r14, 1; jb ca_exhausted` per back-edge. Mirroring L's
  loop fuel this way is also what makes "L returns at fuel `n`" provable (2 fused instructions per
  iteration).
* **Not in the contract, but required:** `rbx`, `r12`, `r13` must not occur (`RegsRestored` relies
  on "they do not occur in `checker.s`", not a theorem); local labels must keep the file's labels
  unique (`Host.labels_nodup`); leaves only (a hand-written body that calls L functions needs
  `FunSim` of the callee at `n - 1`, available in `execSim_all`'s induction but not worth it now).

So yes: a hand-written block can be dropped in for one function, and its correctness is exactly
"`FnSimAt p G n f fd kf` for all `n`".

**What changes in `compile_correct`.** Replace `compileFn tab t f fd` by
`fnCode X tab t f fd := (X.lookup f).getD (compileFn tab t f fd)` for a table `X : List (FnName ×
Program)`, in `compileFns`/`compileProgT`/`compileProg` (a `compileProgX X`), in `FunSim`'s
quantifier, `code_of_lookup`, `hProg` (`stepSim`, `sim_tail`, `sim_callTail`), `compileFn_head`
(now an obligation of the table: each body starts with `label (fnL f)`) and `funSim` (a case
split: a function in `X` takes its proof from the hypothesis, the others keep today's proof). New
hypothesis of the theorem: `hX : ∀ f c, X.lookup f = some c → c[0]? = some (.label (fnL f)) ∧ ∀ n
fd kf, p.lookup f = some fd → Code c kf → FnSimAt p G n f fd kf`. With `X = []` this is today's
theorem, so `compile_correct` stays as a corollary; the final theorems are unchanged: the kernel
check of the committed file (`checkerFile_eq`, `asm_lit`) compares with `compileProgX checkerX`,
and `hX` is discharged once by the per-routine theorems at `checkerTab` (their table side
conditions are `decide`: for `app_find`, `5 < wK`, `1 < nw`, `16 + 16 (nb + nw) < 2^31`).
`AsmEmit`/`asm_lit` print and check the table's bodies like any function. The trusted parser
already reads every form the pilot uses (`leaq` with scale 2, `cmovCC`, `mulq`, `imulq r, r`,
`cmpq r, mem`); `scripts/check-asm.sh` covers their encodings. Estimate: **1 lane-day** for the
proof threading (mechanical, ~150 changed lines in `SimCall`/`SimTail`/`SimFun`/`Correct`/`Main`),
**0.5 day** for emitter, literal and file check.

## 2. (A) or (B)

**(A)**, clearly. In (A) the L body stays: every L-level proof, analysis and tool (vcgen specs,
`Prog.wf`, `GKeep`/`Agree`/`WriteSet`, `FuelMono`, the census, the twin refinements) is untouched,
and only one machine-level obligation is added per routine. The pilot shows the obligation splits
into an L-side functional model (`appFind_run`: the L code at fuel `n` *is* `afSpec`, a pure
function, by `RunEq`'s step equations; 230 lines) and a machine-side simulation against that model
(`appFindAsm_sim`). That is (B)'s convenience (prove the asm against a pure function) without
(B)'s cost.

(B) adds a primitive to L: a new `FunDecl` kind with a spec instead of a body. Every L-level tool
must learn it, and the library specs that callers use (`ConsLibSpec`, `MemoLibSpec`, proved today
from the L body under `ArenaRel`-style relations) would have to be proved at the machine level
against those relational specs, which is much harder than against the function's own L
semantics. (B) pays off only for code with no sensible L body; there is none here.

## 3. Pilot: `app_find`

`app_find(t, f, a, h)` = `consFindG appCS` (exact table: the slot's key word is `f | a << 32`, no
record read). L: 110.9 instructions per call, clang -O2 of the L program 64.7 (perfgap). The
hand-written body (`appFindAsm tab`, `AppFindAsm.lean`; printed at `checkerTab` in the
appendix): frameless, no stack check, locals in nine scratch registers, the
tier's descriptor words loaded once, the key word and home slot computed in registers, then the
probe loop: **22 instructions of prologue, 7 per empty probe, 13 per occupied probe**, the same
bounds checks and fuel decrement as L. A hand-tuned variant (one fewer load in the
hit path, `cmpq $1, mem`) is 0.7 G better; the proved one uses forms the existing step lemmas
cover.

Init, `perf stat`, interleaved, harness of 4f9bfff9:

| | instructions | cycles (min of 6, load 12–26) |
|---|---:|---:|
| master | 359.13 G | 96.77 G |
| `app_find` proved asm | 348.74 G (−10.38 G, −2.89%) | 95.26 G (−1.50 G, −1.55%) |
| `app_find` hand-tuned (unproved) | 348.05 G (−11.08 G) | |

Medians of the cycles: 97.10 G and 95.77 G (−1.4%); every one of the six pairs favours the asm
except the last (noise). About half of the instruction saving shows in cycles at this load.
Per call: 110.9 → 50.8 instructions (clang 64.7: hand asm beats the oracle because it has no
SysV frame, no callee-saved pushes and no struct return).

**Proof** (`ConAgua/AsmEsc/`, 930 lines, elaborates in ~2 s, axioms `propext`, `Classical.choice`,
`Quot.sound`):
* `Step.lean` (113 lines, reusable): six step lemmas for forms the compiler does not emit
  (`op r, r`, `imul r, r`, `mul r`, `lea r, [b + 2i]`, `cmp [rcx + 8 rax], r`, `cmovCC r, r`).
* `AppFindL.lean` (228): `appFind_body` (by `rfl`), `afLoop`/`afSpec` (the loop and the function
  at fuel `n`), `afW_run` (the loop, by induction on the fuel with `RunEq`'s equations),
  `afBody_run`, **`appFind_run`**: `(invoke p (exec p n) "app_find" [t,f,a,h]).run σ =
  (afSpec σ.mem t f a h n).map (·, σ)`.
* `AppFindAsm.lean` (586, of which ~100 the program and the contract): `af_loop` (the probe loop,
  by induction on the fuel, with `ev_gen` checkpoints that forget the state's shape), the
  prologue, and **`appFindAsm_sim`**: for every table with `ASLOT` tiered and `CTL` a word array,
  every program containing `appFind`, every fuel, `FnSimAt p G n "app_find" appFind kf`.

Time: about 2 hours of agent time from the first line to the last `sorry`, on top of ~40 minutes
of reading. The style is the compiler proof's (one `ev_*` lemma per instruction, `simp only` on
`Reg64s.set64_*`/`*_mk`); the Kraken vcgen (`kvcgen64`, `Program.wp`, `cfg_cases`) was not
needed: the straight-line steps are cheap this way, and `ev_gen` checkpoints keep the terms small.
Pitfalls met: matcher identity (state the L-side lemmas as predicates on `stepRun` results, not as
equations between `match`es); `simp` on dependent `if h : i < size` after rewriting a local
(keep the state as a `setLoc` chain and rewrite with hypotheses about an abstract state);
`omega` intermittently failing on goals that mention `UInt64.toNat` atoms (generalize them first).

## 4. Templates

The pilot's proof is already parametric in the table (all offsets are `tab.len64 a`,
`tab.base64 a`); what is `app`-specific is the array ids and the key word (`nk = 2`). Of the 20
ConsLib instances, **13 are exact** (`app bvar const forall imax fvar nanon succ max lam param sort
zero`, `nk ≤ 2`): their finds differ only in `sa`, `nk` and the descriptor offsets, so one
generator `asmFindExact C tab` and one proof (an `nk` case split in the key word, `afSpec`
generalized to `consFindG C` with `C.exact`) cover them, as `consFindG_spec` does at L level.
The 7 fingerprint tables run an instance-specific match fragment (`mpre`/`mc`, arbitrary L); a
template would have to compile the fragment, i.e. be a code generator again. They are small
(0.1–0.15 G gap each): leave them to the compiler. MemoLib (`ilm_* ilp_* crm_* apd_* env_*`) is
a second template (find, put), ConsLib push a third. Push and put write memory (`MemRel` after
the stores, `Pres`) and include the in-place growth, which runs on real inputs and so cannot be
left to `ca_exhausted`: either the asm implements it (long but straight loops) or the framework
lets an asm body tail-jump to the compiled L code of a slow-path function (needs `FunSim` of that
function at the same `n`; a small extension of `execSim_all`).

## 5. Estimate and recommendation

**Gain.** Measured for `app_find`: −10.4 G instructions (−2.9%), −1.5 G cycles (−1.5%). The hash
routines are 113 G of L's 359 G instructions (perfgap); the pilot runs at 0.46× L per call. At a
similar ratio the top seven (`app_find ilm_find ilm_put app_push apd_find ilp_find crm_find`, ~78 G
in L) would save ~42 G instructions (**~12%**, ~6% of the cycles at the pilot's ratio of cycle
to instruction gain), all hash routines ~60 G (~17%, ~8–9% of the cycles). L is instruction-bound
(IPC 3.45, perfgap §1), and under load cycles follow instructions more closely.

**Cost.** Framework 1.5 lane-days. Exact-find template (13 instances, one proof): ~0.5 day.
MemoLib find/put: ~1–2 days (put writes). ConsLib push with growth: ~2 days. A one-off leaf of
the pilot's shape (straight line + one loop, no stores): 2–4 hours.

**Trust.** Nothing new. The asm is checked by the kernel against Kraken; the parser, printer and
assembler checks already cover the forms. Kraken's semantics of a few more instruction forms
becomes load-bearing (inside its fuzzed scope).

**Against and with the leaf back end.** Leafgen improves every leaf automatically for a one-time
compiler-proof cost and reaches maybe 2/3 of the leaf gap (perfgap §4); asm goes beyond clang on a
handful of routines at a per-template cost. They combine: the table `X` overrides whatever the
back end emits, so asm only needs to beat the improved back end where it matters. Order: leafgen
first; re-measure the hash routines; then the framework and the exact-find template (best
gain per proof hour: 13 instances, one proof, `app_find` alone 2.9%), then MemoLib, then push.

## Appendix: the proved `app_find` at `checkerTab`

As measured: replace `ca_f_app_find`'s body in `checker.s` with this text and build with the
harness (`cc -std=gnu23 -O2 -pthread -o checker main.c checker.s`). Offsets: `ASLOT` length
`2672`, base `128` (tiered, `+ 8 (t & 1)`), `CTL` length `2608`, base `64`.

```
ca_f_app_find:
movq %rdi, %rsi
andq $1, %rsi
movq 2672(%r15,%rsi,8), %rdx
cmpq $1, %rdx
jbe ca_error
movq 128(%r15,%rsi,8), %rcx
movq 2608(%r15), %rax
cmpq $62, %rax
jbe ca_error
movq 64(%r15), %rax
movq 496(%rax), %rsi
imulq %rdi, %rsi
movq %rdx, %rdi
shlq $32, %r9
orq %r9, %r8
movq (%rcx), %r11
addq $8, %r11
movq $-7046029254386353131, %rax
imulq %rax, %r10
movq %r10, %rax
shrq $32, %rax
xorq %r10, %rax
mulq %r11
movq %rdx, %r9
movq %rdi, %rdx
movq 8(%rcx), %rdi
addq $2, %rdi
movq $0, %r10
.Lasm_app_find_H:
cmpq %r11, %r10
jae ca_error
leaq (%rdi,%r9,2), %rax
cmpq %rdx, %rax
jae ca_error
cmpq %rsi, (%rcx,%rax,8)
jbe .Lasm_app_find_E
addq $1, %rax
cmpq %rdx, %rax
jae ca_error
cmpq %r8, (%rcx,%rax,8)
je .Lasm_app_find_F
addq $1, %r9
movq $0, %rax
cmpq %r11, %r9
cmovae %rax, %r9
addq $1, %r10
subq $1, %r14
jb ca_exhausted
jmp .Lasm_app_find_H
.Lasm_app_find_F:
subq $1, %rax
movq (%rcx,%rax,8), %rax
subq %rsi, %rax
subq $1, %rax
movq %rax, %rdi
movq $1, %rax
movq %r9, %r8
movq %r10, %r9
ret
.Lasm_app_find_E:
movq $0, %rax
movq $0, %rdi
movq %r9, %r8
movq %r10, %r9
ret
```
