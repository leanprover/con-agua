# strongverdict: the threaded verdict without the weakening

Lane brief (2026-11-10): the user, on the weakened threaded verdict of ronsync2 (§6 items 3–5):
"stronger sounds better". Restore the strong form at the cost of one more trusted fact about
`main.c` in the harness model.

## 1. The new harness fact, checked against `main.c`

`run_jobs`/`worker` (main.c, the comment at lines 168–186 and the code below it):

* `j = __atomic_fetch_add(&g_next, 1)`: one counter; the atomic read-modify-write hands out each of
  `0, 1, 2, …` exactly once, in the counter's modification order. If index `j` was handed out, every
  `j' < j` was handed out before it.
* After the claim the thread checks only `j >= g_k` (no `g_stop` check between the claim and the
  call), so every claimed index below `k` is run to the end of its `ca_check_b` call.
* A call that does not accept is stored in the thread's slot and the thread stops: a slot holds
  that thread's first (and last) failure.
* `main` joins every thread, then takes the slot with the smallest `j`.

So, when the harness reports the failure of job `j` (the failing thread's call `i`): every `j' < j`
was claimed (counter), run to completion (no stop check before the call), and accepted (otherwise its
thread's slot would hold `j' < j`, and `j` would not be the minimum). Every such call is an ordinary
call of a thread, so `ThreadsRun`'s per-call facts hold for it. And the failing thread's earlier
claims are below `j` (the same counter). `main.c` justifies the fact as written; it is not changed
(only two of its comments).

The new trusted facts, in `ThreadFail` (`Final/ThreadsVerdict.lean`):

* `before`: the failing thread's calls before `i` claimed smaller indices than call `i`;
* `others : ThreadsAcc dm₀ st₀ B ths`: a list of threads `ths` whose calls are all as `ThreadsRun`
  has them (`ThreadsAcc` is `ThreadsRun`'s per-thread fields, factored out: in place buffer,
  own region, zero at the first call, carried over, `BufCallH`, `FirstReturn`, accept, buffer kept,
  claim below `k`, claims increasing);
* `below`: every job index below call `i`'s is claimed by a call of a thread of `ths`.

(`ths` may contain the failing thread's own accepting prefix, its calls `0 … i-1`.)

## 2. Strong form reached, and the limit

The conclusion is the pooled verdict **without** the weak disjunct: `TwinVerdict [b] c`, or the
stages and the index ok and the failing thread's job list fails from the index state's worker with
class `c` (the pre-ronsync2 shape of `TwinVerdictPooled`). The brief asked for `TwinVerdict [b] c`
itself, the sequential run's verdict. That is not reachable with a harness fact: it needs a
twin-level theorem that a job's result (from `AState.worker` states reached by accepted jobs) does
not depend on which accepted jobs ran before it, e.g. that `recordJob` leaves the persistent tier
unchanged (then `SameEnter` holds between every worker state and the sequential run's state, and
`recordJob_sameEnter` transports the failure). con-ron proves no such frame theorem (it proves only
`PExt`, a persistent extension), nor any pool-to-sequential theorem for rejection; the accept side
also stays pooled (`TwinAcceptsPooled`). Proving it would be an `SMono`-like derivation over every
function `recordCheck` reaches (the knot alone is 331 functions), a lane of its own.

What the new fact buys in the proof: the threads' accepting calls below `j` are a pool covering the
positions below `j`, so con-ron's `pooled_fold` induction, cut at `j` (`pool_prefix`,
`Arena/PoolJobs.lean`, `pool_twin` now uses it), gives `PrefixOK` at every position up to `j`, hence
the fold invariant at the view of each of the failing thread's jobs; the old case "some record below
does not pass on its own" disappears, and with it `TwinJobPasses` and
`TwinVerdictPooled.of_not_passes`.

## 3. Before/after

### `TwinVerdictPooled` (`Final/TwinVerdict.lean`)

Before:
```lean
/-- **The twin's pool rejects or declines `chunks`**: the pipeline fails before the jobs
(`TwinVerdict`), or the stages and the stream index ran ok and some worker's list of jobs (record
positions) fails from the index state's worker with an error of class `c`, or some record before
the list's jobs does not pass on its own (the approved weakening: "the job fails with class `c`,
or some record below is rejected"). -/
def TwinVerdictPooled (chunks : List ByteArray) (c : L.Word) : Prop :=
  TwinVerdict chunks c ∨
  ∃ (pins : List NatOpPinSet) (sA sB sC sD sE sF : AState) (pre : PreludeIx) (r : ParseResultD)
    (ds : Array IDeclaration) (ipins : List INatOpPinSet) (I : IStreamIndex) (w : List Nat),
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧
    parseChunks chunks sB = .ok (.ok r, sC) ∧
    preparePrelude pre r.decls sC = .ok (ds, sD) ∧
    internAllPins pins sD = .ok (ipins, sE) ∧
    buildIndex ds sE = .ok (.ok I, sF) ∧
    (∀ t ∈ w, t < ds.size) ∧
    (TwinFailsV (checkJobList .verified ipins I ds w) sF.worker c ∨
      ∃ i, (∀ t ∈ w, i < t) ∧
        ¬ ∃ s', checkJobList .verified ipins I ds [i] sF.worker = .ok (.ok (), s'))
```

and (deleted)
```lean
/-- **Record `i`'s job passes on its own**: at every run of the stages and the stream index, the
twin's job of record `i` from the index state's worker accepts. -/
def TwinJobPasses (chunks : List ByteArray) (i : Nat) : Prop :=
  ∀ (pins : List NatOpPinSet) (sA sB sC sD sE sF : AState) (pre : PreludeIx) (r : ParseResultD)
    (ds : Array IDeclaration) (ipins : List INatOpPinSet) (I : IStreamIndex),
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) →
    builtinPreludeE sA = .ok (.ok pre, sB) →
    parseChunks chunks sB = .ok (.ok r, sC) →
    preparePrelude pre r.decls sC = .ok (ds, sD) →
    internAllPins pins sD = .ok (ipins, sE) →
    buildIndex ds sE = .ok (.ok I, sF) →
    ∃ s', checkJobList .verified ipins I ds [i] sF.worker = .ok (.ok (), s')
```

After:
```lean
/-- **The twin's pool rejects or declines `chunks`**: the pipeline fails before the jobs
(`TwinVerdict`), or the stages and the stream index ran ok and some worker's list of jobs (record
positions) fails from the index state's worker with an error of class `c`. -/
def TwinVerdictPooled (chunks : List ByteArray) (c : L.Word) : Prop :=
  TwinVerdict chunks c ∨
  ∃ (pins : List NatOpPinSet) (sA sB sC sD sE sF : AState) (pre : PreludeIx) (r : ParseResultD)
    (ds : Array IDeclaration) (ipins : List INatOpPinSet) (I : IStreamIndex) (w : List Nat),
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧
    parseChunks chunks sB = .ok (.ok r, sC) ∧
    preparePrelude pre r.decls sC = .ok (ds, sD) ∧
    internAllPins pins sD = .ok (ipins, sE) ∧
    buildIndex ds sE = .ok (.ok I, sF) ∧
    (∀ t ∈ w, t < ds.size) ∧
    TwinFailsV (checkJobList .verified ipins I ds w) sF.worker c
```

### The harness model: `ThreadsRun` (`Final/ThreadsFinal.lean`)

Before:
```lean
/-- **What the threaded harness does** (trusted; the module doc lists it): entry 1 at `dm₀`
returning at `st₀`, the buffer `B`, and the threads `ths`. -/
structure ThreadsRun [Host] (b pb : ByteArray) (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState)
    (B : Array Word) (ths : List ThreadM) : Prop where
  call₀ : AbiCall b pb dm₀ ra₀
  ret₀ : FirstReturn dm₀ (label abiStartAL) ra₀ st₀
  rdx₀ : st₀.data.regs.rdx = 0
  rax₀ : 9223372036854775808 ≤ st₀.data.regs.rax.toNat
  /-- the buffer: `OUT`'s first `len` words, `len` its word `1` -/
  bufw : ∀ i (h : i < B.size), rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * i)) = some B[i]
  buflen : ∃ w, rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8)) = some w ∧ w.toNat = B.size
  /-- the calls: the buffer in place, each thread on its region -/
  calls : ∀ t ∈ ths, ∀ i < t.n, BufCallH B (t.dm i) (t.ra i) ∧
    (t.dm i).regs.rdi.toNat = outAddr dm₀.regs.r8.toNat ∧ (t.dm i).regs.rcx.toNat = t.base ∧
    (t.dm i).regs.r8.toNat = t.blen
  zero : ∀ t ∈ ths, 0 < t.n → ∀ x, t.base ≤ x → x < t.base + t.blen → (t.dm 0).dmem.get? (A x) = some 0
  ret : ∀ t ∈ ths, ∀ i < t.n, FirstReturn (t.dm i) (label abiCheckBL) (t.ra i) (t.st i)
  acc : ∀ t ∈ ths, ∀ i < t.n, (t.st i).data.regs.rdx = 0 ∧ (t.st i).data.regs.rax = ACCEPT
  /-- route A: the buffer's words at each call's return -/
  kept : ∀ t ∈ ths, ∀ i < t.n, ∀ q (h : q < B.size),
    rdW (t.st i).data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * q)) = some B[q]
  next : ∀ t ∈ ths, ∀ i, i + 1 < t.n → ∀ x, t.base ≤ x → x < t.base + t.blen →
    (t.dm (i + 1)).dmem.get? (A x) = (t.st i).data.dmem.get? (A x)
  claimed : ∀ t ∈ ths, ∀ i < t.n, (t.dm i).regs.rdx < st₀.data.regs.rax - 9223372036854775808
  cover : ∀ j : Word, j < st₀.data.regs.rax - 9223372036854775808 → ∃ t ∈ ths, ∃ i < t.n, (t.dm i).regs.rdx = j
  /-- the claims increase in each thread (the claim counter is monotone) -/
  incr : ∀ t ∈ ths, ∀ i j, i < j → j < t.n → (t.dm i).regs.rdx < (t.dm j).regs.rdx
```

After (the same fields, the per-thread ones factored out into `ThreadsAcc`, which `ThreadsRun`
extends; `hR.calls` etc. still name them):
```lean
/-- **The threads' accepting calls** (trusted; the module doc lists it): for entry 1 at `dm₀`
returning at `st₀` and the buffer `B`, every call `i < t.n` of each thread `t` of `ths` is made
with the buffer in place and on the thread's region, returns accept with the buffer kept, and
claims a job index below `k`; each thread's region is zero at its first call and carries over
between its calls, and its claims increase. -/
structure ThreadsAcc [Host] (dm₀ : MachineData) (st₀ : MachineState) (B : Array Word)
    (ths : List ThreadM) : Prop where
  /-- the calls: the buffer in place, each thread on its region -/
  calls : ∀ t ∈ ths, ∀ i < t.n, BufCallH B (t.dm i) (t.ra i) ∧
    (t.dm i).regs.rdi.toNat = outAddr dm₀.regs.r8.toNat ∧ (t.dm i).regs.rcx.toNat = t.base ∧
    (t.dm i).regs.r8.toNat = t.blen
  zero : ∀ t ∈ ths, 0 < t.n → ∀ x, t.base ≤ x → x < t.base + t.blen → (t.dm 0).dmem.get? (A x) = some 0
  ret : ∀ t ∈ ths, ∀ i < t.n, FirstReturn (t.dm i) (label abiCheckBL) (t.ra i) (t.st i)
  acc : ∀ t ∈ ths, ∀ i < t.n, (t.st i).data.regs.rdx = 0 ∧ (t.st i).data.regs.rax = ACCEPT
  /-- route A: the buffer's words at each call's return -/
  kept : ∀ t ∈ ths, ∀ i < t.n, ∀ q (h : q < B.size),
    rdW (t.st i).data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * q)) = some B[q]
  next : ∀ t ∈ ths, ∀ i, i + 1 < t.n → ∀ x, t.base ≤ x → x < t.base + t.blen →
    (t.dm (i + 1)).dmem.get? (A x) = (t.st i).data.dmem.get? (A x)
  claimed : ∀ t ∈ ths, ∀ i < t.n, (t.dm i).regs.rdx < st₀.data.regs.rax - 9223372036854775808
  /-- the claims increase in each thread (the claim counter is monotone) -/
  incr : ∀ t ∈ ths, ∀ i j, i < j → j < t.n → (t.dm i).regs.rdx < (t.dm j).regs.rdx

/-- **What the threaded harness does** (trusted; the module doc lists it): entry 1 at `dm₀`
returning at `st₀`, the buffer `B`, and the threads `ths`, whose calls all accept
(`ThreadsAcc`) and claim every job index below `k`. -/
structure ThreadsRun [Host] (b pb : ByteArray) (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState)
    (B : Array Word) (ths : List ThreadM) : Prop extends ThreadsAcc dm₀ st₀ B ths where
  call₀ : AbiCall b pb dm₀ ra₀
  ret₀ : FirstReturn dm₀ (label abiStartAL) ra₀ st₀
  rdx₀ : st₀.data.regs.rdx = 0
  rax₀ : 9223372036854775808 ≤ st₀.data.regs.rax.toNat
  /-- the buffer: `OUT`'s first `len` words, `len` its word `1` -/
  bufw : ∀ i (h : i < B.size), rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * i)) = some B[i]
  buflen : ∃ w, rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8)) = some w ∧ w.toNat = B.size
  cover : ∀ j : Word, j < st₀.data.regs.rax - 9223372036854775808 → ∃ t ∈ ths, ∃ i < t.n, (t.dm i).regs.rdx = j
```

### The failing run's model: `ThreadFail`, `ThreadsFail` (`Final/ThreadsVerdict.lean`)

Before:
```lean
/-- **A thread's call `i` fails** (trusted; the module doc lists it): entry 1 at `dm₀` returning
at `st₀`, the buffer `B`, and the thread `t`'s calls `0, …, i` (`ThreadsRun`'s fields for them),
the calls before `i` accepting, call `i` returning `rdx = 2`. -/
structure ThreadFail [Host] (b pb : ByteArray) (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState)
    (B : Array Word) (t : ThreadM) (i : Nat) : Prop where
  call₀ : AbiCall b pb dm₀ ra₀
  ret₀ : FirstReturn dm₀ (label abiStartAL) ra₀ st₀
  rdx₀ : st₀.data.regs.rdx = 0
  rax₀ : 9223372036854775808 ≤ st₀.data.regs.rax.toNat
  /-- the buffer: `OUT`'s first `len` words, `len` its word `1` -/
  bufw : ∀ q (h : q < B.size), rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * q)) = some B[q]
  buflen : ∃ w, rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8)) = some w ∧ w.toNat = B.size
  /-- the calls: the buffer in place, on the thread's region -/
  calls : ∀ i' ≤ i, BufCallH B (t.dm i') (t.ra i') ∧
    (t.dm i').regs.rdi.toNat = outAddr dm₀.regs.r8.toNat ∧ (t.dm i').regs.rcx.toNat = t.base ∧
    (t.dm i').regs.r8.toNat = t.blen
  zero : ∀ x, t.base ≤ x → x < t.base + t.blen → (t.dm 0).dmem.get? (A x) = some 0
  ret : ∀ i' ≤ i, FirstReturn (t.dm i') (label abiCheckBL) (t.ra i') (t.st i')
  acc : ∀ i' < i, (t.st i').data.regs.rdx = 0 ∧ (t.st i').data.regs.rax = ACCEPT
  rdx : (t.st i).data.regs.rdx = 2
  /-- route A: the buffer's words at each accepting call's return -/
  kept : ∀ i' < i, ∀ q (h : q < B.size),
    rdW (t.st i').data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * q)) = some B[q]
  next : ∀ i', i' < i → ∀ x, t.base ≤ x → x < t.base + t.blen →
    (t.dm (i' + 1)).dmem.get? (A x) = (t.st i').data.dmem.get? (A x)
  claimed : ∀ i' ≤ i, (t.dm i').regs.rdx < st₀.data.regs.rax - 9223372036854775808

/-- **The threaded harness reports a failure with the code `k`**: entry 1 failed with
`rax = k`, or a thread's call `i` failed with `rax = k`. -/
def ThreadsFail [Host] (b pb : ByteArray) (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState)
    (k : Word) : Prop :=
  (Entry1Fail b pb dm₀ ra₀ st₀ ∧ k = st₀.data.regs.rax) ∨
  ∃ (B : Array Word) (t : ThreadM) (i : Nat), ThreadFail b pb dm₀ ra₀ st₀ B t i ∧
    k = (t.st i).data.regs.rax
```

After (new: the parameter `ths`, the fields `before`, `others`, `below`):
```lean
/-- **A thread's call `i` fails** (trusted; the module doc lists it): entry 1 at `dm₀` returning
at `st₀`, the buffer `B`, and the thread `t`'s calls `0, …, i` (`ThreadsRun`'s fields for them),
the calls before `i` accepting and claiming smaller job indices, call `i` returning `rdx = 2`;
and every job index below call `i`'s claimed by an accepting call of the threads `ths`
(`ThreadsAcc`). -/
structure ThreadFail [Host] (b pb : ByteArray) (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState)
    (B : Array Word) (ths : List ThreadM) (t : ThreadM) (i : Nat) : Prop where
  call₀ : AbiCall b pb dm₀ ra₀
  ret₀ : FirstReturn dm₀ (label abiStartAL) ra₀ st₀
  rdx₀ : st₀.data.regs.rdx = 0
  rax₀ : 9223372036854775808 ≤ st₀.data.regs.rax.toNat
  /-- the buffer: `OUT`'s first `len` words, `len` its word `1` -/
  bufw : ∀ q (h : q < B.size), rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * q)) = some B[q]
  buflen : ∃ w, rdW st₀.data.dmem (A (outAddr dm₀.regs.r8.toNat + 8)) = some w ∧ w.toNat = B.size
  /-- the calls: the buffer in place, on the thread's region -/
  calls : ∀ i' ≤ i, BufCallH B (t.dm i') (t.ra i') ∧
    (t.dm i').regs.rdi.toNat = outAddr dm₀.regs.r8.toNat ∧ (t.dm i').regs.rcx.toNat = t.base ∧
    (t.dm i').regs.r8.toNat = t.blen
  zero : ∀ x, t.base ≤ x → x < t.base + t.blen → (t.dm 0).dmem.get? (A x) = some 0
  ret : ∀ i' ≤ i, FirstReturn (t.dm i') (label abiCheckBL) (t.ra i') (t.st i')
  acc : ∀ i' < i, (t.st i').data.regs.rdx = 0 ∧ (t.st i').data.regs.rax = ACCEPT
  rdx : (t.st i).data.regs.rdx = 2
  /-- route A: the buffer's words at each accepting call's return -/
  kept : ∀ i' < i, ∀ q (h : q < B.size),
    rdW (t.st i').data.dmem (A (outAddr dm₀.regs.r8.toNat + 8 * q)) = some B[q]
  next : ∀ i', i' < i → ∀ x, t.base ≤ x → x < t.base + t.blen →
    (t.dm (i' + 1)).dmem.get? (A x) = (t.st i').data.dmem.get? (A x)
  claimed : ∀ i' ≤ i, (t.dm i').regs.rdx < st₀.data.regs.rax - 9223372036854775808
  /-- the thread's earlier calls claimed smaller job indices -/
  before : ∀ i' < i, (t.dm i').regs.rdx < (t.dm i).regs.rdx
  /-- the jobs below call `i`'s: each claimed by an accepting call of a thread of `ths` -/
  others : ThreadsAcc dm₀ st₀ B ths
  below : ∀ j < (t.dm i).regs.rdx, ∃ t' ∈ ths, ∃ i' < t'.n, (t'.dm i').regs.rdx = j

/-- **The threaded harness reports a failure with the code `k`**: entry 1 failed with
`rax = k`, or a thread's call `i` failed with `rax = k`. -/
def ThreadsFail [Host] (b pb : ByteArray) (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState)
    (k : Word) : Prop :=
  (Entry1Fail b pb dm₀ ra₀ st₀ ∧ k = st₀.data.regs.rax) ∨
  ∃ (B : Array Word) (ths : List ThreadM) (t : ThreadM) (i : Nat),
    ThreadFail b pb dm₀ ra₀ st₀ B ths t i ∧ k = (t.st i).data.regs.rax
```

### The L-level claim `ThreadEVerdict` (proved: `threadEVerdict_proved`)

Before:
```lean
def ThreadEVerdict : Prop :=
  ∀ (Vt : Type u) [ConLeche.SetTheory Vt] (b pb : ByteArray) (sz : TieredArray → Nat), InputsOK b pb sz →
    ∀ (N₁ : Nat), N₁ < 2 ^ 62 → ∀ (rs₁ : List Word) (m₁ : Mem),
    L.run checkerProg N₁ "check" [] (loadMemM b pb sz 1) = .ok (rs₁, m₁) →
    9223372036854775808 ≤ (rs₁.headD 0).toNat →
    ∀ (B : Array Word), B = (m₁.arr64 OUT).extract 0 ((m₁.arr64 OUT).getD 1 0).toNat →
    ∀ (r₀ : Mem), (∀ b ∈ parOwnedL, r₀.arr64 b = zeros (m₁.arr64 b).size) → r₀.glob INIT = 0 →
    ∀ (j : Word) (cs : List (Word × Nat × Mem)) (n : Nat) (e : Err), ThreadFails B j n e r₀ cs →
    (∀ c ∈ cs, c.1 < rs₁.headD 0 - 9223372036854775808) → j < rs₁.headD 0 - 9223372036854775808 →
    e.cls ≠ 0 → (∀ i < j.toNat, TwinJobPasses [b] i) → TwinVerdictPooled [b] e.cls
```

After:
```lean
def ThreadEVerdict : Prop :=
  ∀ (Vt : Type u) [ConLeche.SetTheory Vt] (b pb : ByteArray) (sz : TieredArray → Nat), InputsOK b pb sz →
    ∀ (N₁ : Nat), N₁ < 2 ^ 62 → ∀ (rs₁ : List Word) (m₁ : Mem),
    L.run checkerProg N₁ "check" [] (loadMemM b pb sz 1) = .ok (rs₁, m₁) →
    9223372036854775808 ≤ (rs₁.headD 0).toNat →
    ∀ (B : Array Word), B = (m₁.arr64 OUT).extract 0 ((m₁.arr64 OUT).getD 1 0).toNat →
    ∀ (r₀ : Mem), (∀ b ∈ parOwnedL, r₀.arr64 b = zeros (m₁.arr64 b).size) → r₀.glob INIT = 0 →
    ∀ (j : Word) (cs : List (Word × Nat × Mem)) (n : Nat) (e : Err), ThreadFails B j n e r₀ cs →
    (∀ c ∈ cs, c.1 < j) → j < rs₁.headD 0 - 9223372036854775808 → e.cls ≠ 0 →
    ∀ (ths : List (Mem × List (Word × Nat × Mem))),
    (∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m₁.arr64 b).size) ∧
      t.1.glob INIT = 0 ∧ ThreadRuns B t.1 t.2 ∧ ∀ c ∈ t.2, c.1 < rs₁.headD 0 - 9223372036854775808) →
    (∀ t ∈ ths, (t.2.map (·.1)).Pairwise (· < ·)) →
    (∀ i : Word, i < j → ∃ t ∈ ths, ∃ c ∈ t.2, c.1 = i) →
    TwinVerdictPooled [b] e.cls
```

### The final theorem (`Final/EndToEnd.lean`), text unchanged

```lean
theorem checkerFile_threads_verdict [Host] (V : Type w) [ConLeche.SetTheory V] (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (k : Word)
    (hF : ThreadsFail b pb dm₀ ra₀ st₀ k) (hk : k &&& 3 ≠ 0) : TwinVerdictPooled [b] (k &&& 3) :=
```

Its meaning changes through `ThreadsFail` (stronger hypotheses) and `TwinVerdictPooled` (stronger
conclusion). Axioms unchanged: `[propext, Classical.choice, Quot.sound]`.

## 4. Other changes

* `ThreadsFinal.threadsAcc_runs`: the per-thread L chain, out of `threadsRun_twinAcceptsPooled_regs`,
  now shared with `threadFail_twin` (the other threads' chains).
* `ParThreadTwin.threadRuns_chain`: a thread's `ThreadRuns` as a `JobChain` (was a local `have`).
* `ThreadsE.threads_twinVerdictPooled`: the hypothesis `∀ i < j, TwinJobPasses [b] i` replaced by the
  other threads' runs below `j` (`ths`, `hth`, `hinc`, `hbelow`) and the failing thread's earlier claims
  below `j` (`hcs : ∀ c ∈ cs, c.1 < j`, was `< k`).
* Docs: OVERVIEW §2.3 (the threaded verdict's assumptions) and §9.3 (what it says), the Final and
  Verdict module docs, two comments in `main.c`. `docs/deviations.md` has no row on it.
