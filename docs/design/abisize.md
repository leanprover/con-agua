# Lane abisize: the buffer-size hypotheses out of the final theorems

**Change.** The setup stub `ca_setup` (`abiHead`, `ConAgua/Compiler/Abi.lean`) checks, after the
region size, `cmp rsi, 0; jl ca_abi_decline; cmp rcx, 0; jl ca_abi_decline`: an input or pin-data
length with the top bit set returns `rdx = 1` (exhausted), the same exit as a too-small region.
Every entry that takes buffers goes through `ca_setup` (`ca_start_a`, `ca_start_a0`, so the driver
`ca_start` too); `ca_check_b` takes no buffers.

**Proof.** `sim_abiStub`'s go-case gets `rsi < 2^63`, `rcx < 2^63`; entry 1's posts
(`abi_start_outcome`, `abiMode_outcome`, `abiA_outcome`, `abiA0_outcome`) add `SizesPost b pb`
(`rdx = 1 ∨ b.size < 2^63 ∧ pb.size < 2^63`, via `AbiCall.hn/hnp`); `DrvAccepts` carries the two
bounds; the threaded theorem takes them from entry 1's `rdx₀ = 0`. `hb`, `hpb` are gone from
`checkerFile_accepts`, `_regs`, `_model_exists`, `_no_False`, `checkerFile_threads_*`,
`checkerFile_drv_accepts_regs`, `threadsRun_twinAcceptsPooled(_regs)`, `drvAccepts_twin`.
`ThreadsRun` never carried them. main.c drops its own `>= 2^63` check.

**`h64` stays.** `System.Platform.numBits` is `(getNumBits ()).val` for an opaque
`getNumBits : Unit → {n // n = 32 ∨ n = 64}`: nothing in the logic decides it. The twin's frontend
(con-leche `Frontend/ExportC.lean`, `Scan/*`) indexes the input with `USize`, so `TwinAccepts` itself
depends on it, and the frontend refinements (`ConAgua/Scan/WordLink.lean` and every `*Link` with
`h64`) need `USize` = 64 bits to match the machine words. Removing it would mean proving the
theorem also for a 32-bit `USize`, where the twin's parser computes something else.
