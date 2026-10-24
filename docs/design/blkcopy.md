# Lane `blkcopy`: block copy and scan as L primitives (journal)

Branch `blkcopy`, worktree `_tmp/wt/blkcopy`. Phase 1: inventory, design, unproved prototype,
measurements. Suggestion (user): byte/word copy loops as an L language primitive with efficient
assembly, proved once in the compiler, instead of per-element L loops whose every store pays
index arithmetic and (with tiered arrays) a tier-descriptor lookup.

## 1. Inventory and profile (master `62f7d23b`)

Exact dynamic instruction counts with `scripts/asmprof.py` (a copy in `_tmp/blkcopy/asmprof.py`
links `harness/main.c` instead of the old `harness/e2e.c` and passes the pins as an argument).
Per-function shares, master:

| fixture | instructions | copy/scan functions (share of all instructions) |
|---|---:|---|
| `irrel_commit` (69 KB) | 77 M | `rom_u64` 6.6, `rom_put` 3.3 (ROM/pin reading, every run) |
| `delta_chain` | 92 M | `rom_u64` 5.5, `rom_put` 2.8, scanners (`skip_ws`, `key_end`, `skip_digits`) 5.3 |
| `pinstall_ok` | 191 M | `rom_u64` 2.6, `rom_put` 1.3, scanners 12.0, string body 2.4 |
| `long_line_5mib` | 1.13 G | `utf8_valid`+`utf8_char` 39.1, `str_close` 16.7, `str_put_esc` 15.3, `has_escape` 14.0, `lit_hash` 9.4 |
| `complete_c03d` | 4.3 G | `iw_copy` 1.6 |
| `complete_c04a` | 26.0 G | `iw_copy` 1.3, scanners 1.4 |
| `init435` (Lean's `Init`, 346 MB) | 372.8 G | scanners 4.0 (`skip_digits` 1.9, `key_end` 1.1, `skip_ws` 1.0), `beta_peel` 0.8 (not a pure copy), every copy function together < 0.2 |

So on the real workload (`Init`) the copy loops do not matter; the JSON scanners do a little.
They matter for the fixed cost of small inputs (ROM/pin reading: 5–10 %), for long strings
(`long_line_5mib`: ~95 % is scanning and copying bytes), and slightly for the kernel fixtures
(`iw_copy`, a recursive per-element copy at 42 instructions per word).

**Kinds of loops** (static inventory: ~80 copy statements in L, most of them fixed-length record
copies, unrolled by hand, never hot):

* word→word slice copies, recursive one call per element: `iw_copy`, `er_copy`, `pool_copy`,
  `lh_er_copy`, `iw_pool`, `spn_to_iw`, `iw_to_spn`, `ik_copy`, `ek_copy`, `spn_pool`,
  `dind_copy`, `er_from_iw_go`, `block_caps_at_er_copy_go`, `n_idxs_copy`, `ptr_names_copy`
  (the last two transform); loops: `erec_push` loop (`WhnfIotaRec`), `prep_copy_rec`,
  `prep_back_rec`, `sput` (RomLevels: POOL ← RSTK), `beta_peel`'s spine copy (interleaved with
  lambda peeling: not a block copy). `promote_l_pool` transforms every element (a call each).
* byte→word widening copies: `rput` (`rom_put`: PB → POOL), `str_put_esc`'s fast path (IN → POOL),
  `put` (`str_put`, front only, not in `checkerProg`).
* 8-byte little-endian loads: `rom_u64` (8 byte loads, 7 multiplies, 105 instructions per call).
* scans (first index in a range whose byte is in a class): `skip_ws`, `skip_digits`, `key_end`,
  `str_close`, `has_escape`, the ASCII run of `utf8_valid`, `rom_put`'s ASCII check, the run up
  to the next backslash in `str_put_esc`.
* the `pre_*` copies of the frontend (`Checker/Prelude.lean`, `preFn`) read the builtin prelude
  from constant data (`ldc`) instead of `IN`: a source "constant bytes" is needed if these should
  convert too.

## 2. Design

### Syntax and semantics

New statements (and one expression), all with the tier of `tierA` (lane tierarr: `t & 1`, a
constant `0` for untiered arrays; the compiler resolves a descriptor ONCE per block):

```
Stmt.copy64 (d : ArrId) (dt di : Expr) (s : ArrId) (st si : Expr) (n : Expr)
    -- copy D⟨dt⟩[di ..] := S⟨st⟩[si ..] for n
Stmt.copy8w (d : ArrId) (dt di : Expr) (s : ByteSrc) (si : Expr) (n : Expr)
    -- copy D⟨dt⟩[di ..] := S.u8[si ..] for n      (zero-extended bytes; ByteSrc = arr8 a | rom d)
Stmt.scan8 (x : Var) (s : ByteSrc) (i e : Expr) (c : ByteClass)
    -- x := scan S.u8[i .. e] until C              (first j ∈ [i, e) with C (S[j]), else e)
Expr.ld8x8 (a : ArrId) (i : Expr)
    -- A.u64le[i]: the word of bytes i .. i+7, little-endian
```

`ByteClass` is a Lean constant (a 256-entry table, `tblOf p`); it goes into the program's
constant data like an `ldc` string (`Stmt.roms`).

Semantics, in `Mem` terms, is the obvious loop, so that proofs can unfold it:

```
def Mem.copy64 (m : Mem) (d : ArrId) (di : Word) (s : ArrId) (si : Word) : Nat → Mem
  | 0 => m
  | k + 1 => (m.set64 d di ((m.arr64 s)[si.toNat]!)).copy64 d (di + 1) s (si + 1) k
def scanN (b : Array UInt8) (c : ByteClass) (i e : Nat) : Nat   -- first j ∈ [i, e) with c b[j], else e
```

`step` evaluates the operands left to right, then checks the bounds ONCE, as natural numbers:
`di + n ≤ len (tierA d dt)` and `si + n ≤ len (tierA s st)` (`i ≤ e ≤ len` for a scan,
`i + 8 ≤ len` for `ld8x8`); out of bounds is `throw .oob` before anything is written. A block
costs no fuel (like `st64`): the compiled code may burn less fuel than the L run (`SPost.r14` is
`≤`), so this is allowed by the existing simulation statement. Ascending element order is part of
the semantics, so an overlapping copy within one array means what the old loop meant.

Differences from the loops they replace: a loop aborts at the first out-of-bounds element after
writing the ones before; the block aborts before writing anything. Both are `error`, never an
accept; the refinement proofs of the converted functions carry the same preconditions as before
(the callers already establish the bounds), so their specs are unchanged. A recursive copy could
exhaust the stack on a long slice where the block cannot: that only turns `exhausted` into a
result.

### Code generation (Kraken's x64 subset)

Kraken models no `rep movs`, no `bt`, no SSE integer compares or `pmovzx` (only
`movups/vmovups/movaps/addps/subps` among vector instructions). So the blocks are scalar loops
over `rax`, `rcx`, `rdx` (the compiler's scratch registers; leaves keep their register locals),
plus one frame temporary for the end pointer:

* copy64: bounds (`add`, `jc`, `cmp`, `ja` per side), `rcx` = source pointer, `rdx` = destination
  − source, then `mov rax,[rcx]; mov [rcx+rdx],rax; add rcx,8; cmp rcx,end; jb` — 5 instructions
  per word (was 42 for `iw_copy`).
* copy8w: `movzx rax,byte [rcx]; mov [rdx],rax; add rcx,1; add rdx,8; cmp rcx,end; jb` — 6 per
  byte (was ~25–33 with the bounds checks and index arithmetic of each `st64`).
* scan8: `movzx rdx,byte [rcx+rax]; cmpb $0, tbl(%r15,%rdx); jne; add rax,1; cmp rax,e; jb` —
  6 per byte (was 15–36). A table lookup handles any class; SWAR (8 bytes per step with
  `(x − 0x01…) & ~x & 0x80…`) would give ~1.5 per byte for single-byte and "≥ 128" classes, but
  only long strings would see it.
* ld8x8: one `mov rax, [rcx + rax]` after the bound check.

Operands that are simple (a local, a global, a length, a small constant) are used in place;
others are evaluated into temporaries.

## 3. Prototype (unproved)

`ConAgua/Proto/BlkCompile.lean` (not in the lake globs; run with
`scripts/lake env lean --run ConAgua/Proto/BlkCompile.lean OUT.s [FNS]`, 4 s): a copy of
`Compiler/Compile.lean` (namespace `L.CompilerB`) that compiles a call of a reserved name
(`__copy64_*`, `__copy8w_*`, `__scan8_*`, `__ld8x8_*`; array ids in a registry) inline, as the
blocks above (`intrCode`); such a call does not make a function a non-leaf. `L.Blk.blkify`
replaces the bodies of 12 functions of `checkerProg` (`str_put_esc`, `utf8_valid`, `has_escape`,
`str_close`, `key_end`, `skip_digits`, `skip_ws`, `rom_u64`, `rom_put`, `iw_copy`, `er_copy`,
`pool_copy`) with versions using them. With no function selected the output is byte-identical
to `asm/checker.s` (checked).

### Results

`instructions:u`, master (`62f7d23b`, `asm/checker.s`) against the prototype (`blk2`: the 12
functions; `blk4`: also every call of `rom_u64` inlined as the 8-byte load, so its callers can
become leaves). `bench.py --set default --reps 3`, interleaved (machine load 60–120, so cycles
and wall are noisy; instructions are exact):

| fixture | master | blk2 | ratio |
|---|---:|---:|---:|
| `irrel_commit` | 77 M | 72 M | 0.94 (blk4: 70.3 M, 0.91) |
| `delta_chain` | 92 M | 86 M | 0.93 |
| `nested_struct_proj` | 99 M | 94 M | 0.95 |
| `mutual_struct_proj` | 159 M | 151 M | 0.95 |
| `shift-cascade` | 129 M | 121 M | 0.94 |
| `dag_tower_unfold` | 141 M | 130 M | 0.92 |
| `inmodel_nested` | 207 M | 198 M | 0.96 |
| `pinstall_ok` | 192 M | 178 M | 0.93 |
| `long_line_5mib` | 1 128 M | 416 M | 0.37 (wall 0.066 → 0.037 s) |
| `complete_c03d` | 4 318 M | 4 251 M | 0.985 |
| `let-ladder` | 9 274 M | 9 263 M | 0.999 |
| `beta-ladder` | 17 437 M | 17 427 M | 0.999 |
| `complete_c04a` | 26 031 M | 25 610 M | 0.984 |
| **geomean** | | | **0.888** instructions, 0.932 cycles, 0.955 wall |
| `init435` (one run) | 372.83 G | 367.03 G | 0.984 |

What is left in the converted functions (asmprof, blk2): the scans and copies run at 6
instructions per byte (`long_line_5mib`: each of `str_close`, `has_escape`, `utf8_valid`,
`str_put_esc` is now 63 M; `lit_hash` at 106 M is the largest item, and it hashes, it does not
copy). `rom_put` dropped from 217 to 148 instructions per call: names average 4.3 bytes, so the
call, the frame and the bounds checks dominate. `rom_u64` went from 105 to 33 per call, and to
~8 inline in blk4.

Verdicts: `bench.py --set all --reps 0 --no-conron --no-ref`, master against blk2: 675 fixtures, 0 disagreements (log `_tmp/blkcopy/verdicts2.log`); blk4: 675 fixtures, 0 disagreements (`verdicts4.log`).

### tierpool

Lane tierpool's head (`d6642eb6`) does not build (`Front/Unescape.lean`, `Arena/NatAdd.lean`,
`Arena/Scratch.lean`), so the prototype could not be measured on its checker. The prototype has
the tierpool variants ready (`replacementsTP`, `__copy8wt_*`: tiered destination, descriptor
resolved once per block; run with `… OUT.s all tp`). These tierpool functions would switch to
the primitives:

* `str_put_esc` (`escLoop`'s per-byte `POOL⟨pt⟩[pb + k] := c`): scan to the next backslash, then
  one `copy POOL⟨pt⟩[pb + k ..] := IN.u8[j ..]`. This is where the +9.5 % on `long_line_5mib`
  comes from; with the block it does not depend on the tier at all (the tier is looked up once).
* `rom_put` / `rputLoop`: `copy POOL⟨pt⟩[pb ..] := PB.u8[i ..] for l` (plus the ASCII scan).
* `sput` (`RomLevels`, POOL⟨pt⟩ ← RSTK), `spn_pool` (POOL⟨pt⟩ ← SPN), `iw_pool` (POOL⟨pt⟩ ← IW):
  word copies with a tiered destination.
* `pool_copy0` (copy-on-promote, `POOL⟨0⟩[q + j] := POOL⦃o + j⦄`) and `pool_copy` (IW ←
  `POOL⦃s⦄`): word copies with a tiered SOURCE (`POOL⟨o >> 40⟩[o & (2^40 − 1) ..]`); a slice lies in
  one tier, so the block decodes the tier once.
* `str_put` (front only), `utf8_put` stays as it is (at most 4 stores, no loop).

## 4. Cost of the real feature (estimate)

**Compiler, once** (the "proved once" part):
* Syntax/semantics: `Stmt.copy64`, `Stmt.copy8w`, `Stmt.scan8`, `Expr.ld8x8`, `ByteSrc`
  (`arr8 a | rom d`: the `pre_*` frontend copies read the prelude from constant data, so
  `Checker/Prelude.lean`'s `preS` must turn an `IN` source into `rom preludeBytes`), `Mem.copy64`,
  `Mem.copy8w`, `scanN`, `step` arms.
* Structural functions with new arms: `tempsE/tempsS/tempsSB`, `roms` (class tables), `nglob`,
  `uses`, `readsReg`, `calls`, `Stmt.wf`/WFFast, `toPB` (`Rom/PinRead.lean`), `preS`, write sets
  (`WriteSet.lean`: `{tierA d c}` for a constant tier, `{d, d + 256}` otherwise), `PureEval`
  (`ld8x8` only). ~2 h.
* Simulation proofs: `sim_copy64` (tier on either side), `sim_copy8w`, `sim_scan8`, `sim_ld8x8`.
  The first three are a new shape for the compiler proof: a machine loop with no L loop around
  it, proved by induction on the iterations inside one `SimS` case, with the invariant
  "`Inv` for `σ.mem.copy64 … j`, `rcx` = source + 8j, the end pointer in its temporary". The
  pieces exist (`ev_*` step lemmas, `Inv.store64`, `Pres.store64`, `MemRel.rom` for the class
  table, temporaries as in `compileArgs`). `ld8x8` needs `rdW` at a byte address as the
  little-endian word of 8 `get8`s. Estimate 6–10 h (tierarr's straight-line `ld64t/st64t/len64t`
  feature, semantics to sim proofs, took 150 min of work).
* Lemma library: `Mem.copy64`/`copy8w` frames (other arrays, lengths, globals unchanged), the
  element read (`(m.copy64 d di s si k).arr64 d` at `x`: in range and `d ≠ s` or no overlap → the
  source word, else unchanged), `scanN_stop/skip/end`. ~1–2 h.
* ModelGen (lane lmodel2): arms for the new statements (`copy` → guard + `m.copy64 …`, `scan` →
  `scanN …`), so that generated `l_model`s cover converted functions. ~1 h on top of lmodel2.

**Per converted function** (its own spec is re-proved; the spec STATEMENT and the model stay, so
callers and refinement proofs do not change): a bridge lemma "old model = scanN/copy form" by
induction (`skipWsN b i = scanN b notWs i b.size`, `escLoopW` over a backslash-free run = one
`copy8w`), then a short straight-line spec. ~30 min each for `skip_ws`, `skip_digits`,
`key_end`, `has_escape`, `str_close`, `rom_put`, `iw_copy`, `er_copy`, `pool_copy`; ~1–2 h
for `str_put_esc` and `utf8_valid` (the loop changes shape: per run instead of per byte);
`rom_u64` ~1 h (bit arithmetic: Σ bᵢ·256ⁱ = the LE word) plus its callers if it is inlined.
Watch: models indexed by L fuel (`erCopyW`, `poolCopyW`: `Nat → …`) — the block needs no fuel,
so their specs get a "for every fuel ≥ 1" form and callers that name a specific fuel need a
small adaptation (+1–2 h). For tierpool's writers, the conversion should happen after (or
inside) tierpool, since both rewrite the same lines.

**Total**: ~12–18 h of agent work for the feature and the 12 conversions measured here.

## 5. Assessment

* Real workload (`Init`): −1.6 % instructions, nearly all from the JSON scanners (`skip_digits`,
  `key_end`, `skip_ws`), not from copies (copies < 0.2 % of `Init`).
* Small inputs: −5 to −9 % (the ROM/pin reading of every run: `rom_u64`, `rom_put`).
* Long strings: −63 % on `long_line_5mib`, and it removes tierpool's +9.5 % there.
* Kernel fixtures: −0.1 to −1.6 % (`iw_copy`).
* Not done: SWAR scans (8 bytes per step, ~1.5 instructions per byte for single-byte and
  "≥ 128" classes; only long strings would gain), unrolled copies, the `pre_*` copies (need the
  `rom` byte source), the rarely run copy loops of §1.

A cheaper alternative with the same machine code: idiom recognition in the compiler (compile
the exact loop shape `while j < n { A[x + j] := B[y + j]; j += 1 }` as the block). That needs no
change to L code or its proofs, but only covers loops of exactly that shape: not the recursive
copies (`iw_copy`, …), not the scans (whose loops are all different), not `rom_u64`. The
primitive is the better design; the idiom form could serve as a stopgap for `rputLoop`/`putLoop`.

## 6. Phase 2, step 1: the primitives, proved (landed with `asm/checker.s` unchanged)

As designed in §2, with these choices made while proving:

* **Syntax** (`L/Syntax.lean`): `BSrc` (`arr a` | `rom d`), `WArr` (`plain a` | `tier a t`),
  `Expr.ld8x8`, `Stmt.copy64`, `Stmt.copy8w`, `Stmt.scan8`. Surface (`L/Notation.lean`):
  `x := scan!(A.u8, i, e, C)`, `copy!(D.u64, di, S.u64|S.u8|D.c8, si, n)` (with `D⟨t⟩`/`S⟨t⟩`),
  `le64!(A.u8, i)`. The `!` keeps `scan`/`copy`/`le64` usable as identifiers.
* **Semantics** (`L/Semantics.lean`): the ascending loop (`Mem.copy64`, `Mem.copy8w`), `scanN`,
  `le64` (Kraken's `Nat.ofBytes` order); bounds checked once as natural numbers, `oob` before any
  write; no fuel. Facts: `L/Blocks.lean`.
* **Operands** must be `Expr.isOpnd` (a local, a global, a length, an imm32 constant; `WF`), so the
  code reads them in place and evaluating them cannot fail.
* **Code** (`Compiler/Compile.lean`): bounds checks with `cmp`/`sub` only (`n ≤ len`,
  `o ≤ len - n`; `ev_addRI` leaves the flags unspecified, so a carry check would need a new
  flag model). Loops: `copy64Loop`/`copy8wLoop` 6 instructions per element, `scanLoop` 7 per
  byte (the class byte comes from the table in constant data at `[r15 + rdx + off]`); the end
  of a copy in temporary `0`; `x := rax` after a scan (`storeRax`).
* **Proofs** (`Compiler/SimBlock.lean`, `sim_copy64`, `sim_copy8w`, `sim_scan8`; `ld8x8` in
  `sim_expr`): the loops by induction on the remaining iterations (`scan_loop`, `copy64_loop`,
  `copy8w_loop`) with `Inv` carried through `Inv.store64`; helper lemmas `sim_lenChk`,
  `sim_warrDesc` (tier descriptor, `DescAt`), `sim_wordPtr`, `sim_endPtr64/8`, `sim_storeTmp`,
  `sim_srcLen`/`sim_srcBase` (`SrcAt`: the bytes, outside every word array and the stack);
  new step lemmas `ev_movzxM`, `ev_movzxS`, `ev_movzxR`, `ev_ld64b`; `rdW_bytes` (an 8-byte load
  is the little-endian word). No `sorry`; `compile_correct`'s statement unchanged.
* **Arms elsewhere**: WF/WFFast (class table and `rom` bytes via `Stmt.roms`), write sets
  (`WriteSet`, `WriteSetSplit`, `LeafFrame`, `RecGenSpec25`), `FuelMono`, `PureEval`, `Preserve`,
  `CallF`, `ConsLib`/`SlotGrow` renamings, `Rom/Subst` (`PB` → constant bytes), `Rom/Stage`,
  `PinRead.toPB`, `Checker/Prelude.preS` + `PreludeSim` (the prelude copies read their scans
  from `preludeBytes`), E2E `Ser`/`Trace`.
* **ModelGen**: no arms yet (no `l_model` group uses a block; lane lmretro is changing
  `ModelGen.lean`). To do with the first `l_model`'d user: `copy!` → guard + `m.copy64 …`,
  `scan!` → `UInt64.ofNat (scanN …)`, `le64!` → `le64 …`.
