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

(see below)
