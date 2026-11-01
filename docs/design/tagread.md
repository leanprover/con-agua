# Lane tagread: the tag read after con-ron #133

Task: win back the speed the two-shape handle word cost (lane ronsync, `docs/design/ronsync.md`
§4, §8: on Init +13.5 % instructions, wall +5.2 % at one thread, +2.8 % at 16, against master
860b0632; con-ron itself paid +1.65 %).

## 1. Where the instructions went

Master 7d1169fc against 860b0632 on Init (`_tmp/fixtures/init/init435.ndjson`, `perf stat -e
instructions:u`, one thread): 214.47 G → 243.44 G. A `perf record` per function (shares of the
total; the sampling is throttled, so only shares are compared) showed three causes:

* **The tag read itself.** `tagE` = `f + w·(4 − f)` compiles to 13 instructions (the code
  generator has no common subexpressions: `h` is read three times, `f` computed twice) where
  `h >> 28` was 2. 183 sites in `checker.s`, 135 of them a comparison with a literal.
* **Inlining.** The inliner takes leaves of at most 80 nodes (`Inline.lean`, `Stmt.size`).
  `tagE` has 19 nodes (`h >> 28`: 3), so `app_count` and `get_app_fn` (one `⟦e⟧.tag == 4`
  loop each) grew past the limit and became calls: 6.4 G instructions in functions that had
  none of their own before.
* **Frames.** `tagE`'s `mul` has a non-simple right operand, so every function reading a tag
  needs a frame temporary (`tempsE`) and a frame.

The rest is not in the readers: `app_find` runs the same 87 lines of code as before but more
often (the cons hashes are of words, and the words changed), as do other `*_find` probes and
`app_push`; this is the twin's layout and hash, mirrored.

## 2. Prototypes

`_tmp/tagread/proto/emit/Emit.lean` (not committed): rewrites `checkerProg` (reading the built
oleans) and runs the inliner and the compiler on it, so a variant's `checker.s` includes the
inlining effect, which a peephole on `checker.s` misses. Instructions on Init (G), each binary
accepting:

| variant | instr | vs master |
|---|---:|---:|
| master 7d1169fc | 243.44 | |
| literal tests `tag == k` as `(h >> 26) & 31 == k` (k ≠ 4), `tag == 4` as `14 < ((h >> 26) & 31 ^ 4) − 1` | 233.81 | −4.0 % |
| full tag by a table read `tagTbl[(h >> 26) & 31]` (`ldc`) | 229.02 | −5.9 % |
| both | 226.52 | −7.0 % |
| table read, `ldc` code without `lea` and without the (provably dead) bounds check | 222.94 | −8.4 % |
| both, same `ldc` code | 222.95 | −8.4 % |
| table read, `ldc` code, `idxGE` operands reordered | **221.70** | **−8.9 %** |

With the cheaper `ldc` code the literal tests gain nothing more (four instructions either way),
so they were not done: the L code, its 711 `evalE_tagE` uses and every refinement proof stay as
they are. A peephole prototype on `checker.s` alone (no inlining effect) had shown only −1.6 %
for the literal tests and −3.6 % for both: the inliner is a large part of the win.

## 3. The change

* **`tagE` (`L/TRec.lean`)**: `ldc tagTbl ((h >> 26) & 31)`, a 32-byte constant table indexed by
  the shape bit and the tag field (`0 … 15` for a narrow word, `4` for each of the sixteen wide
  values). Six nodes, no frame temporary. Its value is still `tagW` (`StoreFields.lean`), which
  stays the arithmetic form: `ldc_tagTbl`/`rdc_tagTbl` (the table read is `tagW`, on every word),
  from `tagTbl_getElem` (`decide` over the 32 entries) and `tagIx_toNat`; `evalE_tagE` and
  `Expr.pval_tagE` are now two-line `simp only`s. No other proof changed.
* **`idxGE`**: the same value with every right operand a constant or `h`
  (`(((h >> 30) & 1) · 0x3c000000 + 0x3ffffff) & h`), so it needs no frame temporary either;
  `idxG_eq` relates it to `idxG`, which is unchanged.
* **The compiler, `ldc` in the register generator (`gen`, `Compile.lean`)**: the byte load is
  addressed from `r15` directly (`movzx d, byte [r15 + d + off]`, `ldcA`; it was `lea` into a
  scratch register, then the load), and the bounds check (`chkI`) is emitted only when the
  bounds-check analysis cannot show the index below the string's length (`ctx.ck none i
  d.length`, the same `safeIdx` the array loads use: `(h >> 26) & 31` has bound 32). Proof:
  `gen_ldc` (`SimGen.lean`) rewritten for the new code (`ck_sound` for the dropped check,
  `ev_movzxS` for the load), `chkI_spec` (`Sim32.lean`) beside `chkR_spec`. The fallback
  `compileE` keeps its code.

L's semantics and every L function are unchanged, so the twin relation and the deviations are
untouched (no row in `docs/deviations.md`); Audit and Final statements unchanged.

## 4. Codegen notes (asked)

* No common subexpressions: an expression tree is evaluated as written, each `var` read once per
  occurrence (from its register, or the stack). A reader that mentions `h` twice costs two reads;
  hence the table.
* `idxW` is one `and`, `idxA` two (`lea` + `and`), `idxG` five; `idxA` cannot be one operation
  (a narrow word must read past the `app` array), `idxG` only runs in the derived reads' `app` and
  `param` arms.

## 5. Numbers
