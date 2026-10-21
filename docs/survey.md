# con-agua survey (2026-10-21)

Reference clones (read-only): `_tmp/ref/{con-leche,con-ron,kraken,vcgen-showcase}`.
Paths below are relative to `_tmp/ref/` unless absolute. Revisions:
con-leche `103562b` (2026-10-17, this is also con-ron's pinned dep), con-ron `4c9eaf7`
(2026-10-17), kraken `72f3a7a` (2026-10-20, "wp-foundation" PR #165), vcgen-showcase `e7deda3`.

Scratch build experiments: `/home/joachim/con-agua/_tmp/try/` (kraken-n0921, scan-n0921, vc/T.lean).

---------------------------------------------------------------------------------------------
## 1. Input parsing in con-ron / con-leche

### 1.1 Rust (con-ron)

`con-ron/crates/con-ron-core/src/frontend/` (11 234 lines total):

| file | lines | role |
|---|---:|---|
| `scan_fast.rs` | 4513 | **the byte recogniser**: port of con-leche `Scan/Fast.lean`; one NDJSON line -> `LineRec` |
| `scan_types.rs` | 679 | `ScanRes`, `ScanErr`, `ErrTag`, `Key`, record types (`LineRec`, `ExprRec`, ...) |
| `export_c.rs` | 2808 | applying records into the store; `apply_line` :2009, `apply_final_line` :2049, `feed_chunk` :2078, `chunk_step` :2204, `parse_source` :2315 |
| `text.rs`, `nat_decimal.rs` | 185, 181 | UTF-8 / code-point strings, decimal digits -> `ron::Nat` |
| `prepare.rs`, `prelude*.rs`, `nat_op_ground.rs` | | later stages, not parsing |

It is not a general JSON parser. It is a recogniser for the lean4export dialect only. There is
no DOM and no key lookup: a key is classified by its first byte plus its length, and each
record kind has its own slot loop with a `seen` bitmask. `scan_fast.rs` has no closures, and it
is the one place where con-ron uses `while` loops (Aeneas turns them back into recursion). Small
leaf functions, with their line numbers in `scan_fast.rs`:

* `byte_at` :85, `is_ws` :96, `is_digit` :101
* `skip_ws` :107, `skip_digits` :118, `match_lit` :132
* `key_end` :149, `key_at` :183, `value_at` :704
* `scan_bool` :716, `num_end` :733, `read_nat_at` :754
* `str_close` :792, `has_escape` :818, `utf8_decode` :917, `unescape` :1069
* `scan_string` :1087, `skip_braced` :1283, `next_member` :1339
* the record loops: `scan_*_loop`, from :1434 to :3724
* `scan_line_loop` :3767, `scan_line_fwd` :4044, `newline_from` :4072

The driver reads the file in 4 MiB chunks through `HandleSource`
(`crates/con-ron/src/driver.rs:931-976`). This reading is trusted (`ReadsAs`).

### 1.2 Lean models: the scanner is con-leche's own and is not twinned

* **con-leche** `ConLeche/Frontend/Scan/` holds four pieces:
  * `Types.lean` (434 lines): `ScanErr` :92, `ScanRes` :124 (`.ok val pos | .err e`), the records,
    `LineRec` :231, `IdTable`.
  * `Fast.lean` (2612 lines): the executed recogniser. It is total and first-order, recurses
    on the position (`termination_by b.size - i.toNat`), and works over
    `(b : @& ByteArray) (i : USize)`.
  * `Naive.lean` (794 lines): the specification over `List UInt8`, written with `NRes`.
  * `Equiv.lean` plus `Equiv/{Kit,Scalars,Keys,Objects}.lean`: the proof that the two agree.
    It is `@[csimp] scanLineSpec_eq_scanLineFwd` at `Equiv.lean:1002`, with per-function
    equalities such as `skipWs_eq` (`Equiv/Scalars.lean:23`), `strClose_eq` (`Scalars.lean:343`)
    and `skipBraced_eq` (`Equiv/Keys.lean:3692`).
  * Imports: `Std.Data.HashMap.{Basic,Lemmas}` only. The whole `Scan/` directory builds standalone
    in about 40 s (checked on v4.35.0 and on nightly-2026-09-21, see §4).
* **The con-ron arena twin (B)** reuses `scanLineFwd` verbatim. The `Arena/Frontend/ExportC.lean`
  header (lines 13-28) says "The scanner is NOT twinned" and imports `ConLeche.Frontend.Scan.Fast`.
  The arena-tier functions that read bytes are in `proof/ConRon/Arena/Frontend/ExportC.lean`,
  all in the monad `AM`:
  * `applyFinalLine` :511
  * `feedChunk` :527 — `StateD → ByteArray → USize → Nat → AM (Except (CheckError×Nat) (StateD×Nat×USize))`
  * `parseBytes` :564, `chunkStep` :580, `chunkFinish` :592, `parseChunksGo` :607, `parseChunks` :617
* **Theorem 1 (twin ⊑ con-leche) for the frontend** is `proof/ConRon/Bridge/Frontend/{Lines,Chunks}.lean`,
  for example `feedChunk_run` at `Chunks.lean:367` and `parseChunks_run` at :579. These proofs are
  written about runs (`hrun : f … s = .ok (x, s')`), not with vcgen. The scanner itself needs
  nothing in Theorem 1, because both sides call the same `scanLineFwd` (`Lines.lean` header).
* **Theorem 2 (Aeneas Rust ⊑ twin) for the scanner** is `proof/ConRon/Refine2/Frontend/Scan/*.lean`
  (17 k lines). The lemmas are stated port-left / con-leche-right with `= ok` hypotheses:
  * `Kit.lean`: `skip_ws_refines` :333, `newline_from_refines` :2150, `str_close_refines` :2358,
    `skip_braced_refines` :2983. The list is in the header of `Kit.lean:16-52`.
  * `Line.lean:3227`: `scan_line_fwd_refines`. It is assembled in `Scan/Spec.lean` (`scanSpec`).
  * The relation is `absPos j = skipWs (absBytes b) (absPos i)`, where `absBytes : Slice U8 → ByteArray`
    and `absPos : Usize → USize`.
  * The Aeneas output, `proof/ConRon/Generated/Funs.lean`, is a good picture of what an
    "L denotation" looks like. Example: `frontend.scan_fast.skip_braced_loop` at :78120, a
    `Result` monad with `Slice.index_usize` and checked `+`/`-`.
  * The proofs are manual inductions on fuel `f ≥ len - i` with `bind_eq_ok_iff`
    (for example `str_close_loop_refines`, `Kit.lean:2271-2356`).

### 1.3 Is there a byte-level JSON validator in Lean?

* There is no general JSON validator over bytes in con-leche or con-ron. Lean core's
  `Lean.Data.Json.Parser` is a `String`/`Parsec` parser; it has no proofs and is not used here.
* The closest thing to a generic JSON validator is **`skipBraced`**:
  * con-leche `Scan/Fast.lean:741`, `skipBraced (b : @& ByteArray) (i : USize) (depth : Nat) : USize`.
  * It skips a bracket- and string-balanced `{…}`/`[…]` value, stepping over strings via
    `strClose` :504.
  * It returns `0` when the value does not close or a newline comes first.
  * It is used to skip the `meta` header line (`Fast.lean:2561`).
  * Its naive spec is `naiveSkipBraced` (`Naive.lean:305`) and its equality is `skipBraced_eq`.
* The line structure is checked by `scanLineFwd` (`Fast.lean:2587`):
  * it skips whitespace, reads `{…}` with `scanLineLoop` and then requires `\n` (`.trailing` otherwise);
  * it returns continue position `0` for an unterminated last line;
  * `newlineFrom` (:2604) tells a malformed line from one cut at the chunk end.

### 1.4 Recommended spike target

**Stage A, the actual first spike: `skipBraced` (with `strClose`), then `skipWs` and `newlineFrom`.**

| | Rust | Lean model (= the arena tier, reused) | Theorem-2 lemma in con-ron |
|---|---|---|---|
| A1 | `str_close` `scan_fast.rs:792` | `ConLeche.Frontend.strClose : ByteArray → USize → USize` `Fast.lean:504` | `str_close_refines` `Kit.lean:2358` |
| A2 | `skip_braced` `scan_fast.rs:1283` | `ConLeche.Frontend.skipBraced : ByteArray → USize → Nat → USize` `Fast.lean:741` | `skip_braced_refines` `Kit.lean:2983` |
| A3 | `skip_ws` :107, `newline_from` :4072 | `skipWs` :85, `newlineFrom` :2604 | :333, :2150 |

Why these functions:
* They are pure functions (bytes, position) → position with no allocation and no records.
  They fit "parse JSON without storing the result" exactly: the result is "where the balanced
  value ends, or 0".
* They still exercise everything the L → x64 compiler needs:
  * byte loads `b[i]` with base+index addressing;
  * a 64-bit counter (`depth`, which can overflow and panic in Rust: a partial-correctness Err);
  * nested `if` chains and a `while` loop;
  * a call to a second function (`str_close`) with an early `return`.
* The spec on the Lean side already exists, is executed by both con-leche and con-ron, and has a
  naive `List UInt8` spec proven equal to it. A refinement `L ⊑ skipBraced` therefore plugs
  directly into con-ron's chain.
* Shape of the L-level theorem, in the Bridge/Specs style:

  ```lean
  ⦃fun m => m = m₀ ∧ m₀.arr 0 = b.data⦄ L.skip_braced i d
  ⦃fun r m' => m' = m₀ ∧ r = (skipBraced b i d).toUInt64; ⊤⦄
  ```

  The side conditions are `b.size < 2^64`, `i.toNat ≤ b.size` and `d < 2^64`.

**Stage B, the "NDJSON line structure" step.** This is a loop over lines with a line validator,
with no records built.
* There is no ready-made Lean function for it. The nearest are con-leche
  `ConLeche/Frontend/ExportC.lean:549` `feedChunk` and the arena `feedChunk`
  (`Arena/Frontend/ExportC.lean:527`). Both apply each record (`applyLine`), so they are not
  storage-free.
* So we would define our own small spec, `scanLinesSpec b i n`. It is `feedChunk` with
  `applyLine` replaced by `pure`, using the result of `scanLineFwd` erased to
  ok/err/offset/next-pos.
* L would then implement a validating-only `scan_line_fwd`. The Rust counterpart is
  `scan_line_fwd` and the `scan_*_loop` family. Note that even validation-only needs
  `unescape`/UTF-8 checking: `scanString` (`Fast.lean:627`) fails on bad escapes and bad UTF-8
  via `String.fromUTF8?`.
* A full port is about 4.5 k lines of Rust, so do it per record kind after stage A. A cheap
  intermediate is a "meta header + blank lines" validator: `skipWs`, `{`, `skipBraced`,
  `skipWs`, `\n`. Its spec is composed from con-leche's functions.

---------------------------------------------------------------------------------------------
## 2. con-ron's arena tier (B) and Theorem 1

* **Monad** (`proof/ConRon/Arena/Monad.lean:139`): `abbrev AM := StateT AState (Except CheckError)`.
  * `AState` is at :119: `store : EStore`, `memos`, `caches`, `pins`.
  * There is one failure primitive, `fail` (:144).
  * There is no `IO`, no `partial` and no typeclass-polymorphic body, and fuel is an explicit `Nat`.
  * OVERVIEW.md §7.2 says `ReaderT PersTier (StateT …)`. The code takes the tier as an explicit
    argument (`hinst emptyTier …` in Capstone).
* **The store** (`Arena/Store.lean`, `Handle.lean`): per-constructor arrays plus hash-cons
  tables, with 32-bit handles. `denoteE` (`Arena/Denote.lean:181`) reads a handle back into a
  con-leche `Expr`. The invariant `StoreWF` is in `Arena/WF.lean`.
* **The spec shape** (`Bridge/Specs.lean:1-61`, the "seven rules"):
  `⦃fun s => s = s₀⦄ f args ⦃fun r s' => Post s₀ r s'; ⊤⦄`.
  * Real preconditions are ordinary hypotheses.
  * `⊤` as the exception post means partial correctness. (`⦃P⦄x⦃Q⦄` defaults to `⊥`, which is
    total correctness.)
  * There is no `∃` in posts, answers are named relations, and there is one failure primitive.
  * Bridge between triples and runs (`Bridge/Rel.lean:47-65`):
    * `AM.of_run`: triple + `prog.run s = .ok (a,s')` ⇒ `Q a s'`;
    * `AM.triple_of_run`: the converse.

    Both go through `Std.WP.StateT.wp_apply_eq`.
* **Representative example** (`Bridge/Specs.lean:214-217`). The program, `Arena/Monad.lean`:

  ```lean
  -- program (Arena/Monad.lean): def view (h : EIdx) : AM ENodeView := …
  @[spec] theorem view_spec (s₀ : AState) (h : EIdx) :
      ⦃fun s => s = s₀⦄ view h
      ⦃fun v s' => s' = s₀ ∧ s₀.store.view h = some v; ⊤⦄ := by
    vcgen [view] with finish
  ```

  With callee specs and grind vocabulary (`Specs.lean:425-435`, `internLamE_spec_view`):

  ```lean
    sym only [bridge_grind, → EStore.view_of_findBind (tag := ETag.lam) (htag := rfl),
        denoteE_view_eq, EStore.internBind_spec (tag := ETag.lam) (htag := rfl)] =>
      vcgen [internLamE] <;> finish
  ```

  The header needs `import Std.WP`, `import Std.Tactic.Do` ("the vcgen syntax on v4.35.0;
  lean4#15290 moves it to `Std.WP.Tactic`"), `set_option experimental.vcgen true`,
  `open Std.WP`, `open scoped Lean.Order` (`Specs.lean:68-79`).
  * The grind attribute is `register_grind_attr bridge_grind` in `Bridge/GrindAttr.lean`, and the
    vocabulary is in `Bridge/Grind.lean`.
  * The matcher-auxiliary clash workaround is `Specs.lean:83-115`.
* **Spec grades** (OVERVIEW §7.3): `PSpec` (pure grade, invariant `StateOK`, frame `PStep`) and
  `CSpec` (core grade). An example is `structPsAt_spec` in `Bridge/Inductives/StructParts.lean:118-164`.
* **Nat limbs.**
  * Rust `crates/con-ron-core/src/ron/nat.rs` (1080 lines): `pub struct Nat { pub limbs: Vec<u64> }`
    :57, little-endian, normalised (no trailing zero limb).
  * Every pass is an index-carrying `*_from` recursion; there are no loops and no `&mut`.
  * Operations: `add` :235, `sub` :270, `mul` :525, `div_mod` :570, `gcd` :644, `land`/`lor`/`xor`,
    `shift_*`, `hash64` :718.
  * Lean `proof/ConRon/Refine/Nat.lean` (2411 lines):
    * `limbsToNat : List U64 → Nat` (`x :: r ↦ x.val + 2^64 * limbsToNat r`) :8, `toNat` :12;
    * `LimbsWF`/`NatWF` :14-16 (last limb ≠ 0);
    * `*_refines` lemmas (`div_mod_refines` :2264, `gcd_refines` :2354) over the Aeneas model.
  * It uses `ring` etc., so it needs Mathlib via Aeneas.
  * The **twin** uses Lean's `Nat` directly; limbs appear only in Theorem 2.

---------------------------------------------------------------------------------------------
## 3. Kraken (x64 semantics)

* **Lake:** `kraken/lakefile.toml`. There are **no dependencies (no Mathlib)**, `requiresModuleSystem = true`,
  `autoImplicit = false`.
  * Libraries: `Kraken` (globs `Kraken.*`) and `KrakenAArch64`. Executables: `krakenrunner_x64`,
    `krakenrunner_aarch64`, `att2intel`.
  * About 6.6 k lines for x64 plus the shared files; 43 modules in `Kraken/`.
  * **Build time:** `lake build Kraken` takes **8-11 s cold on this 96-core machine**, on all of
    nightly-2026-09-21, nightly-2026-09-24 and v4.35.0. It succeeds on all three
    (`_tmp/try/kraken-n0921`).
* **Syntax** (`Kraken/X64/Syntax.lean`):
  * `Reg64` (16 GPRs) and `Reg : Width → Type` (`low r w`, `ah..dh`), with `Width = W8|W16|W32|W64`.
  * `AddrExpr { base : Option RegOrRip, idx : Option {reg, scale : Width}, disp : ConstExpr }`.
    This is base + index*{1,2,4,8} + disp.
  * `ConstExpr`: label, int64, add/sub, before/after the current instruction.
  * Operand types: `RegOrMem w`, `Operand w` (adds `imm`), `CondCode` (16 codes plus aliases `e/ne/b/ae`).
  * `Operation w`:
    * moves: mov, movsx, movzx, push, pop, setcc, cmovcc, lea;
    * arithmetic: add, adc, adcx, adox, inc, dec, neg, sub, sbb, cmp, mul, mulx, imul1, imul;
    * logic and shifts: test, and, not, or, xor, shl, shr, sar, shld, shrd, rol, ror, rcl, rcr, bswap;
    * control: **jcc (cc) (label)**, **jmp RelRegOrMem**, **call RelRegOrMem**, **ret**, nop, nopalign.
  * Plus some SSE/AVX.
  * `Instr.regular (address_size) (operation_size) (op)`, `Directive = instr | label | byteArray`,
    **`abbrev Program := List Directive`**.

  This is everything a naive compiler needs. There is **no `syscall`, no `div`/`idiv`, no `rep`/string
  instructions**, and no bss/data (no mutable globals). I/O therefore has to sit in a trusted
  harness outside the model.
* **State** (`Kraken/X64/Semantics.lean:226-282`):
  * `MachineData { regs : Reg64s, zmms, status : StatusFlags, dmem : DataMem }` and
    `MachineState { data, pc : Int64 }`.
  * `inductive Effects`: `done`, `unimplemented`, `gp_unaligned`, `nonmem_load/store`,
    `undefined` (nondeterministic values, for example undefined flags), `require_{read,write,exec}_access`.
  * The semantics is written in CPS over `Effects`.
* **Memory** (`Kraken/Mem.lean`):
  * `abbrev Mem w := ExtHashMap (BitVec w) UInt8`, `DataMem := Mem 64`, a partial byte map.
    `Mem.loadInt`/`storeInt` are little-endian.
  * A load or store outside the map's domain becomes `nonmem_load`/`nonmem_store`, which
    `Effects.All` treats as `False`. So the domain is the memory the program owns.
  * Separation logic: `Kraken/Separation.lean` has `⋆` and `=⋆` over ExtHashMap.
    `Kraken/X64/Sep.lean` has the `@[kspec]` lemmas `store_sep`/`load_sep`, with
    `s.dmem =⋆ Eq (bs.At addr) ⋆ R`.
  * Implication for L: **arrays must be preallocated regions in dmem**, because nothing can grow
    the map. "Growable" therefore means a capacity fixed at start and an Err when it is exceeded.
* **Program to execution** (`Kraken/Layout.lean`, `Semantics.lean:786-851`):
  * `Layout { start : Int64, size : Nat → Nat }` turns a `Program` into an `Executable`
    (a `List (Sized Directive)` with addresses).
  * Labels are resolved by `Executable.labels` (address of the first matching label, otherwise `-1`).
  * `Executable.step` runs the directives at the pc; `straightline` runs from the pc onward.
  * `Effects.All post` and `step1 e s post := (e.step s .done).All post` are in `X64/OmniSemantics.lean`.
  * `Eventually trans post s` (`Kraken/OmniSemantics.lean`) is the least fixpoint "inevitably
    reaches", with `step_cps`, `eventually_trans` and `reg_dec_loop` (a loop-to-0 invariant rule).
  * Proofs are layout-generic (`[layout : Layout]`), so they hold for any concrete encoding sizes
    the assembler picks.
* **`Kraken/X64/WP/*`** (new; merged 2026-10-20):
  * `Host.lean`: `class Host { prog : Program, layout, zero_inert, addr_determines_offset }`,
    with `Host.exe` and `Host.addrOf k`.
  * `Basic.lean`: `Program.wp [Host] (p : Program) (Q : MachineData → Prop) (E : Int64 → MachineData → Prop) (s) : Prop`.
    Its meaning: for every infix position `k` of `p` in `Host.prog`, the state
    `Eventually (step1 Host.exe)` reaches either the fall-through address with `Q`, or some pc
    with `E` (a jump out, for example to a call target).
  * Lemmas: `Program.wp_mono`, `wp_cons`, `Host.eventually_of_interp`, and soundness
    `Program.step1_of_wp_at` / `step1_of_wp`.
  * The comment calls it "the bridge to `Std.WP` and thus `vcgen`", but **no `WPMonad`/`Std.WP`
    instance or vcgen use exists yet**. No example or file uses `Program.wp`, and there are no
    call/ret or loop composition lemmas yet. We would build those, or wait for upstream.
* **Examples and proof style** (`Kraken/X64/Examples/Examples.lean`, `IncrementDMA.lean`, `IncrementMMIO.lean`):
  * Programs are written with the `parse("…AT&T…")` term macro (`Kraken/X64/Parser*`).
  * Proofs follow the pattern `apply step_cps; kprologue p with s; sym => kstep; tactic => … grind / bv_decide`.
    `kstep` is a `grind`/`SymM` tactic in `Kraken/Tactics.lean:230`.
  * Examples: `swap_correct`, a jnz example, `sib_example_correct` (base+index*scale),
    `alu_mem_example`, `dynamic_stack_example`.
  * The loop example `p3_correct` is `sorry` (its old proof is commented out). So **loop proofs
    are not mature yet**.
* **Printing and running:**
  * `Kraken/X64/PrintATT.lean` (`toATT`, which round-trips with `parse`) and `PrintIntel.lean`
    print real assembly text; `Att2Intel.lean` is an executable.
  * There is **no machine-code encoder**: real bytes come from an external assembler (gas/clang).
    That is trusted, mitigated by the layout-generic proofs.
  * `Executable.eval` (`Semantics.lean:823`, `partial`) is a concrete interpreter, used with
    `#eval` and `Program.fakeLayout`. See the `#guard_msgs` example at :853.
  * `KrakenRunnerX64.lean` runs a `.S` file through the semantics and prints registers/flags as
    JSON, with no memory tracking. It also has fuzzer modes.
  * `Kraken/Fuzzer.lean` is differential-testing infrastructure: it compares against a real CPU,
    and `filterAssemblable` uses the system assembler.

---------------------------------------------------------------------------------------------
## 4. Toolchains

| repo | `lean-toolchain` | installed in elan? |
|---|---|---|
| con-leche | `leanprover/lean4:v4.35.0` | yes |
| con-ron (`proof/lean-toolchain`) | `leanprover/lean4:v4.35.0` | yes |
| kraken | `leanprover/lean4:nightly-2026-09-21` (= 4.36.0-nightly) | **installed now** (I ran `elan toolchain install`; it was missing) |
| vcgen-showcase | `leanprover/lean4-nightly:nightly-2026-08-18` (README says 07-15, stale) | no |

Other installed nightlies: 04-29, 08-20, 08-21, 09-10, 09-24, 10-14, 10-15.

Checks (`_tmp/try/`):
* **vcgen + `Std.WP` works on v4.35.0, on nightly-2026-09-21 and on nightly-2026-10-15.** I ran
  `_tmp/try/vc/T.lean`: an `AM`-style `StateT Nat (Except String)` triple
  `⦃fun s => s = s₀⦄ incr k ⦃fun _ s' => s' = s₀ + k; ⊤⦄ := by vcgen [incr] with finish`,
  with `import Std.WP` + `import Std.Tactic.Do` + `set_option experimental.vcgen true`.
  * On 10-15 there is additionally `Std/WP/Tactic.lean` (lean4#15290). `Std/WP/EPostSlot.lean`
    appears from 09-24 on.
* **Kraken `72f3a7a` builds on v4.35.0 as well as on its own nightly.**
* **con-leche's `ConLeche/Frontend/Scan/{Types,Fast,Naive,Equiv/*}` builds on nightly-2026-09-21**
  (and on v4.35.0), in about 40 s.

**Recommendation: use Kraken's `leanprover/lean4:nightly-2026-09-21`.**
* Kraken is the dependency most tied to toolchain features: `sym =>`, `kstep` on `SymM`, and the
  new WP layer that will move to `Std.WP`. Its upstream will keep tracking nightlies.
* vcgen works there.
* The con-leche parts we need are core-only and build there.
* v4.35.0 is the fallback if con-leche alignment ever matters more. Kraken HEAD builds on it today.

**Dependencies:**
* `kraken`: lake `[[require]] git = "https://github.com/AeneasVerif/kraken"` (the clone's origin, checked),
  `rev = "72f3a7a…"`. It has no transitive dependencies.
* `con-leche`: lake `[[require]] git = "https://github.com/leanprover/con-leche"`,
  `rev = "103562ba1c46cee26f134d0435765adcb5d22486"` (the same pin as con-ron).
  * con-leche has no dependencies of its own, and lake builds only the imported modules.
  * Its `lean-toolchain` mismatch only produces a warning.
  * Risk: an import outside `Scan/` might not build on the nightly. Mitigation: import only
    `ConLeche.Frontend.Scan.*`, or vendor those files.
  * I did not test it as an actual git dependency; I only did a standalone copy build.
* **con-ron is not importable cheaply.**
  * Its lakefile requires `aeneas` at a local path, `../_tmp/aeneas-lean-v4.35.0`, patched by
    `scripts/setup-aeneas-lean.sh`.
  * Aeneas pulls in Mathlib, and everything is pinned to v4.35.0.
  * The `Arena/**` twin would also drag in con-leche's kernel.
  * For the spike we don't need it: the arena-tier byte functions *are* con-leche's `Scan/Fast`.
  * Later, for the stores, copy the needed `Arena/*` definitions (they import con-leche plus Std
    only, with no Aeneas). Alternatively, depend on con-ron with a lake lib that roots only
    `ConRonArena`. That still needs the Aeneas require to resolve, so copying is simpler.

---------------------------------------------------------------------------------------------
## 5. Proof-style notes (vcgen + grind)

* **con-leche `CLAUDE.md:40-55`** ("The cached simulation proofs"):
  * one `sym only [conleche_grind, …] => vcgen [f, …] <;> finish` per arm or induction case;
  * callee specs and IHs go in vcgen's list as terms, never as `have`s;
  * one unconditional unfolding equation per function;
  * the pure side's nested `match` never reaches grind: one guarded equation per arm;
  * name every `fun`/mode gate; no `∃`/disjunction/`fun` in posts;
  * recursive triples by `induction`, not by recursive pattern matching;
  * every raised `finish` limit carries a comment.
* **con-leche `DESIGN.md:106147-106410`** (task #356, the spike and the conversion):
  * five rules, the numbers (proof lines −63 %, elaboration 0.70×), and vcgen automation gaps
    with workarounds;
  * the gaps: a conditional fall-through equation gives "No spec found"; an `ite`-headed equation
    is ignored; specs through projections must be restated; a pattern-lambda elaborated in another
    module has another matcher; `modifyGet fun s => match …` is opaque;
  * a `Std.Do` triple gives "could not determine the program type", so use `Std.WP` triples.
* **con-ron `CLAUDE.md:190-210`**: Theorem 1 VCs by `vcgen` + `grind` inside `SymM`.
  * Nothing goes between `vcgen` and `finish`, and there is no positional addressing (`case vcN`,
    `rename_i`).
  * The mathematics is in `@[bridge_grind]` lemmas. Grind-shaped means every variable is in a
    pattern and facts are equations over named projections.
  * Real vcgen/grind limits get reproducers in `_tmp/corpus/vcgen-grind/`.
  * DESIGN history: `con-ron/DESIGN.md` tasks #111 (:66631, mvcgen → vcgen), #116 (:67885), #121-#124 (:68466-69070).
* **`con-ron/proof/ConRon/Bridge/Specs.lean:1-61`**: the seven-rule spec template, quoted in §2.
* **`vcgen-showcase/README.md`**:
  * recipes: triples, `for`/`while` invariants (`inv1`, and `inv2` as the termination variant);
  * `Id.of_wp_run_eq` for pure-facing specs;
  * `StackMachine.lean` is a compiler-correctness example by induction with vcgen per case;
    relevant to our L → x64 compiler proof style, though over a toy stack machine.
* **Aeneas-style manual refinement** (`Refine2/Frontend/Scan/Kit.lean`) is the run-based fallback:
  fuel induction plus `bind_eq_ok_iff`. It was not converted to vcgen.
