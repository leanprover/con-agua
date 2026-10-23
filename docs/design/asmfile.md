# Lane asmfile: the committed assembler file, parsed at elaboration time

(journal; started 2026-10-23 20:16 UTC)

## Goal

The generated assembly is committed (`asm/checker.s`: entry stub, trampoline, the checker's
functions, the data symbols; exactly what `harness/main.c` is assembled with), and the final
theorems are about that file: a term elaborator `include_asm "…"` parses it when the module is
elaborated, and the kernel checks that its code is the compiler's output. con-agua then builds
from the repository with a C compiler and an assembler alone; the printer leaves the trusted base,
the parser enters it.

## Design (prototype on branch `asmfile`)

```
asm/checker.s ──include_asm (TRUSTED: Parse + Term + Include)──> checkerFile : Program
                                                                     │  kernel, structural (1 s)
compileProg checkerTab checkerProg "check" ──asm_lit (kernel, per function)──> checkerAsm
checkerFile_eq : checkerFile = checkerStub ++ compileProg checkerTab checkerProg "check"
checkerFile_accepts … (hcode : Code checkerFile k0) …  (AsmFinal; via Code.right)
```

* **Parser** `ConAgua/AsmFile/Parse.lean` (trusted, ~200 lines, `parseAsmFile : String → Except
  String AsmFile`): line based; accepts exactly the subset the printer writes (`.text`,
  `.globl`, `.section .rodata`/`.note.GNU-stack`, labels, 20 mnemonics, 64-bit registers, `$INT`,
  `INT(%B[,%I,S])`, branch targets, data lines `NAME: .quad/.byte …`) and rejects everything
  else, with the line number. Choices that follow `as`: decimal integers only, no leading zero
  (`as` reads `010` as octal), signed 64-bit range; `.text` after another section rejected (the
  code is one contiguous run); a branch `jmp/call NAME` is relative (`.rel (.sub (.label NAME)
  .after_current_instruction)`, Kraken's parser's reading); only the condition-code spellings
  Kraken's printer uses. The `.text` section is the `Program`; data lines are returned, not code.
  On the checker's file it agrees with Kraken's own parser (`Kraken.X64.Parser.parse`, 1225 lines,
  general) directive for directive; ours is smaller and stricter, so it is the one we trust.
* **Term** `ConAgua/AsmFile/Term.lean` (trusted): `toExpr` of each directive, with two
  value-preserving rewrites so that the term is the one `asm_lit` builds from the compiler's
  evaluation: a label string becomes `lbl f n m` / `fnL g` / `errorL` … only if that term
  evaluates (run here) to the same string, an `Int64` literal becomes `Int64.ofInt i`. `asm_lit`
  now builds its literals with these same functions (moved out of `AsmLit.lean`).
  Why not plain string labels: the kernel needs **26 ms per label** to check `lbl "f" n "X" =
  ".Lca_f_…X"` (`String.append` on byte arrays; 1000 labels: 26 s; a `String.ofList` variant: 21
  ms); the file has 37 061 label occurrences (17 195 distinct), i.e. 8–16 CPU-minutes.
* **Elaborator** `ConAgua/AsmFile/Include.lean` (trusted): `include_asm "path"` (path relative to the
  Lean file, as `include_str`) reads, parses, cuts the code before `ca_enter:` and each `ca_f_g:`
  (value-preserving: the term is `s₀ ++ (s₁ ++ … ++ [])`, the shape of `asm_lit`'s `checkerAsm`),
  and as a check (not needed for soundness) prints the parsed code again with Kraken's `toATT` and
  compares with the file's `.text` lines (parse ∘ print = id on the file; rejects e.g. `jc`).
* **`ConAguaAsm/Checker.lean`**: `noncomputable def checkerFile : Program := include_asm
  "../asm/checker.s"` — the one line an auditor reads. Not compiled (nothing runs it).
* **Equality** `ConAgua/AsmFile/Eq.lean` (untrusted) `asm_file_eq checkerFile_eq : checkerFile =
  checkerStub ++ checkerAsm via checkerAsm_eq` in `ConAgua/Checker/AsmFileEq.lean`: declares
  `checkerStub` (the file's code before the trampoline, a literal), `checkerFile_eq.lit :
  checkerFile = checkerStub ++ checkerAsm` by `Eq.refl` (structural: same terms after delta), and
  `checkerFile_eq : checkerFile = checkerStub ++ compileProg checkerTab checkerProg "check"`.
  Before the kernel, the segments are compared as `Expr`s, so a stale or misprinted file fails
  with `the file differs from L.Checker.checkerAsm in segment 1021 (nat_op_deps); regenerate it`.
* **Final theorems** (`Checker/AsmFinal.lean`): `checkerFile_accepts`, `checkerFile_model_exists`,
  `checkerFile_no_False` with `hcode : Code checkerFile k0`; `code_of_checkerFile` gives `Code
  checkerAsm (k0 + checkerStub.length)` (`Code.right`), then `checkerAsm_accepts` as before.
  `Final/Remaining.lean`: `checkerFile_accepts_remaining` (renamed; `Census/Main.lean` and
  `census.py` follow). Axioms unchanged (`propext`, `Classical.choice`, `Quot.sound`).
* **The stub is in the file but not yet in the proof**: the theorems start at `ca_enter`
  (`HarnessCall`), as before; lane `abi` proves the stub establishes the layout. The kernel check
  `abiStub checkerTab = checkerStub` is not in the build: plain `Eq.refl` overflows the kernel's
  stack (the kernel compares lists element by element, recursively: `List.replicate 20000 0 ++ [] =
  …` overflows, 3000 is fine; the stub has 10 380 directives); split along the literal's tree
  (`t = take k t ++ drop k t`, `Eq.refl` on ≤ 2600 elements) it works but costs **22 s and +4.5 GB**
  (peak 6.8 GB), almost all evaluating the 4646 ROM words (`romWordList`, well-founded recursion,
  `UInt64` shifts: 17 s for the words alone). Options for lane `abi`: prove the stub's behaviour
  about the literal `checkerStub` directly, or make the ROM words cheap for the kernel (a literal
  word list in `tab_lit%`, as `romLen`), then add the check. The chunked proof (meta code; `appC`
  is `HAppend.hAppend` at `Program`, `litLen` counts a literal's elements):
  ```
  partial def listEqProof (leaf : Nat) (t lit : Expr) : Expr :=
    let refl := mkApp2 (mkConst ``Eq.refl [1]) progTy t
    match appendArgs? lit with
    | some (a, b) =>
      if litLen lit ≤ leaf then refl else
      let k := mkRawNatLit (litLen a)
      let tk := mkApp3 (mkConst ``List.take [0]) dirTy k t
      let td := mkApp3 (mkConst ``List.drop [0]) dirTy k t
      let split := appC.app tk |>.app td
      let hs := mkApp4 (mkConst ``Eq.symm [1]) progTy split t
        (mkApp3 (mkConst ``List.take_append_drop [0]) dirTy k t)
      let hc := mkApp8 (mkConst ``congr [1, 1]) progTy progTy (appC.app tk) (appC.app a) td b
        (mkApp6 (mkConst ``congrArg [1, 1]) progTy progTo tk a appC (listEqProof leaf tk a))
        (listEqProof leaf td b)
      mkApp6 (mkConst ``Eq.trans [1]) progTy t split lit hs hc
    | none => refl
  ```
* **Lake**: `lakefile.toml` has `[[input_file]] checker_s` (`asm/checker.s`, `text = true`) and a
  library `ConAguaAsm` (`globs = ["ConAguaAsm.+"]`, `needs = ["checker_s"]`) holding only
  `ConAguaAsm.Checker`. Lake mixes a library's `needs` into every one of its modules' traces
  (`Module.recFetchPreSetup`, `depTrace := … extraDepJob.getTrace`), so the file's content hash is
  part of the module's input hash, hence of the shared artifact cache's key (seen in the trace:
  `["ConAgua/ConAguaAsm:extraDep", [… ["…/asm/checker.s", "f9755464d554b7be"]]]`); a separate
  library because a `needs` on `ConAgua` would rebuild all 1800 modules on every change of the
  file. `include_str` itself is not tracked by Lake at all (a plain `IO.FS.readFile`). Checked: a
  changed file rebuilds `ConAguaAsm.Checker` (8.9 s); reverting it restores from the cache.
  `scripts/lake` snapshots everything under `asm/` too (the cache incident's time-of-check gap
  applies to the file as to a source: Lean reads it when the module is compiled) and, on a change
  during a build, deletes the local state of every `ConAguaAsm` module.
* **Generator** `scripts/asm_file.py [--check] [--no-build]`: runs `ConAgua/Checker/AsmEmit.lean`
  (now `asmTextAbi checkerTab (compileProg checkerTab checkerProg "check")` plus the data
  symbols; it no longer needs the `Asm*` modules) and writes or compares the file (4 s).
  `land.sh` runs `--check --no-build`. `checker_prog.py` reminds to run it. A stale file also
  fails the build itself, at `checkerFile_eq`.
* `asm_lit` no longer compiles its literals (nothing runs them now: the file is printed from
  `compileProg`): the ten `AsmPart` modules went from 28–36 s to 15–21 s each.
* `harness/check-asm.sh` checks the committed file (assembler/objdump against the text) instead
  of printing one: `[checker] OK: 232141 instructions match`. `cc harness/main.c asm/checker.s`
  links and runs (`error` on an empty input, as master's stubs give).

## Measurements (this machine, `lake env lean`, peak RSS of the process tree)

| module | wall | peak |
|---|---:|---:|
| `ConAguaAsm.Checker` (parse 1.7 s, round trip, term, kernel) | 8.5 s | 1.9 GB |
| `ConAgua.Checker.AsmFileEq` | 1.5 s | 2.9 GB |
| `AsmPart0…9` (unchanged checks, literals no longer compiled) | 15–21 s each | (as before) |
| `scripts/asm_file.py --check` | 4 s | |

Olean of `ConAguaAsm.Checker`: 17 MB. The file: 5.3 MB, 251 120 lines (251 094 directives:
10 383 stub, the trampoline, 1751 functions).

## Workflow changes for every lane

* After changing the checker's L code (and `scripts/checker_prog.py`), the compiler or the stub:
  build, run `scripts/asm_file.py`, commit `asm/checker.s`. Otherwise the build fails at
  `checkerFile_eq` naming the first stale function, and `land.sh` at `asm_file.py --check`.
* A merge conflict in `asm/checker.s`: take either side and rerun `scripts/asm_file.py`.
* Not changed: `scripts/e2e.py` still compiles its own programs with `e2e-l asm`; it could link
  `asm/checker.s` for the `check` entry.

## Negative tests (scratch, `_tmp/asmfile/Bad.lean`)

`jae`→`jb` in one function: `asm_file_eq: the file differs … in segment 1021 (nat_op_deps)`;
`.byte 0x90` in `.text`: `line 3: unknown instruction '.byte'`; a trailing `# c`: `bad register`;
`$07421703487488`: `integer with a leading zero`; `.text` after `.rodata`: rejected; `jc`
(an `as` alias): rejected by the parser (only the printer's spellings).
