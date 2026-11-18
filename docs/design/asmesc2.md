# Lane `asmesc2`: the asm escape, and hand-written `mul_row`/`sub_row`

Lane of 2026-11-18, from master `9e83e46da`. Task: land the asm escape framework of lane asmesc
(`git show asmesc:docs/design/asmesc.md`, variant A) and proved hand-written x86 bodies for the
bignum inner loops `mul_row` and `sub_row` (measured by lane mulasm, `git show
mulasm:docs/design/mulasm.md`).

## Step 1: the framework (no behaviour change)

A table of hand-written bodies `X : AsmTab := List (Nat × Program)`, keyed by `nameCode f` (a
`Nat`, so that the kernel's lookup during `asm_lit` compares numbers, not strings; `nameCode` is
injective, `nameCode_inj`). `ConAgua/Compiler/Compile.lean`:

* `fnCode X tab t sk f fd`: `X`'s body for `f` if there is one, else `compileFn tab t sk f fd`;
* `compileFns X …`, `compileProgT X …` take the table; `compileProgX X tab p entry` is the whole
  program with the table; `compileProg tab p entry := compileProgX [] tab p entry`.

The proof (`ConAgua/Compiler/SimCall.lean`):

* `FnSimAt p G sk n f fd kf`: the per-function contract, i.e. the body of the old `FunSim` for one
  function whose code starts at `kf` (unchanged text).
* `FunSim p G X t sk n`: `FnSimAt` for every function at its code `fnCode X …`.
* `AsmOk p G X`: every body in `X` for a function `f` starts with `label (fnL f)` and meets
  `FnSimAt p G sk n f fd kf` for every `sk`, `n`, `fd = p.lookup f`, `kf`. `AsmOk.nil`.
* `fnCode_head` (from `AsmOk`) replaces `compileFn_head` at the call sites (`sim_callTail`,
  `sim_tail`, `enter_core`).
* `funSimC` (`SimFun.lean`) is the old `funSim` (compiled code meets `FnSimAt`); `funSim` splits on
  `X.lookup (nameCode f)`.
* `execSim_all`, `enter_core`, `compile_correct_frame`, `compile_correct`,
  `compile_correct_frame_ref` take `(X : AsmTab) (hX : AsmOk p G X)` and are about
  `compileProgX X`. The final chain (`Final/{ParAbi,SeqAbi,BufAbi}`) passes `[] (AsmOk.nil _ _)`;
  no statement in `Final/*` changes in this step.
* `asm_lit`/`asm_lit_fns` take an optional trailing `asm X`: the per-function equations are about
  `fnCode X …` and the whole-program one about `compileProgX X tab p entry`; without the clause,
  `X = []` and the statement is `compileProg tab p entry = name` as before.

`checker.s` is byte-identical (`asm_file.py --check`: up to date). The full build passes.
