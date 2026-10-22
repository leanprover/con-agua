# Lane `erecfix`: the core's `EREC` write set without a 20 GB kernel check

## Problem

`checkerProg_coreErec : closedA checkerProg coreErecA coreErecC coreFns = true` was
`by decide +kernel`: one kernel check that, for each of the ~420 functions of `coreFns`, looks the
name up in the 1720-function `checkerProg` by `String` comparison (the kernel unfolds
`String.decEq` down to byte lists), walks the body, and checks every callee's membership in
`coreFns` (again `String` comparisons) and every stored array's membership in the 255-element
`coreErecA`. User report: 20 GB RSS; two parallel builds nearly hit the 50 GB session cap.

## Design (as `prog_wf`, `Compiler/WFSplit.lean`)

`ConAgua/Compiler/WriteSetSplit.lean`:

* `namesTree fs : Option NTree`: the function set as a search tree of `nameCode`s (WFFast's
  injective name numbering); `namesTree_spec`: `(t.find (nameCode f)).isSome = decide (f ∈ fs)`.
  The command `names_tree t : fs` evaluates it with compiled code, declares the literal `t`
  and `t.eq : namesTree fs = some t` (one kernel check over the names only).
* `Stmt.okWB ctl pa pc t`: `okW` with the array/`CTL`-word sets as Boolean predicates and the
  callee check as a tree lookup (GMP `Nat` comparisons, no `String` comparison).
  `Stmt.okW_of_okWB` turns it into `okW` given `pa a → a ∈ A`, `pc w → w ∈ C`.
* `wsChk ctl pa pc t x`: per function of the program: its name is not in the tree, or its body
  passes `okWB`. No lookup in the program.
* `prog_all h : p chk`: `h : ∀ x ∈ p, chk x = true`, one kernel check per chunk of
  `progWfChunk` (32) functions (`h.c<j>`), joined by `forall_mem_cons_of` with no evaluation.
* `closedW_of_all`: `closedW ctl p A C fs` from the tree, the two predicate facts and
  `∀ x ∈ p, wsChk … x`. Lookups come from `List.lookup_eq_some_iff` (the found pair is a member
  of `p`), the call closure from the tree (each callee's code is in `fs`).

`Checker/CoreErec.lean` keeps `checkerProg_coreErec`'s statement and proves it by
`closedW_of_all coreTree.eq coreErecPa_mem coreErecPc_mem checkerProg_coreChk`. No `decide`
evaluates `checkerProg` as a whole: each chunk check sees 32 bodies; the final theorem's kernel
check only matches the chunk elements against `checkerProg`'s literal (shared subterms).
Non-core functions cost one name code and one tree lookup each (the `||` short-circuits before
the body). `scripts/core_fns.py --check` is unchanged (it reads `Arena/CoreErec.lean`).

## Measurements (`lean ConAgua/Checker/CoreErec.lean`, VmHWM sampled every 0.5 s)

* Before: 20 GB RSS (user report). Re-measuring here was not possible: the session cgroup
  was at ~38 GB from other lanes; a guarded run was killed at 4.4 GB after 7 s, still rising.
* After: peak 3.0 GB, 12 s wall. Importing the module's dependencies alone peaks at 2.3 GB
  (1 s), so the checks add ~0.7 GB.

## `IndCore` (coordinator's follow-up)

`Checker/IndCore.lean`'s `checkerProg_coreStage : CoreStageClosed checkerProg` was the same
pattern (`stageCoreFns` = 5 stage entry points ++ `coreFns`, arrays but `EREC`, `IW`, `PINS`,
`CTL` words but 129, 200). Same fix (`stageCoreTree`, `coreStagePa`/`Pc`). `stageCoreFns` repeats
names (entry points also in `coreFns`), so `namesTree` keeps a repeated name once instead of
failing.

* Before: the census-run worktree built the old `IndCore` and `CoreErec` side by side, observed
  RSS ~22 GB each (49 GB anon in the session cgroup).
* After: `IndCore` peak 3.2 GB, 11.7 s wall.

`Arena/CoreErec.lean`'s module doc still says the checker's instance is `by decide +kernel`;
left as is to avoid rebuilding its heavy dependents for a comment.
