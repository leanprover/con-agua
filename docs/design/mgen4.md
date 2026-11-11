# Lane mgen4: generator gaps of `l_model`, and the conversions they open

Fourth lane on `l_model` (`ConAgua/L/ModelGen.lean`, tests in `L/ModelGenTest.lean`; the earlier
lanes: `docs/design/mgen.md`, `docs/design/mgen3.md`). mgen3 (§5 there) converted about 250
hand-written models and listed the generator gaps it worked around. This lane closes the gaps
that a small change covers, then converts what they open. Same constraints as every lane: no L
program change (`checker.s`, `pins.bin` identical), no final statement change, no new axiom, no
heartbeats raised. Every generator change is an option that is off by default, or applies only
where the generator raised an error before, so no existing `l_model` changes its output (the
gate build rebuilds every `l_model` module, all unchanged).

## 1. Generator changes (round 1)

### `share`: a join point over a duplicated memory term

A total memory callee (`G ∧ s'.mem = F`, `erec_put`) is inlined: the memory after it is the term
`F m …`, and the next statement reads that term wherever it reads the memory. `rule_copy`'s
eleven `erec_put(b + i, EREC⦃old + i⦄)` each mention the memory before them three times (the
callee's memory argument, the read `EREC⦃old + i⦄`, the guard `erec_put` checks), so the model
held `3 ^ 11` copies (mgen3 kept the hand model). With `share`, a statement that writes the
memory (a store, `setG`, `set8`/`set32`, `copy!`, a total memory callee) and mentions a memory
term that is not a variable more than once (`dupMem`: occurrences of the term's syntax in the
statement's new memory and guards) starts a join point `fW.jᵢ` over the memory: the code from
that statement on becomes a definition (the join point machinery of an `if` whose branches fall
through, `mkJoin`), applied to the memory term. Inside it the memory is the variable `m`, so the
statement mentions only that. `rule_copy`'s model is ten join points, linear in size.

Test `tSh` (four calls of a callee with a guard over the memory). A twelve-call version proved
in 80 s, a ten-call one in 6 s, eight calls in 1.5 s: on that toy the steps' `grind` (not
E-matching, not the model's size; few heartbeats) grows fast with the number of calls, so the
test uses four. On the real `rule_copy` (eleven calls, `EREC` pool slices) the whole `l_model`
takes about a second.

### A binder named `L`

The generated proof text writes the library's names root-qualified (`_root_.L.exec`, `rootL`), so
that a binder `L` does not capture them; that also rooted the binder's own fields (`L.rc` →
`_root_.L.rc`, unknown), and mgen3's helpers renamed such binders to `hL`. Now the command renames
a binder `L` to `L'`, and every `L` / `L.x` after it (`renameBinderL`): after the binder, `L.x`
can only mean the binder's field (a local comes first in name resolution). The spec's binder is
then named `L'`. Test `tPfL_spec`.

### Implicit binders as model parameters

An implicit binder (`{C : …}`) that a callee's model mentions became an unknown identifier in the
generated definitions (only explicit binders were collected as the models' parameters, `mps`).
Implicit and strict-implicit binders are collected too; the models take them explicitly. Test
`tPfL_spec` (its `C` is implicit).

### `fold` with memory readers

`fold [erRd]` failed ("unsupported term"): fold patterns were word arithmetic only, so generated
models read `rdW (m.arr64 (tierA EREC (x >>> 40))) (x &&& …)` and users bridged by `rfl` lemmas
(`erRd_foldN`, `prd_rdW`). A fold function whose body is a word read `rdW (m.arr64 A) i` (`i` a
pattern over its other parameters: `cnt m t = rdW (m.arr64 CTL) (2 + t)`) or a pool slice word
`rdW (m.arr64 (tierA A (x >>> 40))) (x &&& 1099511627775)` (`erRd`, `prd`) is a reader
(`Fold.reader`): `A.u64[i]` and `A⦃x⦄` become `f m …` where they match. Test `tRd`.

### `mixed` callee posts

Posts that state some results as values beside the call's effect were rejected: `str_put_esc`
(`r.headD 0 = s₀.mem.top ∧ strPutEscW … = some (r.tail.headD 0, s'.mem)`: "unsupported post
conjunct"), `ls_put` (`r = [s₀.mem.top, lsPutL b v] ∧ lsPutW b s₀.mem v = some s'.mem`:
"ambiguous post"), `stk_pool` / `rom_put` (`G ∧ r = [s₀.mem.top] ∧ s'.mem = F`: ambiguous). Now
such a post is `CKind.mixed`: the stated results are the values (over the memory before the
call), and the effect (`F = some (r.ⱼ, s'.mem)` giving result `j`, `F = some s'.mem`, or the
total `s'.mem = F` with its guards) is handled as before. Only these shapes, which raised errors
before, are read so; a pure result beside `F = some (r.headD 0, s'.mem)` or a memory model stays
ignored as it was. Test `tMx`.

### Not changed: literals and instances in generated `if`s

mgen3 met `rw [ite_eq_left h]` and `split` failing on generated `if`s where `simp only [h,
↓reduceIte]` works. A generated `if k = 0` is `@ite _ (@Eq Word k (@OfNat.ofNat Word 0 _))
(instDecidableEqUInt64 …)`, a hand-stated one over `UInt64` the same with `UInt64` for `Word`
(reducible); the instances are the same. No case in the current tree reproduced the failure
where the generated form could be changed without changing every model's output, so the
generator is unchanged here.

## 2. Conversions

### Batch 1: `rule_copy` (`share`)

`rc_spec` is generated (`fns [hL.rc ↦ rcpW list] … share`): the hand model `rcpW` (`some ([0],
cpMem m b old)`) and its hand spec are gone. The generated `rcpW` checks `erec_put`'s bound at each
copy (`none` otherwise), so the two walks over `rules_to_erec_go` (`rteGoW_mem`, `rteGoW_afr`)
case on its result and take the memory from `rcpW_some` (`rcpW m b old = some (r, m') → m' =
cpMem m b old`, one `split` per join point); `cpMem` stays as the users' description of the copy.

| module | instructions | user s | RSS MB |
|---|---|---|---|
| `Arena/IndSumSpec/ConsBlockRecsTF` | 68.2 → 75.5 G | 10.6 → 11.4 | 1230 → 1290 |
