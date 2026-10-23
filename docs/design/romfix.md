# Lane `romfix`: `Rom/CIReadRefCaps.lean` without a > 15 GB elaboration

## Problem

`ConAgua/Rom/CIReadRefCaps.lean` (lane decls4) needed more than 15 GB in one `lean` process when
rebuilt; its import closure includes `Arena/IndStubs.lean`, so every lane editing IndStubs rebuilt
it and hit the coordinator's 16 GB watchdog.

## Diagnosis

Elaborated alone (`lake env lean`, RSS poll-and-kill guard at 8 GB): killed at 8 GB. Imports alone
peak at 2.2 GB. Bisecting `caps_rel` by truncating the proof (rest `all_goals sorry`) showed the
memory grows steadily with the number of `omega` calls after the equalities
`hc1 … hc13 : (c + k).toNat = c.toNat + k` enter the context (line ~252): every `omega` there,
even for `erTop m₀ ≤ c.toNat + 3`, took ~0.5 s and ~130 MB that stay allocated (8 trivial `omega`s:
+1.2 GB). `trace.omega` shows why: omega eliminates the 11 chained equalities one by one and its
justification for the final contradiction is a tree of 12 000 lines (one `omega` call), exponential
in the number of equalities, and so is the proof term.

## Fix

A file-local macro `comega` used for every `omega` in `caps_rel` after the equalities:
`simp only [hc1, …, hc13, hq64] at *` (rewrite every `(c + k).toNat` to `c.toNat + k`), then `clear`
the equalities and `hcN`, then `omega`. Also the 32 numeral side goals of `hword` (`2 < 15`, `2 ≠ 1`,
…) are `decide` instead of `omega`, and `set_option maxHeartbeats 8000000` on `caps_rel` is gone
(not needed any more). Statements unchanged.

## Measurements (`lake env lean ConAgua/Rom/CIReadRefCaps.lean`, peak RSS of the process)

| | peak RSS | time |
|---|---|---|
| before | > 8 GB (guard kill; coordinator saw > 15 GB) | killed |
| after | 2.5 GB (imports alone: 2.2 GB) | 5.6 s |

Lesson (general): many `UInt64.toNat (c + k) = c.toNat + k` facts in context make every later
`omega` exponential. Rewrite with them and clear them before `omega`, or keep them as one `∀` lemma.
Import cutting (IndStubs) is not needed now: the module rebuilds in seconds.
