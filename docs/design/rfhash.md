# Lane `rfhash`: the memo hash drops `k2`'s high half (journal)

Branch `rfhash`, from master `e9a3b3d1`. Bug found by lane `compopt` (its journal, "c05b: an L hash
bug, not the compiler").

## The bug

`memoFindG` (`Arena/MemoLib.lean`) started its probe at `homeW (k1 ^ (k2 << 32))`. Every memo that
keeps a second component in the **high** half of `k2` lost it from the hash:

* the banked memos (`MemoBank.genW k2 g = k2 ||| g << 32`): `rf` (`replace_fvars_go`, key
  `(h, CTL[219] << 32)`) and the mode-memo banks;
* the eager bit (`wh`, Knot memos: `((mode >> 1) & 1) << 32`);
* `rrSch` (`ruleRhsC`, `ctor ∣ us << 32`).

For `rf` every bank's entry for one `h` got the same home slot, and since dead banks' entries stay
live until the memo's per-declaration clear, the cluster only grew. On
`complete_c05b_nest30_pi1000` `rf_find` ran ~1 500 probes per call (compopt: 98% of 1.47 T
instructions).

## The fix

`kh k1 k2 := (k1 ^^^ (k2 <<< 32)) ^^^ ((k2 >>> 32) * golden)` and the same expression in
`memoFindG`. Both halves of `k2` now enter the hash; the high half is spread by a multiply so that
small generations / bits do not cancel against the (small, dense) handle in `k1` as a plain
rotation would. Key equality (the probe compares both words) is unchanged, so the memo semantics,
`MemoLib`/`MemoLibRel` and all refinements are untouched: no proof unfolds `kh` beyond
`memoFindG_spec`'s `finish [.., kh]`, which went through unchanged. Full `ConAgua` builds.

No deviation row: the memo library is `con-ron: none` (the twin uses `Std.HashMap`; con-ron uses a
fresh map per `replaceFVars`).

## Measurements (`perf stat -e instructions:u`, compiled `check`, CA_WORDS 2^25, 1 pin variant)

| fixture | before (compopt `base.bin`, master `efb16f47`) | after | con-ron `--jobs=1` |
|---|---:|---:|---:|
| c05b_nest30_pi1000 | 1 470 824 M (67 s) | 33 103 M (3.4 s) | 9 519 M |

44× fewer instructions; now 3.5× con-ron, in line with L's usual ~3× (compopt baseline). Exact
profile (compopt's `asmprof.py`) after: `rf_find` 4.0% at 166 instructions per call (was ~179 000);
the top is now `e_view` 14%, `der_b` 13%, `crf_go` 6%, `forall_find` 5%, `crm_find` 5%.

Fixtures without the bug pay a little for the 3 extra instructions per probe (`>>`, `*`, `^`):
c04a_restart_70 43 089 M → 43 678 M (+1.4%), c03d_pi_depth_1030 5 728 M → 5 812 M (+1.5%), both
measured against compopt's `base.bin` (master `efb16f47`, so this includes some master drift).
