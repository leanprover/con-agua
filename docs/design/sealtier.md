# Lane sealtier: frame by construction for the record pool (reproof.md rec. 4)

Lane of 2026-11-10 (Opus), from master `7022cc7fd`. Brief: make "a job does not write `EREC`
tier 0" one theorem (a static check on the program text, no runtime check), and delete the
per-function tier-0 frame proofs it replaces. This journal is Step 0, the inventory. It stops
there: the inventory shows the premise does not hold (§3).

## 1. Method

A throwaway `lean --run` script over `checkerProg` (1776 functions; kept outside the repository in
`_tmp/sealtier/tools/Inv.lean`). For every function it lists the stores whose destination is
array 136 (`EREC`) and the calls of `erec_put`/`erec_alloc`, and it computes call closures:
`record_job` (the job: `scratch_enter`, `and_pin_ok`, `check_decl`, `scratch_drop`; 1349
functions), `check_a` (entry 1: the stages and the stream index; 768 functions).

## 2. Inventory

* **Stores into `EREC`: one.** `erec_put`'s `EREC⟨t⟩[i] := v` with `t := ⦃a⦄.tier`. The tier
  comes from bit 40 of the address at run time. No other function stores into `EREC`, with
  `st64`, `st64t`, `st32t` or a block copy.
* **Calls of `erec_put`: 189, in 47 functions.** None of them has a tier in the program text: each
  passes an address that `erec_alloc` returned, and `erec_alloc` picks the tier from the scratch
  flag `CTL[1]`.

  | functions | reached by | functions | `erec_put` calls | `erec_alloc` calls |
  |---|---|---:|---:|---:|
  | job only (`check_constant_val`, `class_const_ok_lit`, `class_fe_r_rec`, `cv_new`, `generated_rule_nested`, `quot_pin_hit`, `rom_cv`, `rule_copy`, `rules_to_erec`, `sum_rules_go`) | `record_job` only | 10 | 57 | 9 |
  | shared (`block_table`, `ci_at_lps`, `rci_*`, `rec_info_rec`, `rules_refire`, `erec_ci`, `er_put5`, …) | the job and entry 1 | 31 | 125 | 21 |
  | entry 1 only (`rom_*_to`, `intern_pin_sets`) | `check_a` only | 6 | 7 | 4 |

  The shared functions write tier 0 legitimately in entry 1 (they build the stream index's
  records and the pins' records) and tier 1 in a job. No job-only function is reached outside
  `record_job`.
* **The flag in a job.** Only `scratch_reset` (`scrTail`) writes `CTL[1]`. No `scratch_*`
  function is in the closure of `and_pin_ok` and `check_decl`, so the flag stays on for the whole
  job. That part could be checked on the text by the existing `closedW` machinery (the `CTL`
  index set).

## 3. What a frame theorem would replace: nearly nothing

The brief assumes that "a job does not write tier 0" is proved today as a write set per function.
It is not:

* The jobs' write sets (`Arena/Jobs.lean`: `apA`, `cdA`; decided in `Checker/JobsClosed.lean`)
  **contain both tiers of `EREC`**. `Stmt.okW` needs both tiers for any `st64t`, so `erec_put`
  forces this. No write set in the repository leaves out `↑EREC` but keeps `tier1 EREC`.
* The job keeps the stream index's records (`JobM.ofDrop`, `andPin_job`, `IndexR.frameIdx`)
  because of **`IWGrow`/`ErecGrow`** (`erGet`: tier 0 below `CTL[129]` unchanged). Every
  function's spec carries this growth fact. 31 of the 41 writer functions in the job's closure
  are shared with entry 1, where tier 0 grows, so their per-function growth proofs stay even if a
  theorem gave "tier 0 unchanged" for the job. The job-only ten carry the same `IWGrow` shape as
  everything else, and their callers compose it.
* There are **no `erec_put` leaves**. `closedWL`'s only record-pool leaf is `erec_alloc` in the
  stream index builder's write set (`dcLeaves`, `Arena/IndDeclConstsFrame.lean`). That is the
  mirror fact: entry 1, with the flag off, does not write `CTL[130]`.
* `erecPutMem_frame`, `wrER_frame` and the `MemFrame [EREC, tier1 EREC] []` frames name both
  tiers and are not tier-0 facts.
* The threaded mode's "a job does not write the frozen buffer" is not proved. It is the
  **trusted route-A hypothesis** of `ThreadsRun` (`Final/ThreadsFinal.lean`: the buffer "stays in
  place", `mprotect`). It covers all 63 frozen arrays (store records, slot tables, columns,
  `PINS`, `EIX*`, …), so an `EREC`-only theorem cannot remove it. Removing it would also change a
  final theorem's hypotheses.

## 4. The static restructuring, if wanted anyway

This is the twin-faithful form (con-ron's job writes its own tier behind `&mut`, the base behind
`&`): **the store's tier is the mode's tier, not the address's.** `erec_put` becomes
`i := ⦃a⦄.idx; t := CTL.u64[1]; EREC⟨t⟩[i] := v`, or `t := ⦃a⦄.tier | CTL.u64[1]`, which
leaves entry 1 exactly as today. The check on the text is: every `EREC` store in the closure has
that tier, and the closure never writes `CTL[1]`. The theorem is: flag on at entry implies
`EREC` tier 0 is unchanged. Compiled code: one load of `CTL[1]` (an `or` in the second variant)
in place of a shift. There is no check and no branch.

The cost is semantic. `erecPutMem m a v` then depends on `m`'s flag. Every lemma that names the
written tier needs the premise "flag off, or the address is tier 1": `erecPutMem_arr` (21 uses),
`erRd_erecPutMem_ne` (10), `erecP_putMem_other` (6), `erecP_putMem_self` (5), `erecPutMem_lo` (3)
and `erecPutMem_grow` (1). `erecPutMem` appears 203 times in 30 files. The callers have the
premise (`erAllocW_spec`: the address's tier is the flag's), but they must pass it on. The gain
is a new theorem and possibly the `erec_alloc` leaf of `dcLeaves`. Measured against §3, it would
delete nothing.

## 5. Status

Stopped after Step 0. The change was not made and no number of §2 has moved. To decide (the
coordinator, with the user): drop rec. 4 for `EREC`; or re-aim it at the route-A hypothesis (a
proved "phase B writes no frozen array" for all 63 arrays, which needs every store library's
tier to be static in a job, i.e. the mode-tier store of §4 for every tiered store, and a change
of `ThreadsRun`'s hypotheses).
