# dedup2: the remaining duplicate lemmas

Lane dedup2 of 2026-11-10 (Opus), from master `52f1aaf0c`. Follow-up of lane dedup
(`syncvocab.md`, "Follow-up: duplicate names"). Pure renames and deletions: no L change, no
statement of a final or refinement theorem changed.

## 1. The scan

An elaboration-time scan of the environment (`_tmp/dedup2/Scan.lean`, run with `scripts/lake env
lean`): it imports every built `ConAgua` module (minus the bench/emit executables, which redefine
`main` or each other's helpers), and groups every theorem of a `ConAgua` module (not generated
`Checker.Asm*`/`Checker.Prog*`, not auxiliary `eq_*`/`match_*`/`_proof_*` declarations) by its type
with binder names and binder kinds erased and universe parameters renamed by position (`Expr`
equality, so instances and implicit arguments must agree). A second pass compares the types
after reducible unfolding (`whnfR` at every subterm): it merges statements that differ only in
`≠` vs `¬ … = …`, `Word` vs `UInt64`, `ArrId` vs `Nat`. Uses come from the `.ilean` reference
index (every `.ilean` under `.lake/build`: module, line, columns), so a rename touches exactly the
references Lean resolved, not text that happens to match.

On master `52f1aaf0c`: 33 612 theorems, 256 groups of the same statement (406 removable names),
16 more groups after reducible unfolding (8 merged, §3).

Tooling (`_tmp/dedup2/`): `Scan.lean` (groups, declaration ranges, binder kinds, simp flag),
`idx.py` (the `.ilean` index), `plan.py` + `decisions.py` (which member stays, under which name,
in which module, and which files need an import), `apply.py` (deletes the other members, puts an
`attribute [...] K` line where one carried attributes, rewrites every reference, adapts the
arguments where the binder kinds differ: `D h` → `K _ _ h` where `K`'s leading binders are
explicit, `D x h` → `K h` where they became implicit and `h` names them, `@K x (by omega)`
otherwise, and adds `import <home>` where the kept module was not visible).

## 2. Batch 1: word arithmetic and word lists, into `L/WordOff.lean`

25 groups (the `UInt64` arithmetic and the `List Word` readings `r.getD k 0`, `r.drop 3`),
122 deleted theorems, 1281 references renamed, in 284 files. The kept statement is a new
theorem in `ConAgua/L/WordOff.lean` (namespace `L`, beside `off_toNat`; it imports only
`L.Syntax`), named in Mathlib style; its binder kinds are those of the copies with the most
references (`toNat_add_of_lt (d k : Word) (h)`: 289 references to explicit copies such as
`widx2`, 114 to implicit ones such as `word_add_toNat`). 244 files import `L.WordOff` now.

| kept | deleted | references |
|---|---|---|
| `L.getD_zero` | `getD_zero_headD`, `agGetD0`, `getD0`, `getD0_headD`, `getD_zero`, `ntGetD0`, `sumGetD0` | 51 |
| `L.toNat_add_ofNat_of_lt` | `word_add`, `fo_toNat_add_small`, `toNat_add_ofNat`, `toNat_add_small`, `toNat_add_small'`, `word_add_toNat`, `addW_toNat`, `ofNat_add_toNat`, `partsWadd`, `tailToNat`, `word_toNat_add` | 47 |
| `L.toNat_add_of_lt` | `addW`, `addW_toNat`, `peel_word_add_toNat`, `widx2`, `sum_toNat_add`, `wadd_toNat'`, `word_add_toNat`, `addN` | 403 |
| `L.toNat_add_of_not_lt` | `add_nc`, `add_noovf`, `dk_toNat`, `toNat_add_of_not_lt'`, `partsAddNoOv`, `pos2_word_add`, `rec3Add_toNat`, `sumAddNoOv`, `word_add_nowrap` | 24 |
| `L.toNat_and_one_le` | `and_one_le`, `tier_bit` | 11 |
| `L.toNat_eq_toNat_sub_one_add_one` | `ctrW_toNat`, `ue_toNat_pred`, `word_toNat_pred`, `ctrW_toNat'`, `fuel_pred`, `toNat_pred` | 25 |
| `L.decide_lt_eq_not_decide_le` | `dec_lt_not_le`, `dec_lt_not_le'` | 3 |
| `L.getD_one` | `getD1`, `getD_one`, `pr_getD1`, `getD1`, `agGetD1`, `cnGetD1'`, `getD1`, `getD1_eq`, `getD1_eq'`, `getD1_headD`, `getD_one`, `getD_one_eq`, `ntGetD1`, `sumGetD1`, `getD1` | 193 |
| `L.getD_two` | `getD2`, `getD_two`, `pr_getD2`, `getD2`, `agGetD2`, `getD2`, `getD2'`, `getD2_eq`, `getD_two`, `pos2_getD2`, `sumGetD2`, `getD2` | 120 |
| `L.getD_three` | `getD3`, `getD3'`, `getD3_eq`, `getD_three`, `scaGetD3`, `getD3` | 34 |
| `L.eq_zero_or_eq_one_of_le_one` | `h01`, `le_one_cases`, `word_le_one` | 36 |
| `L.toNat_ne_zero_of_ne` | `pr_word_ne0`, `toNat_ne_zero'` | 33 |
| `L.toNat_sub_one_of_ne` | `pr_word_sub1`, `sub1_toNat`, `word_pred`, `pos2_word_pred`, `rec2ToNat_pred`, `sumToNat_pred`, `toNat_sub_one'` | 52 |
| `L.toNat_add_one_of_ne` | `succW_toNat`, `toNat_succ_of_ne`, `pos2_word_succ` | 34 |
| `L.toNat_add_one_of_word_lt` | `succ_toNat_of_lt`, `wsucc`, `forUp_succ_toNat` | 19 |
| `L.toNat_add_one_of_lt` | `toNat_succ_lt`, `toNat_succ`, `escTN_add_one`, `toNat_add_one'`, `word_add_one` | 44 |
| `L.toUInt64_toNat` | `toUInt64_toNat_self`, `word_ofNat_toNat` | 13 |
| `L.add_one_add_one` | `word_add11`, `word_add2`, `word_add11` | 11 |
| `L.add_toUInt64_succ` | `word_succ_add`, `word_add_nat_succ` | 4 |
| `L.ofNat_toNat` | `ofNat_toNat'`, `ofNat_toNat_word` | 60 |
| `L.toNat_ofNat_of_lt` | `ofNat_toNat_lt`, `ofNatN`, `ofNat_toNat_lt` | 37 |
| `L.exists_toNat_eq_succ` | `apd_fuel_pred`, `wordSucc_of_ne` | 7 |
| `L.headD_drop_three` | `dcDrop3_headD`, `drop3_headD`, `partsDrop3` | 10 |
| `L.drop_three` | `drop3_eq`, `usDrop3_eq` | 8 |
| `L.getD_four` | `getD4_eq`, `getD_four` | 2 |

What the rewrite met:

* **Binder kinds.** An implicit copy's `D h` became `K _ _ h`; an explicit copy's `D w h` became
  `K h` when `h` is a name (its type fixes `w`), else `@K w (by omega)` (24 places, all
  `toNat_add_one_of_lt`/`toNat_sub_one_of_ne`/`exists_toNat_eq_succ` with a `by` argument);
  two named-argument calls (`addW_toNat (x := …) (y := …)`, DefEqStuckCert) by hand.
* **`L` shadowed.** 76 references are `_root_.L.…`: in 32 files a binder or a `variable (L : …)`
  named `L` (a `Lens`, an `NbLook`, an `RsLook`) turns `L.toNat_add_of_lt` into field notation on
  it. Where no binder shadows it the name is `L.…`.
* **A grind pattern across a private import.** `Pool.lean`'s `grind_pattern [arena_grind] add_nc
  => x + y < x` now puts `L.toNat_add_of_not_lt` into `arena_grind`; with a plain `import
  L.WordOff` every module that uses `arena_grind` without seeing `WordOff` failed with "Unknown
  constant". `Pool` re-exports it (`public import`, in `scripts/shake-allowlist.txt` with the
  reason).
* **Imports.** `shake` then found 37 imports whose only use had been a deleted copy (e.g. eleven
  of `IndPosSpec.NestKeyMap`, five of `Pos2DecHLSplit`): removed. `Arena/DeclValRef.lean` lost its
  last importers that way; nothing used its other lemmas (`dvT`, `checkDefnVal_dvT`,
  `decls_decCI_defn`, …: the refinements in `Verdict/DeclValsE.lean` no longer go through them),
  so it is deleted rather than listed as unbuilt.
* Module docstrings that listed a deleted lemma among the file's contents lost the name
  (DmCgW, Pos2DecHLSplit, DecCVX, ConsRecsTFSimOf, CtorX, DomsW, CheckSumCtor, For, WalkRefine).
  Other lanes' journals that cite old names (natsurvey, forloop, lconstructs, refgen) are history
  and stay.

## 3. Batch 2: the rest

## 4. `finish [erec_grind]`

Lane dedup found that `finish [… , erec_grind]` does not close goals that `finish [… , erRd]`
closes, while `grind [erec_grind]` does. The reason: `finish` is a step inside a grind goal that
`sym`, `grind … =>` or `vcgen … with` set up, and it elaborates its list incrementally
(`Lean.Elab.Tactic.Grind.withParams`, `elabGrindParams (incremental := true)`). Named lemmas and
definitions go to `params.extra` and are activated in the running goal (`Grind.assertExtra`); an
attribute set's name is only pushed onto `params.extensions`, and nothing reads that list any
more, because the goal's E-matching theorems were copied from the extensions when the goal was
made (`mkGoalCore`). So `finish [S]` is a silent no-op for every set (`erec_grind`, `arena_grind`,
`lang_grind`). `vcgen … with finish [S]` is the same: `vcgen` starts its grind goal with
`Grind.mkDefaultParams` (`Lean/Elab/Tactic/VCGen/Frontend.lean`). Checked on a three-line
example (a set `my_grind` holding `f_eq`): `grind [my_grind]`, `grind [my_grind] => finish` and
`grind => finish [f_eq]` close `f n = n + 1`, `grind => finish [my_grind]` does not.

Corrected: `syncvocab.md` (§4's "named by the proofs …" and the Follow-up's `abbrev → def` note),
the docstrings of `ErecVocab.lean` and `L/GrindAttr.lean` (which recommended `finish
[erec_grind]` and `vcgen … with finish [lang_grind]`), and `scripts/sync-rules/vocab_attr.py`:
it added `arena_grind` to every `finish` list and gave a bare `finish` the list `[arena_grind]`
(no effect), and `erec_grind` likewise in `sets+`. Now the sets go only into `grind`/`sym` lists
(and a bare `sym =>` gets one), and `sets+` adds to `finish` lists (and a bare `finish`) the
declaration `erec_grind` holds, `erRd` (`FINISH_PLUS`). No proof in the tree used a set in a
`finish` list.

## 5. Left, and why
