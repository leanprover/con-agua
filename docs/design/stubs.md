# Lane `stubs`: Remaining checker stubs; first fixtures accepted end to end

Journal of lane `stubs` (decisions, measurements, findings, open ends). Only this lane edits this file.

## Landing 1: no stub left in `checkerProg` (2026-10-23)

`checkerProg` had 9 `abortStub`s (master `89e6c093`). All have L code now, in three new
modules (namespace `L.Stubs`, each `FunDecl` cited; `Checker/Prog.lean` regenerated: 1739
functions, **0 stubs**):

| stub | module | twin | notes |
|---|---|---|---|
| `fvar_b(f, e)` | `StubNames` | `fvarB` | adapter: `ab_fvb(e, f)` (`Abs1.lean`) is already `fvarB` |
| `reserved_rec_name(n)` | `StubNames` | `reservedRecName` (+ `litGuardNames`) | `reserved_contains`, the ten literal-guard pins, pins 14‥20, 21‥28, in the twin's order (`lit_guard_has`, `pin_range_has`) |
| `name_rec(n)`, `name_rec_i(n, i)` | `StubNames` | `blockRecNameSetOk`, `targetRecPins` (`internNNode (.str n "rec")`, `s!"rec_{i}"`) | the string at the pool top (`pool_room`), then `intern_nstr`; decimal digits by `mulhi(x, ⌈2^67/10⌉) >> 3` (`dec_len`) |
| `intern_ls_iw(o, l)` | `StubNames` | `internLsNode` | the `IW` slice copied to the pool top (`iw_pool`), then `intern_ls` (as `spn_ls`) |
| `lv_zero_caps(l)` | `StubInd` | `zeronessOf` (in `blockCapsAt`) | `lv_zero` on the level heap, the parameters copied to fresh `EREC` words (`lh_er_copy`), heap top restored; `(0,0,0)` never, `(1, off, len)` ifAllZero (`decPW`) |
| `rec_rule_bits(vis, c)` | `StubInd` | `recRuleBits`, `recRuleKOf`, `recRuleEtaOf` | shared prefix `ctor_family` (ctor record, Π-result head, inductive record) |
| `open_pis_at_fvars_f(n, e, i)` | `StubInd` | `openPisAtFvarsF`/`…FGo`, fallback `openPisAtFvars` | fvars on `SPN` above `CTL[136]` (the twin's `acc`, `inst_list`'s slice convention), copied to an `IW` slice; the fallback runs as the twin's (store effects only: it cannot succeed where the one-pass walk failed) |
| `consts_resolve_ffast(vis, e)` | `ConstsResolveF` | `constsResolveFFast`/`…FGo`, `constsResolve` at leaves | **memory map addition**: word array `155` = `CRM` (walk-local memo, cleared per call), `CTL[158]`, `CTL[159]` its stamp − 1 and live count |

Other files: `Checker/LoopDecl.lean` (lane loopt2): the new callees of `intern_ls_iw` and
`consts_resolve_ffast` added to `declExtFns` (the closure check failed without them; mechanical).
`docs/deviations.md` D28 (pool words written per `name_rec*`/`intern_ls_iw` call, as D21/D24).

**Refinements: none yet.** The contracts are lane `induct`'s `RelAM` statements in
`IndStubs.lean` (`fvarB_spec`, `reservedRecName_spec`, `nameRec_spec`, `nameRecI_spec`,
`internLsIw_spec`, `lvZeroCaps_spec`, `recRuleBits_spec`, `openPisAtFvarsF_spec`,
`constsResolveFFast_spec`), still `sorry` (owner indproofs3; `stubM` is opaque, so they do not see
the new code). Next: word models (`l_model`) and `@[refines]` theorems for the small ones
(`fvar_b`, `reserved_rec_name`, `rec_rule_bits`, `lv_zero_caps`).

**e2e before** (`scripts/e2e.py --no-diff --no-perf --no-interp`, 675 fixtures, 413 s): `check`:
3 agree-reject, 44 agree-reject (L aborts), 2 l-error (`hoist_ok`: lane front3), **626 missing,
all at `intern_ls_iw`** (`eq_at1`, `param_levels`); `check_np`: 1 agree-accept, 46 agree-reject,
628 missing (`intern_ls_iw` 499, `consts_resolve_ffast` 129). The stub identity (`missing N`)
survives on this path: `e2e.py` compiles the text dump with `DIAG` stubs; only
`harness/check-asm.sh` (from `checkerAsm`) reads a stub as `error`, moot now with no stubs.
**After**: next entry.

After merging master (lane loopt2's `LoopDecl` per-function agreement lists): `consts_resolve_ffast`
is real code in `checkerProg` now, so it moved to `openFns` (`DeclCvg.lean`, the texts' open
callees: its contract is its stub spec, as for `has_fvar_fast`) and out of `cvgOwn2`, `ivOwn1`,
`armOwn1` (one `rfl` each fewer). For lane loopt2: mechanical, merge as is.

## e2e with no stubs (2026-10-23, `162ba476` = landing 1's tree before the last master merge)

`scripts/e2e.py --no-diff --no-perf --no-interp --jobs 12`, 675 fixtures, 9756 s (162 min: the
tracer runs on every L error, and there are now ~270 of them, each up to 400 s); report in
`docs/e2e.md`.

**The first fixtures accepted end to end by the compiled checker: 399**, every one also accepted
by con-ron and by `e2e-ref`. Against both references (`check`):

| con-ron | e2e-ref | L `check` | fixtures |
|---|---|---|---:|
| accept | accept | **accept** | 399 |
| reject | reject | no | 206 |
| decline | decline | no | 55 |
| accept | accept | no | 7 |
| error | error | no | 4 |
| timeout | timeout | – | 2 |
| accept | accept | – (L timeout) | 1 |
| exit -6 | memout | no | 1 |

All three agree on accept/not on 664 of 675; con-ron and `e2e-ref` disagree on none; **no
fixture where L accepts and a reference does not.** Classes: `check` 399 agree-accept, 3
agree-reject, 262 agree-reject (L aborts), 7 l-error, 3 l-timeout, 1 ref-memout; `check_np` 385,
3, 278, 6, 2, 1. (Before: 0 and 1 agree-accept.)

The 7 `l-error`s (L aborts, both references accept), filed here as bugs (the coordinator assigns):

* **B1. `lv_node` abort #2 under `rec_fire_levels` → `sle_go` → `lv_sub_int` → `lp_substl`**
  (owner: whnf4, `InstLP.lean`; the recursors come from the inductive install, indproofs3):
  `nest_rose_tree`, `inmodel_groups` (`check`), and `nested_rec`, `nested_struct_proj`,
  `inmodel_nested` (`check_np`): ι-reduction of a **nested** inductive's recursor. Abort #2 is
  `CTL[8 + t] <= i` at tag 0: the word handed to `lv_node` as a level is not a live level handle
  (a word of another kind, or a slice word read past its end). Reproducer:
  `scripts/e2e.py --only nested_rec`.
* **B2. `hoist_ok`** (`natop_order`, `natop_before_ble`): the ground hoist; lane front3 is on it.
* **B3. untraced** (`eager_open_nat_control` 67 KB, `inmodel_nested` under `check`,
  `arena/good/perf/app-lam` 1.2 MB): the tracer ran out of time or size; open.
* `l-timeout`s (3) and the 7 fixtures that got further with 8× larger arrays are capacities and
  speed, not verdict bugs.

Where L aborts and both references reject or decline (262), the stage agrees (`decl` for nearly
all): an `abort` in L is how every twin error is translated, so these are agreements; the top
rows are `check_value_group` abort #1 (27), `check_div_mod_pin_loop` (22, declines: D4),
`nest_uniform` (19), `infer_spine_arg` (13).
