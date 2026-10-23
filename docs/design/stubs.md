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
**After**: the run is still going (tracing every L error is slow); hand checks of the compiled
`check` on the 12 smallest fixtures: 3 **accept** (`indexed_nested_aux`, `nat_shiftleft_ok`,
`nested_pin_names`), 9 `error`. Results and the agreement with the references: next entry.
