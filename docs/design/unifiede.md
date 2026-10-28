# Lane unifiedE: one model and one refinement per function, for both outcomes

Rank 1 of `docs/design/lnext.md` §4. Until now, a function whose errors claim the twin's failure had:

* an ok model `fW` (usually written by hand) with its spec;
* an ok refinement `fW_okC` (the model's `some` refines the twin's ok run);
* an error model `fE` (`l_model … errors`);
* an error claim `fE_claim` (the model's error claims the twin's failure).

The error claim repeated the ok refinement's induction, case splits and invariant bookkeeping
line for line. A twin change touched both proofs. Several functions had both halves again under
a second invariant package (`tmnW_okPC`, `tmnE_claimP`).

Brief (user, 2026-10-28): one refinement is the direction regardless of the line savings. The
goal is uniformity: one model and one refinement per function, so that a con-ron sync touches one
place per function. Savings and elaboration times are still measured. A slower module is
flagged.

## 1. Design

### 1.1 The model: `l_model … unified`

`ConAgua/L/ModelGen.lean`, tests `tUni*` in `ConAgua/L/ModelGenTest.lean`.

`unified` is `errors` with three changes:

* **The error post is over the class.** It reads
  `fun ε => G → ε.cls ≠ 0 → fE n s₀.mem args = .error ε` (not `ε.code ≠ 0`). An error of
  class `0` leaves the model free: a load out of bounds, or an abort of a callee outside the
  verdict closure, whose code may be nonzero but whose class is `0`.
* **Callees outside the verdict closure keep their `Option` models.** A callee spec with a
  `some` post is called through `L.liftE F` (`none` becomes `.error .oob`, class `0`). Its spec is
  wrapped as `L.Triple.nv (mem (by decide +kernel)) S` (`L/ErrSpec.lean`). The wrapped spec adds
  the error post `closedNV p fs = true → ε.cls = 0`. `nv [G, mem]` names that closedness `G` and
  the membership lemma (`L.Checker.nv_mem`). `G` is an assumption of the error posts only, so a
  unified spec's ok post holds without it. Before, the error models called these callees
  through their whole run (`callE`). Every error proof then needed one `ErrClaim.of_callE_nv`
  line per such call, plus 3–4 lines to get from `callE … = .ok` back to the callee's `Option`
  model. Now the refinement sees `liftE (gW …)`: `none` is a one-line `RefE.of_cls0`, and `some`
  is the callee's model directly.
* **Unified callees are called through their unified models.** A callee listed by its unified
  spec (an `Except` post) is called as that model (`tmnE` calls `tcmE`). The caller's refinement
  then applies the callee's refinement to the model value directly.

Callees with error claims that are not migrated yet stay `callE` (`tcmE` calls
`target_params_def_eq` this way). The refinement then reads their ok half through their old `Option`
spec and `…_okC`, and their error half through their `CoreSpecE` claim, as before.

### 1.2 The refinement: `RefE` (`ConAgua/Arena/Verdict.lean`)

```
def RefE (G : Prop) (x : Except Err α) (T : AM β) (a : AState) (R : α → β → AState → Prop) : Prop :=
  match x with
  | .ok v => ∃ y a', T.run a = .ok (y, a') ∧ R v y a'
  | .error e => G → ErrClaim T a e
```

One theorem per function, by one induction over its unified model:
`f_ref : hyps → RefE (VerdictCtx p) (fE p n m args) twin a (fun v y a' => FPost … v y a')`.

* **`G`** is what the error claims assume about the program, `VerdictCtx p`
  (`Verdict/VCtx.lean`, a named-field structure): `closedNV p nvFns = true` and the core stubs'
  claims (`CoreStubsE`). Only the error arms use it. So **the ok half needs nothing new**, and
  ok refinements up the call chain do not gain hypotheses. This was the trap of the first
  version: with the hypotheses as plain arguments of `f_ref`, every ok refinement above
  `target_k53_args` would have needed `hnv`/`hcE`.
* **The post `R`** is a named-field Prop structure per function (`TcmPost`, `TmnPost`), not the
  ∧-tuple of the old `…_okC`.
* **The kit.** These lemmas carry both outcomes at once:
  * `RefE.ret` (an ok leaf);
  * `RefE.of_cls0` (an error of class `0`: abort `0`, `liftE none`, out of fuel);
  * `RefE.bind_left` (a callee's error claim);
  * `RefE.bind_right` (the twin's step ran ok; both outcomes continue);
  * `RefE.ite_pos` / `ite_neg`.
* **The halves, from a call's run, through the model's spec.** `RefE.run_ok` and `RefE.run_okW`
  turn `callE`/`callW … = ok` into the twin's ok run with `R`. `RefE.run_err` and
  `RefE.coreSpecE` give the `ErrClaim`/`CoreSpecE` of a failing run. `RefE.triple` gives the ok
  triple, the shape of the `@[refines]` theorems.

### 1.3 Callers keep their statements, through the run

The lnext plan generated an equation `fW = (fE).toOption`, so that callers' `Option` models could
keep calling `fW`. **That equation is not provable for the existing models.** It holds only
if `fE` reads every callee exactly as `fW` does. But:

* hand ok models read loads as `rdW` defaults where L aborts out of bounds, so their `some` is not
  a run;
* they call callees through other hand models (`pdeW cR`, `consW`), where `fE` has the callee's
  run or its unified model.

So `fW n … = some` does not imply `fE … = .ok`. A caller's `Option` model now reads a unified
function **through its run**:

* `cR n "f" args m` in a `CallM` model (the hand models' callee reading), named per callee
  (`tcmR`, `K53Look`);
* `callW p n "f"` in a generated model.

The caller's ok refinement gets the callee's ok half by `RefE.run_okW (fE_spec …) (f_ref …) h`.
This needs the callee's lookups (`TcmLook p`): `tkaW_okC`, `tkhW_okC` and `tkW_okC` gained one
argument `hT : TcmLook p`. Their callers pass `L.tmn.tcm` / `P.k53.tmn.tcm`.

What the pilot kept unchanged:

* the `@[refines]` theorems: same statements, proved by `RefE.triple` (`targetClassMatch_refinesC`
  now at fuel `n` with `n ≤ 2^62`, like the other `refinesC`; no users);
* `tcm_claimA` (its statement; `RefE.coreSpecE`);
* `classes_nfs`' error model and claim (two calls replaced).

The hand ok models of the pilots and their specs are gone: `tcmW`, `tcmF`, `tcmK1–6`,
`targetClassMatch_spec`, `tcmF_spec`, `tmnW`, `tmnK1–4`, `tmn_spec`. The unified model is the
function's only model.

### 1.4 Several invariant packages: one theorem with a conditional post

`target_major_nfs` had both halves twice, under `StageC` (`tmnW_okC`, `tmnE_claim`) and under the
classes' package (`tmnW_okPC`, `tmnE_claimP`: constructor slices without the bound, pointers into
`mb`). `tmn_ref` takes the weaker hypotheses (`DecB` + `< 2^64` for the constructors). It states
the extra conclusions as a field that is an implication:
`ptrs : ∀ mb ps, decNL m nfo nfl = some ps → PtrsB mb ps nfs → fresh ∧ ∃ ps', …`. One proof
replaces four.

## 2. Pilot (`ctors_have_name`, `target_class_match`, `target_major_nfs`)

* **`ctors_have_name`** has no error half: it is in the no-verdict closure (`nvFns`), and its old
  "error proof" was one `ErrClaim.of_callE_nv` line at each call site. The unified mode treats it
  as such: an `Option` callee, lifted (`liftE (chnW …)`). Its model `chnW`, spec and `chnW_ok` stay.
  So the leaf case of the bottom-up order is "a no-verdict function needs no migration".
* **`target_class_match`**: `tcmE` (unified; `target_params_def_eq` through `callE`, five no-verdict
  callees lifted), `tcm_ref` (157 lines), `TcmPost`. `tcm_claimA` and `targetClassMatch_refinesC` are
  derived from it.
* **`target_major_nfs`**: `tmnE` (unified; calls `tcmE`, lifts `chnW` and `consW`), `tmn_ref` (154
  lines), `TmnPost`, `targetMajorNfs_refinesC` derived. `classes_nfs`' refinement (`RecGen28`) and
  its error claim (`IndBNfs`) read `tmn_ref` from the run.
* **Caller `target_k53_args`**: its hand model calls `target_class_match` through `cR` (`tcmR`,
  `K53Look`; `tcmR_spec`, `Tka`), and its refinement reads `tcm_ref` through the run (`RecCheckK53`).

### 2.1 Lines

Declarations replaced (lines with their doc comments, `_tmp/unifiedE/declen.py`):

| function | before: ok refinement(s) | before: error claim(s) | before | after | change |
|---|---|---|---:|---:|---:|
| `target_class_match` | `tcmW_okC` 122, `tcmF_okC` 30 | `tcm_claim` 181, `tcm_claimA` 30 | 363 | `tcm_ref` 157 + `TcmPost` 7 + `tcm_claimA` 26 = 190 | **−48 %** |
| `target_major_nfs` | `tmnW_okC` 113, `tmnW_okPC` 134 | `tmnE_claim` 128, `tmnE_claimP` 141, `targetMajorNfs_claim` 27 | 543 | `tmn_ref` 154 + `TmnPost` 11 = 165 | **−70 %** |
| `ctors_have_name` | (`chnW_ok`, unchanged) | none (no-verdict) | — | — | — |
| the two `@[refines]` | 36 + 37 | | 73 | 37 + 38 | ±0 |
| **refinement layer** | | | **979** | **430** | **−56 %** |

`target_class_match` alone (one package) shows the per-function rate of merging the halves: about
half. `target_major_nfs` adds the merged second package.

Whole diff of the pilot's files against master (models, specs, refinements, claims, callers;
without the generator, the kit and the test): **+493 −1 409 = −916 lines**. Of the removed lines,
about 300 are the hand ok models and their specs: `TcmLook`'s `tcmK*`/`tcmW`, `TruncSl`'s arms and
specs, `TcmF`, `TcmK6`, `Tmn`'s `tmnW` part; `IndT/RecCheckTcm` and `IndT/RecCheckTmn` are gone. One-time infrastructure: +285 −23 (`RefE` kit 116,
`VerdictCtx` 19, `ErrSpec` 23, generator with its documentation +81 −23, tests 46).

### 2.2 Elaboration time

User seconds of `lean` on each module alone, three interleaved runs, base (master d6abfaec) and new
(`_tmp/unifiedE/time2.sh`, `time3.sh`; `times2–5.txt`), medians:

| module | base | new | |
|---|---:|---:|---|
| `Verdict/IndBTcm` | 2.29 | 2.30 | `tcm_ref` instead of `tcm_claim`; `thW_afr` moved in |
| `Verdict/IndBTmn` | 2.09 | **2.76** | **slower (+0.7 s)**: `tmnE`'s generated step 1.39 → 1.90 s (`finish`; with the `simp [Cmp.evalW, Cmp.eval]` recipe of the old `tmnE` it took 3.0 s), `tmn_ref` 0.33 s against `tmnE_claim` 1.52 s |
| `Verdict/IndBNfs` | 14.68 | 14.27 | noisy (14.2–16.1) |
| `Verdict/IndBTka` | 5.32 | 5.27 | |
| `Arena/IndT/RecCheckTcm` | 1.49 | — | deleted (`tcmW_okC`; `thW_afr` moved to `IndBTcm`) |
| `Arena/IndT/RecCheckTmn` | 0.79 | — | deleted |
| `Arena/IndT/RecGen28` | 4.45 | 4.07 | `tmnW_okPC` gone |
| `Arena/IndT/RecCheckK53` | 1.60 | 1.61 | |
| `Arena/RecCheckSpec/Tmn` | 3.27 | 0.80 | the hand `tmn_spec` (2.5 s) gone |
| `Arena/RecCheckSpec/TruncSl` | 1.32 | 0.54 | the hand `targetClassMatch_spec` gone |
| `Arena/RecCheckSpec/TcmLook`, `TcmF`, `TcmK6` | 1.38 | 1.17 | |
| `Arena/RecCheckSpec/K53Look` | 0.50 | 0.51 | |
| `Arena/RecCheckSpec/Tka` | 14.48 | 14.48 | 15.6 when its model called `cR n "target_class_match" [12 words] m` directly: the list literal costs `grind` 8 %; a named reading `tcmR` (the run, 12 word arguments) is at parity |
| **sum** | **53.7** | **47.8** | **−11 %** |

`IndBTmn` is the one module that got slower: its generated step now does what the deleted
hand `tmn_spec` did, and the sum over the modules is lower.

## 3. Migration of the other split functions

### 3.1 Inventory

`_tmp/unifiedE/inv.py` (master d6abfaec + this lane) finds 170 functions with an error claim or
error model and an ok refinement. The survey attributes refinement and error-claim lines to
88 of them: 11.8 k + 11.1 k lines (lnext §2, counting differently: 132 functions, 17.9 k + 14.3 k).
The error models are generated (`errors`) for all but a handful (`classes_nfs`, `nest_ctors`,
`nest_fields`, `target_k53_args`, and the hand models listed in mgen.md §1.2). Most ok models are
hand-written.

Bottom-up depth (the longest chain of split callees below a function) over the 170:

| depth | functions | refinement lines | error-claim lines |
|---:|---:|---:|---:|
| 0 (no split callee) | 67 | 5 103 | 5 352 |
| 1 | 22 | 2 006 | 1 596 |
| 2 | 20 | 2 571 | 1 330 |
| 3 | 11 | 1 726 | 992 |
| 4–5 | 12 | 1 835 | 1 540 |
| 6–19 (the `check_block` / `install_step_go` spine) | 18 | 3 132 | 1 193 |

The list with depths, files and callees: `_tmp/unifiedE/split.txt`.

### 3.2 How to migrate one function `f`

1. **Callees first.** Every split callee of `f` is either migrated (list its unified spec in
   `specs`) or stays `callE` (no spec; its ok half through its old spec and `…_okC`, its error
   half through its claim). Callees in `nvFns` are listed by their `Option` spec; add
   `nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]`. Replace
   `l_model fE_spec … errors` by `… unified nv […]`. Do not use a binder named `L` (the generator
   root-qualifies `L.`): `hL`.
2. **The post** as a named-field structure `FPost` (the conclusions of the old `…_okC` besides the
   twin's run). A second invariant package becomes extra fields, as implications from its extra
   hypotheses (§1.4).
3. **`f_ref`**: start from the old ok refinement and walk the unified model's arms:
   * at each callee, `rcases h : <callee value> with e | ⟨r, m₁⟩`;
   * the error arm is `RefE.of_cls0` (lifted, abort `0`), `RefE.bind_left (callee's ref/claim)`, or
     `fun hV => …` with the callee's `CoreSpecE` (`hV.nv`, `hV.core`);
   * the twin side is consumed by `RefE.bind_right run` as the ok proof found the runs;
   * leaves are `RefE.ret run ⟨fields⟩`.

   Take the error arms from the old claim. Typical: 2–4 lines per callee with errors.
4. **Derive what users need**: the `@[refines]` theorem (`RefE.triple`), the old `CoreSpecE` claim
   if a non-migrated caller uses it (`RefE.coreSpecE`), nothing else. Delete the old ok refinement,
   the old claim, the hand ok model with its arms and spec once no user is left.
5. **Callers**:
   * a caller whose `Option` model nests `fW` switches to the run: `cR n "f" [args] m`, its spec
     `hcR n "f"`;
   * its refinement takes `RefE.run_okW (fE_spec …) (f_ref …) h` (the caller's ok lemma gains
     `f`'s lookups);
   * a caller's error model that called `f` through `callE` takes `RefE.run_err hsT hnv ⟨hnv, hcE⟩`
     (or keeps `CoreSpecE`);
   * callers that are being migrated themselves list `fE_spec` in `specs`.
6. Pitfalls met in the pilot:
   * after `rcases` on a value, the hypotheses about `(r, m).fst` need `dsimp only` before `omega`;
   * a `by … omega` argument whose goal mentions `{ mem := m, … }.mem` needs `dsimp only` first;
   * `Err.cls_of_code` (`grind →`) is needed by the generated steps for loads out of bounds;
   * a caller's `Option` model reads the run through a named function of word arguments
     (`tcmR cR n m args := cR n "f" [args] m`, its spec `hcR n _ _ s₀`), not a list literal
     (`Tka` 8 % slower otherwise);
   * try the default `finish` recipe before `simp [...]` on the unified model (`tmnE`: 1.9 s
     against 3.0 s).

### 3.3 Batches (for migration lanes)

Ordered bottom-up; each batch is one lane's landing (or two), grouped by the Verdict file family
so that one lane owns its files:

1. **Leaves, depth 0** (67, ≈ 10.4 k lines of pairs), by family:
   * 1a: `WhnfModels2E` (`reduce_nat*`, 7) and `WhnfModels6E` (`m2c_*`, 10);
   * 1b: the positivity leaves `PosE1M`, `PosE2M`, `PosE3Cm`, `PosTopE1` (`nest_*`, 17);
   * 1c: `IndBRec1/4`, `IndBHdr`, `IndBFields`, `IndBTmm`, `IndBToi`, `IndBPins`, `IndBRecPins`,
     `IndBTpd` (`target_params_def_eq_step`; then `target_params_def_eq` at depth 1);
   * 1d: `Decl*E` (`check_value_group`, `lvl_eq_fueled`, `defn_nat_*`, `install_header`,
     `install_basis_decl`), `DefEq*E` (5), `Front*E` (`vi_*` leaves), `WhnfModels3E/E/7E`.

   `classes_nfs` (hand error model, nested loops) waits for the generator's nested-loop error
   models or stays hand-written over `tmn_ref` (§2).
2. **Depth 1–2** (42, ≈ 7.5 k): `target_params_def_eq`, `whnf_telescope`, `install_value`,
   `check_constant_val`, `check_thm_val`, the `check_block_*_one` functions, `class_*_ok`,
   `target_major_pins`, `target_major_of_outside(_tail)`, `vi_*`. `target_class_match` is done.
3. **Depth 3–5** (23, ≈ 6.1 k): `check_abs_ctor_sorts_all`, `class_rec_tys_ok`,
   `class_rules_ok`, `check_div_mod_pin*`, `target_k53_args` (hand error model: replace it by
   the unified model), `target_k53_heads`, `target_k53`, `target_major_of*`, `check_block_tele(s)`,
   `class_majors`, `validate_ind_d`.
4. **The spine, depth 6–19** (18, ≈ 4.3 k): `apply_ind`, `check_block_inds`/`classes`/`pass`,
   `class_nodes_agree`, `class_fields_agree`, `class_ctor(s)_of`, `classes_ctors`,
   `gen_rec_check(_prep)`, `check_block(_tail, _rec)`, `check_ind_decl`, `check_decl`,
   `install_step_go`. One lane, in order.

Expected total, at the pilot's rates: about −50 % of the pair lines. That is **−12 to −16 k lines**
over the 32.2 k (lnext's count), more where a second invariant package merges. On top, the hand
ok models and specs that the unified models replace: ≈ 4.3 k lines (spec, word model and
equation layers of the 88 attributed functions), most of them removable.

### 3.4 Retiring the separate error machinery

After batch 4:

* `errors` mode (its `code ≠ 0` post) has no users. `unified` becomes the only error mode, and
  the keyword can become the default for functions outside `nvFns`;
* the `fE_claim` theorems are gone;
* `triple_of_callE_err … Err.code_ne_of_cls` and `CoreSpecE.of_runs` remain only in the core
  stubs' claims;
* `ErrClaim`, `CoreSpecE` and `callE_spec` stay (the `RefE` kit is built on them; callees
  without a spec);
* the hand `Except` models of mgen.md §1.2 go with their functions' batches.

### 3.5 Batch 1d (`Decl*E`, `DefEq*E`, `Front*E`, `WhnfModels3E/E/7E`)

**Landing 1: the definition arm's and phase B's leaves.** Four functions:

| function | before: ok refinement + error claim | after | change |
|---|---|---:|---:|
| `install_basis_decl` | `ibdW_ok` 39 + `ibdE_okT` 44 = 83 | `ibd_ref` 36 + `IbdPost` 4 = 40 | −52 % |
| `check_value_group` | `cvgW_okT` 175 + `cvgE_okT` 245 = 420 | `cvg_ref` 197 + `CvgPost` 5 + `CvgCtx` 3 = 205 | −51 % |
| `defn_nat_cert` | `defnNatCert_okC` 102 + `defnNatCertE_okC` 136 = 238 | `dnc_ref` 115 + `DncPost` 5 = 120 | −50 % |
| `defn_nat_gate` | `defnNatGate_okC` 98 + `defnNatGateE_okC` 145 = 243 | `dng_ref` 117 + `DngPost` 6 + `defnNatGate_okC` 15 (from the run) = 138 | −43 % |
| **sum** | **984** | **503** | **−49 %** |

Also gone: the hand ok models and their specs (`ibdW`/`ibdK*`/`ibd_specW`, the `cvgW` block with
its arms and `cvg_specW`, the generated `defnNatCertW`/`defnNatGateW`). Whole diff: +487 −1 099.

Choices:

* **`G` is what the error arms assume**, not always `VerdictCtx p`: `True` for
  `install_basis_decl` (its only failure is its own abort), `CvgCtx p` (the core stubs' and
  `install_value_guards`' claims) for `check_value_group`, `CoreStubsE p` for the gates. The
  callees outside the verdict closure need nothing in `G` (their errors are `liftE`'s `.oob`).
  `VerdictCtx` (`Verdict/VCtx.lean`) imports `DeclValE`, so the `Decl` files cannot use it anyway.
* **Callers kept their statements where cheap**: `defnNatGate_okC` and `natGateSpecE_of` are now
  one-liners from the run (`RefE.run_okW`, `RefE.run_err`), so `DeclDefnT`/`DeclDefnE` did not
  change. `checkValueGroup_specT` (`PhaseBT`) is `RefE.triple`; `checkPending_errT` takes `hnv`
  instead of three `NVAt` hypotheses.
* **Placement**: a unified refinement sits where its ok users can import it: `ibd_ref` in
  `Arena/DeclBasisSpec` (used by `install_basis_decls`' ok refinement), `dnc_ref`/`dng_ref` in
  `Arena/DeclNatGateT` (with `certify_nat_eqs`' error model and claim, moved there from
  `DeclGatesE`; that file now imports `DeclValE` for `CoreStubsE`), `cvg_ref` in `DeclValE`
  (`PhaseBT` imports it).

Elaboration (user seconds, `lean` on the module alone, median of 3 interleaved runs, base master
63762a3f; load 30–75, so ±15 % is noise; two series for the flagged modules):

| module | base | new | |
|---|---:|---:|---|
| `Verdict/DeclValE` | 7.87 / 5.63 | 12.58 / 10.27 | **slower (+4.6 s)**: `checkValueGroupE`'s generated steps. Measured alone: `errors locals` 3.5 s, `unified locals` with all callees `callE` 9.7 s, with the three no-verdict callees lifted 7.9 s; `unified` without `locals` the same, `finish` fails (26 s). The unified error post (`G → ε.cls ≠ 0 → …`) costs the `simp` steps about twice `errors`' |
| `Arena/DeclCvg`, `DeclCvgT`, `PhaseBT` | 7.18, 2.53, 3.73 | 3.93, 0.88, 2.69 | `cvgW` and its spec, `cvgW_okT` gone |
| `Arena/DeclNatGateT` | 1.63 / 1.24 | 4.02 / 3.64 | **slower (+2.4 s)**: the gates' unified models and `certE_okT` moved in |
| `Verdict/DeclGatesE` | 5.90 | 0.73 | the gates' error models and claims gone |
| `Arena/DeclNatGateSpec` | 2.72 | 0.89 | the generated `W` models gone |
| `Arena/DeclBasisSpec` | 3.11 / 2.51 | 3.63 / 2.19 | noise (first series under load) |
| `Verdict/DeclBasisE` | 5.11 / 4.29 | 5.85 / 3.53 | noise |
| `DeclHeader`, `DeclHdrE`, `DeclPendE`, `TopE` | 15.72 | 13.39 | |
| **sum (first series)** | **55.5** | **48.6** | **−12 %** |

Not migrated in this batch, and why:

* **`lvl_eq_fueled`**: its hand models `lfW`/`lveC` are nested in the models of
  `check_thm_val` (`tvK4`), the agree body (`DomsW`) and the positivity walk (`NestOccAny`, `NitW`,
  `NtyW`; batch 1b's files); deleting them means switching all of these to the run at once.
  Better after batch 1b.
* **`install_header`**: its hand model `ihW` and `ihW_okT` are shared with
  `class_const_ok_header` (the same body, batch 1c's `IndBHdr`, `RecGen3`); migrating it alone
  would leave two refinements of one body. Better together with, or after, batch 1c.
* **`Front*E` (`vi_unsafe`, `vi_np_go`, `vi_ctor`, `vi_rec_idx`)**: their ok halves are facts about
  the model (`unsafeW_twin`: no record is unsafe), not twin runs, and their error halves are
  `VerdictClaimL` about the whole `validateIndD` (failures as record verdicts). `RefE` fits
  neither; it needs a variant over `ErrClaimV`-style twins with a `Prop` ok post (a kit change).

### 3.6 Batch 1c, first landing (`IndBTpd`, `IndBTmm`, `IndBToi`, `IndBPins`, `IndBRecPins`)

Migrated: `target_params_def_eq_step` and `target_params_def_eq` (`pds_ref`, `pde_ref`;
`target_class_match`'s `tcmE` now calls `pdeE` as a unified callee, and `tcm_ref` takes both halves
from `pde_ref`), `target_major_of_member` (`tmm_ref`), `target_outside_inst` (`toi_ref`),
`target_pin_tys` (`tpt_ref`), `target_rec_pins` (`trp_ref`). Posts are named-field structures
(`TpdPost`, `PdsPost extends TpdPost` with the core step, `TmmPost`, `ToiPost`, `TptPost`, `TrpPost`).
The `@[refines]` theorems keep their statements (`RefE.triple`); `targetParamsDefEq_claim`,
`tmm_claim`, `targetOutsideInst_claim`, `targetPinTys_claim`, `targetRecPins_claim` are gone (their
callers read `RefE.run_err`). Deleted hand models with their arms and specs: `pdsW`/`pdsK1–11`,
`pdsF`, `pdeW`/`pdeK1`, `tpdStep_spec`, `tpd_spec`, `pdsC_ok`; `tmmW`/`tmmK1–4`, `tmm_spec`;
`toiW`/`toiK1–5`, the hand `targetOutsideInst_spec`; `tptW`/`tptK*`, `targetPinTys_spec`;
`trpW`/`trpK1–6`, `trp_spec`.

Findings:

* **A unified model whose refinement does not need its lookups drops them.** `pds_ref`,
  `pde_ref` and then `tcm_ref` lost their `TpLook`/`TcmLook` argument: the lookups are needed by
  the spec (`RefE.triple`, `RefE.run_err`), not by the refinement of the model value.
* **A caller of a unified callee that is not unified itself also needs `nv`**: `pdeE` has no
  `Option` callee, but `pdsE_spec`'s error post assumes `closedNV`, so `pdeE` takes
  `nv [closedNV …, nv_mem]` to have it in its own error post.
* **A unified callee in tail position has no continuation**: `tcmE.k_target_holes.arm1` ends in
  `pdeE …` directly, so the old `tcmE.k_target_params_def_eq` is gone.
* **The post of a recursive call is from its own start**: `pde_ref`'s inductive step carries the
  growth across (`hg1.trans hR2.grow`), 3 lines; a kit lemma `RefE.mono` (weaken `R` under an
  implication) would make it one.
* **`G`**: the leaves that call no core stub (`target_major_of_member`, `target_outside_inst`) state
  their refinement under `G := closedNV p nvFns = true`, not `VerdictCtx p`: their callers'
  error claims (`tmcE_claim`, `tmtE_claim`, not migrated) have `hnv` only.
* **Skipped: `class_rule_ok_guards`** (`IndBRec4`). Its error half needs `UceProg p` (with
  `StrLitSupportedOK`, a semantic fact) for `uce_errClaim_hi`; as a plain hypothesis of the
  refinement it would reach every ok refinement above (`cruleW_okC`, `RecGen9`), the trap of §1.2.
  It needs `VerdictCtx` (or a variant) to carry `UceProg`, a kit change; batch 1d's `Decl*E` meet
  the same. Its twin side also needs a guards-prefix definition (`classRuleOk = guardsT >>= rest`).

Lines (`declen.py`, master 63762a3f against this branch; before = ok refinement(s) + error claim(s)):

| function | before | after | change |
|---|---|---|---:|
| `target_params_def_eq(_step)` | `pdsC_ok` 73, `pdsR_okC` 105, `pdsW_okC` 41, `pdeW_okC` 94; `pdsStep_claim` 280, `pdeE_claim` 94, `targetParamsDefEq_claim` 26 = 713 | `pds_ref` 227 + `pde_ref` 88 + posts 12 = 327 | **−54 %** |
| `target_major_of_member` | `tmmW_sim` 174; `tmmE_claim` 154, `tmm_claim` 20 = 348 | `tmm_ref` 167 + `TmmPost` 7 + `tmmE_kpl` 7 = 181 | **−48 %** |
| `target_outside_inst` | `toiW_ok` 101; `toiE_claim` 175, `targetOutsideInst_claim` 15 = 291 | `toi_ref` 150 + `ToiPost` 7 = 157 | **−46 %** |
| `target_pin_tys` | `tptW_okC` 58; `tptE_claim` 67, `targetPinTys_claim` 15 = 140 | `tpt_ref` 60 + `TptPost` 5 = 65 | **−54 %** |
| `target_rec_pins` | `trpW_ok` 117; `trpE_claim` 203, `targetRecPins_claim` 12 = 332 | `trp_ref` 199 + `TrpPost` 5 = 204 | **−39 %** |
| `tcm_ref` (caller) | 157 | 144 | |
| **pairs** | **1 824** | **934** | **−49 %** |

Whole diff of this landing against master 63762a3f (models, specs, refinements, callers, imports):
**+873 −2 278 = −1 405 lines** in 30 files.

Elaboration (user seconds, `lean` on the module alone, median of 3 interleaved runs, base master
63762a3f, `_tmp/unify-b1c/time.sh`, `times1.txt`; load 10–30):

| module | base | new | |
|---|---:|---:|---|
| `Verdict/IndBTpd` | 5.51 | 5.01 | |
| `Arena/IndT/RecCheckTpd`, `RecCheckSpec/Tpd`, `TaGoWMfr`, `PdsC`, `BvbWStageC` | 9.75 | 3.11 | the hand models, `tpdStep_spec`/`tpd_spec` and the ok refinements gone |
| `Verdict/IndBTcm`, `IndBTmn`, `Arena/IndT/RecCheckK53` | 7.00 | 6.83 | |
| `Verdict/IndBTmm` | 22.01 | **32.22** | **slower (+10.2 s)**: `tmmE`'s generated `simp` steps (now with the four callees' specs; `finish` fails, `locals` 39 s) |
| `Arena/IndSumSpec/ParamLevels` | 8.87 | 0.78 | the hand `tmm_spec` gone; with `IndBTmm`: 30.9 → 33.0 (+7 %) |
| `Verdict/IndBToi` | 2.44 | **3.99** | **slower (+1.6 s)**: `toiE`'s steps (`finish` fails, `locals` 6.0 s) |
| `Arena/RecCheckSpec/ToiW` | 1.84 | 0.48 | the hand `targetOutsideInst_spec` gone; with `IndBToi`: 4.3 → 4.5 |
| `Verdict/IndBRecPins` | 4.19 | **6.76** | **slower (+2.6 s)**: `trp_ref` and `targetRecPins_refines` moved in (`finish` 7.5 s, `locals` 10.0 s) |
| `Arena/RecCheckSpec/TargetRecPins` | 5.31 | 3.49 | the hand model and `trp_spec` gone; with `IndBRecPins`: 9.5 → 10.3 |
| `Arena/RecCheckSpec/ErToIwWStage` | 11.00 | 8.92 | `targetPinTys_spec` gone, `tptR` in |
| `IndBPins`, `IndBGrp`, `IndBClm`, `RecCheckPins`, `RecGen19`, `GenRec1` | 11.40 | 11.11 | |
| `IndBTmc`, `IndBTmt`, `IndBTmo`, `RecGenTmf`, `DecTMDecBOf`, `OcW` | 19.34 | 18.88 | |
| **sum** | **108.7** | **101.6** | **−7 %** |

Each flagged module is offset by the module that held the deleted hand spec, except `IndBRecPins`
(+0.8 s over the pair).

### 3.7 Batch 1a (`WhnfModels2E`: `reduce_nat*`; `WhnfModels6E`: `m2c_*`)

All 17 functions migrated in one landing: the `reduce_nat` family (7) and `major_to_ctor`'s pieces
(10). `major_to_ctor` itself keeps its `errors` model (a wrapper outside the batch); its claim
`majorToCtorE_of` is `m2cHead_ref`'s error half through the run (`RefE.run_err`), its ok refinement
`majorToCtor_refines'` the ok half (`RefE.growRefW`).

| family | before: ok refinements + error claims | after | change |
|---|---|---:|---:|
| `reduce_nat*` (7) | `callW_reduceNat*` 799 + `callE_reduceNat*` 519 = 1 318 | `reduceNat*_ref` 584 | **−56 %** |
| `m2c_*` (10) | `m2c*_ok` 956 + `m2c*E_ok` 830 + the hand error model `m2cAnd2HE` 37 = 1 823 | `m2c*_ref` 868 | **−52 %** |
| shared pieces | | `CorePost` + `RefE.coreSpec` (`KnotE`), `RefE.tail(_eq)`, `CorePost.relist`, `GrowPost` + 3 lemmas, `M2CCtxE`, `PreOk`/`PreRef`, `and2Push_of` | ≈ +150 |

Also gone: the generated `W` models of `reduce_nat*` (`WhnfDeltaRefine3`), the hand `W` models of
`m2c_*` with their specs (≈ 330 lines, `WhnfM2CRefine`), `CoreRef.congr`. Whole diff of the
batch against master: +1 403 −3 403 (including the imports the new import graph makes redundant).

Choices:

* **`G` is the knot's error half at the callees' fuel.** These functions are called from the
  knot's slots, and their errors are the slots' (`whnf`, `infer_io`, `defeq`): `G` is
  `KnotUpToE p n` for `reduce_nat*` and `M2CCtxE p n` (`KnotUpToE` and `ProofIrrelWE`, `proof_irrel`
  being outside the knot) for `m2c_*`. The ok halves need only `KnotUpTo`, as before.
* **The post is `CoreRef`'s, as a structure** (`CorePost dec dn m₀ vis fe M eb ok`: the relation
  after the run, the result decoded, the result words valid), so the `CoreSpec` statements of the
  knot (`ReduceNatSpec'`, `MajorToCtorOK`) are `RefE.coreSpec` one-liners. The arms that leave a
  slice on the stack use `GrowPost` (`CoreAfterG`, `GrowRef`).
* **`m2c_pre` is not a twin function**: it runs a prefix of each arm (`m2cPreT … k`), so an ok run
  is not an ok run of a twin computation. Its refinement is `PreRef`: the ok value gives the twin's
  prefix (`PreOk`, around the old `PreRun`), an error claims the failure of `m2cPreT … k` for every
  continuation `k`. Its callers apply it as before.
* **Tail calls** (`reduce_nat_head` → `_k`/`_ap`, `m2c_arms` → the arms, …): the caller's model
  re-lists the callee's result, the twin runs the callee's twin from some state. `RefE.tail` takes
  the callee's `RefE` through both (`RefE.tail_eq` when the runs are equal); each such call is
  3–6 lines.
* **Placement.** The knot's ok side (`DefEqKnot`, `WhnfDeltaRefine4`'s `whnf_step`) uses these
  refinements, so they sit below it: `reduce_nat*` in `Verdict/WhnfNatE` (no longer importing
  `WhnfSlotE`; `DefEqKnot` imports it; `ReduceNatE`, `reduceNat_refines` moved in), `m2c_*` in
  `Arena/WhnfM2CRefine2..5` in place of the ok refinements (importing `WhnfModels6E` and `KnotE`;
  `ProofIrrelWE` moved to `WhnfM2CRefine2`). `ErrClaim.of_run_err`/`of_run_eqW` moved from
  `WhnfSlotE` to `KnotE`. The new graph makes about 45 imports elsewhere redundant (removed, shake).
* **Two model recipes changed**: `m2c_eta`'s unified model by the default recipe (`simp []` needed
  `heartbeats 1000000` and took 16 s; default 8 s). For `reduce_nat*` `simp []` stays: the default
  recipe and `finish … gen 30` fail, `simp [] locals` is slower.

Elaboration (user seconds, `lean` on the module alone, median of 3 interleaved runs, base master
63762a3f, load 17–32):

| module | base | new | |
|---|---:|---:|---|
| `Verdict/WhnfModels2E` | 29.41 | 34.01 | **slower (+4.6 s, +16 %)**: the unified models do the work of the deleted `W` models' steps (below) with the callee specs lifted; recipes tried above |
| `Arena/WhnfDeltaRefine3` | 13.86 | 3.72 | `W` models of `reduce_nat*`, three ok refinements gone |
| `Verdict/WhnfNatE` | 5.47 | 1.61 | |
| `Arena/WhnfDeltaRefine4`, `DefEqKnot`, `KnotE` | 4.30 | 3.30 | |
| `Verdict/WhnfSlotE`, `WhnfMidE`, `WhnfKnotE` | 4.28 | 4.08 | |
| `Verdict/WhnfModels6E` | 18.03 | 14.95 | `m2c_eta` by the default recipe |
| `Arena/WhnfM2CRefine` | 18.12 | 2.56 | hand `W` specs gone |
| `Arena/WhnfM2CRefine2..5` | 7.46 | 6.56 | |
| `Verdict/WhnfM2CE`, `WhnfPirrE`, `WhnfStuckE` | 6.74 | 3.00 | the claims gone |
| **sum** | **107.7** | **73.8** | **−31 %** |

For the generator/kit (not changed here): `CorePost`/`RefE.coreSpec` (and the `GrowPost` variant)
are the `RefE` form of `CoreRef`/`CoreSpec` for every knot function (batch 1d's `WhnfModels3E/E/7E`
will want them; they sit in `Arena/KnotE`); `RefE.tail` (a tail call whose continuation re-lists the
callee's value) recurs in every nested family and belongs to the kit; a `PreRef`-like shape (an ok
half that is not a twin run) recurs for prefixes of twin functions.
