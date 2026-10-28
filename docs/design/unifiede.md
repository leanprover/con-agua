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
* **The kit** (§1.5) carries both outcomes at once, and gives the halves from a call's run
  through the model's spec.

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

### 1.5 The kit

Every lemma below exists once; a batch lane uses these and does not define local copies (a
missing shape is a kit change, reported, not a local helper).

**`RefE` (`Arena/Verdict.lean`)**, a model value against an ok run of a twin computation:

* steps, both outcomes at once: `RefE.ret` (an ok leaf), `RefE.of_cls0` (an error of class `0`:
  abort `0`, `liftE none`, out of fuel, a load out of bounds), `RefE.bind_left` (a callee's error
  claim), `RefE.bind_right` (the twin's step ran ok; the rest decides), `RefE.ite_pos`/`ite_neg`;
* `RefE.mono` (a weaker post: a recursive call's post is from its own start), `RefE.of_run_eq`
  (another twin with the same run), `RefE.tail` / `RefE.tail_eq` (a tail call whose continuation
  re-lists the callee's value, against a twin that runs as the callee's);
* the halves from the call's run, through the model's spec: `RefE.run_ok` / `run_okW` (the ok
  half from `callE`/`callW … = ok`), `RefE.run_err` (the `ErrClaim` of a failing run),
  `RefE.coreSpecE` (as `CoreSpecE`), `RefE.triple` (the ok triple, the `@[refines]` shape);
* `ErrClaim.of_run_eqW`, `ErrClaim.of_run_err` (a claim through equal or failing runs),
  `callW_of_callE` and `callE_of_callW`;
* a twin's prefix (its guards as a function of their own, `crgT`, `cchT`, `rgT`) split off a
  `do` block that copies the rest into each guard's branches:
  `simp only [prefix, bind_assoc, ite_bindAM, fail_bindAM, pure_bind]` (`crgT_bind`).

There is no lemma from a unified model's ok value back to the call's run: the model does not
model bounds (a load is `rdW`) or fuel failures of class `0`, so an ok model value does not make
the run ok. An arm that needs the run (a callee's write-set frame, `run_memFrame`) calls the
callee through `callE` and reads both halves (`RefE.run_ok`, `RefE.run_err`).

**`RefC` (`Arena/Verdict.lean`)**, a model value whose ok half is a fact, not a twin run:
`RefC G x Ok C` says an ok value satisfies `Ok v` and an error `e` the claim `C e` under `G`.
The shapes it covers:

* a function that stands for a prefix of a twin function (`m2c_pre`'s `PreRef`: the ok value
  gives the prefix's run, an error claims the failure of the prefix with every continuation);
* a check whose ok result is a fact about the model (`vi_unsafe`: no type record is unsafe);
* a twin that reports failures as values: `C := ErrClaimV T a` or `VerdictClaimL T a`.

Its lemmas: `RefC.mono`, `RefC.run_ok` / `run_okW`, `RefC.run_err` (with `C0`: the claim holds
for errors of class `0`, as every claim of the verdict closure does).

**Core functions (`Arena/RefECore.lean`)**, the functions the knot's slots call, whose ok halves
are `CoreRef`s: the post `CorePost` (the relation after the run, the result decoded and valid),
`RefE.coreSpec` / `CoreSpec.of_refE` (the knot's `CoreSpec` from the refinement), `CoreRef.post`,
`CorePost.ret`, `RefE.bind_core` (a kept-stack callee, then the rest). For arms that leave a
slice on the stack: `CoreAfterG`, `GrowRef`, `GrowPost` with `GrowPost.growRef`, `of_core`,
`of_tail`, `RefE.growRefW`, `RefE.bind_grow` / `bind_growK`.

**`G`, what the error arms assume (`Verdict/VCtx.lean`).** One rule: `G` is the weakest of these
that the function's error arms need, so that callers with less in their context can use the
refinement:

* `True`: its only errors are its own aborts (`install_basis_decl`);
* `closedNV p nvFns = true`: its callees with errors are outside the verdict closure (lifted) or
  unified under this `G` (most leaves of the inductive checks);
* `CoreStubsE p`: the core stubs' claims and no lifted callee (the nat gates);
* `VerdictCtx p`: both; `VerdictCtxU p`: also `UceProg p` (`unresolved_consts_error`'s program:
  the consts-resolve sites);
* the knot's claims (`KnotUpToE p n`) or a family's named-field structure, where non-migrated
  callees' claims are needed (`CvgCtx`, `M2CCtxE`, `PeelG`, `NrtG`, …). Such a structure takes
  `VerdictCtx`'s fields by name (`nv`, `core`) so that callers pass `hG.nv`.

`CoreStubsE` and `VerdictCtx` sit below `Verdict/DeclValE.lean` (in `VCtx`), so the `Decl` files
can use them.

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
   * a load out of bounds is `.error .oob` exactly (`ld64_rdW_specE`, `L.ld8_specE`), so the
     generated steps close its error goal by `simp` (with a post over the code they needed
     `Err.cls_of_code` and `grind` at every load);
   * a caller's `Option` model reads the run through a named function of word arguments
     (`tcmR cR n m args := cR n "f" [args] m`, its spec `hcR n _ _ s₀`), not a list literal
     (`Tka` 8 % slower otherwise);
   * try the default `finish` recipe before `simp [...]` on the unified model (`tmnE`: 1.9 s
     against 3.0 s).
   * an induction hypothesis applied in a `have` with tactic arguments (`ih (by omega) …`,
     `HSl0.of (by rw …)`): the tactic arguments run before the implicit arguments are fixed by
     unification, so `omega`/`rw` see metavariables. Name the implicits
     (`ih (ao := ao + 1) (al := al - 1) …`) or apply it where the goal is known (`exact`,
     `refine`), as `pde_ref` and `cfg_ref` do.
7. Callee specs the generator lifts in `unified` mode (no wrapper needed): an `Option` model
   (`some (r.headD 0, m)`, `some (r, m)`, a tuple), a total model (`r.headD 0 = F`,
   `r ≠ [] ∧ r = F` as `e_view`'s, `s'.mem = F`), one result as a list
   (`some ([r.headD 0], m)`). `↦ fW tuple` counts the `return`s of the named blocks spliced into
   the body (a loop's `return (k, x, y)`). A post's length conjunct
   (`r = [r.headD 0, r.getD 1 0, …]` or `r.tail.headD 0`) is accepted and, under `simp […]`,
   taken apart by `L.List.eq_headD_cons` (it no longer loops `simp_all`): list the spec as it
   is, no primed variant. A guard without a `Decidable` instance (`flush_caches`' `FlushOK`) is
   decided classically (the definitions `noncomputable`), no `open Classical in`; a generated
   definition holding `sorry` stops the command with an error.

### 3.3a Rules for batch lanes

* Use the kit (§1.5); do not define local copies of its lemmas. A missing shape or generator
  feature is reported to the coordinator, with the function that needs it, and the function is
  skipped until the kit has it.
* `G` by the rule of §1.5: the weakest assumption the error arms need, named.
* The post is a named-field structure; a second invariant package is a conditional field (§1.4).
* One model and one refinement per function: delete the hand ok model, its arms and spec, the
  old ok refinement and the error claim once no user is left; derive the `@[refines]` theorem
  and any `CoreSpecE` a non-migrated caller needs as one-liners (`RefE.triple`,
  `RefE.coreSpecE`).
* Place the refinement where its ok users can import it; the old Verdict file keeps one-liners.
* Measure the modules touched (user seconds, median of 3 interleaved runs, base and new); a
  module more than 10 % slower is flagged with what was tried (`finish` before `simp […]`).
* Merge master before each landing: the kit and the generator are shared, a sibling's landing
  may change imports (shake).

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

**Landing 2: the knot families' leaves** (`DefEq*E`, `WhnfModels3E/E/7E`). Nine functions:

| function | before: ok model/spec + ok refinement + error claim | after: ref + post + derived | change |
|---|---:|---:|---:|
| `whnf_top` | 39 | 26 | −33 % |
| `whnf_core_loop` | ≈ 170 | ≈ 93 | −45 % |
| `defeq_lst` | 174 | 106 | −39 % |
| `defeq_list_rev` | 183 | 111 | −39 % |
| `lazy_delta_reduction` | 165 | 83 | −50 % |
| `lazy_delta_proj_reduction` | 180 | 119 | −34 % |
| `defeq_lams` | 267 | 136 | −49 % |
| `defeq_peel` | 315 | ≈ 214 | −32 % |
| `proof_irrel_half` (with `proof_irrel`'s ok and error proofs over it) | 432 | 276 | −36 % |
| **sum** | **≈ 1 925** | **≈ 1 164** | **−40 %** |

Plus 81 lines of shared helpers in `Arena/KnotE.lean`; whole diff +1 047 −1 726.

* **Placement**: as in landing 1, the unified model and its `…_ref` sit in the Arena file of the
  ok side (`DefEqMidLoops`, `DefEqMidLazy2`, `DefEqStuckProj`, `DefEqMidLams`, `DefEqMidPeel`,
  `WhnfCoreLoop`, `WhnfIotaRefine4`, `IndTwin`), because the knot's construction (`KnotUpTo`,
  `DefEqKnot`, `KnotTagged`, `KnotEntry`) needs the ok halves there. The Verdict files keep the
  old `…_refinesE` as one-liners (`RefE.coreSpecE`).
* **`G`**: `KnotUpToE p n` where that suffices, else a named-field structure of the non-migrated
  callees' `CoreSpecE` claims and the no-verdict callees' class-`0` facts (`CoreStepE`,
  `LazyIterUpToE`, `LdprG`, `LamsG`, `PeelG`, `PihG`).
* **Ok halves**: the slot theorems (`CoreSpec`) are one-liners through `CoreSpec.of_refE`
  (`KnotE.lean`: batch 1a's `RefE.coreSpec` for a model value that `w` reads back as `(r, m)`;
  over 1a's `CorePost`, with `RefE.bind_core`, `CorePost.ret`); `defeqPeel_refines` keeps its
  `GrowRefP` shape (batch 1a's `GrowPost`, moved down to `WhnfCoreProj`; `RefE.bind_grow`).
* **`proof_irrel_half`**'s twin was a relation (`PiHalfRun`); it is now a computation
  (`piHalfA : AM (Option Bool)`, `piHalfT_eq`), so that `RefE` applies. `PiHalfRun`, `pihW`,
  `growRef_ret`, `growRef_bindK`, `GrowRefP.of_core` are gone.
* **Callers**: `whnfTop_refinesE` needs the ok knot (`∀ n, KnotOK p n`) and moved to its user
  `PosKnotE`; `whnfTop_stageE` gained it (`IndA9`, `IndBWt` pass `knotOK`). `whnfCoreLoop_err`
  moved to `WhnfCoreSlot`.
* **For the kit/generator** (not changed here): `RefE.of_run_eq` and `RefE.mono` (`KnotE.lean`)
  are generic and belong next to `RefE`; the `tuple` mode on `lazy_delta_reduction` (three result
  words) kept only two in the unified model, so it uses `list`.

Elaboration (as above; base master 488d6d54, load 7–30):

| module | base | new | |
|---|---:|---:|---|
| `Arena/WhnfCoreLoop` | 3.35 / 3.22 | 4.13 / 3.83 | **slower (+0.7 s)**: the unified loop model moved in (`simp` instead of `finish`: the same) |
| `Verdict/WhnfModelsE` | 13.67 | 13.19 | its old home |
| `Arena/WhnfIotaRefine4` | 5.69 / 5.61 | 6.31 / 6.14 | +0.6 s: `pihE` moved in |
| `Verdict/WhnfModels3E` | 11.42 | 9.71 | its old home |
| `Arena/DefEqMidLams`, `DefEqMidPeel` | 6.35, 10.37 | 5.09, 8.37 | |
| `Verdict/DefEqLoopsE`, `DefEqLamsE`, `DefEqPeelE`, `WhnfPirrE` | 14.17 | 6.47 | the claims gone |
| `Verdict/IndBWt` | 5.44 / 5.37 | 6.21 / 5.38 | noise |
| the other 14 modules | 131.3 | 131.6 | |
| **sum (24 modules)** | **188.3** | **177.2** | **−6 %** |

Batch 1d in all: 13 functions migrated, the pair lines ≈ 2 910 → ≈ 1 670 (−43 %); `lvl_eq_fueled`
and `install_header` wait for batches 1b/1c, the `vi_*` leaves for a `RefE` variant (above).

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

### 3.8 Batch 1c, second landing (`IndBRec1`, `IndBFields`)

Migrated: `class_key_of` (`kof_ref`, `KofPost`; `classKeyOf_refines` moved to `IndBRec1`, same
statement), `class_minor_slot` (`cms_ref`, `CmsPost`; the `DecB` slices of the second invariant
package are a conditional field `ihsB`, §1.4; `class_minor_slot_go` stays a run, its spec's `∃`
post is no model the generator reads), `class_rec_ty_ok_guards` (`rg_ref`, `RgPost`),
`class_fields_of_go` (`cfg_ref`, `CfgPost`, by induction; all seven callees lifted). The callers'
error claims (`IndBCtor`, `IndBRec2`'s `classRecTyOk_claim`, `IndArmE`'s `classKeyOfE_of`) read
`RefE.run_err`, their ok refinements `RefE.run_okW`; `cfoW` calls `class_fields_of_go` through
`callW`, and `cfoW_sim`/`classFieldsOf_refines` moved into `IndBFields`.

* **A function that stands for a prefix of a twin function**: `class_rec_ty_ok_guards` has no twin
  of its own; its old ok proof (`rgW_sim`), its pass lemma (`rgW_pass`) and its claim (`rgE_claim`,
  over `do …guards…; rest` for any `rest`) were three copies of the guard analysis. Now one twin
  definition of the prefix, `rgT` (the guards, ending in `pure ci`), with `rgT_bind :
  classRecTyOk … = rgT … >>= rest`, and `rg_ref` against `rgT`. The hand model `rtoW` reads the
  guards through `cR` (`rtoW_simC`, `rtsW_simC` gained `hrp : RtoProg p`, three call sites).
  `class_rule_ok_guards` (skipped in §3.6) has the same shape.
* **`G := closedNV p nvFns = true`** for all four (no core stub below them), as in §3.6.
* **Skipped: `class_const_ok_header`** (`IndBHdr`). Its ok half is `install_header`'s model `ihW` and
  `ihW_okT` (the same body), and batch 1d skipped `install_header` for the same reason (§3.5): each
  waits for the other. They should be migrated together, by one lane: one unified model of the
  body, one refinement, used by both.
* **Recipe**: `classRecTyOkGuardsE` with `simp []` (the old `errors` recipe) took 13.0 s for the
  module; with the default `finish` 5.0 s. `cfgE`, `classKeyOfE`, `classMinorSlotE` keep theirs
  (`finish` fails or is slower).

Lines (`declen.py`, master 63762a3f against this branch; before = ok refinement(s) + error claim(s);
the `rg` row includes `rgT`/`rgT_bind` after, the `cms` row the reworked scan lemmas `cmsGo_hits`,
`cmsGo_decB`):

| function | before | after | change |
|---|---:|---:|---:|
| `class_key_of` | 155 | 93 | **−40 %** |
| `class_minor_slot` | 212 | 170 | **−20 %** |
| `class_rec_ty_ok_guards` | 361 | 185 | **−49 %** |
| `class_fields_of_go` | 374 | 179 | **−52 %** |
| **pairs** | **1 102** | **627** | **−43 %** |

The hand models, arms and specs deleted on top: about 250 lines. Whole diff of this landing
against the first one (2853d80e): **+658 −1 317 = −659 lines** in 21 files.

Elaboration (as §3.6, `times2.txt`; load 14–25; `IndBRec1` new after the recipe change, 3 runs
5.00–5.24):

| module | base | new | |
|---|---:|---:|---|
| `Verdict/IndBRec1` | 5.93 | 5.02 | the three refinements; 13.78 with `simp []` for `classRecTyOkGuardsE` |
| `Verdict/IndBFields` | 3.98 | **4.45** | **slower (+0.5 s)**: `cfoW`, its spec and `cfoW_sim` moved in |
| `Arena/RecGenSpec/ClassFieldsOf` | 3.03 | 0.72 | …moved out of here; with `IndBFields`: 7.0 → 5.2 |
| `RecGenSpec/ClassConstOk`, `ClassKeyCanon`, `ClassMinorSlot`, `RgW`, `CntW` | 16.62 | 13.24 | hand models and specs gone |
| `IndBCtor`, `IndBRec2`, `IndBRec3`, `IndArmE`, `IndBE`, `RecGen27`, `RecGen7` | 21.43 | 22.19 | |
| `CfoProg`, `ClassFeR`, `ClassMinorSlotHit`, `ClassMinorSlotW`, `KcW` | 18.32 | 18.13 | |
| **sum** | **69.3** | **63.8** | **−8 %** |

### 3.9 Batch 1b, first landing (the positivity leaves)

Batch 1b's 17 depth-0 functions are two groups. Seven are leaves: `nest_pos_fvar`,
`nest_cont_checks`, `nest_ctors_crest`, `nest_group_ctors` (called only by the `nestPos` block),
`nest_inst_type_ty` (under `nest_inst_type`), `nest_uniform` and `nest_root` (under
`check_block_positivity`). The other ten are the `nestPos` mutual block itself (`nest_pos`,
`_bind`, `_app`, `nest_cont`, `_key`, `_new`, `nest_frame`, `nest_ctors`, `_one`, `_walk`,
`nest_fields`). The survey put the block at depth 0 because a cycle counts as depth 0. Its two
halves are one joint induction each, `NbOKC`/`nbOKC_all` and `NbOKE`/`nbOKE_all`. This landing
migrates the seven leaves. The block is the next landing.

| function | before: ok refinement + error claim | after | change |
|---|---|---|---:|
| `nest_pos_fvar` | `pfW_ok` 78 + `pfvE_claim` 116 = 194 | `pfv_ref` 97 + `PfvPost` 7 + `pfK_eq`/`pfK_run` 22 = 126 | −35 % |
| `nest_cont_checks` | `p2ccW_okW` 48 + `nccE_claim` 86 = 134 | `ncc_ref` 67 + `NccPost` 9 + `nccT_eq` 17 = 93 | −31 % |
| `nest_ctors_crest` | `p2ctW_okC` 126 + `crestE_claim` 182 = 308 | `crest_ref` 160 + `CrestPost` 13 + `crestT`/`oneRest`/`oneK_eq` 43 = 216 | −30 % |
| `nest_uniform` | `unW_ok` 59 + `nuE_claim` 71 + spec 16 = 146 | `nu_ref` 66 + `NuPost` 6 = 72 | −51 % |
| `nest_root` | `p2rtW_okC` 133 + `nrtE_claim` 172 = 305 | `nrt_ref` 151 + `NrtPost` 11 = 162 | −47 % |
| `nest_inst_type_ty` | `ntyW_ok` 131 + `ntyE_claim` 197 = 328 | `nty_ref` 163 + `NtyPost`/`NtyOk`/`ntyT` 42 + `ntyT_eq` and helpers 38 = 243 | −26 % |
| `nest_group_ctors` | `gcW_ok` 100 + `ngcE_claim` 121 = 221 | `ngc_ref` 112 + `GcPost` 11 = 123 | −44 % |
| **sum** | **1 636** | **1 035** | **−37 %** |

The hand ok models are gone too, with their continuations, arms and specs: `pfW`, `p2ccW`,
`p2ctW`, `unW`, `p2rtW`, `ntyW` and `gcW`, about 370 lines. Generator wrappers were added:
`noaW1`, `cpW1`, `ucW1` (15 lines each) and `nhiO` (7). The whole diff against master is
+1 379 −2 263.

The rate is lower than the pilot's, for three reasons:

* Four of the leaves are fragments of a twin function: `pfK`, `nccT`, `oneK`'s head and
  `nestInstType` up to `instPisWith`. Their old claims held "whatever the continuation". The
  unified refinement takes the fragment at `pure`, so it needs a lemma that splits the
  continuation off (`pfK_eq`, `nccT_eq`, `oneK_eq`, `ntyT_eq`), and sometimes the fragment
  restated (`crestT`, `oneRest`, `ntyT`).
* The old ok refinements of `nest_cont_checks` and `nest_ctors_crest` returned the pieces of the
  twin run separately, and their callers splice the pieces into the enclosing twin's run.
  `NccPost` keeps those pieces as fields, so `contOKC_step` did not change.
* The error halves were already short: their callees are mostly outside the verdict closure.

Choices:

* **`G` per function, as in 1d.** `pfv_ref`, `ncc_ref` and `nu_ref` use
  `closedNV p nvFns = true`: their callees are lifted, and the block's error steps have only
  `hnv`. `crest_ref` uses `VerdictCtx p`, because the core stubs type the crest. `nrt_ref` uses
  `NrtG`, which is `closedNV` plus the block's `CtorsOKE` at every fuel, because `nest_ctors`
  stays `callE` until the block is migrated.
* **Generator limits, worked around with wrappers.** `unified` cannot lift a callee spec with
  a singleton-list post `some ([r.headD 0], m)` (`nest_occ_any`, `nest_cont_params_closed`,
  `nest_uniform_cs`), or a pure spec `r.headD 0 = F` (`nest_ctx_hi_at`). The wrappers (`noaW1`,
  `cpW1`, `ucW1`, `nhiO`, each with a one-line spec from the old one) restate them as
  `some (r.headD 0, m)`. A generator change would remove them.
* **The block's hand models read the leaves through the run.** `pfvR`, `nccR`, `crestR`,
  `ngcR` and `ntyR` are `cR n "f" [args] m`. The block's ok steps take `RefE.run_okW`. They now
  need the leaves' lookups, so `nbOKC_all` takes `L : NbLook p`. The error steps take
  `RefE.run_err`.
* **Placement** follows the ok users' imports. `pfv_ref` and `ncc_ref` are in `Verdict/PosE1L`,
  imported by `PosApp`/`PosCont`; `cpW_okW` moved in with them. `crest_ref` is in
  `Arena/IndT/PosCrest`. `nty_ref` and `ngc_ref` are in new modules, `Verdict/PosNty` and
  `Verdict/PosNgc`. `nu_ref` is in `PosTopE2`, `nrt_ref` in `PosTopE4`.
* **Pitfall.** If the twin's result is `Unit`, destructuring `RefE.run_ok…` with `-` for that
  value silently clears the run hypothesis that depends on it. Use `_` instead.

Elaboration (user seconds, `lean` on the module alone, median of 3 interleaved runs, base master
63762a3f + unrelated landings, load 6–56):

| module | base | new | |
|---|---:|---:|---|
| `Verdict/PosE1M` | 29.3 | 32.5 | **+11 %**: the unified `pfvE`, `nccE`, `ntyE`. With `simp [rdW]`, as their `errors` models had, it was 46.0. With `simp []` it is 32.5. `finish` fails. Wall time 8 → 21 s: `ntyE`'s step (`heartbeats 4000000`) is one long serial declaration |
| `Verdict/PosTopE1` | 12.4 | 16.8 | **+35 %**: the unified `nuE`, `nrtE`. With `simp [rdW]` it was 21.2. `finish` fails |
| `Arena/IndPosSpec/NestGroupCtors`, `NtyW`, `UnW`, `UnW2`, `P2rtW`, `P2sdW`, `NitW`, `CfW`, `NestContParamsClosed` | 43.6 | 19.0 | hand models and their specs gone |
| `Arena/IndRealAbsPos` | 23.1 | 15.8 | the hand models' `…_afr` gone |
| `Arena/IndT/Pos*`, `PosRoot`, `Positivity` | 25.8 | 18.5 | |
| `Verdict/PosE1N`, `PosE2`, `PosE3O`, `PosTopE4` | 11.1 | 8.1 | claims gone |
| `GgW2`, `FgW2`, `PosE2M`, `PosE3Cm` and 15 more (incl. the new `PosNty`, `PosNgc`) | 138.2 | 141.4 | |
| **sum (45 modules)** | **288.9** | **252.1** | **−13 %** (first series, with `simp [rdW]`: 270.2) |

### 3.10 Batch 1b, second landing (the `nestPos` block)

The block's eleven functions are `nest_pos`, `_bind`, `_app`, `nest_cont`, `_key`, `_new`,
`nest_frame`, `nest_ctors`, `_one`, `_walk` and `nest_fields`. Each now has one refinement. The
eleven statements `PosRef` … `FieldsRef` are in `Verdict/PosE.lean`. Each has the hypotheses of
the old `XOKC`/`XOKE` and the conclusion `RefE (NbG p) (xE p n m args) twin a (XPost …)`. The
posts are named-field structures: `PosPost`, `AppPost`, `KindPost`, `FramePost`, `CtorsPost`,
`OnePost`, `WalkPost`, `FieldsPost`. `NbRef n` collects the eleven statements. One induction
proves it, `nbRef_all` (`Arena/IndT/PosAll.lean`). Each step `xRef_step` lives in the old ok
step's file. The induction replaces the two old ones, `nbOKC_all` over the hand models and
`nbOKE_all` over `callE`.

| function | before: ok step + error step | after | change |
|---|---|---:|---:|
| `nest_pos` | `posOKC_step` 115 + `posOKE_step` 129 = 244 | `posRef_step` 163 | −33 % |
| `nest_pos_bind` | 116 + 169 = 285 | 203 | −29 % |
| `nest_pos_app` | 103 + 155 = 258 | 164 | −36 % |
| `nest_cont` | 140 + 218 = 358 | 213 | −41 % |
| `nest_cont_key` | 99 + 143 + `keyOKE_zero` 8 = 250 | 154 | −38 % |
| `nest_cont_new` | 192 + 314 = 506 | 331 | −35 % |
| `nest_frame` | 216 + 298 = 514 | 305 | −41 % |
| `nest_ctors` | 86 + 122 = 208 | 113 | −46 % |
| `nest_ctors_one` | 133 + 140 = 273 | 197 | −28 % |
| `nest_ctors_walk` | 99 + 72 = 171 | 106 | −38 % |
| `nest_fields` | 129 + 206 = 335 | 185 | −45 % |
| **steps** | **3 402** | **2 134** | **−37 %** |

The statements went the same way. The old ones were the `*OKC` (`PosDefs`, 250 lines), the
`*OKE` (`PosE`, about 200), and `NewOKE`/`KeyOKE`/`KeyOKEc`. The new ones are the `*Ref`, the
posts, `NbG` and `NbRef`: about 330 lines with the fragments' split lemmas. The hand models are
gone too: the mutual `nbPosW` … `nbFieldsW` and their continuations (`NbPosW`, `NbKeyK2`). Also
gone are their arm lemmas, their specs `nb*_step` and `nbSpec_all` (`GgW2`, `Nb`), and the
`StageR` predicates `NewOK`/`WalkOK`. So are the files `PosE1S`, `PosE3C`, `PosE3O`, `PosE3W`,
`PosE3F` and `PosAllE`. The whole diff against master is +2 036 −4 555. With the first landing,
the batch is +3 415 −6 818.

Choices:

* **`G` is `NbG p`**: the no-verdict closure, the core stubs' claims and `whnf_top`'s claim
  under `StageT`. Every error arm of the block needs only these, plus `nest_inst_type`'s `NitE`,
  which follows from them and the lookups (`nitE_all`). `nrt_ref` now uses `NbG` too, with the
  block's ok and error halves both coming from `nbRef_all`. The callers' error claims
  (`checkBlockPositivityE_claim`, `nestSeedsE_claim`, `cid_claim2`) take one `NbG p`
  (`nbG_prog`), where before they took `NbOKE` at every environment.
* **The models call every callee through `callE`**, as the old error models did. The new steps
  are the old error steps with `ErrClaim` replaced by `RefE` and the ok leaves of the old ok
  steps added. That is why they came out mechanical, and why the three steps could be proved in
  parallel by three helpers against one fixed statement file.
* **`errors` models with the unified spec derived.** A model with no lifted callee is the same
  definition in `errors` and in `unified` mode. Only the spec's error post differs (code or
  class). `triple_uni_of_code` (`Verdict/PosE3Fm.lean`) turns the `errors` spec `xE_specC` into
  the unified one `xE_spec`. Two reasons for this. The generated `unified` steps fail for
  `nest_cont_new` and `nest_ctors_one`: `grind` does not close `a.code = 0`, `a.cls ≠ 0` from
  `Err.cls_of_code`. And for the others, the `unified` steps cost more: `PosE1M`'s four block
  models took 41–49 s with `unified`, 32–34 s with `errors`. This is a generator observation.
  `unified` without `nv` could emit the `errors` steps and derive its spec the same way.
* **Fragments.** `nest_ctors_one` and `nest_ctors_walk` refine `oneT`/`walkT`, which are
  `oneK`/`walkK` at a continuation returning its inputs. `oneK_split`/`walkK_split` recover the
  CPS form. The old `@[refines]` statements (`PosCensus`) keep their `∀ K` form, as one-liners
  from `RefE.triple`.
* **`nest_seeds`** (batch 2) reads `nest_cont_key` through the run (`keyR`). Its ok proof
  (`p2sdW_okC`) and its error claim (`nsdE_claim`) take `ih.key` through `RefE.run_okW` and
  `RefE.run_err`.

Elaboration (user seconds, `lean` on the module alone, median of 3 interleaved runs, base master
at the merge; load 4–95):

| module | base | new | |
|---|---:|---:|---|
| `Arena/IndPosSpec/GgW2` | 70.6 | 11.1 | the hand models' specs `nb*_step` gone |
| `Verdict/PosE1M` | 38.9 | 34.9 | block models back in `errors` mode (second series; first series with `unified`: 34.4 → 38.6) |
| `Verdict/IndE` | 4.69 | 3.86 | the same for `nckE` (first series with `unified`: 3.96 → 5.59) |
| `Verdict/PosE` | 0.69 | 1.08 | the statements, posts, split lemmas |
| `Verdict/PosE2` | 4.47 | 1.54 | `newOKE_step`, `frameOKE_step` gone |
| `Verdict/PosE1S`, `PosE3C/O/W/F`, `PosAllE` | 7.07 | — | deleted |
| `Arena/IndT/Pos*` (the eleven step files, `PosAll`, `PosCensus`, `PosDefs`) | 15.8 | 14.1 | |
| `PosE2M`, `PosE3Cm`, `PosE3Fm`, `NbPosW`, `NbKeyK2`, `Nb`, `WalkOK` and 10 more | 55.6 | 53.0 | |
| **sum (41 modules, first series, still with the `unified` block models)** | **192.6** | **124.9** | **−35 %** |

Kit candidate: `RefE.of_run_eq` (`Arena/KnotE.lean`, from another batch) moves a refinement along
an equation of twin runs. Two helpers wrote it again before finding it. It belongs in
`Arena/Verdict.lean` with the rest of the kit.

### 3.11 The kit after batch 1, and the functions batch 1 skipped

**The kit** (§1.5) gathers the helpers the batch lanes had put in place: `RefE.tail`/`tail_eq`,
`RefE.of_run_eq`, `RefE.mono` and the `ErrClaim` run lemmas (from `Arena/KnotE`) and
`callE_of_callW` are in `Arena/Verdict.lean`; `CorePost`, `RefE.coreSpec`, `CoreSpec.of_refE`,
`RefE.bind_core` (from `KnotE`), `CoreAfterG`, `GrowRef`, `GrowPost` (from `WhnfCoreProj`),
`RefE.growRefW`, `GrowPost.of_tail` (from `WhnfM2CRefine2`), `GrowPost.of_core`,
`RefE.bind_grow(K)` (from `DefEqMidPeel`, over `GrowRefP`, which is `GrowRef` unfolded) are in the
new `Arena/RefECore.lean`. New: `RefC` (an ok fact and an error claim; `PreRef` is now a `RefC`),
`VerdictCtxU` (with `UceProg`), and `CoreStubsE`/`VerdictCtx` moved below `DeclValE` into
`Verdict/VCtx`, so that the `Decl` files can use them.

**Why the unified steps cost about twice the `errors` steps.** The word and byte load specs
(`ld64_rdW_specE`, `L.ld8_specE`) had the error post `e.code = 0`. The `errors` post
`ε.code ≠ 0 → …` closes against it by `simp`, but the unified post `G → ε.cls ≠ 0 → …` needs
`cls` from `code` (`Err.cls_of_code`), which `simp_all` does not have: every load's error goal
went through slow `simp_all` rounds and then `grind`. The error is `.oob` exactly, so the posts
now say `e = .oob` (and `Err.cls_oob` is a `lang_grind` lemma). `checkValueGroupE`'s step:
`errors` 2.5 s, `unified` 8.6 s before, 2.9 s after (profile: `simp` 5.8 s → 1.6 s, `grind`
0.9 s → 0.004 s).

Elaboration of the 41 modules with unified models or the moved kit (user seconds, median of 3
interleaved runs, base master 93656432):

| module | base | new |
|---|---:|---:|
| `Verdict/DeclValE` | 10.37 | 5.27 |
| `Verdict/IndBTmm` | 32.97 | 14.75 |
| `Verdict/IndBToi` | 4.30 | 2.52 |
| `Verdict/IndBRecPins` | 7.37 | 4.67 |
| `Verdict/PosE1M` | 34.96 | 26.14 |
| `Verdict/PosTopE1` | 17.83 | 11.66 |
| `Verdict/WhnfModels2E` | 33.17 | 30.31 |
| `Verdict/WhnfModels6E` | 16.67 | 14.35 |
| `Arena/DefEqMidLoops`, `DefEqMidLams` | 12.64 | 9.56 |
| the other 32 (incl. the new `RefECore`; `DefEqMidLazy2` re-measured at parity) | 163.1 | 163.1 |
| **sum** | **333.4** | **282.4** |

So the flagged modules of batch 1 (`DeclValE`, `IndBTmm`, `IndBToi`, `IndBRecPins`, `PosE1M`,
`PosTopE1`, `WhnfModels2E`) are back at or below their `errors` times.

**The generator.** `↦ fW tuple` counted only the `return`s of the body, not those of the named
blocks spliced into it (`lazy_delta_reduction`'s `return (k, x, y)` is in `⟪lazyDeltaLoop⟫`): the
arity now includes them. `unified` now lifts the callee specs with a total model (`r.headD 0 = F`,
`r ≠ [] ∧ r = F` as `e_view`'s, `s'.mem = F`; a guard's failure is `.error .oob`) and a result
stated as a one-element list (`some ([r.headD 0], m)`). Tests: `tUniL`, `tUseOne`, `tTup3`. With
these, the positivity wrappers `noaW1`, `cpW1`, `ucW1`, `nhiO` are gone, and the twelve positivity
models that were `errors` plus `triple_uni_of_code` (their unified steps were slower before the
load fix) are `unified` (`PosE1M`, `PosE2M`, `PosE3Cm`, `PosE3Fm`, `IndE`; 20 modules at parity,
93.9 → 93.1 s).

**Migrated here**:

| function | before: ok + claim | after | change |
|---|---|---|---:|
| `class_rule_ok_guards` | `crgW_okC` 90 + `crgE_claim` 129 = 219 | `crg_ref` 110 + `CrgPost` 8 + `crgT`/`crgT_bind` 31 = 149 | −32 % |
| `vi_unsafe` | 86 | 54 | −37 % |
| `vi_np_go` | 67 | 50 | −25 % |
| `vi_ctor` | 346 | 167 | −52 % |
| `vi_rec_idx` | 160 | 89 | −44 % |

* `class_rule_ok_guards` (`Verdict/IndBCrg`): `G := VerdictCtxU p`, against the twin's guards prefix
  `crgT` (`classRuleOk = crgT >>= rest`, as `rgT`). `cruleW` reads it through the run;
  `cruleW_okC` and three callers gained `CruleProg p`. The hand model `crgW` and its arms are gone.
* `vi_*` (`Verdict/FrontViE`): `RefC` with `G := True` (the lifted callees' errors are `.oob`; the
  callers pass `closedNV frontAllProg nvFns`, `frontAllProg_nv`, proved once in `FrontValidE`,
  +2 s there). The front models that read them (`nparamsW`, `recW`, `recsGoW`, `recsW`,
  `validateW`, `orderInW`) read the run and take the program; four of them return the memory now
  (the run's memory is unchanged only by the ok fact). The hand models `unsafeW`, `npGoW`,
  `recIdxW`, `ctorW` and `IndApplyRefine4` are gone. 15 modules 68.4 → 69.5 s.

**`lvl_eq_fueled`** (`Verdict/LefRef`, after batch 1b): `lefE` (unified, `lvl_eq_c` through
`callE`), `lef_ref` against `lefT u v := lvlEq? u v >>= liftFueled "level comparison"` (with
`lefT_bind` for the callers' continuations), `G := NVAt p "lvl_eq_c"` (weaker than `closedNV`;
`check_thm_val`'s claim has only that). `LefPost` has the `StageT` package, the frame (`mfr`: the
function is not in `stageCoreFns`, so callers cannot frame the call themselves) and the `StageC`
package as a conditional field. The two identical hand models `lfW` and `lveC` (and `lveW`) are
gone; the callers' models `tvK3`, `agK3`, `nitK4` read the function through the run. Pair lines
≈ 147 (five ok lemmas and the claim) → ≈ 55 (−63 %); 20 modules at parity (44.0 → 43.5 s).

**Not migrated**:

* `install_header` and `class_const_ok_header` (§3.5, §3.8) are not one body: their abort codes
  differ (`R_LOOSE_BOUND_VARIABLE` against a plain `abort`), `unresolved_consts_error` is called
  with `w = 0` against `w = 2`, and the twins differ (`installHeader`, `classConstOk`'s header).
  Only the ok model `ihW` is shared. They need two unified models and two refinements (the second
  against a header prefix of `classConstOk` with a `…_bind` lemma); the shared `ihW` goes when
  both are done.

### 3.12 Batch 2c, first landing (the block checks: `BlkE1`, `BlkE2`, `BlkE4`)

Batch 2c's functions, from §3.1 (depth 1–2, `Verdict/Blk*`, `Verdict/IndsE*`):
`check_block_classes_keys`, `check_block_ctors_one`, `check_block_ctors_go`,
`check_block_idx_sorts_one`, `check_block_idx_sorts` (this landing), `check_block_agree_one` and
`check_block_agree` (next landing: their models nest `lvl_eq_fueled`'s hand models, which the kit
lane replaces first).

| function | before: ok refinement + error claim | after | change |
|---|---|---|---:|
| `check_block_classes_keys` | `ckkW_sim` 40 + `ckkE_claim` 47 = 87 | `ckk_ref` 54 + `CkkPost` 6 = 60 | −31 % |
| `check_block_ctors_one` | `icboW_simC` 77 + `icboE_claim` 77 = 154 | `icbo_ref` 80 + `IcboPost` 10 = 90 | −42 % |
| `check_block_ctors_go` | `icbgW_simC` 94 + `icbgE_claim` 96 = 190 | `icbg_ref` 101 + `IcbgPost` 9 + `CtorsG` 3 = 113 | −41 % |
| `check_block_idx_sorts_one` | `iisW_simC` 117 + `iisE_claim` 92 = 209 | `iis_ref` 120 + `IisPost` 7 = 127 | −39 % |
| `check_block_idx_sorts` | `iisrW_simC` 69 + `iisrE_claim` 75 = 144 | `iisr_ref` 75 + `IisrPost` 7 = 82 | −43 % |
| **pairs** | **784** | **472** | **−40 %** |

Also gone: the hand model `iisW`/`iisK1–3` with `iis_spec` (`Iis.lean`, deleted), the generated ok
models `icboW`, `icbgW`, `iisrW`, `ckkW` with their specs, `kofCall_sim`, and what only they used
(`Sim.tail`, `installCons_afr`, the `callW` forms of the `rec2` header lemmas, now over `recW`). The
`@[refines]` theorems (`checkBlockIdxSorts_refinesC`, `checkBlockCtors_refinesC`, whose ok model
`ictW` reads `check_block_ctors_go` through `callW`) keep their statements. Whole diff against
master: +637 −1 054 in 18 files.

Choices:

* **`G` per function**: `closedNV p nvFns = true` for `check_block_classes_keys` (`class_key_of` is
  unified under it, `sl_cons` lifted); `CheckStructFieldSortsIE p` alone for the index sorts (the
  lifted callees' errors are `.oob`; `check_struct_field_sorts_i` stays `callE`); `CtorsG p`
  (`nv`, `sc : CheckSumCtorsE p`) for the constructors (`check_sum_ctors` stays `callE`).
  `check_sum_ctors`, `check_struct_field_sorts_i(_go)`, `check_struct_doms_at`,
  `check_block_doms_at` and `check_block_tables` are depth-0 leaves that no batch-1 list named;
  they are still split.
* **Placement**: `ckk_ref` in `Arena/RecGenSpec/CntW` (its ok user `RecGen21`), `icbo_ref`/`icbg_ref`
  in `Arena/IndT/Install7` (`checkBlockCtors_refinesC`), `iis_ref`/`iisr_ref` in a new
  `Arena/IndT/IdxSorts` (imports `Verdict/IndBE` for the claim; `Tail` imports it). The Verdict
  files keep only the derived claims of the depth-3 callers (`RefE.run_err`).
* **`CheckSumCtorsE` moved** from `Verdict/IndBE` to `Install7` (next to `checkSumCtors_refinesC`'s
  users; `err_stmt` needs only `Verdict/IndAGen`): importing `IndBE` there would have added 69
  modules below `Install7`.
* **`ClassKeyOfE` is gone**: `check_block_classes`' claim reads `class_key_of` through `ckk_ref`,
  so the statement, `classKeyOfE_of` and the hypothesis in `cid_claim2/3` went.
* **Recipes**: the default `finish` for `icboE`/`icbgE` (4.2 s for `Install7`; `simp [rdW]` 4.7 s);
  `simp [rdW]` for `ckkE` (4.5 s for `CntW`; default 5.0 s); `simp [rdW]` for `iisE`/`iisrE`.

Elaboration (user seconds, `lean` on the module alone, median of 3 interleaved runs, base master
affbbf73; load 18–42; `CntW` from a separate series after the recipe change):

| module | base | new | |
|---|---:|---:|---|
| `Arena/IndT/Install7` | 0.96 | **4.19** | **slower (+3.2 s)**: `icboE`/`icbgE` moved in |
| `Arena/IndInstallSpec/Icbo`, `Verdict/BlkE1` | 10.46 | 2.11 | the generated ok models and the error models gone |
| `Arena/IndT/IdxSorts` (new) | — | 5.57 | the unified models and refinements |
| `Arena/IndInstallSpec/Iis` (deleted), `Arena/IndT/Install5`, `Verdict/BlkE2` | 12.43 | 1.20 | |
| `Arena/RecGenSpec/CntW` | 4.29 | 4.46 | `ckkE` moved in |
| `Verdict/BlkE4` | 3.73 | 3.16 | |
| `GrcProg`, `InstallRec2PSl`, `RecGen21`, `Tail`, `IndBE`, `IndArmE`, `IndArmTopE`, `IndA8`, `IndA9` | 9.47 | 9.91 | |
| **sum** | **41.3** | **30.6** | **−26 %** |

`Install7` is the one flagged module; with the files it replaces (`Icbo`, `BlkE1`) it is 11.4 → 6.3 s.

### 3.13 Batch 2a, first landing (`Decl*`, `whnf_telescope`)

The batch's functions (`_tmp/unifiedE/inv.py` on master 1dc86825, the `Decl*`/`DefEq*`/`Whnf*`
families and `IndBWt`; `DefEq*`/`Whnf*` have nothing left at depth 1–2): depth 0 left over
`install_header`, `install_basis_decls`, `check_defn_val`, `check_opaque_val`, `check_reduce_pin`,
`check_div_mod_certs`, `check_type_pins`; depth 1 `check_constant_val`, `install_value`,
`check_thm_val`, `check_basis_decl`, `check_div_mod_pin_value`, `whnf_telescope`; depth 2
`check_decl_axiom`, `check_decl_defn`, `check_decl_opaque`, `check_decl_quot`, `check_decl_thm`,
`check_div_mod_pin_at`. This landing migrates fourteen of them:

| function | before: ok refinement(s) + error claim(s) | after | change |
|---|---|---|---:|
| `install_header` | `ihE_okT` 244 (`ihW_okT` stays: `class_const_ok_header`'s) | `ih_ref` 185 + `IhPost` 7 + `IhCtx` 3 = 195 | (−20 %) |
| `check_constant_val` | `ccvW_okT` 47 + `ccvW_okTA` 39 + `ccvE_okT` 60 = 146 | `ccv_ref` 54 + `CcvPost` 6 + `ccvE_okT` 13 = 73 | −50 % |
| `install_value` | `ivW_genT` 102 + `ivW_okT` 62 + `ivE_core` 107 + `installValue_errT` 66 = 337 | `ivc_ref` 99 + `iv_ref` 37 + `IvPost`/`IvCtx`/`ivCoreT` 16 + `installValue_errT` 13 = 165 | −51 % |
| `check_defn_val`, `check_opaque_val` | `dvW_okT` 36 + `defnvE_okT` 90 + `opaquevE_okT` 90 = 216 | `dv_ref` 85 + `ov_ref` 85 + `DvCtx`/`DvPost` 10 + the two claims 28 = 208 | −4 % |
| `check_decl_defn` | `cdfW_okT` 143 + `checkDeclDefn_errT` 161 + `NatGateSpecE`/`natGateSpecE_of` 16 = 320 | `cdf_ref` 147 + `CdfCtx`/`CdfPost` 9 + `checkDeclDefn_errT` 22 = 178 | −44 % |
| `install_basis_decls` | 143 | 64 | −55 % |
| `check_basis_decl` | 242 | 117 | −52 % |
| `check_decl_quot` | 231 | 106 | −54 % |
| `check_div_mod_certs`, `check_type_pins`, `check_div_mod_pin_value`, `check_div_mod_pin_at` | `cmC` 239, `ctpC` 118, `cpvC` 105, `cpaC` 52; `cmE` 259, `ctpE` 112, `cpvE` 128, `cpaE` 71, `cpaClaimE_of` 7 = 1 091 | `cm_ref` 239, `ctp_ref` 112, `cpv_ref` 98, `cpa_ref` 55, `DmPost` 7; `cmC` 22, `cpvC` 17, `cpaC` 18, `cpaClaimE_of` 9 = 570 | −48 % |
| `whnf_telescope` | `wtW_simC` 138 + `wtE_claim` 154 = 292 | `wt_ref` 135 + `WtPost`/`WtG` 12 = 147 | −50 % |
| **pairs** | **3 262** | **1 823** | **−44 %** |

The hand ok models with their arms and specs are gone too: `ccvW`/`ccvK1–3`/`ccv_specW`, `ivW`/
`ivK1–5`/`iv_specW`, `dvW`/`dv_specW`/`ov_specW`/`dvBody_specW`, `cdfW`/`cdfK1–5`/`cdf_specW`,
`ibdsW`, `cbdW`, `cdqW`, the file `DeclDivModSpec/CmW` (`cmW`, `dmCtpW`, `dmCpvW`, `cpaW` and their
specs), `wtW`/`wtK1–6`/`wtW_spec`. Whole diff against master c4aef6d6: **+1 608 −3 652** in 38
files.

Choices and findings:

* **`install_header` alone.** Its body and `class_const_ok_header`'s are two functions (§3.11);
  `ih_ref` is `install_header`'s. The shared hand model `ihW` and `ihW_okT` stay for
  `class_const_ok_header`'s ok proof (`RecGen3`, `IndBHdr`; batch 2b) and go with it. `G` is
  `IhCtx p` (`closedNV` and `UceProg`: its consts-resolve site), the weakest that fits; callers
  pass `⟨hG.nv, hG.uce⟩` from `VerdictCtxU`.
* **`G` per function**: `VerdictCtxU p` for `check_constant_val` (the core stubs and the header);
  `IvCtx` (`nv`, `uce`, `IvgE`) for `install_value`; `DvCtx` (`NVAt "env_push"`, `CoreStubsE`,
  `IvgE`) for the value checks; `CdfCtx pins` (`VerdictCtxU`, `IvgE`, the pin gate's
  `DivGateSpecE`) for the definition arm; `True` for the basis family; `CoreStubsE p` for the
  `Nat.div` gates; `WtG` (`closedNV`, `WhnfTopE`) for `whnf_telescope`.
* **A callee read through its run where the caller needs the run.** The definition arm needs each
  callee's write-set frame (`PinSetsR.step`, `run_memFrame`), which comes from the program run, not
  from a unified model's value. So `checkDeclDefnE` calls all its callees through `callE` and its
  refinement takes their halves from the runs (`RefE.run_ok`, `RefE.run_err` with `ccv_ref`,
  `dv_ref`, `dng_ref`). `whnf_telescope` does the same for `whnf_top` (`whnfC_rsim` reads the run).
  A kit lemma from a unified model's ok value back to the call's run would allow listing such
  callees by their unified specs.
* **`install_value` against a kind-generic twin.** `ivT` has three kinds; `ivc_ref` is against
  `ivCoreT` (header, guards unless `vk = 1`, push) and `iv_ref` reads each kind by
  `RefE.of_run_eq`. The ok proof needs `install_value_guards`' spec, so `installValue_errT` and
  `installStepGo_errT` gained `CvgProg p` (`DeclTopE` passes `hdc.cvg`).
* **Two value checks, one text, two models.** `check_defn_val` and `check_opaque_val` differ only
  in the abort code; their unified models are two constants, so `dv_ref` and `ov_ref` are the same
  proof twice. They replace one shared ok proof and two error claims: −4 % only.
* **`NatGateSpecE` gone**: with `dng_ref` read from the run, the definition arm's error claim no
  longer takes the structural gate's claim as a hypothesis; `natGateSpecE_of`, and the hypothesis
  in `DeclTopE`/`TopE`, are gone. `DivGateSpecE` moved to `Arena/DeclDefnT` (the pin gate is not
  migrated: depth ≥ 3).
* **Recipes.** `simp []` for every model here (with `locals` for `installHeaderE`); `finish` fails
  for `installHeaderE`, `checkBasisDeclE`, `checkDivModCertsE`. `cv_lps`' spec carries the result's
  length (`r = [r.headD 0, r.tail.headD 0]`), which as a `simp_all` hypothesis loops (max
  recursion); `cvLps_specW1` drops it for the generator.
* **Placement**: `ccv_ref`, `dv_ref`/`ov_ref` in `Verdict/DeclValsE` (now imported by
  `Arena/DeclArmT`), `ih_ref` in `Verdict/DeclHdrE`, `iv_ref` in `Arena/DeclArmT`, `cdf_ref` in
  `Arena/DeclDefnT`, the `Nat.div` gates in `Arena/DeclDivGateT2`, `wt_ref` in `Arena/IndT/Sum1`.
* **Left for the next landing**: `check_reduce_pin`, `check_decl_axiom`, `check_decl_thm`,
  `check_thm_val` (after `lvl_eq_fueled`), `check_decl_opaque`. `install_value_guards` (depth 0,
  not in §3.1's list: no `@[refines]` of its own) has its hand model `ivgW` nested in
  `check_thm_val`'s; it follows that.

Elaboration (user seconds, `lean` on the module alone, median of 3 interleaved runs, base master
c4aef6d6, load 15–96, `_tmp/unify-b2a/times1.txt`):

| module | base | new | |
|---|---:|---:|---|
| `Arena/DeclDivGateT2` | 2.42 | **10.59** | the four unified models and refinements moved in |
| `Verdict/DeclGatesE2`, `Arena/DeclDivModSpec/CmW` | 29.54 | 2.92 | …from here (`CmW` deleted); with `DeclDivGateT2`: 32.0 → 13.5 |
| `Arena/IndT/Sum1` | 2.34 | **6.46** | `wtE` and `wt_ref` moved in |
| `Verdict/IndBWt`, `Arena/IndSumSpec/WtW`, `StructProjArgP` | 21.81 | 12.10 | …from here; with `Sum1`: 24.2 → 18.6 |
| `Arena/DeclDefnT` | 1.23 | **2.58** | `checkDeclDefnE` and `cdf_ref` moved in |
| `Verdict/DeclDefnE` | 2.51 | 0.57 | …from here; with `DeclDefnT`: 3.7 → 3.2 |
| `Arena/DeclArmT` | 1.61 | **2.18** | `installValueE`, `iv_ref` |
| `Arena/DeclCrpT`, `DeclDivGateT` | 2.57 | 3.95 | call sites only (load noise; 0.4 s for a doc change) |
| `Verdict/DeclValsE` | 2.23 | 2.56 | three unified models |
| `Verdict/DeclBasisE`, `DeclQuotE` | 7.02 | 1.15 | claims gone |
| `Verdict/DeclHdrE`, `DeclStepE` | 8.64 | 7.96 | |
| the other 21 | 45.6 | 41.8 | |
| **sum (38 modules)** | **127.5** | **94.8** | **−26 %** |

Every flagged module is a new home of models and refinements whose old modules got faster by more.

### 3.14 Batch 2a, second landing (the declaration arms, `check_thm_val`, `install_value_guards`)

The rest of the batch's list (§3.13), now that `lvl_eq_fueled` is unified (§3.11's follow-up), and
`install_value_guards`:

| function | before: ok refinement(s) + error claim(s) | after | change |
|---|---|---|---:|
| `check_reduce_pin` | `crpW_okT` 199 + `crpE_okT` 240 = 439 | `crp_ref` 202 + `CrpPost` 5 + `crpE_okT` 16 = 223 | −49 % |
| `check_decl_axiom` | `cdaW_gen` 293 + `cdaW_okT` 33 + `checkDeclAxiom_errT` 408 + `checkDeclAxiom_loopT` 24 = 758 | `cda_ref` 340 + `CdaPost` 5 + `checkDeclAxiom_errT` 14 + `checkDeclAxiom_loopT` 24 = 383 | −49 % |
| `check_thm_val` | `tvW_okT` 116 + `dvK1_okT` 58 + `tvE_okT` 196 + `checkThmVal_refinesT` 21 = 391 | `tv_ref` 177 + `TvCtx` 4 + `ArmPost` 5 + `checkThmVal_refinesT` 19 = 205 | −48 % |
| `check_decl_thm` | `cdtW_okT` 65 + `checkDeclThm_errT` 79 = 144 | `cdt_ref` 61 + `CdtCtx` 2 + `CdtPost` 5 + `checkDeclThm_errT` 20 = 88 | −39 % |
| `check_decl_opaque` | `cdoW_okT` 174 + `checkDeclOpaque_errT` 180 + `checkDeclOpaque_loopT` 28 = 382 | `cdo_ref` 172 + `checkDeclOpaque_errT` 20 + `checkDeclOpaque_loopT` 27 = 219 | −43 % |
| `install_value_guards` | `IvgT` 9 + `ivgW_okT` 86 + `ivgE_okT` 148 = 243 | `ivg_ref` 117 + `IvgPost` 6 + `ivgE_okT` 8 = 131 | −46 % |
| **pairs** | **2 357** | **1 249** | **−47 %** |

Gone with them: the hand models `crpW`/`crpK1–8`, `cdaW`/`cdaK1–10`/`cdaQ1–2`/`cdaT`/`cdaRet`,
`tvW`/`tvK1–4` and the shared tail `dvK1–4`, `cdtW`/`cdtK1–3`, `cdoW`/`cdoK1–6` (the file
`Arena/DeclArmOpaque`), `ivgW`/`ivgK1–5`, with their arms and specs. `Arena/DeclValSpec` holds only
`ValProg` and the twin equations. Whole diff against master 9458a945: **+1 065 −2 774** in 25
files.

* **`G`**: `CoreStubsE p` (`check_reduce_pin`), `VerdictCtxU p` (`check_decl_axiom`), `TvCtx`
  (core stubs, `IvgE`, `lvl_eq_c` outside the closure) for `check_thm_val`, `CdtCtx`
  (`VerdictCtxU` and `IvgE`) for the theorem and the opaque arms, `IhCtx` (`closedNV`, `UceProg`)
  for `install_value_guards` as for `install_header`.
* **`install_value_guards`** was not in §3.1's list (no `@[refines]` of its own) but has an error
  claim (`IvgE`) and an ok proof (`ivgW_okT`) read by five refinements. `ivg_ref` (in
  `Verdict/DeclValE`, below `check_value_group`'s and `check_thm_val`'s) replaces both; the five
  call sites read it through the run (`RefE.run_ok`), and `IvgE` stays as the claim's shape
  (`ivgE_okT` is `RefE.run_err`) for the hypotheses of `CvgCtx`, `DvCtx`, `TvCtx`, `CdtCtx`.
* **The arms read their callees through their runs**, as the definition arm (§3.13), where the
  ok half needs the call's write-set frame or the loop's `run_memFrame`.
* **Shake.** The new import graph left 16 imports unused; removing them broke five downstream
  modules that had used them transitively (`DeclHeader`, `DeclAxQuotT`, `DeclDefnT`, `RecGen3`,
  `RecGen7`), which now import what they use.
* **Not here**: `install_header`'s shared hand model `ihW` and `ihW_okT` stay for
  `class_const_ok_header` (batch 2b).

Elaboration (user seconds, median of 3 interleaved runs, base master 9458a945, load 14–28,
`_tmp/unify-b2a/times2.txt`):

| module | base | new | |
|---|---:|---:|---|
| `Arena/DeclAxQuotT` | 0.73 | **6.51** | `checkDeclAxiomE` and `cda_ref` moved in |
| `Verdict/DeclAxiomE`, `Arena/DeclArmAxiom` | 11.18 | 1.18 | …from here; with `DeclAxQuotT`: 11.9 → 7.7 |
| `Arena/DeclCrpT` | 1.67 | **2.84** | `checkDeclOpaqueE`, `cdo_ref`, `crp_ref` |
| `Verdict/DeclCrpE`, `DeclArmsE`, `Arena/DeclArmOpaque` | 5.66 | 1.23 | …from here; with `DeclCrpT`: 7.3 → 4.1 |
| `Verdict/DeclValE` | 4.76 | **6.08** | `installValueGuardsE`, `ivg_ref`, `checkThmValE`, `tv_ref` |
| `Verdict/DeclHdrE`, `Arena/DeclValSpec`, `DeclCvg`, `DeclCvgT` | 9.59 | 7.03 | …from here; with `DeclValE`: 14.4 → 13.1 |
| the other 13 | 24.4 | 24.6 | |
| **sum (25 modules)** | **58.0** | **49.5** | **−15 %** |

Batch 2a in all: 21 functions, one model and one refinement each; the pairs 5 619 → 3 072
(−45 %).

### 3.15 Batch 2c, second landing (`check_block_agree_one`, `check_block_agree`)

After `lvl_eq_fueled` (§3.11): `cbaoE` and `cbagE` are unified (`IndsE4`, `IndsE5`, moved from
`IndsE1`); `cbaoE` calls `lvl_eq_fueled` through its unified model `lefE` (the twin rewritten with
`lefT_bind`; ok and error arms from `lef_ref`), `cbagE` calls `cbaoE`; `open_pis_at_fvars_f` and
`fvar_type_ds` are lifted; `check_block_doms_at` stays `callE` (`cbdaE_claim`, `domsW_simC`).
`G := VerdictCtx p` (`check_block_doms_at`'s claim needs `nv` and `core`). One post for both,
`AgreePost` (`stage`, `grow`, `abs`, `core`). `checkBlockAgree_refinesC` keeps its statement
(`RefE.triple`); `check_block_inds`' claim (`IndsE7`) reads `RefE.run_err`.

| function | before: ok refinements + error claim | after | change |
|---|---|---|---:|
| `check_block_agree_one` | `agW_okC` 119 + `checkBlockAgreeOne_refinesC` 32 + `cbaoE_claim` 166 = 317 | `cbao_ref` 170 + `AgreePost` 6 = 176 | −44 % |
| `check_block_agree` | `iagW_simC` 116 + `checkBlockAgree_refinesC` 21 + `cbagE_claim` 134 = 271 | `cbag_ref` 124 + `checkBlockAgree_refinesC` 22 = 146 | −46 % |
| **pairs** | **588** | **322** | **−45 %** |

Also gone: the hand models `agW`/`agK1–4` with `checkBlockAgreeOne_spec`, `iagW`/`iagK1–3` with
`iag_spec`, the module `Arena/IndT/Install2`, the statements `CheckBlockAgreeE`/`CheckBlockAgreeOneE`.
Whole diff against master 985859c8: +230 −668 in 11 files.

**Not migrated: `check_block_doms_at`.** Its hand model `domsW` and ok proof `domsW_simC` are shared
with `check_struct_doms_at` (`sdomsW` is `domsW` with the words dropped; `sdomsW_simC` is built on
`domsW_simC`, used by `Sum4`, `IndBSum1`). The two depth-0 leaves should be migrated together, as
`install_header`/`class_const_ok_header`. With them, the batch-1 leftovers of this family are
`check_sum_ctors`, `check_struct_field_sorts_i(_go)` and `check_block_tables` (§3.12).

Elaboration (as §3.12, base master 985859c8, load 9–12; `IndsE5` from a separate series after the
recipe change: `simp [rdW]` 3.25 s, the default 2.2 s; `IndsE4` keeps `simp [rdW]`, 2.9 s against
3.3 s):

| module | base | new | |
|---|---:|---:|---|
| `Verdict/IndsE4` | 1.07 | **2.94** | **slower (+1.9 s)**: `cbaoE` moved in |
| `Verdict/IndsE5` | 0.78 | **2.2** | **slower (+1.4 s)**: `cbagE` moved in |
| `Verdict/IndsE1` | 8.96 | 5.57 | the two models moved out |
| `Arena/IndInstallSpec/IagW`, `DomsW`, `Arena/IndT/Install2` (deleted) | 9.95 | 4.33 | the hand models and ok refinements gone |
| `IndsE2`, `IndsE7`, `Install4` | 2.21 | 2.20 | |
| **sum** | **23.0** | **17.2** | **−25 %** |

Batch 2c in all: 7 functions, pairs 1 372 → 794 lines (−42 %); no kit or generator change needed.

### 3.16 Batch 2b, first landing (inductive targets and classes: `IndBPins`, `IndBTmt/Tmo`, `IndBHdr`, `IndBRec2`, `IndBFields`, `PosTopE1`, `PosE2M`)

The batch's functions (depth 1–2 of §3.1 in the `IndB*`/`Pos*` families, callees migrated):
`target_major_pins`, `target_major_of_outside_tail`, `target_major_of_outside`,
`class_const_ok_header` (skipped in batch 1), `class_const_ok`, `class_rec_ty_ok`, `class_fields_of`,
`check_abs_ctor_sorts_one`, `check_abs_ctor_sorts`, `nest_grow_group`, `nest_seeds` (this landing);
`class_rule_ok`, `class_rules_ok_one` (after `class_rule_ok_guards`, §3.11) and `nest_inst_type`
(after `lvl_eq_fueled`) are the second landing. Not in this batch: `whnf_telescope` (batch 2a),
`class_stream_recs` and `check_sum_tele_slow` (their callee `check_constant_val` is batch 2a's).

| function | before: ok refinement(s) + error claim(s) | after | change |
|---|---|---|---:|
| `target_major_pins` | `tmpW_okC` 112, `tmpE_claim` 148, `targetMajorPins_claim` 13, frames `tmpW_mfrR` 24, `tptR_mfr` 11 = 308 | `tmp_ref` 126 + `TmpPost` 6 = 132 | −57 % |
| `target_major_of_outside_tail` | `tmtW_simC` 86, `tmtE_claim` 86, `tmoTail_claim` 25 = 197 | `tmt_ref` 106 + `TmoPost` 7 = 113 | −43 % |
| `target_major_of_outside` | `tmoW_simC` 163, `tmoE_claim` 214, `tmo_claim` 26 = 403 | `tmo_ref` 168 | −58 % |
| `class_const_ok_header` | `classConstOkHeader_claim` 244 (ok half: `install_header`'s `ihW_okT`, shared) | `cch_ref` 182 + `CchPost` 5 + `cchT`/`cchT_bind` 33 = 220 | −10 % |
| `class_const_ok` | `ccoW_simT` 37, `classConstOk_of_ih` 38, `ccoW_simC` 16, `classConstOk_claim` 69 = 160 | `cco_ref` 41 + `CcoPost` 5 = 46 | −71 % |
| `class_rec_ty_ok` | `rtoW_simC` 110, `classRecTyOk_claim` 169 = 279 | `rto_ref` 130 + `RtoPost` 6 = 136 | −51 % |
| `class_fields_of` | `cfoW_sim` 31, `cfoW_afr` 11, `classFieldsOf_claim` 48 = 90 | `cfo_ref` 33 (`CfgPost`) | −63 % |
| `check_abs_ctor_sorts_one` | `iaoW_simC` 63, `iaoE_claim` 61 = 124 | `iao_ref` 70 | −44 % |
| `check_abs_ctor_sorts` | `iacW_simC` 145, `iacE_claim` 157 = 302 | `iac_ref` 136 + `IacPost` 6 = 142 | −53 % |
| `nest_grow_group` | `ggW_ok` 133, `nggE_claim` 184 = 317 | `ngg_ref` 158 + `NggPost` 10 = 168 | −47 % |
| `nest_seeds` | `p2sdW_okC` 153, `nsdE_claim` 204 = 357 | `nsd_ref` 163 + `NsdPost` 8 = 171 | −52 % |
| **pairs** | **2 781** | **1 399** | **−50 %** |

The hand ok models with their arms and specs are gone too (about 700 lines): `tmpW`/`tmpK1–4`,
`tptR`, `tmtW`/`tmtK1–3`, `tmoW`/`tmoK1–4`, `ccoW`/`ccoK1–3`, `rtoW`/`rtoK1–5`, the generated `cfoW`,
`iaoW`/`iaoK1–2`, `iacW`/`iacK1–4`, `ggW`/`ggK1–4`, `p2sdW`/`p2sdK1–3`/`keyR`, and their specs; the
files `Arena/IndT/RecGen3`, `Arena/RecGenSpec/ClassConstOk`, `ClassConstOkHeader` and
`Arena/IndPosSpec/P2sdW`. The `@[refines]` theorems keep their statements (`RefE.triple`). Whole diff
against master 985859c8: +1 288 −3 434 in 49 files.

Choices:

* **`G` per function** (§1.5): `VerdictCtx p` for `target_major_pins` (the core stubs);
  `closedNV p nvFns = true` for `target_major_of_outside(_tail)` and `class_fields_of`;
  `VerdictCtxU p` for `class_const_ok_header`, `class_const_ok`, `class_rec_ty_ok` (the header's
  consts-resolve site needs `UceProg`, `uce_errClaim_hi`); `CheckStructFieldSortsIE p` for the
  abstract constructor sorts (`check_struct_field_sorts_i` stays `callE`); `NitE …` for
  `nest_grow_group` and `NbG p` for `nest_seeds` (`nest_inst_type` stays `callE` until the second
  landing).
* **`class_const_ok_header` has its own model and refinement.** Its ok half used to be
  `install_header`'s `ihW`/`ihW_okT` (the same body, but another L function with other abort codes
  and another twin). Its twin is a prefix of `classConstOk`, so as with `rgT` (§3.8) there is one
  twin definition of the prefix, `cchT`, with `cchT_bind : classConstOk … = cchT … >>= rest`. With
  `install_header` migrated (§3.13), the shared hand model `ihW` (`ihK1–9`, `ihW_step`, `ih_specW`,
  `Arena/DeclHeader`) and `ihW_okT` (`Arena/DeclValT`, 160 lines) had no user left and are gone.
* **One post for a tail and its caller**: `target_major_of_outside` ends in its tail, so both
  refinements share `TmoPost`; `tmo_ref`'s tail arm is `tmt_ref` and `RefE.mono`. Likewise `IacPost`
  for the abstract constructor sorts and `CfgPost` for `class_fields_of`.
* **Frames as post fields**: `tmpW_mfrR` (the frame of `target_major_pins`, used by `class_majors`)
  is a field `mfr` of `TmpPost`, shorter than a lemma over the model.
* **`nest_grow_group`'s old ok proof was generic** over a call reading and an invariant; its one
  user fixed both, so `ngg_ref` states that invariant directly.
* **Callers** (depth 3, minimal): `class_majors` (`clmW_simC`, `clmE_claim`), `target_major_of`
  (`tmcW_simC`, `tmcE_claim`), `class_rec_tys_ok` (`rtsW` reads the call through `rtoR`),
  `check_abs_ctor_sorts_all` (`iaaW_simC`, `iaaE_claim`), `nest_cont_new` (`newRef_step`) read the
  halves through the run (`RefE.run_okW`, `RefE.run_err`). `nestSeedsE_claim` lost its `NitE`
  hypothesis (`cid_claim2`).
* **Placement**: `tmp_ref` in `Arena/IndT/RecCheckPins`, `tmt_ref`/`tmo_ref` in `Arena/IndT/RecGenTmf`
  (`IndBTmt`/`IndBTmo` keep the models only), `cch_ref`/`cco_ref` in `IndBHdr`, `rto_ref` in
  `IndBRec2`, `iao_ref`/`iac_ref` in `Arena/IndT/Install6`, `ngg_ref` in `Verdict/PosE2`, `nsdE` and
  `nsd_ref` in `PosTopE4` (the model lists `nckE_spec`, from `IndE`).
* **Recipes**: the default `finish` for `tmpE`, `iaoE`, `iacE`, `nsdE`; `finish … gen 20` for
  `classConstOkHeaderE` (`simp []` hits the recursion limit) and `classRecTyOkE`; `simp […]` for
  `tmtE` (1.8 → 1.0 s for `IndBTmt` against `finish`), `tmoE`, `nggE` (`finish` fails),
  `classConstOkE`, `cfoE` (slightly faster than `finish`).

Elaboration (user seconds, `lean` on the module alone, median of 3 interleaved runs, base master
985859c8, load 6–28):

| module | base | new | |
|---|---:|---:|---|
| `Verdict/PosE2M` | 17.85 | **20.65** | **slower (+2.8 s)**: `nggE` unified (`finish` fails; `simp []`) |
| `Verdict/PosTopE4` | 2.02 | **4.15** | **slower (+2.1 s)**: `nsdE` moved in … |
| `Verdict/PosTopE1` | 10.99 | 7.88 | … from here; the pair 13.0 → 12.0 |
| `Verdict/IndBHdr` | 3.34 | **4.63** | **slower (+1.3 s)**: the unified header model (`finish … gen 20`); with the deleted `ClassConstOk(Header)` 6.3 → 4.6 |
| `Verdict/IndBRec2`, `IndBRec3` | 3.47 | 4.04 | `rto_ref` moved in; with `RgW`, `RecGen7` (−0.3) |
| `Verdict/IndBTmt`, `IndBTmo`, `IndBToi`, `IndBTmc` | 8.23 | 8.32 | `IndBTmt` with `simp [Cmp.evalW, Cmp.eval]` (`finish`: 9.4) |
| `Arena/IndInstallSpec/IacW`, `IndPosSpec/GgW`, `GgW2`, `IndT/PosRoot`, `RecGenSpec/OcW` | 39.18 | 20.55 | hand models and specs gone |
| `IndPosSpec/P2sdW`, `IndT/RecGen3`, `RecGenSpec/ClassConstOk`, `ClassConstOkHeader` (deleted) | 7.87 | — | |
| `Verdict/PosE1M` | 24.92 | 27.03 | import changes only (noise; load) |
| the other 30 modules | 74.4 | 74.0 | |
| **sum (48 modules)** | **192.3** | **171.2** | **−11 %** |

Each flagged module is offset by the module that held the deleted hand model, except `PosE2M`.
For the generator: nothing was missing in this landing; `nestSeedsFuel_spec` (a singleton-list post)
and `nckE_spec` (a unified spec with `G = True`) were taken without wrappers, so the wrappers of §3.9
(`noaW1`, `cpW1`, `ucW1`) may be removable.

### 3.17 Batch 2b, second landing (`class_rule_ok`, `class_rules_ok_one`, `nest_inst_type`)

The three functions that waited for `class_rule_ok_guards` and `lvl_eq_fueled` (§3.11):

| function | before: ok refinement(s) + error claim(s) | after | change |
|---|---|---|---:|
| `class_rule_ok` | `cruleW_okC` 84, `classRuleOk_claim` 142 = 226 | `crule_ref` 109 + `CrulePost` 9 = 118 | −48 % |
| `class_rules_ok_one` | `cr1W_relC` 42, `cr1_claim` 50 = 92 | `cr1_ref` 37 (`CrulePost`) | −60 % |
| `nest_inst_type` | `nitW_ok` 71, `nitLe_realC` 36, `NitLe` 19, `NtyOk`/`nty_ok` 13; `nitE_all` 163, `NitE` 8 = 310 | `nit_ref` 127 + `NitPost` 9 = 136 | −56 % |
| **pairs** | **628** | **291** | **−54 %** |

Gone with them: the hand models `cruleW`/`cruK1–4`, `cr1W`/`cr1K`, `nitW`/`nitK1–5`, `ntyR`, their arms
and specs (`classRuleOk_spec`, `classRulesOkOne_spec`, both `nestInstType_spec`), `nitWf`; the files
`Arena/IndT/RecGen4`, `Arena/IndPosSpec/NitLe`, `Arena/IndT/PosNit`. Whole diff against master
62ca90b6: +413 −1 049 in 30 files.

* **`G`**: `VerdictCtxU p` for `class_rule_ok` and `class_rules_ok_one` (the domains' consts-resolve
  site, `uce_errClaim_hi`, as `class_rule_ok_guards`); `closedNV p nvFns = true` for
  `nest_inst_type` (`lvl_eq_fueled`'s `NVAt p "lvl_eq_c"` follows from it, `nvAt_of`).
* **`NitE` is gone.** It was the error claim of `nest_inst_type` that the block's steps and the
  depth-2 callers assumed; they now read `nit_ref` (`nest_grow_group`'s `nggE` and `nest_seeds`'
  `nsdE` call `nitE` as a unified callee; `nest_cont`'s `errors` model `ncE` keeps `callE` and reads
  both halves through the run). `ngg_ref`'s `G` weakened from `NitE …` to `closedNV`. `NbG` did not
  change (`NitE` was derived inside the block from it, `nitE_all`).
* **`class_rules_ok_one`** moved to `IndBRec4` next to `class_rule_ok` (its unified model ends in
  `cruleE`, and `RecGen9` imports it there). `class_rules_ok`' hand model reads it through
  `cr1R`; `crsW_simC`/`crrW_simC` take `CrsProg` instead of `CruleProg` (the lookup).
* **Generator observations** (not changed here): `cruleE` needs `open Classical in`: the callee
  spec of `flush_caches` has an undecidable guard (`FlushOK`), and without it the generated
  model reads `sorry = true` for that guard and the steps fail, silently. A spec whose post
  has an extra length conjunct `r = [r.headD 0, r.getD 1 0, r.getD 2 0]` is rejected as an
  "ambiguous post" in `unified` mode (`piBinders_spec`; `nitE` lists `piBinders_spec'`).
* **Recipes**: the default `finish` for `nitE`; `simp [Cmp.evalW, Cmp.eval]` for `cruleE`/`cr1E`
  (`IndBRec4` 1.96 s against 2.30 s with `finish`). With `nitE` lifted, `nggE` stays `simp []`
  (17.7–19.4 s for `PosE2M`; `simp [rdW]` 18.5–23.2, `finish` fails) and `nsdE` the default
  (`PosTopE4` 3.9–4.8 s; `simp []` the same, `simp [rdW]` 64–87 s).

Elaboration (user seconds, `lean` on the module alone, median of 3 interleaved runs, base master
62ca90b6; load 5–100):

| module | base | new | |
|---|---:|---:|---|
| `Arena/RecGenSpec/Rec3TmdWDecB`, `CfhW`, `CrsK6`, `CrsProg`, `CruleProg`, `FlushStage` | 20.54 | 15.18 | hand models and specs gone |
| `Verdict/IndBRec4`, `IndBRec5`, `IndBRec6`, `IndBCrg` | 12.08 | 10.75 | |
| `Arena/IndT/RecGen4`, `IndPosSpec/NitLe`, `IndT/PosNit` (deleted) | 1.88 | — | |
| `Verdict/PosE1M` | 24.61 | 21.29 | `nitE` unified (noise: load) |
| `Verdict/PosE2M`, `PosTopE4` | 21.41 | 20.98 | `nitE` lifted in `nggE`, `nsdE` |
| `IndPosSpec/NitW`, `NtyW`, `NestOccAny`, `GgW` | 6.05 | 4.65 | |
| the other 9 modules | 10.83 | 9.95 | |
| **sum (29 modules)** | **97.4** | **82.8** | **−15 %** |

No module is more than 10 % slower.

Batch 2b in all: 14 functions migrated, the pair lines 2 781 + 628 = 3 409 → 1 399 + 291 = 1 690
(−50 %), plus about 850 lines of hand models and specs and the shared `ihW`/`ihW_okT`.

### 3.18 Batch 3b, first landing (`target_major_of_const`, `target_major_of`, `class_majors`)

Batch 3b's functions (depth 3–5 of §3.1 in the `IndB*` target and class families, callees
migrated): `target_major_of_const`, `target_major_of`, `class_majors` (this landing);
`class_rec_tys_ok`, `class_rules_ok`, `class_recs_rules_ok_go`, `class_recs_rules_ok` and
`target_k53_args`, `target_k53_heads`, `target_k53` in their own landings. Not in 3b:
`check_abs_ctor_sorts_all` and `check_block_positivity` (block checks, 3c), `check_sum_tele`
(its callee `check_sum_tele_slow` is 3a's), `classes_nfs` (hand model, §3.3).

| function | before: ok refinement + error claim(s) | after | change |
|---|---|---|---:|
| `target_major_of_const` | `tmcW_simC` 95, `tmcE_claim` 117, `tmc_claim` 29 = 241 | `tmc_ref` 86 (`TmoPost`) | −64 % |
| `target_major_of` | `tmfW_simC` 85, `tmfE_claim` 110, `tmf_claim` 23 = 218 | `tmf_ref` 81 (`TmoPost`) | −63 % |
| `class_majors` | `clmW_simC` 174, `clmE_claim` 211, `classMajors_claim` 25 = 410 | `clm_ref` 161 + `ClmPost` 7 + `classMajors_claim` 23 = 191 | −53 % |
| **pairs** | **869** | **358** | **−59 %** |

`classMajors_refinesC` keeps its statement (`RefE.triple`, 27 → 29 lines). Gone with them: the
hand models `tmcW`/`tmcK1–2`, `tmfW`/`tmfK1–3`/`tmfK6` with their arms and specs `tmc_spec`,
`tmf_spec` (`Arena/RecGenSpec/Tmc`), the generated ok model `clmW` and `clm_spec`
(`Arena/RecGenSpec/Clm`), the `errors` models. Whole diff against master d4f85701: +324 −988 in 11
files.

* **`G`**: `closedNV p nvFns = true` for `target_major_of_const` and `target_major_of` (every callee
  is lifted or unified under it: `tmmE`, `tmoE`, `tmcE`); `VerdictCtx p` for `class_majors`
  (`tmp_ref`'s core stubs; `tmf_ref` through `hV.nv`).
* **Post**: the three `target_major_of*` share `TmoPost` with `tmo_ref`/`tmt_ref` (the member branch
  `tmm_ref`'s `TmmPost` by `RefE.mono`, its `AFr` to `AbsOK`). `ClmPost` has `class_majors`' five
  conjuncts as fields.
* **Callee readings**: `block_shape_member_names`, `sl_find`, `get_app_args_f`, `get_app_fn_f` and
  `e_view` through `callW_spec` (lifted runs, as `tmoE`); `class_majors`' `intern_const`,
  `mk_app_n_f` and `sl_cons` through their `Option` models (`internConst_spec`, `mknF_spec`,
  `slCons_specW`, as `tmpE`), so the stage lemmas (`internConst_stage`, `mknF_ok`, `clsConsW`) take
  the lifted value directly.
* **Placement**: the models stay in `Verdict/IndBTmc`, `IndBTmf`, `IndBClm` (now models only, below
  the refinements); `tmc_ref`/`tmf_ref` next to `tmo_ref` in `Arena/IndT/RecGenTmf`, `clm_ref`,
  `classMajors_refinesC` and `classMajors_claim` (`RefE.coreSpecE`, for `IndArmE`'s
  `classMajorsE_of`) in `Arena/IndT/RecGen19`.
* **Callers** (minimal): `check_block_classes`' ok refinement (`cbcW_simC`, `RecGen21`) and error
  claim (`BlkE4`) read `clm_ref` through the run (`RefE.run_okW`, `RefE.run_ok`; the post's
  `(r, s'.mem).snd` needs `dsimp only` before `omega`, §3.2's pitfall).
* **Recipes**: `simp [Cmp.evalW, Cmp.eval]` for all three models (as the `errors` ones); every
  proof went through on the first full build.

Elaboration (user seconds, `lean` on the module alone, median of 3 interleaved runs, base master
d4f85701, load 32–59):

| module | base | new |
|---|---:|---:|
| `Verdict/IndBTmc`, `IndBTmf`, `IndBClm` (models) | 5.86 | 4.44 |
| `Arena/IndT/RecGenTmf`, `RecGen19`, `RecGen21` | 4.82 | 3.96 |
| `Verdict/BlkE4`, `IndArmE`, `IndBTmm` | 24.01 | 21.29 |
| `Arena/RecGenSpec/Tmc`, `Clm` (deleted) | 7.56 | — |
| **sum (11 modules)** | **42.3** | **29.7** |

No module is slower.

### 3.18 Batch 3b, the rules and recursor types (`class_rec_tys_ok`, `class_rules_ok`, `class_recs_rules_ok_go`, `class_recs_rules_ok`)

The depth-3–4 functions of the `IndBRec*` family whose callees are unified (`class_rec_ty_ok`,
§3.16; `class_rules_ok_one`, §3.17):

| function | before: ok refinement + error claim(s) | after | change |
|---|---|---|---:|
| `class_rec_tys_ok` | `rtsW_simC` 115, `rtsE_claim` 132, `classRecTysOk_claim` 21 = 268 | `rts_ref` 115 + `RtsPost` 6 + `classRecTysOk_claim` 18 = 139 | −48 % |
| `class_rules_ok` | `crsW_simC` 136, `crsE_claim` 178, `classRulesOk_claim` 26 = 340 | `crs_ref` 143 + `CrsPost` 7 = 150 | −56 % |
| `class_recs_rules_ok_go`, `class_recs_rules_ok` | `crrW_simC` 147, `crrE_claim` 177, `classRecsRulesOk_claim` 33 = 357 | `crr_ref` 161 + `crra_ref` 27 + `CrrPost` 8 + `classRecsRulesOk_claim` 16 = 212 | −41 % |
| the three `@[refines]` | 25 + 33 + 33 = 91 | 26 + 33 + 26 = 85 | −7 % |
| **pairs** | **965** | **501** | **−48 %** |

Gone with them: the hand models `rtsW`/`rtsK1–3`/`rtoR`, `crsW`/`crsK1–6`/`cr1R`, `crrW`/`crrK1–5`/`crraW`,
their arms, grind patterns and specs (`classRecTysOk_spec`, `classRulesOk_spec`,
`classRecsRulesOkGo_spec`, `classRecsRulesOk_spec`, `rtoR_spec`, `cr1R_spec`); the files
`Arena/IndT/RecGen7`, `RecGen9`, `RecGen10` and `Arena/RecGenSpec/CrsK6`. `classRulesOk_claim` had no
user left (its one user was `crrE_claim`). Whole diff against master d4f85701: +487 −1 330 in 15 files.

* **`G`**: `VerdictCtxU p` for all four (the callees' `rto_ref` and `cr1_ref` have it; the
  functions' own errors are aborts `0` and lifted no-verdict callees).
* **Models**: `classRecTysOkE` calls `classRecTyOkE`, `crsE` calls `cr1E`, `crrE` calls `crsE`,
  `crraE` calls `crrE` (unified callees); `sl_cons`, `cv_lps` (`cvLps_specW1`, so `IndBRec5` imports
  `Verdict/DeclValE`), `param_levels`, `class_gen_rule`, `target_major_at` and `rec4` lifted. The
  recursion is the model's own; each refinement is one induction over it. The `classGenRule = none`
  reject is `ErrClaim.fail` in place.
* **Posts**: `RtsPost` (stage, growth, `decCVS`, memo), `CrsPost` and `CrrPost` (the same with
  `decEL`/`decRRS` and the core step). `class_recs_rules_ok` repacks `class_recs_rules_ok_go`'s
  result, so `crra_ref` shares `CrrPost`.
* **Callers**: the spine (`gen_rec_check_prep`'s `grpE`, `gen_rec_check`'s `gckE`, `GenRec2`,
  `GenRec3`) already read these through the run; they keep `classRecTysOk_refinesC`,
  `classRecsRulesOk_refinesC` (`RefE.triple`) and the two claims (`RefE.coreSpecE`) with unchanged
  statements; only two imports changed.
* **Placement**: the refinements and the derived theorems in `Verdict/IndBRec3`, `IndBRec5`,
  `IndBRec6` (`ctorsAt_denote` moved there from `RecGen10`).
* **Recipes**: the default `finish` for `classRecTysOkE` (it was `simp []` as an `errors` model),
  `simp [Cmp.evalW, Cmp.eval]` for `crsE`, `crrE`, `crraE` (as before). No generator or kit change
  was needed.

Elaboration (user seconds, `lean` on the module alone, median of 3 interleaved runs, base master
d4f85701, load ≈ 28):

| module | base | new | |
|---|---:|---:|---|
| `Arena/RecGenSpec/Rec3TmdWDecB` | 17.87 | 1.15 | the hand specs `classRecsRulesOkGo_spec` etc. gone |
| `Arena/RecGenSpec/ClassRecTysOk`, `DecCVX`, `DecRR`, `CrsK6` (deleted) | 5.93 | 1.52 | |
| `Arena/IndT/RecGen7`, `RecGen9`, `RecGen10` (deleted) | 3.41 | — | |
| `Verdict/IndBRec3`, `IndBRec4`, `IndBRec5`, `IndBRec6` | 13.52 | 11.67 | |
| `Arena/IndT/GenRec2`, `GenRec3` | 3.74 | 4.00 | `GenRec2` 2.41 → 2.65 (+0.24 s, import change only: it now imports `IndBRec3`) |
| **sum (14 modules)** | **44.5** | **18.3** | **−59 %** |

No module of the family is more than 10 % slower (`GenRec2`'s +10 % is 0.24 s and comes from its
import, not from a proof in it).

### 3.18 Batch 3a, first landing (the `Nat.div` pin gate, `certify_nat_eqs`)

The batch's functions (§3.1's inventory at depth 3–5 in the `Decl*`/`DefEq*`/`Whnf*` families, and
what batch 2 left): `check_div_mod_pin_loop` (depth 3), `check_div_mod_pin` (depth 4), with them
the pin gate `defn_div_gate` (no `@[refines]` of its own, so not in the inventory; §3.13 left it
for depth ≥ 3) and the depth-0 leaf `certify_nat_eqs` (error model and claim beside the ok
refinement `certW_okT`; `dnc_ref` read it through `callE`). This landing migrates these four;
`class_stream_recs`, `check_sum_tele_slow` and `check_sum_tele` are the second. The other
`Decl*`/`DefEq*`/`Whnf*` functions of the inventory are done; the `errors` models left in
`DefEqLazyE`, `DefEqSpineE`, `DefEqQuickE`, `DefEqEagerE`, `WhnfModels3E` are the knot's own
functions (their ok halves are the knot's `CoreSpec` slots, not in §3.1's inventory).

| function | before: ok refinement(s) + error claim(s) | after | change |
|---|---|---|---:|
| `check_div_mod_pin_loop` | `loopC` 146; `loopCE` 152, `LoopClaimE`/`loopClaimE` 24, `CpaClaimE`/`cpaClaimE_of` 18 = 340 | `loop_ref` 122 + `PinPost` 5 = 127 | −63 % |
| `check_div_mod_pin` | `cpC` 108; `cpCE` 133 = 241 | `cp_ref` 116 + `CpPost` 4 = 120 | −50 % |
| `defn_div_gate` | `divGateSpecC` 78; `divGateSpecE_of` 94 = 172 | `dg_ref` 81 + `DgPost` 6 + `divGateSpecC` 13 + `divGateSpecE_of` 9 = 109 | −37 % |
| `certify_nat_eqs` | `certW_okT` 78; `certE_okT` 60 = 138 | `cert_ref` 61 + `CertPost` 5 + `certW_okT` 13 = 79 | −43 % |
| **pairs** | **891** | **435** | **−51 %** |

Also gone: the generated `W` models `loopW`, `dmCpW`, `dgW` with their specs, the hand `certW` with
`certify_specW`, the two unused `errors` models of `check_div_mod_pin(_loop)` in
`Verdict/DeclGatesE2` (each function had two), and with `divGateSpecE_of` moved out the modules
`Verdict/DeclGatesE2` and `Verdict/DeclGatesE` (`gateNvList`/`nvlG` had no other user). Whole diff
against master d4f85701: +353 −951 in 12 files.

* **`G := CoreStubsE p`** for all four: the lifted callees' errors are `.oob`; the attempt
  (`cpa_ref`) and `is_def_eq_core` need the core stubs' claims.
* **The callers keep their statements.** `cdf_ref` (`DeclDefnT`) reads the gate through `callE`
  (it needs the call's write-set frame, as in §3.13), so `DivGateSpecC` (with `PinSetsR` after and
  the frame) and `DivGateSpecE` stay as statements, now one-liners from `dg_ref` through the run
  (`RefE.run_okW`, `RefE.run_err`); `DgPost` leaves out what only the run gives. `dnc_ref`'s
  certificate arm takes `RefE.run_err … cert_ref`; `certW_okT` (`@[refines]`) and `certW_okC`
  keep their statements.
* **Placement**: `loop_ref`, `cp_ref` in `Verdict/DivModPinE` (now imported by `Arena/DeclDivGateT`
  instead of `DeclDivGateT2`), `dg_ref` with `DivGateSpecC/E` in `Arena/DeclDivGateT`, `cert_ref` in
  `Arena/DeclNatGateT`. Models take the program bundle (`fns [hD.lCheckDivModPinLoop ↦ …]`).
* **Recipes**: `extra [ld64_rdW_specE] simp []` (the old `errors` recipe) for the three gate models;
  the full `extra` list and `simp []` for `certifyNatEqsE`. No kit or generator change needed.

Elaboration (user seconds, `lean` on the module alone, median of 3 interleaved runs, base master
d4f85701, `_tmp/unify-b3a/times1.txt`, load 30–80; `DeclDivGateT`, `DeclDivGateT2`, `TopE` from
a second series, `times1b.txt`, the first being noisy for `DeclDivGateT2`):

| module | base | new | |
|---|---:|---:|---|
| `Arena/DeclDivGateT` | 1.51 | **1.98** | **slower (+0.5 s)**: `defnDivGateE` and `dg_ref` moved in … |
| `Verdict/DeclGatesE2`, `DeclGatesE` (deleted) | 4.56 | — | … from here |
| `Verdict/DivModPinE` | 6.47 | 3.77 | the two unified models and refinements instead of the claims |
| `Arena/DeclDivGateT2` | 13.30 | 12.57 | `loopC` gone |
| `Arena/DeclDivModSpec/DecCIDefnValue`, `RomPinSets` | 4.52 | 2.18 | the `W` models gone |
| `Arena/DeclNatEq`, `DeclNatGateT` | 9.33 | 9.31 | |
| `Arena/DeclDefnT`, `Verdict/DeclDefnE`, `TopE` | 4.72 | 4.37 | |
| **sum** | **44.4** | **34.2** | **−23 %** |
