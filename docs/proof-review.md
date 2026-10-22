# Proof-overhead review (2026-10-22, lane `proofreview`)

A fresh read of four representative functions, from the L code through the word model, the L-side
spec and the refinement, plus project-wide counts (`grep`/`wc` over `ConAgua/`, master `1089eb4`).
Nothing in the code was changed.

## 0. Summary

* **The headline ratios undercount.** DESIGN.md's "4–5 proof lines per L line" for the walks
  counts only the `*Refine.lean` file. Counting everything written for the function (word model,
  continuations, guarded equations, L spec, program bundle, refinement), the spectrum is about
  **12 (walks) to 20 (whnf slot) proof lines per L line**, not 4 to 19.
* **The proof is mostly plumbing.** In all four samples, genuine algorithmic reasoning (the facts
  you would put in a paper proof: cut-off arithmetic, a loop invariant, "hit means the cached value")
  is **5–10 %** of the lines. The rest is:
  * the hand-written word model: a second copy of the L code (25–45 %);
  * per-callee case splits on `Option` results (20–35 %);
  * re-establishing the relation and frames (10–15 %);
  * decoding words into twin values (5–15 %);
  * program-lookup hypotheses and fuel (5 %).
* **The biggest repeated pattern** is the three-layer architecture L ⇒ word model `fW` ⇒ twin. The
  model is a by-hand transliteration of the L text into `Option (… × Mem)` with first-order
  continuations `fK₁…fKₙ`, `fKᵢ_some` equations and `grind_pattern`s. The relational lemma then
  walks it callee by callee with
  `cases h : callee … | none => rw [h] at hb; simp at hb | some x => obtain …; rw [h, fK_some] at hb`.
  All of this follows from the L AST.

## 1. The four functions

Line counts are physical lines including doc comments. "L" counts the `lfn` text.

### 1.1 Phase-4 expression walk: `lift_go` + five arms + `lift_entry` (`liftLooseBVars*`)

Files: `Arena/Lift.lean` (591), `LiftSpec.lean` (171), `LiftRefine.lean` (521).

| part | lines | what it is |
|---|---:|---|
| L code (`liftGo` 24, arms 65, entry 6) | ~99 | |
| word model `liftW`/`lift*W` (mutual) | 120 | the L text again, as `if … then none else …` |
| continuations `appK₁…pjK₁` + `_some` eqs | 63 | first-order continuations so `grind` can match |
| guarded equations (`liftW_cut`, `liftW_app`, `…_hit/_miss`) + 22 `grind_pattern`s | 164 | one `rw [liftW]; simp [h…]` per arm |
| `LiftProg` bundle (33 lookups) + `liftProg`/`liftProg_ok` | 48 | program-lookup hypotheses |
| L spec (`liftGo_step`, 5 `*_step`, fuel induction, entry model+spec) | 190 | `vcgen … <;> finish (gen := 20)`; the arms are copy-paste |
| refinement: memo glue (`withLC`, `lmemo_set/clear`) | 36 | relation re-establishment (`ArenaD`) |
| refinement: statements `LGoOK`/`ArmRef`/`LArmOK` | 39 | each arm's twin arguments spelled out again |
| refinement: dispatcher `lgoOK_succ` | 135 | 10 tags × (`by_cases` tag, `by_cases` bound, dead branch, `view_run`, guarded eq) |
| refinement: `tail_ok`, `probe_ok` | 58 | memo hit/miss + intern tail, shared by the 5 arms |
| refinement: 5 arms | 139 | `cases h1 : liftW … \| none \| some`, IH, `tail_ok` |
| refinement: fuel induction + entry + `_run` | 90 | `liftEntry_run` is 25 lines of generic run⇒triple plumbing |
| **total proof** | **~1150** | **11.7 per L line** (DESIGN.md quotes 4.8: refinement file only) |

What the refinement lines do: hypothesis plumbing (callee `cases`, `obtain`, `rw … at hb`) ≈ 45 %,
dead-branch closing ≈ 10 %, view/decoding ≈ 15 %, relation re-establishment ≈ 10 %, genuine ≈ 5 %
(`cut_iff`, `add_noovf`, `succW_toNat`: word vs `Nat` arithmetic at the cut-off and `c + 1`).
Typical dispatcher arm, repeated ten times:

```lean
  by_cases g5 : h >>> 28 = 5
  · by_cases hc : rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h
    · rw [liftW] at hb; simp [hcut, hs, g5, hc] at hb          -- dead branch: model aborts
    rw [view_run _ a _ (view_lam m a hR h hh (vok 28 hc) g5).1]  -- twin's view
    rw [liftW_lam n m h c k hcut (vok 28 hc) g5] at hb           -- guarded equation
    exact (arm 28 hc).2.1 (vok 28 hc) g5 hb
```

`Inst1*` (98 L lines, 446 + 174 + 519 lines) is the same text with renames. It was produced by
`scripts/inst1_from_lift.py`, which shows that the model, the specs and most of the refinement are
mechanical.

### 1.2 whnf: the knot's `whnf` slot and `whnf_loop` (`WhnfDelta.lean`, `WhnfDeltaSlot.lean`)

L: `whnfL` 10, `whnfLoopB` 7, `whnfLoopL` 4 = **21 L lines**. `WhnfDeltaSlot.lean` is 385 lines,
plus the `WhnfLoopSpec`/`WhnfStepSpec` statements (~25) and a share of `WhnfDeltaProg`
(41 lookups for 16 functions).

| part | lines | class |
|---|---:|---|
| `whnfStuck_iff` (the tag word vs `whnfStuckTag`) | 14 | decoding (5 `rw [show (2 : UInt32) = …]` + 32-way `by_cases`) |
| model `whnfW`, `whnfLoopW` + guarded eqs | 47 | model |
| L specs (`whnf_spec`, `whnfLoopB_spec`, `whnfLoop_spec`) | 42 | `vcgen` + `finish` |
| `CoreS.set_wh`, `KeptAll.wh` | 56 | relation re-establishment: "copy of `CoreS.set_wc`" |
| twin unfoldings (`knot_whnf_stuck/hit/miss`, `whnfLoop_done/cont`) | 37 | unfolding |
| `WhnfStepUpTo` + `whnfLoopW_ok` (loop induction) | 53 | fuel + plumbing; genuine core ~10 |
| `whnfLoop_refines`, `whnf_refines` | 97 | triple⇒run⇒triple plumbing, 3 cases (stuck/hit/miss) |
| **total** | **~410** | **≈ 19.5 per L line** |

`CoreS.set_wh` is the clearest case of re-establishing the relation. It rebuilds the whole `CoreS`
record by hand, one framing argument per component, and the same lemma exists as `set_wc`, `set_wk`,
`set_in`, `set_io`, `set_de`, `set_lq`, `set_lsq` (8 × ~50 lines). The project has 40 `CoreS.*`
lemmas (1185 lines) and 210 `*frame*` lemmas (2427 lines).

```lean
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [98] [101] (by simp) (by simp) m m' hf a
        hS.arena.1), DerR.of_store _ _ _ (DerR.frameM [98] [101] m m' hf (by simp) a hS.arena.2) rfl⟩,
      ⟨mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wc,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wk,
        hq, …   -- 12 memo components, then pins, env, readL, readLs, nwf, erec, spn, memos, bstk, den
```

`WhnfStepUpTo`/`KnotUpTo` exist because "L has no fuel-monotonicity lemma" (`WhnfDeltaSlot.lean`
docstring). `Front/RunModel.lean` now has `exec_mono`/`invoke_mono`. The 234 `UpTo` mentions are
obsolete scaffolding.

**Side finding: one function proved twice.** `nat_succ_ok` (17 L lines) is refined under `CoreS`
(`WhnfDeltaRefine.lean`: model 19, spec 9, twin-run eqs 30, `callW_natSuccOk` 125 → ~190 lines) and
again under `StageR` (`DeclNatLit.lean`: its own `natSuccOkW` with `List Word` results, spec 10,
`natSuccOk_ref` 107 → ~135 lines). The file header gives the reason: the function uses only pins,
env and expression tables, but the two relations are not related. `DeclNatLit.lean` (668 lines) is
this duplication for the whole `nat_lit_supported` family. `IndMaster.lean`'s 49 `*_stage` lemmas
(1396 lines) re-wrap master callees for `StageR` in the same way.

### 1.3 Inductive check (lane `indproofs2`): `cons_sum_ctors` + `ctor_info_rec`

L: `consSumCtorsL` 9, `ctorInfoRecL` 12 = **21 L lines**. Proof: `IndSumSpec9.lean`, 328 lines. It
uses lane `indproofs2`'s new library: `IndSim.lean` (`Sim`, 107), `IndDecStab.lean` (`DecB`, 652),
and lane `decls2`'s `envPushW_ok`.

| part | lines | class |
|---|---:|---|
| `ciRecMem`/`ciRecW` + `ciRec_specW` | 30 | model + spec (a model of 7 stores) |
| `cscW`/`cscK1..3` + 5 `_some` eqs + `csc_spec` | 53 | model + spec |
| `rdW_set64_ne_er`, `decCV_shift`, `ciRecMem_eq`, `ciRec_stage` | 95 | **decoding a freshly written record**: index arithmetic |
| `decCVp_truncM`, `rdW_of_iwN_truncM` | 17 | decoding (`DecB` adapters) |
| `cscW_ok` (fuel induction) | 80 | ~55 plumbing, ~15 decoding, ~10 genuine |
| census `consSumCtors_refines` | 18 | `triple_post` glue, half of it the statement |
| **total** | **~330** | **≈ 15.7 per L line** |

The record write is the expensive part. `ciRec_stage` has six copies of
`have c1 : (cq + 1).toNat = cq.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega` and a
`rcases i with _ | _ | _ | _ | i` over the copied words, to show that a 7-word `EREC` record written
by `st64`s decodes as `.ctorInfo cv nP nF`. DESIGN.md (indproofs2 landing 2) measures ~80 lines per
record kind. The project has 915 `UInt64.toNat_add` and 987 `.toNat < 2 ^ 32` occurrences.

`Sim.bindK` is not used here: `cscW_ok` still does
`cases h2 : callW p k "env_push" … with | none => rw [h2] at h; simp [cscK2] at h | some x => …`
per callee. `Sim.bindK` appears in 24 files only.

### 1.4 Declaration arm: `check_thm_val` (`DeclArms.lean`, `DeclValSpec.lean`, `DeclValRef.lean`)

L: **14 lines**, a straight line through 8 calls and 2 `abort` guards. Its own proof is complete; the
census status is `sorry` only through the core stubs.

| part | lines | class |
|---|---:|---|
| `tvK1..tvK4`, `tvW`, 5 `_some` eqs, 5 `grind_pattern`s | 48 | model: **3.4 model lines per L line** |
| `tv_specW` (`vcgen` + `finish (gen := 20)`, `maxHeartbeats 1600000`) | 18 | L spec |
| `checkThmVal_eq` (twin's `do` re-associated) | 9 | unfolding |
| `tvW_ok` | 87 | 5 callees × ~10 lines plumbing; ~12 decoding (`ev`, `et`, `hcb`); ~5 genuine (`b = true` from `r4 ≠ 0`) |
| share of `dvK1_ok` (59 lines, shared by 3 value checks) | 20 | same pattern |
| census `checkThmVal_refines` | 17 | `triple_post` + `AM.of_run_ok` |
| share of `ValProg` (10 lines, 4 functions) | 3 | lookups |
| **total** | **~200** | **≈ 14 per L line** |

This is the cleanest view of the per-callee pattern (7 lines, ×5 in `tvW_ok`):

```lean
  cases h2 : stubM "ensure_sort_core" m1 [vis, 0, r1.headD 0] with
  | none => rw [h2] at h; simp [tvK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, tvK2_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    ensureSortCore_spec dn vis fe 0 (r1.headD 0) hx1l m1 m2 a1 r2 h2 hS1
```

followed at the end by `simp only [StateT.run_bind, hrun1, exc_ok_bind', hrun2, …]` to replay the
twin's binds. `Sim.bindK` does exactly this and was written for it.

## 2. What repeats across the four

| pattern | where in the samples | project-wide count |
|---|---|---|
| **P1. Hand-written word model + continuation defs + `_some` eqs + `grind_pattern`s**: a second copy of the L text | 347 / 410 / 83 / 48 lines | 1163 `…W` defs (9.8k lines), 1579 continuation defs (9.1k), 1006 `K_some` eqs (2.3k), 1697 `grind_pattern`s (2.4k), guarded equations (several k) |
| **P2. The L spec**: `rw [invoke_eq _ hp.f]; simp only [callFn, fL]; cases n \| zero => vcgen [exec] <;> grind \| succ n => sym only […] => vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, <callee specs>] <;> finish` | every function | 1688 `invoke_eq`, 1231 identical `vcgen` heads, 747 identical zero-fuel cases |
| **P3. Per-callee `Option` case split** in the relational lemma: `cases h : callee \| none => rw/simp \| some => obtain; rw [h, K_some]; obtain := callee_ok`, then replay the twin's binds | 5 arms, 5 callees, 2 callees | 957 `cases h : callW/stubM`, ~4.9k `cases h :`, 2524 one-line `\| none =>` dead branches, 1549 `obtain ⟨r, m⟩ := q`, 1369 `Option.some.injEq, Prod.mk.injEq` |
| **P4. Relation re-establishment and frames**, by anonymous-constructor rebuilding | `lmemo_set`, `CoreS.set_wh`, `ciRec_stage`'s `StageR` part | 210 frame lemmas (2.4k), 40 `CoreS.*` (1.2k), `MemFrame` 1198 uses, `IWGrow` 1254 uses |
| **P5. The same function under two relations** (`CoreS` vs `StageR` vs `ArenaD` vs `LoopR`) | `nat_succ_ok` ×2 | `DeclNatLit` 668, `IndMaster` `_stage` 1.4k, `DeclMasterStage`, `constE_stage`, … |
| **P6. Decoding words into twin values** (`decE`/`decI` truncation, `< 2^32`, `toNat_add`, tag words `h >>> 28`, `tierW`/`idxW`, record offsets) | `cut_iff`, `whnfStuck_iff`, `ciRec_stage`, `ev`/`et` | 915 `toNat_add`, 987 `< 2 ^ 32`, 719 `HW`, 1061 `>>> 28 =`, 2348 `tierW`/`idxW`, 7113 `rdW (m.arr64 X)` |
| **P7. Program-lookup hypotheses** | `LiftProg` 33 fields, `WhnfDeltaProg` 41, `ValProg` | **4801** `p.lookup "…"` lines; 109 bundle structures (1.8k lines) |
| **P8. Fuel scaffolding**: `n ≤ F` twin-fuel quantifiers, `UpTo` families, zero cases | `LGoOK`'s `n ≤ F`, `WhnfStepUpTo` | 234 `UpTo`, 747 zero cases |
| **P9. Triple ⇄ run ⇄ census glue** (`M.triple_of_run`, `M.of_run`, `triple_post`, `AM.of_run_ok`, `*_run` corollaries) | `liftEntry_run`, `whnf_refines`' first 10 lines, every census theorem | 601 `triple_post`/`triple_of_run`, 367 `AM.of_run_ok`, 655 census theorems (16.6k lines) |
| **P10. Tag dispatch with hoisted view checks**, in L, model, guarded eqs and refinement | `lift_go` (10 tags), `whnf` stuck tags | 330 `if g == k {` arms in L |

A crude classification of all 22.4k declarations by name (script in the lane's scratchpad) gives:
L code 21.8k lines; models and continuations ~19k; specs ~28k; relational `_ok`/`_ref`/`_stage`
~54k; census theorems 16.6k; "other theorems" (guarded equations, decoders, frames, twin
unfoldings) ~97k.

## 3. Smaller with the current tools (no change to L)

1. **Use `Sim` everywhere, and state callee facts as `Sim` facts** (P3, P9). `IndSim.lean` has
   `Sim.bindK`, `Sim.bind_twin` and `Sim.run`. A callee lemma stated as
   `Sim (calleeW …) (twinOp) a Q` turns each 7-line block in §1.4 into one `refine Sim.bindK rfl
   (fun _ _ => rfl) (callee_sim …) fun r x m a hQ => ?_` and removes the final bind replay and the
   dead branches (`Sim.of_none`). The lane's pilot measured 45 lines for 4 callees, against ~60.
   `tvW_ok` would go from 87 to ~35; `cscW_ok` from 80 to ~40. **Estimate: 8–12k lines** over the
   ~46k lines of relational lemmas. Cost: restating the callee lemmas, ~1 line each. A two-line
   `macro "sim_call" t:term : tactic` would help further but goes against PLAN's "no custom
   tactics"; the lemma form already gets most of the gain.
2. **Drop the `UpTo` families with `exec_mono`** (P8): `KnotUpTo`/`WhnfStepUpTo` become the plain
   spec at `n`. **~1k lines**, mostly in statements. It also removes the `hk.mono (by omega)`
   arguments. Cost: low (a `Spec.mono` lemma per spec shape, derived from `invoke_mono`).
3. **One generic "memo insert keeps `CoreS`" lemma** (P4): `CoreS` as a record of components
   indexed by the memo schema, with `set_*` proved once over `S : MemoSch` by `decide` on
   `S.arr ∉ others`. **~400 lines** now (8 `set_*`), and every new memo after that is free. The same
   idea applies to `ArenaR.with_memos`/`memos_build`.
4. **Program bundles from the text** (P7): replace hand-listed `XProg` structures with one
   `ProgHas p fs` checked by `decide +kernel` through the `wfFast` search tree, whose fields are
   projected by a `simp` lemma. Alternatively make the bundle a class instance that `liftProg_ok`-
   style lemmas provide. The 600-entry `rfl` timeout (DESIGN, decls3) is exactly what the search
   tree avoids. **~3–4k lines**, low cost.
5. **Keep handle bounds in the relation, not in every post** (P6): `ArenaR` could carry "every word
   in a handle column, and every intern result, is `< 2^32`" (the `HW` invariant). Then the 57
   `if 4294967296 <= r { abort }` guards in L and most `HW`/`< 2^32` side conditions (`hx2l`,
   `hwvl`, `hwtl`, …) become `hS.hw _`. **~1–2k lines** and 57 L guards. Cost: medium (the intern
   proofs must establish it once per table).
6. **A generic "written record decodes" lemma for `wrER`/`set64` runs** (`decCV_shift` is a start):
   `decCI (erecP (wrER m q ws)) q = decodeList ws` when `q = erTop m`. **~80 lines per record kind**
   (DESIGN.md's measurement), perhaps 1–2k overall. Records (§4.2) give this for free.

## 4. What changes to L (or its tooling) would buy

### 4.1 Generate the word model and the L spec from the L AST (highest value; tooling, not semantics)

Everything in P1 and P2 follows from the `lfn` text. Straight-line code becomes a continuation chain
(one `fKᵢ` per call). A call becomes the callee's registered model, or `callW` if it has none.
`abort` becomes `none`, a loop becomes fuel recursion, and the guarded equations come from the
`if` structure. `scripts/inst1_from_lift.py` already does this as text generation for one family.
An `@[l_model]` attribute or `#l_model f` command elaborating `fW`, the `fKᵢ`, their
`_some`/guarded equations with `grind_pattern`s, and `f_spec` proved by the standard
`vcgen` + `finish` script would remove it all from the hand-written text.

* Samples: lift 550 of 1150 lines (48 %), whnf slot 90 of 410 (22 %), cons_sum_ctors 83 of 330
  (25 %), check_thm_val 66 of 200 (33 %).
* Project-wide estimate: **40–55k hand-written lines** (models ~19k, `_some`/patterns ~5k, guarded
  equations and specs ~20–30k).
* It also removes a class of bugs: a model that silently drifts from the L code (the spec catches
  this today, but only after a failing `finish`, which costs far more than a passing one).
* Cost: a metaprogram of ~1.5–2.5k lines over `Stmt` (the AST is small: 13 statement forms), and a
  convention for callee models (an attribute mapping a function name to its model and spec). Models
  that are deliberately abstracted (`memoSlotW`) can stay hand-written.

### 4.2 Adopt records and globals (they exist; adoption is ~0)

`L/Records.lean` (`fld_set64`) and globals (`closedG`, frames by construction) landed in lane
`lfeat`, but only 2 non-`L/` files use `Mem.fld`/`evalE_at` and 2 declare a `GVar`. Meanwhile the
code has 887 `CTL.u64[…]` accesses and 509 hand-computed `X.u64[i * k + t * j + o]` addresses. The
proofs carry 7113 `rdW (m.arr64 X) (…)` reads.

* Record layouts for `AREC`/`LAREC`/`LEREC`/`PJREC`/`BREC` (record `2i + t`), `EREC` constant
  records and `IW` slices would turn `rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)` into
  `m.fld LET (rid h) body`. `fld_set64` replaces `ciRec_stage`-style decoding.
* Globals for the store counts/tops (`CTL[22 + t]`, `CTL[42]`, `CTL[136]`, `CTL[137]`, …) give
  frames by construction, so the `MemFrame [98] [101]` lists and `StackKept` (326 uses) shrink.
* **Estimate: 3–6k lines**, more on new code. Cost: medium-high as a migration of existing tables
  (L text, models, `ArenaR` statements). It is cheap if done together with §4.1, because regenerated
  models absorb the change.

### 4.3 A tag `switch` with one verified `view`

Dispatchers hoist the scratch check and do one bound check per tag (`lift_go`, `inst_go`,
`raw_nat_lit`, `reduce_nat`, `whnf_core_step`, the walks: 330 `if g == k` arms). Two options:

* An L library function `expr_view(h)` returning `(tag, f0, f1, f2)` with **one** refinement against
  the twin's `view`.
* Surface syntax `switch tag(h) { app(f, a) => … }` that expands to it.

The twin's `match ← view h with` would then be mirrored 1:1, and each dispatcher's refinement would
be one `cases` on the decoded view instead of 10 × (`by_cases` tag, `by_cases` bound, dead branch,
`view_run`, guarded eq). In `lgoOK_succ` that is 135 → ~40 lines. **~3–4k lines** across the
dispatchers. Cost: low-medium (no semantics change; possibly one extra call per node at run time,
which a compiler `inline` could remove).

### 4.4 Structured slice loops instead of self-recursion

Lane `indproofs` turned ~20 `while` loops into self-recursion so the fuel induction mirrors the
twin's list recursion. That costs a call frame per element, which matters with ~3M-deep inputs.
`for x in IW[o .. o + l] { … }` as surface syntax over a counted `while`, with one library theorem
"a slice loop whose body refines `g` refines `List.forM`/`foldlM g`", would make the loop part of
`cscW_ok`-style proofs a single application. **~60–80 lines per loop**, roughly 2–3k over the inductive
stage. Cost: medium (the library theorem, a `DecB`-aware variant).

### 4.5 Smaller items

* **Declared result arity.** Calls returning `List Word` give models over `List Word × Mem` and
  `r.headD 0`/`r.tail.headD 0` in every post, plus `cscK3`-style "keep the first word"
  continuations. A function's declared arity (`lfn … returns 2`) would make models
  `Option (Word × Word × Mem)`. Small saving, broad.
* **Typed handle words** (a `u32` local class, or `decE` defined only on `< 2^32`). Same goal as
  §3.5, with a compiler/semantics cost. §3.5 is cheaper.
* **Memory model.** Per-function array write sets (`closedA`, `WriteSet.lean`) exist and are used in
  28 files. Making `Triple.frame` (callee spec + its text-derived write set) the standard way a
  caller gets a callee's frame, as `Triple.gframe` is for globals, would remove most `MemFrame`
  arguments in posts. This is a convention change, not a new memory model. A typed region memory is
  not needed.

## 5. A different proof architecture: one relation, footprints

P4 and P5 have one cause: each tier invented its own relation (`ArenaR` ⊂ `ArenaD` ⊂ `CoreS`;
`CheckR` ⊂ `StageR` ⊂ `LoopR`; `EnvR`, `DeclsR`, `FrontInv`), each a positional conjunction, and a
callee proved under one is unusable under another. A footprint discipline would fix it:

* every relation is a conjunction of **named components**, each with the arrays/globals it reads
  (`ArenaR`: the store tables; `PinsFull`: `PINS`; `EnvR`: `EIX*`, `EREC`; a memo: its schema's
  array and counters);
* a function's relational lemma is stated with **only the components it reads and writes**, plus
  its write set (from the text, `closedA`);
* one generic lemma per relation family transports it: the components outside the write set are
  kept by `frame`, and the result is the full `CoreS`/`StageR`/`LoopR`.

Then `nat_succ_ok`, `const_e` and the master callees are proved once and used by every tier.
`IndMaster`'s `_stage` lemmas, `DeclNatLit`, `DeclMasterStage` and the per-memo `set_*` lemmas go
away. DESIGN.md records two cross-lane blockers of this kind (`StageX`/`TwinOK` inside `StageR`, and
the 35 files touched by `StageR`'s anonymous constructor). Named-component relations make adding a
component a non-breaking change. **Estimate: 5–8k lines now**, and it stops the growth of
duplicates. Cost: medium-high, a coordinated restatement of the relations; do it per tier.

## 6. Ranked recommendations

Score = (estimated savings × breadth) / cost; breadth = fraction of functions affected.

| # | recommendation | est. savings | breadth | cost | notes |
|---|---|---:|---|---|---|
| 1 | **Generate `fW`, `fKᵢ`, `_some`/guarded equations, `grind_pattern`s and the `vcgen` spec from the `lfn` AST** (§4.1) | 40–55k lines (25–45 % per function) | every function | medium (1.5–2.5k lines of meta code) | removes P1+P2; makes §4.2/§4.3 migrations cheap |
| 2 | **`Sim` as the standard relational form**: callee facts as `Sim …`, relational lemmas as `Sim.bindK` chains (§3.1) | 8–12k | every caller of a callee | low (library exists; restate callee lemmas) | removes most of P3 and the dead branches; start with new code |
| 3 | **Program-lookup bundles from the text** via a `wfFast`-style decided `ProgHas` (§3.4) | 3–4k | every file | low | P7: 4801 lookup lines |
| 4 | **Footprint-based relations, one refinement per function** (§5, with §3.3) | 5–8k + stops duplication | core, stage, loop tiers | medium-high | fixes P4/P5 and the open `StageX`/`TwinOK` blockers |
| 5 | **Tag `switch` over one verified `expr_view`, then records/globals for the tables** (§4.3, §4.2) | 6–10k | walks, whnf, infer, defeq, inductives | medium (low after #1) | P6/P10; records already exist in L |

Cheap side items worth doing anyway:
* `exec_mono` instead of `UpTo` (~1k lines, low cost).
* Handle bounds as a relation invariant (§3.5, ~1–2k lines).
* Correct the DESIGN.md ratio: report the all-in figure (model + spec + refinement) next to the
  refinement-only figure, so lanes compare like with like.
