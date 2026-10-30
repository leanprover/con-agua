# Lane refgen: a pilot of the refinement generator (lnext2 §2, rank 2)

Question: can the model ⊑ twin `RefE` proofs be generated as a lockstep walk? The walk would
step the model's continuations and the twin's `do` block together, dispatch each callee to a
registered refinement, and close the remaining semantic goals with `grind`. lnext2 counted the
refinement layer at 108 k lines (36 % of proof lines), with ≥ 27 % of the `RefE` lines being
plumbing. It hoped for −10 to −12 k lines. Go if the pilot functions lose ≥ 40 % of their lines
and no module gets slower.

Base: master 28f9c0b6. **Only this journal landed.** The pilot is
`_tmp/refgen/pilot.patch` (the kit `ConAgua/Arena/RefWalk.lean`, the sum family's steps
`ConAgua/Arena/IndT/SumSteps.lean`, `ctl_ref` and `ctor_ref` rewritten in `Arena/IndT/Sum4.lean`,
statements unchanged). It also includes `_tmp/refgen/pp_ref2.lean` (`pp_ref`, `DefEqStuckProj`,
redone with the kit) and the counting scripts `_tmp/refgen/reflen.py` and `ncl.py`. All of it
builds against 28f9c0b6.

**Answer in short.**

* The walk works. Each step of today's walk becomes one `refine` against one rule of a small
  kit. The pilot theorems shrink by **−62 %** (`ctl_ref` 314 → 103 lines, `ctor_ref` 250 → 110)
  and `pp_ref` by **−39 %** (77 → 47). The converted module is **faster**: Sum4's elaboration
  work goes from 4.20 s to 3.38 s, plus 0.30 s for the new steps file.
* **The per-call plumbing does not go away. It moves into one step lemma per (callee, invariant
  package).** In the walk that lemma is about as long as the plumbing it replaces at a single
  call site. The RefE files call 178 distinct callees at 317 call sites (1.8 sites per callee,
  129 callees with one site), and the packages differ by family. So the step lemmas barely
  amortize. Counted with the steps it needs, the pilot module goes from 655 to 541 code lines
  (**−17 %**), or −5 % with the kit.
* **A real generator** (the walk driven from a registry, preconditions closed by `grind`) pays
  for every transport goal. A `decHL` transport across four steps took `grind` about 0.5 s, where
  the explicit term costs nothing. There are 300+ call sites.
* **Verdict: no-go for the generator as lnext2 scoped it.** Rolled out, the realistic gain is
  **−4 to −6 k lines** for 70–110 h, not −10 to −12 k. The kit alone is a small win, and it is
  optional (§5).

## 1. How today's `RefE` proofs walk

Read in `ctl_ref` / `ctor_ref` (`Arena/IndT/Sum4.lean`), `pp_ref` (`DefEqStuckProj.lean`) and
`inferConst_ref` (`InferLeaves.lean`). The model `fE` is a chain of continuations: `fE.arm1`
gives `K₁ (liftE (callW p n "f₁" args m))`, and each `Kᵢ` is a `match` on the callee's outcome
followed by the arm's guards and the next call. `fE.k_f.none`, `.abortN` and `.armN` are its
guarded equations. The twin is a `do` block, unfolded once (`unfold cscTailT`, or a
`checkSumCtor_eq` by `rfl`). Per callee outside the verdict closure (lifted), today's proofs
write:

| piece | lines |
|---|---:|
| split the model: `rcases h : callW …`, `liftE_none`, `K.none`, `RefE.of_cls0`, `liftE_some`, `K.arm1` | 4–5 |
| the callee's L triple: `triple_of_callW (f_spec …)`, `subst` | 2–3 |
| its word model against the twin (`fooSim`, `sumSim_of_relW (foo_ok …)`, `RelW`) | 1–2 |
| `AbsOK` after it (`foo_afr`, `AFr.of_frame`) | 1 |
| con-ron's bridge lemma on the run (`*_run`, `*_spec`: `PStep` and denotations) | 2–3 |
| thread the package: `StageC.of_pstep`, and later `hg₁.trans hg₂`, `p₁.ext.trans p₂.ext`, `hp.toCore` | 1–3 |
| `RefE.bind_right hrun` | 1 |
| per abort guard: `by_cases`, `K.abort1`/`arm1` with all its arguments, `cases o`, `absurd`, `simp only [unwrapOr]`, `RefE.bind_left … ErrClaim.fail` | 6–10 |

What the user has to supply in any scheme: the statement (relation, `R` as a named-field
structure, `G`), the twin-side bridge facts (denotations, `WScoped`), and the transports of
decoded facts to later states (`decHL_grow`, `denote*_ext`).

## 2. Design

### 2.1 The kit (`Arena/RefWalk.lean`, 82 code lines, generic)

One rule per pair of shapes. Each covers both outcomes, so no rule leaves a `none` arm or an
error arm behind:

* `RefE.bindSim (hK : ∀ e, K (.error e) = .error e) (h1 : Sim c op a Q) (h2 : ∀ r x m₁ a₁, op.run a = .ok (x, a₁) → Q r x m₁ a₁ → RefE G (K (.ok (r, m₁))) (g x) a₁ R) : RefE G (K (liftE c)) (op >>= g) a R`
  handles a lifted callee by its `Sim`, its "registered refinement". `hK` is `fun _ => rfl` for
  every generated continuation. This replaces the split, the `none` arm and `bind_right`.
* `RefE.bindE` / `RefE.lastE` take a unified callee's own `RefE`, then the rest, or as the twin's
  last statement. `RefE.onlySim` handles an L helper the twin has no step for (`sl_eq`).
* The guards:
  * `RefE.guard` is a model abort against the twin's `unless b do fail ce`, whose do-elaboration
    is `if b = true then jp () else fail ce >>= jp`. It takes `c → b = false`, `b = false → c`
    and the class equation (`by decide`).
  * `RefE.guardOpt` is the same against `unwrapOr o ce >>= g`.
  * `RefE.abort0` is a guard of the model alone with a class-0 abort (a range or capacity check).
  * `RefE.twinFail` / `twinPass` cover a twin guard that L checks in pieces.
* `walk_k K` is `dsimp only [K]`, which unfolds the continuation at the head to its arm. It is a
  macro, not a search tactic (PLAN.md's "no custom tactics").

### 2.2 The family's package and its steps (`Arena/IndT/SumSteps.lean`, 229 code lines)

`SumAt dn vis fe env m₀ a₀ m a` is the walk's package from `(m₀, a₀)` to `(m, a)`. Its named
fields are `stage : StageC …`, `abs : AbsOK m`, `grow : IWGrow m₀ m` and
`core : CoreStep V env fe a₀ a`. It comes with `refl`, `trans`, `pstep` (from a con-ron
`PStep`) and the transports `decHL` and `top`. A step is
`foo_step (hk : SumAt … m₀ a₀ m a) (pre…) : Sim (callW p n "foo" args m) twinFoo a (fun r x m' a' => SumAt … m a m' a' ∧ facts)`.
The facts are the result decoded against the twin's (an abort flag as an iff, `r.headD 0 = 0 ↔ o = none`)
and denoting con-leche's. Each step proof is today's plumbing for that callee, written once:
`triple_of_callW`, the `Sim`/`RelW` lemma, `AFr`, the bridge lemma and `SumAt.pstep`. The pilot has 11
steps: `opf`, `pl`, `ic`, `gaf`, `gaa`, `slEq`, `fdr`, `iar`, `strip`, `sr` and `ftds`.

A call site is then:

```lean
refine RefE.bindSim (fun _ => rfl) (fdr_step hP k5 (k15.decHL hxl hxlb) (k15.top hxlb)
  (hok₀.mono k05.core.ext) hxfvs5) fun r7 b1 m7 a7 _ ⟨k7, hb1⟩ => ?_
walk_k ctlE.k_field_doms_resolve
refine RefE.guard (by decide) hb1.1 hb1.2 fun _ hb => ?_
```

Threading shrinks to `kᵢ.trans kⱼ`. Each local `kᵢ : SumAt mᵢ₋₁ aᵢ₋₁ mᵢ aᵢ` carries the stage,
`AbsOK`, the growth and the core step at once. The final post's `grow` and `core` are one
`k08.grow.trans …` and `k08.core.trans …`.

### 2.3 What stays by hand, and where `grind` helps

* **Guards whose L and twin conditions differ.** `ctl_ref`'s residual guard is one example. The
  twin checks `xfn == hd && take == cq1 && length == nP + nIdx`. L checks `nP ≤ al`, calls
  `sl_eq`, then checks three flags. After `rw [decI_beq …]`, a plain `grind` closes both
  implications (about 100 ms each). Before, they took ~45 hand lines (`hb3`, `hfalse`, `htrue`).
  This is the pilot's best use of `grind`.
* **Transports** of a decoded fact or a denotation to a later state (`k15.decHL hxl hxlb`,
  `denote_ext h kᵢⱼ.core.ext`). The pilot keeps them as terms. `grind [SumAt.trans, SumAt.decHL]`
  closes them but costs about 0.5 s per site (measured on one `decHL` across four steps). This is
  what blocks automation (§4).
* **Unified callees' extra facts** (`ccv_ref`, `sds_ref`, `fsorts_ref`). Their posts do not
  carry con-ron's core step, so the walk calls the bridge on the run that `bindE` hands over
  (`checkConstantVal_bridge`, `checkStructDomsAt_spec`, `checkStructFieldSortsI_spec`), with
  their `WScoped` side facts.
* **Fuel splits** (`rcases m with _ | m'` before a unified callee at `n + 1`) and the final
  `RefE.ret` / post structure.

## 3. Pilot numbers

Lines per theorem (`_tmp/refgen/reflen.py`: from `theorem` to the next declaration, statement
included). Code lines per file (`ncl.py`: no comments, no blanks).

| function | family | today | walk | change |
|---|---|---:|---:|---:|
| `ctl_ref` (`check_sum_ctor_tail`) | `StageC`, 8 lifted callees + 1 unified | 314 | 103 | −67 % |
| `ctor_ref` (`check_sum_ctor`) | `StageC`, 5 lifted + 3 unified | 250 | 110 | −56 % |
| `pp_ref` (`defeq_proj_pair`, a `defeq` helper) | `CoreS`, guards + a tail call | 77 | 47 | −39 % |

| file (code lines) | today | pilot |
|---|---:|---:|
| `Arena/IndT/Sum4.lean` | 655 | 312 |
| `Arena/IndT/SumSteps.lean` (new: the family's steps) | — | 229 |
| Sum4 + its steps | 655 | **541 (−17 %)** |
| `Arena/RefWalk.lean` (new: the kit, shared by every family) | — | 82 |

Elaboration, median of 3 interleaved runs. "Work" is the profiler's sum of tactic execution,
type checking, elaboration, simp, interpretation and the rest, with imports left out. "Wall" is
`lake env lean` on the file, imports included (~0.6 s):

| file | today work | pilot work | today wall | pilot wall |
|---|---:|---:|---:|---:|
| `Sum4` | 4.20 s | 3.38 s | 5.58 s | 5.44 s |
| `SumSteps` (new) | — | 0.30 s | — | 0.91 s |
| `pp_ref` alone (`profiler`, same categories) | 115 ms | 137 ms | | |

In Sum4, `simp`/`rw` with long argument lists (`K.abort1 p m vis0 …`) leave the walk.
Tactic execution drops from 951 ms to 569 ms. `grind` rises from 484 ms to 749 ms (three
guard calls). Sum4 plus its steps is 12 % less work. `pp_ref` is +20 ms: two `simp_all` for
guards that were `rw`s. A first version with `grind` there was +60 ms.

## 4. Why not the generator

1. **The registry costs what it saves.** Today a lifted call costs 12–15 lines at its call
   site. Its step lemma is 15–25 lines: a long post, decoded facts and denotations. Over the
   `RefE` files, 178 callees are split by `rcases` at 317 sites (1.8 per callee, 129 with one
   site), and a step is per (callee, package): `StageC` vs `StageR` + `IWGrow` vs `CoreS` vs the
   memo packages. In the sum family the 11 steps would have 0–3 further users each (`opf` 3,
   `strip` 2, `ic` 2, `gaf` / `gaa` / `ftds` 1, the rest 0). What is truly generic, the walk
   rules, is 82 lines once. The rest is the plumbing, moved.
2. **The steps are not generable from what is registered today.** A step composes four facts
   with a different shape per callee:
   * the L triple (`LocEq ∧ W m args = some (r, s'.mem)`, or `some (r.headD 0, …)` with an
     extra `s'.mem = s₀.mem`);
   * the word model against the twin (`Sim` vs `RelW` vs an `_ok` lemma with its own argument
     order);
   * `AFr` (`foo_afr`, `AFr.of_frame (foo_frame …)`);
   * the bridge (`PSpec` with a store precondition, `*_run` with a state equation, `PSpecP`
     with pins, or `ReadOK` with the restricted environment).

   Normalizing them is one adapter per callee, the same lines again.
3. **Automating the walk means `grind` on transports.** The walk's remaining arguments are
   mostly transports (§2.3). Closing them by `grind` costs ~0.5 s per site, minutes over the
   rollout, against zero for the explicit terms. Leaving them explicit gives lines like the
   pilot's.
4. **Where L and the twin are not in lockstep, the walk still needs hand guards.** That
   happens where L split a twin guard (`ctl_ref`'s residual) or the twin's shape differs (in
   `inferConst_ref` the twin is rewritten per branch by `inferConstT_run`, and `pp_ref` goes
   through `pp_both` / `RefE.of_run_eq`). `grind` closed `ctl_ref`'s guard well. That is a
   finding for the kit, not for generation.

## 5. Rollout estimate, and what to do instead

* **Generator (lnext2's plan):** 30–50 h for the generator and 40–60 h for steps over the
  families. Gain **−4 to −6 k lines**: the pilot's −17 % net on the plumbing-heavy half of the
  ~26.7 k `RefE` lines (321 theorems by `reflen.py`), about −2.3 k, plus −15 to −30 % on the
  guard-heavy core half (`pp_ref` is a favourable case), −2 to −4 k. The cost is ~100 ms per `grind` guard and possibly transports. Not worth it, and below
  lnext2's −10 to −12 k.
* **The kit alone, applied when a file is touched anyway** (con-ron syncs, migrations):
  * land `RefWalk.lean`. Its rules `guard`, `guardOpt`, `abort0`, `bindSim` and `bindE` remove
    the `none` arms, the `K.abortN`/`armN` rewrites with their argument lists, and
    `bind_right`;
  * a family package such as `SumAt` replaces the threading;
  * write steps only for callees with ≥ 2 sites in that package.

  Expect −15 to −20 % per converted file at no time cost (Sum4: −17 %, 12 % less work). It
  applies as `_tmp/refgen/pilot.patch` against 28f9c0b6. It is not landed, because the go
  criterion counted with its steps is not met.
* lnext2 should drop rank 2 or demote it to "kit when touching". Rank 3 and lower are not
  affected.
