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

## 6. Migration recipe (lane refwalk1)

Landed: the kit `ConAgua/Arena/RefWalk.lean`, the pilot's sum family (`IndT/SumSteps.lean`,
`ctl_ref`/`ctor_ref` in `IndT/Sum4.lean`) and the whole `RecGen` family in two packages: the
`target_major_of` functions (`TmAt`: `IndT/RecGenTmf.lean`'s `tmt_ref`, `tmo_ref`, `tmc_ref`,
`tmf_ref`; `clm_ref` in `RecGen19.lean`, `cbc_ref` in `RecGen21.lean`) and the class functions
(`RcAt`, `RecGen23.lean`: `cnaLoop_ref`; `RecGen24.lean`: `cfaLoop_ref` and the step `tma_step`;
`RecGen27.lean`: `cxo_ref`, `cosLoop_ref`, `ccsLoop_ref`; `RecGen28.lean`: `cns_ref`). Statements
unchanged. The pilot's `walk_k` macro is gone (PLAN.md:
no custom tactics); write `dsimp only [K]`. Follow this section verbatim for the next family.

### 6.1 The shape of a converted theorem

```lean
theorem f_ref … (hC : StageC dn vis fe env m a) (hA : AbsOK m) … :
    RefE G (fE p n m …) (twinF …) a (fun v x a' => FPost …) := by
  cases n with
  | zero => rw [fE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n =>
  rw [fE.arm1]; unfold twinF                     -- or `rw [twinF_eq]` (an `rfl` lemma)
  -- a lifted callee WITH a step lemma (≥ 2 call sites under this package); the `_`s are the
  -- call's equation (`callW … = some (r1, m1)`, for `callW_keepW`) and the twin's run
  refine RefE.bindSim (fun _ => rfl) (g_step hP k0 …) fun r1 x1 m1 a1 _ _ ⟨k1, hx1⟩ => ?_
  dsimp only [fE.k_g]
  -- a lifted callee WITHOUT a step lemma: its plumbing stays at the call site
  refine RefE.bindLift (fun _ => rfl) fun r2 m2 h2 => ?_
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩) (h_spec p …) h2
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := hSim … hW2 k1.stage.stage   -- the `Sim`/`RelW`/`_ok`
  obtain ⟨p2, hP2⟩ := ConRon.Bridge.Inductives.h_run k1.stage.check.state … hrun2
  have k2 := FamAt.pstep k1.stage hS2 (h_afr hW2 k1.abs) hg2 … p2
  refine ⟨_, _, hrun2, ?_⟩
  dsimp only [fE.k_h]
  -- a guard: model `if c then .error e else rest` against the twin's check
  refine RefE.guard (by decide) (fun hc => …) (fun hb => …) fun _ _ => ?_
  -- a unified callee (its own `RefE`), `G → G'` as the second argument
  refine RefE.bindE (fun _ => rfl) (fun hV => hV.nv) (u_ref … k2.stage k2.abs …)
    fun ⟨r3, m3⟩ y a3 hrun3 hR3 => ?_
  dsimp only [fE.k_u]
  -- a unified callee read through its call (`K (callE …)`): its model spec, its `RefE`
  refine RefE.bindRun (s₀ := ⟨m3, Locals.init []⟩) (fun _ => rfl) (uE_spec p … ⟨m3, Locals.init []⟩ …)
    (fun hG => hG.nv) id (u2_ref …) fun r4 s4 z a4 h4 _ hrun4 ⟨hS4, hg4, …⟩ => ?_
  dsimp only [fE.k_u2] at hS4 hg4 ⊢
  …
  exact RefE.ret rfl ⟨…, (k1.trans k2).grow.trans hR3.grow, …⟩
```

Which rule for which pair of shapes:

| model | twin | rule |
|---|---|---|
| `K (liftE c)`, a step lemma `Sim c op a Q` | `op >>= g` | `RefE.bindSim` |
| `K (liftE c)`, one call site | `op >>= g` | `RefE.bindLift`, then `⟨_, _, hrun, ?_⟩` |
| `K (liftE c)` | no step (an L helper, `sl_find`, `sl_cons`, a record writer) | `RefE.onlySim (fun _ => rfl) (fun _ _ h => h)` |
| `K x`, a unified callee | `op >>= g` / `op` last | `RefE.bindE` / `RefE.lastE` |
| `K (callE p n f args s₀.mem)`, a unified callee through its spec | `op >>= g` | `RefE.bindRun` (pass `s₀`) |
| `K (callE p n f args m)`, a knot callee (`whnf_top`, `infer_type_core`): its error a claim of `G`, its ok an `RSim` | `op >>= g` | `RefE.bindCall` |
| `if c then .error e else rest` | `if b = true then jp () else fail ce >>= jp` (`unless`) | `RefE.guard` |
| same | `if b = true then T else fail ce` / `if b = true then fail ce else T` | `RefE.guardIf` / `RefE.guardThen` |
| same | `unwrapOr o ce >>= g` | `RefE.guardOpt` |
| same, class `0` (a capacity, a range) | nothing | `RefE.abort0` |
| same, already decided by a `cases` (the twin's `match` on the callee's `Option`) | `fail ce` / the arm | `RefE.abortAt` / `RefE.pass` |
| `.error e` / `x` | a twin guard L checks in pieces | `RefE.twinFail` / `RefE.twinPass` |

### 6.2 The package

One structure per family, named fields, from `(m₀, a₀)` to `(m, a)`: the stage (`StageC`), `AbsOK`,
the `IW` growth and whatever else the family threads (`PosMR` for `TmAt`; the core step for
`SumAt`, the store's `Ext` for `TmAt`). Give it `trans`, a constructor from con-ron's step
(`pstep`: `StageC.of_pstep` inside), and the transports the family uses more than once (`decHL`,
`top`). It goes in the family's lowest file (`SumSteps.lean`, `RecGenTmf.lean`). Each call site
then threads one `kᵢ`; the final post takes `(k1.trans k2).grow`, `kᵢ.pos`, `kᵢ.abs`.

### 6.3 When to write a step lemma

Count the call sites of each lifted callee under the same package (grep the family's files for
`"callee"`). Two or more: a step `g_step (hk : FamAt … m₀ a₀ m a) … : Sim (callW p n "g" args m)
twinG a (fun r x m' a' => FamAt … m a m' a' ∧ decoded facts)`, proved once by the call site's
plumbing (`tma_step` in `RecGen24.lean`: `cfaLoop_ref` and `cxo_ref`; a twin argument that is a
`Nat` the caller has as `c.toNat` goes in as `(ht : c.toNat = t)`). One: `bindLift` with the
plumbing inline (5–8 lines). In the `target_major_of` family no lifted callee has two sites under
`TmAt`, so it has no steps. Over the whole `RecGen` family only `target_major_at` has two sites
under one package (`RcAt`); refgen §4's "1.8 sites per callee" holds here too, so expect a family
to need zero to two steps.

### 6.4 Pitfalls

* **Irreducible continuations.** The model of a recursive function (`clmE`: a mutual
  definition) has `@[irreducible]` continuations, so `fun _ => rfl` and `dsimp only [K]` fail
  ("type mismatch `rfl`"). Use `(fun _ => K.none ..)` for `hK`, `rw [K.arm1]` for an unguarded arm,
  and for a guard `RefE.ofArms (fun h => K.abort1 (hc1 := h) ..) (fun h => K.arm1 (hc1 := h) ..)
  (RefE.abort0 …)` (the guard hypotheses of the generated equations are named `hc1`, `hc2`, …;
  `..` fills the rest, it must come last).
* **`rw [ite_eq_left …]` after `dsimp only [K, List.headD_cons]` fails** ("did not find
  pattern"): `dsimp` rewrites the condition but not its `Decidable` instance. Use the rules
  (`RefE.abortAt`, `RefE.pass`, `RefE.guard…`), which unify up to defeq, instead of `rw`.
* **`fun ⟨…, -⟩ => ?_` does not parse**; a `refine`'s `fun` pattern takes `_`.
* **Keep the `simp only at hS hg hd hA`** after `triple_of_callW` where its post mentions
  `{ mem := m, loc := … }.mem`: `omega` takes the unreduced term for another atom (cbc_ref).
* **Guard conditions.** Write the two implications as terms when short (`Bool.eq_false_iff`,
  `beq_iff_eq`, `hgood.symm.trans (by rw [hz]; rfl)`); `by grind` closes the flag-vs-Bool ones
  (`(r.headD 0 != 0) = b`) at no measurable cost here. No `simp_all`.
* `RefE.bindE`'s second argument is `id` when the callee's `G` is the caller's, `fun hV => hV.nv`
  from `VerdictCtx` to `closedNV`.
* **`RefE.bindRun` infers `s₀` from `callE … s₀.mem` as the state of the goal**, not the spec's
  `⟨m, Locals.init []⟩`; pass `(s₀ := ⟨m, Locals.init []⟩)`. A twin argument the caller rewrote
  (`rw [hnpT] at h`) is rewritten in the callee's `RefE` before the rule (`rw [hnpT] at hR3`).
* **A post with pair projections** (`(r, s'.mem).1`, a model value `⟨b, m2⟩.2`) after
  `bindE`/`bindRun` needs `dsimp only at h…` before `omega` (`cnaLoop_ref`, `ccsLoop_ref`).
* **`obtain ⟨rfl, …⟩` on a twin run's `s' = s₀`** eliminates the earlier state name, which
  later lines still use; write `obtain ⟨e, …⟩ := …; subst a1` (the later name).
* **A continuation decided by a `cases` of the callee's decoded result** (`rcases ox with _ | …`):
  `rw [K.abort1 (hc1 := hd)]` / `rw [K.arm1 (hc1 := by …)]` with the named hypothesis, no
  argument list.

### 6.5 Numbers (refwalk1)

Lines per theorem (`reflen.py`) and code lines per file (`ncl.py`), against master 9948b019;
elaboration `lake env lean` on the file, median of 3 interleaved runs (load 15–30):

| theorem | before | after |
|---|---:|---:|
| `tmf_ref` | 81 | 60 |
| `tmc_ref` | 86 | 78 |
| `tmo_ref` | 168 | 127 |
| `tmt_ref` | 106 | 79 |
| `clm_ref` | 161 | 131 |
| `cbc_ref` | 174 | 135 |
| `cnaLoop_ref` | 141 | 119 |
| `cfaLoop_ref` | 226 | 192 |
| `cxo_ref` | 303 | 241 |
| `cosLoop_ref` | 124 | 113 |
| `ccsLoop_ref` | 159 | 147 |
| `cns_ref` | 254 | 241 |
| the four wrappers (`cna_ref`, `cfa_ref`, `cos_ref`, `ccs_ref`) | 149 | 149 |
| **`RecGen` family** | 2132 | 1812 (**−15 %**) |

| file (code lines) | before | after | wall before → after | max RSS |
|---|---:|---:|---:|---:|
| `IndT/Sum4.lean` | 655 | 312 | 6.45 → 5.94 s | 2.94 → 2.94 GB |
| `IndT/SumSteps.lean` (new) | — | 229 | | |
| `IndT/RecGenTmf.lean` (with `TmAt`, 38 lines) | 510 | 437 | 1.61 → 1.57 s | 2.75 → 2.74 GB |
| `IndT/RecGen19.lean` | 222 | 192 | 1.58 → 1.49 s | 2.72 → 2.72 GB |
| `IndT/RecGen21.lean` | 243 | 204 | 2.07 → 2.00 s | 2.80 → 2.79 GB |
| `IndT/RecGen23.lean` (with `RcAt`, 33 lines) | 238 | 238 | 2.65 → 2.52 s | 2.83 → 2.83 GB |
| `IndT/RecGen24.lean` (with `tma_step`, 17 lines) | 335 | 319 | 3.35 → 3.44 s | 2.93 → 2.92 GB |
| `IndT/RecGen27.lean` | 895 | 810 | 2.47 → 2.40 s | 2.92 → 2.92 GB |
| `IndT/RecGen28.lean` | 280 | 268 | 3.47 → 3.20 s | 3.03 → 3.03 GB |
| `RefWalk.lean` (new, shared) | — | 130 | | |

The `RecGen` family: 2723 → 2468 code lines (**−9.4 %** with its two packages and its step), time
and memory unchanged (each file elaborates in 1–3 s past its imports). The sum family: 655 → 541
(−17 %, refgen §3). So the `RefE` theorems lose 15–20 % and a converted file 9–17 %, the low end
where the plumbing is mostly unified callees and loops (`cns_ref`, the class loops), the high end
where it is lifted callees with guards (`tmo_ref`, `cxo_ref`, `ctl_ref`).

### 6.6 Next families

By `reflen.py` lines (master after this lane), lifted-call density first:

* ~~`IndT/Install*`~~: done (refwalk3, §6.8).
* ~~One package for the sum and install families~~, ~~the remaining wrapper `Sim`s~~: done
  (refwalk5, §6.9).
* ~~`IndT/Sum1–3`~~: done (refwalk2, §6.7).
* ~~The knot callers~~ (the 11 files of §6.7, and `DeclAxQuotT`): done (refwalk4, §6.10).
* ~~`IndT/Positivity`, `PosCrest`, `Tail`, `Pass`, `Block`, `CheckIndDecl`~~: done (refwalk5,
  §6.9).
* **`Verdict/IndB*` and the declaration arms**: `IndBHdr`, `IndBTpd`, `IndBRec2`, `IndBRec4` and
  the `Decl*T` gates done (refwalk4, §6.10); the other `IndB*` files not looked at.

### 6.7 Sum1–3 (lane refwalk2)

Converted: `wt_ref` (`Sum1.lean`), `cts_ref`, `ct_ref` (`Sum2.lean`), `cfb_ref`, `csfGo_ref`,
`fsorts_ref` (`Sum3.lean`). Statements unchanged. New kit rule `RefE.bindCall` (a knot callee read
through its call: `whnf_top` in `wt_ref`, `infer_type_core` and `ensure_sort_core` in `csfGo_ref`;
11 other files have the same `rcases … callE … "whnf_top"/"infer_type_core"/…` split: `Install1`
(done, refwalk3: `idc_ref`, §6.8),
`RecCheckPins`, `DeclCrpT`, `DeclNatGateT`, `DeclDivGateT2`, `Verdict/DeclValE`, `DeclValsE`,
`IndBHdr`, `IndBTpd`, `IndBRec2`, `IndBRec4`).

**No package and no steps.** §6.6 expected `SumAt` and the pilot's steps to apply; they do not. The
further sites of `opf`, `strip` and `ic` are in `Install3`/`Install6`, not here, and every lifted
callee of Sum1–3 has one call site (`intern_fvar`, `instantiate1_fast`, `sl_cons`, `intern_sort`,
`close_telescope`, `cv_new`, `strip_pis`, `lv_leq_top`, `pin_word`, `lvl_eq_true`, `sl_contains`,
`sl_get`, `fvar_type_d`, `iw_alloc`). The posts carry no core step (only `csfGo_ref` composes two
`CoreStep.ext`s), so `SumAt`'s `core` would be dead weight, and the threading is short. The
conversion is the rules alone: `bindLift`/`bindSim` (a `Sim` that is not a step, such as
`sumSim_of_relW (ftdF_ok …)`, goes into `bindSim` directly), `onlySim`, `bindE`/`lastE`, `bindCall`,
`abort0`, `ofArms`, `abortAt`/`pass`, `guardIf`.

Pitfalls (add to §6.4):

* **`RefE.lastE (fun _ => rfl) (fun _ => rfl) …` can unify `K` with `Except.ok`** when the model is
  `K (callee …)` of a continuation applied to arguments (`fsortsE.k_… p nW res`, `ctE.k_… p`):
  "type mismatch `rfl` … `Except.ok (Except.error e) = Except.error e`". Name it:
  `RefE.lastE (K := fsortsE.k_check_struct_field_sorts_i_go p nW res) …`.
* **`RefE.onlySim`'s `Q` is not inferred from an anonymous constructor** (`fun r m h => ⟨…, …⟩`):
  pass `(fun _ _ h => h)` and destructure in the rest.
* **`bindLift` takes the twin's run before the model's guard**: for a class-`0` guard after the
  callee (`4294967296 ≤ fv`), give `⟨_, _, hrun, ?_⟩` first, then `RefE.abort0` (or
  `RefE.ofArms … (RefE.abort0 …)` for a recursive model).
* **Rewrite the goal, not the claims**: where a knot claim or an `RSim` states the twin at
  `(nP + (j - 1)).toNat` and `decI (rt.headD 0)` and the goal at `nP.toNat + J` and `t`, a
  `rw [← hdep]` and `subst ht` on the goal before the rule let `bindCall` take
  `hV.core.inferTypeCore …` and `inferC_rsim …` as they are (no `rwa … at this`).
* **`subst a1` for a run that leaves the twin state (`ha1 : a1 = a`)**: `subst ha1` eliminates
  `a` instead, which the rest of the proof still names.
* **A three-way decoded result** (`decLvlEq`: `0`/`1`/`2` for `none`/`some false`/`some true`):
  `rcases x with _ | _ | _ <;> simp only [decLvlEq] at hx`, then `RefE.abortAt`/`RefE.pass` per
  case with `by rw [hx]; decide`.
* **`grind` on a guard over `List.contains`** got lost in `List.contains_append` instances (1000
  instances, failed). State the two flags as iffs first (`rq.headD 0 = 0 ↔ x ≠ some true`,
  `r3.headD 0 = 0 ↔ ws.contains fv = false`) and close the implications with `rw` and `simpa`.

Numbers, against master 28b855fc (`reflen.py`, `ncl.py`; elaboration `lake env lean` on the file,
median of 3 interleaved runs, load 12–14):

| theorem | before | after |
|---|---:|---:|
| `wt_ref` | 135 | 121 |
| `cts_ref` | 120 | 106 |
| `ct_ref` | 108 | 104 |
| `cfb_ref` | 151 | 96 |
| `csfGo_ref` | 153 | 126 |
| `fsorts_ref` | 29 | 23 |
| **Sum1–3** | 696 | 576 (**−17 %**) |

| file (code lines) | before | after | wall before → after | max RSS |
|---|---:|---:|---:|---:|
| `IndT/Sum1.lean` | 205 | 192 | 3.60 → 3.92 s | 2.46 → 2.46 GB |
| `IndT/Sum2.lean` | 374 | 357 | 2.63 → 2.40 s | 2.60 → 2.59 GB |
| `IndT/Sum3.lean` | 505 | 415 | 2.96 → 3.05 s | 2.58 → 2.59 GB |
| `RefWalk.lean` (`bindCall`) | 130 | 142 | | |

Sum1–3: 1084 → 964 code lines (**−11 %**), time and memory unchanged (Sum1's +0.3 s is noise: the
profiler's categories agree within 0.1 s, and most of the file is `wtE`'s `l_model`). The gain sits
where the twin and L walk in lockstep with guards (`cfb_ref` −36 %, `csfGo_ref` −18 %); `ct_ref`
(−4 %) is mostly the twin's own branches on `strip_pis`'s result and the view, which no rule
covers.

### 6.8 Install1, 3, 4, 6, 7 (lane refwalk3)

Converted: `cbda_ref`, `sds_ref` (`Install1.lean`), `cbt_ref`, `cbts_ref` (`Install3.lean`),
`cbi_ref` (`Install4.lean`), `iao_ref`, `iac_ref`, `iaa_ref` (`Install6.lean`), `icbo_ref`,
`icbg_ref`, `ict_ref` (`Install7.lean`). Statements unchanged. New kit rule `RefE.callE_zero`.

**One package, three steps**, all in `Install1.lean` (the family's lowest file; `Install3` now
imports it):

* `InsAt` (stage, `AbsOK`, growth, core step; `refl`, `trans`, `pstep`, `cstep`, `decHL`): the same
  fields as `SumAt`, which lives in `SumSteps.lean`, above `Install1`–`6`. One package for both
  families is a move of `SumAt` down to `Install1` (or `Lift.lean`) and a rename; not done here,
  since `SumSteps` was the sum lane's file.
* `ftd_step` (`fvar_type_d`, two sites: `cbda_ref`, `sds_ref`), `slGet_step` (`sl_get`, an L helper
  for `onlySim`: two sites in `sds_ref`), and `idc_ref` (`is_def_eq_core` as a unified callee's
  `RefE`, its error by `CoreStubsE`, its ok run by `isDefEqC_rsim`; two sites) taken by `bindE`.
  For one site `RefE.bindCall` (§6.7) does the same inline.
* `open_pis_at_fvars_f` and `strip_pis` have one site each under `InsAt` (`iao_ref`, `cbt_ref`):
  `bindLift`. The sum steps `opf_step`/`strip_step` are stated over `SumAt`.

**`bindRun` retires the wrapper `Sim`s.** The unified callees read through their run
(`check_constant_val`, `check_sum_tele`, `check_struct_field_sorts_i`, `check_sum_ctors`) were
split twice: the error by `RefE.run_err` and the callee's `RefE`, the ok run by a hand `Sim`
around the same `RefE` (`installCstSimC`, `installSimSumCtorsC`, `installSimFsortsC`) or by a
second triple (`checkConstantVal_refinesT`). `bindRun` takes the callee's `RefE` once for both;
its post (`CcvPost`, `CtsPost`, `FsortsPost`, `SctsPost`) has what the wrapper had, and the
packages' `core` comes from the post or from con-ron's spec on the run. `installCstSimC`,
`installSimSumCtorsC` and `installSimCall` are gone (dead), and so are the unused `RSim.toSim`
and `Sim.withRunC`.

Pitfalls (add to §6.4):

* **A unified callee at `n` whose `RefE` is at `n + 1`** (`fsorts_ref`, called at the caller's
  fuel): split the fuel before `bindRun` (`rcases n with _ | k`) and close the `0` case by
  `RefE.callE_zero (fun _ => rfl)`. This replaces `callE_err_mono` on the error side.
* **The twin's last step followed by L-only callees** (`icbo_ref`: `checkSumCtors`, then two
  `rec2`): `rw [← bind_pure (checkSumCtors V fe fe _ _ _ _ _ _ _ _ _)]` makes the twin a bind, then
  `bindRun`, `onlySim`s and `RefE.ret rfl`. Write the `_`s: `checkSumCtors ..` in the pattern
  elaborates with one argument too many and does not match.
* **A positive model guard** (`if c then rest else .error e`, class `0`: `cbt_ref`'s result sort)
  has no rule: `split; rotate_left; · exact RefE.of_cls0 rfl`, then the `c` case.
* **`hK' := fun _ => rfl` in `lastE` fails** when the callee's ok arm repacks the pair
  (`ictE.k_check_block_ctors_go`), even for a non-recursive model: use `K.arm1 ..` (and `K.none ..`).
* **A named argument that shares a name with an explicit one** (`ct_ref … (n := …)`, where `n` is a
  `Word` after the fuel `k`) fills that one and shifts the positional rest: pass it positionally.
* **`grind` on a flag-vs-`Bool` guard is not free at scale**: four `by grind [decBool]` in
  `Install1` cost 0.35 s (90 ms each). Have the step state the flag as an iff
  (`idc_ref`: `v.1.headD 0 = 0 ↔ c = false`) and pass `hc.1 hc.2`; for a `decW0B` flag,
  `(fun h => by rw [← hok, h]; rfl) (fun h => by simpa [h] using hok)`.

Numbers, against master 1b1b1898 (`reflen.py`, `ncl.py`; elaboration `lake env lean` on the file,
3 interleaved runs, load 26–37, so "work" is the profiler's sum without imports and blocked time):

| theorem | before | after |
|---|---:|---:|
| `cbda_ref` | 111 | 78 |
| `sds_ref` | 128 | 66 |
| `cbt_ref` | 123 | 90 |
| `cbts_ref` | 58 | 56 |
| `cbi_ref` | 175 | 145 |
| `iao_ref` | 71 | 52 |
| `iac_ref` | 136 | 121 |
| `iaa_ref` | 68 | 63 |
| `icbo_ref` | 82 | 71 |
| `icbg_ref` | 101 | 88 |
| `ict_ref` | 33 | 28 |
| **`Install*` family** | 1086 | 858 (**−21 %**) |

| file (code lines) | before | after | work before → after | wall (median) | max RSS |
|---|---:|---:|---:|---:|---:|
| `IndT/Install1.lean` (with `InsAt`, 3 steps) | 353 | 315 | 3.05 → 2.62 s | 3.47 → 3.53 s | 2.47 → 2.46 GB |
| `IndT/Install3.lean` | 287 | 233 | 2.05 → 2.06 s | 2.97 → 2.12 s | 2.61 → 2.58 GB |
| `IndT/Install4.lean` | 287 | 257 | 1.65 → 1.36 s | 2.15 → 2.08 s | 3.00 → 3.01 GB |
| `IndT/Install6.lean` | 351 | 307 | 0.88 → 0.79 s | 1.37 → 1.41 s | 2.66 → 2.65 GB |
| `IndT/Install7.lean` | 335 | 275 | 2.54 → 2.49 s | 3.81 → 2.74 s | 2.66 → 2.65 GB |
| `IndInstallSpec/InstallSimCall.lean` | 48 | 38 | | | |
| `RefWalk.lean` (`callE_zero`) | 142 | 147 | | | |

The family: 1661 → 1425 code lines (**−14 %**, with its package, its three steps and the dead
wrappers), no file slower, memory unchanged. The `RefE` theorems lose 21 %, more than the
`RecGen` family (−15 %): the gain is where a unified callee was split twice (`sds_ref` −48 %,
`cbt_ref` −27 %, `iao_ref` −27 %) and where `bindE`/`lastE` replace a `rcases` of a unified
callee's result (`cbi_ref`, `icbg_ref`); the loops over unified callees (`cbts_ref`, `iaa_ref`)
lose 3–7 %. No file was left out.

### 6.9 Positivity, PosCrest, Tail, Pass, Block, CheckIndDecl (lane refwalk5)

Converted: `crest_ref` (`PosCrest.lean`), `cbp_ref` (`Positivity.lean`), `tail_ref` (`Tail.lean`),
`pass_ref` (`Pass.lean`), `block_ref` (`Block.lean`), `cid_ref` (`CheckIndDecl.lean`); and, from
§6.6's cleanups, `iis_ref` (`IdxSorts.lean`). Statements unchanged. New kit rule `RefE.bindRunLe`.

**No package and no steps.** Every lifted callee has one site (`bindLift`, or `onlySim` for the L
steps: `cv_lps`, the `block_shape_*` readers, `sl_nodup`, `check_block_positivity_init`/`_nfs`,
`cons_block_ctors`, `check_block_pass_rec`); the bulk is unified callees, which were split twice
(the error by `RefE.run_err`, the ok run by a second triple: `checkBlockInds_refinesC`,
`checkBasisDecl_refines`, `checkBlockIdxSorts_refinesC`, …) and are now one `bindRun`/`bindRunLe`
each. The knot calls of `crest_ref` (`infer_type_core`, `ensure_sort_core`) are `bindCall`.

**One package for the sum and install families.** `SumAt` (`SumSteps.lean`) is gone; its steps
and `Sum4` take `InsAt` (`Install1.lean`), which got `SumAt.top`.

**The last wrapper `Sim`.** `installSimFsortsC` (`Sum3.lean`) is deleted; `iis_ref` takes
`fsorts_ref` by `bindRunLe`. The `@[refines]` ok halves (`checkBlockIdxSorts_refinesC`,
`checkBasisDecl_refines`, the `…_refinesC` of the pass's checks) lose their last proof users here
but stay: they are the census links. The remaining wrapper `Sim`s (`cmC`, `cpvC`, `cpaC`,
`checkConstantVal_absOK`, …) are in the `Decl*T` files of the knot-call lane.

Pitfalls (add to §6.4):

* **A unified callee called at less fuel than its spec** (`pass_ref`: the checks at `F`, their
  specs and `RefE`s at `n + 3`, only `F ≤ n + 3` known; `iis_ref`: `fsorts_ref n` is at `n + 1`):
  `RefE.bindRunLe hle`. It replaces both `callE_err_mono` with its `hk0` on the error side and the
  fuel split of §6.8 (`rcases n` and `RefE.callE_zero`).
* **The twin's last step is a unified callee read through its run** (`check_basis_decl` and
  `check_block` in `cid_ref`, `check_block_tail` in `block_ref`, `check_block_tables` in
  `tail_ref`, `checkStructFieldSortsI` in `iis_ref`): `rw [← bind_pure (f _ _)]`, `bindRun`, then
  `RefE.ret rfl`. A twin still behind a `match some … with` (`cid_ref`'s `checkBlock`) needs
  `dsimp only` before the `rw`.
* **A guard on a `Bool` the twin computes** (`if !nameNodup … then fail … else`, `if !b then fail`):
  `RefE.ofArms (fun h => K.abort1 (hc1 := h) ..) (fun h => K.arm1 (hc1 := h) ..) (RefE.guardThen
  …)`, also for a non-recursive model whose guarded equations take explicit arguments.
* **`RefE.onlySim` needs `Option (ρ × Mem)`**: a callee whose `Option` has no memory
  (`nodupW : … → Option Word`) keeps its `rcases`.
* **A binder named `V`** clashes with `local notation "V"`; name it `Vf` in a rule stated in such a
  file.
* **Unused imports**: the conversions left three (`shake` gate).

Numbers, against master c7e644e2 (`reflen.py`, `ncl.py`; elaboration `lake env lean` on the file,
master's text in a master worktree, 3 interleaved runs, median, load 13–16):

| theorem | before | after |
|---|---:|---:|
| `crest_ref` | 154 | 122 |
| `cbp_ref` | 213 | 198 |
| `tail_ref` | 307 | 270 |
| `pass_ref` | 448 | 353 |
| `block_ref` | 242 | 211 |
| `cid_ref` | 174 | 154 |
| **the family** | 1538 | 1308 (**−15 %**) |
| `iis_ref` | 121 | 110 |

| file (code lines) | before | after | wall before → after | max RSS |
|---|---:|---:|---:|---:|
| `IndT/PosCrest.lean` | 220 | 188 | 1.37 → 1.45 s | 2.77 → 2.77 GB |
| `IndT/Positivity.lean` | 460 | 445 | 3.26 → 3.16 s | 2.93 → 2.93 GB |
| `IndT/Tail.lean` | 381 | 344 | 3.86 → 3.74 s | 3.32 → 3.32 GB |
| `IndT/Pass.lean` | 513 | 418 | 3.84 → 3.70 s | 3.41 → 3.40 GB |
| `IndT/Block.lean` | 307 | 276 | 2.24 → 2.18 s | 3.34 → 3.33 GB |
| `IndT/CheckIndDecl.lean` | 330 | 310 | 2.21 → 2.31 s | 3.34 → 3.33 GB |
| `IndT/IdxSorts.lean` | 277 | 266 | 2.72 → 2.75 s | 2.75 → 2.74 GB |
| `IndT/Sum3.lean` (`installSimFsortsC`) | 415 | 392 | 3.08 → 3.40 s | 2.70 → 2.70 GB |
| `IndT/SumSteps.lean` (`SumAt`) | 228 | 205 | 1.04 → 0.93 s | 2.59 → 2.58 GB |
| `IndT/Install1.lean` (`InsAt.top`) | 315 | 317 | 2.26 → 2.24 s | 2.58 → 2.59 GB |
| `RefWalk.lean` (`bindRunLe`) | 147 | 165 | | |

The family: 2211 → 1981 code lines (**−10 %**); with the cleanups and the kit rule 3593 → 3326
(−7 %). Time and memory unchanged (the differences are within the runs' spread: Sum3's runs are
2.88–3.99 s before, 2.87–4.17 s after). As §6.5 predicted for unified callees, the files lose ~10 %;
the theorems lose more (−15 %) where a callee was split twice (`pass_ref` −21 %, `crest_ref` −21 %
with its two knot calls) and least where the plumbing is facts about the results (`cbp_ref` −7 %:
the twin's whole run is rebuilt for `checkBlockPositivity_spec`). No file was left out.

Next families, by `reflen.py` (none converted yet, `liftE_none` splits per file): the inference
bodies (`InferBodyBindPi`'s `pisLoop_ref`, `InferBodyBind`'s `lamsLoop_ref`, `InferBodyDisp`'s
`ibo_ref`/`ib_ref`, `InferBodySpine*`'s `spLoop_ref`/`spioLoop_ref`; ~1.1 k lines, 3–7 splits each),
the iota reduction (`WhnfIotaRecRefine*`: `vck_ref`, `major_ref`, `fire2_ref`; 13 splits per file),
`InferProj*` (`ipa_ref`, `ip_grade`), and the positivity tops (`PosNty`'s `nty_ref`, `PosTopE4`'s
`nsd_ref`, `IndsE4`'s `cbao_ref`).

### 6.10 The knot callers (lane refwalk4)

Converted: `cch_ref`, `cco_ref` (`Verdict/IndBHdr.lean`), `pds_ref`, `pde_ref` (`IndBTpd.lean`),
`rto_ref` (`IndBRec2.lean`), `crule_ref` (`IndBRec4.lean`), `crp_ref`, `cdo_ref` (`DeclCrpT.lean`),
`cert_ref`, `dnc_ref`, `dng_ref` (`DeclNatGateT.lean`), `cm_ref`, `ctp_ref`, `cpv_ref`, `cpa_ref`
(`DeclDivGateT2.lean`), `cda_ref` (`DeclAxQuotT.lean`), `ivg_ref`, `tv_ref`, `cvg_ref`
(`Verdict/DeclValE.lean`), `ccv_ref`, `dv_ref`, `ov_ref` (`DeclValsE.lean`), `tmp_ref`
(`IndT/RecCheckPins.lean`). Statements unchanged. No new kit rule, no package, no steps: every
lifted callee has one site under its theorem, and the knot calls are `bindCall` as they stand.
`checkConstantVal_absOK` (`DeclArmT.lean`) had no users and is gone. `cmC`, `cpvC`, `cpaC` have no
proof users either, but they are `@[refines]` census links (their proofs are one `RefE.run_okW`
each), so they stay, like §6.9's ok halves. `e_view` does not occur in these files, so no shared
`e_view` lemma was added.

**`bindCall` takes the knot's `Sim`s as they are.** The `StageT` sims of `KnotStageProg`
(`inferTypeCore_sim`, `ensureSortCore_sim`, `isDefEqCore_sim`) are `Sim`s over `(r, m')`. `bindCall`
wants an `RSim`-shaped `h1`, which is `fun b h => hq.isDefEqCore_sim … b.1 b.2 h`. A `RelW`
(`apdF_okT`, `crfF_okT`, applied to the call's `callW`) goes in the same way:
`fun b h => apdF_okT … m b.2 a b.1 (apdF_of_callW hap h) pre`. The `StageC` `RSim`s (`inferC_rsim`,
`isDefEqC_rsim`) go in unapplied. A `RelW` for `bindSim` (`lbbF_okT`, `hffF_okT`, the `nat_op_*`
refs) is `(fun r m' h => lbbF_okT … m m' a r h hS)`, or `(natOpGuard_ref … m a · · pre ·)`.

Pitfalls (add to §6.4):

* **Rewrite the twin's argument once, at the top.** The twin reads `cv.type`, `vg.jv`, `decE x`
  where the knot claims and sims say `decI wt`, `decI wj`. A `rw [hty]` (or `rw [hty, hjv]`,
  `simp only [decE_eq]`) on the goal before the first `bindCall` removes every
  `rw [h00, ← hty] at this` / `at hrun` pair. `(0 : Word).toNat` against `0` needs no rewrite:
  `bindCall` unifies up to defeq. A twin form folded under a definition (`dvT`) needs the `rw` again
  after the `unfold`.
* **The twin's result as an equation in the post** (`decI (r.headD 0) = x` of the sims): name it
  in the `fun` pattern and `subst`. A `rfl` pattern fails when the twin's result binder is `_`.
* **`bindCall`'s `herr` is the claim on the twin step itself.** The old `intro hG; …;
  exact ErrClaim.bind_left this` becomes the bare claim. An extra `ErrClaim.bind_left` makes the
  rule split the twin at the wrong bind (`get`, `whnf`).
* **`lastE` against a non-recursive continuation of the model's own arguments**
  (`defnNatGateE.k_defn_nat_cert p`) needs `(K := …)` too, as in §6.7.
* **A run that leaves the twin state (`e1 : a1 = a`) after `bindSim`** is `subst a1`. A
  `rw [e1] at hrun1 hS1` leaves the goal at `a1`, and a later `bindE` with a callee stated at `a`
  fails.
* **A redundant `import ConAgua.Arena.RefWalk`** where an imported knot caller already brings it
  (`IndBRec2` through `IndBHdr`, the `Decl*T` files through each other) fails the `shake` gate. So
  did `RecGen28`'s import after refwalk3; it is dropped here.

**What stays by hand**, and why:

* **A twin step computed from several L calls**: `pds_ref`'s `tpClosed` from four reads (`bvar_b` ×2,
  `fvar_b` ×2) with early exits. The reads are `onlySim`, but the exits stay `K.arm` rewrites.
* **Model arms that return `.ok` early** (`if r = 0 then .ok (0, m) else rest`: `cert_ref`, the
  `div_mod` guards of `cm_ref`/`ctp_ref`/`cpa_ref`, `dng_ref`'s membership): no rule. The
  `by_cases` and the `K.armᵢ` rewrites stay.
* **A callee whose model equation is needed later**: `tmp_ref`'s `tptE` (its frame `tptE_mfr` takes
  `tptE … = .ok`). `bindE` does not hand the equation out, so the `rcases` stays.
* **A call outside the closure with no twin step and an error claim** (`callE` of `erec_ci`,
  `pin_at`, `env_push` in `cdo_ref`, `dv_ref`, `ov_ref`): no rule. An `onlyCall` (the `callE`
  analogue of `onlySim`) would save one line per site, so it was not added.
* **`install_value_guards` in `tv_ref`, `cvg_ref`, `dv_ref`, `ov_ref`**: its error half is a field of
  the caller's `G` (`hG.ivg`), not `RefE.run_err` under the spec's `Gs`, so `bindRun` does not
  apply.
* **`ctp_ref`'s `is_def_eq_core`**: the twin reads `tp.2` where L reads `decI tp.2.word.toUInt64`.
  `rw [← decI_word]` on the goal would also rewrite the model's arguments.

`dv_ref` and `ov_ref` are the same proof over two models (67 lines each). One lemma over the
model would take another 67 lines off.

Numbers, against master 1b1b1898 (the eleven files are unchanged on master since; `reflen.py`,
`ncl.py`; elaboration is `lake env lean` on master's text and the
branch's in the branch worktree, 3 interleaved runs, median, load 13–23. "work" is the profiler's
sum without `import` and `blocked`:

| theorem | before | after |
|---|---:|---:|
| `cch_ref` | 182 | 128 |
| `cco_ref` | 41 | 26 |
| `pds_ref` | 227 | 198 |
| `pde_ref` | 88 | 81 |
| `rto_ref` | 130 | 103 |
| `crule_ref` | 109 | 91 |
| `crp_ref` | 201 | 156 |
| `cdo_ref` | 172 | 153 |
| `cert_ref` | 61 | 58 |
| `dnc_ref` | 111 | 99 |
| `dng_ref` | 117 | 89 |
| `cm_ref` | 239 | 221 |
| `ctp_ref` | 112 | 111 |
| `cpv_ref` | 98 | 86 |
| `cpa_ref` | 55 | 45 |
| `cda_ref` | 340 | 298 |
| `ivg_ref` | 117 | 76 |
| `tv_ref` | 178 | 131 |
| `cvg_ref` | 197 | 169 |
| `ccv_ref` | 54 | 37 |
| `dv_ref` | 84 | 67 |
| `ov_ref` | 84 | 67 |
| `tmp_ref` | 126 | 112 |
| **the family** | 3123 | 2602 (**−17 %**) |

| file (code lines) | before | after | work before → after | wall (median) | max RSS |
|---|---:|---:|---:|---:|---:|
| `Verdict/IndBHdr.lean` | 343 | 275 | 2.54 → 2.59 s | 3.87 → 3.86 s | 2.57 → 2.57 GB |
| `Verdict/IndBTpd.lean` | 389 | 354 | 3.54 → 3.45 s | 4.60 → 4.44 s | 2.74 → 2.74 GB |
| `Verdict/IndBRec2.lean` | 193 | 166 | 1.37 → 1.45 s | 2.60 → 2.10 s | 2.69 → 2.72 GB |
| `Verdict/IndBRec4.lean` | 217 | 200 | 1.52 → 1.46 s | 2.30 → 1.83 s | 2.69 → 2.70 GB |
| `DeclCrpT.lean` | 528 | 464 | 2.50 → 2.14 s | 2.72 → 3.00 s | 2.70 → 2.69 GB |
| `DeclNatGateT.lean` | 396 | 354 | 2.78 → 2.61 s | 2.81 → 3.34 s | 2.62 → 2.61 GB |
| `DeclDivGateT2.lean` | 630 | 589 | 6.39 → 6.54 s | 5.67 → 6.47 s | 2.89 → 2.88 GB |
| `DeclAxQuotT.lean` | 373 | 332 | 4.30 → 4.25 s | 5.33 → 4.92 s | 3.09 → 3.08 GB |
| `Verdict/DeclValE.lean` | 543 | 426 | 5.19 → 4.87 s | 5.25 → 5.63 s | 2.79 → 2.79 GB |
| `Verdict/DeclValsE.lean` | 279 | 228 | 1.94 → 1.92 s | 1.78 → 1.91 s | 2.66 → 2.66 GB |
| `IndT/RecCheckPins.lean` | 192 | 179 | 0.41 → 0.39 s | 1.15 → 1.20 s | 2.62 → 2.61 GB |
| `DeclArmT.lean` (`checkConstantVal_absOK`) | 384 | 375 | | | |

The family: 4083 → 3567 code lines (**−13 %**), memory unchanged, work unchanged (−0.4 to +0.15 s
per file). The wall times at load ~20 move both ways by up to 0.5 s between batches (a second batch
gave `DeclNatGateT` 3.13 → 2.83 s, `IndBRec2` 1.97 → 2.35 s). Only `DeclDivGateT2` was slower in
both batches (+0.6 s), and its profile differs by 0.1 s (`instantiate metavars`), so no file was
left out. The `RefE` theorems lose 17 %. That is the Sum1–3/`Install` range, because the knot calls
were the longest hand splits (6–9 lines each to 3–4 lines each: `ivg_ref` −35 %, `tv_ref` −26 %,
`cch_ref` −30 %, `dng_ref` −24 %). They lose least where the plumbing is model-only arms (`ctp_ref`
−1 %, `cert_ref` −5 %, `cm_ref` −8 %).

Next families: the ones §6.9 lists (the inference bodies, the iota reduction, `InferProj*`, the
positivity tops), and the other `Verdict/IndB*` files (`IndBClm`, `IndBCrg`, `IndBTmo`, …; check
`reflen.py`).
