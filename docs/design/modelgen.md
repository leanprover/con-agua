# Lane `modelgen`: Generated word models and vcgen specs

Journal of lane `modelgen` (decisions, measurements, findings, open ends). Only this lane edits this file.

## Generated models and specs (2026-10-22, lane `modelgen`)

Recommendation 1 of `docs/proof-review.md`: generate, from an L function's text, the word model
(the second copy of the L code), its continuations and guarded equations, and the `vcgen` spec
with its proof. Piloted on finished, untouched code: the phase-4 walks (`Lift*`, `Inst1*`) and the
level files (`Level*`).

### The mechanism: `l_model` (`L/ModelGen.lean`, a command, ~1150 lines of meta code)

```
l_model liftGo_spec (p : Prog) (hp : LiftProg p)
  fns [hp.go ↦ liftW, hp.app ↦ liftAppW, …]
  specs [derB_spec p hp.derb n, memoFindG_spec lfSch p _ hp.lff n, mkApp_spec … n, …]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW] gen 20 heartbeats 1000000
```

* **Input.** For each member of a (mutually recursive) group, a proof `p.lookup "f" = some F` and
  the model's name; the specs of the callees as terms (the same terms a hand proof gives `vcgen`).
  The command reads `F`'s `lfn` text back from the file (declaration range, re-parsed), so it has
  the locals' names and the leaf terms as written (`CTL`, `⟪S.cs⟫`).
* **Callee models come from the callees' specs**, not from a registry: the post of each spec term
  is analysed (six shapes: effectful `F = some (r.headD 0, s'.mem)`; pure results
  `r.headD 0 = F₀ ∧ …` with the memory unchanged; a result list `r ≠ [] ∧ r = F`; memory only
  `F = some s'.mem`; total memory update with side conditions `G ∧ s'.mem = F`; read-only
  `F = some (r.headD 0)`). So any hand-written or generated spec in the PLAN's shape is a callee.
* **Translation** is symbolic execution of the statement list: locals are inlined, `abort` is
  `none`, a load is `rdW`, a store `Mem.set64`, a call to a group member is its model at fuel `n`,
  `x := call f(…); return x` is a tail call, and the code after an effectful call becomes a
  first-order continuation `fW.kᵢ` over the locals it reads (`| none => none | some (x, m₁) => …`,
  the PLAN's named-continuation style). The code after an `if` whose branches both fall through
  becomes a join point (a named function of the locals and the memory) instead of a copy.
  Identical continuations of a group are shared (the five lift arms share one "find; put; return"
  tail, the hand code's `lsetK`). `fold [tierW, idxW]` folds named word functions back in, and
  `fold [lvG, lvA, lvB]` the named results of a list callee.
* **Output.** The models (structural recursion on the fuel; well-founded on `(n, depth)` when
  continuations call the group's models, as `LevelLeq.lean` does by hand; no fuel argument for a
  single non-recursive function, as the hand `lhMkW`/`dist1W`); one **guarded equation**
  `fW.armᵢ` per non-`none` leaf of each model's and continuation's `if` tree (the path conditions
  as hypotheses, proved by the equation lemma and `ite_eq_left/right`) with a `grind_pattern` per
  attribute; the **spec** as a conjunction over the group, a step theorem `name.stepᵢ` per member
  (`vcgen` with only the callees that member calls, then `finish`) and the fuel induction.

### Pilot: what was replaced, lines and time

| file | lines before | after | what changed |
|---|---:|---:|---|
| `Lift.lean` | 591 | 219 | models, 10 continuations, 33 hand equations, 22 patterns, `liftGo_step` → one `l_model` |
| `LiftSpec.lean` | 171 | 56 | 5 arm steps, the induction, the entry's model/eqs/spec → one `l_model` |
| `LiftRefine.lean` | 521 | 526 | equation names (`liftW_app` → `liftW.arm4`, …), `tail_ok` over the shared continuation (+6) |
| `Inst1.lean` | 550 | 193 | as `Lift.lean` |
| `Inst1Spec.lean` | 174 | 60 | as `LiftSpec.lean` |
| `Inst1Refine.lean` | 519 | 524 | as `LiftRefine.lean` |
| `LevelSimp.lean` | 294 | 123 | `combW`, `simpW` (+`imaxW`, `simpK₁/₂`), `nzW`, 21 equations, 3 specs → three `l_model` |
| `LevelSimpRel.lean` | 264 | 273 | `imaxW_ok` over the generated join point (+9), names |
| **total** | **3084** | **1974** | **−1110 (−36 %)**; the generator is +1150 once |

Per function the hand-written part that remains is the L text, the program bundle and one
`l_model` (10–15 lines with the callee spec list). The refinements were adapted mechanically: the
dispatcher proofs (`lgoOK_succ`, `igoOK_succ`) kept their `by_cases` skeleton and dead-branch
lines (`rw [liftW] at hb; simp […] at hb` works on the generated model), only the equation names
and their hypothesis lists changed (the generated arm takes every path condition, e.g.
`liftW.arm4 n m h c k hcut hs g0 g4 hc` for the hand `liftW_app n m h c k hcut (vok 4 hc) g4`).
No theorem used outside these files changed (`liftEntry_refines`, `liftEntry_run`,
`instEntry_refines`, `instEntry_run`, `LiftProg`, `InstProg`, `liftProg`, `instProg`,
`lvComb/Simp/Nz_spec`, `combW_ok`, `simpW_ok`, `nzW_ok` keep their statements; the entries'
`liftEntryW`/`instEntryW` now take the fuel of their own call, `n + 1`, which only the two
refinement files read).

**Build time** (CPU seconds of `lake env lean` per file, old and new interleaved, two runs each,
load average 65–157, so ±15 %): `Lift` + `LiftSpec` 99 → 85, `Inst1` + `Inst1Spec` 45 → 56,
`LevelSimp` 7.6 → 6.2, the refinements unchanged (1–2.5 each); in total about the same (157 →
152). The generated specs pass each step only the callees it calls; the generated arm equations
carry more hypotheses than the hand ones (every path condition), which costs `finish` a little
(`Inst1`). The model/spec files now elaborate their steps in parallel (one theorem per member).

### What the generator does not handle (yet), from a dry run over all 43 level functions

Besides the 3 replaced, 28 more level functions were generated and their specs proved by the
standard script in a scratch copy (`LevelSubst` 4, `LevelZero` 2, `LevelHeap` `lh_mk`/`lv_eq`,
`LevelEquiv` 5, `LevelLeq`'s group of 7 in one `l_model` with `heartbeats 4000000`,
`LevelIntern` 5), 25 s for the `LevelLeq` group. Not handled:

* **several results**: `return (a, b, c)` (`lv_node`, `ls_node`, `lp_lookup`, `lv_lookup`) and
  callees whose post has `r.tail.headD 0` inside the model (`lookupW … = some (r.headD 0,
  r.tail.headD 0)`, so `lp_substl`, `lp_spw`, `lv_substl`, `lv_spw`): a list-valued model kind and
  a two-word continuation binder would cover them;
* **loops and named blocks** (`succ_find`'s `⟪sfindLoop⟫`, `succ_push`'s `⟪hpBlkS⟫`): a `while`
  needs its own fuel-recursive model and loop spec;
* **parameterized `FunDecl`s and models with Lean parameters** (`lvMemG A`, `lvSpwG PA`,
  `memoFindG S`, the generic `substLW KA VA`): the lookup must be `some F` for a constant `F`;
* **callee posts with extra facts** (`succ_push`'s `spushOK m t = true ∧ r = [scnt m t] ∧ …`).

Shape differences that matter for **retrofitting** (none of them for new code):

* the generated model is the L text, not a hand abstraction: `lhMkW` has a guard
  `(m.arr64 CTL).size ≤ 192` the L code does not have (a store out of bounds aborts, which the
  generated model does not model); `imaxW`'s two tests merged with `∧` are a nested `if` and a
  join point; the memo's `r ≠ []` becomes a `none` branch unless `noguard`;
* names are positional (`fW.kᵢ`, `fW.armᵢ`) and arm hypotheses are the raw path conditions (no
  `viewOK` bundling); a refinement written against hand names needs renames;
* **models used by other lanes' files cannot be swapped in place**: `zeroW` (7 files), `eqK` (6),
  `lvSubIntW` (5), `equivW`, `caW` (3 each), … are unfolded or rewritten by `Decl*`/`Ind*`/`Whnf*`
  proofs, and the level models call each other (`dist1W` is fuel-free by hand and generated, but
  `caW` in `LevelLeq` takes it as a callee), so replacing one cascades. That is why only
  `LevelSimp` (internal to the `Level*` files) was replaced.

### Recommendation

Use `l_model` for **new** L code: write the `lfn`, list the callee specs, and write the relational
proof against the generated `fW.armᵢ`/`fW.kᵢ.armᵢ` (look them up with `#check`, or `trace`). This
removes the model, continuations, `_some` equations, guarded equations, `grind_pattern`s and the
spec proofs (in the pilot 63 % of the model/spec files, 36 % of model + spec + refinement).
Do not retrofit finished code whose models other files read; retrofit only where the models are
internal (as `LevelSimp`), or when a function is rewritten anyway. Next steps, in order of value:
several results (a list model kind), `while` loops with a generated loop spec, `FunDecl`
parameters, optional names for arms (`l_model … arms [cut, bvar_lt, …]`) so refinements read
better, and generating the callee facts in `Sim` form (recommendation 2) from the same arms.
