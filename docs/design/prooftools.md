# Lane `prooftools`: Proof tooling: lookup bundles, Sim.bindK, fuel, handle bound

Journal of lane `prooftools` (decisions, measurements, findings, open ends). Only this lane edits this file.

## Proof tooling: `Sim`, `ProgHas`, fuel monotonicity (2026-10-22, lane `prooftools`)

The low-cost items of `docs/proof-review.md` (recommendations 2 and 3, and the two side items),
built as reusable tools and piloted on finished modules nobody is editing: the `abstract1`,
`abstractRange`, `instantiateList`, `fvarRange`, `bvar_b`, `has_fvar` walks (`Arena/{Abs1,ArRange,
InstList,FVarRange,BvarB,HasFvar}*.lean`) and the 17 store-table refinements
(`Arena/{App,Const,Let,Lam,Forall,Sort,BVar,FVar,Proj,Zero,Max,Imax,Param,Ls,NStr,NAnon,NNum}Refine.lean`).
Every theorem name and statement that another file uses is unchanged.

### The tools

* **`ConAgua/Arena/SimLib.lean`: `Sim` in `L.Arena`.** Lane `indproofs2`'s `Sim` (`IndSim.lean`)
  sits behind `IndMaster`, so the walks and stores could not use it. SimLib is the same definition
  right above `StoreRel`, plus what the pilot needed:
  * `SimD dec mo op a R`: the decoded form (`Sim` with post `x = dec r ∧ R m' a'`), and
    `Sim.ofD`/`SimD.exists` to and from the walks' existing statements
    `model = some (r, m') → ∃ a', op.run a = .ok (dec r, a') ∧ R m' a'`;
  * `Sim.bindD`: `Sim.bindK` for a decoded callee (the rest sees `dec r`);
  * `Sim.ofOk`/`Sim.ofOkD`: from the stores' `…_correct` form (`AM.ok ∧ R ∧ AM.res = dec w`);
  * `Sim.triple`/`Sim.tripleD`: **model spec + `Sim` ⇒ census triple** (P9), replacing the 5-line
    `M.triple_of_run`/`M.of_run`/`subst`/`exact ⟨hloc, …⟩` block;
  * `MPost mo Q` with `MPost.bindK`/`MPost.ret`: the same composition for model-only facts (frames,
    result bounds), and `Sim.withM` to add such a fact to a `Sim` post.
  `L.Ind.Sim` and `L.Arena.Sim` coexist: inside `namespace L.Ind` the local name wins over
  `open L.Arena` (checked). Lane `indproofs3` can replace `IndSim.lean`'s `sim` section by an
  import of SimLib when it next touches the file (the definitions are identical).
* **`ConAgua/L/ProgHas.lean`: program bundles from the program text (rec. 3).**
  `ProgHas p fs := ∀ f fd, fs.lookup f = some fd → p.lookup f = some fd`. A bundle is the function
  list the module already writes for its test program:
  `def AbsProg (p : Prog) : Prop := ProgHas p absWalkProg`. Lookups are `hp.get "abs_go"` (the body
  is computed from the list by `rfl`); sub-bundles are `hp.right` (`l₁ ++ l₂`, with a decided
  no-shadowing check on the names' bytes), `hp.left`, `.trans`, `.cons`, `.append`; the test
  program's own bundle is `ProgHas.refl _` (or `.left` of it); `ProgHas.agreeWith hp hq ns` is
  `closedW_of_agree`'s hypothesis (the `WriteSets` `agree` proofs went from 10–40 lines of
  `hp.x.trans rfl` to one line each). Use `def`, not `abbrev`, for the bundle name: `sym`
  unfolds reducible definitions in the context, after which `hp.base` (a theorem in the bundle's
  namespace) no longer resolves.
* **`ConAgua/L/FuelMono.lean`: `exec_mono` moved to `L/`** (`KExt`, `step_mono`, `invoke_mono`,
  `exec_mono`, `exec_le`; `Front/RunModel.lean` re-exports the old `L.Front.*` names). New:
  `invoke_fuel_le (hk : k ≤ n) : triple at fuel n → triple at fuel k`, which is what every
  `XUpTo p n := ∀ j ≤ n, XSpec p j` family exists for.

### How to write a relational lemma with `Sim` (the standard style from now on)

1. State callee facts as `Sim`/`SimD` (or keep an existing `∃`-statement and wrap it with
   `Sim.ofD fun r m' e => callee_ok … e` at the use site).
2. After the twin's views are rewritten (`rw [StateT.run_bind, viewApp_run, viewApp_ok …,
   except_ok_bind]`, plus `dsimp only` if a `match` on the view is left), turn the goal into a
   `Sim` and chain one `bindD` per callee:
   ```lean
   refine SimD.exists (Sim.bindD rfl (fun _ _ => rfl)
     (Sim.ofD fun x m₁ e => ih m m₁ a _ k d fu x hA hfw e) fun x m₁ a₁ hA₁ => ?_) hb
   refine Sim.bindD (K := aappK₁.aappK₂ h k _ _ x) rfl (fun _ _ => rfl)
     (Sim.ofD fun y m₂ e => ih m₁ m₂ a₁ _ k d fu y hA₁ haw e) fun y m₂ a₂ hA₂ => ?_
   exact Sim.ofD fun r m' hb => atail_ok … hb      -- or Sim.ret ⟨…⟩, Sim.ofOk …
   ```
   No `cases h : callee`, no dead `| none =>` branches, no final `simp only [StateT.run_bind,
   ha₁, ha₂, …]` replay.
3. The census theorem is `Sim.tripleD (f_spec …) (Sim.ofOkD (f_correct …))` (or `Sim.triple` with
   a general post).

Pitfalls found in the pilot:
* **Name the continuation from the second callee on**: `(K := fK₁.fK₂ … x)`. `rfl` for
  `hs : K (some (r, m)) = body r m` assigns `body := fun r m => K (some (r, m))` unreduced, and the
  next `?K ?mo` then unifies first-order with `K₁ (some (x, m₁))`. The first step needs no name
  (the hypothesis `hb` fixes it). A `where`-continuation takes the outer function's parameters it
  uses: `#check @fK₁.fK₂` gives the arity.
* **The relation must be a named predicate** applied to `m' a'` (`ArenaA`, or an `abbrev` such as
  InstList's `SpnR m₀`): a conjunction `ArenaL m' a' ∧ m'.arr64 ILSPN = m.arr64 ILSPN` is not a
  higher-order pattern under the `∃`, and `SimD.exists` fails to elaborate. Pass `(R := SpnR m)`.
* A relation relative to the arm's start memory (InstList's spine frame) still needs the
  transitivity chain at the end (`hs₃.trans (hs₂.trans hs₁)`): `Sim` composes the steps, not the
  frames. `MPost` composes frames of the model alone.

### Pilot measurements

Lines (physical, `wc -l`), before = master `48010ce`, after = this landing.

| file group | before | after | Δ | tool |
|---|---:|---:|---:|---|
| walk refinements (`Abs1Refine`, `ArRangeRefine`, `InstListRefine`, `FVarRangeRefine`, `BvarBRefine`, `HasFvarRefine`) | 3348 | 3123 | −225 | `Sim.bindD` (24 arms, 2 cut-off steps), `MPost` (6 frame lemmas), `Sim.triple` |
| 17 store refinements | 4336 | 4293 | −43 | `Sim.tripleD` + `Sim.ofOkD` (5 lines → 1–2 each) |
| bundles + their users (`Abs1`, `Abs1Spec`, `ArRange(Spec)`, `InstList(Spec)`, `BvarB`, `WriteSets`) | 3356 | 3328 | −28 | `ProgHas` (4 structures, 4 `_ok` proofs, 5 `agree`/`closed` proofs) |
| unchanged pilot files (`HasFvar`, `FVarRange`) | 528 | 528 | 0 | |
| **pilot total** | **11568** | **11272** | **−296 (−2.6 %)** | |
| new library (`SimLib` 201, `ProgHas` 124, `FuelMono` 117 of which 83 moved from `RunModel`) | | | +359 net | |

Per construct: a walk arm's callee plumbing went from ~15 lines (two callees: 9 `cases`/`obtain`
lines, two `ih` obtains, the final replay) to 4–5; a three-callee arm from ~20 to 6–7; a frame
lemma (`FrOK.app`) from 15 to 4; a census glue block from 5 to 1–2. `ProgHas` alone saves little in
the pilot (−28): the structures were short, `hp.get "mk_app"` is longer than `hp.base.mkapp` (the
`vcgen` lists of `InstListSpec`/`Abs1Spec` grew by 21 wrapped lines), and its gain is in the
`agree` proofs (−40 in `WriteSets`) and in not writing new structures.

Elaboration cost: wall time was useless (load average 70–100 during the measurement: the unchanged
`FVarRange` went from 16 s to 40 s between two runs), so `perf stat -e instructions:u` of
`lake env lean <file>`, master `48010ce` against this branch, in 10⁹ instructions:

| file | before | after | |
|---|---:|---:|---|
| `Abs1` | 21 | 28 | `AbsProg.base` (33 `hp.get`s by `constructor`) and the decided `NoShadow` |
| `Abs1Spec` | 582 | 591 | `hp.get` in the `vcgen` lists (+1.5 %) |
| `ArRange` / `ArRangeSpec` | 31 / 693 | 33 / 702 | same (+1 %) |
| `InstList` / `InstListSpec` | 40 / 328 | 46 / 353 | same (+8 % on the spec file) |
| `Abs1Refine` / `InstListRefine` / `ArRangeRefine` | 18 / 18 / 7 | 19 / 17 / 6 | `Sim.bindD`: no cost |
| `AppRefine` (a store) | 6 | 6 | `Sim.tripleD`: no cost |
| `FVarRange` (unchanged, control) | 117 | 117 | |

So `Sim` is free, and `ProgHas` costs a few percent where `hp.get "f"` sits in a `vcgen` list (each
use re-runs the `rfl` lookup through a ~70-entry list with `String` comparisons). A spec that
needs many lookups should `have` them once, or take the bundle.

### What did not work, or was not done

* **`UpTo` families (side item 1):** none is in the pilot modules (all 234 mentions are in
  `Whnf*`/`DefEq*`/`Infer*`/`KnotSlot`, lanes `whnf4` and finished `defeq2`). `invoke_fuel_le` is the
  replacement; the conversion is a per-family edit: delete `def XUpTo`, take `XSpec p n`, and pass
  `invoke_fuel_le (by omega) (hs …)` where a `j ≤ n` instance was used. Not measured.
* **Handle bounds in the relation (side item 2):** the pilot shows the store relation already
  carries the bound for every word *read* from a record (`ARecRel` stores `k.f.word.toUInt64`, a
  `UInt32`; `view_app` returns `hfw`/`haw`); what is missing is the bound on intern *results*, which
  is a post, not a relation fact: `internM_hw` (`WhnfCoreApp.lean`, lane `whnf4`) proves it once for
  every table. All 57 `if 4294967296 <= r { abort }` guards are in `Ind*`/`Rec*`/`Decl*`/
  `LevelLeq`/`Front/IndApply` (active lanes), after `intern_*`, `const_e`, `reduce_cert_var` and
  `EREC` reads: each is dead code given `internM_hw` (or the env relation for `EREC`/`const_e`), so
  removing it keeps the twin semantics exactly (no deviation row needed) **once the callee's
  refinement post carries `HW r`**. The tool for that without restating lemmas is `Sim.withM
  (callee_sim …) (internM_hw-as-MPost …)`. Not done here: it needs `internM_hw` moved to
  `StoreLib.lean` (a `whnf4` file today) and edits in the owning lanes' L code.
* **Bundles with field users elsewhere** keep a shim per used field (`BvbProg.lbb` for `CoreWalks`);
  a `def` bundle cannot offer `hp.field` for free. Only one shim was needed in the pilot.
* **Not converted:** the dispatchers (`anodeOK_succ` etc., P10: tag dispatch, not callee chains),
  the entries (`absEntryW_correct`: one callee between two twin-only memo clears; `Sim.bind_twin`
  would do it, saving ~3 lines each), `lbvarArm_ok`, and the probe/tail helpers (`aprobe_ok`,
  `atail_ok`, `ltail_ok`), whose `∃`-statements are kept and wrapped with `Sim.ofD` at the use site.

### Recommendation for lanes

1. **New relational lemmas: `Sim`/`SimD` + `Sim.bindD` chains, census theorems by `Sim.tripleD`.**
   Import `ConAgua.Arena.SimLib` (or `IndSim` in the inductive tier, same API). Expect the callee
   plumbing of a lemma to shrink by half to two thirds; name the relation, name `K` from the second
   callee on.
2. **New program bundles: `def XProg (p : Prog) : Prop := ProgHas p xWalkProg`**, where `xWalkProg`
   is the list the module writes anyway; lookups `hp.get "f"`, sub-bundles `hp.right`. Better
   still, let callee specs take the bundle rather than five lookups each (the long `hp.get` lists
   in `vcgen [...]` come from `mkApp_spec p hderb happf happp happi hmk n`-style signatures).
3. **Existing files:** convert opportunistically when a lane edits the file anyway; a whole-file
   conversion of a finished walk took ~10 minutes of mechanical editing (with throwaway regex
   converters for the walks' common arm shape) and saves 5–10 %.
4. Lane `whnf4` (owner of the `UpTo` families and `internM_hw`): replace `KnotUpTo`/`WhnfStepUpTo`
   with `invoke_fuel_le`, and move `internM_hw`/`hdW_lt`/`hit_idx_lt` to `StoreLib.lean`; then the
   inductive/decl lanes can drop their `2^32` guards with `Sim.withM`.
