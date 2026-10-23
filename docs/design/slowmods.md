# Lane `slowmods`: the slowest modules

Goal: no module above ~60 s or ~6 GB of elaboration. Measurements: each module elaborated alone
(`lake env lean -Dprofiler=true -Dprofiler.threshold=1000 F.lean`, imports from the shared cache),
wall seconds and peak RSS of the process tree, niced, 3-4 at a time on the shared machine (load ~50-70):
compare before/after of the same module, not single digits.

## Landings

| module | before | after | how |
|---|---:|---:|---|
| `ConAgua.Checker.ProjFnShapeRef` | ~290 s (lane's figure) | 2 s, 2.5 GB | `pfs_spec` from `L.Ind.isProjFnShape_specW` (`IndRealIpf.lean`, the same L function's spec by `vcgen` with `L.evalC_spec`) plus `pfsW = ipfW`; its own `vcgen` over `evalC` had ~790 paths |
| `ConAgua.Arena.DeclCanonExpr` | 442 s, 2.8 GB | 26 s, 2.6 GB | `canonExprEq_spec`: plain `vcgen`, then `simp only` the locals (`setLoc`/`setLocs`/`init9_k`, `Cmp.eval`) at every goal, then `grind`, instead of `sym … => vcgen … <;> finish` |
| `ConAgua.Checker.FrontProgAgree` | 264 s, 4.3 GB | 15 s, 3.0 GB | `front_agree`: each `checkerProg.lookup f = frontAllProg.lookup f` by position on both sides (`lk_of_idx`, `LoopProgTac.lean`; `lkF_of_idx` from `frontAll_nodup`, one kernel check over name codes), the positions computed once per chunk by compiled code, the proof assigned without the elaborator's `isDefEq`; was `rfl` (141 s elaboration + 122 s kernel comparing `String`s) |
| `ConAgua.Arena.DeclNatDeps` | 627 s, 4.3 GB | 146 s, 3.9 GB | `natOpDeps_specW`: plain `vcgen`, `simp only` the locals and `a[i.toNat] = rdW a i` (`nd_getElem`), `grind -lia -ring -linarith` with one guarded equation per dispatch arm (`depsArmW_k`); still ~4 s per goal (32 goals; the 15 bound hypotheses of the loads) |
| `ConAgua.Arena.RecGenSpec16` (helper c) | 241 s, 3.6 GB | 11 s, 2.8 GB | `tmm_spec`: `vcgen` with `L.evalE_spec`, `all_goals simp_all [...]`, no `grind` |
| `ConAgua.Arena.IndInstallSpec28` (helper c) | 209 s, 4.1 GB | 6 s, 2.9 GB | `icp_spec`, same |
| `ConAgua.Arena.IndInstallSpec12` (helper c) | 106 s, 3.1 GB | 6 s, 2.8 GB | `icf_spec`, `ica_spec`, same |
| `ConAgua.Arena.IndSumSpec14` (helper b) | 223 s, 3.2 GB | 23 s, 3.0 GB | `tblW_spec`: recipe 1 (`grind (gen := 30)`) |
| `ConAgua.Arena.DefEqLeaves` (helper b) | 260 s, 3.1 GB | 14 s, 3.0 GB | `sameConstHeads_spec`, `isEagerReduce_spec`: `L.evalC_spec`, simp, per-branch model lemmas, `grind -lia -linarith` (one trivial `>>> 28` goal cost 25-30 s in `lia`, 209 s in `linarith`, not bounded by `maxHeartbeats`) |
| `ConAgua.Arena.ConstsResolveFRefine` (helper b) | 249 s, 3.2 GB | 17 s, 2.8 GB | `crf_spec`: recipe 1 with `L.evalC_spec`; `clp_spec` (79 s): one `simp_all only […]` instead of `grind` (2.5 s) |
| `ConAgua.Arena.RecCheckSpec18` (helper a) | 49 s, 9.8 GB | 18 s, 3.5 GB | `cpMem_eq`: the discharger clears the twenty `(b + k).toNat = …` facts before `omega` (PLAN memory hygiene) |
| `ConAgua.Arena.InstLPWalkGo` (helper a) | 85-167 s, 2.0 GB | 31 s | `vcgen` with `L.evalC_spec`, simp the locals and reads to `rdW`, `grind` |
| `ConAgua.Scan.Line` (helper c) | 231 s (344 s under load), 1.2 GB | 93 s under load | `lineLoop_spec`: `L.evalC_spec`/`L.evalE_spec`, `subst_vars`, simp, `grind` |
| `ConAgua.Arena.DeclDivMod2` (helper a) | 275 s, 3.1 GB | 14 s, 2.9 GB | `certCtx_specW` (straight-line code): plain `vcgen`, `rename_i`, split the callees' posts, `subst` the locals, one `simp (decide := true)`; depends on `vcgen`'s order of inaccessible names |
| `ConAgua.Arena.RecCheckSpec14` (helper a) | 297 s, 3.5 GB | 78 s, 3.0 GB | recipe on `ee_spec`/`tte_spec`/`tka_spec`, `ld64_rdW_spec` in `tka_spec`; `tka_spec`'s 11 goals still ~75 s |

## Findings

- `ProjFnShapeRef`: the same function `is_proj_fn_shape` had two specs, one in `IndRealIpf.lean`
  (`evalC_spec`, PLAN "long `&&`/`||` chain") and one here (plain `evalC`, every `&&`/`||` exit a
  path). Before writing a spec, grep for one of the same L function. Re-proving the old proof with
  `evalC_spec` alone was 130 s (three `grind`s of ~47 s); reusing the existing spec, 2 s.

- **The recipe "normalize the locals, then grind"** (`DeclCanonExpr`). After `sym only […] => vcgen
  … <;> finish`, each goal still carries the state as unsimplified chains (`({…}.setLocs [9, 10, 11,
  12] (eViewW …)).snd.loc 9`, `Cmp.ne.eval …`); `finish` works through them in the e-graph, and the
  cost grows with the arm's position in an `if t == k { … }; …` dispatch (1 s for the first arm,
  58 s for the last; 18 arms, 440 s). A plain `vcgen` followed by `all_goals (try simp only
  [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, List.headD_cons, …, Locals.init
  lemmas, Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte, …] at *)` and `all_goals grind
  [lang_grind, arena_grind, …]` closes the same goals in under 1 s each. Guarded per-arm equations
  for the model's `if` chain (PLAN) made no difference here: the cost was on the L side.

- **Lookups by `rfl` in a big program** (`FrontProgAgree`, also `LoopDeclAgree`/`LoopDeclArm*`): the
  elaborator and then the kernel compare the name with every name before it as `String`s. By
  position instead (the names are distinct): ~50 ms per lookup. Elaborating the proof term with the
  `rfl` term elaborator costs as much as the kernel check; assign the term from a tactic.

- **Second recipe, `evalE_spec` + `simp_all`** (helper c): with `ld64` in the `vcgen` set, a load's
  bound hypothesis is used inside later `arr[i]'h` terms, so `simp … at *` cannot rewrite it and
  `grind` hits instance limits; with `L.evalE_spec` the loads are `rd64` (no proofs inside) and one
  `simp_all` with the model and its continuation lemmas closes every goal. Mind
  `-UInt64.not_lt, -UInt64.not_le` where the model tests `x < y` and the L code `!(x < y)`.
  On `DeclNatDeps` the same `simp_all` looped (step limit even at 4M steps, after `subst_vars`),
  so that one stays on `grind`.
- `Scan.Line`'s `lineLoop_spec` (231 s): the time is `vcgen` itself under `sym` (130 s; plain
  `vcgen` without `sym` ran out of 4M heartbeats after 254 s), plus ~90 `finish`es of ~1 s. Open.
