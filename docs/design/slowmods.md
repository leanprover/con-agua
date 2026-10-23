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
| `ConAgua.Arena.DeclNatDeps` | 627 s, 4.3 GB | 146 s, 3.9 GB, then 43 s, 3.9 GB (helper a: `rdW`-valued load spec `nd_ld64_spec`, `LocEq.restore` first, `subst_vars`, `simp (decide := true)`) | `natOpDeps_specW`: plain `vcgen`, `simp only` the locals and `a[i.toNat] = rdW a i` (`nd_getElem`), `grind -lia -ring -linarith` with one guarded equation per dispatch arm (`depsArmW_k`); still ~4 s per goal (32 goals; the 15 bound hypotheses of the loads) |
| `ConAgua.Arena.RecGenSpec16` (helper c) | 241 s, 3.6 GB | 11 s, 2.8 GB | `tmm_spec`: `vcgen` with `L.evalE_spec`, `all_goals simp_all [...]`, no `grind` |
| `ConAgua.Arena.IndInstallSpec28` (helper c) | 209 s, 4.1 GB | 6 s, 2.9 GB | `icp_spec`, same |
| `ConAgua.Arena.IndInstallSpec12` (helper c) | 106 s, 3.1 GB | 6 s, 2.8 GB | `icf_spec`, `ica_spec`, same |
| `ConAgua.Arena.IndSumSpec14` (helper b) | 223 s, 3.2 GB | 23 s, 3.0 GB | `tblW_spec`: recipe 1 (`grind (gen := 30)`) |
| `ConAgua.Arena.DefEqLeaves` (helper b) | 260 s, 3.1 GB | 14 s, 3.0 GB | `sameConstHeads_spec`, `isEagerReduce_spec`: `L.evalC_spec`, simp, per-branch model lemmas, `grind -lia -linarith` (one trivial `>>> 28` goal cost 25-30 s in `lia`, 209 s in `linarith`, not bounded by `maxHeartbeats`) |
| `ConAgua.Arena.ConstsResolveFRefine` (helper b) | 249 s, 3.2 GB | 17 s, 2.8 GB | `crf_spec`: recipe 1 with `L.evalC_spec`; `clp_spec` (79 s): one `simp_all only […]` instead of `grind` (2.5 s) |
| `ConAgua.Arena.RecCheckSpec18` (helper a) | 49 s, 9.8 GB | 18 s, 3.5 GB | `cpMem_eq`: the discharger clears the twenty `(b + k).toNat = …` facts before `omega` (PLAN memory hygiene) |
| `ConAgua.Arena.InstLPWalkGo` (helper a) | 85-167 s, 2.0 GB | 31 s | `vcgen` with `L.evalC_spec`, simp the locals and reads to `rdW`, `grind` |
| `ConAgua.Scan.Line` (helper c) | 231 s (344 s under load), 1.2 GB | 73 s under load (load 70-120), 2.0 GB | `lineLoop_spec`: `L.evalC_spec`/`L.evalE_spec`, `subst_vars`, simp, `grind` |
| `ConAgua.Arena.WalkLeaves` (helper a) | 67 s (99 s under load), 1.3 GB | 51 s, 1.2 GB | `flNode_step`, `lsbNode_step`: `L.evalC_spec`, simp the locals and `rd64`/`a[i]` reads to `rdW`, `grind` |
| `ConAgua.Arena.IndRealIpf` (helper c) | 152 s | 12 s, 2.5 GB | `L.evalE_spec`/`L.evalC_spec`, `simp_all […, -UInt64.not_lt, -UInt64.not_le]`, a plain `grind` for ~7 goals |
| `ConAgua.Arena.RecCheckSpec14` round 2 (helper b) | 78 s | 17 s, 2.9 GB | `simp only [LocEq] at *` and `*` in the locals simp: the callees' `s'.loc = (…setLoc…).loc` posts rewrite the reads before `grind` |
| `ConAgua.Arena.NatShl` (helper b) | 63 s | 26 s, 1.1 GB | dropped `and_intros` (96 goals -> 218), the `St.setLoc_loc`/`Locals.init_cons_*` lemmas instead of unfolding |
| `ConAgua.Front.FieldsDeclSpec` (helper b) | 62 s (133 s under load) | 23 s, 1.4 GB | `declVal_spec`: `L.evalC_spec` for the five-way `||`, `simp only`, `grind (gen := 16)` |
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
- When the model reads memory with `rdW`, rewrite `rd64` and `a[x.toNat]` reads to `rdW` in the simp
  before `grind` (helper a); otherwise `grind` fails or splits on `rdW_eq` instances.
- `Scan.Line` (helper c): the ~60-argument callee specs were not the cost; the `||` chains were
  (`evalC` unfolded: one path per exit). With `evalC_spec`/`evalE_spec` `vcgen` takes 0.4 s for 279
  goals; then close the `≠ .brk` goals, `clear` the 60 lookups and `ih` (halves `subst_vars`),
  `subst_vars`, `rfl` the frame goals, one `simp only … at *`, `grind (splits := 40)`. Further: per-arm
  lemmas for the loop body.
- In the locals simp, pass `(config := {decide := true})`: `Var` is `Nat` behind an `abbrev`, and
  `Nat.reduceEqDiff` leaves `if 3 = 17 …` chains from `St.setLoc_loc` (DeclNatDeps).

## Final table (master 2da9604e, each module alone, 3 at a time, load ~35-70)

| module | before (s, GB) | after (s, GB) |
|---|---:|---:|
| `Arena.DeclNatDeps` | 627, 4.3 | 40, 3.8 |
| `Arena.DeclCanonExpr` | 442, 2.8 | 33, 2.6 |
| `Arena.DeclDivMod2` | 305, 3.1 | 14, 3.0 |
| `Arena.RecCheckSpec14` | 296, 3.5 | 18, 2.9 |
| `Checker.ProjFnShapeRef` | ~290 | 2, 2.5 |
| `Checker.FrontProgAgree` | 264, 4.3 | 18, 3.0 |
| `Arena.DefEqLeaves` | 255, 3.2 | 13, 3.0 |
| `Arena.ConstsResolveFRefine` | 251, 3.0 | 13, 2.8 |
| `Arena.IndSumSpec14` | 243, 3.3 | 23, 3.0 |
| `Scan.Line` | 231, 1.2 | 57, 2.1 |
| `Arena.RecGenSpec16` | 228, 3.5 | 12, 2.9 |
| `Arena.IndInstallSpec28` | 200, 4.0 | 7, 2.9 |
| `Arena.IndRealIpf` | 152, 2.6 | 9, 2.5 |
| `Arena.IndInstallSpec12` | 106, 3.1 | 5, 2.8 |
| `Arena.InstLPWalkGo` | 85, 2.0 | 23, 1.9 |
| `Arena.WalkLeaves` | 67, 1.3 | 39, 1.3 |
| `Arena.NatShl` | 63, 1.1 | 23, 1.1 |
| `Front.FieldsDeclSpec` | 62, 1.6 | 18, 1.5 |
| `Arena.RecCheckSpec18` | 49, 9.6 | 8, 3.5 |

Sum of these: 4416 s before, 401 s after. Left over 60 s / 6 GB: `IndSumSpec12` (399 s) and
`IndInstallSpec17` (112 s), indproofs4's; `AsmPart3` (371 s, 4.8 GB), `AsmPart2` (6.4 GB) and
`Checker.Prog` (79 s, 6.35 GB), generated by `scripts/checker_prog.py` (after compproofA lands:
split by cost, not by count).

## Generated files: the asm parts and `Checker.Prog`

- **Why `AsmPart3` (functions 1313–1750) took 371 s**: it held the 110 prelude copies `pre_*`
  (`preFn preTree X`). `preE` turns every input-byte read into `ldc preludeBytes i`, and compiling
  an `ldc d` computes `romIdx d tab.rom` (`isPrefixOf` of the 15 700-byte prelude against the ROM):
  ~5 s of kernel evaluation per function (`romIdx preludeBytes checkerTab.rom = 87` by `decide
  +kernel`: 5 s; three times in one declaration: still 5 s, the kernel caches it within a check).
  `preS` itself (the renaming, `nameCode` lookups) is ~1.6 s per copy; a literal body (evaluated by
  compiled code, `rfl` to `preFn preTree X`) did not help.
- **Fix**: `asm_lit_fns` takes `set_option asmLitBatch b`: the equations of `b` consecutive functions
  are one kernel check (their conjunction `name.f<j>_batch`, each `name.f<i>_eq` a projection), so
  shared work such as that `romIdx` is evaluated once per batch. `scripts/checker_prog.py` writes
  ASM_PARTS = 6 parts for the functions before the copies (batch 1, as before) and PRE_PARTS = 4
  parts for the copies (one batch each). 55 copies: 17 s in one batch, 31 s in batches of 16,
  ~180 s one by one. Batching the other functions gained nothing and cost memory.
- **Parts after compproofA's compiler** (each alone, 4 at a time): parts 0–5 34–45 s, 3.1–3.9 GB
  except part 4 (6.2 GB: `pb_check`, below); parts 6–9 (copies) 13–19 s, 4.3–5.0 GB. Before: 50–371 s,
  up to 6.55 GB.
- **`pb_check`** (function 1163, in part 4): 6.1 GB for one function. It reads the pin buffer by
  `ldc`; `romIdx` of that long string scans the ROM in the kernel. Not fixable in the generator or
  `AsmLit` (the cost is the compiler's `romIdx`); a compiler-side fix would look strings up by a
  precomputed offset table instead of `isPrefixOf` scans. Left to the compiler lane.
- **`Checker.Prog`** (79–103 s, 6.4 GB): most of it was `prog_wf checkerProg_wf` (the static check,
  55 kernel chunks). It is now its own generated module `Checker/ProgWf.lean` (imported by
  `PreludeSimProg` and `AsmFinal`, its only users), so the 30 modules importing the program no
  longer wait for it: `Prog` 24 s / 4.5 GB, `ProgWf` 57 s / 6.1 GB (chunk size 16 or 64: same).
- **ROM literals and `pb_check`** (after compproofA): measured in the kernel, `romIdx romData rom`
  14 s and `romData`-literal length 4 s with `bytesToExpr`'s balanced `++` tree of 64-byte chunks
  (each element passes ~10 appends); as `List.flatten [256-byte chunks]` 5 s and 1.4 s
  (`romIdx preludeBytes rom` 5 s -> 2 s). `bytesToExpr` (WFSplit.lean, used by `tab_lit%`) now
  writes that. `pb_check` also made the kernel compute `romData` from its encoders (6 s, 1.5 GB per
  check): it now reads `romDataLit` (`Rom/DataLit.lean`, `bytes_lit% romData`, with
  `romDataLit_eq : romDataLit = romData` by `decide +kernel` once, 12 s / 3.7 GB);
  `pbCheck_subPB` rewrites with it. Results: `pb_check` alone 6.1 -> 4.0 GB (11 s; one other
  function: 2.8 GB); `AsmPart4` 6.2 -> 4.1 GB, 27 s; `ProgWf` 6.1 -> 4.1 GB, 48 s; `Prog` 4.5 -> 3.4
  GB; the copies' parts 4.3-5.0 -> ~3.7 GB, 13 -> 9 s. What is left in `pb_check` is `romIdx`
  scanning 15 800 ROM positions before the pin data; an offset table in `Tab` (lookup instead of
  scan; touches `Compile.lean`, `WF.lean`/`WFFast.lean`'s `ldc` check and `SimExpr.lean`'s `ldc` case)
  would remove it.
