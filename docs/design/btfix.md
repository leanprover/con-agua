# Lane btfix: the build-time lane's leftovers

The leftovers of `docs/design/buildtime.md` ("Left"), smallest first. Same rules: fix causes, no
heartbeats or timeouts raised, `ConAgua/Final` statements, L program text, `checker.s`,
`pins.bin` and `main.c` unchanged.

## Silent `simp_all` steps (`CkcW`, `ErToIwWStage`)

`l_model`'s `simp [lemmas]` recipe proves each step by
`vcgen … <;> (try simp_all [models, lemmas]) <;> grind`. Both modules passed
`simp [getElem_rdW']`, a lemma of `Arena.WhnfCoreProj`, which neither imports (directly or not).
`simp_all` elaborates its arguments first and throws `Unknown identifier` for it; the `try`
swallows the error, no warning remains, and `grind` alone proved every step. (Checked: the same
`simp_all [fooBarNotHere]` outside `try` is an error, under `try`/`first` nothing is reported.)

Variants, each module alone (`lake env lean`, two runs each, idle machine):

| variant | `CkcW` | `ErToIwWStage` |
|---|---:|---:|
| as on master (`simp_all` always fails) | 5.4–5.6 s | 9.1–9.3 s |
| `simp []` (`simp_all` runs, no lemma) | 4.7 s | fails (`grind`) |
| `simp [getElem_rdW']` with `WhnfCoreProj` imported | 3.9 s | 9.0–9.1 s |
| `extra [ld64_rd_spec] simp []` (loads answered as `rdW` by `vcgen`) | **3.6–3.8 s** | **9.0–9.1 s** |

Landed: the last. `ld64_rd_spec` (`Arena/LdRd.lean`) is already in both modules' imports, so no
import changes (importing `WhnfCoreProj` would have put a ~490-module subtree upstream of them;
moving the lemma to `LdRd` would rebuild ~1150 modules). The loads come out of `vcgen` as `rdW`
instead of `a[i.toNat]'h`, which is what `getElem_rdW'` was meant to rewrite.

### Finding the pattern elsewhere: `scripts/simp_scope.py`

`scripts/simp_scope.py` (after a build; ~40 s) reports every simp argument (`simp`, `simp only`,
`simp_all`, `simpa`, `dsimp`, `l_model`'s `simp [..]`) whose name is a constant declared
somewhere (project, packages, toolchain) but in none of the modules the file imports. Its query
`scripts/simp_scope.lean` reads the `.olean`s directly (no environment: some modules cannot be
imported together, e.g. `LiftBench` and `NatBits`). Name resolution is approximated: a name is in
scope if an imported constant is that name or ends with `.name`; names that also occur outside
simp lists in the file (hypotheses, binders) are skipped; `Lean.*` (builtin simprocs such as
`reduceIte`) counts as always in scope.

On master d6368206 it reports exactly the two cases above and nothing else. Not a gate (yet).

## `l_model`'s `simp` option and long `specs` (`Arena.Lift`)

The generated step proofs are text, parsed back as a tactic. `l_model` printed each spec term
with the default width (120), so a long one wrapped onto a new line at column 2, left of the
tactic it sits in (`… ; (vcgen [… mkForall_spec p … (hp.get "intern_forall")⏎  (hp.get
"mk_forall") n, ih1] <;> …)`); an application's arguments must lie right of the enclosing
tactic block's column (`checkColGt`), so the proof did not parse ("expected checkColGt"). The
`finish` recipe has the same text but was not affected in practice. Now every term is printed
on one line (`Format.pretty` with width 100000). And a `simp` lemma that is neither a binder of
the `l_model` nor a constant in scope is an error at the `l_model` (it would make every step's
`simp_all` fail silently, as in `CkcW`).

`Arena.Lift` (`liftGo_spec`), alone, two interleaved runs each:

| recipe | CPU | wall |
|---|---:|---:|
| `finish [tierW, idxW] gen 20 heartbeats 1000000` (before) | 31.2–31.7 s | 22.3–22.7 s |
| `heartbeats 1000000 simp [tierW, idxW]` | 22.0–22.6 s | 16.6–16.9 s |
| `heartbeats 1000000 simp [tierW, idxW] locals` (landed) | 20.9 s | 15.8 s |

Without `heartbeats` (the existing value, not raised) the `simp` variants run out of heartbeats
in `step1` (`lift_go`'s dispatch: `simp_all` 10.8 s of the module). The `finish` time was
`grind` (20.6 s); with `simp` it is `simp` (10.8 s) and `grind` (1.9 s).

## The inductive arm's write-set checks in one walk (`IndArmClosed`)

`IndArmClosed1`…`3` ran nine `prog_all` checks (`wsChk` per arm) over the whole `checkerProg`,
three per module: each arm's chunk checks reduced every function's `nameCode` (its UTF-8 bytes,
in the kernel) and the bodies of the functions in its set again. Now `wsChkM` checks all nine
arms on one function (`List.all` over the arms' tests), one `prog_all`
(`checkerProg_armChk`); the per-arm facts `checkerProg_arm*Chk` keep their names and follow from
it by `wsChk_of_all` (no evaluation), so `Checker.IndArm` is unchanged apart from its imports.
The name trees (their own kernel checks, ~11 s per four or five) moved to `IndArmTrees1`/`2`,
built in parallel before the check; `IndArmTests` holds `tA`/`tC`/`wsChkM`.

Experiments first (the check alone over the built trees): `List.all` over the arms 25.7 CPU-s;
a variant passing the name code once (`wsChkC … (nameCode x.1)`) 25.5 s, the same (the kernel
caches the shared reductions within one check); `nameCode` of every function alone ~4 s.

Each module alone (`lake env lean`, otherwise idle machine):

| | before | after |
|---|---:|---:|
| modules | `IndArmClosed1`/`2`/`3`: 32.4 / 22.7 / 34.4 CPU-s | `IndArmTrees1`/`2`: 11.5 / 10.9, `IndArmClosed`: 25.4 CPU-s |
| CPU | 89.5 s | 47.8 s |
| longest chain (wall) | 35 s | 11.9 + 26.0 = 38 s |

The modules are off the critical path (buildtime.md, "Left"), so the 3 s longer chain costs
nothing; the build saves ~42 CPU-s.
