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
