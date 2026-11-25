# Lane cmpfollow: follow-ups after compare2

Lane of 2026-11-25 (Opus): CmpVRoots removal, heartbeat profiling, POOL growth, a cheaper sequential bank switch (D57), tooling.

## 1. `Arena/CmpVRoots.lean` removed (17:10–17:40)

The 556-line copy of con-ron's `Bridge/Modular/Roots.lean` is gone; `Arena/CmpVCone.lean` and
`Arena/JustifyRef6.lean` use the vendored lemmas (`ConRon.Bridge.Modular.{NSeen, XRel,
names_exact, expr_exact, const_exact, table_exact}`). The vendored module failed at four sites, all
the toolchain's `do` elaborator (no `pure () >>=` left; as patch 0002): patch
`con-ron/0004-modular-roots-do.patch` (an `AM.bind_ok`/`AM.pure_ok`/`subst` triple dropped at
three sites, a `dsimp`/`simp` made `try`). Its imports `Modular.Rel` and `Modular.Worker` build
unpatched; the lakefile's `ConRonBridge` globs list the three modules (the rest of
`Bridge.Modular` stays out). Gates 16/16 OK.

## 2. `Final/CmpA.lean`, `Final/CmpC.lean` under the default `maxHeartbeats` (17:16–17:30)

Profiled with `-Dprofiler=true` and `trace.profiler` (`lake env lean`, one file at a time):

| file | before (limit, file wall) | after (limit, file wall) |
|---|---|---|
| `CmpA` | 1 600 000, 3.70 s (proof 3.20 s) | default, 1.62 s (proof 1.18 s) |
| `CmpC` | 3 200 000, 2.82 s | default, 2.82 s (no change needed) |

`CmpA`: 2.02 s of the proof was one `rw [← Code.label (i := 147) hC rfl]` (turning `at_ (Kc + 147)`
back into `label abiCmpDoneL` in a goal whose machine state is large: the rewrite abstracts over the
whole goal). Replaced by `Eq.mp (congrArg (Ev _ _) (Code.label …))` inside the `ev_congr`, no
rewrite. `CmpC` already elaborates under the default limit (1.7 s tactics, 2.0 s kernel: the
`hC.get (i := N) rfl` lookups into the stub list); its raised limit was a leftover.
