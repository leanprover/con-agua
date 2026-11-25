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
