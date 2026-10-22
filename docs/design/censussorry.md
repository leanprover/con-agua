# Lane `censussorry`: Census: proven locally vs sorry; sorry sources

Journal of lane `censussorry` (decisions, measurements, findings, open ends). Only this lane edits this file.

## Status split (2026-10-22)
`sorryAx` is searched per constant with `Expr.getUsedConstants` (memoized by name; library modules skipped); a linked theorem is `local` when its own term (aux names `proof_`/`match_`/`eq_`/`_x` mapped to their owner) has none. On master at b3519c32 all 165 sorry targets are `local`: every sorry sits in stub specs (`L.Ind.*_spec`, top: `stubM_spec` blocking 148). Census exe peak 4.4 GB, ~340 s (machine load 130).
