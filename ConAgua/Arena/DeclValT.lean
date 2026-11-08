module

public import ConAgua.Arena.DeclRec

@[expose] public section

/-!
# `env_push`'s frame

The value checks end with `env_push`, which changes the environment; it writes the index rows,
`ECON` and `CTL[128]` only (`envPushW_frame`), so the core's memos (`CoreMemos`) stay well formed
across it.
-/

open ConRon.Arena

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/- ronsync2 stage 2: commented out (stale program / l_model / removed twin)
/-- **`env_push` writes the index rows, `ECON` and its count** (`CTL[128]`). -/
theorem envPushW_frame {m m' : Mem} {vis q : Word} {r : List Word}
    (h : envPushW m vis q = some (r, m')) :
    MemFrame [EIXA, EIXS, EIXN, ECON, EIXA1, EIXS1, EIXN1] [128] m m' := by
  sorry
-/

end L.Arena
