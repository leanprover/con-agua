module

public import ConAgua.Arena.IndPosSpec.DepthGo
public import ConAgua.Arena.IndPosSpec.CrLook
public import ConAgua.Arena.IndPosSpec.Rx
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndPos

@[expose] public section

/-!
# PcrW

`pcrW`, `nestCrest_spec`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The model of `nest_crest`** (at exec fuel `n + 3`). -/
l_model nestCrest_spec (p : Prog) (L : CrLook p)
  fns [L.cr ↦ pcrW list]
  specs [nestCanonCrest_spec p L.rx.ha L.rx.hl L.rx.hk L.ng L.np L.ip L.raf L.rap L.rgo L.rnd L.rcl L.ra L.cc n,
      posRec5_specW p L.rx.ha L.rx.h5 (n + 2), (rxSpec_all p L.rx (n + 2)).2.2.2.2.2.2.2]
  grind [arena_grind, ind_grind] pfuel 3

end L.Ind

end
