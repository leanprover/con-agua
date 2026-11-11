module

public import ConAgua.Arena.IndPosSpec.U4W


public import ConAgua.Arena.IndPosSpec.NestOccAny

public import ConAgua.Arena.IndPosSpec.PcrW
public import ConAgua.Arena.IndPosSpec.EntryW
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndPos2

@[expose] public section

/-!
# P2ctK1

`nestCtorsResOk_spec` (`roW`), `pcrWf`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`nest_ctors_res_ok(ctx, hi, cur)` is its model `roW`** (generated). -/
l_model nestCtorsResOk_spec (p : Prog) (hl : NoLook p) (hoa : p.lookup "nest_occ_any" = some nestOccAnyL)
    (hrh : p.lookup "nest_res_head" = some nestResHeadL) (had : AdF p)
    (hp : p.lookup "nest_ctors_res_ok" = some nestCtorsResOkL)
  fns [hp ↦ roW list]
  specs [nestResHead_spec p hrh had n, gaaF_spec p had n, nestOccAny_spec p hl hoa n]
  grind [arena_grind]

end L.Ind

namespace L.Ind

open L.Arena

/-- `nest_crest` at any exec fuel (below `3` it never returns). -/
def pcrWf : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | k + 3, m, no, nl, us, dO, dL, hO, hL, cty => pcrW k m no nl us dO dL hO hL cty
  | _, _, _, _, _, _, _, _, _, _ => none

end L.Ind

end
