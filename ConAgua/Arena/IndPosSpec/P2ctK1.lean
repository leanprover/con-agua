module

public import ConAgua.Arena.IndPosSpec.PcrW
public import ConAgua.Arena.IndPosSpec.U4W

@[expose] public section

/-!
# P2ctK1

`roK0`, `roW`, `pcrWf`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

def roK0 (k : Nat) (ctx hi cur : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => if r.headD 0 = 0 then some ([0], m1) else roK1 k ctx hi (gaaF m1 [CWF, cur])
/-- The model of `nest_ctors_res_ok(ctx, hi, cur)`. -/
def roW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | k + 1, m, ctx, hi, cur => roK0 k ctx hi cur (resHeadW m cur)

end L.Ind

namespace L.Ind

open L.Arena

/-- `nest_crest` at any exec fuel (below `3` it never returns). -/
def pcrWf : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | k + 3, m, no, nl, us, dO, dL, hO, hL, cty => pcrW k m no nl us dO dL hO hL cty
  | _, _, _, _, _, _, _, _, _, _ => none

end L.Ind

end
