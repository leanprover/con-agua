import ConAgua.Arena.IndPosSpec.PcrW
import ConAgua.Arena.IndPosSpec.U4W

/-!
# P2ctK1

`roK0`, `roW`, `pcrWf`, `p2ctK2`, `p2ctK1`, `p2ctW`.
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

def p2ctK2 (cR : CallM) (k : Nat) (vis no nl us dO dL hO hL hi : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => p2ctK3 cR k vis hi (pcrWf k m2 no nl us dO dL hO hL (r.headD 0))
def p2ctK1 (cR : CallM) (k : Nat) (vis no nl us dO dL hO hL cv hi : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    match nodupW k m1 (r.headD 0) (r.tail.headD 0) with
    | none => none
    | some b => if b = 0 then none
      else p2ctK2 cR k vis no nl us dO dL hO hL hi (cR k "inst_lp_fast" [CWF, r.headD 0, r.tail.headD 0, us,
        rdW (m1.arr64 EREC) (cv + 3)] m1)
/-- The model of `nest_ctors_crest(vis, namesOff, namesLen, us, dsOff, dsLen, holesOff, holesLen, cv, hi)`. -/
def p2ctW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, no, nl, us, dO, dL, hO, hL, cv, hi => p2ctK1 cR k vis no nl us dO dL hO hL cv hi (cvLpsW k m cv)

end L.Ind

end
