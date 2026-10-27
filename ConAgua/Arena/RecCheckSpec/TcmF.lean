import ConAgua.Arena.IndPartsSpec8
import ConAgua.Arena.RecCheckSpec.TcmLook

/-!
# TcmF

`tcmF`, `TmnLook`.
-/

noncomputable section

/-!
# `RecCheck`: `targetMajorNfs` (lane `indproofs3`, helper `rec`)

The walk's recorded constructor normal forms of a class. L (D18): the loop became the twin's list
recursion (the tail first, so the class-match calls fire from the last entry to the first), each
kept entry `sl_cons`ed onto the kept tail (a copy, so the result is a pointer slice decoded below
the tops). Callees: `ctors_have_name` (helper `recb`'s `chnW`), `target_class_match`
(`RecCheckSpec/TcmLook`), `sl_cons`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The word model -/

def tcmF (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, q, fto, ftl, pfo, pfl, us, dso, dsl, lvls, edso, edsl =>
    tcmW cR n m vis q fto ftl pfo pfl us dso dsl lvls edso edsl

/-- The lookups of `target_major_nfs`. -/
structure TmnLook (p : Prog) : Prop where
  tcm : TcmLook p
  chn : p.lookup "ctors_have_name" = some ctorsHaveName
  tmn : p.lookup "target_major_nfs" = some targetMajorNfs

end L.Ind

end
end
