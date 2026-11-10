module

public import ConAgua.Arena.IndPosSpec.CrLook
public import ConAgua.Arena.IndPosSpec.NestOccAny
public import ConAgua.Arena.IndPosSpec.NkcW
public import ConAgua.Arena.IndPosSpec.PfLook
public import ConAgua.Arena.IndPosSpec.RootHoles

@[expose] public section

/-!
# U4W

`u4W`, `u4K`, `roK1`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

end L.Ind

namespace L.Ind

open L.Arena

end L.Ind

namespace L.Ind

open L.Arena

mutual
def u4W : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, ko, nF, cl, i =>
    if nF ≤ i then some ([0], m)
    else if rdW (m.arr64 IW) (ko + i) ≠ 0 then u4K n ko nF cl i (ustWf n m cl 0 i)
    else u4W n m ko nF cl (i + 1)
def u4K (n : Nat) (ko nF cl i : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (su, m1) => if su ≠ 0 then some ([1], m1) else u4W n m1 ko nF cl (i + 1)
end

end L.Ind

namespace L.Ind

open L.Arena

def roK1 (k : Nat) (ctx hi : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => roK2 (noaW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1))
      (rdW (m2.arr64 IW) (ctx + 4)) hi (r.headD 0) (r.tail.headD 0))
end L.Ind

namespace L.Ind

open L.Arena

/-- The lookups of `nest_ctors_crest`. -/
structure CtLook (p : Prog) : Prop where
  cr : CrLook p
  ha : p.lookup "iw_alloc" = some iwAlloc
  hc : p.lookup "er_copy" = some erCopy
  he : p.lookup "er_to_iw" = some erToIw
  hcv : p.lookup "cv_lps" = some cvLps
  hsc : p.lookup "sl_contains" = some slContains
  hnd : p.lookup "sl_nodup" = some slNodup
  hp : p.lookup "nest_ctors_crest" = some nestCtorsCrestL

end L.Ind

end
