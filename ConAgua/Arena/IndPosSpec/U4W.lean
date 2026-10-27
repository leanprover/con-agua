import ConAgua.Arena.IndPosSpec.CrLook
import ConAgua.Arena.IndPosSpec.NestOccAny
import ConAgua.Arena.IndPosSpec.NkcW
import ConAgua.Arena.IndPosSpec.PfLook
import ConAgua.Arena.IndPosSpec.RootHoles

/-!
# U4W

`cfK1`, `cfW`, `haWf`, `u4W`, `u4K`, `roK1`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

def cfK1 (k : Nat) (us dO dL gO gL ns2 aO aL kb : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 ≠ 0 then
      cfK2 ns2 aO aL kb (nagW k m1 us dO dL gO gL (rdW (m1.arr64 IW) ns2) (rdW (m1.arr64 IW) (ns2 + 1)))
    else cfK2 ns2 aO aL kb (some ([rdW (m1.arr64 IW) ns2, rdW (m1.arr64 IW) (ns2 + 1)], m1))
/-- The model of `nest_cont_new_finish(ctx, us, dsOff, dsLen, grpOff, grpLen, ns2, actOff, actLen, kb)`. -/
def cfW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, ctx, us, dO, dL, gO, gL, ns2, aO, aL, kb => cfK1 k us dO dL gO gL ns2 aO aL kb (dcWf k m ctx dO dL)

end L.Ind

namespace L.Ind

open L.Arena

def haWf : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, ctx, po, pl, i => haW k m ctx po pl i

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
