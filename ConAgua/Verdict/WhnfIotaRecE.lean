module

public import ConAgua.Arena.WhnfIotaRecRefine2

@[expose] public section

/-!
# The fire's verdict claim: `iota_rec_fire` (lane `verdicts-b`, helper `k2`)

`iotaRecFireE_of` (`IotaRecFireE`): the error half of `fire_ref` (`Arena/WhnfIotaRecRefine2`), whose
errors are `iota_rec_fire2`'s, `iota_rec_fam`'s and `iota_rec_vck`'s (`fire2_ref`, `fam_ref`,
`vck_ref`, under `FamG`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **`IotaRecFireE`**: `iota_rec_fire`'s verdicts are `iota_rec_fire2`'s (`fire_ref`'s error
half). -/
theorem iotaRecFireE_of (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p) (hw : WhnfCallees p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (hnv : closedNV p L.Checker.nvFns = true) : IotaRecFireE p :=
  fun n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj ctorP rl major sn lps rule cvj
      np nf args hS hm4 hebm hcw hus husj hmaj hlps hrule hci hfe hsa hsat hmI =>
    RefE.coreSpecE (irFireE_spec p hp.fire (n + 1) s₀ mode vis d c us recP so usj ctorP rl major) hnv
      ⟨hkE, hnv⟩
      (fire_ref p hp hc hw hEI hER hEK n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so usj
        ctorP rl major sn lps rule cvj np nf args hS hm4 hebm hcw hus husj hmaj hlps hrule hci hfe hsa
        hsat hmI)

end L.Arena
