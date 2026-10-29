import ConAgua.Verdict.WhnfIotaRecE
/-!
# `iota_certs_full`'s verdict claim

`iotaCertsFullE_of` (`IotaCertsFullE`): the error half of `icfTop_ref` (`Arena/WhnfIotaRefine5`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **`IotaCertsFullE`**: `iota_certs_full`'s verdicts are the slots'. -/
theorem iotaCertsFullE_of (p : Prog) (hp : IotaProg4 p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) : IotaCertsFullE p :=
  fun n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d h ao an args hS hm4 hebm hh hargs htop =>
    RefE.coreSpecE ((icfE_spec p hp (n + 1)).2.2.2.2 s₀ mode vis d h ao an) hnv hkE
      (icfTop_ref p hp hil n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d h ao an args hS hm4 hebm hh
        hargs htop)

end L.Arena
