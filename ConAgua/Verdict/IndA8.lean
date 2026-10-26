import ConAgua.Verdict.IndA5
import ConAgua.Verdict.DeclBasisE
import ConAgua.Verdict.DeclValsE

/-!
# `check_ind_decl`'s leaf hypotheses `CheckBasisDeclE`, `CheckConstantValE` discharged (lane
`verdicts-b`, helper `ia2`)

From `cbdE_okT` (DeclBasisE.lean) and `ccvE_okT` (DeclValsE.lean, under `CoreStubsE`).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

theorem checkBasisDeclE_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) :
    CheckBasisDeclE p :=
  fun hB hC hR hpa hp _n _m _a _dn hdn _fe _vis _k hk hS hQ _e hc =>
    cbdE_okT hB hC hR hnv hpa hp hdn hk hS hQ hc

theorem checkConstantValE_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hcE : CoreStubsE p) : CheckConstantValE p := by
  intro hp hq hap hkp s₀ a₀ dn fe vis q cv hS hqd hqb hlps hCr F hF e hc
  exact ccvE_okT hq hp hap hkp hnv hcE hF hc hS hqd hqb hlps hCr

end L.Ind
