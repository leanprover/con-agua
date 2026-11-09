module

public import ConAgua.Arena.WhnfIotaRecRefine2

@[expose] public section
/-!
# `prepare_major`'s verdict claims (lane `verdicts-b`, helper `k2`)

No verdict site of its own: `prepare_major`'s claims are `pm_ref`'s error half
(`Arena/WhnfIotaRefine4.lean`: `major_to_ctor`'s, `lit_major_to_ctor`'s, the `whnf` slot's);
`prepareMajorE_of`: `PrepareMajorE`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

section prep
variable (p : Prog) (hp : IotaProg4 p) (hc : IotaCallees p) (hw : WhnfCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p) (hE : ErecKeptKnot p)
  (hnv : closedNV p L.Checker.nvFns = true) (hM : MajorToCtorE p)

include hp hc hw hsup hmtc hE hnv hM in
/-- **`PrepareMajorE`**: `prepare_major`'s verdicts are `major_to_ctor`'s, `lit_major_to_ctor`'s
and the `whnf` slot's (`pm_ref`'s error half). -/
theorem prepareMajorE_of : PrepareMajorE p :=
  fun n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d rec isK ro rc major rules hS hm4 hebm hmaj hr =>
    RefE.coreSpecE (pmE_spec p hp.prepareMajor (n + 1) s₀ mode vis d rec isK ro rc major) hnv
      ⟨hkE, hnv, hM⟩ (pm_ref p hp hc hw hsup hmtc hE n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d rec
        isK ro rc major rules hS hm4 hebm hmaj hr)

end prep

end L.Arena
