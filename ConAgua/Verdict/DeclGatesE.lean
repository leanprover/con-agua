import ConAgua.Verdict.DeclDefnE
import ConAgua.Arena.GrindAttr
/-!
# The verdict claims of the definition arm's gates (lane `verdicts-b`, helper `d`)

`defn_nat_gate`'s (the structural-`Nat` gate: `dng_ref`'s error half, `DeclNatGateT.lean`); the
`Nat.div`-family pin gate's (`defn_div_gate` / `check_div_mod_pin*` / `check_type_pins` /
`check_div_mod_certs`) are in `DeclGatesE2.lean`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Rom (PinSetsR)
open ConRon.Bridge (FoldOK PinsDenote CheckOK StepOK)

local notation "V" => ConLeche.CheckMode.verified

/-- The gates' callees outside the verdict closure. -/
def gateNvList : List FnName :=
  ["nat_op_equations", "subst_const0_pairs", "subst_const0", "subst_const_all", "subst_const0_list",
   "div_mod_env_guard", "div_mod_pin_guard", "div_mod_certs_guard", "div_mod_cert_guard",
   "div_mod_cert_applied", "div_mod_cert_stmts", "div_mod_cert_proofs", "div_mod_type_pins",
   "div_mod_decl_pin", "type_pin_stored", "ground_guards", "nat_op_guard", "nat_op_deps",
   "nat_op_stored_ok_all", "nat_op_names", "sl_contains", "env_find", "rom_pin_sets",
   "nat_div_mod_names", "env_push", "pin_word", "pin_at"]

theorem gateNv_mem : ∀ f ∈ gateNvList, f ∈ L.Checker.nvFns :=
  _root_.L.Checker.nv_sub (by decide +kernel)

/-- A failing callee of the gates' list claims nothing. -/
theorem nvlG {p : Prog} (hnv : closedNV p L.Checker.nvFns = true) {α : Type} {T : AM α}
    {a : AState} {f : FnName} (hf : f ∈ gateNvList) {n : Nat} {vs : List Word} {m : Mem} {e : Err}
    (h : callE p n f vs m = .error e) : ErrClaim T a e :=
  ErrClaim.of_callE_nv hnv (gateNv_mem f hf) h

/-- **`defn_nat_gate`'s error claim** (`NatGateSpecE`). -/
theorem natGateSpecE_of {p : Prog} (hN : NatSubProg' p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hcE : CoreStubsE p) (hnv : closedNV p L.Checker.nvFns = true)
    (hg : p.lookup "defn_nat_gate" = some defnNatGate)
    (hc : p.lookup "defn_nat_cert" = some defnNatCert) : NatGateSpecE p :=
  fun _dn _vis _w _fe2 _env _env2 _n _nm k hk m _a hn hSw hC henv hie hnm _e hcall =>
    RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (defnNatGate_specE p hg hc k _ _ _ _) hnv hcE
      (dng_ref hN hq hcl k hk hn hSw hC henv hie hnm) hcall

end L.Arena
