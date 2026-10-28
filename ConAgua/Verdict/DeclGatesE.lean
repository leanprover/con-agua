import ConAgua.Arena.Verdict
import ConAgua.Checker.NoVerdictTree
/-!
# The definition arm's gates: their callees outside the verdict closure (lane `verdicts-b`)

`gateNvList` and `nvlG`: a failing callee of the gates outside the verdict closure claims nothing.
The `Nat.div`-family pin gate's claims (`defn_div_gate` / `check_div_mod_pin*`) are in
`DeclGatesE2.lean`; the structural gate's refinement is `dng_ref` (`DeclNatGateT.lean`).
-/

open ConRon.Arena

namespace L.Arena

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

end L.Arena
