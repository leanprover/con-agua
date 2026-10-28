import ConAgua.Arena.DeclBasisSpec2

/-!
# `check_basis_decl`'s error claim

From its unified refinement `cbd_ref` (`Arena/DeclBasisSpec2.lean`) through the run: a duplicate
declaration rejects, the quotient block without the pinned `Eq` basis declines; the ROM readers
and `find_is` claim nothing.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_basis_decl`'s error claim**, from `cbd_ref` through the run. -/
theorem cbdE_okT {p : Prog} (hB : BasisProg p) (hC : CanonProg p) (hR : L.Rom.RomRefs p)
    (hnv : closedNV p L.Checker.nvFns = true) (hpa : p.lookup "pin_at" = some pinAtL)
    (hp : p.lookup "check_basis_decl" = some checkBasisDeclL)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m : Mem} {k : Word} {e : Err} (hk : k.toNat < 5) (hS : StageR dn vis fe m a)
    (hQ : k = 4 → ConRon.Bridge.StateOK a ∧ L.Rom.NamesDn dn a L.Rom.quotNames)
    (hc : callE p n "check_basis_decl" [vis, k] m = .error e) :
    ErrClaim (checkBasisDecl fe (basisOfW k.toNat)) a e :=
  RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkBasisDecl_specE p hB hpa hp n _ vis k) hnv trivial
    (cbd_ref hB hC hR hdn n hk hS hQ) hc

end L.Arena
