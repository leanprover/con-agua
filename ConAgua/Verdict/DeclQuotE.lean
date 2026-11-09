module

public import ConAgua.Arena.DeclCheckT
public import ConAgua.Arena.GrindAttr

@[expose] public section

/-!
# The verdict claim of the quotient arm `check_decl_quot`, from `cdq_ref` through the run
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt CVAt dw quotW)
open ConRon.Bridge (FoldOK PinsDenote)

local notation "V" => ConLeche.CheckMode.verified

section quot
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)

/-- **`check_decl_quot`'s error claim under `StageT`** (`cdq_ref`'s error half). -/
theorem checkDeclQuot_errT {p : Prog} (hQ : QuotArmProg p) (hQs : QuotSims p dn)
    (hnv : closedNV p L.Checker.nvFns = true) (k : ConLeche.QuotKind) (cv : IConstantVal) :
    ArmSpecE pins dn ds p "check_decl_quot" (.quotDecl k cv) := by
  intro n _ m a vis fe i hi hd hok hR hS hF hden _ _ e hc
  have hd' : ds[i.toNat] = .quotDecl k cv := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
  obtain ⟨c, hcd, -⟩ := hx
  obtain ⟨env, hF⟩ := hF
  exact RefE.run_err (s₀ := ⟨m, Locals.init []⟩)
    (checkDeclQuot_specE p hQ.cdq hQ.rcp hQ.cqr.cqr hQ.cqr.basis n _ i vis) hnv trivial
    (cdq_ref (pins := pins) hQ hQs n hS hR.decls hi hd' hok hF.check.readOK hcd) hc

end quot

end L.Arena
