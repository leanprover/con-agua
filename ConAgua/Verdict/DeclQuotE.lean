module

public import ConAgua.Arena.CheckerT
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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_decl_quot`'s error claim under `StageT`**, from `cdq_ref` through the run. -/
theorem checkDeclQuot_errT {p : Prog} (hQ : QuotProg p) (hRp : RecProg p) (hdn : DnInj dn) (hQd : QuotDn dn)
    (hnv : closedNV p L.Checker.nvFns = true) (k : ConLeche.QuotKind) (cv : IConstantVal) :
    ArmSpecE pins dn ds p "check_decl_quot" (.quotDecl k cv) := by
  intro n _ m a vis fe pend i hi hd hok0 hR hS _ hden _ _ e hc
  have hd' : ds[i.toNat] = .quotDecl k cv := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  have hcvD : ∃ c, Frontend.denoteCV a.store cv = some c := by
    obtain ⟨x, hx⟩ := hden
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
    obtain ⟨c, hc, -⟩ := hx
    exact ⟨c, hc⟩
  exact RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkDeclQuot_specE p hQ hRp n _ i vis) hnv trivial
    (cdq_ref hQ hdn n hS.stage hR.decls hi hd' hok0 (hQd.namesDn hS.twin.mem) hcvD) hc
-/

end quot

end L.Arena
