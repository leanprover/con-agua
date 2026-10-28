import ConAgua.Arena.CheckerT
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# The verdict claim of the axiom arm `check_decl_axiom`, from `cda_ref` through the run
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt CVAt dw)
open ConRon.Bridge (FoldOK PinsDenote)

local notation "V" => ConLeche.CheckMode.verified

section ax
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)

/-- **`check_decl_axiom`'s error claim under `StageT`**, from `cda_ref` through the run. -/
theorem checkDeclAxiom_errT {p : Prog} (hX : AxProg p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hap : ApdF p) (hkp : CrKeep p) (hnv : closedNV p L.Checker.nvFns = true) (hcE : CoreStubsE p)
    (hUL : UceLookups p) (hdn : DnInj dn) (hQd : QuotDn dn) (cv : IConstantVal) :
    ArmSpecE pins dn ds p "check_decl_axiom" (.axiomDecl cv) := by
  intro n hn m a vis fe pend i hi hd hok hR hS hF hden _ hCr e hc
  have hd' : ds[i.toNat] = .axiomDecl cv := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
  obtain ⟨c, hcvd, -⟩ := hx
  exact RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkDeclAxiom_specE p hX n _ i vis) hnv
    ⟨⟨hnv, hcE⟩, ⟨hUL, strLitSupported_core p hq.knot.str⟩⟩
    (cda_ref hX hq hcl hap hkp hdn hQd hn hS hR.decls hi hd' hok hcvd hF hCr) hc

end ax

end L.Arena
