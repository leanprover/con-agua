module

public import ConAgua.Arena.DeclCheckT
public import ConAgua.Arena.GrindAttr

@[expose] public section

/-!
# The verdict claims of the `check_decl` arms (lane `verdicts-b`, helper `d`)

The arms' `ArmSpecE` (`Arena/CheckerT.lean`, the error half of `ArmSpecT`): the arm's failing runs
claim the twin's `checkDecl` failure. Under the hypotheses of the ok refinements and the callees' error
claims (`CoreStubsE`, `IvgE`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)
open ConRon.Bridge (FoldOK PinsDenote CheckOK StepOK)

local notation "V" => ConLeche.CheckMode.verified

section arms
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)

/-- **`check_decl_thm`'s error claim under `StageT`** (`cdt_ref`'s error half). -/
theorem checkDeclThm_errT {p : Prog} (hX : ThmArmProg p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p)
    (hC : CcvSims p dn) (hG : VerdictCtxU p) (cv : IConstantVal) (v : EIdx) :
    ArmSpecE pins dn ds p "check_decl_thm" (.thmDecl cv v) := by
  intro n hn m a vis fe i hi hd _ hR hS hF hden _ hIM e hc
  have hd' : ds[i.toNat] = .thmDecl cv v := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl] at hx
  obtain ⟨c, hcd⟩ : ∃ c, Frontend.denoteCV a.store cv = some c := by
    revert hx; cases Frontend.denoteCV a.store cv <;> simp
  exact RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkDeclThm_specE p hX n _ i vis) hG.nv hG
    (cdt_ref (pins := pins) hX hq hcl hap hkp hcrf hC hn hS hR.decls hi hd' hcd hF hIM.cr) hc

/-- **`check_decl_opaque`'s error claim under `StageT`** (`cdo_ref`'s error half). -/
theorem checkDeclOpaque_errT {p : Prog} (hX : OpqArmProg p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p)
    (hC : CcvSims p dn) (hG : VerdictCtxU p) (cv : IConstantVal) (v : EIdx) :
    ArmSpecE pins dn ds p "check_decl_opaque" (.opaqueDecl cv v) := by
  intro n hn m a vis fe i hi hd _ hR hS hF hden _ hIM e hc
  have hd' : ds[i.toNat] = .opaqueDecl cv v := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨y, hy⟩ := hden
  simp only [Frontend.denoteDecl] at hy
  obtain ⟨c, hcd⟩ : ∃ c, Frontend.denoteCV a.store cv = some c := by
    revert hy; cases Frontend.denoteCV a.store cv <;> simp
  obtain ⟨x, hx⟩ : ∃ x, denoteE a.store v = some x := by
    revert hy; rw [hcd]; cases denoteE a.store v <;> simp
  exact RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkDeclOpaque_specE p hX n _ i vis) hG.nv hG
    (cdo_ref (pins := pins) hX hq hcl hap hkp hcrf hC hn hS hR.decls hi hd' hcd hx hF hIM.cr) hc

end arms

end L.Arena
