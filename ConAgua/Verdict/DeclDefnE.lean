module

public import ConAgua.Arena.DeclCheckT
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.StrLitSup

@[expose] public section

/-!
# The verdict claim of the definition arm `check_decl_defn` (lane `verdicts-b`, helper `d`)

From the arm's refinement for both outcomes (`cdf_ref`, `Arena/DeclDefnT.lean`): the constant
check, the definition check and the two gates' failures claim the twin's `checkDecl` failure,
under `VerdictCtxU` (the gates' core calls under its `CoreStubsE`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Rom (PinSetsR)
open L.Front (DECL DLP DeclsF DeclAt CVAt dw)
open ConRon.Bridge (FoldOK PinsDenote CheckOK StepOK)

local notation "V" => ConLeche.CheckMode.verified

section defn
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)

/-- **`check_decl_defn`'s error claim under `StageT`** (`cdf_ref`'s error half). -/
theorem checkDeclDefn_errT {p : Prog} (hX : DefnProgT p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p)
    (hC : CcvSims p dn) (hdn : DnInj dn) (hG : VerdictCtxU p) (cv : IConstantVal) (v : EIdx)
    (hh : ConLeche.ReducibilityHint) :
    ArmSpecE pins dn ds p "check_decl_defn" (.defnDecl cv v hh) := by
  intro n hn m a vis fe i hi hd _ hR hS hF hden hPD hIM e hc
  have hd' : ds[i.toNat] = .defnDecl cv v hh := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨y, hy⟩ := hden
  obtain ⟨c, x, hcv, hx⟩ : ∃ c x, Frontend.denoteCV a.store cv = some c ∧
      denoteE a.store v = some x := by
    simp only [Frontend.denoteDecl] at hy
    revert hy
    cases Frontend.denoteCV a.store cv <;> cases denoteE a.store v <;> simp
  obtain ⟨env, hF⟩ := hF
  obtain ⟨pinsP, hPD⟩ := hPD
  exact RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkDeclDefn_specE p hX n _ i vis) hG.nv hG
    (cdf_ref hX hq hcl hap hkp hcrf hC hdn hn hS hR.pinsets hR.decls hi hd' hF hcv hx hPD hIM.cr) hc

end defn

end L.Arena
