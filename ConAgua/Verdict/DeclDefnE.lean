import ConAgua.Arena.CheckerT
import ConAgua.Arena.GrindAttr

/-!
# The verdict claim of the definition arm `check_decl_defn` (lane `verdicts-b`, helper `d`)

From the arm's refinement for both outcomes (`cdf_ref`, `Arena/DeclDefnT.lean`): the constant
check, the definition check and the two gates' failures claim the twin's `checkDecl` failure. The
pin gate's error claim (`DivGateSpecE`) is a hypothesis here (`dg_ref`'s error half, `DeclDivGateT.lean`).
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
theorem checkDeclDefn_errT {p : Prog} (hA : ArmProg p) (hV : ValProg p)
    (hG : DefnProgT p pins) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hlc : LoopClosed p) (hap : ApdF p) (hkp : CrKeep p)
    (hnv : closedNV p L.Checker.nvFns = true) (hcE : CoreStubsE p) (hUL : UceLookups p)
    (hivE : IvgE p) (hDG : DivGateSpecE p pins) (hdn : DnInj dn)
    (cv : IConstantVal) (v : EIdx) (hh : ConLeche.ReducibilityHint) :
    ArmSpecE pins dn ds p "check_decl_defn" (.defnDecl cv v hh) := by
  intro n hn m a vis fe pend i hi hd _ hR hS hF hden hPD hCr e hc
  have hd' : ds[i.toNat] = .defnDecl cv v hh := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨env, hfold⟩ := hF
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl] at hx
  split at hx
  rotate_left
  · cases hx
  rename_i c e' hcvd hvd
  exact RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkDeclDefn_specE p hG.df n _ i vis) trivial
    ⟨⟨⟨hnv, hcE⟩, ⟨hUL, strLitSupported_core p hq.knot.str⟩⟩, hivE, hDG⟩
    (cdf_ref hA hV hG hq hcl hlc hap hkp hdn n hn hS hR.pinsets hR.decls hi hd' hfold hcvd hvd hPD
      hCr) hc

end defn

end L.Arena
