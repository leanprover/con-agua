import ConAgua.Arena.DeclCrpT
import ConAgua.Arena.GrindAttr

/-!
# The verdict claims of the `check_decl` arms (lane `verdicts-b`, helper `d`)

`ArmSpecE`: the error half of `ArmSpecT` (`Arena/CheckerT.lean`), the arm's failing runs claim
the twin's `checkDecl` failure. Under the hypotheses of the ok refinements and the callees' error
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

/-- **The shape of an arm's error spec** (`ArmSpecT`'s error half): a failing run of the arm on
record `d` claims the twin's `checkDecl` failure from the same state. -/
def ArmSpecE (p : Prog) (f : FnName) (d : IDeclaration) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a₀ : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (i : Word), i.toNat < ds.size → ds[i.toNat]? = some d →
    ConRon.Bridge.StateOK a₀ → LoopR pins dn m a₀ vis fe pend ds →
    StageT dn vis fe m a₀ → (∃ env, FoldOK V env fe a₀) →
    (∃ x, Frontend.denoteDecl a₀.store d = some x) → (∃ pinsP, PinsDenote a₀.store pins pinsP) →
    L.Stubs.CrOK m → ∀ e, callE p n f [i, vis] m = .error e →
    ErrClaim (checkDecl V pins fe d) a₀ e

/-- **`check_decl_thm`'s error claim under `StageT`** (`cdt_ref`'s error half). -/
theorem checkDeclThm_errT {p : Prog} (hV : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (hnv : closedNV p L.Checker.nvFns = true) (hcE : CoreStubsE p)
    (hUL : UceLookups p) (hivE : IvgE p)
    (hp : p.lookup "check_decl_thm" = some checkDeclThm) (cv : IConstantVal) (v : EIdx) :
    ArmSpecE pins dn ds p "check_decl_thm" (.thmDecl cv v) := by
  unfold ArmSpecE
  intro n hn m a vis fe pend i hi hd _ hR hS hF hden _ hCr e hc
  have hd' : ds[i.toNat] = .thmDecl cv v := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨env, hF⟩ := hF
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl] at hx
  split at hx
  rotate_left
  · cases hx
  rename_i c e' hcd he
  exact RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkDeclThm_specE p hV hp n _ i vis) hnv
    ⟨⟨⟨hnv, hcE⟩, ⟨hUL, strLitSupported_core p hq.knot.str⟩⟩, hivE⟩
    (cdt_ref (pins := pins) hV hq hap hkp hn hS hR.decls hi hd' hF hcd hCr) hc

/-- **`check_decl_opaque`'s error claim under `StageT`** (`cdo_ref`'s error half). -/
theorem checkDeclOpaque_errT {p : Prog} (hV : ValProg p) (hC : CrpProg p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hlc : LoopClosed p) (hap : ApdF p) (hkp : CrKeep p)
    (hnv : closedNV p L.Checker.nvFns = true) (hcE : CoreStubsE p) (hUL : UceLookups p)
    (hivE : IvgE p) (hdn : DnInj dn)
    (hp : p.lookup "check_decl_opaque" = some checkDeclOpaque) (cv : IConstantVal) (v : EIdx) :
    ArmSpecE pins dn ds p "check_decl_opaque" (.opaqueDecl cv v) := by
  intro n hn m a vis fe pend i hi hd _ hR hS hF hden _ hCr e hc
  have hd' : ds[i.toNat] = .opaqueDecl cv v := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨env, hF⟩ := hF
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl] at hx
  split at hx
  rotate_left
  · cases hx
  rename_i c e' hcd he
  exact RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkDeclOpaque_specE p hp n _ i vis) trivial
    ⟨⟨⟨hnv, hcE⟩, ⟨hUL, strLitSupported_core p hq.knot.str⟩⟩, hivE⟩
    (cdo_ref hV hC hq hcl hlc hap hkp hdn n hn hS hR.decls hi hd' hF hcd he hCr) hc

end arms

end L.Arena
