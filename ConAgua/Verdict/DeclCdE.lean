import ConAgua.Arena.CheckerT
import ConAgua.Arena.GrindAttr

/-!
# The verdict claim of `check_decl` (lane `verdicts-b`, helper `d`)

`CheckDeclSpecE`, the error half of `cd_ref` (`Arena/CheckerT.lean`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt DeclAtF IndDeclAt CVAt dw decCIs)
open ConRon.Bridge (FoldOK PinsDenote CheckOK StepOK)

local notation "V" => ConLeche.CheckMode.verified

section cd
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/-- **What `check_decl` claims on failure under `StageT`** (the error half of `CheckDeclSpecT`). -/
def CheckDeclSpecE : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (i : Word), i.toNat < ds.size → ConRon.Bridge.StateOK a →
    LoopR pins dn m a vis fe pend ds → StageT dn vis fe m a →
    (∃ env, FoldOK V env fe a) → (∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x) →
    (∃ pinsP, PinsDenote a.store pins pinsP) → IndMemos m →
    ∀ e, callE p n "check_decl" [i, vis] m = .error e →
    ErrClaim (checkDecl V pins fe (dsAt ds i)) a e

/-- **`check_decl` fails only where `checkDecl` does** under `StageT`, for the front's record
kinds: the error half of `cd_ref` (each arm by its error claim, the inductive branch by
`IndArmSpecE`). -/
theorem checkDecl_errT {p : Prog} (hP : CheckDeclProg p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hlc : LoopClosed p) (hib : IbeProg p) (hin : StepIn p indFns)
    (hdn : DnInj dn) (hQd : QuotDn dn) (hia : IndArmSpec p dn) (hicl : IndMemoClosed p)
    (hcrf : L.Ind.CrfF p) (hnv : closedNV p L.Checker.nvFns = true)
    (harms : ArmsE pins dn ds p) (hiaE : IndArmSpecE p dn)
    (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) :
    CheckDeclSpecE pins dn ds p := by
  intro n hn m a vis fe pend i hi hok hR hS hF hden hPD hIM e hc
  exact RefE.run_err (checkDecl_specE p hP.cd n ⟨m, Locals.init []⟩ i vis) hnv ⟨harms, hiaE⟩
    (cd_ref hP hq hcl hlc hib hin pins dn hdn hQd hia hicl hcrf ds hFD hLD (by omega) hi hok hR hS hF hden hPD
      hIM) hc

end cd

end L.Arena
