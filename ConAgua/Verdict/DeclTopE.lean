module

import ConAgua.Verdict.DeclDefnE
import ConAgua.Verdict.DeclArmsE
import ConAgua.Verdict.DeclAxiomE
import ConAgua.Verdict.DeclQuotE
import ConAgua.Arena.DeclNatSubAll
import ConAgua.Arena.StrLitSup
public import ConAgua.Arena.CheckerT

@[expose] public section
/-!
# Phase A's fold: what its error arms assume, from the leaves' claims

`istgG_of`: `IstgG`, what `fold_ref`'s error half (`CheckerT.lean`) assumes, from the program
hypotheses of the ok refinement (`LoopCallees`) and the claims of what lies outside the
declaration family:

* `CoreStubsE p`: the core stubs' error claims (`DeclValE.lean`),
* `IndArmSpecE p dn`: the inductive arm's (`check_ind_decl`),
* `DivGateSpecE p pins`: the definition arm's pin gate (`DeclDefnT.lean`),
* `closedNV p nvFns`: the callees outside the verdict closure claim nothing,
* `UceLookups p`: `unresolved_consts_error` and its walks at their names (`UnresolvedE.lean`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

section top
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_decl`'s arms' error claims** (`ArmsE`), from their theorems. -/
theorem armsE_of (hdc : LoopCallees dn p) (hcE : CoreStubsE p) (hDG : DivGateSpecE p pins)
    (hnv : closedNV p L.Checker.nvFns = true) (hUL : UceLookups p) : ArmsE pins dn ds p := by
  have hkp : CrKeep p := ⟨hdc.indMemo, hdc.crf⟩
  have hap := hdc.cd.crp.apd
  have hU : UceProg p := ⟨hUL, strLitStored_core p hdc.knot.knot.str⟩
  have hivE : IvgE p := ivgE_okT hdc.cvg hap hkp hnv hU
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun cv => checkDeclAxiom_errT pins dn ds hdc.cd.axp hdc.knot hdc.leaf hap hkp hnv hcE hUL hdc.dninj hdc.quotDn cv
  · exact fun cv v hh => checkDeclDefn_errT pins dn ds hdc.cd.arm hdc.cd.val
      ⟨hdc.cd.df, hdc.cd.natSub, hdc.cd.natGate, hdc.cd.natCert, hdc.cd.natText,
        divGateSpecC hdc.cd.dm hdc.knot hdc.leaf hdc.cd.dgClosed (substC0_of hdc.cd.natSub.toNatSubProg)
          (substCAll_of ⟨hdc.cd.natSub.toNatSubProg, hdc.cd.dm.lSubstConstAll⟩) hkp pins⟩
      hdc.knot hdc.leaf hdc.loop hap hkp hnv hcE hUL hivE hDG hdc.dninj cv v hh
  · exact fun cv v => checkDeclThm_errT pins dn ds hdc.cd.val hdc.knot hap hkp hnv hcE hUL hivE
      hdc.cd.th cv v
  · exact fun cv v => checkDeclOpaque_errT pins dn ds hdc.cd.val hdc.cd.crp hdc.knot hdc.leaf hdc.loop
      hap hkp hnv hcE hUL hivE hdc.dninj hdc.cd.op cv v
  · exact fun k cv => checkDeclQuot_errT pins dn ds hdc.cd.quot hdc.cd.val.rcp hdc.dninj hdc.quotDn hnv k cv
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **What phase A's fold's error arms assume** (`IstgG`: `check_decl`'s arms' and inductive arm's
claims, `install_value`'s), from the leaves' error claims: the whole declaration family. -/
theorem istgG_of (hdc : LoopCallees dn p) (hcE : CoreStubsE p) (hia : IndArmSpecE p dn)
    (hDG : DivGateSpecE p pins) (hnv : closedNV p L.Checker.nvFns = true) (hUL : UceLookups p) :
    IstgG pins dn ds p := by
  have hU : UceProg p := ⟨hUL, strLitStored_core p hdc.knot.knot.str⟩
  exact ⟨⟨armsE_of pins dn ds p hdc hcE hDG hnv hUL, hia⟩,
    ⟨hnv, hU, ivgE_okT hdc.cvg hdc.cd.crp.apd ⟨hdc.indMemo, hdc.crf⟩ hnv hU⟩⟩
-/

end top

end L.Arena
