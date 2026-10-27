import ConAgua.Verdict.DeclDefnE
import ConAgua.Verdict.DeclAxiomE
import ConAgua.Verdict.DeclFoldE
import ConAgua.Verdict.DeclQuotE

/-!
# Phase A's fold: the error claim from the leaves' (lane `verdicts-b`, helper `d`)

`installFoldGo_errTop`: `install_fold_go`'s error spec (`FoldGoSpecE`, `DeclFoldE.lean`) from the
program hypotheses of the ok refinement (`LoopCallees`, `installFoldGo_refines`) and the claims of
what lies outside the declaration family:

* `CoreStubsE p`: the core stubs' error claims (`DeclValE.lean`),
* `IndArmSpecE p dn`: the inductive arm's (`check_ind_decl`),
* `NatGateSpecE p`, `DivGateSpecE p pins`: the definition arm's gates (`DeclDefnE.lean`),
* `closedNV p nvFns`: the callees outside the verdict closure claim nothing,
* `UceLookups p`: `unresolved_consts_error` and its walks at their names (`UnresolvedE.lean`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

/-- A callee of the list is outside the verdict closure: `NVAt`. -/
theorem nvAt_of_closed {p : Prog} (hnv : closedNV p L.Checker.nvFns = true) {f : FnName}
    (hf : f ∈ declNvList) : NVAt p f :=
  fun _ _ _ _ h => callE_nv hnv (declNv_mem f hf) _ _ _ h

section top
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/-- **`check_decl`'s error claim from the arms'**: the five arms by their theorems, the inductive
one by its hypothesis. -/
theorem checkDeclSpecE_of (hdc : LoopCallees dn p) (hcE : CoreStubsE p) (hia : IndArmSpecE p dn)
    (hNG : NatGateSpecE p) (hDG : DivGateSpecE p pins)
    (hnv : closedNV p L.Checker.nvFns = true) (hUL : UceLookups p) (hFD : FrontDecls ds)
    (hLD : DeclsLpsDn dn ds) :
    CheckDeclSpecE pins dn ds p := by
  have hkp : CrKeep p := ⟨hdc.indMemo, hdc.crf⟩
  have hap := hdc.cd.crp.apd
  have hU : UceProg p := ⟨hUL, strLitSupported_core p hdc.knot.knot.str⟩
  have hivE : IvgE p := ivgE_okT hdc.cvg hap hkp hnv hU
  have hnvP : NVAt p "pin_word" := nvAt_of_closed hnv (by decide +kernel)
  have hnvE : NVAt p "env_push" := nvAt_of_closed hnv (by decide +kernel)
  have hnvL : NVAt p "lvl_eq_c" := fun _ _ _ _ h =>
    callE_nv hnv (by decide +kernel) _ _ _ h
  refine checkDecl_errT pins dn ds hdc.cd.cd hdc.andInd.toIbeProg hnv ⟨?_, ?_, ?_, ?_, ?_⟩ hia hFD hLD
  · exact fun cv => checkDeclAxiom_errT pins dn ds hdc.cd.axp hdc.knot hap hkp hnv hcE hUL hdc.dninj hdc.quotDn cv
  · exact fun cv v hh => checkDeclDefn_errT pins dn ds hdc.cd.arm hdc.cd.val
      ⟨hdc.cd.df, hdc.cd.natSub, hdc.cd.natGate, hdc.cd.natCert, hdc.cd.natText,
        divGateSpecC hdc.cd.dm hdc.knot hdc.leaf hdc.cd.dgClosed (substC0_of hdc.cd.natSub.toNatSubProg)
          (substCAll_of ⟨hdc.cd.natSub.toNatSubProg, hdc.cd.dm.lSubstConstAll⟩) hkp pins⟩
      hdc.knot hdc.leaf hdc.loop hap hkp hnv hcE hUL hivE hNG hDG hdc.dninj cv v hh
  · exact fun cv v => checkDeclThm_errT pins dn ds hdc.cd.val hdc.knot hap hkp hnv hcE hUL hivE hnvP hnvL
      hnvE hdc.cd.th cv v
  · exact fun cv v => checkDeclOpaque_errT pins dn ds hdc.cd.val hdc.cd.crp hdc.knot hdc.leaf hdc.loop
      hap hkp hnv hcE hUL hivE hnvE hdc.dninj hdc.cd.op cv v
  · exact fun k cv => checkDeclQuot_errT pins dn ds hdc.cd.quot hdc.cd.val.rcp hdc.dninj hdc.quotDn hnv k cv

/-- **`install_fold_go` fails only where `installFold` does** (and `install_fold_next`), from the
leaves' error claims: the whole declaration family. -/
theorem installFoldGo_errTop (hdc : LoopCallees dn p) (hcE : CoreStubsE p) (hia : IndArmSpecE p dn)
    (hNG : NatGateSpecE p) (hDG : DivGateSpecE p pins)
    (hnv : closedNV p L.Checker.nvFns = true) (hUL : UceLookups p) (hFD : FrontDecls ds)
    (hLD : DeclsLpsDn dn ds) (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hpi : p.lookup "install_step" = some installStepL)
    (hpd : p.lookup "install_decl_step" = some installDeclStepL)
    (hpg : p.lookup "install_fold_go" = some installFoldGoL)
    (hpx : p.lookup "install_fold_next" = some installFoldNextL) (hsz : ds.size < 2 ^ 63)
    (hb : BracketProg p) (n : Nat) (hn : n ≤ 2 ^ 62) :
    FoldGoSpecE pins dn ds p n ∧ FoldNextSpecE pins dn ds p n := by
  have hkp : CrKeep p := ⟨hdc.indMemo, hdc.crf⟩
  have hap := hdc.cd.crp.apd
  have hU : UceProg p := ⟨hUL, strLitSupported_core p hdc.knot.knot.str⟩
  have hivE : IvgE p := ivgE_okT hdc.cvg hap hkp hnv hU
  have hCD := checkDeclSpecE_of pins dn ds p hdc hcE hia hNG hDG hnv hUL hFD hLD
  have hGo := installStepGo_errT pins dn ds hdc.istg hdc.iv hap hkp hnv hivE hU hCD
  have hSt := installStep_errT pins dn ds hb hpi hnv hGo
  have hDS := installDeclStep_errT pins dn ds hdc hFD hnv hpd hSt
  exact installFoldGo_refinesE pins dn ds p hpp hpn hps hpi hpd hpg hpx hsz hb hdc hFD hLD hDS n hn

end top

end L.Arena
