module

import ConAgua.Verdict.DeclDefnE
import ConAgua.Verdict.DeclArmsE
import ConAgua.Verdict.DeclAxiomE
import ConAgua.Verdict.DeclQuotE
public import ConAgua.Arena.Jobs

@[expose] public section
/-!
# The jobs: what their error arms assume, from the leaves' claims

`jobG_of`: `JobG`, what the jobs' error halves (`Arena/Jobs.lean`) assume, from the arms' error
claims (`armsE_of`, under the hypotheses of the arms' ok refinements and `VerdictCtxU`: the core
stubs' error claims, `unresolved_consts_error`'s program, the closed no-verdict callees) and the
inductive arm's (`IndArmSpecE p dn`, `check_ind_decl`).
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

/-- **`check_decl`'s arms' error claims** (`ArmsE`), from their theorems, under the hypotheses of
their ok refinements (`checkerProg_cdProgPB`'s) and the verdict context. -/
theorem armsE_of (hax : AxArmProg p) (hdf : DefnProgT p) (hth : ThmArmProg p)
    (hop : OpqArmProg p) (hqa : QuotArmProg p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hap : ApdF p) (hkp : CrKeep p) (hcrf : L.Ind.CrfF p) (hC : CcvSims p dn)
    (hQs : QuotSims p dn) (hdn : DnInj dn) (hG : VerdictCtxU p) : ArmsE pins dn ds p where
  axiom_ := checkDeclAxiom_errT pins dn ds hax hq hcl hap hkp hcrf hC hQs hdn hG
  defn := checkDeclDefn_errT pins dn ds hdf hq hcl hap hkp hcrf hC hG
  thm := checkDeclThm_errT pins dn ds hth hq hcl hap hkp hcrf hC hG
  opaque_ := checkDeclOpaque_errT pins dn ds hop hq hcl hap hkp hcrf hC hG
  quot := checkDeclQuot_errT pins dn ds hqa hQs hG.nv

/-- **What the jobs' error claims assume** (`JobG`: `check_decl`'s arms' and the inductive arm's
claims, the callees outside the verdict closure claiming nothing). -/
theorem jobG_of (hA : ArmsE pins dn ds p) (hia : IndArmSpecE p dn)
    (hnv : closedNV p L.Checker.nvFns = true) : JobG pins dn ds p :=
  ⟨⟨hA, hia⟩, hnv⟩

end top

end L.Arena
