import ConAgua.Arena.IndRealCrF
import ConAgua.Arena.IndRealWalk
import ConAgua.Arena.RecGen

/-!
# CruleProg

`StageR.restrict`, `StageR.unrestrict`, `cruK4`, `CruleProg`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Shared pieces -/

/-- The stage relation at a smaller view of the same index. -/
theorem StageR.restrict {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (h : StageR dn vis fe m a) (k : Word) : StageR dn k (fe.restrictTo k.toNat) m a :=
  ⟨⟨h.1.arena, h.1.core, h.1.pins, h.1.env.restrictTo k, h.1.mode⟩, h.2⟩

/-- Back from a smaller view (`fe`'s own view is `vis`). -/
theorem StageR.unrestrict {dn : NIdx → Option ConLeche.Name} {vis k : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (h : StageR dn k (fe.restrictTo k.toNat) m a) (hv : fe.visibleBelow = vis.toNat) :
    StageR dn vis fe m a :=
  ⟨⟨h.1.arena, h.1.core, h.1.pins, ⟨hv, h.1.env.keys, h.1.env.vals, h.1.env.consts, h.1.env.tkeys, h.1.env.tvals, h.1.env.tables⟩, h.1.mode⟩, h.2⟩

/-! ## `class_rule_ok` -/

def cruK4 (gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => if r4.headD 0 = 0 then none else some ([gen], m4)

/-- The lookups `class_rule_ok` needs. -/
structure CruleProg (p : Prog) : Prop extends FlushProg p where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "er_copy" = some erCopy
  eti : p.lookup "er_to_iw" = some erToIw
  lps : p.lookup "cv_lps" = some cvLps
  dom : p.lookup "class_rule_ok_domains" = some classRuleOkDomains
  guards : p.lookup "class_rule_ok_guards" = some classRuleOkGuards
  rule : p.lookup "class_rule_ok" = some classRuleOkL
  strip : StripProg p
  bvb : BvbProg p
  hf : HfF p
  hcr : CrfF p

end L.Ind

end
