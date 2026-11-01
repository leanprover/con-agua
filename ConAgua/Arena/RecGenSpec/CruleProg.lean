module

public import ConAgua.Arena.IndRealCrF
public import ConAgua.Arena.IndRealWalk
public import ConAgua.Arena.RecGen

@[expose] public section

/-!
# CruleProg

`StageR.restrict`, `StageR.unrestrict`, `CruleProg`.
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
  ⟨⟨h.check.arena, h.check.core, h.check.pins, h.check.env.restrictTo k, h.check.mode⟩, h.iw⟩

/-- Back from a smaller view (`fe`'s own view is `vis`). -/
theorem StageR.unrestrict {dn : NIdx → Option ConLeche.Name} {vis k : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (h : StageR dn k (fe.restrictTo k.toNat) m a) (hv : fe.visibleBelow = vis.toNat) :
    StageR dn vis fe m a :=
  ⟨⟨h.check.arena, h.check.core, h.check.pins, ⟨hv, h.check.env.keys, h.check.env.vals, h.check.env.consts, h.check.env.tkeys, h.check.env.tvals, h.check.env.tables⟩, h.check.mode⟩, h.iw⟩

/-! ## `class_rule_ok` -/

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
