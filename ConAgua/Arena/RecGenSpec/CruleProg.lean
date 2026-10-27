import ConAgua.Arena.IndRealCrF
import ConAgua.Arena.DeclCvg

/-!
# CruleProg

`StageR.restrict`, `StageR.unrestrict`, `crgK4`, `crgK3`, `crgK2`, `crgK1` and the lemmas only they use.
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

def crgK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => if r4.headD 0 = 0 then none else some ([0], m4)

def crgK3 (visR gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => if r3.headD 0 = 0 then none else crgK4 (crfF m3 [visR, gen])

def crgK2 (cR : CallM) (N : Nat) (visR gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    crgK3 visR gen (cR N "all_level_params_defined" [r2.headD 0, r2.tail.headD 0, gen] m2)

def crgK1 (cR : CallM) (N : Nat) (visR cvR gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if r1.headD 0 ≠ 0 then none else crgK2 cR N visR gen (L.Arena.cvLpsW N m1 cvR)

def crgK0 (cR : CallM) (N : Nat) (visR cvR gen : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r0, m0) =>
    if r0.headD 0 = 0 then none else crgK1 cR N visR cvR gen (hffF m0 [CWF, gen])

/-- **The model of `class_rule_ok_guards`** (`all_level_params_defined` read through `cR`). -/
def crgW (cR : CallM) : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | N + 1, m, visR, cvR, gen => crgK0 cR N visR cvR gen (lbbF m [CWF, 0, gen])

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
