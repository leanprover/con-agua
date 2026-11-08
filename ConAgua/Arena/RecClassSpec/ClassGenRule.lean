module

public import ConAgua.Arena.RecClassSpec.PrefixBinders
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.RecClass

@[expose] public section

/-!
# ClassGenRule

`findSlot_spec`, `gfsW`, `ruW`, `ruW_eq`, `classGenRule_spec`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

l_model findSlot_spec (p : Prog) (h : RuProg p)
  fns [h.fs ↦ gfsW list]
  specs [findSlotGo_spec p h n]
  grind [arena_grind]

/-- **The model of `class_gen_rule`.** -/
def ruW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, rco, rcl, cgo, cgl, rlvls, c, x =>
    ruK1 n g rco rcl cgo cgl rlvls x (rdW (m.arr64 IW) (g + 13))
      (gfsW n m g c (rdW (m.arr64 EREC) (rdW (m.arr64 IW) x)))

section arms2
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (next : Mem → Option (List Word × Mem))
  (g x so sl j c cn rP i v e app fvso fvsl pvo pvl rlvls xso xsl idxo idxl r t tele wso wsl rco rcl cgo cgl
    nn s fo fl ihso ihsl body sv rc fx : Word) (r1 r2 r3 r4 r5 r6 : List Word)
theorem ruW_eq : ruW (n + 1) m g rco rcl cgo cgl rlvls c x = ruK1 n g rco rcl cgo cgl rlvls x
    (rdW (m.arr64 IW) (g + 13)) (gfsW n m g c (rdW (m.arr64 EREC) (rdW (m.arr64 IW) x))) := rfl
end arms2

attribute [ind_grind] ruW_eq

section specs
variable (p : Prog) (h : RuProg p)
include h

theorem classGenRule_spec (n : Nat) (s₀ : St) (g rco rcl cgo cgl rlvls c x : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "class_gen_rule" [g, rco, rcl, cgo, cgl, rlvls, c, x]
    ⦃fun r s' => LocEq s' s₀ ∧ ruW n s₀.mem g rco rcl cgo cgl rlvls c x = some (r, s'.mem); ⊤⦄ := by
  sorry

end specs

end L.Ind

end
