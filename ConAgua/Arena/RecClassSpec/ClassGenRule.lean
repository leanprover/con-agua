import ConAgua.Arena.RecClassSpec.PrefixBinders
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

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
  grind [arena_grind] simp [rdW_eq]

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
  rw [invoke_eq _ h.ru]
  simp only [callFn, classGenRule]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    findSlot_spec p h n, opfF_spec p h.opf n, ruleBody_spec p h n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq] at *)
  all_goals grind (gen := 20) (instances := 5000) [lang_grind, arena_grind, ind_grind, rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7]

end specs

end L.Ind

end
