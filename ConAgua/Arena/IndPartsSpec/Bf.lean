module

public import ConAgua.Arena.IndPartsSpec.IndPartsProg5
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndParts
import ConAgua.L.ModelGen

@[expose] public section

/-!
# Bf

`bsn_spec`, the models `rbaW` (`read_block_at`) and `readBlockW` (`read_block`).
-/

section


/-!
# The reader's top: `block_shape_names_of`'s spec, the models of `read_block_at`, `read_block`
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The `vcgen` specs -/

section spec
variable (p : Prog) (hP : IndPartsProg4 p)
include hP

theorem bsn_spec (hp : p.lookup "block_shape_names_of" = some blockShapeNamesOf) (n : Nat) :
    ∀ (s₀ : St) (cto ctl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_names_of" [cto, ctl]
    ⦃fun r s' => LocEq s' s₀ ∧ bsnW n s₀.mem cto ctl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ cto ctl; rw [invoke_eq _ hp]; simp only [callFn, blockShapeNamesOf]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ cto ctl
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapeNamesOf]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        slCons_specW p hP.alloc hP.copy hP.cons n, ih] <;>
      finish (gen := 20) [rdW_eq, erRd]

end spec

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The model of `read_block_at`** (at exec fuel `n + 4`). -/
l_model rba_spec (p : Prog) (hP : IndPartsProg5 p) (c : CallM) (hc : CallSpec p c)
  fns [hP.readAt ↦ rbaW list]
  specs [bsn_spec p hP.toIndPartsProg4 hP.namesOf (n + 3), bmc_spec p hP.toIndPartsProg4 (n + 2),
      erToIw_specW p hP.alloc hP.erCopy hP.erToIw (n + 3),
      flo_spec p hP.alloc hP.erCopy hP.erToIw hP.slEq hP.flo (n + 3), cpo_spec p hP.cpo (n + 3),
      clo_spec p hP.alloc hP.erCopy hP.erToIw hP.slEq hP.clo (n + 3), bt_spec p hP c hc n]
  grind [arena_grind, ind_grind] fold [erRd] finish [rdW_eq, erRd] pfuel 4

/-- **The model of `read_block`** (at exec fuel `n + 5`). -/
l_model rb_spec (p : Prog) (hP : IndPartsProg5 p) (c : CallM) (hc : CallSpec p c)
  fns [hP.read ↦ readBlockW list]
  specs [bs_spec p hP.alloc hP.copy hP.cons hP.rec3 hP.rec6 hP.recs hP.ctors hP.split (n + 4),
      rba_spec p hP c hc n]
  grind [arena_grind, ind_grind] finish [rdW_eq] pfuel 5

end L.Ind

end

end
