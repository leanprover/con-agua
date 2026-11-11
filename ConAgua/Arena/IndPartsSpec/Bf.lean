module

public import ConAgua.Arena.IndPartsSpec.IndPartsProg5
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndParts

@[expose] public section

/-!
# Bf

`bsl_spec`, `bsn_spec` and the lemmas only they use.
-/

section


/-!
# Refinements of `IndParts`, part 13 (lane `indproofs2`, helper `parts`): `blockShape?`'s pins

The reserved-name and level-parameter pins (`block_shape_pins_formers`/`_recs`/`_ctors`/`_ok`,
pure in the twin: one `Bool`), and the eliminator (`block_shape_large`). Shared pieces: a constant's
level parameters copied by `er_to_iw` (`partsLpsCopy`), `reserved_contains` against the twin's
`reservedBasisNames` (`partsResCont`).
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

section arms
variable (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 : Word) (m : Mem) (r : List Word) (no nl : Word)
theorem bbH2_fail (h : r.headD 0 = 0) : bbH2 c n nPd cto ctl cso csl rso rsl cvT0 no nl (some (r, m)) =
    some ([0, 0], m) := by simp only [bbH2]; exact ite_eq_left h
theorem bbH2_ok (h : ¬ r.headD 0 = 0) : bbH2 c n nPd cto ctl cso csl rso rsl cvT0 no nl (some (r, m)) =
    bbH3 c n nPd cto ctl cso csl rso rsl no nl (r.tail.headD 0) (r.tail.tail.headD 0)
      (erToIwW (n + 3) m (erRd m (cvT0 + 1)) (erRd m (cvT0 + 2))) := by
  simp only [bbH2]; exact ite_eq_right h
end arms
attribute [ind_grind] bbH2_fail bbH2_ok

set_option maxHeartbeats 20000000 in
theorem bb_spec (p : Prog) (hP : IndPartsProg5 p) (c : CallM) (hc : CallSpec p c) (n : Nat) (s₀ : St) (nPd cto ctl cso csl rso rsl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 4)) "block_shape_build" [nPd, cto, ctl, cso, csl, rso, rsl]
    ⦃fun r s' => LocEq s' s₀ ∧ bbW c n s₀.mem nPd cto ctl cso csl rso rsl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.build]
  simp only [callFn, blockShapeBuild]
  sym (gen := 24) (instances := 30000) only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      bsn_spec p hP.toIndPartsProg4 hP.namesOf (n + 3), bmc_spec p hP.toIndPartsProg4 (n + 2),
      erToIw_specW p hP.alloc hP.erCopy hP.erToIw (n + 3),
      bpo_spec p hP.alloc hP.resFrom hP.resCont hP.erCopy hP.erToIw hP.slEq hP.pinsF hP.pinsR
        hP.pinsC hP.pinsOk (n + 2), bt_spec p hP c hc n] <;>
    finish (gen := 20) [bbW, rdW_eq, erRd, bbH1_some, bbH2_fail, bbH2_ok, bbH3_some, bbH4_fail, bbH4_ok, bgoK3_some]

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

theorem bsh_spec (p : Prog) (hP : IndPartsProg5 p) (c : CallM) (hc : CallSpec p c) (n : Nat) (s₀ : St) (nPd off l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 5)) "block_shape" [nPd, off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ bshW c n s₀.mem nPd off l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.shape]
  simp only [callFn, blockShape]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      bs_spec p hP.alloc hP.copy hP.cons hP.rec3 hP.rec6 hP.recs hP.ctors hP.split (n + 4),
      bb_spec p hP c hc n] <;>
    finish (gen := 20) [bshW, rdW_eq, bgoK3_some]

end L.Ind

end

end
