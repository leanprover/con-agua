module

public import ConAgua.Arena.IndPartsSpec.BlockRecNameSetOk
public import ConAgua.Arena.IndPartsSpec.BmgW
public import ConAgua.Arena.IndPartsSpec.BmoW
public import ConAgua.Arena.IndPartsSpec.BpcW
public import ConAgua.Arena.IndPartsSpec.BsoK2
public import ConAgua.Arena.IndSumSpec.ColW
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndCallM
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndParts

@[expose] public section

/-!
# Bsp

`bslW`, `brs_spec`, `brsW`, `rec7_specW`, `packMem` and the lemmas only they use.
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

/-- **`block_shape_large`'s model `bslW`** (generated). -/
l_model bsl_spec (p : Prog) (hP : IndPartsProg4 p) (hec : p.lookup "er_copy" = some erCopy)
    (het : p.lookup "er_to_iw" = some erToIw) (hseq : p.lookup "sl_eq" = some slEq)
    (hp : p.lookup "block_shape_large" = some blockShapeLarge)
  fns [hp ↦ bslW list]
  specs [erToIw_specW p hP.alloc hec het n, slEq_spec p hseq n, slContains_spec p hP.contains n]
  grind [arena_grind] finish [rdW_eq]

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


/-! ## `block_shape_recs_of` -/


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

/-! ## `block_shape_pack` -/

/-- The memory after `block_shape_pack`. -/
def packMem (m : Mem) (a b c d e f g h i : Word) : Mem :=
  let q := rdW (m.arr64 CTL) 200
  (((((((((allocMem m 9).set64 IW q a).set64 IW (q + 1) b).set64 IW (q + 2) c).set64 IW (q + 3) d).set64
    IW (q + 4) e).set64 IW (q + 5) f).set64 IW (q + 6) g).set64 IW (q + 7) h).set64 IW (q + 8) i

theorem packMem_eq (m : Mem) (a b c d e f g h i : Word) :
    packMem m a b c d e f g h i = wrIW (allocMem m 9) (rdW (m.arr64 CTL) 200) [a, b, c, d, e, f, g, h, i] := by
  simp [packMem, wrIW, UInt64.add_assoc]

theorem partsPack_eq (m : Mem) (a b c d e f g h i : Word) :
    (match allocW m 9 with | none => none | some (q, _) => some (q, packMem m a b c d e f g h i)) =
      posRecW m [a, b, c, d, e, f, g, h, i] := by
  rw [posRecW_eq m _ 9 rfl, packMem_eq]; cases allocW m 9 <;> rfl

theorem bsp_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "block_shape_pack" = some blockShapePack) (n : Nat) (s₀ : St)
    (mo ml ro rl nP elim s large isProp : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_shape_pack" [mo, ml, ro, rl, nP, elim, s, large, isProp]
    ⦃fun r s' => LocEq s' s₀ ∧
      posRecW s₀.mem [mo, ml, ro, rl, nP, elim, s, large, isProp] = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [← partsPack_eq, invoke_eq _ hp]
  simp only [callFn, blockShapePack]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish (gen := 20) [packMem, allocMem, allocW]

/-! ## `rec7` and `block_shape_recs_of` -/

/-- The memory after `rec7`. -/
def rec7Mem (m : Mem) (a b c d e f g : Word) : Mem :=
  let q := rdW (m.arr64 CTL) 200
  (((((((allocMem m 7).set64 IW q a).set64 IW (q + 1) b).set64 IW (q + 2) c).set64 IW (q + 3) d).set64
    IW (q + 4) e).set64 IW (q + 5) f).set64 IW (q + 6) g

theorem rec7Mem_eq (m : Mem) (a b c d e f g : Word) :
    rec7Mem m a b c d e f g = wrIW (allocMem m 7) (rdW (m.arr64 CTL) 200) [a, b, c, d, e, f, g] := by
  simp [rec7Mem, wrIW, UInt64.add_assoc]

theorem partsRec7_eq (m : Mem) (a b c d e f g : Word) :
    (match allocW m 7 with | none => none | some (q, _) => some (q, rec7Mem m a b c d e f g)) =
      posRecW m [a, b, c, d, e, f, g] := by
  rw [posRecW_eq m _ 7 rfl, rec7Mem_eq]; cases allocW m 7 <;> rfl

theorem rec7_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (h7 : p.lookup "rec7" = some rec7) (n : Nat) (s₀ : St) (a b c d e f g : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "rec7" [a, b, c, d, e, f, g]
    ⦃fun r s' => LocEq s' s₀ ∧ posRecW s₀.mem [a, b, c, d, e, f, g] = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [← partsRec7_eq, invoke_eq _ h7]
  simp only [callFn, rec7]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish (gen := 20) [rec7Mem, allocMem, allocW]

/-- **`block_shape_recs_of` is its model `brsW`** (generated). -/
l_model brs_spec (p : Prog) (hP : IndPartsProg4 p) (h7 : p.lookup "rec7" = some rec7)
    (hp : p.lookup "block_shape_recs_of" = some blockShapeRecsOf)
  fns [hp ↦ brsW]
  specs [recTargetOf_spec p hP.view hP.find hP.target hP.strip hP.ad n,
    rec7_specW p hP.alloc h7 n, slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [ind_grind] finish [rdW_eq] gen 20

/-! ## `block_shape_build`: the model -/

/-- **`block_shape_seal` is its model `bsealW`** (generated). -/
l_model bseal_spec (p : Prog) (hna : NaF p) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hpk : p.lookup "block_shape_pack" = some blockShapePack)
    (hp : p.lookup "block_shape_seal" = some blockShapeSeal)
  fns [hp ↦ bsealW list]
  specs [naF_spec p hna n, bsp_spec p ha hpk n]
  grind [ind_grind]


end L.Ind

end

end
