import ConAgua.Arena.IndInstall
import ConAgua.Arena.WhnfBase
import ConAgua.Scan.Common
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# Icp

`bpMem`, `icprK`, `icprW`, `icpr_spec`, `icpK8`, `icpK7` and the lemmas only they use.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `check_block_pass` -/

/-- The memory after the record's nineteen writes (`q` the allocation). -/
def bpMem (m : Mem) (q fe1 cO cL p1 aO aL sO sL kO kL nO nL pO pL rd mO mL tO tL : Word) : Mem :=
  ((((((((((((((((((m.set64 IW q fe1).set64 IW (q + 1) cO).set64 IW (q + 2) cL).set64 IW (q + 3) p1
    ).set64 IW (q + 4) aO).set64 IW (q + 5) aL).set64 IW (q + 6) sO).set64 IW (q + 7) sL
    ).set64 IW (q + 8) kO).set64 IW (q + 9) kL).set64 IW (q + 10) nO).set64 IW (q + 11) nL
    ).set64 IW (q + 12) pO).set64 IW (q + 13) pL).set64 IW (q + 14) rd).set64 IW (q + 15) mO
    ).set64 IW (q + 16) mL).set64 IW (q + 17) tO).set64 IW (q + 18) tL

/-! ### `check_block_pass_rec` -/

def icprK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

/-- **The model of `check_block_pass_rec(…)`** (body fuel `n`): the allocation, then the writes. -/
def icprW (p : Prog) (n : Nat) (m : Mem) (fe1 cO cL p1 aO aL sO sL kO kL nO nL pO pL rd mO mL tO tL : Word) :
    Option (List Word × Mem) :=
  match callW p n "iw_alloc" [19] m with
  | none => none
  | some (rq, m1) => some ([rq.headD 0], bpMem m1 (rq.headD 0) fe1 cO cL p1 aO aL sO sL kO kL nO nL pO pL rd
      mO mL tO tL)

set_option maxHeartbeats 1600000 in
theorem icpr_spec (p : Prog) (hp : p.lookup "check_block_pass_rec" = some checkBlockPassRec) (n : Nat)
    (s₀ : St) (fe1 cO cL p1 aO aL sO sL kO kL nO nL pO pL rd mO mL tO tL : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_pass_rec"
      [fe1, cO, cL, p1, aO, aL, sO, sL, kO, kL, nO, nL, pO, pL, rd, mO, mL, tO, tL]
    ⦃fun r s' => LocEq s' s₀ ∧ icprW p n s₀.mem fe1 cO cL p1 aO aL sO sL kO kL nO nL pO pL rd mO mL tO tL =
      some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockPassRec]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, callW_spec p n "iw_alloc"] <;>
    finish (gen := 20) [icprW, bpMem]

/-! ### `check_block_pass` -/

/-- After `nest_seeds`: the record. -/
def icpK8 (p : Prog) (n : Nat) (r1 r3 r4 r5 r6 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r8, m) => icprK (callW p n "check_block_pass_rec"
      [r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0, r1.tail.tail.tail.headD 0, r3.headD 0,
        r3.tail.headD 0, r3.tail.tail.headD 0, r3.tail.tail.tail.headD 0, r6.headD 0, r6.tail.headD 0,
        r6.tail.tail.headD 0, r6.tail.tail.tail.headD 0, rdW (m.arr64 IW) (r4.headD 0 + 7),
        rdW (m.arr64 IW) (r4.headD 0 + 8), r5.headD 0, r5.tail.headD 0, r5.tail.tail.headD 0,
        rdW (m.arr64 IW) (r8.headD 0 + 4), rdW (m.arr64 IW) (r8.headD 0 + 5)] m)
/-- After `class_seeds`: `nest_seeds`. -/
def icpK7 (p : Prog) (n : Nat) (r1 r3 r4 r5 r6 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r7, m) => icpK8 p n r1 r3 r4 r5 r6 (callW p n "nest_seeds"
      [r1.headD 0, r4.headD 0, r7.headD 0, r7.tail.headD 0, r6.tail.tail.tail.tail.headD 0] m)
/-- After `check_block_positivity`: `class_seeds`. -/
def icpK6 (p : Prog) (n : Nat) (r1 r3 r4 r5 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m) => icpK7 p n r1 r3 r4 r5 r6 (callW p n "class_seeds"
      [r4.headD 0, r4.tail.headD 0, r4.tail.tail.headD 0, r5.tail.headD 0, r5.tail.tail.headD 0] m)
/-- After `check_block_classes`: `check_block_positivity`. -/
def icpK5 (p : Prog) (n : Nat) (r1 r3 r4 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m) => icpK6 p n r1 r3 r4 r5 (callW p n "check_block_positivity"
      [r1.headD 0, r1.tail.tail.tail.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0, r3.headD 0,
        r3.tail.headD 0] m)
/-- After `block_nest_ctx`: `check_block_classes` (the parameters read off the context). -/
def icpK4 (p : Prog) (n : Nat) (r1 r3 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m) => icpK5 p n r1 r3 r4 (callW p n "check_block_classes"
      [r1.headD 0, r1.tail.tail.tail.headD 0, rdW (m.arr64 IW) (r4.headD 0 + 7),
        rdW (m.arr64 IW) (r4.headD 0 + 8), r3.headD 0, r3.tail.headD 0] m)
/-- After `check_block_ctors`: `block_nest_ctx`. -/
def icpK3 (p : Prog) (n : Nat) (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m) => icpK4 p n r1 r3 (callW p n "block_nest_ctx"
      [r1.headD 0, r1.tail.tail.tail.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0] m)
/-- After the flush: `check_block_ctors` at the formers' environment (the members read off `p1`). -/
def icpK2 (p : Prog) (n : Nat) (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => icpK3 p n r1 (callW p n "check_block_ctors"
      [r1.headD 0, r1.headD 0, r1.tail.tail.tail.headD 0, rdW (m.arr64 IW) (r1.tail.tail.tail.headD 0),
        rdW (m.arr64 IW) (r1.tail.tail.tail.headD 0 + 1), r1.tail.headD 0, r1.tail.tail.headD 0] m)
/-- After `check_block_inds`: the flush. -/
def icpK1 (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m) => icpK2 p n r1 (callW p n "flush_caches" [] m)

/-- **The model of `check_block_pass(vis, p0, isRec)`** (body fuel `n`). -/
def icpW (p : Prog) (n : Nat) (m : Mem) (vis p0 isRec : Word) : Option (List Word × Mem) :=
  icpK1 p n (callW p n "check_block_inds" [vis, p0, isRec] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (r r1 r3 r4 r5 r6 r8 : List Word)
theorem icprK_some : icprK (some (r, m)) = some ([r.headD 0], m) := rfl
theorem icpK8_some : icpK8 p n r1 r3 r4 r5 r6 (some (r, m)) = icprK (callW p n "check_block_pass_rec"
      [r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0, r1.tail.tail.tail.headD 0, r3.headD 0,
        r3.tail.headD 0, r3.tail.tail.headD 0, r3.tail.tail.tail.headD 0, r6.headD 0, r6.tail.headD 0,
        r6.tail.tail.headD 0, r6.tail.tail.tail.headD 0, rdW (m.arr64 IW) (r4.headD 0 + 7),
        rdW (m.arr64 IW) (r4.headD 0 + 8), r5.headD 0, r5.tail.headD 0, r5.tail.tail.headD 0,
        rdW (m.arr64 IW) (r.headD 0 + 4), rdW (m.arr64 IW) (r.headD 0 + 5)] m) := rfl
theorem icpK7_some : icpK7 p n r1 r3 r4 r5 r6 (some (r, m)) = icpK8 p n r1 r3 r4 r5 r6 (callW p n "nest_seeds"
      [r1.headD 0, r4.headD 0, r.headD 0, r.tail.headD 0, r6.tail.tail.tail.tail.headD 0] m) := rfl
theorem icpK6_some : icpK6 p n r1 r3 r4 r5 (some (r, m)) = icpK7 p n r1 r3 r4 r5 r (callW p n "class_seeds"
      [r4.headD 0, r4.tail.headD 0, r4.tail.tail.headD 0, r5.tail.headD 0, r5.tail.tail.headD 0] m) := rfl
theorem icpK5_some : icpK5 p n r1 r3 r4 (some (r, m)) = icpK6 p n r1 r3 r4 r (callW p n "check_block_positivity"
      [r1.headD 0, r1.tail.tail.tail.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0, r3.headD 0,
        r3.tail.headD 0] m) := rfl
theorem icpK4_some : icpK4 p n r1 r3 (some (r, m)) = icpK5 p n r1 r3 r (callW p n "check_block_classes"
      [r1.headD 0, r1.tail.tail.tail.headD 0, rdW (m.arr64 IW) (r.headD 0 + 7),
        rdW (m.arr64 IW) (r.headD 0 + 8), r3.headD 0, r3.tail.headD 0] m) := rfl
theorem icpK3_some : icpK3 p n r1 (some (r, m)) = icpK4 p n r1 r (callW p n "block_nest_ctx"
      [r1.headD 0, r1.tail.tail.tail.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0] m) := rfl
theorem icpK2_some : icpK2 p n r1 (some (r, m)) = icpK3 p n r1 (callW p n "check_block_ctors"
      [r1.headD 0, r1.headD 0, r1.tail.tail.tail.headD 0, rdW (m.arr64 IW) (r1.tail.tail.tail.headD 0),
        rdW (m.arr64 IW) (r1.tail.tail.tail.headD 0 + 1), r1.tail.headD 0, r1.tail.tail.headD 0] m) := rfl
theorem icpK1_some : icpK1 p n (some (r, m)) = icpK2 p n r (callW p n "flush_caches" [] m) := rfl
end arms
attribute [ind_grind] icprK_some icpK8_some icpK7_some icpK6_some icpK5_some icpK4_some icpK3_some
  icpK2_some icpK1_some

set_option maxHeartbeats 1600000 in
theorem icp_spec (p : Prog) (hp : p.lookup "check_block_pass" = some checkBlockPass) (n : Nat) (s₀ : St)
    (vis p0 isRec : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_pass" [vis, p0, isRec]
    ⦃fun r s' => LocEq s' s₀ ∧ icpW p n s₀.mem vis p0 isRec = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockPass]
  vcgen [exec, step, L.evalE_spec, evalC, evalArgs, setLoc, setLocs,
    callW_spec p n "check_block_inds", callW_spec p n "flush_caches", callW_spec p n "check_block_ctors",
    callW_spec p n "block_nest_ctx", callW_spec p n "check_block_classes",
    callW_spec p n "check_block_positivity", callW_spec p n "class_seeds", callW_spec p n "nest_seeds",
    callW_spec p n "check_block_pass_rec"]
  all_goals simp_all [LocEq, Expr.pval, L.Arena.rd64_rdWC, BinOp.eval, St.setLocs_cons, St.setLoc_loc,
    St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr,
    icpW, icprK_some, icpK8_some, icpK7_some, icpK6_some, icpK5_some, icpK4_some, icpK3_some,
    icpK2_some, icpK1_some]

end L.Ind
