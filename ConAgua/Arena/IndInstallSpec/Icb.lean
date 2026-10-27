import ConAgua.Arena.IndInstall
import ConAgua.Arena.WhnfBase
import ConAgua.Scan.Common
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# Icb

`ictlK7`, `ictrK6`, `ictrK5`, `ictrW`, `ictlK7_some`, `ictrK6_some` and the lemmas only they use.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `check_block_tail_rec` -/

def ictlK7 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
/-- After `cons_block_recs_tf`: the projection tables. -/
def ictrK6 (p : Prog) (n : Nat) (q pp : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m) => ictlK7 (callW p n "check_block_tables" [pp, rdW (m.arr64 IW) pp, rdW (m.arr64 IW) (pp + 1),
      rdW (m.arr64 IW) (q + 4), rdW (m.arr64 IW) (q + 5), rdW (m.arr64 IW) (q + 6), rdW (m.arr64 IW) (q + 7),
      r6.headD 0] m)
/-- After `check_block_rec`: the recursors consed. -/
def ictrK5 (p : Prog) (n : Nat) (q pp fe2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m) => ictrK6 p n q pp (callW p n "cons_block_recs_tf"
      [fe2, pp, 0, r5.tail.headD 0, r5.tail.tail.headD 0, r5.headD 0] m)

/-- **The model of `check_block_tail_rec(block.off, block.len, q, p, fe2, nested)`** (body fuel `n`). -/
def ictrW (p : Prog) (n : Nat) (m : Mem) (bO bL q pp fe2 nested : Word) : Option (List Word × Mem) :=
  ictrK5 p n q pp fe2 (callW p n "check_block_rec"
    [fe2, pp, nested, rdW (m.arr64 IW) (q + 12), rdW (m.arr64 IW) (q + 13), rdW (m.arr64 IW) (q + 17),
      rdW (m.arr64 IW) (q + 18), rdW (m.arr64 IW) (q + 14), rdW (m.arr64 IW) (q + 15),
      rdW (m.arr64 IW) (q + 16), bO, bL, rdW (m.arr64 IW) (q + 1), rdW (m.arr64 IW) (q + 2)] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (q pp fe2 : Word) (r : List Word)
theorem ictlK7_some : ictlK7 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem ictrK6_some : ictrK6 p n q pp (some (r, m)) = ictlK7 (callW p n "check_block_tables"
      [pp, rdW (m.arr64 IW) pp, rdW (m.arr64 IW) (pp + 1), rdW (m.arr64 IW) (q + 4), rdW (m.arr64 IW) (q + 5),
        rdW (m.arr64 IW) (q + 6), rdW (m.arr64 IW) (q + 7), r.headD 0] m) := rfl
theorem ictrK5_some : ictrK5 p n q pp fe2 (some (r, m)) = ictrK6 p n q pp
      (callW p n "cons_block_recs_tf" [fe2, pp, 0, r.tail.headD 0, r.tail.tail.headD 0, r.headD 0] m) := rfl
end arms
attribute [ind_grind] ictlK7_some ictrK6_some ictrK5_some

set_option maxHeartbeats 1600000 in
theorem ictr_spec (p : Prog) (hp : p.lookup "check_block_tail_rec" = some checkBlockTailRec) (n : Nat) (s₀ : St)
    (bO bL q pp fe2 nested : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_tail_rec" [bO, bL, q, pp, fe2, nested]
    ⦃fun r s' => LocEq s' s₀ ∧ ictrW p n s₀.mem bO bL q pp fe2 nested = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockTailRec]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "check_block_rec", callW_spec p n "cons_block_recs_tf", callW_spec p n "check_block_tables"] <;>
    finish (gen := 40) (instances := 20000) [ictrW, rdW_eq]

/-! ## `check_block_tail` -/

/-- After `block_nested_bit`: the rest. -/
def ictlK4 (p : Prog) (n : Nat) (bO bL q pp fe2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m) => ictlK7 (callW p n "check_block_tail_rec" [bO, bL, q, pp, fe2, r4.headD 0] m)
/-- After the flush: the container bit. -/
def ictlK3 (p : Prog) (n : Nat) (bO bL q pp fe2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => ictlK4 p n bO bL q pp fe2 (callW p n "block_nested_bit"
      [pp, rdW (m.arr64 IW) (q + 8), rdW (m.arr64 IW) (q + 9)] m)
/-- After `cons_block_ctors`: the flush. -/
def ictlK2 (p : Prog) (n : Nat) (bO bL q pp : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m) => ictlK3 p n bO bL q pp (r2.headD 0) (callW p n "flush_caches" [] m)
/-- After `check_block_idx_sorts`: the constructors consed. -/
def ictlK1 (p : Prog) (n : Nat) (bO bL q pp env1 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => ictlK2 p n bO bL q pp (callW p n "cons_block_ctors" [rdW (m.arr64 IW) (pp + 4),
      rdW (m.arr64 IW) (q + 4), rdW (m.arr64 IW) (q + 5), env1] m)

/-- **The model of `check_block_tail(block.off, block.len, q)`** (body fuel `n`). -/
def ictlW (p : Prog) (n : Nat) (m : Mem) (bO bL q : Word) : Option (List Word × Mem) :=
  ictlK1 p n bO bL q (rdW (m.arr64 IW) (q + 3)) (rdW (m.arr64 IW) q) (callW p n "check_block_idx_sorts"
    [rdW (m.arr64 IW) q, rdW (m.arr64 IW) (q + 3), rdW (m.arr64 IW) (rdW (m.arr64 IW) (q + 3)),
      rdW (m.arr64 IW) (rdW (m.arr64 IW) (q + 3) + 1), rdW (m.arr64 IW) (q + 1), rdW (m.arr64 IW) (q + 2)] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (bO bL q pp env1 fe2 : Word) (r : List Word)
theorem ictlK4_some : ictlK4 p n bO bL q pp fe2 (some (r, m)) =
    ictlK7 (callW p n "check_block_tail_rec" [bO, bL, q, pp, fe2, r.headD 0] m) := rfl
theorem ictlK3_some : ictlK3 p n bO bL q pp fe2 (some (r, m)) = ictlK4 p n bO bL q pp fe2
      (callW p n "block_nested_bit" [pp, rdW (m.arr64 IW) (q + 8), rdW (m.arr64 IW) (q + 9)] m) := rfl
theorem ictlK2_some : ictlK2 p n bO bL q pp (some (r, m)) =
    ictlK3 p n bO bL q pp (r.headD 0) (callW p n "flush_caches" [] m) := rfl
theorem ictlK1_some : ictlK1 p n bO bL q pp env1 (some (r, m)) =
    ictlK2 p n bO bL q pp (callW p n "cons_block_ctors" [rdW (m.arr64 IW) (pp + 4), rdW (m.arr64 IW) (q + 4),
      rdW (m.arr64 IW) (q + 5), env1] m) := rfl
end arms
attribute [ind_grind] ictlK4_some ictlK3_some ictlK2_some ictlK1_some

set_option maxHeartbeats 1600000 in
theorem ictl_spec (p : Prog) (hp : p.lookup "check_block_tail" = some checkBlockTail) (n : Nat) (s₀ : St)
    (bO bL q : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_tail" [bO, bL, q]
    ⦃fun r s' => LocEq s' s₀ ∧ ictlW p n s₀.mem bO bL q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockTail]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "check_block_idx_sorts", callW_spec p n "cons_block_ctors",
      callW_spec p n "flush_caches", callW_spec p n "block_nested_bit", callW_spec p n "check_block_tail_rec"] <;>
    finish (gen := 40) (instances := 20000) [ictlW, rdW_eq]

/-! ## `check_block` -/

def icbK9 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
/-- After the pass: the tail. -/
def icbK8 (p : Prog) (n : Nat) (bO bL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbK9 (callW p n "check_block_tail" [bO, bL, r.headD 0] m)
/-- After `block_raw_rec`: the pass. -/
def icbK7 (p : Prog) (n : Nat) (vis bO bL p0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbK8 p n bO bL (callW p n "check_block_pass" [vis, p0, r.headD 0] m)
/-- After the flush: the raw recursion bit. -/
def icbK6 (p : Prog) (n : Nat) (vis bO bL p0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => icbK7 p n vis bO bL p0 (callW p n "block_raw_rec" [p0] m)
/-- After the second `sl_nodup`: the verdict, then the flush. -/
def icbK5 (p : Prog) (n : Nat) (vis bO bL p0 nd1 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if nd1 = 0 ∨ r.headD 0 = 0 then none
    else icbK6 p n vis bO bL p0 (callW p n "flush_caches" [] m)
/-- After the first `sl_nodup`. -/
def icbK4 (p : Prog) (n : Nat) (vis bO bL p0 : Word) (r3 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbK5 p n vis bO bL p0 (r.headD 0)
      (callW p n "sl_nodup" [r3.headD 0, r3.tail.headD 0] m)
/-- After the member names. -/
def icbK3 (p : Prog) (n : Nat) (vis bO bL p0 : Word) (r2 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbK4 p n vis bO bL p0 r (callW p n "sl_nodup" [r2.headD 0, r2.tail.headD 0] m)
/-- After the constructor names. -/
def icbK2 (p : Prog) (n : Nat) (vis bO bL p0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbK3 p n vis bO bL p0 r (callW p n "block_shape_member_names" [p0] m)
/-- After the constructors. -/
def icbK1 (p : Prog) (n : Nat) (vis bO bL p0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbK2 p n vis bO bL p0 (callW p n "block_caps_ctor_names" [r.headD 0, r.tail.headD 0] m)

/-- **The model of `check_block(vis, block.off, block.len, p0)`** (body fuel `n`). -/
def icbW (p : Prog) (n : Nat) (m : Mem) (vis bO bL p0 : Word) : Option (List Word × Mem) :=
  icbK1 p n vis bO bL p0 (callW p n "block_shape_all_ctors" [p0] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis bO bL p0 nd1 : Word) (r r2 r3 : List Word)
theorem icbK9_some : icbK9 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem icbK8_some : icbK8 p n bO bL (some (r, m)) = icbK9 (callW p n "check_block_tail" [bO, bL, r.headD 0] m) :=
  rfl
theorem icbK7_some : icbK7 p n vis bO bL p0 (some (r, m)) =
    icbK8 p n bO bL (callW p n "check_block_pass" [vis, p0, r.headD 0] m) := rfl
theorem icbK6_some : icbK6 p n vis bO bL p0 (some (r, m)) =
    icbK7 p n vis bO bL p0 (callW p n "block_raw_rec" [p0] m) := rfl
theorem icbK5_dup (h : nd1 = 0 ∨ r.headD 0 = 0) : icbK5 p n vis bO bL p0 nd1 (some (r, m)) = none := by
  simp only [icbK5]; rw [ite_eq_left h]
theorem icbK5_ok (h : ¬ (nd1 = 0 ∨ r.headD 0 = 0)) : icbK5 p n vis bO bL p0 nd1 (some (r, m)) =
    icbK6 p n vis bO bL p0 (callW p n "flush_caches" [] m) := by
  simp only [icbK5]; rw [ite_eq_right h]
theorem icbK4_some : icbK4 p n vis bO bL p0 r3 (some (r, m)) = icbK5 p n vis bO bL p0 (r.headD 0)
      (callW p n "sl_nodup" [r3.headD 0, r3.tail.headD 0] m) := rfl
theorem icbK3_some : icbK3 p n vis bO bL p0 r2 (some (r, m)) =
    icbK4 p n vis bO bL p0 r (callW p n "sl_nodup" [r2.headD 0, r2.tail.headD 0] m) := rfl
theorem icbK2_some : icbK2 p n vis bO bL p0 (some (r, m)) =
    icbK3 p n vis bO bL p0 r (callW p n "block_shape_member_names" [p0] m) := rfl
theorem icbK1_some : icbK1 p n vis bO bL p0 (some (r, m)) =
    icbK2 p n vis bO bL p0 (callW p n "block_caps_ctor_names" [r.headD 0, r.tail.headD 0] m) := rfl
end arms
attribute [ind_grind] icbK9_some icbK8_some icbK7_some icbK6_some icbK5_dup icbK5_ok icbK4_some icbK3_some
  icbK2_some icbK1_some

set_option maxHeartbeats 4000000 in
theorem icb_spec (p : Prog) (hp : p.lookup "check_block" = some checkBlock) (n : Nat) (s₀ : St)
    (vis bO bL p0 : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block" [vis, bO, bL, p0]
    ⦃fun r s' => LocEq s' s₀ ∧ icbW p n s₀.mem vis bO bL p0 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlock]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "block_shape_all_ctors", callW_spec p n "block_caps_ctor_names",
      callW_spec p n "block_shape_member_names", callW_spec p n "sl_nodup", callW_spec p n "flush_caches",
      callW_spec p n "block_raw_rec", callW_spec p n "check_block_pass", callW_spec p n "check_block_tail"] <;>
    finish (gen := 40) (instances := 20000) [icbW]

end L.Ind
