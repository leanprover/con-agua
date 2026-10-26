import ConAgua.Arena.DeclNatSpec

/-!
# `nat_op_deps` refines `natOpDeps` (lane `decls3`, helper `decls3-nat`)

Split from `DeclNatSpec.lean` for its `vcgen` spec's cost (fifteen branches). The loads go through
`nd_ld64_spec` (reads as `rdW`, no bound proofs inside terms), the state equations are substituted,
the locals normalized (`simp only`, `decide` for the `Var` literals), and `grind` closes the goals
with one guarded equation per arm of the dispatch (`depsArmW_k`); ten minutes with
`sym … <;> finish`, about 30 s now.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section deps
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-- **The grounds of each structural `Nat` operation**, as pin numbers: the operation pinned at
`i` needs the operations pinned at `is` (`natOpDeps`'s `if` chain, in its order). -/
def depsTab : List (Nat × List Nat) :=
  [(15, [15]), (16, [16]), (17, [15, 17]), (18, [16, 18]), (19, [16, 18, 19]), (20, [20]), (21, [21]),
   (22, [15, 17, 21, 22]), (23, [15, 17, 21, 23]), (24, [21, 23, 24]), (25, [16, 18, 21, 22, 23, 25]),
   (26, [16, 17, 18, 21, 22, 23, 26]), (27, [16, 18, 21, 22, 23, 27]), (28, [17, 18, 21, 28]),
   (29, [17, 21, 22, 29])]

/-- The first entry `(i, is)` of `tab` with `c = f i` gives `is.map f`; none gives `[]`. -/
def depsL (f : Nat → Word) (c : Word) : List (Nat × List Nat) → List Word
  | [] => []
  | (i, is) :: t => if c = f i then is.map f else depsL f c t

def depsW (m : Mem) (c : Word) : List Word := depsL (pinW m) c depsTab

/-- `depsL`'s allocation: the first entry `(i, is)` with `c = f i` allocates a fresh `IW` slice
holding `is.map f`; none gives `(0, 0)`. -/
def armsW (p : Prog) (n : Nat) (m1 : Mem) (f : Nat → Word) (c : Word) :
    List (Nat × List Nat) → Option (List Word × Mem)
  | [] => some ([0, 0], m1)
  | (i, is) :: t => if c = f i then
      ntBW (callW p n "iw_alloc" [UInt64.ofNat is.length] m1) fun rq mq =>
        some ([rq.headD 0, UInt64.ofNat is.length], wrIW mq (rq.headD 0) (is.map f))
    else armsW p n m1 f c t

/-- The word `j` of the pin record at `pi`. -/
def pw (m1 : Mem) (pi j : Word) : Word := rdW (m1.arr64 IW) (pi + j)

/-- `nat_op_deps` after `nat_op_pins` (the pin record at `pi`): the dispatch on `c`, as the L text
writes it (`armsW` for the proofs, `depsArmW_eq`). -/
def depsArmW (p : Prog) (n : Nat) (m1 : Mem) (pi c : Word) : Option (List Word × Mem) :=
  if c = pw m1 pi 0 then ntBW (callW p n "iw_alloc" [1] m1) fun rq mq => some ([rq.headD 0, 1], (mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 0))) else
  if c = pw m1 pi 1 then ntBW (callW p n "iw_alloc" [1] m1) fun rq mq => some ([rq.headD 0, 1], (mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1))) else
  if c = pw m1 pi 2 then ntBW (callW p n "iw_alloc" [2] m1) fun rq mq => some ([rq.headD 0, 2], ((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 0)).set64 IW (rq.headD 0 + 1) (pw m1 pi 2))) else
  if c = pw m1 pi 3 then ntBW (callW p n "iw_alloc" [2] m1) fun rq mq => some ([rq.headD 0, 2], ((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1)).set64 IW (rq.headD 0 + 1) (pw m1 pi 3))) else
  if c = pw m1 pi 4 then ntBW (callW p n "iw_alloc" [3] m1) fun rq mq => some ([rq.headD 0, 3], (((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1)).set64 IW (rq.headD 0 + 1) (pw m1 pi 3)).set64 IW (rq.headD 0 + 2) (pw m1 pi 4))) else
  if c = pw m1 pi 5 then ntBW (callW p n "iw_alloc" [1] m1) fun rq mq => some ([rq.headD 0, 1], (mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 5))) else
  if c = pw m1 pi 6 then ntBW (callW p n "iw_alloc" [1] m1) fun rq mq => some ([rq.headD 0, 1], (mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 6))) else
  if c = pw m1 pi 7 then ntBW (callW p n "iw_alloc" [4] m1) fun rq mq => some ([rq.headD 0, 4], ((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 0)).set64 IW (rq.headD 0 + 1) (pw m1 pi 2)).set64 IW (rq.headD 0 + 2) (pw m1 pi 6)).set64 IW (rq.headD 0 + 3) (pw m1 pi 7))) else
  if c = pw m1 pi 8 then ntBW (callW p n "iw_alloc" [4] m1) fun rq mq => some ([rq.headD 0, 4], ((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 0)).set64 IW (rq.headD 0 + 1) (pw m1 pi 2)).set64 IW (rq.headD 0 + 2) (pw m1 pi 6)).set64 IW (rq.headD 0 + 3) (pw m1 pi 8))) else
  if c = pw m1 pi 9 then ntBW (callW p n "iw_alloc" [3] m1) fun rq mq => some ([rq.headD 0, 3], (((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 6)).set64 IW (rq.headD 0 + 1) (pw m1 pi 8)).set64 IW (rq.headD 0 + 2) (pw m1 pi 9))) else
  if c = pw m1 pi 10 then ntBW (callW p n "iw_alloc" [6] m1) fun rq mq => some ([rq.headD 0, 6], ((((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1)).set64 IW (rq.headD 0 + 1) (pw m1 pi 3)).set64 IW (rq.headD 0 + 2) (pw m1 pi 6)).set64 IW (rq.headD 0 + 3) (pw m1 pi 7)).set64 IW (rq.headD 0 + 4) (pw m1 pi 8)).set64 IW (rq.headD 0 + 5) (pw m1 pi 10))) else
  if c = pw m1 pi 11 then ntBW (callW p n "iw_alloc" [7] m1) fun rq mq => some ([rq.headD 0, 7], (((((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1)).set64 IW (rq.headD 0 + 1) (pw m1 pi 2)).set64 IW (rq.headD 0 + 2) (pw m1 pi 3)).set64 IW (rq.headD 0 + 3) (pw m1 pi 6)).set64 IW (rq.headD 0 + 4) (pw m1 pi 7)).set64 IW (rq.headD 0 + 5) (pw m1 pi 8)).set64 IW (rq.headD 0 + 6) (pw m1 pi 11))) else
  if c = pw m1 pi 12 then ntBW (callW p n "iw_alloc" [6] m1) fun rq mq => some ([rq.headD 0, 6], ((((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1)).set64 IW (rq.headD 0 + 1) (pw m1 pi 3)).set64 IW (rq.headD 0 + 2) (pw m1 pi 6)).set64 IW (rq.headD 0 + 3) (pw m1 pi 7)).set64 IW (rq.headD 0 + 4) (pw m1 pi 8)).set64 IW (rq.headD 0 + 5) (pw m1 pi 12))) else
  if c = pw m1 pi 13 then ntBW (callW p n "iw_alloc" [4] m1) fun rq mq => some ([rq.headD 0, 4], ((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 2)).set64 IW (rq.headD 0 + 1) (pw m1 pi 3)).set64 IW (rq.headD 0 + 2) (pw m1 pi 6)).set64 IW (rq.headD 0 + 3) (pw m1 pi 13))) else
  if c = pw m1 pi 14 then ntBW (callW p n "iw_alloc" [4] m1) fun rq mq => some ([rq.headD 0, 4], ((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 2)).set64 IW (rq.headD 0 + 1) (pw m1 pi 6)).set64 IW (rq.headD 0 + 2) (pw m1 pi 7)).set64 IW (rq.headD 0 + 3) (pw m1 pi 14))) else
  some ([0, 0], m1)


def natOpDepsW (p : Prog) (n : Nat) (m : Mem) (c : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "nat_op_pins" [] m) fun rp m1 => depsArmW p n m1 (rp.headD 0) c

theorem natOpDepsW_eq (p : Prog) (n : Nat) (m : Mem) (c : Word) : natOpDepsW p n m c =
    ntBW (callW p n "nat_op_pins" [] m) fun rp m1 => depsArmW p n m1 (rp.headD 0) c := rfl

theorem depsArmW_0 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word}  (h0 : c = pw m1 pi 0) :
    depsArmW p n m1 pi c = ntBW (callW p n "iw_alloc" [1] m1) fun rq mq => some ([rq.headD 0, 1], (mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 0))) := by
  rw [depsArmW, if_pos h0]
theorem depsArmW_1 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} (h0 : c ≠ pw m1 pi 0) (h1 : c = pw m1 pi 1) :
    depsArmW p n m1 pi c = ntBW (callW p n "iw_alloc" [1] m1) fun rq mq => some ([rq.headD 0, 1], (mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1))) := by
  rw [depsArmW, if_neg h0, if_pos h1]
theorem depsArmW_2 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} (h0 : c ≠ pw m1 pi 0) (h1 : c ≠ pw m1 pi 1) (h2 : c = pw m1 pi 2) :
    depsArmW p n m1 pi c = ntBW (callW p n "iw_alloc" [2] m1) fun rq mq => some ([rq.headD 0, 2], ((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 0)).set64 IW (rq.headD 0 + 1) (pw m1 pi 2))) := by
  rw [depsArmW, if_neg h0, if_neg h1, if_pos h2]
theorem depsArmW_3 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} (h0 : c ≠ pw m1 pi 0) (h1 : c ≠ pw m1 pi 1) (h2 : c ≠ pw m1 pi 2) (h3 : c = pw m1 pi 3) :
    depsArmW p n m1 pi c = ntBW (callW p n "iw_alloc" [2] m1) fun rq mq => some ([rq.headD 0, 2], ((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1)).set64 IW (rq.headD 0 + 1) (pw m1 pi 3))) := by
  rw [depsArmW, if_neg h0, if_neg h1, if_neg h2, if_pos h3]
theorem depsArmW_4 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} (h0 : c ≠ pw m1 pi 0) (h1 : c ≠ pw m1 pi 1) (h2 : c ≠ pw m1 pi 2) (h3 : c ≠ pw m1 pi 3) (h4 : c = pw m1 pi 4) :
    depsArmW p n m1 pi c = ntBW (callW p n "iw_alloc" [3] m1) fun rq mq => some ([rq.headD 0, 3], (((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1)).set64 IW (rq.headD 0 + 1) (pw m1 pi 3)).set64 IW (rq.headD 0 + 2) (pw m1 pi 4))) := by
  rw [depsArmW, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
theorem depsArmW_5 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} (h0 : c ≠ pw m1 pi 0) (h1 : c ≠ pw m1 pi 1) (h2 : c ≠ pw m1 pi 2) (h3 : c ≠ pw m1 pi 3) (h4 : c ≠ pw m1 pi 4) (h5 : c = pw m1 pi 5) :
    depsArmW p n m1 pi c = ntBW (callW p n "iw_alloc" [1] m1) fun rq mq => some ([rq.headD 0, 1], (mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 5))) := by
  rw [depsArmW, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
theorem depsArmW_6 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} (h0 : c ≠ pw m1 pi 0) (h1 : c ≠ pw m1 pi 1) (h2 : c ≠ pw m1 pi 2) (h3 : c ≠ pw m1 pi 3) (h4 : c ≠ pw m1 pi 4) (h5 : c ≠ pw m1 pi 5) (h6 : c = pw m1 pi 6) :
    depsArmW p n m1 pi c = ntBW (callW p n "iw_alloc" [1] m1) fun rq mq => some ([rq.headD 0, 1], (mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 6))) := by
  rw [depsArmW, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]
theorem depsArmW_7 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} (h0 : c ≠ pw m1 pi 0) (h1 : c ≠ pw m1 pi 1) (h2 : c ≠ pw m1 pi 2) (h3 : c ≠ pw m1 pi 3) (h4 : c ≠ pw m1 pi 4) (h5 : c ≠ pw m1 pi 5) (h6 : c ≠ pw m1 pi 6) (h7 : c = pw m1 pi 7) :
    depsArmW p n m1 pi c = ntBW (callW p n "iw_alloc" [4] m1) fun rq mq => some ([rq.headD 0, 4], ((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 0)).set64 IW (rq.headD 0 + 1) (pw m1 pi 2)).set64 IW (rq.headD 0 + 2) (pw m1 pi 6)).set64 IW (rq.headD 0 + 3) (pw m1 pi 7))) := by
  rw [depsArmW, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]
theorem depsArmW_8 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} (h0 : c ≠ pw m1 pi 0) (h1 : c ≠ pw m1 pi 1) (h2 : c ≠ pw m1 pi 2) (h3 : c ≠ pw m1 pi 3) (h4 : c ≠ pw m1 pi 4) (h5 : c ≠ pw m1 pi 5) (h6 : c ≠ pw m1 pi 6) (h7 : c ≠ pw m1 pi 7) (h8 : c = pw m1 pi 8) :
    depsArmW p n m1 pi c = ntBW (callW p n "iw_alloc" [4] m1) fun rq mq => some ([rq.headD 0, 4], ((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 0)).set64 IW (rq.headD 0 + 1) (pw m1 pi 2)).set64 IW (rq.headD 0 + 2) (pw m1 pi 6)).set64 IW (rq.headD 0 + 3) (pw m1 pi 8))) := by
  rw [depsArmW, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_pos h8]
theorem depsArmW_9 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} (h0 : c ≠ pw m1 pi 0) (h1 : c ≠ pw m1 pi 1) (h2 : c ≠ pw m1 pi 2) (h3 : c ≠ pw m1 pi 3) (h4 : c ≠ pw m1 pi 4) (h5 : c ≠ pw m1 pi 5) (h6 : c ≠ pw m1 pi 6) (h7 : c ≠ pw m1 pi 7) (h8 : c ≠ pw m1 pi 8) (h9 : c = pw m1 pi 9) :
    depsArmW p n m1 pi c = ntBW (callW p n "iw_alloc" [3] m1) fun rq mq => some ([rq.headD 0, 3], (((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 6)).set64 IW (rq.headD 0 + 1) (pw m1 pi 8)).set64 IW (rq.headD 0 + 2) (pw m1 pi 9))) := by
  rw [depsArmW, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_pos h9]
theorem depsArmW_10 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} (h0 : c ≠ pw m1 pi 0) (h1 : c ≠ pw m1 pi 1) (h2 : c ≠ pw m1 pi 2) (h3 : c ≠ pw m1 pi 3) (h4 : c ≠ pw m1 pi 4) (h5 : c ≠ pw m1 pi 5) (h6 : c ≠ pw m1 pi 6) (h7 : c ≠ pw m1 pi 7) (h8 : c ≠ pw m1 pi 8) (h9 : c ≠ pw m1 pi 9) (h10 : c = pw m1 pi 10) :
    depsArmW p n m1 pi c = ntBW (callW p n "iw_alloc" [6] m1) fun rq mq => some ([rq.headD 0, 6], ((((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1)).set64 IW (rq.headD 0 + 1) (pw m1 pi 3)).set64 IW (rq.headD 0 + 2) (pw m1 pi 6)).set64 IW (rq.headD 0 + 3) (pw m1 pi 7)).set64 IW (rq.headD 0 + 4) (pw m1 pi 8)).set64 IW (rq.headD 0 + 5) (pw m1 pi 10))) := by
  rw [depsArmW, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_pos h10]
theorem depsArmW_11 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} (h0 : c ≠ pw m1 pi 0) (h1 : c ≠ pw m1 pi 1) (h2 : c ≠ pw m1 pi 2) (h3 : c ≠ pw m1 pi 3) (h4 : c ≠ pw m1 pi 4) (h5 : c ≠ pw m1 pi 5) (h6 : c ≠ pw m1 pi 6) (h7 : c ≠ pw m1 pi 7) (h8 : c ≠ pw m1 pi 8) (h9 : c ≠ pw m1 pi 9) (h10 : c ≠ pw m1 pi 10) (h11 : c = pw m1 pi 11) :
    depsArmW p n m1 pi c = ntBW (callW p n "iw_alloc" [7] m1) fun rq mq => some ([rq.headD 0, 7], (((((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1)).set64 IW (rq.headD 0 + 1) (pw m1 pi 2)).set64 IW (rq.headD 0 + 2) (pw m1 pi 3)).set64 IW (rq.headD 0 + 3) (pw m1 pi 6)).set64 IW (rq.headD 0 + 4) (pw m1 pi 7)).set64 IW (rq.headD 0 + 5) (pw m1 pi 8)).set64 IW (rq.headD 0 + 6) (pw m1 pi 11))) := by
  rw [depsArmW, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_pos h11]
theorem depsArmW_12 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} (h0 : c ≠ pw m1 pi 0) (h1 : c ≠ pw m1 pi 1) (h2 : c ≠ pw m1 pi 2) (h3 : c ≠ pw m1 pi 3) (h4 : c ≠ pw m1 pi 4) (h5 : c ≠ pw m1 pi 5) (h6 : c ≠ pw m1 pi 6) (h7 : c ≠ pw m1 pi 7) (h8 : c ≠ pw m1 pi 8) (h9 : c ≠ pw m1 pi 9) (h10 : c ≠ pw m1 pi 10) (h11 : c ≠ pw m1 pi 11) (h12 : c = pw m1 pi 12) :
    depsArmW p n m1 pi c = ntBW (callW p n "iw_alloc" [6] m1) fun rq mq => some ([rq.headD 0, 6], ((((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1)).set64 IW (rq.headD 0 + 1) (pw m1 pi 3)).set64 IW (rq.headD 0 + 2) (pw m1 pi 6)).set64 IW (rq.headD 0 + 3) (pw m1 pi 7)).set64 IW (rq.headD 0 + 4) (pw m1 pi 8)).set64 IW (rq.headD 0 + 5) (pw m1 pi 12))) := by
  rw [depsArmW, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_pos h12]
theorem depsArmW_13 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} (h0 : c ≠ pw m1 pi 0) (h1 : c ≠ pw m1 pi 1) (h2 : c ≠ pw m1 pi 2) (h3 : c ≠ pw m1 pi 3) (h4 : c ≠ pw m1 pi 4) (h5 : c ≠ pw m1 pi 5) (h6 : c ≠ pw m1 pi 6) (h7 : c ≠ pw m1 pi 7) (h8 : c ≠ pw m1 pi 8) (h9 : c ≠ pw m1 pi 9) (h10 : c ≠ pw m1 pi 10) (h11 : c ≠ pw m1 pi 11) (h12 : c ≠ pw m1 pi 12) (h13 : c = pw m1 pi 13) :
    depsArmW p n m1 pi c = ntBW (callW p n "iw_alloc" [4] m1) fun rq mq => some ([rq.headD 0, 4], ((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 2)).set64 IW (rq.headD 0 + 1) (pw m1 pi 3)).set64 IW (rq.headD 0 + 2) (pw m1 pi 6)).set64 IW (rq.headD 0 + 3) (pw m1 pi 13))) := by
  rw [depsArmW, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12, if_pos h13]
theorem depsArmW_14 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} (h0 : c ≠ pw m1 pi 0) (h1 : c ≠ pw m1 pi 1) (h2 : c ≠ pw m1 pi 2) (h3 : c ≠ pw m1 pi 3) (h4 : c ≠ pw m1 pi 4) (h5 : c ≠ pw m1 pi 5) (h6 : c ≠ pw m1 pi 6) (h7 : c ≠ pw m1 pi 7) (h8 : c ≠ pw m1 pi 8) (h9 : c ≠ pw m1 pi 9) (h10 : c ≠ pw m1 pi 10) (h11 : c ≠ pw m1 pi 11) (h12 : c ≠ pw m1 pi 12) (h13 : c ≠ pw m1 pi 13) (h14 : c = pw m1 pi 14) :
    depsArmW p n m1 pi c = ntBW (callW p n "iw_alloc" [4] m1) fun rq mq => some ([rq.headD 0, 4], ((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 2)).set64 IW (rq.headD 0 + 1) (pw m1 pi 6)).set64 IW (rq.headD 0 + 2) (pw m1 pi 7)).set64 IW (rq.headD 0 + 3) (pw m1 pi 14))) := by
  rw [depsArmW, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12, if_neg h13, if_pos h14]
theorem depsArmW_15 {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} (h0 : c ≠ pw m1 pi 0) (h1 : c ≠ pw m1 pi 1) (h2 : c ≠ pw m1 pi 2) (h3 : c ≠ pw m1 pi 3) (h4 : c ≠ pw m1 pi 4) (h5 : c ≠ pw m1 pi 5) (h6 : c ≠ pw m1 pi 6) (h7 : c ≠ pw m1 pi 7) (h8 : c ≠ pw m1 pi 8) (h9 : c ≠ pw m1 pi 9) (h10 : c ≠ pw m1 pi 10) (h11 : c ≠ pw m1 pi 11) (h12 : c ≠ pw m1 pi 12) (h13 : c ≠ pw m1 pi 13) (h14 : c ≠ pw m1 pi 14) :
    depsArmW p n m1 pi c = some ([0, 0], m1) := by
  rw [depsArmW, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12, if_neg h13, if_neg h14]

theorem nd_getElem (a : Array Word) (x : Word) (h : x.toNat < a.size) : a[x.toNat] = rdW a x := by
  simp [rdW, h]

/-- `ld64` answering `rdW` (a copy of `L.Arena.ld64_rdW_spec`, `InferBodyIntern.lean`, which this
module does not import): the read carries no bound proof, so the fifteen loads leave no dependent
hypotheses behind. -/
private theorem nd_ld64_spec (a : ArrId) (i : Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ ld64 a i
    ⦃fun r s' => s' = s₀ ∧ r = rdW (s₀.mem.arr64 a) i ∧ i.toNat < (s₀.mem.arr64 a).size; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs hrun
  subst hs
  simp only [ld64, StateT.run_bind, StateT.run_get, pure_bind] at hrun
  split at hrun
  · rename_i h
    simp only [pure] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨rfl, by simp [rdW, h], h⟩
  · simp [throw, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift] at hrun
    cases hrun

set_option maxHeartbeats 8000000 in
theorem natOpDeps_specW (p : Prog) (hp : p.lookup "nat_op_deps" = some natOpDepsL) (n : Nat)
    (s₀ : St) (c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_op_deps" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ natOpDepsW p n s₀.mem c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natOpDepsL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, nd_ld64_spec, st64,
    callW_spec p n "nat_op_pins", callW_spec p n "iw_alloc"]
  all_goals (try exact LocEq.restore _ _)
  all_goals subst_vars
  all_goals (try simp (config := {decide := true}) only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    St.setLocs_cons, List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil, Locals.init_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte,
    beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, nd_getElem] at *)
  all_goals grind -lia -ring -linarith (gen := 20) [lang_grind, arena_grind, natOpDepsW_eq, ntBW, pw, depsArmW_0, depsArmW_1, depsArmW_2, depsArmW_3, depsArmW_4, depsArmW_5, depsArmW_6, depsArmW_7, depsArmW_8, depsArmW_9, depsArmW_10, depsArmW_11, depsArmW_12, depsArmW_13, depsArmW_14, depsArmW_15]

theorem pw_rec {m m1 : Mem} {pi : Word} {ws : List Word} (hI : IWOK m)
    (hrec : RecPost m m1 [pi] ws) (j : Nat) (hj : j < ws.length) :
    pw m1 pi (UInt64.ofNat j) = ws[j] := by
  obtain ⟨hq, hKeep, hroom, htop, hget⟩ := hrec
  have h1 := hget j hj
  have hpi : pi.toNat = iwTop m := by simp only [List.headD_cons] at hq; rw [hq]; rfl
  have hsz := hI.2.2.1
  have hj64 : (UInt64.ofNat j).toNat = j := by
    rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hj (by show ws.length ≤ 2 ^ 64; omega))]
  have hadd : (pi + UInt64.ofNat j).toNat = iwTop m + j := by
    rw [UInt64.toNat_add, hj64, hpi]; omega
  simp only [pw, rdW, hadd]
  have h2 := hget j hj
  rw [h2]
  simp [List.getElem?_eq_getElem hj]

theorem decI_inj_iff {κ : IdxKind} {x y : Word} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) :
    ((decI x : Idx κ) = decI y) ↔ x = y :=
  ⟨fun e => (decI_eq_iff x hx _).mp e ▸ decI_word_self y hy, fun e => e ▸ rfl⟩

theorem pin_lt {m : Mem} {ps : Pins} (hF : PinsFull m ps) (i : Nat) (h1 : 1 ≤ i) (h2 : i ≤ 51) :
    (pinW m i).toNat < 2 ^ 32 := by
  have := hF.names_lt (i - 1) (by omega)
  rwa [show 1 + (i - 1) = i by omega] at this

/-- Every pin `depsTab` names is a name pin (`1 ≤ i ≤ 51`). -/
theorem depsTab_ok : ∀ x ∈ depsTab, x.2.length < 2 ^ 64 ∧ ∀ i ∈ x.2, 1 ≤ i ∧ i ≤ 51 := by decide

theorem depsL_lt {m : Mem} {ps : Pins} (hF : PinsFull m ps) (c : Word) :
    ∀ tab : List (Nat × List Nat), (∀ x ∈ tab, x.2.length < 2 ^ 64 ∧ ∀ i ∈ x.2, 1 ≤ i ∧ i ≤ 51) →
      ∀ w ∈ depsL (pinW m) c tab, w.toNat < 2 ^ 32
  | [], _ => by simp [depsL]
  | (i, is) :: t, ht => by
    simp only [depsL]
    split
    · simp only [List.mem_map]
      rintro _ ⟨j, hj, rfl⟩
      have := (ht _ List.mem_cons_self).2 j hj
      exact pin_lt hF j this.1 this.2
    · exact depsL_lt hF c t fun x hx => ht x (List.mem_cons_of_mem _ hx)

theorem depsW_lt {m : Mem} {ps : Pins} (hF : PinsFull m ps) (c : Word) :
    ∀ w ∈ depsW m c, w.toNat < 2 ^ 32 := depsL_lt hF c depsTab depsTab_ok

/-- `depsArmW` on the pin record of `m` (word `j` is pin `j + 15`) is `armsW` over `depsTab`. -/
theorem depsArmW_eq {p : Prog} {n : Nat} {m1 : Mem} {pi c : Word} {f : Nat → Word}
    (hv : ∀ j : Word, j.toNat < 15 → pw m1 pi j = f (j.toNat + 15)) :
    depsArmW p n m1 pi c = armsW p n m1 f c depsTab := by
  simp only [depsArmW, armsW, depsTab]
  simp only [List.map_cons, List.map_nil]
  simp only [List.length_cons, List.length_nil]
  simp only [wrIW]
  simp only [UInt64.add_zero]
  simp only [UInt64.add_assoc]
  simp only [UInt64.reduceAdd, Nat.reduceAdd]
  simp only [UInt64.reduceOfNat]
  simp only [hv 0 (by decide), hv 1 (by decide), hv 2 (by decide), hv 3 (by decide), hv 4 (by decide),
    hv 5 (by decide), hv 6 (by decide), hv 7 (by decide), hv 8 (by decide), hv 9 (by decide),
    hv 10 (by decide), hv 11 (by decide), hv 12 (by decide), hv 13 (by decide), hv 14 (by decide)]
  simp only [UInt64.reduceToNat, Nat.reduceAdd]

theorem natOpDeps_run {m : Mem} {a : AState} (hF : PinsFull m a.pins) {c : Word}
    (hc : c.toNat < 2 ^ 32) :
    (natOpDeps (decI c)).run a = .ok ((depsW m c).map decI, a) := by
  have hd : ∀ i, 1 ≤ i → i ≤ 51 → ((decI c : NIdx) = decI (pinW m i) ↔ c = pinW m i) :=
    fun i h1 h2 => decI_inj_iff hc (pin_lt hF i h1 h2)
  simp only [depsW, depsTab]
  simp only [depsL, List.map_cons, List.map_nil]
  simp [natOpDeps, StateT.run_bind, pinAt_run hF, exc_ok_bind', StateT.run_map, hd 15 (by decide) (by decide),
    hd 16 (by decide) (by decide), hd 17 (by decide) (by decide), hd 18 (by decide) (by decide),
    hd 19 (by decide) (by decide), hd 20 (by decide) (by decide), hd 21 (by decide) (by decide),
    hd 22 (by decide) (by decide), hd 23 (by decide) (by decide), hd 24 (by decide) (by decide),
    hd 25 (by decide) (by decide), hd 26 (by decide) (by decide), hd 27 (by decide) (by decide),
    hd 28 (by decide) (by decide), hd 29 (by decide) (by decide)]
  simp only [apply_ite (fun z => StateT.run z a), apply_ite (List.map (decI : Word → NIdx)),
    apply_ite (fun l => (Except.ok (l, a) : Except CheckError (List NIdx × AState))), StateT.run_pure,
    List.map_cons, List.map_nil]
  rfl

/-- **`armsW` keeps the stage** and answers the slice of `depsL`. -/
theorem armsW_keep (hN : NatGateProg p) {k : Nat} {m m1 m' : Mem} {a : AState} {c : Word}
    {r : List Word} (hS1 : StageR dn vis fe m1 a) (hg1 : IWGrow m m1) (hF : PinsFull m a.pins) :
    ∀ tab : List (Nat × List Nat), (∀ x ∈ tab, x.2.length < 2 ^ 64 ∧ ∀ i ∈ x.2, 1 ≤ i ∧ i ≤ 51) →
      armsW p k m1 (pinW m) c tab = some (r, m') →
      KeepPost dn vis fe (decRL (fun m => decHL m) 0) m m' a r
        ((depsL (pinW m) c tab).map (decI : Word → NIdx)) := by
  intro tab
  induction tab with
  | nil =>
    intro _ hw
    simp only [armsW, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨hS1, hg1, by simp [depsL, decRL, decHL, hslice?]⟩
  | cons x t ih =>
    obtain ⟨i, is⟩ := x
    intro ht hw
    simp only [armsW, depsL] at hw ⊢
    by_cases hci : c = pinW m i
    · rw [if_pos hci] at hw ⊢
      cases hq : callW p k "iw_alloc" [UInt64.ofNat is.length] m1 with
      | none => rw [hq] at hw; simp at hw
      | some qq =>
      obtain ⟨rq, mq⟩ := qq
      rw [hq, bW_some] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hi := ht _ List.mem_cons_self
      refine (emit_keep hN.lIwAlloc hS1 ?_ ?_ hq rfl rfl).of_grow hg1
      · rw [List.length_map, UInt64.toNat_ofNat_of_lt' hi.1]
      · simp only [List.mem_map]
        rintro _ ⟨j, hj, rfl⟩
        exact pin_lt hF j (hi.2 j hj).1 (hi.2 j hj).2
    · rw [if_neg hci] at hw ⊢
      exact ih (fun x hx => ht x (List.mem_cons_of_mem _ hx)) hw

theorem pinRecW_get (m : Mem) (i : Nat) (h : i < (pinRecW m).length) (hi : i < 15) :
    (pinRecW m)[i] = pinW m (i + 15) := by
  rcases i with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|i
  all_goals first | rfl | omega

theorem natOpDeps_ref (hN : NatGateProg p) (c : Word) :
    CallRef p "nat_op_deps" [c] (fun m a => StageR dn vis fe m a ∧ H c) (natOpDeps (decI c))
      (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mm => natOpDepsW p k mm c) (natOpDeps_specW p hN.lNatOpDeps k · c) hcall
  simp only [natOpDepsW] at hw
  cases hp : callW p k "nat_op_pins" [] m with
  | none => rw [hp] at hw; simp at hw
  | some qp =>
  obtain ⟨rp, m1⟩ := qp
  rw [hp, bW_some] at hw
  obtain ⟨h0, hrec, -, hr⟩ := natOpPins_fref hN k m rp m1 hS.2 hp
  have hrec' : RecPost m m1 [rp.headD 0] (pinRecW m) := by rw [← hr]; exact hrec
  rw [depsArmW_eq (f := pinW m) fun j hj => by
    have := pw_rec hS.2 hrec' j.toNat (by simp [pinRecW]; omega)
    rw [UInt64.ofNat_toNat] at this
    rw [this, pinRecW_get m _ _ hj]] at hw
  exact ⟨_, a, natOpDeps_run (hS.1.pins.full ‹_›) hc,
    armsW_keep hN (hrec.2.1.stage hS) hrec.2.1.1 (hS.1.pins.full ‹_›) depsTab depsTab_ok hw⟩



@[refines ConRon.Arena.natOpDeps]
theorem natOpDeps_refines (hN : NatGateProg p) (c : Word) :
    RefAM p "nat_op_deps" [c] (fun m a => StageR dn vis fe m a ∧ H c) (natOpDeps (decI c))
      (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) :=
  (natOpDeps_ref hN c).refAM

end deps

end L.Ind