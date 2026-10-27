import ConAgua.Arena.IndPosSpec.NoConstWf
import ConAgua.Arena.RecCheckSpec.ErToIwWStage

/-!
# NestOccAny

`noaW`, `noaK`, `noaW_nil`, `noaW_cons`, `noaK_hit`, `noaK_miss` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_occ_any`: `xs.anyM (nestOcc names lo hi ·)` -/

mutual
def noaW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, no, nl, lo, hi, off, l =>
    if l = 0 then some ([0], m) else noaK k no nl lo hi off l (noConstWf k m no nl lo hi (rdW (m.arr64 IW) off))
def noaK (k : Nat) (no nl lo hi off l : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (b, m1) => if b ≠ 0 then some ([1], m1) else noaW k m1 no nl lo hi (off + 1) (l - 1)
end

section arms
variable (k : Nat) (m m1 : Mem) (no nl lo hi off l b : Word)
theorem noaW_nil (h : l = 0) : noaW (k + 1) m no nl lo hi off l = some ([0], m) := by simp [noaW, h]
theorem noaW_cons (h : ¬ l = 0) : noaW (k + 1) m no nl lo hi off l =
    noaK k no nl lo hi off l (noConstWf k m no nl lo hi (rdW (m.arr64 IW) off)) := by simp [noaW, h]
theorem noaK_hit (h : b ≠ 0) : noaK k no nl lo hi off l (some (b, m1)) = some ([1], m1) := by rw [noaK, ite_eq_left h]
theorem noaK_miss (h : ¬ b ≠ 0) : noaK k no nl lo hi off l (some (b, m1)) =
    noaW k m1 no nl lo hi (off + 1) (l - 1) := by rw [noaK, ite_eq_right h]
end arms
attribute [ind_grind] noaW_nil noaW_cons noaK_hit noaK_miss

theorem nestOccAny_spec (p : Prog) (hl : NoLook p) (hp : p.lookup "nest_occ_any" = some nestOccAnyL)
    (k : Nat) : ∀ (s₀ : St) (no nl lo hi off ln : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_occ_any" [no, nl, lo, hi, off, ln]
    ⦃fun r s' => LocEq s' s₀ ∧ noaW k s₀.mem no nl lo hi off ln = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ no nl lo hi off ln
    rw [invoke_eq _ hp]; simp only [callFn, nestOccAnyL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ no nl lo hi off ln
    simp only [invoke_eq _ hp, callFn, nestOccAnyL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, nestOcc_spec' p hl k, ih] <;>
      finish (gen := 20) [Locals.init_cons_zero]

def ntyK6 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) => if r6.headD 0 = 0 then none else some ([r6.tail.headD 0], m6)
def ntyK5 (k : Nat) (key : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => ntyK6 (instW k m5 (rdW (m5.arr64 IW) (key + 2)) (rdW (m5.arr64 IW) (key + 3)) (r5.headD 0))
def ntyK4 (cR : CallM) (k : Nat) (key cvC : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => ntyK5 k key (cR k "inst_lp_fast" [CWF, r4.headD 0, r4.tail.headD 0,
      rdW (m4.arr64 IW) (key + 1), rdW (m4.arr64 EREC) (cvC + 3)] m4)
def ntyK3 (cR : CallM) (k : Nat) (key cvC : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => if r3.headD 0 = 0 then none else ntyK4 cR k key cvC (cvLpsW k m3 cvC)
def ntyK1 (cR : CallM) (k : Nat) (key : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then none
    else if rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3 then none
    else if lsNodeW m1 (rdW (m1.arr64 IW) (key + 1)) = [] then none
    else if (lsNodeW m1 (rdW (m1.arr64 IW) (key + 1))).tail.headD 0 ≠
        rdW (m1.arr64 EREC) (r.tail.headD 0 + 1 + 2) then none
    else ntyK3 cR k key (r.tail.headD 0 + 1) (stripF 6 m1 [rdW (m1.arr64 IW) (key + 3),
      rdW (m1.arr64 EREC) (r.tail.headD 0 + 1 + 3)])
/-- The model of `nest_inst_type_ty(vis, key)` at exec fuel `k + 1` (its `inst_lp_fast` read through
`cR`). -/
def ntyW (cR : CallM) (k : Nat) (m : Mem) (vis key : Word) : Option (List Word × Mem) :=
  ntyK1 cR k key (envFindW m (rdW (m.arr64 IW) key) vis)

section arms
variable (cR : CallM) (k : Nat) (m1 m3 m4 m5 m6 : Mem) (key cvC : Word) (r r3 r4 r5 r6 : List Word)
theorem ntyK6_some (h : ¬ r6.headD 0 = 0) : ntyK6 (some (r6, m6)) = some ([r6.tail.headD 0], m6) := by
  rw [ntyK6, ite_eq_right h]
theorem ntyK5_some : ntyK5 k key (some (r5, m5)) =
    ntyK6 (instW k m5 (rdW (m5.arr64 IW) (key + 2)) (rdW (m5.arr64 IW) (key + 3)) (r5.headD 0)) := rfl
theorem ntyK4_some : ntyK4 cR k key cvC (some (r4, m4)) = ntyK5 k key (cR k "inst_lp_fast" [CWF, r4.headD 0,
    r4.tail.headD 0, rdW (m4.arr64 IW) (key + 1), rdW (m4.arr64 EREC) (cvC + 3)] m4) := rfl
theorem ntyK3_some (h : ¬ r3.headD 0 = 0) : ntyK3 cR k key cvC (some (r3, m3)) = ntyK4 cR k key cvC (cvLpsW k m3 cvC) := by
  rw [ntyK3, ite_eq_right h]
theorem ntyK1_eq (r : List Word) (m1 : Mem) : ntyK1 cR k key (some (r, m1)) =
    if r.headD 0 = 0 then none
    else if rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3 then none
    else if lsNodeW m1 (rdW (m1.arr64 IW) (key + 1)) = [] then none
    else if (lsNodeW m1 (rdW (m1.arr64 IW) (key + 1))).tail.headD 0 ≠
        rdW (m1.arr64 EREC) (r.tail.headD 0 + 1 + 2) then none
    else ntyK3 cR k key (r.tail.headD 0 + 1) (stripF 6 m1 [rdW (m1.arr64 IW) (key + 3),
      rdW (m1.arr64 EREC) (r.tail.headD 0 + 1 + 3)]) := rfl
end arms
attribute [ind_grind] ntyK6_some ntyK5_some ntyK4_some ntyK3_some ntyK1_eq

/-- `nest_inst_type_ty` at any exec fuel. -/
def ntyWf (cR : CallM) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, vis, key => ntyW cR k m vis key

def nitK5 (ty : Word) (rs : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => if r5.headD 0 = 0 then none else some ([rs.getD 1 0, ty], m5)
def nitK4 (cR : CallM) (k : Nat) (ctx ty : Word) (rs v : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if r4.headD 0 ≠ 0 then none else nitK5 ty rs (lveC cR k m4 (v.tail.headD 0) (rdW (m4.arr64 IW) (ctx + 9)))
def nitK2 (cR : CallM) (k : Nat) (ctx hi ty : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rs, m2) =>
    if eViewW m2 (rs.getD 2 0) = [] then none
    else if (eViewW m2 (rs.getD 2 0)).headD 0 ≠ 2 then none
    else nitK4 cR k ctx ty rs (eViewW m2 (rs.getD 2 0))
      (noaW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4)) hi
        (rs.headD 0) (rs.getD 1 0))
def nitK1 (cR : CallM) (k : Nat) (ctx hi : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => nitK2 cR k ctx hi (r1.headD 0) (piBW k m1 CWF (r1.headD 0))
/-- The model of `nest_inst_type(vis, ctx, hi, key)` at exec fuel `k + 1`. -/
def nitW (cR : CallM) (k : Nat) (m : Mem) (vis ctx hi key : Word) : Option (List Word × Mem) :=
  nitK1 cR k ctx hi (ntyWf cR k m vis key)

section arms
variable (cR : CallM) (k : Nat) (m1 m2 m4 m5 : Mem) (ctx hi ty : Word) (r1 rs r4 r5 v : List Word)
theorem nitK5_some (h : ¬ r5.headD 0 = 0) : nitK5 ty rs (some (r5, m5)) = some ([rs.getD 1 0, ty], m5) := by
  rw [nitK5, ite_eq_right h]
theorem nitK4_ok (h : ¬ r4.headD 0 ≠ 0) : nitK4 cR k ctx ty rs v (some (r4, m4)) =
    nitK5 ty rs (lveC cR k m4 (v.tail.headD 0) (rdW (m4.arr64 IW) (ctx + 9))) := by rw [nitK4, ite_eq_right h]
theorem nitK2_eq : nitK2 cR k ctx hi ty (some (rs, m2)) =
    if eViewW m2 (rs.getD 2 0) = [] then none
    else if (eViewW m2 (rs.getD 2 0)).headD 0 ≠ 2 then none
    else nitK4 cR k ctx ty rs (eViewW m2 (rs.getD 2 0))
      (noaW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4)) hi
        (rs.headD 0) (rs.getD 1 0)) := rfl
theorem nitK1_some : nitK1 cR k ctx hi (some (r1, m1)) =
    nitK2 cR k ctx hi (r1.headD 0) (piBW k m1 CWF (r1.headD 0)) := rfl
end arms
attribute [ind_grind] nitK5_some nitK4_ok nitK2_eq nitK1_some

end L.Ind

end
