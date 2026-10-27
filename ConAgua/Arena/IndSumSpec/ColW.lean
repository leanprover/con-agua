import ConAgua.Arena.IndRealNames
import ConAgua.Arena.IndSum

/-!
# ColW

`plK0`, `plK3`, `plK2`, `plgW`, `plK1`, `plgW_nil` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `param_levels_go`: `lps.map .param`, interned -/

/-- After the empty allocation. -/
def plK0 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m') => some ([q, 0], m')
/-- After `sl_cons`. -/
def plK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([r.headD 0, r.tail.headD 0], m3)
/-- After the recursion. -/
def plK2 (k : Nat) (u : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => plK3 (consW k m2 u (r.headD 0) (r.tail.headD 0))

mutual
/-- **The model of `param_levels_go`.** -/
def plgW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, o, l =>
    if l = 0 then plK0 (allocW m 0)
    else plK1 k o l (pinternW m (rdW (m.arr64 IW) o))
/-- After `intern_param`. -/
def plK1 (k : Nat) (o l : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (u, m1) => if 4294967296 ≤ u then none else plK2 k u (plgW k m1 (o + 1) (l - 1))
end

section arms
variable (k : Nat) (m m1 m2 m3 : Mem) (o l u q : Word) (r : List Word)
theorem plgW_nil (hl : l = 0) : plgW (k + 1) m o l = plK0 (allocW m 0) := by simp [plgW, hl]
theorem plgW_cons (hl : l ≠ 0) : plgW (k + 1) m o l = plK1 k o l (pinternW m (rdW (m.arr64 IW) o)) := by
  simp [plgW, hl]
theorem plK0_some : plK0 (some (q, m1)) = some ([q, 0], m1) := rfl
theorem plK1_big (h : 4294967296 ≤ u) : plK1 k o l (some (u, m1)) = none := by simp [plK1, h]
theorem plK1_ok (h : ¬ 4294967296 ≤ u) :
    plK1 k o l (some (u, m1)) = plK2 k u (plgW k m1 (o + 1) (l - 1)) := by simp only [plK1, ite_eq_right h]
end arms

grind_pattern [ind_grind] plgW_nil => plgW (k + 1) m o l
grind_pattern [ind_grind] plgW_cons => plgW (k + 1) m o l
grind_pattern [ind_grind] plK0_some => plK0 (some (q, m1))
grind_pattern [ind_grind] plK1_big => plK1 k o l (some (u, m1))
grind_pattern [ind_grind] plK1_ok => plK1 k o l (some (u, m1))
section census
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hg : p.lookup "sl_get" = some slGet)
  (hpf : p.lookup "param_find" = some paramFind) (hpp : p.lookup "param_push" = some paramPush)
  (hip : p.lookup "intern_param" = some internParam)
  (hp : p.lookup "param_levels_go" = some paramLevelsGoL)
include ha hc hsc hg hpf hpp hip hp

/-- The model of `param_levels`. -/
def plW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, o, l => plK4 (plgW k m o l)
where
  /-- After `param_levels_go`. -/
  plK4 : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (r, m1) => plK5 (ilF m1 [r.headD 0, r.tail.headD 0])
  /-- After `intern_ls_iw`. -/
  plK5 : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (r, m2) => some ([r.headD 0], m2)

omit ha hc hsc hg hpf hpp hip hp in
theorem plW_succ (k : Nat) (m : Mem) (o l : Word) : plW (k + 1) m o l = plW.plK4 (plgW k m o l) := rfl
omit ha hc hsc hg hpf hpp hip hp in
theorem plK4_some (r : List Word) (m1 : Mem) :
    plW.plK4 (some (r, m1)) = plW.plK5 (ilF m1 [r.headD 0, r.tail.headD 0]) := rfl
omit ha hc hsc hg hpf hpp hip hp in
theorem plK5_some (r : List Word) (m2 : Mem) : plW.plK5 (some (r, m2)) = some ([r.headD 0], m2) := rfl
grind_pattern [ind_grind] plW_succ => plW (k + 1) m o l
grind_pattern [ind_grind] plK4_some => plW.plK4 (some (r, m1))
grind_pattern [ind_grind] plK5_some => plW.plK5 (some (r, m2))

end census

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `struct_proj_guards_col`: the twin's `col` -/

/-- After the recursion: its word. -/
def colK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0], m2)

mutual
/-- **The model of `struct_proj_guards_col`.** -/
def colW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, uo, ul, so, sl, z, j, k, acc =>
    if k = 0 then some ([acc], m)
    else if getDW m uo ul j 0 ≠ 0 then
      colK n uo ul so sl z j k (minternW m acc (getDW m so sl j z))
    else colK2 (colW n m uo ul so sl z (j + 1) (k - 1) acc)
/-- After `intern_max`. -/
def colK (n : Nat) (uo ul so sl z j k : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (mx, m1) =>
    if 4294967296 ≤ mx then none else colK2 (colW n m1 uo ul so sl z (j + 1) (k - 1) mx)
end

/-! ## `struct_proj_guards_row`: the twin's `row` -/

/-- After the recursion: the cons. -/
def rowK2 (n : Nat) (g : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rr, m2) => plK3 (consW n m2 g (rr.headD 0) (rr.tail.headD 0))

mutual
/-- **The model of `struct_proj_guards_row`.** -/
def rowW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, uo, ul, so, sl, z, i, k =>
    if k = 0 then plK0 (allocW m 0)
    else rowK1 n uo ul so sl z i k (colW n m uo ul so sl z 0 i (getDW m so sl i z))
/-- After `struct_proj_guards_col`. -/
def rowK1 (n : Nat) (uo ul so sl z i k : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rg, m1) => rowK2 n (rg.headD 0) (rowW n m1 uo ul so sl z (i + 1) (k - 1))
end

end L.Ind

end
