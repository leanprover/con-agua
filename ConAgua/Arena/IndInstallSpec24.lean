import ConAgua.Arena.IndGrindAttr
import ConAgua.Arena.IndInstall
import ConAgua.Arena.WhnfBase
import ConAgua.Scan.Common

/-!
# Refinements of `IndInstall`, part 24 (lane `indproofs3`, helper `tail`): `checkBlockTables`,
the word models

`check_block_tables_one(p, m, cs.off, ss.off, vis)` (one structure-like member: `struct_proj_guards`,
`block_shape_lps`, `check_struct_proj_table`, after a capacity abort on `nP + nF + 1`) and
`check_block_tables(p, ms.off, ms.len, cs.off, cs.len, ss.off, ss.len, vis)` (recursion as the
twin's over the three lists side by side).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `check_block_tables_one` -/

def ctoK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
def ctoK2 (p : Prog) (n : Nat) (pp ms cA nF vis : Word) (rg : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rl, m) => ctoK3 (callW p n "check_struct_proj_table"
      [rdW (m.arr64 EREC) (rdW (m.arr64 IW) ms), rdW (m.arr64 EREC) cA, rl.headD 0, rl.tail.headD 0,
        rdW (m.arr64 IW) (pp + 4), nF, rdW (m.arr64 IW) (pp + 6), rg.headD 0, rg.tail.headD 0, cA, vis] m)
def ctoK1 (p : Prog) (n : Nat) (pp ms cA nF vis : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rg, m) => ctoK2 p n pp ms cA nF vis rg (callW p n "block_shape_lps" [pp] m)

/-- **The model of `check_block_tables_one(p, m, cs.off, ss.off, vis)`** (body fuel `n`). -/
def ctoW (p : Prog) (n : Nat) (m : Mem) (pp ms co so vis : Word) : Option (List Word × Mem) :=
  if rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (rdW (m.arr64 IW) co + 1) + 1 ≤ rdW (m.arr64 IW) (pp + 4)
  then none
  else ctoK1 p n pp ms (rdW (m.arr64 IW) (rdW (m.arr64 IW) co)) (rdW (m.arr64 IW) (rdW (m.arr64 IW) co + 1)) vis
    (callW p n "struct_proj_guards" [rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) co) + 3),
      rdW (m.arr64 IW) (pp + 4), rdW (m.arr64 IW) (rdW (m.arr64 IW) co + 1),
      rdW (m.arr64 IW) (rdW (m.arr64 IW) so), rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 1)] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (pp ms co so cA nF vis : Word) (r rg : List Word)
theorem ctoK3_some : ctoK3 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem ctoK2_some : ctoK2 p n pp ms cA nF vis rg (some (r, m)) = ctoK3 (callW p n "check_struct_proj_table"
      [rdW (m.arr64 EREC) (rdW (m.arr64 IW) ms), rdW (m.arr64 EREC) cA, r.headD 0, r.tail.headD 0,
        rdW (m.arr64 IW) (pp + 4), nF, rdW (m.arr64 IW) (pp + 6), rg.headD 0, rg.tail.headD 0, cA, vis] m) :=
  rfl
theorem ctoK1_some : ctoK1 p n pp ms cA nF vis (some (r, m)) =
    ctoK2 p n pp ms cA nF vis r (callW p n "block_shape_lps" [pp] m) := rfl
end arms
attribute [ind_grind] ctoK3_some ctoK2_some ctoK1_some

set_option maxHeartbeats 1600000 in
theorem cto_spec (p : Prog) (hp : p.lookup "check_block_tables_one" = some checkBlockTablesOne) (n : Nat)
    (s₀ : St) (pp ms co so vis : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_tables_one" [pp, ms, co, so, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ ctoW p n s₀.mem pp ms co so vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockTablesOne]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "struct_proj_guards", callW_spec p n "block_shape_lps",
      callW_spec p n "check_struct_proj_table"] <;>
    finish (gen := 40) (instances := 20000) [ctoW, rdW_eq]

/-! ## `check_block_tables` -/

def ctbK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

mutual
/-- **The model of `check_block_tables`** at exec fuel `n`. -/
def ctbW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, pp, mo, ml, co, cl, so, sl, vis =>
    if ml = 0 then some ([vis], m) else if cl = 0 then some ([vis], m) else if sl = 0 then some ([vis], m)
    else if rdW (m.arr64 IW) (rdW (m.arr64 IW) co + 1) = 1 then
      if rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 1) = 1 then
        if rdW (m.arr64 IW) (rdW (m.arr64 IW) mo + 1) = 0 then
          ctbK1 p n pp mo ml co cl so sl (callW p n "check_block_tables_one"
            [pp, rdW (m.arr64 IW) mo, rdW (m.arr64 IW) (rdW (m.arr64 IW) co),
              rdW (m.arr64 IW) (rdW (m.arr64 IW) so), vis] m)
        else ctbK2 (ctbW p n m pp (mo + 1) (ml - 1) (co + 1) (cl - 1) (so + 1) (sl - 1) vis)
      else ctbK2 (ctbW p n m pp (mo + 1) (ml - 1) (co + 1) (cl - 1) (so + 1) (sl - 1) vis)
    else ctbK2 (ctbW p n m pp (mo + 1) (ml - 1) (co + 1) (cl - 1) (so + 1) (sl - 1) vis)
/-- After `check_block_tables_one`: the recursion at its view. -/
def ctbK1 (p : Prog) (n : Nat) (pp mo ml co cl so sl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => ctbK2 (ctbW p n m pp (mo + 1) (ml - 1) (co + 1) (cl - 1) (so + 1) (sl - 1) (r.headD 0))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (pp mo ml co cl so sl vis : Word) (r : List Word)
theorem ctbW_zero : ctbW p 0 m pp mo ml co cl so sl vis = none := by simp [ctbW]
theorem ctbW_nil1 (h : ml = 0) : ctbW p (n + 1) m pp mo ml co cl so sl vis = some ([vis], m) := by
  simp [ctbW, h]
theorem ctbW_nil2 (h1 : ml ≠ 0) (h : cl = 0) : ctbW p (n + 1) m pp mo ml co cl so sl vis = some ([vis], m) := by
  simp [ctbW, h1, h]
theorem ctbW_nil3 (h1 : ml ≠ 0) (h2 : cl ≠ 0) (h : sl = 0) :
    ctbW p (n + 1) m pp mo ml co cl so sl vis = some ([vis], m) := by simp [ctbW, h1, h2, h]
theorem ctbW_one (h1 : ml ≠ 0) (h2 : cl ≠ 0) (h3 : sl ≠ 0)
    (hc : rdW (m.arr64 IW) (rdW (m.arr64 IW) co + 1) = 1) (hs : rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 1) = 1)
    (hi : rdW (m.arr64 IW) (rdW (m.arr64 IW) mo + 1) = 0) :
    ctbW p (n + 1) m pp mo ml co cl so sl vis = ctbK1 p n pp mo ml co cl so sl (callW p n "check_block_tables_one"
      [pp, rdW (m.arr64 IW) mo, rdW (m.arr64 IW) (rdW (m.arr64 IW) co),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) so), vis] m) := by
  simp [ctbW, h1, h2, h3, hc, hs, hi]
theorem ctbW_skip (h1 : ml ≠ 0) (h2 : cl ≠ 0) (h3 : sl ≠ 0)
    (h : ¬ (rdW (m.arr64 IW) (rdW (m.arr64 IW) co + 1) = 1 ∧ rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 1) = 1 ∧
      rdW (m.arr64 IW) (rdW (m.arr64 IW) mo + 1) = 0)) :
    ctbW p (n + 1) m pp mo ml co cl so sl vis =
      ctbK2 (ctbW p n m pp (mo + 1) (ml - 1) (co + 1) (cl - 1) (so + 1) (sl - 1) vis) := by
  rw [ctbW]; simp only [h1, h2, h3, ite_false]
  by_cases hc : rdW (m.arr64 IW) (rdW (m.arr64 IW) co + 1) = 1
  · by_cases hs : rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 1) = 1
    · have hi : ¬ rdW (m.arr64 IW) (rdW (m.arr64 IW) mo + 1) = 0 := fun hi => h ⟨hc, hs, hi⟩
      simp only [hc, hs, hi, ite_true, ite_false]
    · simp only [hc, hs, ite_true, ite_false]
  · simp only [hc, ite_false]
theorem ctbK1_some : ctbK1 p n pp mo ml co cl so sl (some (r, m)) =
    ctbK2 (ctbW p n m pp (mo + 1) (ml - 1) (co + 1) (cl - 1) (so + 1) (sl - 1) (r.headD 0)) := by
  simp [ctbK1]
theorem ctbK2_some : ctbK2 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms
attribute [ind_grind] ctbW_nil1 ctbW_nil2 ctbW_nil3 ctbK1_some ctbK2_some

set_option maxHeartbeats 1600000 in
theorem ctb_spec (p : Prog) (hp : p.lookup "check_block_tables" = some checkBlockTables) (n : Nat) :
    ∀ (s₀ : St) (pp mo ml co cl so sl vis : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_tables" [pp, mo, ml, co, cl, so, sl, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ ctbW p n s₀.mem pp mo ml co cl so sl vis = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ pp mo ml co cl so sl vis; rw [invoke_eq _ hp]; simp only [callFn, checkBlockTables]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ pp mo ml co cl so sl vis
    rw [invoke_eq _ hp]
    simp only [callFn, checkBlockTables]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "check_block_tables_one", ih] <;>
      finish (gen := 40) (instances := 20000) [ctbW, rdW_eq]

end L.Ind
