import ConAgua.Arena.RecGenSpec18

/-!
# `classMajors` (lane `indproofs3`, helper `indproofs3-pos-cls`)

Every class key checked as a major: the key's application (`intern_const`, the `mk_app_n` stub),
`target_major_of`, `target_major_pins`; a recursion consing each major onto the rest's slice (D18).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Frames -/

/-! ## `class_majors` -/

mutual
/-- **The model of `class_majors(vis, pp, cao, cal, pfo, pfl, ko, kl)`** at exec fuel `n`. -/
def clmW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, pp, cao, cal, pfo, pfl, ko, kl =>
    if kl = 0 then some ([0, 0], m)
    else clmK1 p n vis pp cao cal pfo pfl ko kl (rdW (m.arr64 IW) ko)
      (callW p n "intern_const" [rdW (m.arr64 IW) (rdW (m.arr64 IW) ko),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) ko + 1)] m)
def clmK1 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl ko kl key : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if 4294967296 ≤ r.headD 0 then none
      else clmK2 p n vis pp cao cal pfo pfl ko kl (callW p n "mk_app_n_f"
        [r.headD 0, rdW (m.arr64 IW) (key + 2), rdW (m.arr64 IW) (key + 3)] m)
def clmK2 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl ko kl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => clmK3 p n vis pp cao cal pfo pfl ko kl
      (callW p n "target_major_of" [vis, pp, cao, cal, pfo, pfl, pfo, pfl, r.headD 0] m)
def clmK3 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl ko kl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => clmK4 p n vis pp cao cal pfo pfl ko kl r
      (callW p n "target_major_pins" [vis, rdW (m.arr64 IW) (pp + 4), r.headD 0] m)
def clmK4 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl ko kl : Word) (r3 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => ckkK2 p n r3 (clmW p n m vis pp cao cal pfo pfl (ko + 1) (kl - 1))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis pp cao cal pfo pfl ko kl key : Word) (r r3 : List Word)
theorem clmW_zero : clmW p 0 m vis pp cao cal pfo pfl ko kl = none := by simp [clmW]
theorem clmW_nil (h : kl = 0) : clmW p (n + 1) m vis pp cao cal pfo pfl ko kl = some ([0, 0], m) := by
  simp [clmW, h]
theorem clmW_cons (h : kl ≠ 0) : clmW p (n + 1) m vis pp cao cal pfo pfl ko kl =
    clmK1 p n vis pp cao cal pfo pfl ko kl (rdW (m.arr64 IW) ko)
      (callW p n "intern_const" [rdW (m.arr64 IW) (rdW (m.arr64 IW) ko),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) ko + 1)] m) := by simp [clmW, h]
theorem clmK1_some : clmK1 p n vis pp cao cal pfo pfl ko kl key (some (r, m)) =
    if 4294967296 ≤ r.headD 0 then none
      else clmK2 p n vis pp cao cal pfo pfl ko kl (callW p n "mk_app_n_f"
        [r.headD 0, rdW (m.arr64 IW) (key + 2), rdW (m.arr64 IW) (key + 3)] m) := by simp [clmK1]
theorem clmK2_some : clmK2 p n vis pp cao cal pfo pfl ko kl (some (r, m)) = clmK3 p n vis pp cao cal pfo pfl ko kl
      (callW p n "target_major_of" [vis, pp, cao, cal, pfo, pfl, pfo, pfl, r.headD 0] m) := by simp [clmK2]
theorem clmK3_some : clmK3 p n vis pp cao cal pfo pfl ko kl (some (r, m)) = clmK4 p n vis pp cao cal pfo pfl ko kl r
      (callW p n "target_major_pins" [vis, rdW (m.arr64 IW) (pp + 4), r.headD 0] m) := by simp [clmK3]
theorem clmK4_some : clmK4 p n vis pp cao cal pfo pfl ko kl r3 (some (r, m)) =
    ckkK2 p n r3 (clmW p n m vis pp cao cal pfo pfl (ko + 1) (kl - 1)) := by simp [clmK4]
end arms
attribute [ind_grind] clmW_nil clmW_cons clmK1_some clmK2_some clmK3_some clmK4_some

set_option maxHeartbeats 1600000 in
theorem clm_spec (p : Prog) (hp : p.lookup "class_majors" = some classMajorsL) (n : Nat) :
    ∀ (s₀ : St) (vis pp cao cal pfo pfl ko kl : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "class_majors" [vis, pp, cao, cal, pfo, pfl, ko, kl]
    ⦃fun r s' => LocEq s' s₀ ∧ clmW p n s₀.mem vis pp cao cal pfo pfl ko kl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis pp cao cal pfo pfl ko kl; rw [invoke_eq _ hp]; simp only [callFn, classMajorsL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis pp cao cal pfo pfl ko kl
    rw [invoke_eq _ hp]
    simp only [callFn, classMajorsL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "intern_const", callW_spec p n "mk_app_n_f", callW_spec p n "target_major_of",
        callW_spec p n "target_major_pins", callW_spec p n "sl_cons", ih] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

/-- The lookups of `class_majors`. -/
structure ClmProg (p : Prog) : Prop where
  tmf : TmfProg p
  tmp : TmpProg p
  keys : KeysProg p
  cm : p.lookup "class_majors" = some classMajorsL

end L.Ind
