module

public import ConAgua.Arena.IndCallM
public import ConAgua.Arena.IndCopy2
public import ConAgua.Arena.RecGen
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.IndGrindAttr
public import ConAgua.Arena.Env

@[expose] public section

/-!
# DecCIIndCv

`cftK4`, `cftK3`, `cftK2`, `cftK1`, `cftK1_some`, `cftK2_some` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Model -/

def cftK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => some ([r4.headD 0], m4)

def cftK3 (cR : CallM) (N : Nat) (mp q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => cftK4 (cR N "inst_lp_fast"
      [CWF, r3.headD 0, r3.tail.headD 0, rdW (m3.arr64 IW) (mp + 1), rdW (m3.arr64 EREC) (q + 4)] m3)

def cftK2 (cR : CallM) (N : Nat) (mp : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then none
    else if rdW (m2.arr64 EREC) (r2.tail.headD 0) ≠ 3 then none
    else cftK3 cR N mp (r2.tail.headD 0) (erToIwW N m2 (rdW (m2.arr64 EREC) (r2.tail.headD 0 + 2))
      (rdW (m2.arr64 EREC) (r2.tail.headD 0 + 3)))

def cftK1 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (e, m1) => if 4294967296 ≤ e then none else some ([e], m1)

section arms
variable (cR : CallM) (N : Nat) (m m1 m2 m3 m4 : Mem) (vis o l mp q e : Word) (r2 r3 r4 : List Word)
theorem cftK1_some : cftK1 (some (e, m1)) = if 4294967296 ≤ e then none else some ([e], m1) := rfl
theorem cftK2_some : cftK2 cR N mp (some (r2, m2)) =
    if r2.headD 0 = 0 then none
    else if rdW (m2.arr64 EREC) (r2.tail.headD 0) ≠ 3 then none
    else cftK3 cR N mp (r2.tail.headD 0) (erToIwW N m2 (rdW (m2.arr64 EREC) (r2.tail.headD 0 + 2))
      (rdW (m2.arr64 EREC) (r2.tail.headD 0 + 3))) := rfl
theorem cftK3_some : cftK3 cR N mp q (some (r3, m3)) = cftK4 (cR N "inst_lp_fast"
      [CWF, r3.headD 0, r3.tail.headD 0, rdW (m3.arr64 IW) (mp + 1), rdW (m3.arr64 EREC) (q + 4)] m3) := rfl
theorem cftK4_some : cftK4 (some (r4, m4)) = some ([r4.headD 0], m4) := rfl
end arms

grind_pattern [ind_grind] cftK1_some => cftK1 (some (e, m1))
grind_pattern [ind_grind] cftK2_some => cftK2 cR N mp (some (r2, m2))
grind_pattern [ind_grind] cftK3_some => cftK3 cR N mp q (some (r3, m3))
grind_pattern [ind_grind] cftK4_some => cftK4 (some (r4, m4))

/-! ## Relational lemma -/

theorem decCI_ind_cv {a : Array Word} {q : Nat} {cv : IConstantVal}
    {caps : IIndCaps} (h : decCI (aread a) q = some (.indInfo cv caps)) : decCV (aread a) (q + 1) = some cv := by
  sorry

theorem decTM_lvls' {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    iwH m (p + 1) = some M.lvls := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨w5, h5, a1, ha1, w4, h4, w3, h3, w2, h2, ac, hac, w1, hw1, w0, h0, a, ha, rfl⟩ := h
  exact ha1

end L.Ind

end
