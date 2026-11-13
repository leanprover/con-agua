module

public import ConAgua.Arena.IndCallM
public import ConAgua.Arena.IndCopy2
public import ConAgua.Arena.RecGen
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.IndGrindAttr
public import ConAgua.Arena.Env
import ConAgua.Arena.RecLayout.CIDec

@[expose] public section

/-!
# DecCIIndCv

`cftK4`, `cftK3`, `cftKF`, `cftK2`, `cftK1` (the parts of `class_former_ty`'s model `cftW`), `CftProg`, `decTM_lvls'`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Model -/

/-- After `inst_lp_fast`: its word. -/
def cftK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => some ([r4.headD 0], m4)

/-- After `er_to_iw` (the levels' slice): `inst_lp_fast` of the telescope `ty` at the class's levels. -/
def cftK3 (cR : CallM) (N : Nat) (mp ty : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => cftK4 (cR N "inst_lp_fast"
      [CWF, r3.headD 0, r3.tail.headD 0, rdW (m3.arr64 IW) (mp + 1), ty] m3)

/-- After `family_telescope`: the stored levels to `IW`. -/
def cftKF (cR : CallM) (N : Nat) (mp q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rt, m3) => cftK3 cR N mp (rt.headD 0) (erToIwW N m3 (erRd m3 (q + (CI.cv + CV.lpsOff))) (erRd m3 (q + (CI.cv + CV.lpsLen))))

/-- After `env_find` (memory unchanged): an inductive's record, its telescope. -/
def cftK2 (cR : CallM) (N : Nat) (vis mp : Word) (r2 : List Word) (m : Mem) : Option (List Word × Mem) :=
  if r2.headD 0 = 0 then none
  else if erRd m (r2.tail.headD 0) ≠ 3 then none
  else cftKF cR N mp (r2.tail.headD 0)
    (cR N "family_telescope" [vis, r2.tail.headD 0 + CI.cv, r2.tail.headD 0 + CI.indCaps] m)

/-- After `intern_bvar(0)`: the word if it is a handle. -/
def cftK1 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (e, m1) => if 4294967296 ≤ e then none else some ([e], m1)

section arms
variable (cR : CallM) (N : Nat) (m m1 m3 m4 : Mem) (vis mp q e ty : Word) (rt r3 r4 : List Word)
theorem cftK1_some : cftK1 (some (e, m1)) = if 4294967296 ≤ e then none else some ([e], m1) := rfl
theorem cftKF_some : cftKF cR N mp q (some (rt, m3)) =
    cftK3 cR N mp (rt.headD 0) (erToIwW N m3 (erRd m3 (q + (CI.cv + CV.lpsOff))) (erRd m3 (q + (CI.cv + CV.lpsLen)))) := rfl
theorem cftK3_some : cftK3 cR N mp ty (some (r3, m3)) = cftK4 (cR N "inst_lp_fast"
      [CWF, r3.headD 0, r3.tail.headD 0, rdW (m3.arr64 IW) (mp + 1), ty] m3) := rfl
theorem cftK4_some : cftK4 (some (r4, m4)) = some ([r4.headD 0], m4) := rfl
end arms

grind_pattern [ind_grind] cftK1_some => cftK1 (some (e, m1))
grind_pattern [ind_grind] cftKF_some => cftKF cR N mp q (some (rt, m3))
grind_pattern [ind_grind] cftK3_some => cftK3 cR N mp ty (some (r3, m3))
grind_pattern [ind_grind] cftK4_some => cftK4 (some (r4, m4))

/-- `class_former_ty`'s callees (`family_telescope` and `inst_lp_fast` are read through a `CallM`). -/
structure CftProg (p : Prog) : Prop where
  rowGet : p.lookup "env_row_get" = some envRowGetL
  baseGet : p.lookup "base_row_get" = some baseRowGetL
  find : p.lookup "env_find" = some envFindL
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "er_copy" = some erCopy
  eti : p.lookup "er_to_iw" = some erToIw
  bf : p.lookup "bvar_find" = some bvarFind
  bp : p.lookup "bvar_push" = some bvarPush
  ib : p.lookup "intern_bvar" = some internBVar
  cft : p.lookup "class_former_ty" = some classFormerTyL

/-! ## Relational lemma -/

theorem decTM_lvls' {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    iwH m (p + 1) = some M.lvls := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨w5, h5, a1, ha1, w4, h4, w3, h3, w2, h2, ac, hac, w1, hw1, w0, h0, a, ha, rfl⟩ := h
  exact ha1

end L.Ind

end
