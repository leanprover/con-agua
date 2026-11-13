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

`cftK4`, `cftK3`, `cftKF`, `cftK2`, `cftK1` (the parts of `class_former_ty`'s model `cftW`), `CftProg`, `decCI_ind_cv`, `decTM_lvls'`.
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
  | some (rt, m3) => cftK3 cR N mp (rt.headD 0) (erToIwW N m3 (erRd m3 (q + 2)) (erRd m3 (q + 3)))

/-- After `env_find` (memory unchanged): an inductive's record, its telescope. -/
def cftK2 (cR : CallM) (N : Nat) (vis mp : Word) (r2 : List Word) (m : Mem) : Option (List Word × Mem) :=
  if r2.headD 0 = 0 then none
  else if erRd m (r2.tail.headD 0) ≠ 3 then none
  else cftKF cR N mp (r2.tail.headD 0)
    (cR N "family_telescope" [vis, r2.tail.headD 0 + 1, r2.tail.headD 0 + 5] m)

/-- After `intern_bvar(0)`: the word if it is a handle. -/
def cftK1 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (e, m1) => if 4294967296 ≤ e then none else some ([e], m1)

section arms
variable (cR : CallM) (N : Nat) (m m1 m3 m4 : Mem) (vis mp q e ty : Word) (rt r3 r4 : List Word)
theorem cftK1_some : cftK1 (some (e, m1)) = if 4294967296 ≤ e then none else some ([e], m1) := rfl
theorem cftKF_some : cftKF cR N mp q (some (rt, m3)) =
    cftK3 cR N mp (rt.headD 0) (erToIwW N m3 (erRd m3 (q + 2)) (erRd m3 (q + 3))) := rfl
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

theorem decCI_ind_cv {a : Nat → Option Word} {q : Nat} {cv : IConstantVal}
    {caps : IIndCaps} (h : decCI a q = some (.indInfo cv caps)) : decCV a (q + 1) = some cv := by
  cases hq : a q with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
  all_goals rw [hk] at h
  all_goals first | (simp [Option.bind_eq_some_iff] at h; done) | skip
  cases e : decCV a (q + 1) with
  | none => simp [e] at h
  | some cv' =>
    simp only [e, Option.bind_some] at h
    cases e2 : decCaps a (q + CI.indCaps.toNat) with
    | none => simp [e2] at h
    | some c =>
      simp only [e2, Option.bind_some, Option.pure_def, Option.some.injEq,
        IConstantInfo.indInfo.injEq] at h
      rw [h.1]

theorem decTM_lvls' {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    iwH m (p + 1) = some M.lvls := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨w5, h5, a1, ha1, w4, h4, w3, h3, w2, h2, ac, hac, w1, hw1, w0, h0, a, ha, rfl⟩ := h
  exact ha1

end L.Ind

end
