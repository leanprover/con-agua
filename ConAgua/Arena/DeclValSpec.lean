import ConAgua.Arena.DeclCvg
import ConAgua.Arena.DeclHeader
import ConAgua.Arena.DeclRec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

noncomputable section

/-!
# `checkDecl`'s value checks under the stage relation (lane `decls3`)

`checkConstantVal` is `installHeader`, then the type's sort (`checkConstantVal_eq`).
`check_thm_val(vis, c)` refines `checkThmVal` at the arm's constant record `c` (built by `erec_ci`
with the kind the twin pushes, its value word at `c + 5`): a word model with the core's calls read
through a `CallM`, `install_value_guards`' model `ivgW`, `env_push` through `callW`. The unified
models of `check_constant_val`, `check_defn_val` and `check_opaque_val` and their refinements are
in `Verdict/DeclValsE.lean`.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-- The value checks' functions in a program. -/
structure ValProg (p : Prog) : Prop where
  ccv : p.lookup "check_constant_val" = some checkConstantValL
  dv : p.lookup "check_defn_val" = some checkDefnValL
  tv : p.lookup "check_thm_val" = some checkThmValL
  ov : p.lookup "check_opaque_val" = some checkOpaqueValL
  lef : p.lookup "lvl_eq_fueled" = some lvlEqFueled
  ih : IhProg p
  cvg : CvgProg p
  rcp : RecProg p

/-! ## Twin equations -/

theorem ite_bindAM {α β : Type} (c : Prop) [Decidable c] (x y : AM α) (f : α → AM β) :
    ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  split <;> rfl

theorem fail_bindAM {α β : Type} (e : CheckError) (f : α → AM β) : (fail e >>= f) = fail e := rfl

/-- `checkConstantVal` is `installHeader`, then the type's sort. -/
theorem checkConstantVal_eq (mode : ConLeche.CheckMode) (fe : IFEnv) (cv : IConstantVal) :
    checkConstantVal mode fe cv = (do installHeader fe cv
                                      let st ← inferTypeCore mode fe checkFuel 0 cv.type
                                      let _ ← ensureSortCore mode fe checkFuel 0 st
                                      pure ()) := by
  simp only [checkConstantVal, installHeader, bind_assoc, ite_bindAM, fail_bindAM, pure_bind]

section models
variable (p : Prog)

/-! ## The value checks' common tail (`check_thm_val`'s, after its guards) -/

/-- After the push: its view word. -/
def dvK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => some ([r4.headD 0], m4)

/-- After `is_def_eq_core`: the push. -/
def dvK3 (n : Nat) (vis c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => if r3.headD 0 = 0 then none else dvK4 (callW p n "env_push" [vis, c] m3)

/-- After the value's type. -/
def dvK2 (cl : CallM) (n : Nat) (vis c t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => dvK3 p n vis c (cl n "is_def_eq_core" [vis, 0, r2.headD 0, t] m2)

/-- After the value's guards. -/
def dvK1 (cl : CallM) (n : Nat) (vis c v t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => dvK2 p cl n vis c t (cl n "infer_type_core" [vis, 0, v] m1)

section arms
variable (cl : CallM) (n : Nat) (m m1 m2 m3 : Mem) (vis c v t : Word) (r1 r2 r3 : List Word)
theorem dvK1_some : dvK1 p cl n vis c v t (some (r1, m1)) =
    dvK2 p cl n vis c t (cl n "infer_type_core" [vis, 0, v] m1) := rfl
theorem dvK2_some : dvK2 p cl n vis c t (some (r2, m2)) =
    dvK3 p n vis c (cl n "is_def_eq_core" [vis, 0, r2.headD 0, t] m2) := rfl
theorem dvK3_some : dvK3 p n vis c (some (r3, m3)) =
    if r3.headD 0 = 0 then none else dvK4 (callW p n "env_push" [vis, c] m3) := rfl
theorem dvK4_some (r4 : List Word) (m4 : Mem) : dvK4 (some (r4, m4)) = some ([r4.headD 0], m4) :=
  rfl
end arms

grind_pattern [ind_grind] dvK1_some => dvK1 p cl n vis c v t (some (r1, m1))
grind_pattern [ind_grind] dvK2_some => dvK2 p cl n vis c t (some (r2, m2))
grind_pattern [ind_grind] dvK3_some => dvK3 p n vis c (some (r3, m3))
grind_pattern [ind_grind] dvK4_some => dvK4 (some (r4, m4))

/-! ## `check_thm_val(vis, c)` -/

/-- After `lvl_eq_fueled`: abort on `false`, then `check_defn_val`'s tail. -/
def tvK4 (cl : CallM) (n : Nat) (vis c v t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if r4.headD 0 = 0 then none else dvK1 p cl n vis c v t (ivgW cl n m4 vis (c + 1) v)

/-- After the zero level. -/
def tvK3 (cl : CallM) (n : Nat) (vis c v t u : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => tvK4 p cl n vis c v t (cl n "lvl_eq_fueled" [u, r3.headD 0] m3)

/-- After `ensure_sort_core`. -/
def tvK2 (cl : CallM) (n : Nat) (vis c v t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => tvK3 p cl n vis c v t (r2.headD 0) (pinWordW m2 53)

/-- After the type's type. -/
def tvK1 (cl : CallM) (n : Nat) (vis c v t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => tvK2 p cl n vis c v t (cl n "ensure_sort_core" [vis, 0, r1.headD 0] m1)

/-- **The model of `check_thm_val`.** -/
def tvW (cl : CallM) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, c =>
    tvK1 p cl n vis c (rdW (m.arr64 EREC) (c + 5)) (rdW (m.arr64 EREC) (c + 4))
      (cl n "infer_type_core" [vis, 0, rdW (m.arr64 EREC) (c + 4)] m)

section arms
variable (cl : CallM) (n : Nat) (m m1 m2 m3 m4 : Mem) (vis c v t u : Word) (r1 r2 r3 r4 : List Word)
theorem tvW_step : tvW p cl (n + 1) m vis c =
    tvK1 p cl n vis c (rdW (m.arr64 EREC) (c + 5)) (rdW (m.arr64 EREC) (c + 4))
      (cl n "infer_type_core" [vis, 0, rdW (m.arr64 EREC) (c + 4)] m) := rfl
theorem tvK1_some : tvK1 p cl n vis c v t (some (r1, m1)) =
    tvK2 p cl n vis c v t (cl n "ensure_sort_core" [vis, 0, r1.headD 0] m1) := rfl
theorem tvK2_some : tvK2 p cl n vis c v t (some (r2, m2)) =
    tvK3 p cl n vis c v t (r2.headD 0) (pinWordW m2 53) := rfl
theorem tvK3_some : tvK3 p cl n vis c v t u (some (r3, m3)) =
    tvK4 p cl n vis c v t (cl n "lvl_eq_fueled" [u, r3.headD 0] m3) := rfl
theorem tvK4_some : tvK4 p cl n vis c v t (some (r4, m4)) =
    if r4.headD 0 = 0 then none else dvK1 p cl n vis c v t (ivgW cl n m4 vis (c + 1) v) := rfl
end arms

grind_pattern [ind_grind] tvW_step => tvW p cl (n + 1) m vis c
grind_pattern [ind_grind] tvK1_some => tvK1 p cl n vis c v t (some (r1, m1))
grind_pattern [ind_grind] tvK2_some => tvK2 p cl n vis c v t (some (r2, m2))
grind_pattern [ind_grind] tvK3_some => tvK3 p cl n vis c v t u (some (r3, m3))
grind_pattern [ind_grind] tvK4_some => tvK4 p cl n vis c v t (some (r4, m4))

set_option maxHeartbeats 1600000 in
theorem tv_specW (h : ValProg p) (cl : CallM) (hc : CallSpec p cl) (n : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_thm_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ tvW p cl n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.tv]
  simp only [callFn, checkThmValL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        pinWord_specW p h.cvg.pin n, hc n "lvl_eq_fueled",
        ivg_specW p h.cvg cl hc n, hc n "infer_type_core", hc n "ensure_sort_core",
        hc n "is_def_eq_core", callW_spec p n "env_push"] <;>
      finish (gen := 20) [rdW_eq]

end models

end L.Arena
