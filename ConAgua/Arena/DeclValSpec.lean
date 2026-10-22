import ConAgua.Arena.DeclArms
import ConAgua.Arena.DeclCvg
import ConAgua.Arena.DeclStepGo
import ConAgua.Arena.IndInstallSpec3

/-!
# `checkDecl`'s value checks under the stage relation (lane `decls3`)

`check_constant_val(vis, q)` refines `checkConstantVal` (the header's checks, `install_header`,
then the type's sort), and `check_defn_val`/`check_thm_val`/`check_opaque_val(vis, c)` refine
`checkDefnVal`/`checkThmVal`/`checkOpaqueVal` at the arm's constant record `c` (built by `erec_ci`
with the kind the twin pushes, its value word at `c + 5`). On the template of `DeclCvg.lean`:
word models with the core's stubs (`stubM`), `install_header`'s and `install_value_guards`' models
(`ihW`, `ivgW`), `env_push` through `callW`; relational lemmas from `StageR`. Through the stubs of
the core (`infer_type_core`, `ensure_sort_core`, `is_def_eq_core`), the walks and `lvl_eq_c`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

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

/-! ## `check_constant_val(vis, q)` -/

section models
variable (p : Prog)

/-- After `ensure_sort_core`. -/
def ccvK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m3) => some ([0], m3)

/-- After `infer_type_core`. -/
def ccvK2 (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => ccvK3 (stubM "ensure_sort_core" m2 [vis, 0, r2.headD 0])

/-- After `install_header`. -/
def ccvK1 (vis t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => ccvK2 vis (stubM "infer_type_core" m1 [vis, 0, t])

/-- **The model of `check_constant_val`.** -/
def ccvW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, q => ccvK1 vis (rdW (m.arr64 EREC) (q + 3)) (ihW n m vis q)

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (vis q t : Word) (r1 r2 r3 : List Word)
theorem ccvW_step : ccvW (n + 1) m vis q = ccvK1 vis (rdW (m.arr64 EREC) (q + 3)) (ihW n m vis q) :=
  rfl
theorem ccvK1_some : ccvK1 vis t (some (r1, m1)) =
    ccvK2 vis (stubM "infer_type_core" m1 [vis, 0, t]) := rfl
theorem ccvK2_some : ccvK2 vis (some (r2, m2)) =
    ccvK3 (stubM "ensure_sort_core" m2 [vis, 0, r2.headD 0]) := rfl
theorem ccvK3_some : ccvK3 (some (r3, m3)) = some ([0], m3) := rfl
end arms

grind_pattern [ind_grind] ccvW_step => ccvW (n + 1) m vis q
grind_pattern [ind_grind] ccvK1_some => ccvK1 vis t (some (r1, m1))
grind_pattern [ind_grind] ccvK2_some => ccvK2 vis (some (r2, m2))
grind_pattern [ind_grind] ccvK3_some => ccvK3 (some (r3, m3))

theorem ccv_specW (h : ValProg p) (n : Nat) (s₀ : St) (vis q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_constant_val" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ ccvW n s₀.mem vis q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.ccv]
  simp only [callFn, checkConstantValL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        ih_specW p h.ih n, stubM_spec p "infer_type_core" n,
        stubM_spec p "ensure_sort_core" n] <;>
      finish (gen := 20)

/-! ## `check_defn_val(vis, c)` and `check_opaque_val(vis, c)`: one text -/

/-- After the push: its view word. -/
def dvK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => some ([r4.headD 0], m4)

/-- After `is_def_eq_core`: the push. -/
def dvK3 (n : Nat) (vis c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => if r3.headD 0 = 0 then none else dvK4 (callW p n "env_push" [vis, c] m3)

/-- After the value's type. -/
def dvK2 (n : Nat) (vis c t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => dvK3 p n vis c (stubM "is_def_eq_core" m2 [vis, 0, r2.headD 0, t])

/-- After the value's guards. -/
def dvK1 (n : Nat) (vis c v t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => dvK2 p n vis c t (stubM "infer_type_core" m1 [vis, 0, v])

/-- **The model of `check_defn_val`** (and of `check_opaque_val`). -/
def dvW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, c =>
    dvK1 p n vis c (rdW (m.arr64 EREC) (c + 5)) (rdW (m.arr64 EREC) (c + 4))
      (ivgW n m vis (c + 1) (rdW (m.arr64 EREC) (c + 5)))

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (vis c v t : Word) (r1 r2 r3 : List Word)
theorem dvW_step : dvW p (n + 1) m vis c =
    dvK1 p n vis c (rdW (m.arr64 EREC) (c + 5)) (rdW (m.arr64 EREC) (c + 4))
      (ivgW n m vis (c + 1) (rdW (m.arr64 EREC) (c + 5))) := rfl
theorem dvK1_some : dvK1 p n vis c v t (some (r1, m1)) =
    dvK2 p n vis c t (stubM "infer_type_core" m1 [vis, 0, v]) := rfl
theorem dvK2_some : dvK2 p n vis c t (some (r2, m2)) =
    dvK3 p n vis c (stubM "is_def_eq_core" m2 [vis, 0, r2.headD 0, t]) := rfl
theorem dvK3_some : dvK3 p n vis c (some (r3, m3)) =
    if r3.headD 0 = 0 then none else dvK4 (callW p n "env_push" [vis, c] m3) := rfl
theorem dvK4_some (r4 : List Word) (m4 : Mem) : dvK4 (some (r4, m4)) = some ([r4.headD 0], m4) :=
  rfl
end arms

grind_pattern [ind_grind] dvW_step => dvW p (n + 1) m vis c
grind_pattern [ind_grind] dvK1_some => dvK1 p n vis c v t (some (r1, m1))
grind_pattern [ind_grind] dvK2_some => dvK2 p n vis c t (some (r2, m2))
grind_pattern [ind_grind] dvK3_some => dvK3 p n vis c (some (r3, m3))
grind_pattern [ind_grind] dvK4_some => dvK4 (some (r4, m4))

theorem dvBody_specW (h : ValProg p) (body : FunDecl) (hb : body = checkDefnValL) (n : Nat)
    (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ callFn (exec p n) body [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ dvW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  subst hb
  simp only [callFn, checkDefnValL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        ivg_specW p h.cvg n, stubM_spec p "infer_type_core" n,
        stubM_spec p "is_def_eq_core" n, callW_spec p n "env_push"] <;>
      finish (gen := 20) [rdW_eq]

theorem dv_specW (h : ValProg p) (n : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_defn_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ dvW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.dv]
  exact dvBody_specW p h _ rfl n s₀ vis c

theorem ov_specW (h : ValProg p) (n : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_opaque_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ dvW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.ov]
  exact dvBody_specW p h _ rfl n s₀ vis c

/-! ## `check_thm_val(vis, c)` -/

/-- After `lvl_eq_fueled`: abort on `false`, then `check_defn_val`'s tail. -/
def tvK4 (n : Nat) (vis c v t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if r4.headD 0 = 0 then none else dvK1 p n vis c v t (ivgW n m4 vis (c + 1) v)

/-- After the zero level. -/
def tvK3 (n : Nat) (vis c v t u : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => tvK4 p n vis c v t (lveW m3 u (r3.headD 0))

/-- After `ensure_sort_core`. -/
def tvK2 (n : Nat) (vis c v t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => tvK3 p n vis c v t (r2.headD 0) (pinWordW m2 53)

/-- After the type's type. -/
def tvK1 (n : Nat) (vis c v t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => tvK2 p n vis c v t (stubM "ensure_sort_core" m1 [vis, 0, r1.headD 0])

/-- **The model of `check_thm_val`.** -/
def tvW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, c =>
    tvK1 p n vis c (rdW (m.arr64 EREC) (c + 5)) (rdW (m.arr64 EREC) (c + 4))
      (stubM "infer_type_core" m [vis, 0, rdW (m.arr64 EREC) (c + 4)])

section arms
variable (n : Nat) (m m1 m2 m3 m4 : Mem) (vis c v t u : Word) (r1 r2 r3 r4 : List Word)
theorem tvW_step : tvW p (n + 1) m vis c =
    tvK1 p n vis c (rdW (m.arr64 EREC) (c + 5)) (rdW (m.arr64 EREC) (c + 4))
      (stubM "infer_type_core" m [vis, 0, rdW (m.arr64 EREC) (c + 4)]) := rfl
theorem tvK1_some : tvK1 p n vis c v t (some (r1, m1)) =
    tvK2 p n vis c v t (stubM "ensure_sort_core" m1 [vis, 0, r1.headD 0]) := rfl
theorem tvK2_some : tvK2 p n vis c v t (some (r2, m2)) =
    tvK3 p n vis c v t (r2.headD 0) (pinWordW m2 53) := rfl
theorem tvK3_some : tvK3 p n vis c v t u (some (r3, m3)) =
    tvK4 p n vis c v t (lveW m3 u (r3.headD 0)) := rfl
theorem tvK4_some : tvK4 p n vis c v t (some (r4, m4)) =
    if r4.headD 0 = 0 then none else dvK1 p n vis c v t (ivgW n m4 vis (c + 1) v) := rfl
end arms

grind_pattern [ind_grind] tvW_step => tvW p (n + 1) m vis c
grind_pattern [ind_grind] tvK1_some => tvK1 p n vis c v t (some (r1, m1))
grind_pattern [ind_grind] tvK2_some => tvK2 p n vis c v t (some (r2, m2))
grind_pattern [ind_grind] tvK3_some => tvK3 p n vis c v t u (some (r3, m3))
grind_pattern [ind_grind] tvK4_some => tvK4 p n vis c v t (some (r4, m4))

set_option maxHeartbeats 1600000 in
theorem tv_specW (h : ValProg p) (n : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_thm_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ tvW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.tv]
  simp only [callFn, checkThmValL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        pinWord_specW p h.cvg.pin n, lvlEqFueled_spec p h.lef n,
        ivg_specW p h.cvg n, stubM_spec p "infer_type_core" n,
        stubM_spec p "ensure_sort_core" n,
        stubM_spec p "is_def_eq_core" n, callW_spec p n "env_push"] <;>
      finish (gen := 20) [rdW_eq]

end models

end L.Arena
