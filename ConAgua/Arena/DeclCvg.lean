import ConAgua.Arena.DeclStep
import ConAgua.Arena.IndRealWalk
import ConAgua.Arena.CoreLevels
import ConAgua.Arena.Pins
import ConAgua.Arena.Frame
import ConAgua.Arena.IndPartsSpec2
import ConAgua.Arena.IndMaster
import ConAgua.Arena.IndInstallSpec
import ConAgua.Arena.IndStubs
import ConAgua.Arena.IndCallM

/-!
# Phase B's check, `check_value_group`: its write set from the text

The declaration loop's relation `LoopR` has, beside the stage relation (`StageR = CheckR ∧ IWOK`,
what every callee keeps), the pending checks (`PEND`, `CTL[130]`) and the front's declaration
records (`DECL`, `DLP`). No callee spec mentions them (a stub's `RelAM` post is `KeepPost`), so
they come from the program text (`closedA`, DESIGN "The relation's architecture"): every function
`check_value_group` reaches writes only arrays other than `PEND`/`DECL`/`DLP` and `CTL` words
other than `130`.

The text is a concrete program `cvgProg`: this lane's functions, lane `induct`'s library and stubs,
and the real master callees (`pin_word`, lane `whnf`'s `lvl_eq_c` with lane `levels`'
`lvl_eq`). A program `p` with that text (`CvgProg p`, a `TextProg`) agrees with it on the reached
functions but `openFns` (the core's entry points and the walks: real code in the checker, stubs
here) and has the write set on a call-closed superset (`StepIn`; for the checker's program,
`ConAgua/Checker/LoopDecl.lean`).
-/

noncomputable section

open ConRon.Arena

namespace L.Arena

open L.Front (DECL DLP)

/-- The arrays a step may write: all but the pending checks and the declaration records. -/
def stepA : List ArrId :=
  (List.range 388).filter fun b => b ≠ PEND ∧ b ≠ DECL ∧ b ≠ DLP ∧ (b < 146 ∨ 149 < b)

/-- The `CTL` words a step may write: all but the pending checks' count, the promotion memos'
words and the pin variant list's header (`CTL[150]`, `CTL[151]`, lane `romload`). -/
def stepC : List Word :=
  ((List.range 1024).filter fun x => x ≠ 130 ∧ x ≠ 150 ∧ x ≠ 151 ∧ (x < 140 ∨ 147 < x)).map
    UInt64.ofNat

/-- `check_value_group`'s text: this lane's functions, lane `induct`'s library and stubs, and the
real master callees it reaches. -/
def cvgProg : Prog :=
  declStepFns ++ L.Ind.libFns ++ L.Ind.stubFns ++ [("pin_word", pinWordL)] ++
    [("lvl_eq_c", lvlEqCL), ("lvl_eq_rec", lvlEqRecL), ("lq_find", memoFindG lqSch),
     ("lq_put", memoPutG lqSch)] ++ levelProg

/-- The functions `check_value_group` reaches. -/
def cvgFns : List FnName :=
  ["check_value_group", "iw_reset", "infer_type_core", "ensure_sort_core", "pin_word", "lvl_eq_c",
   "lq_find", "lvl_eq_rec", "lvl_eq", "lv_equiv", "lv_eq", "lv_node", "lv_simp", "lh_mk", "lv_comb",
   "lv_leq", "lv_rest", "lv_imax", "lv_cases", "lv_cases_at", "lv_subsimp", "lv_subst", "lv_imax_l",
   "lv_dist1", "lv_dist2", "lv_imax_r", "lq_put", "install_value_guards", "cv_lps", "er_to_iw",
   "iw_alloc", "er_copy", "loose_bvars_bounded_fast", "has_fvar_fast", "all_level_params_defined",
   "consts_resolve_ffast", "is_def_eq_core"]

/-- **The callees the declaration texts do not fix** (lane `loopt2`): real code in the checker's
program, stubs in the texts (`cvgProg`, `ivProg`, `armText`): the core's entry points, the walks,
the ROM readers and the gates' leaves. Their specs come from their own refinements (or
`stubM_spec`), never from the texts' lookups; their write set is the checker's (`StepIn`). -/
def openFns : List FnName :=
  ["infer_type_core", "ensure_sort_core", "is_def_eq_core", "loose_bvars_bounded_fast",
   "has_fvar_fast", "all_level_params_defined", "nat_lit_supported", "rom_cv",
   "rom_ci", "rom_expr_pin", "rom_basis_decls", "rom_basis_decls_a", "rom_pin_sets",
   "consts_resolve_ffast"]

/-- **`fs` lies in a call-closed function set with a step's write set** (`stepA`, `stepC`). -/
def StepIn (p : Prog) (fs : List FnName) : Prop :=
  ∃ F : List FnName, (∀ f ∈ fs, f ∈ F) ∧ closedA p stepA stepC F = true

open Std.WP in
open scoped Lean.Order in
/-- A function of `fs` keeps the memory outside a step's write set (`invoke_memFrame`). -/
theorem StepIn.memFrame {p : Prog} {fs : List FnName} (h : StepIn p fs) (n : Nat) {f : FnName}
    (hf : f ∈ fs) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs
    ⦃fun _ s => MemFrame stepA stepC s₀.mem s.mem ∧ s.mem.bytes = s₀.mem.bytes; ⊤⦄ :=
  by obtain ⟨_, hF, hc⟩ := h; exact invoke_memFrame hc n (hF f hf) vs s₀

/-- **A program with a text `q` on the functions `fs`**: it agrees with `q` on `fs` but
`openFns`, and `fs` has a step's write set in it. -/
structure TextProg (p q : Prog) (fs : List FnName) : Prop where
  agree : ∀ f ∈ fs, f ∉ openFns → p.lookup f = q.lookup f
  closed : StepIn p fs

/-- A program with `check_value_group`'s text. -/
structure CvgProg (p : Prog) : Prop extends TextProg p cvgProg cvgFns where
  bvb : BvbProg p
  hf : L.Ind.HfF p

section lookups
variable {p : Prog} (h : CvgProg p)
include h
theorem CvgProg.cvg : p.lookup "check_value_group" = some checkValueGroupL :=
  (h.agree _ (by decide) (by decide)).trans rfl
theorem CvgProg.reset : p.lookup "iw_reset" = some L.Ind.iwReset :=
  (h.agree _ (by decide) (by decide)).trans rfl
theorem CvgProg.pin : p.lookup "pin_word" = some pinWordL :=
  (h.agree _ (by decide) (by decide)).trans rfl
theorem CvgProg.ivg : p.lookup "install_value_guards" = some installValueGuardsL :=
  (h.agree _ (by decide) (by decide)).trans rfl
theorem CvgProg.lps : p.lookup "cv_lps" = some L.Ind.cvLps :=
  (h.agree _ (by decide) (by decide)).trans rfl
theorem CvgProg.eti : p.lookup "er_to_iw" = some L.Ind.erToIw :=
  (h.agree _ (by decide) (by decide)).trans rfl
theorem CvgProg.alloc : p.lookup "iw_alloc" = some L.Ind.iwAlloc :=
  (h.agree _ (by decide) (by decide)).trans rfl
theorem CvgProg.copy : p.lookup "er_copy" = some L.Ind.erCopy :=
  (h.agree _ (by decide) (by decide)).trans rfl
end lookups

end L.Arena

/-! ## Word models and their `vcgen` specs (no twin values) -/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

/-- The model of `pin_word(k)`. -/
def pinWordW (m : Mem) (k : Word) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else some ([rdW (m.arr64 PINS) k], m)

theorem pinWord_specW (p : Prog) (hp : p.lookup "pin_word" = some pinWordL) (n : Nat) (s₀ : St)
    (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_word" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ pinWordW s₀.mem k = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, pinWordL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [pinWordW, pinW_eq, rdW_eq]

/-- The model of `iw_reset()`. -/
def iwResetW (m : Mem) : Option (List Word × Mem) := some ([], m.set64 CTL 200 0)

theorem iwReset_specW (p : Prog) (hp : p.lookup "iw_reset" = some iwReset) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "iw_reset" []
    ⦃fun r s' => LocEq s' s₀ ∧ iwResetW s₀.mem = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iwReset]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
      finish [iwResetW]

/-- The model of `cv_lps(q)` (its copy runs at `n - 1`). -/
def cvLpsW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, q => erToIwW n m (rdW (m.arr64 EREC) (q + 1)) (rdW (m.arr64 EREC) (q + 2))

theorem cvLpsW_step (n : Nat) (m : Mem) (q : Word) :
    cvLpsW (n + 1) m q = erToIwW n m (rdW (m.arr64 EREC) (q + 1)) (rdW (m.arr64 EREC) (q + 2)) :=
  rfl

grind_pattern [ind_grind] cvLpsW_step => cvLpsW (n + 1) m q

theorem cvLps_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw)
    (hp : p.lookup "cv_lps" = some cvLps) (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cv_lps" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ cvLpsW n s₀.mem q = some (r, s'.mem) ∧
      r = [r.headD 0, r.tail.headD 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, cvLps]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        erToIw_specW2 p ha hc he n] <;>
      finish (gen := 20)

/-! ### `install_value_guards(vis, q, v)` -/

mutual
/-- **The model of `install_value_guards`**, `all_level_params_defined` and `consts_resolve_ffast`
read through `cl` (`stubCall`
for the `StageR` proofs, `realCall p` under `StageT`). -/
def ivgW (cl : CallM) : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, vis, q, v => ivgK1 cl n vis v (cvLpsW n m q)

def ivgK1 (cl : CallM) (n : Nat) (vis v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => ivgK2 cl n vis v r1 (lbbF m1 [4000000000, 0, v])

def ivgK2 (cl : CallM) (n : Nat) (vis v : Word) (r1 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then none else ivgK3 cl n vis v r1 (hffF m2 [4000000000, v])

def ivgK3 (cl : CallM) (n : Nat) (vis v : Word) (r1 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 ≠ 0 then none
    else ivgK4 cl n vis v (cl n "all_level_params_defined" [r1.headD 0, r1.tail.headD 0, v] m3)

def ivgK4 (cl : CallM) (n : Nat) (vis v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if r4.headD 0 = 0 then none else ivgK5 (cl n "consts_resolve_ffast" [vis, v] m4)

def ivgK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => if r5.headD 0 = 0 then none else some ([0], m5)
end

section arms
variable (cl : CallM) (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis q v : Word) (r1 r2 r3 r4 r5 : List Word)
theorem ivgW_step : ivgW cl (n + 1) m vis q v = ivgK1 cl n vis v (cvLpsW n m q) := rfl
theorem ivgK1_some : ivgK1 cl n vis v (some (r1, m1)) =
    ivgK2 cl n vis v r1 (lbbF m1 [4000000000, 0, v]) := rfl
theorem ivgK2_some : ivgK2 cl n vis v r1 (some (r2, m2)) =
    if r2.headD 0 = 0 then none else ivgK3 cl n vis v r1 (hffF m2 [4000000000, v]) :=
  rfl
theorem ivgK3_some : ivgK3 cl n vis v r1 (some (r3, m3)) =
    if r3.headD 0 ≠ 0 then none
    else ivgK4 cl n vis v (cl n "all_level_params_defined" [r1.headD 0, r1.tail.headD 0, v] m3) :=
  rfl
theorem ivgK4_some : ivgK4 cl n vis v (some (r4, m4)) =
    if r4.headD 0 = 0 then none else ivgK5 (cl n "consts_resolve_ffast" [vis, v] m4) := rfl
theorem ivgK5_some : ivgK5 (some (r5, m5)) = if r5.headD 0 = 0 then none else some ([0], m5) :=
  rfl
end arms

grind_pattern [ind_grind] ivgW_step => ivgW cl (n + 1) m vis q v
grind_pattern [ind_grind] ivgK1_some => ivgK1 cl n vis v (some (r1, m1))
grind_pattern [ind_grind] ivgK2_some => ivgK2 cl n vis v r1 (some (r2, m2))
grind_pattern [ind_grind] ivgK3_some => ivgK3 cl n vis v r1 (some (r3, m3))
grind_pattern [ind_grind] ivgK4_some => ivgK4 cl n vis v (some (r4, m4))
grind_pattern [ind_grind] ivgK5_some => ivgK5 (some (r5, m5))

theorem ivg_specW (p : Prog) (h : CvgProg p) (cl : CallM) (hc : CallSpec p cl) (n : Nat) (s₀ : St)
    (vis q v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_value_guards" [vis, q, v]
    ⦃fun r s' => LocEq s' s₀ ∧ ivgW cl n s₀.mem vis q v = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.ivg]
  simp only [callFn, installValueGuardsL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        cvLps_specW p h.alloc h.copy h.eti h.lps n,
        lbbF_spec p h.bvb n, hffF_spec p h.hf n,
        hc n "all_level_params_defined", hc n "consts_resolve_ffast"] <;>
      finish (gen := 20)

/-! ### `check_value_group(vis, g)` -/

-- `CallM`, `stubCall`, `realCall`, `CallSpec`: `IndCallM.lean`.

mutual
/-- **The model of `check_value_group`** (after `iw_reset`, the type `t` and value `v` read), the
core's entry points read through `c`. -/
def cvgW (c : CallM) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, g => cvgK0 c n vis g (iwResetW m)

def cvgK0 (c : CallM) (n : Nat) (vis g : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m0) =>
    cvgK1 c n vis g (rdW (m0.arr64 EREC) (g + 4)) (rdW (m0.arr64 EREC) (g + 5))
      (c n "infer_type_core" [vis, 0, rdW (m0.arr64 EREC) (g + 4)] m0)

def cvgK1 (c : CallM) (n : Nat) (vis g t v : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => cvgK2 c n vis g t v (c n "ensure_sort_core" [vis, 0, r1.headD 0] m1)

def cvgK2 (c : CallM) (n : Nat) (vis g t v : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if rdW (m2.arr64 EREC) g = 1 then cvgK3 c n vis g t v (r2.headD 0) (pinWordW m2 53)
    else cvgK6 c n vis t v m2

def cvgK3 (c : CallM) (n : Nat) (vis g t v u : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => cvgK4 c n vis g t v (c n "lvl_eq_c" [u, r3.headD 0] m3)

def cvgK4 (c : CallM) (n : Nat) (vis g t v : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => if r4.headD 0 ≠ 2 then none else cvgK5 c n vis t v (ivgW c n m4 vis (g + 1) v)

def cvgK5 (c : CallM) (n : Nat) (vis t v : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m5) => cvgK6 c n vis t v m5

def cvgK6 (c : CallM) (n : Nat) (vis t v : Word) (m : Mem) : Option (List Word × Mem) :=
  cvgK7 c n vis t (c n "infer_type_core" [vis, 0, v] m)

def cvgK7 (c : CallM) (n : Nat) (vis t : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r7, m7) => cvgK8 (c n "is_def_eq_core" [vis, 0, r7.headD 0, t] m7)

def cvgK8 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r8, m8) => if r8.headD 0 = 0 then none else some ([0], m8)
end

section arms
variable (c : CallM) (n : Nat) (m m0 m1 m2 m3 m4 m5 m7 m8 : Mem) (vis g t v u : Word)
  (r0 r1 r2 r3 r4 r5 r7 r8 : List Word)
theorem cvgW_step : cvgW c (n + 1) m vis g = cvgK0 c n vis g (iwResetW m) := rfl
theorem cvgK0_some : cvgK0 c n vis g (some (r0, m0)) =
    cvgK1 c n vis g (rdW (m0.arr64 EREC) (g + 4)) (rdW (m0.arr64 EREC) (g + 5))
      (c n "infer_type_core" [vis, 0, rdW (m0.arr64 EREC) (g + 4)] m0) := rfl
theorem cvgK1_some : cvgK1 c n vis g t v (some (r1, m1)) =
    cvgK2 c n vis g t v (c n "ensure_sort_core" [vis, 0, r1.headD 0] m1) := rfl
theorem cvgK2_some : cvgK2 c n vis g t v (some (r2, m2)) =
    if rdW (m2.arr64 EREC) g = 1 then cvgK3 c n vis g t v (r2.headD 0) (pinWordW m2 53)
    else cvgK6 c n vis t v m2 := rfl
theorem cvgK3_some : cvgK3 c n vis g t v u (some (r3, m3)) =
    cvgK4 c n vis g t v (c n "lvl_eq_c" [u, r3.headD 0] m3) := rfl
theorem cvgK4_some : cvgK4 c n vis g t v (some (r4, m4)) =
    if r4.headD 0 ≠ 2 then none else cvgK5 c n vis t v (ivgW c n m4 vis (g + 1) v) := rfl
theorem cvgK5_some : cvgK5 c n vis t v (some (r5, m5)) = cvgK6 c n vis t v m5 := rfl
theorem cvgK6_eq : cvgK6 c n vis t v m = cvgK7 c n vis t (c n "infer_type_core" [vis, 0, v] m) := rfl
theorem cvgK7_some : cvgK7 c n vis t (some (r7, m7)) =
    cvgK8 (c n "is_def_eq_core" [vis, 0, r7.headD 0, t] m7) := rfl
theorem cvgK8_some : cvgK8 (some (r8, m8)) = if r8.headD 0 = 0 then none else some ([0], m8) :=
  rfl
end arms

grind_pattern [ind_grind] cvgW_step => cvgW c (n + 1) m vis g
grind_pattern [ind_grind] cvgK0_some => cvgK0 c n vis g (some (r0, m0))
grind_pattern [ind_grind] cvgK1_some => cvgK1 c n vis g t v (some (r1, m1))
grind_pattern [ind_grind] cvgK2_some => cvgK2 c n vis g t v (some (r2, m2))
grind_pattern [ind_grind] cvgK3_some => cvgK3 c n vis g t v u (some (r3, m3))
grind_pattern [ind_grind] cvgK4_some => cvgK4 c n vis g t v (some (r4, m4))
grind_pattern [ind_grind] cvgK5_some => cvgK5 c n vis t v (some (r5, m5))
grind_pattern [ind_grind] cvgK6_eq => cvgK6 c n vis t v m
grind_pattern [ind_grind] cvgK7_some => cvgK7 c n vis t (some (r7, m7))
grind_pattern [ind_grind] cvgK8_some => cvgK8 (some (r8, m8))

set_option maxHeartbeats 1600000 in
theorem cvg_specW (p : Prog) (h : CvgProg p) (c : CallM) (hc : CallSpec p c) (n : Nat) (s₀ : St)
    (vis g : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_value_group" [vis, g]
    ⦃fun r s' => LocEq s' s₀ ∧ cvgW c n s₀.mem vis g = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.cvg]
  simp only [callFn, checkValueGroupL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        iwReset_specW p h.reset n, pinWord_specW p h.pin n, ivg_specW p h c hc n,
        hc n "infer_type_core", hc n "ensure_sort_core", hc n "lvl_eq_c", hc n "is_def_eq_core"] <;>
      finish (gen := 20)

end L.Arena

/-! ## The relational lemmas: a model run from the stage relation is a twin run -/

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- **`er_to_iw` under the stage relation**: the copy decodes as the `EREC` slice, the stage
relation holds after it, the pool only grew. A zero-length copy needs no source bound. -/
theorem erToIwW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : erToIwW n m o l = some (r, m'))
    (hS : StageR dn vis fe m a) (hsrc : l.toNat = 0 ∨ o.toNat + l.toNat ≤ (m.arr64 EREC).size) :
    r = [r.headD 0, r.tail.headD 0] ∧ r.tail.headD 0 = l ∧
    (∀ {k : IdxKind}, (decHL m' (r.headD 0).toNat l.toNat : Option (List (Idx k))) =
      hslice? (erA m) o.toNat l.toNat) ∧
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ (r.headD 0).toNat + l.toNat ≤ iwTop m' := by
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  have hh := erToIwW_two h
  rcases hsrc with hl0 | hsrc
  · have hl : l = 0 := UInt64.toNat_inj.mp (by simpa using hl0)
    subst hl
    simp only [erToIwW] at h
    cases hal : allocW m 0 with
    | none => simp [hal] at h
    | some qm =>
    obtain ⟨q, m1⟩ := qm
    obtain ⟨hS1, hg1, -, -⟩ := allocW_stage hal hS
    obtain ⟨rfl, rfl, -⟩ := allocW_facts hal hsz
    simp only [hal] at h
    cases n with
    | zero => simp [erCopyW] at h
    | succ n =>
    cases n with
    | zero => simp [erCopyW] at h
    | succ n =>
    simp only [Nat.add_sub_cancel, erCopyW_nil n _ _ _ _ rfl, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, rfl, fun {k} => ?_, hS1, hg1, ?_⟩
    · simp [decHL, hslice?]
    · have := allocMem_top m 0 hc
      simp only [iwTop, this]; simp
  · obtain ⟨hr, hdec, hgrow, hfr, hEeq, htop⟩ := erToIwW_dec (k := IdxKind.name) h hsz hc hEs hsrc
    have hdec' : ∀ {k : IdxKind}, (decHL m' (rdW (m.arr64 CTL) 200).toNat l.toNat :
        Option (List (Idx k))) = hslice? (erA m) o.toNat l.toNat := fun {k} =>
      (erToIwW_dec (k := k) h hsz hc hEs hsrc).2.1
    subst hr
    refine ⟨rfl, rfl, fun {k} => hdec', ⟨CheckR.frame_iw hfr hS.1, ?_, ?_, ?_, ?_, ?_⟩, hgrow,
      by simp only [List.headD_cons]; omega⟩
    · -- the new top is in bounds: the allocation checked the room
      simp only [erToIwW] at h
      cases hal : allocW m l with
      | none => simp [hal] at h
      | some qm =>
        obtain ⟨q, m1⟩ := qm
        obtain ⟨-, -, hroom⟩ := allocW_facts hal hsz
        obtain ⟨hq, -, -⟩ := allocW_facts hal hsz
        rw [← htop, hfr.2.2.1 IW]; subst hq; exact hroom
    · simp only [erTop, hfr.2.1 129 (by simp), hEeq]; exact hE1
    · rw [hfr.2.2.1 IW]; exact hsz
    · rw [hEeq]; exact hEs
    · rw [hfr.2.2.1 CTL]; exact hc

/-- **`er_to_iw` writes only the pool and its top** (`IW`, `CTL[200]`). -/
theorem erToIwW_frame {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : erToIwW n m o l = some (r, m'))
    (hS : StageR dn vis fe m a) (hsrc : l.toNat = 0 ∨ o.toNat + l.toNat ≤ (m.arr64 EREC).size) :
    MemFrame [IW] [200] m m' := by
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  rcases hsrc with hl0 | hsrc
  · have hl : l = 0 := UInt64.toNat_inj.mp (by simpa using hl0)
    subst hl
    simp only [erToIwW] at h
    cases hal : allocW m 0 with
    | none => simp [hal] at h
    | some qm =>
    obtain ⟨q, m1⟩ := qm
    obtain ⟨rfl, rfl, -⟩ := allocW_facts hal hsz
    simp only [hal] at h
    cases n with
    | zero => simp [erCopyW] at h
    | succ n =>
    cases n with
    | zero => simp [erCopyW] at h
    | succ n =>
    simp only [Nat.add_sub_cancel, erCopyW_nil n _ _ _ _ rfl, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact allocMem_frame m 0
  · exact (erToIwW_dec (k := IdxKind.name) h hsz hc hEs hsrc).2.2.2.1

/-- Destructuring a constant value: its name, its universe-parameter slice, its type. -/
theorem decCV_slice {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    ∃ w1 w2, a[q + 1]? = some w1 ∧ a[q + 2]? = some w2 ∧
      hslice? a w1.toNat w2.toNat = some cv.levelParams := by
  simp only [decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨nm, -, lv, hlv, ty, -, rfl⟩ := h
  simp only [hlist?, bind, Option.bind_eq_some_iff] at hlv
  obtain ⟨o', ho2, l', hl2, hsl⟩ := hlv
  simp only [nat?, Option.map_eq_some_iff] at ho2 hl2
  obtain ⟨w1, hw1, rfl⟩ := ho2
  obtain ⟨w2, hw2, rfl⟩ := hl2
  exact ⟨w1, w2, hw1, hw2, hsl⟩

theorem rdW_of_get? {a : Array Word} {x w : Word} {k : Nat} (hk : k = x.toNat) (h : a[k]? = some w) :
    rdW a x = w := by
  subst hk; simp [rdW, h]

theorem exc_ok_bind' {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl

theorem fuelW : (4000000000 : Word).toNat = coreWalkFuel := rfl

theorem decVG_words {a : Array Word} {g : Nat} {vg : ValueGroup} (h : decVG a g = some vg) :
    (∃ wk, a[g]? = some wk ∧ decVK wk.toNat = some vg.kind) ∧ decCV a (g + 1) = some vg.cv ∧
    ∃ wj, a[g + 5]? = some wj ∧ wj.toNat < 2 ^ 32 ∧ vg.jv = decI wj := by
  simp only [decVG, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨k, hk, vk, hvk, cv, hcv, jv, hjv, rfl⟩ := h
  simp only [nat?, Option.map_eq_some_iff] at hk
  obtain ⟨wk, hwk, rfl⟩ := hk
  obtain ⟨wj, hwj, hlt, rfl⟩ := hd?_some hjv
  exact ⟨⟨wk, hwk, hvk⟩, hcv, wj, hwj, hlt, rfl⟩

theorem decCV_typeW {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    ∃ w, a[q + 3]? = some w ∧ w.toNat < 2 ^ 32 ∧ cv.type = decI w := by
  simp only [decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨_, _, _, _, ty, hty, rfl⟩ := h
  exact hd?_some hty

/-- A grown pool keeps every record of the old one. -/
theorem IWGrow.erecExt {m m' : Mem} (h : IWGrow m m') : ArrExt (erecP m) (erA m') := by
  intro i v hv
  simp only [erecP, Array.getElem?_extract] at hv
  split at hv
  · rename_i hi
    simp only [Nat.zero_add] at hv
    have hi' : i < erTop m := by simp [erTop, erecTop] at hi ⊢; omega
    simp only [erA]; rw [h.2.2.2 i hi']; exact hv
  · simp at hv

/-- The memory after `iw_reset` is in the stage relation. -/
theorem iwReset_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (hS : StageR dn vis fe m a) :
    StageR dn vis fe (m.set64 CTL 200 0) a ∧ m.set64 CTL 200 0 = m.set64 CTL 200 0 ∧
      (m.set64 CTL 200 0).arr64 EREC = m.arr64 EREC ∧ erTop (m.set64 CTL 200 0) = erTop m := by
  have hf : MemFrame [] [200] m (m.set64 CTL 200 0) := MemFrame.setCtl m 200 0
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  have hE : (m.set64 CTL 200 0).arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp) (by decide)
  have h129 : erTop (m.set64 CTL 200 0) = erTop m := by simp only [erTop, hf.2.1 129 (by simp)]
  refine ⟨⟨CheckR.frame_hi (by simp) (by simp) hf hS.1, ?_, ?_, ?_, ?_, ?_⟩, rfl, hE, h129⟩
  · have hIW := hf.2.2.1 IW
    simp only [iwTop, rdW_set64]; split
    · simp
    · rw [hIW]; exact hI1
  · rw [h129, hE]; exact hE1
  · rw [hf.2.2.1 IW]; exact hsz
  · rw [hE]; exact hEs
  · rw [hf.2.2.1 CTL]; exact hc

theorem erecP_reset (m : Mem) : erecP (m.set64 CTL 200 0) = erecP m := by
  have hf : MemFrame [] [200] m (m.set64 CTL 200 0) := MemFrame.setCtl m 200 0
  simp only [erecP, erecTop, hf.1 EREC (by simp) (by decide), hf.2.1 129 (by simp)]

theorem word_add_toNat (g : Word) (k : Nat) (h : g.toNat + k < 2 ^ 64) :
    (g + UInt64.ofNat k).toNat = g.toNat + k := by
  rw [UInt64.toNat_add]; simp; omega

end L.Arena
