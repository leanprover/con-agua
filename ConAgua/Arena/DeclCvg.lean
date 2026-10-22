import ConAgua.Arena.DeclStep
import ConAgua.Arena.CoreLevels
import ConAgua.Arena.Pins
import ConAgua.Arena.Frame
import ConAgua.Arena.IndPartsSpec2
import ConAgua.Arena.IndMaster
import ConAgua.Arena.IndInstallSpec
import ConAgua.Arena.IndStubs

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
`lvl_eq`). A program `p` that agrees with it on the reached functions (`CvgProg p`) has the same
write set (`closedW_of_agree`). When a stub's lane lands its function, `cvgProg` takes the real one
and the `decide` reruns.
-/

open ConRon.Arena

namespace L.Arena

open L.Front (DECL DLP)

/-- The arrays a step may write: all but the pending checks and the declaration records. -/
def stepA : List ArrId := (List.range 256).filter fun b => b ≠ PEND ∧ b ≠ DECL ∧ b ≠ DLP

/-- The `CTL` words a step may write: all but the pending checks' count. -/
def stepC : List Word := ((List.range 1024).filter (· ≠ 130)).map UInt64.ofNat

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

set_option profiler true in
theorem cvgProg_closed : closedA cvgProg stepA stepC cvgFns = true := by decide +kernel

/-- A program with `check_value_group`'s text. -/
def CvgProg (p : Prog) : Prop := ∀ f ∈ cvgFns, p.lookup f = cvgProg.lookup f

theorem CvgProg.closed {p : Prog} (h : CvgProg p) : closedA p stepA stepC cvgFns = true :=
  closedW_of_agree cvgProg_closed h

section lookups
variable {p : Prog} (h : CvgProg p)
include h
theorem CvgProg.cvg : p.lookup "check_value_group" = some checkValueGroupL :=
  (h _ (by decide)).trans rfl
theorem CvgProg.reset : p.lookup "iw_reset" = some L.Ind.iwReset := (h _ (by decide)).trans rfl
theorem CvgProg.pin : p.lookup "pin_word" = some pinWordL := (h _ (by decide)).trans rfl
theorem CvgProg.ivg : p.lookup "install_value_guards" = some installValueGuardsL :=
  (h _ (by decide)).trans rfl
theorem CvgProg.lps : p.lookup "cv_lps" = some L.Ind.cvLps := (h _ (by decide)).trans rfl
theorem CvgProg.eti : p.lookup "er_to_iw" = some L.Ind.erToIw := (h _ (by decide)).trans rfl
theorem CvgProg.alloc : p.lookup "iw_alloc" = some L.Ind.iwAlloc := (h _ (by decide)).trans rfl
theorem CvgProg.copy : p.lookup "er_copy" = some L.Ind.erCopy := (h _ (by decide)).trans rfl
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
/-- **The model of `install_value_guards`.** -/
def ivgW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, vis, q, v => ivgK1 vis v (cvLpsW n m q)

def ivgK1 (vis v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => ivgK2 vis v r1 (stubM "loose_bvars_bounded_fast" m1 [4000000000, 0, v])

def ivgK2 (vis v : Word) (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then none else ivgK3 vis v r1 (stubM "has_fvar_fast" m2 [4000000000, v])

def ivgK3 (vis v : Word) (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 ≠ 0 then none
    else ivgK4 vis v (stubM "all_level_params_defined" m3 [r1.headD 0, r1.tail.headD 0, v])

def ivgK4 (vis v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if r4.headD 0 = 0 then none else ivgK5 (stubM "consts_resolve_ffast" m4 [vis, v])

def ivgK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => if r5.headD 0 = 0 then none else some ([0], m5)
end

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis q v : Word) (r1 r2 r3 r4 r5 : List Word)
theorem ivgW_step : ivgW (n + 1) m vis q v = ivgK1 vis v (cvLpsW n m q) := rfl
theorem ivgK1_some : ivgK1 vis v (some (r1, m1)) =
    ivgK2 vis v r1 (stubM "loose_bvars_bounded_fast" m1 [4000000000, 0, v]) := rfl
theorem ivgK2_some : ivgK2 vis v r1 (some (r2, m2)) =
    if r2.headD 0 = 0 then none else ivgK3 vis v r1 (stubM "has_fvar_fast" m2 [4000000000, v]) :=
  rfl
theorem ivgK3_some : ivgK3 vis v r1 (some (r3, m3)) =
    if r3.headD 0 ≠ 0 then none
    else ivgK4 vis v (stubM "all_level_params_defined" m3 [r1.headD 0, r1.tail.headD 0, v]) := rfl
theorem ivgK4_some : ivgK4 vis v (some (r4, m4)) =
    if r4.headD 0 = 0 then none else ivgK5 (stubM "consts_resolve_ffast" m4 [vis, v]) := rfl
theorem ivgK5_some : ivgK5 (some (r5, m5)) = if r5.headD 0 = 0 then none else some ([0], m5) :=
  rfl
end arms

grind_pattern [ind_grind] ivgW_step => ivgW (n + 1) m vis q v
grind_pattern [ind_grind] ivgK1_some => ivgK1 vis v (some (r1, m1))
grind_pattern [ind_grind] ivgK2_some => ivgK2 vis v r1 (some (r2, m2))
grind_pattern [ind_grind] ivgK3_some => ivgK3 vis v r1 (some (r3, m3))
grind_pattern [ind_grind] ivgK4_some => ivgK4 vis v (some (r4, m4))
grind_pattern [ind_grind] ivgK5_some => ivgK5 (some (r5, m5))

theorem ivg_specW (p : Prog) (h : CvgProg p) (n : Nat) (s₀ : St) (vis q v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_value_guards" [vis, q, v]
    ⦃fun r s' => LocEq s' s₀ ∧ ivgW n s₀.mem vis q v = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.ivg]
  simp only [callFn, installValueGuardsL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        cvLps_specW p h.alloc h.copy h.eti h.lps n,
        stubM_spec p "loose_bvars_bounded_fast" n, stubM_spec p "has_fvar_fast" n,
        stubM_spec p "all_level_params_defined" n, stubM_spec p "consts_resolve_ffast" n] <;>
      finish (gen := 20)

/-! ### `check_value_group(vis, g)` -/

mutual
/-- **The model of `check_value_group`** (after `iw_reset`, the type `t` and value `v` read). -/
def cvgW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, g => cvgK0 n vis g (iwResetW m)

def cvgK0 (n : Nat) (vis g : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m0) =>
    cvgK1 n vis g (rdW (m0.arr64 EREC) (g + 4)) (rdW (m0.arr64 EREC) (g + 5))
      (stubM "infer_type_core" m0 [vis, 0, rdW (m0.arr64 EREC) (g + 4)])

def cvgK1 (n : Nat) (vis g t v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => cvgK2 n vis g t v (stubM "ensure_sort_core" m1 [vis, 0, r1.headD 0])

def cvgK2 (n : Nat) (vis g t v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if rdW (m2.arr64 EREC) g = 1 then cvgK3 n vis g t v (r2.headD 0) (pinWordW m2 53)
    else cvgK6 vis t v m2

def cvgK3 (n : Nat) (vis g t v u : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => cvgK4 n vis g t v (stubM "lvl_eq_c" m3 [u, r3.headD 0])

def cvgK4 (n : Nat) (vis g t v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => if r4.headD 0 ≠ 2 then none else cvgK5 vis t v (ivgW n m4 vis (g + 1) v)

def cvgK5 (vis t v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m5) => cvgK6 vis t v m5

def cvgK6 (vis t v : Word) (m : Mem) : Option (List Word × Mem) :=
  cvgK7 vis t (stubM "infer_type_core" m [vis, 0, v])

def cvgK7 (vis t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r7, m7) => cvgK8 (stubM "is_def_eq_core" m7 [vis, 0, r7.headD 0, t])

def cvgK8 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r8, m8) => if r8.headD 0 = 0 then none else some ([0], m8)
end

section arms
variable (n : Nat) (m m0 m1 m2 m3 m4 m5 m7 m8 : Mem) (vis g t v u : Word)
  (r0 r1 r2 r3 r4 r5 r7 r8 : List Word)
theorem cvgW_step : cvgW (n + 1) m vis g = cvgK0 n vis g (iwResetW m) := rfl
theorem cvgK0_some : cvgK0 n vis g (some (r0, m0)) =
    cvgK1 n vis g (rdW (m0.arr64 EREC) (g + 4)) (rdW (m0.arr64 EREC) (g + 5))
      (stubM "infer_type_core" m0 [vis, 0, rdW (m0.arr64 EREC) (g + 4)]) := rfl
theorem cvgK1_some : cvgK1 n vis g t v (some (r1, m1)) =
    cvgK2 n vis g t v (stubM "ensure_sort_core" m1 [vis, 0, r1.headD 0]) := rfl
theorem cvgK2_some : cvgK2 n vis g t v (some (r2, m2)) =
    if rdW (m2.arr64 EREC) g = 1 then cvgK3 n vis g t v (r2.headD 0) (pinWordW m2 53)
    else cvgK6 vis t v m2 := rfl
theorem cvgK3_some : cvgK3 n vis g t v u (some (r3, m3)) =
    cvgK4 n vis g t v (stubM "lvl_eq_c" m3 [u, r3.headD 0]) := rfl
theorem cvgK4_some : cvgK4 n vis g t v (some (r4, m4)) =
    if r4.headD 0 ≠ 2 then none else cvgK5 vis t v (ivgW n m4 vis (g + 1) v) := rfl
theorem cvgK5_some : cvgK5 vis t v (some (r5, m5)) = cvgK6 vis t v m5 := rfl
theorem cvgK6_eq : cvgK6 vis t v m = cvgK7 vis t (stubM "infer_type_core" m [vis, 0, v]) := rfl
theorem cvgK7_some : cvgK7 vis t (some (r7, m7)) =
    cvgK8 (stubM "is_def_eq_core" m7 [vis, 0, r7.headD 0, t]) := rfl
theorem cvgK8_some : cvgK8 (some (r8, m8)) = if r8.headD 0 = 0 then none else some ([0], m8) :=
  rfl
end arms

grind_pattern [ind_grind] cvgW_step => cvgW (n + 1) m vis g
grind_pattern [ind_grind] cvgK0_some => cvgK0 n vis g (some (r0, m0))
grind_pattern [ind_grind] cvgK1_some => cvgK1 n vis g t v (some (r1, m1))
grind_pattern [ind_grind] cvgK2_some => cvgK2 n vis g t v (some (r2, m2))
grind_pattern [ind_grind] cvgK3_some => cvgK3 n vis g t v u (some (r3, m3))
grind_pattern [ind_grind] cvgK4_some => cvgK4 n vis g t v (some (r4, m4))
grind_pattern [ind_grind] cvgK5_some => cvgK5 vis t v (some (r5, m5))
grind_pattern [ind_grind] cvgK6_eq => cvgK6 vis t v m
grind_pattern [ind_grind] cvgK7_some => cvgK7 vis t (some (r7, m7))
grind_pattern [ind_grind] cvgK8_some => cvgK8 (some (r8, m8))

set_option maxHeartbeats 1600000 in
theorem cvg_specW (p : Prog) (h : CvgProg p) (n : Nat) (s₀ : St) (vis g : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_value_group" [vis, g]
    ⦃fun r s' => LocEq s' s₀ ∧ cvgW n s₀.mem vis g = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.cvg]
  simp only [callFn, checkValueGroupL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        iwReset_specW p h.reset n, pinWord_specW p h.pin n, ivg_specW p h n,
        stubM_spec p "infer_type_core" n, stubM_spec p "ensure_sort_core" n,
        stubM_spec p "lvl_eq_c" n, stubM_spec p "is_def_eq_core" n] <;>
      finish (gen := 20)

end L.Arena

/-! ## The relational lemmas: a model run from the stage relation is a twin run -/

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

theorem allocMem_zero_grow (m : Mem) (hc : 200 < (m.arr64 CTL).size) : IWGrow m (allocMem m 0) := by
  have hf := allocMem_frame m 0
  have hI : (allocMem m 0).arr64 IW = m.arr64 IW := allocMem_IW m 0
  have hE : (allocMem m 0).arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp [EREC, IW]) (by decide)
  have ht : rdW ((allocMem m 0).arr64 CTL) 200 = rdW (m.arr64 CTL) 200 := by
    rw [allocMem_top m 0 hc]; simp
  refine ⟨?_, ?_, fun i _ => by rw [hI], fun i _ => by rw [hE]⟩
  · simp only [iwTop, ht]; exact Nat.le_refl _
  · simp only [erTop, hf.2.1 129 (by simp)]; exact Nat.le_refl _

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

/-- Destructuring a constant value: its name, its universe-parameter slice, its type. -/
theorem decCV_words {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
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

/-- **`install_value_guards` refines `installValueGuards`** at the model level. -/
theorem ivgW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {q v : Word} {r : List Word} {cv : IConstantVal}
    (h : ivgW n m vis q v = some (r, m')) (hS : StageR dn vis fe m a)
    (hq : decCV (erA m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64) (hv : v.toNat < 2 ^ 32) :
    ∃ a', (installValueGuards fe cv (decI v)).run a = .ok ((), a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_words hq
  have e1 : rdW (m.arr64 EREC) (q + 1) = w1 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw1
  have e2 : rdW (m.arr64 EREC) (q + 2) = w2 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw2
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (hslice?_bound _ _ _ _ hsl h0)
  cases n with
  | zero => simp [ivgW] at h
  | succ n =>
  cases n with
  | zero => simp [ivgW, cvLpsW, ivgK1] at h
  | succ n =>
  rw [ivgW_step, cvLpsW_step, e1, e2] at h
  cases h1 : erToIwW n m w1 w2 with
  | none => rw [h1] at h; simp [ivgK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, ivgK1_some] at h
  obtain ⟨-, hr1t, hdec1, hS1, hg1, htop1⟩ := erToIwW_stage h1 hS hsrc
  cases h2 : stubM "loose_bvars_bounded_fast" m1 [4000000000, 0, v] with
  | none => rw [h2] at h; simp [ivgK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, ivgK2_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2, -⟩ :=
    looseBVarsBoundedFast_spec dn vis fe 4000000000 0 v hv m1 m2 a r2 h2 hS1
  by_cases hb2 : r2.headD 0 = 0
  · rw [if_pos hb2] at h; simp at h
  rw [if_neg hb2] at h
  cases h3 : stubM "has_fvar_fast" m2 [4000000000, v] with
  | none => rw [h3] at h; simp [ivgK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, ivgK3_some] at h
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3, -⟩ :=
    hasFvarFast_spec dn vis fe 4000000000 v hv m2 m3 a2 r3 h3 hS2
  by_cases hb3 : r3.headD 0 ≠ 0
  · rw [if_pos hb3] at h; simp at h
  rw [if_neg hb3] at h
  rw [hr1t] at h
  cases h4 : stubM "all_level_params_defined" m3 [r1.headD 0, w2, v] with
  | none => rw [h4] at h; simp [ivgK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, ivgK4_some] at h
  have hdec3 : decHL m3 (r1.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [decHL_grow (hg2.trans hg3) (by omega), hdec1]; exact hsl
  obtain ⟨x4, a4, hrun4, hS4, hg4, hx4, -⟩ :=
    allLevelParamsDefined_spec dn vis fe (r1.headD 0) w2 v hv cv.levelParams m3 m4 a3 r4 h4
      ⟨hS3, hdec3⟩
  by_cases hb4 : r4.headD 0 = 0
  · rw [if_pos hb4] at h; simp at h
  rw [if_neg hb4] at h
  cases h5 : stubM "consts_resolve_ffast" m4 [vis, v] with
  | none => rw [h5] at h; simp [ivgK5] at h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, ivgK5_some] at h
  obtain ⟨x5, a5, hrun5, hS5, hg5, hx5, -⟩ :=
    constsResolveFFast_spec dn vis fe v hv m4 m5 a4 r5 h5 hS4
  by_cases hb5 : r5.headD 0 = 0
  · rw [if_pos hb5] at h; simp at h
  rw [if_neg hb5] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have ex2 : x2 = true := by rw [← hx2]; simpa using hb2
  have ex3 : x3 = false := by rw [← hx3]; simpa using hb3
  have ex4 : x4 = true := by rw [← hx4]; simpa using hb4
  have ex5 : x5 = true := by rw [← hx5]; simpa using hb5
  rw [fuelW] at hrun2 hrun3
  refine ⟨a5, ?_, hS5, hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5)))⟩
  rw [show ((0 : Word).toNat) = 0 from rfl] at hrun2
  simp only [installValueGuards, StateT.run_bind, hrun2, exc_ok_bind', ex2, hrun3, ex3, hrun4,
    ex4, hrun5, ex5, if_true, Bool.false_eq_true, if_false, StateT.run_pure]
  rfl

/-- **`install_value_guards` refines `installValueGuards`** (through the stubs of the walks). -/
@[refines ConRon.Arena.installValueGuards]
theorem installValueGuards_refines (p : Prog) (hC : CvgProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q v : Word) (cv : IConstantVal)
    (hS : StageR dn vis fe s₀.mem a₀) (hq : decCV (erA s₀.mem) q.toNat = some cv)
    (hqb : q.toNat + 3 < 2 ^ 64) (hv : v.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_value_guards" [vis, q, v]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installValueGuards fe cv (decI v)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (installValueGuards fe cv (decI v)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (ivg_specW p hC n s₀ vis q v) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hS', hg⟩ := ivgW_ok hm hS hq hqb hv
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg⟩

/-- **`lvl_eq_c(u, v)` under the stage relation** (`sorry`): lane `whnf`'s `lvlEqC_refines` proves
it under `CoreS`, which has the readback-cache invariants and `NStoreWF` that `StageR` lacks; the
stub `lvl_eq` of lane `indproofs` has the same gap (and calls the uncached `lvl_eq`). -/
theorem lvlEqCStage_spec (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (u v : Word)
    (hu : H u) (hv : H v) :
    RelAM "lvl_eq_c" [u, v] (StageR dn vis fe) (lvlEq? (decI u) (decI v))
      (KeepPost dn vis fe decLvlEq) := sorry

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

/-- **`check_value_group` refines `checkValueGroup .verified`** at the model level, from the
memory after `iw_reset`. -/
theorem cvgW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {g : Word} {r : List Word} {vg : ValueGroup}
    (h : cvgW n m vis g = some (r, m')) (hS : StageR dn vis fe m a)
    (hg : decVG (erecP m) g.toNat = some vg) :
    ∃ a', (checkValueGroup V fe vg).run a = .ok ((), a') ∧ StageR dn vis fe m' a' ∧
      IWGrow (m.set64 CTL 200 0) m' := by
  cases n with
  | zero => simp [cvgW] at h
  | succ n =>
  rw [cvgW_step, show iwResetW m = some ([], m.set64 CTL 200 0) from rfl, cvgK0_some] at h
  generalize hm0 : m.set64 CTL 200 0 = m0 at h
  obtain ⟨hS0, -, hE0, -⟩ := iwReset_stage hS
  rw [hm0] at hS0 hE0
  have hP0 : erecP m0 = erecP m := by rw [← hm0]; exact erecP_reset m
  rw [← hP0] at hg
  have hEs := hS0.2.2.2.2.1
  obtain ⟨⟨wk, hwk, hvk⟩, hcv, wj, hwj, hwjl, hjv⟩ := decVG_words hg
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hb5 : g.toNat + 5 < (m0.arr64 EREC).size := by
    have := (Array.getElem?_eq_some_iff.mp (erecP_get hwj)).1; exact this
  have et : rdW (m0.arr64 EREC) (g + 4) = wt :=
    rdW_of_get? (k := g.toNat + 4) (by rw [UInt64.toNat_add]; simp; omega)
      (erecP_get (by simpa [Nat.add_assoc] using hwt))
  have ev : rdW (m0.arr64 EREC) (g + 5) = wj :=
    rdW_of_get? (k := g.toNat + 5) (by rw [UInt64.toNat_add]; simp; omega) (erecP_get hwj)
  rw [et, ev] at h
  -- `infer_type_core(vis, 0, t)`
  cases h1 : stubM "infer_type_core" m0 [vis, 0, wt] with
  | none => rw [h1] at h; simp [cvgK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, cvgK1_some] at h
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1l, hx1⟩ :=
    inferTypeCore_spec dn vis fe 0 wt hwtl m0 m1 a r1 h1 hS0
  -- `ensure_sort_core(vis, 0, st)`
  cases h2 : stubM "ensure_sort_core" m1 [vis, 0, r1.headD 0] with
  | none => rw [h2] at h; simp [cvgK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, cvgK2_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    ensureSortCore_spec dn vis fe 0 (r1.headD 0) hx1l m1 m2 a1 r2 h2 hS1
  have hext2 : ArrExt (erecP m0) (erA m2) := IWGrow.erecExt (hg1.trans hg2)
  have ek : rdW (m2.arr64 EREC) g = wk := rdW_of_get? rfl (hext2 _ _ hwk)
  rw [ek] at h
  have h00 : (0 : Word).toNat = 0 := rfl
  rw [h00] at hrun1 hrun2
  rw [← hty] at hrun1
  rw [hx1] at hrun2
  -- the tail: `infer_type_core(vis, 0, v)`, `is_def_eq_core(vis, 0, vt, t)`
  have tail : ∀ (m5 : Mem) (a5 : AState), StageR dn vis fe m5 a5 → IWGrow m0 m5 →
      cvgK6 vis wt wj m5 = some (r, m') →
      ∃ a', (do
          let vtype ← inferTypeCore V fe checkFuel 0 vg.jv
          unless ← isDefEqCore V fe checkFuel 0 vtype vg.cv.type do
            fail (.invalid s!"type mismatch in {vg.kind.word}") : AM Unit).run a5 = .ok ((), a') ∧
        StageR dn vis fe m' a' ∧ IWGrow m0 m' := by
    intro m5 a5 hS5 hg5 h
    rw [cvgK6_eq] at h
    cases h7 : stubM "infer_type_core" m5 [vis, 0, wj] with
    | none => rw [h7] at h; simp [cvgK7] at h
    | some rm7 =>
    obtain ⟨r7, m7⟩ := rm7
    rw [h7, cvgK7_some] at h
    obtain ⟨x7, a7, hrun7, hS7, hg7, hx7l, hx7⟩ :=
      inferTypeCore_spec dn vis fe 0 wj hwjl m5 m7 a5 r7 h7 hS5
    cases h8 : stubM "is_def_eq_core" m7 [vis, 0, r7.headD 0, wt] with
    | none => rw [h8] at h; simp [cvgK8] at h
    | some rm8 =>
    obtain ⟨r8, m8⟩ := rm8
    rw [h8, cvgK8_some] at h
    obtain ⟨x8, a8, hrun8, hS8, hg8, hx8, -⟩ :=
      isDefEqCore_spec dn vis fe 0 (r7.headD 0) wt hx7l hwtl m7 m8 a7 r8 h8 hS7
    by_cases hb8 : r8.headD 0 = 0
    · rw [if_pos hb8] at h; simp at h
    rw [if_neg hb8] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have ex8 : x8 = true := by rw [← hx8]; simpa using hb8
    rw [h00, ← hjv] at hrun7
    rw [h00, hx7, ← hty] at hrun8
    refine ⟨a8, ?_, hS8, hg5.trans (hg7.trans hg8)⟩
    simp only [StateT.run_bind, hrun7, exc_ok_bind', hrun8, ex8, if_true, StateT.run_pure]
    rfl
  by_cases hk1 : wk = 1
  · -- a theorem: the proposition test and the value's guards
    rw [if_pos hk1] at h
    subst hk1
    have hkind : vg.kind = .thm := by simpa [decVK] using hvk.symm
    cases h3 : pinWordW m2 53 with
    | none => rw [h3] at h; simp [cvgK3] at h
    | some rm3 =>
    obtain ⟨r3, m3⟩ := rm3
    rw [h3, cvgK3_some] at h
    have hflag : pinW m2 0 ≠ 0 := by
      intro h0; simp [pinWordW, h0] at h3
    simp only [pinWordW, hflag, if_false, Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    have hF := hS2.1.pins.full hflag
    have hz : rdW (m2.arr64 PINS) 53 = pinW m2 53 := by simp [rdW, pinW]
    simp only [List.headD_cons, hz] at h
    cases h4 : stubM "lvl_eq_c" m2 [r2.headD 0, pinW m2 53] with
    | none => rw [h4] at h; simp [cvgK4] at h
    | some rm4 =>
    obtain ⟨r4, m4⟩ := rm4
    rw [h4, cvgK4_some] at h
    obtain ⟨x4, a4, hrun4, hS4, hg4, hx4⟩ :=
      lvlEqCStage_spec dn vis fe (r2.headD 0) (pinW m2 53) hx2l hF.lv_lt.2.1 m2 m4 a2 r4 h4 hS2
    by_cases hb4 : r4.headD 0 ≠ 2
    · rw [if_pos hb4] at h; simp at h
    rw [if_neg hb4] at h
    have ex4 : x4 = some true := by
      simp only [L.Ind.decLvlEq] at hx4
      have : r4.headD 0 = 2 := by simpa using hb4
      rw [this] at hx4
      cases x4 with
      | none => simp at hx4
      | some b =>
        cases b with
        | false => simp at hx4
        | true => rfl
    cases h5 : ivgW n m4 vis (g + 1) wj with
    | none => rw [h5] at h; simp [cvgK5] at h
    | some rm5 =>
    obtain ⟨r5, m5⟩ := rm5
    rw [h5, cvgK5_some] at h
    have hg1' : (g + 1).toNat = g.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hcv4 : decCV (erA m4) (g + 1).toNat = some vg.cv := by
      rw [hg1']
      exact ArrExt.decCV (IWGrow.erecExt (hg1.trans (hg2.trans hg4))) hcv
    obtain ⟨a5, hrun5, hS5, hg5⟩ :=
      ivgW_ok h5 hS4 hcv4 (by rw [hg1']; omega) hwjl
    obtain ⟨a', hrun', hS', hg'⟩ :=
      tail m5 a5 hS5 (hg1.trans (hg2.trans (hg4.trans hg5))) h
    refine ⟨a', ?_, hS', hg'⟩
    rw [hx2] at hrun4
    rw [← hjv] at hrun5
    rw [ex4] at hrun4
    rw [hkind] at hrun'
    simp only [checkValueGroup, StateT.run_bind, hrun1, exc_ok_bind', hrun2, hkind,
      show (ValueKind.thm == ValueKind.thm) = true from rfl, if_true, zeroLevel,
      pinZeroLevel_run hF, hrun4, liftFueled, StateT.run_pure, hrun5]
    simp only [pure_bind, if_true, StateT.run_bind, hrun5, exc_ok_bind']
    exact hrun'
  · rw [if_neg hk1] at h
    have hkind : vg.kind ≠ .thm := by
      intro hk; rw [hk] at hvk
      have : wk.toNat = 1 := by
        unfold decVK at hvk; split at hvk <;> simp_all
      exact hk1 (UInt64.toNat_inj.mp (by simpa using this))
    obtain ⟨a', hrun', hS', hg'⟩ := tail m2 a2 hS2 (hg1.trans hg2) h
    refine ⟨a', ?_, hS', hg'⟩
    have hb : (vg.kind == ValueKind.thm) = false := by
      revert hkind; cases vg.kind <;> decide
    simp only [checkValueGroup, StateT.run_bind, hrun1, exc_ok_bind', hrun2, hb,
      Bool.false_eq_true, if_false]
    exact hrun'

end L.Arena
