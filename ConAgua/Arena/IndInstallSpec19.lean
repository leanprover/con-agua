import ConAgua.Arena.IndInstallSpec18

/-!
# Refinements of `IndInstall`, part 19 (lane `indproofs2`, helper `install`): `checkAbsCtorSorts`,
`checkAbsCtorSortsAll`, the word models
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `check_abs_ctor_sorts_one` -/

def iaoK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([0], m)
def iaoK1 (p : Prog) (n : Nat) (vis isP nF hi srt : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else iaoK2 (callW p n "check_struct_field_sorts_i" [vis, isP, 0, srt, hi, r.tail.headD 0,
      r.tail.tail.headD 0, 0, 0, nF] m)

/-- **The model of `check_abs_ctor_sorts_one(vis, ctx, isProp, nF, tyN, hi)`** (body fuel `n`). -/
def iaoW (p : Prog) (n : Nat) (m : Mem) (vis ctx isP nF tyN hi : Word) : Option (List Word × Mem) :=
  if hi + nF < hi then none
  else iaoK1 p n vis isP nF hi (rdW (m.arr64 IW) (ctx + 9)) (callW p n "open_pis_at_fvars_f" [nF, tyN, hi] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis isP nF hi srt : Word) (r : List Word)
theorem iaoK2_some : iaoK2 (some (r, m)) = some ([0], m) := rfl
theorem iaoK1_none (h : r.headD 0 = 0) : iaoK1 p n vis isP nF hi srt (some (r, m)) = none := by
  simp only [iaoK1, h, ↓reduceIte]
theorem iaoK1_some (h : ¬ r.headD 0 = 0) : iaoK1 p n vis isP nF hi srt (some (r, m)) =
    iaoK2 (callW p n "check_struct_field_sorts_i" [vis, isP, 0, srt, hi, r.tail.headD 0,
      r.tail.tail.headD 0, 0, 0, nF] m) := by simp only [iaoK1, h, ↓reduceIte, if_false]
end arms
attribute [ind_grind] iaoK2_some iaoK1_none iaoK1_some

theorem iao_spec (p : Prog) (hp : p.lookup "check_abs_ctor_sorts_one" = some checkAbsCtorSortsOne)
    (n : Nat) (s₀ : St) (vis ctx isP nF tyN hi : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_abs_ctor_sorts_one" [vis, ctx, isP, nF, tyN, hi]
    ⦃fun r s' => LocEq s' s₀ ∧ iaoW p n s₀.mem vis ctx isP nF tyN hi = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkAbsCtorSortsOne]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "open_pis_at_fvars_f", callW_spec p n "check_struct_field_sorts_i"] <;>
    finish (gen := 40) (instances := 20000) [iaoW, rdW_eq]

/-! ## `check_abs_ctor_sorts` -/

def iacK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([0], m)

mutual
/-- **The model of `check_abs_ctor_sorts(vis, ctx, isProp, cO, cL, oO, oL)`** at exec fuel `n`. -/
def iacW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, ctx, isP, co, cl, oo, ol =>
    if cl = 0 then some ([0], m) else if ol = 0 then some ([0], m)
    else iacK1 p n vis ctx isP co cl oo ol (rdW (m.arr64 IW) co) (rdW (m.arr64 IW) oo)
      (callW p n "all_level_params_defined" [rdW (m.arr64 IW) (ctx + 2), rdW (m.arr64 IW) (ctx + 3),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) oo + 2)] m)
def iacK1 (p : Prog) (n : Nat) (vis ctx isP co cl oo ol c o : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else iacK2 p n vis ctx isP co cl oo ol c o (callW p n "nest_ctx_hi_at" [ctx, 0] m)
def iacK2 (p : Prog) (n : Nat) (vis ctx isP co cl oo ol c o : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => iacK3 p n vis ctx isP co cl oo ol (callW p n "check_abs_ctor_sorts_one"
      [vis, ctx, isP, rdW (m.arr64 IW) (c + 1), rdW (m.arr64 IW) (o + 2), r.headD 0] m)
def iacK3 (p : Prog) (n : Nat) (vis ctx isP co cl oo ol : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => iacK4 (iacW p n m vis ctx isP (co + 1) (cl - 1) (oo + 1) (ol - 1))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis ctx isP co cl oo ol c o : Word) (r : List Word)
theorem iacW_zero : iacW p 0 m vis ctx isP co cl oo ol = none := by simp [iacW]
theorem iacW_nil1 (h : cl = 0) : iacW p (n + 1) m vis ctx isP co cl oo ol = some ([0], m) := by
  simp [iacW, h]
theorem iacW_nil2 (h1 : cl ≠ 0) (h : ol = 0) : iacW p (n + 1) m vis ctx isP co cl oo ol = some ([0], m) := by
  simp [iacW, h1, h]
theorem iacW_cons (h1 : cl ≠ 0) (h2 : ol ≠ 0) : iacW p (n + 1) m vis ctx isP co cl oo ol =
    iacK1 p n vis ctx isP co cl oo ol (rdW (m.arr64 IW) co) (rdW (m.arr64 IW) oo)
      (callW p n "all_level_params_defined" [rdW (m.arr64 IW) (ctx + 2), rdW (m.arr64 IW) (ctx + 3),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) oo + 2)] m) := by simp [iacW, h1, h2]
theorem iacK1_none (h : r.headD 0 = 0) : iacK1 p n vis ctx isP co cl oo ol c o (some (r, m)) = none := by
  simp only [iacK1, h, ↓reduceIte]
theorem iacK1_some (h : ¬ r.headD 0 = 0) : iacK1 p n vis ctx isP co cl oo ol c o (some (r, m)) =
    iacK2 p n vis ctx isP co cl oo ol c o (callW p n "nest_ctx_hi_at" [ctx, 0] m) := by
  simp only [iacK1, h, ↓reduceIte, if_false]
theorem iacK2_some : iacK2 p n vis ctx isP co cl oo ol c o (some (r, m)) =
    iacK3 p n vis ctx isP co cl oo ol (callW p n "check_abs_ctor_sorts_one"
      [vis, ctx, isP, rdW (m.arr64 IW) (c + 1), rdW (m.arr64 IW) (o + 2), r.headD 0] m) := by simp [iacK2]
theorem iacK3_some : iacK3 p n vis ctx isP co cl oo ol (some (r, m)) =
    iacK4 (iacW p n m vis ctx isP (co + 1) (cl - 1) (oo + 1) (ol - 1)) := by simp [iacK3]
theorem iacK4_some : iacK4 (some (r, m)) = some ([0], m) := rfl
end arms
attribute [ind_grind] iacW_nil1 iacW_nil2 iacW_cons iacK1_none iacK1_some iacK2_some iacK3_some iacK4_some

set_option maxHeartbeats 1600000 in
theorem iac_spec (p : Prog) (hp : p.lookup "check_abs_ctor_sorts" = some checkAbsCtorSorts) (n : Nat) :
    ∀ (s₀ : St) (vis ctx isP co cl oo ol : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_abs_ctor_sorts" [vis, ctx, isP, co, cl, oo, ol]
    ⦃fun r s' => LocEq s' s₀ ∧ iacW p n s₀.mem vis ctx isP co cl oo ol = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis ctx isP co cl oo ol; rw [invoke_eq _ hp]; simp only [callFn, checkAbsCtorSorts]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis ctx isP co cl oo ol
    rw [invoke_eq _ hp]
    simp only [callFn, checkAbsCtorSorts]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "all_level_params_defined", callW_spec p n "nest_ctx_hi_at",
        callW_spec p n "check_abs_ctor_sorts_one", ih] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

/-! ## `check_abs_ctor_sorts_all` -/

def iaaK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([0], m)

mutual
/-- **The model of `check_abs_ctor_sorts_all(vis, ctx, isProp, sO, sL, oO, oL)`** at exec fuel `n`. -/
def iaaW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, ctx, isP, so, sl, oo, ol =>
    if sl = 0 then some ([0], m) else if ol = 0 then some ([0], m)
    else iaaK1 p n vis ctx isP so sl oo ol (callW p n "check_abs_ctor_sorts" [vis, ctx, isP,
      rdW (m.arr64 IW) (rdW (m.arr64 IW) so), rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 1),
      rdW (m.arr64 IW) (rdW (m.arr64 IW) oo), rdW (m.arr64 IW) (rdW (m.arr64 IW) oo + 1)] m)
def iaaK1 (p : Prog) (n : Nat) (vis ctx isP so sl oo ol : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => iaaK2 (iaaW p n m vis ctx isP (so + 1) (sl - 1) (oo + 1) (ol - 1))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis ctx isP so sl oo ol : Word) (r : List Word)
theorem iaaW_zero : iaaW p 0 m vis ctx isP so sl oo ol = none := by simp [iaaW]
theorem iaaW_nil1 (h : sl = 0) : iaaW p (n + 1) m vis ctx isP so sl oo ol = some ([0], m) := by
  simp [iaaW, h]
theorem iaaW_nil2 (h1 : sl ≠ 0) (h : ol = 0) : iaaW p (n + 1) m vis ctx isP so sl oo ol = some ([0], m) := by
  simp [iaaW, h1, h]
theorem iaaW_cons (h1 : sl ≠ 0) (h2 : ol ≠ 0) : iaaW p (n + 1) m vis ctx isP so sl oo ol =
    iaaK1 p n vis ctx isP so sl oo ol (callW p n "check_abs_ctor_sorts" [vis, ctx, isP,
      rdW (m.arr64 IW) (rdW (m.arr64 IW) so), rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 1),
      rdW (m.arr64 IW) (rdW (m.arr64 IW) oo), rdW (m.arr64 IW) (rdW (m.arr64 IW) oo + 1)] m) := by
  simp [iaaW, h1, h2]
theorem iaaK1_some : iaaK1 p n vis ctx isP so sl oo ol (some (r, m)) =
    iaaK2 (iaaW p n m vis ctx isP (so + 1) (sl - 1) (oo + 1) (ol - 1)) := by simp [iaaK1]
theorem iaaK2_some : iaaK2 (some (r, m)) = some ([0], m) := rfl
end arms
attribute [ind_grind] iaaW_nil1 iaaW_nil2 iaaW_cons iaaK1_some iaaK2_some

theorem iaa_spec (p : Prog) (hp : p.lookup "check_abs_ctor_sorts_all" = some checkAbsCtorSortsAll)
    (n : Nat) : ∀ (s₀ : St) (vis ctx isP so sl oo ol : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_abs_ctor_sorts_all" [vis, ctx, isP, so, sl, oo, ol]
    ⦃fun r s' => LocEq s' s₀ ∧ iaaW p n s₀.mem vis ctx isP so sl oo ol = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis ctx isP so sl oo ol; rw [invoke_eq _ hp]; simp only [callFn, checkAbsCtorSortsAll]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis ctx isP so sl oo ol
    rw [invoke_eq _ hp]
    simp only [callFn, checkAbsCtorSortsAll]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "check_abs_ctor_sorts", ih] <;>
      finish (gen := 20) [rdW_eq]

end L.Ind
