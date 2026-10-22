import ConAgua.Arena.RecClassSpecL

/-!
# `RecClass`: `ClassGen.prefixBinders` (lane `indproofs2`, helper `rec2`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Models -/

def fcK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

/-- **The model of `class_gen_prefix_binders_find_ctor_go`.** -/
def fcgW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, io, il, cn =>
    if il = 0 then some ([0, 0], m)
    else if rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) io)) = cn then
      some ([1, rdW (m.arr64 IW) io], m)
    else fcK (fcgW n m (io + 1) (il - 1) cn)

/-- **The model of `class_gen_prefix_binders_find_ctor`.** -/
def fcW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, g, c, cn =>
    if rdW (m.arr64 IW) (g + 10) ≤ c then some ([0, 0], m)
    else fcK (fcgW n m (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 9) + c)))
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 9) + c) + 1)) cn)

def psK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([1, r3.headD 0, r3.tail.headD 0], m3)

def psK2 (n : Nat) (ty : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0, 0], m2)
    else psK3 (consW n m2 ty (r2.tail.headD 0) (r2.tail.tail.headD 0))

/-- After the slot's type: the rest (`next`), then the cons. -/
def psK1 (n : Nat) (next : Mem → Option (List Word × Mem)) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if r1.headD 0 = 0 then some ([0, 0, 0], m1) else psK2 n (r1.tail.headD 0) (next m1)

/-- After `find_ctor`: the minor premise's type. -/
def psK4 (n : Nat) (next : Mem → Option (List Word × Mem)) (g cls d : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if r4.headD 0 = 0 then some ([0, 0, 0], m4)
    else psK1 n next (mnW n m4 g cls (r4.tail.headD 0) d)

/-- **The model of `class_gen_prefix_binders_slots_go`.** -/
def psW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, g, s, mc =>
    if rdW (m.arr64 IW) (g + 8) ≤ s then some ([1, 0, 0], m)
    else if rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s)) = 0 then
      psK1 n (fun m1 => psW n m1 g (s + 1) (mc + 1))
        (motW n m g mc (rdW (m.arr64 IW) g + s))
    else psK4 n (fun m1 => psW n m1 g (s + 1) mc) g
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s) + 1)) (rdW (m.arr64 IW) g + s)
      (fcW n m g (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s) + 1))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s) + 2)))

def pbK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([1, r3.headD 0, r3.tail.headD 0], m3)

def pbK2 (n : Nat) (pbo pbl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0, 0], m2)
    else pbK3 (appendW n m2 pbo pbl (r2.tail.headD 0) (r2.tail.tail.headD 0))

def pbK1 (n : Nat) (g : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => pbK2 n (r1.headD 0) (r1.tail.headD 0) (psW n m1 g 0 0)

/-- **The model of `class_gen_prefix_binders`.** -/
def pbW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, g => pbK1 n g (stubM "fvar_type_ds" m [rdW (m.arr64 IW) (g + 1), rdW (m.arr64 IW) (g + 2)])

/-! ## Arms -/

section arms
variable (n : Nat) (m m1 m2 m3 m4 : Mem) (g c cn io il s mc ty cls d pbo pbl : Word)
  (r r1 r2 r3 r4 : List Word) (next : Mem → Option (List Word × Mem))
theorem fcK_some : fcK (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
theorem fcgW_nil (h : il = 0) : fcgW (n + 1) m io il cn = some ([0, 0], m) := by simp [fcgW, h]
theorem fcgW_hit (h : ¬ il = 0) (h2 : rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) io)) = cn) :
    fcgW (n + 1) m io il cn = some ([1, rdW (m.arr64 IW) io], m) := by
  simp only [fcgW]; rw [if_neg h, if_pos h2]
theorem fcgW_miss (h : ¬ il = 0) (h2 : ¬ rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) io)) = cn) :
    fcgW (n + 1) m io il cn = fcK (fcgW n m (io + 1) (il - 1) cn) := by
  simp only [fcgW]; rw [if_neg h, if_neg h2]
theorem fcW_none (h : rdW (m.arr64 IW) (g + 10) ≤ c) : fcW (n + 1) m g c cn = some ([0, 0], m) := by
  simp only [fcW]; rw [if_pos h]
theorem fcW_go (h : ¬ rdW (m.arr64 IW) (g + 10) ≤ c) : fcW (n + 1) m g c cn =
    fcK (fcgW n m (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 9) + c)))
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 9) + c) + 1)) cn) := by
  simp only [fcW]; rw [if_neg h]
theorem psK3_some : psK3 (some (r3, m3)) = some ([1, r3.headD 0, r3.tail.headD 0], m3) := rfl
theorem psK2_fail (h : r2.headD 0 = 0) : psK2 n ty (some (r2, m2)) = some ([0, 0, 0], m2) := by
  rw [psK2, if_pos h]
theorem psK2_ok (h : r2.headD 0 ≠ 0) : psK2 n ty (some (r2, m2)) =
    psK3 (consW n m2 ty (r2.tail.headD 0) (r2.tail.tail.headD 0)) := by rw [psK2, if_neg h]
theorem psK1_fail (h : r1.headD 0 = 0) : psK1 n next (some (r1, m1)) = some ([0, 0, 0], m1) := by
  rw [psK1, if_pos h]
theorem psK1_ok (h : r1.headD 0 ≠ 0) : psK1 n next (some (r1, m1)) = psK2 n (r1.tail.headD 0) (next m1) := by
  rw [psK1, if_neg h]
theorem psK4_fail (h : r4.headD 0 = 0) : psK4 n next g cls d (some (r4, m4)) = some ([0, 0, 0], m4) := by
  rw [psK4, if_pos h]
theorem psK4_ok (h : r4.headD 0 ≠ 0) : psK4 n next g cls d (some (r4, m4)) =
    psK1 n next (mnW n m4 g cls (r4.tail.headD 0) d) := by rw [psK4, if_neg h]
theorem psW_end (h : rdW (m.arr64 IW) (g + 8) ≤ s) : psW (n + 1) m g s mc = some ([1, 0, 0], m) := by
  simp only [psW]; rw [if_pos h]
theorem psW_mot (h : ¬ rdW (m.arr64 IW) (g + 8) ≤ s)
    (h2 : rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s)) = 0) :
    psW (n + 1) m g s mc = psK1 n (fun m1 => psW n m1 g (s + 1) (mc + 1))
      (motW n m g mc (rdW (m.arr64 IW) g + s)) := by
  simp only [psW]; rw [if_neg h, if_pos h2]
theorem psW_min (h : ¬ rdW (m.arr64 IW) (g + 8) ≤ s)
    (h2 : ¬ rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s)) = 0) :
    psW (n + 1) m g s mc = psK4 n (fun m1 => psW n m1 g (s + 1) mc) g
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s) + 1)) (rdW (m.arr64 IW) g + s)
      (fcW n m g (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s) + 1))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s) + 2))) := by
  simp only [psW]; rw [if_neg h, if_neg h2]
theorem pbW_eq : pbW (n + 1) m g =
    pbK1 n g (stubM "fvar_type_ds" m [rdW (m.arr64 IW) (g + 1), rdW (m.arr64 IW) (g + 2)]) := rfl
theorem pbK1_some : pbK1 n g (some (r1, m1)) = pbK2 n (r1.headD 0) (r1.tail.headD 0) (psW n m1 g 0 0) := rfl
theorem pbK2_fail (h : r2.headD 0 = 0) : pbK2 n pbo pbl (some (r2, m2)) = some ([0, 0, 0], m2) := by
  rw [pbK2, if_pos h]
theorem pbK2_ok (h : r2.headD 0 ≠ 0) : pbK2 n pbo pbl (some (r2, m2)) =
    pbK3 (appendW n m2 pbo pbl (r2.tail.headD 0) (r2.tail.tail.headD 0)) := by rw [pbK2, if_neg h]
theorem pbK3_some : pbK3 (some (r3, m3)) = some ([1, r3.headD 0, r3.tail.headD 0], m3) := rfl
end arms

attribute [ind_grind] fcK_some fcgW_nil fcgW_hit fcgW_miss fcW_none fcW_go psK3_some psK2_fail psK2_ok
  psK1_fail psK1_ok psK4_fail psK4_ok psW_end psW_mot psW_min pbW_eq pbK1_some pbK2_fail pbK2_ok pbK3_some

/-! ## Specs -/

/-- The lookups `class_gen_prefix_binders` needs. -/
structure PbProg (p : Prog) extends MnProg p : Prop where
  fcg : p.lookup "class_gen_prefix_binders_find_ctor_go" = some classGenPrefixBindersFindCtorGo
  fc : p.lookup "class_gen_prefix_binders_find_ctor" = some classGenPrefixBindersFindCtor
  psg : p.lookup "class_gen_prefix_binders_slots_go" = some classGenPrefixBindersSlotsGo
  pb : p.lookup "class_gen_prefix_binders" = some classGenPrefixBinders

section specs
variable (p : Prog) (h : PbProg p)
include h

theorem findCtorGo_spec (n : Nat) : ∀ (s₀ : St) (io il cn : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_prefix_binders_find_ctor_go" [io, il, cn]
    ⦃fun r s' => LocEq s' s₀ ∧ fcgW n s₀.mem io il cn = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ io il cn
    rw [invoke_eq _ h.fcg]; simp only [callFn, classGenPrefixBindersFindCtorGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ io il cn
    rw [invoke_eq _ h.fcg]
    simp only [callFn, classGenPrefixBindersFindCtorGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem findCtor_spec (n : Nat) (s₀ : St) (g c cn : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_prefix_binders_find_ctor" [g, c, cn]
    ⦃fun r s' => LocEq s' s₀ ∧ fcW n s₀.mem g c cn = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.fc]
  simp only [callFn, classGenPrefixBindersFindCtor]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, findCtorGo_spec p h n] <;>
      finish (gen := 20) [rdW_eq]

theorem slotsGo_spec (n : Nat) : ∀ (s₀ : St) (g s mc : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "class_gen_prefix_binders_slots_go" [g, s, mc]
    ⦃fun r s' => LocEq s' s₀ ∧ psW n s₀.mem g s mc = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ g s mc
    rw [invoke_eq _ h.psg]; simp only [callFn, classGenPrefixBindersSlotsGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ g s mc
    rw [invoke_eq _ h.psg]
    simp only [callFn, classGenPrefixBindersSlotsGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        classGenMotiveTy_spec p h.toMtProg n, findCtor_spec p h n, classGenMinorTy_spec p h.toMnProg n,
        slCons_specW p h.alloc h.copy h.cons n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq]

theorem prefixBinders_spec (n : Nat) (s₀ : St) (g : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_prefix_binders" [g]
    ⦃fun r s' => LocEq s' s₀ ∧ pbW n s₀.mem g = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.pb]
  simp only [callFn, classGenPrefixBinders]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "fvar_type_ds" n, slotsGo_spec p h n, slAppend_specW p h.alloc h.copy h.app n] <;>
      finish (gen := 20) [rdW_eq]

end specs

end L.Ind
