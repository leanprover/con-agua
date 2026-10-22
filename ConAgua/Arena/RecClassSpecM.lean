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

def pfK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([1, r3.headD 0, r3.tail.headD 0], m3)

def pfK2 (n : Nat) (ty : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0, 0], m2)
    else pfK3 (consW n m2 ty (r2.tail.headD 0) (r2.tail.tail.headD 0))

/-- After the slot's type: the rest (`next`), then the cons. -/
def pfK1 (n : Nat) (next : Mem → Option (List Word × Mem)) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if r1.headD 0 = 0 then some ([0, 0, 0], m1) else pfK2 n (r1.tail.headD 0) (next m1)

/-- After `find_ctor`: the minor premise's type. -/
def pfK4 (n : Nat) (next : Mem → Option (List Word × Mem)) (g cls d : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if r4.headD 0 = 0 then some ([0, 0, 0], m4)
    else pfK1 n next (mnW n m4 g cls (r4.tail.headD 0) d)

def pfR : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m)

mutual
/-- **The model of `class_gen_prefix_binders_slots_go`.** -/
def psW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, g, s, mc =>
    if rdW (m.arr64 IW) (g + 8) ≤ s then some ([1, 0, 0], m)
    else if rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s)) = 0 then
      pfR (smW n m g s mc (rdW (m.arr64 IW) g + s))
    else pfR (snW n m g s mc (rdW (m.arr64 IW) g + s)
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s) + 1))
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s) + 2)))
/-- **The model of `class_gen_prefix_binders_slot_motive`.** -/
def smW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, g, s, mc, d => pfK1 n (fun m1 => psW n m1 g (s + 1) (mc + 1)) (motW n m g mc d)
/-- **The model of `class_gen_prefix_binders_slot_minor`.** -/
def snW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, g, s, mc, d, cls, ctor => pfK4 n (fun m1 => psW n m1 g (s + 1) mc) g cls d (fcW n m g cls ctor)
end

def gpbK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([1, r3.headD 0, r3.tail.headD 0], m3)

def gpbK2 (n : Nat) (pbo pbl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0, 0], m2)
    else gpbK3 (appendW n m2 pbo pbl (r2.tail.headD 0) (r2.tail.tail.headD 0))

def gpbK1 (n : Nat) (g : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => gpbK2 n (r1.headD 0) (r1.tail.headD 0) (psW n m1 g 0 0)

/-- **The model of `class_gen_prefix_binders`.** -/
def gpbW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, g => gpbK1 n g (stubM "fvar_type_ds" m [rdW (m.arr64 IW) (g + 1), rdW (m.arr64 IW) (g + 2)])

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
theorem pfK3_some : pfK3 (some (r3, m3)) = some ([1, r3.headD 0, r3.tail.headD 0], m3) := rfl
theorem pfK2_fail (h : r2.headD 0 = 0) : pfK2 n ty (some (r2, m2)) = some ([0, 0, 0], m2) := by
  rw [pfK2, if_pos h]
theorem pfK2_ok (h : r2.headD 0 ≠ 0) : pfK2 n ty (some (r2, m2)) =
    pfK3 (consW n m2 ty (r2.tail.headD 0) (r2.tail.tail.headD 0)) := by rw [pfK2, if_neg h]
theorem pfK1_fail (h : r1.headD 0 = 0) : pfK1 n next (some (r1, m1)) = some ([0, 0, 0], m1) := by
  rw [pfK1, if_pos h]
theorem pfK1_ok (h : r1.headD 0 ≠ 0) : pfK1 n next (some (r1, m1)) = pfK2 n (r1.tail.headD 0) (next m1) := by
  rw [pfK1, if_neg h]
theorem pfK4_fail (h : r4.headD 0 = 0) : pfK4 n next g cls d (some (r4, m4)) = some ([0, 0, 0], m4) := by
  rw [pfK4, if_pos h]
theorem pfK4_ok (h : r4.headD 0 ≠ 0) : pfK4 n next g cls d (some (r4, m4)) =
    pfK1 n next (mnW n m4 g cls (r4.tail.headD 0) d) := by rw [pfK4, if_neg h]
theorem pfR_some : pfR (some (r, m)) = some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m) := rfl
theorem psW_end (h : rdW (m.arr64 IW) (g + 8) ≤ s) : psW (n + 1) m g s mc = some ([1, 0, 0], m) := by
  simp only [psW]; rw [if_pos h]
theorem psW_mot (h : ¬ rdW (m.arr64 IW) (g + 8) ≤ s)
    (h2 : rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s)) = 0) :
    psW (n + 1) m g s mc = pfR (smW n m g s mc (rdW (m.arr64 IW) g + s)) := by
  simp only [psW]; rw [if_neg h, if_pos h2]
theorem psW_min (h : ¬ rdW (m.arr64 IW) (g + 8) ≤ s)
    (h2 : ¬ rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s)) = 0) :
    psW (n + 1) m g s mc = pfR (snW n m g s mc (rdW (m.arr64 IW) g + s)
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s) + 1))
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 7) + s) + 2))) := by
  simp only [psW]; rw [if_neg h, if_neg h2]
theorem smW_eq : smW (n + 1) m g s mc d = pfK1 n (fun m1 => psW n m1 g (s + 1) (mc + 1)) (motW n m g mc d) := by
  simp only [smW]
theorem snW_eq (ctor : Word) : snW (n + 1) m g s mc d cls ctor =
    pfK4 n (fun m1 => psW n m1 g (s + 1) mc) g cls d (fcW n m g cls ctor) := by
  simp only [snW]
theorem gpbW_eq : gpbW (n + 1) m g =
    gpbK1 n g (stubM "fvar_type_ds" m [rdW (m.arr64 IW) (g + 1), rdW (m.arr64 IW) (g + 2)]) := rfl
theorem gpbK1_some : gpbK1 n g (some (r1, m1)) = gpbK2 n (r1.headD 0) (r1.tail.headD 0) (psW n m1 g 0 0) := rfl
theorem gpbK2_fail (h : r2.headD 0 = 0) : gpbK2 n pbo pbl (some (r2, m2)) = some ([0, 0, 0], m2) := by
  rw [gpbK2, if_pos h]
theorem gpbK2_ok (h : r2.headD 0 ≠ 0) : gpbK2 n pbo pbl (some (r2, m2)) =
    gpbK3 (appendW n m2 pbo pbl (r2.tail.headD 0) (r2.tail.tail.headD 0)) := by rw [gpbK2, if_neg h]
theorem gpbK3_some : gpbK3 (some (r3, m3)) = some ([1, r3.headD 0, r3.tail.headD 0], m3) := rfl
end arms

attribute [ind_grind] fcK_some fcgW_nil fcgW_hit fcgW_miss fcW_none fcW_go pfK3_some pfK2_fail pfK2_ok
  pfK1_fail pfK1_ok pfK4_fail pfK4_ok pfR_some psW_end psW_mot psW_min smW_eq snW_eq gpbW_eq gpbK1_some gpbK2_fail gpbK2_ok gpbK3_some

/-! ## Specs -/

/-- The lookups `class_gen_prefix_binders` needs. -/
structure PbProg (p : Prog) extends MnProg p : Prop where
  fcg : p.lookup "class_gen_prefix_binders_find_ctor_go" = some classGenPrefixBindersFindCtorGo
  fc : p.lookup "class_gen_prefix_binders_find_ctor" = some classGenPrefixBindersFindCtor
  psg : p.lookup "class_gen_prefix_binders_slots_go" = some classGenPrefixBindersSlotsGo
  psm : p.lookup "class_gen_prefix_binders_slot_motive" = some classGenPrefixBindersSlotMotive
  psn : p.lookup "class_gen_prefix_binders_slot_minor" = some classGenPrefixBindersSlotMinor
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

/-- The specs of the slot walk at exec fuel `n`. -/
def SlotsSpec (n : Nat) : Prop :=
  (∀ (s₀ : St) (g s mc : Word), ⦃fun st => st = s₀⦄ invoke p (exec p n) "class_gen_prefix_binders_slots_go" [g, s, mc]
    ⦃fun r s' => LocEq s' s₀ ∧ psW n s₀.mem g s mc = some (r, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (g s mc d : Word), ⦃fun st => st = s₀⦄
    invoke p (exec p n) "class_gen_prefix_binders_slot_motive" [g, s, mc, d]
    ⦃fun r s' => LocEq s' s₀ ∧ smW n s₀.mem g s mc d = some (r, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (g s mc d cls ctor : Word), ⦃fun st => st = s₀⦄
    invoke p (exec p n) "class_gen_prefix_binders_slot_minor" [g, s, mc, d, cls, ctor]
    ⦃fun r s' => LocEq s' s₀ ∧ snW n s₀.mem g s mc d cls ctor = some (r, s'.mem); ⊤⦄)

theorem slots_spec (n : Nat) : SlotsSpec p n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> intros
    · rw [invoke_eq _ h.psg]; simp only [callFn, classGenPrefixBindersSlotsGo]; vcgen [exec] <;> grind
    · rw [invoke_eq _ h.psm]; simp only [callFn, classGenPrefixBindersSlotMotive]; vcgen [exec] <;> grind
    · rw [invoke_eq _ h.psn]; simp only [callFn, classGenPrefixBindersSlotMinor]; vcgen [exec] <;> grind
  | succ n ih =>
    obtain ⟨ihg, ihm, ihn⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro s₀ g s mc
      rw [invoke_eq _ h.psg]
      simp only [callFn, classGenPrefixBindersSlotsGo]
      sym only [lang_grind, arena_grind, ind_grind] =>
        vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ihm, ihn] <;>
        finish (gen := 20) [rdW_eq, loc_init4, loc_init5]
    · intro s₀ g s mc d
      rw [invoke_eq _ h.psm]
      simp only [callFn, classGenPrefixBindersSlotMotive]
      sym only [lang_grind, arena_grind, ind_grind] =>
        vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
          classGenMotiveTy_spec p h.toMtProg n, slCons_specW p h.alloc h.copy h.cons n, ihg] <;>
        finish (gen := 20)
    · intro s₀ g s mc d cls ctor
      rw [invoke_eq _ h.psn]
      simp only [callFn, classGenPrefixBindersSlotMinor]
      sym only [lang_grind, arena_grind, ind_grind] =>
        vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
          findCtor_spec p h n, classGenMinorTy_spec p h.toMnProg n, slCons_specW p h.alloc h.copy h.cons n, ihg] <;>
        finish (gen := 20) [loc_init4, loc_init5]

theorem prefixBinders_spec (n : Nat) (s₀ : St) (g : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_prefix_binders" [g]
    ⦃fun r s' => LocEq s' s₀ ∧ gpbW n s₀.mem g = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.pb]
  simp only [callFn, classGenPrefixBinders]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "fvar_type_ds" n, (slots_spec p h n).1, slAppend_specW p h.alloc h.copy h.app n] <;>
      finish (gen := 20) [rdW_eq]

end specs

end L.Ind
