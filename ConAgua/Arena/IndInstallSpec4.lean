import ConAgua.Arena.IndInstallSpec3

/-!
# Refinements of `IndInstall`, part 4 (lane `indproofs`, helper `install`)

`check_block_positivity_split`: the model of the per-member loop (recursive helper
`check_block_positivity_split_go`) and its `vcgen` spec through the models of
`check_block_positivity_member` and `rec2`.
-/


noncomputable section

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem pmStep_size (m : Mem) (kd nd s : Word) :
    ((pmStep m kd nd s).arr64 IW).size = (m.arr64 IW).size := by
  unfold pmStep
  simp only [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
    rec2Mem_size]

theorem pmGoW_size : ∀ (n : Nat) (m m' : Mem) (kd nd s l : Word), pmGoW n m kd nd s l = some m' →
    (m'.arr64 IW).size = (m.arr64 IW).size
  | 0, m, m', kd, nd, s, l, h => by simp [pmGoW] at h
  | n + 1, m, m', kd, nd, s, l, h => by
    by_cases hl : l = 0
    · rw [pmGoW_nil n m kd nd s l hl] at h; cases h; rfl
    · by_cases hr : (rdW (m.arr64 CTL) 200).toNat + 2 ≤ (m.arr64 IW).size
      · rw [pmGoW_step n m kd nd s l hl hr] at h
        rw [pmGoW_size n _ _ _ _ _ _ h]
        exact pmStep_size _ _ _ _
      · rw [pmGoW_full n m kd nd s l hl hr] at h; simp at h

theorem posMemberW_size {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : posMemberW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (m'.arr64 IW).size = (m.arr64 IW).size := by
  simp only [posMemberW] at h
  cases hal1 : allocW m l with
  | none => simp [hal1] at h
  | some qm =>
  obtain ⟨kq, m1⟩ := qm
  simp only [hal1] at h
  cases hal2 : allocW m1 l with
  | none => simp [hal2] at h
  | some qm2 =>
  obtain ⟨nq, m2⟩ := qm2
  simp only [hal2] at h
  cases hgo : pmGoW (n - 1) m2 kq nq o l with
  | none => simp [hgo] at h
  | some m3 =>
  simp only [hgo, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rw [pmGoW_size _ _ _ _ _ _ _ hgo]
  obtain ⟨-, rfl, -⟩ := allocW_facts hal2 (allocW_size hal1 hsz)
  obtain ⟨-, rfl, -⟩ := allocW_facts hal1 hsz
  rw [allocMem_IW, allocMem_IW]

/-! ## `check_block_positivity_split_go` -/

mutual
/-- **The model of `check_block_positivity_split_go`** (each `rec2` needs room). -/
def pgW : Nat → Mem → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _ => none
  | n + 1, m, kd, nd, s, l =>
    if l = 0 then some m
    else pgK1 n kd nd s l
      (posMemberW n m (rdW (m.arr64 IW) (rdW (m.arr64 IW) s))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) s + 1)))
termination_by n _ _ _ _ _ => 3 * n

/-- After the member call: room for the first `rec2`. -/
def pgK1 (n : Nat) (kd nd s l : Word) : Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m1) =>
    if (rdW (m1.arr64 CTL) 200).toNat + 2 ≤ (m1.arr64 IW).size then
      pgK2 n kd nd s l r m1 (rec2Mem m1 (r.headD 0) (r.tail.headD 0))
    else none
termination_by 3 * n + 2

/-- After the first `rec2`: room for the second, the two stores, the recursive call. -/
def pgK2 (n : Nat) (kd nd s l : Word) (r : List Word) (m1 m2 : Mem) : Option Mem :=
  if (rdW (m2.arr64 CTL) 200).toNat + 2 ≤ (m2.arr64 IW).size then
    pgW n (((rec2Mem m2 (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0)).set64 IW kd
        (rdW (m1.arr64 CTL) 200)).set64 IW nd (rdW (m2.arr64 CTL) 200))
      (kd + 1) (nd + 1) (s + 1) (l - 1)
  else none
termination_by 3 * n + 1
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (kd nd s l : Word) (r : List Word)
theorem pgW_nil (hl : l = 0) : pgW (n + 1) m kd nd s l = some m := by simp [pgW, hl]
theorem pgW_cons (hl : l ≠ 0) : pgW (n + 1) m kd nd s l =
    pgK1 n kd nd s l (posMemberW n m (rdW (m.arr64 IW) (rdW (m.arr64 IW) s))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) s + 1))) := by simp [pgW, hl]
theorem pgK1_full (h : ¬ (rdW (m1.arr64 CTL) 200).toNat + 2 ≤ (m1.arr64 IW).size) :
    pgK1 n kd nd s l (some (r, m1)) = none := by rw [pgK1, if_neg h]
theorem pgK1_ok (h : (rdW (m1.arr64 CTL) 200).toNat + 2 ≤ (m1.arr64 IW).size) :
    pgK1 n kd nd s l (some (r, m1)) =
      pgK2 n kd nd s l r m1 (rec2Mem m1 (r.headD 0) (r.tail.headD 0)) := by rw [pgK1, if_pos h]
theorem pgK2_full (h : ¬ (rdW (m2.arr64 CTL) 200).toNat + 2 ≤ (m2.arr64 IW).size) :
    pgK2 n kd nd s l r m1 m2 = none := by rw [pgK2, if_neg h]
theorem pgK2_ok (h : (rdW (m2.arr64 CTL) 200).toNat + 2 ≤ (m2.arr64 IW).size) :
    pgK2 n kd nd s l r m1 m2 =
      pgW n (((rec2Mem m2 (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0)).set64 IW kd
        (rdW (m1.arr64 CTL) 200)).set64 IW nd (rdW (m2.arr64 CTL) 200))
      (kd + 1) (nd + 1) (s + 1) (l - 1) := by rw [pgK2, if_pos h]
end arms

grind_pattern [ind_grind] pgW_nil => pgW (n + 1) m kd nd s l
grind_pattern [ind_grind] pgW_cons => pgW (n + 1) m kd nd s l
grind_pattern [ind_grind] pgK1_full => pgK1 n kd nd s l (some (r, m1))
grind_pattern [ind_grind] pgK1_ok => pgK1 n kd nd s l (some (r, m1))
grind_pattern [ind_grind] pgK2_full => pgK2 n kd nd s l r m1 m2
grind_pattern [ind_grind] pgK2_ok => pgK2 n kd nd s l r m1 m2

theorem checkBlockPositivitySplitGo_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (h2 : p.lookup "rec2" = some rec2)
    (hg : p.lookup "check_block_positivity_member_go" = some checkBlockPositivityMemberGo)
    (hm : p.lookup "check_block_positivity_member" = some checkBlockPositivityMember)
    (hp : p.lookup "check_block_positivity_split_go" = some checkBlockPositivitySplitGo)
    (n : Nat) :
    ∀ (s₀ : St) (kd nd s l : Word), (s₀.mem.arr64 IW).size < 2 ^ 64 →
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_positivity_split_go" [kd, nd, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ pgW n s₀.mem kd nd s l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ kd nd s l hsz; rw [invoke_eq _ hp]
    simp only [callFn, checkBlockPositivitySplitGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ kd nd s l hsz
    rw [invoke_eq _ hp]
    simp only [callFn, checkBlockPositivitySplitGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        checkBlockPositivityMember_spec p ha h2 hg hm n, rec2_spec p ha h2 n, ih] <;>
      finish (gen := 20) [posMemberW_size, rec2Mem_size]

/-! ## `check_block_positivity_split` -/

/-- The model of `check_block_positivity_split(outsO, outsL)` at the caller's fuel `n`. -/
def posSplitW (n : Nat) (m : Mem) (outsO outsL : Word) : Option (List Word × Mem) :=
  match allocW m outsL with
  | none => none
  | some (kq, m1) =>
    match allocW m1 outsL with
    | none => none
    | some (nq, m2) =>
      match pgW (n - 1) m2 kq nq outsO outsL with
      | none => none
      | some m3 => some ([kq, outsL, nq, outsL], m3)

theorem checkBlockPositivitySplit_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (h2 : p.lookup "rec2" = some rec2)
    (hg : p.lookup "check_block_positivity_member_go" = some checkBlockPositivityMemberGo)
    (hm : p.lookup "check_block_positivity_member" = some checkBlockPositivityMember)
    (hs : p.lookup "check_block_positivity_split_go" = some checkBlockPositivitySplitGo)
    (hp : p.lookup "check_block_positivity_split" = some checkBlockPositivitySplit) (n : Nat)
    (s₀ : St) (outsO outsL : Word) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_positivity_split" [outsO, outsL]
    ⦃fun r s' => LocEq s' s₀ ∧ posSplitW n s₀.mem outsO outsL = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockPositivitySplit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hmod : ∀ kq nq m1 m2 m3, allocW s₀.mem outsL = some (kq, m1) → allocW m1 outsL = some (nq, m2) →
        pgW n m2 kq nq outsO outsL = some m3 →
        posSplitW (n + 1) s₀.mem outsO outsL = some ([kq, outsL, nq, outsL], m3) := by
      intro kq nq m1 m2 m3 h1 h2 h3
      simp [posSplitW, h1, h2, h3]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n,
        checkBlockPositivitySplitGo_spec p ha h2 hg hm hs n] <;>
      finish (gen := 20) [allocW_size]

end L.Ind
