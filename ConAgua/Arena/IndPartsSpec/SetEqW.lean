import ConAgua.Arena.IndPartsSpec.EqW
import ConAgua.Arena.IndPartsSpec.IndPartsProg2

/-!
# SetEqW

`slAllIn_spec`, `allInW`, `allInW_ok`, `setEqW`, `setEqW_ok`, `partsPSl_nil` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `sl_all_in`, `sl_set_eq` -/

/-- **`sl_all_in` is its model `allInW`** (generated). -/
l_model slAllIn_spec (p : Prog) (hc : p.lookup "sl_contains" = some slContains)
    (hp : p.lookup "sl_all_in" = some slAllIn)
  fns [hp ↦ allInW ro]
  specs [slContains_spec p hc n]
  grind [arena_grind]

theorem allInW_ok (n : Nat) : ∀ (m : Mem) (o1 l1 o2 l2 r : Word) (ws1 ws2 : List Word),
    SlR m o1 l1 ws1 → SlR m o2 l2 ws2 → allInW n m o1 l1 o2 l2 = some r →
    r = if ws1.all (fun w => ws2.contains w) then 1 else 0 := by
  induction n with
  | zero => intro m o1 l1 o2 l2 r ws1 ws2 _ _ h; simp [allInW] at h
  | succ n ih =>
    intro m o1 l1 o2 l2 r ws1 ws2 h1 h2 h
    cases h1 with
    | nil => rw [allInW.arm1 n m _ 0 o2 l2 rfl] at h; simp at h; simp [h]
    | @cons _ _ ws hl hs =>
      rw [allInW.arm2 n m _ _ o2 l2 hl] at h
      obtain ⟨b, hb, h⟩ := ipK_inv1 h (by simp [allInW.k_sl_contains])
      have := containsW_ok n m o2 l2 _ b ws2 h2 hb
      by_cases b0 : b = 0
      · rw [allInW.k_sl_contains.arm1 _ _ _ _ _ _ _ b0] at h; simp at h; subst h
        subst b0
        split at this <;> simp_all
      · rw [allInW.k_sl_contains.arm2 _ _ _ _ _ _ _ b0] at h
        rw [ih _ _ _ _ _ _ _ _ hs h2 h]
        split at this <;> simp_all

/-- The model of `sl_set_eq`. -/
def setEqW (n : Nat) (m : Mem) (o1 l1 o2 l2 : Word) : Option Word :=
  if l1 ≠ l2 then some 0
  else match allInW n m o1 l1 o2 l2 with
    | none => none
    | some b => if b = 0 then some 0 else allInW n m o2 l2 o1 l1

theorem setEqW_ok {n : Nat} {m : Mem} {o1 l1 o2 l2 r : Word} {ws1 ws2 : List Word}
    (h1 : SlR m o1 l1 ws1) (h2 : SlR m o2 l2 ws2) (h : setEqW n m o1 l1 o2 l2 = some r) :
    r = if (ws1.length == ws2.length && ws2.all (fun w => ws1.contains w) &&
      ws1.all (fun w => ws2.contains w)) then 1 else 0 := by
  have e1 := slR_length h1; have e2 := slR_length h2
  unfold setEqW at h
  by_cases hl : l1 ≠ l2
  · rw [ite_eq_left hl] at h; simp at h; subst h
    have : ws1.length ≠ ws2.length := fun e => hl (UInt64.toNat_inj.mp (by omega))
    simp [this]
  · rw [ite_eq_right hl] at h
    have hl' : l1 = l2 := by simpa using hl
    have hlen : ws1.length = ws2.length := by rw [e1, e2, hl']
    rcases ha : allInW n m o1 l1 o2 l2 with _ | b <;> rw [ha] at h
    · simp at h
    simp only at h
    have hb := allInW_ok n m o1 l1 o2 l2 b ws1 ws2 h1 h2 ha
    by_cases b0 : b = 0
    · rw [ite_eq_left b0] at h; simp at h; subst h
      subst b0
      split at hb <;> simp_all
    · rw [ite_eq_right b0] at h
      have hb2 := allInW_ok n m o2 l2 o1 l1 r ws2 ws1 h2 h1 h
      split at hb <;> simp_all

theorem partsPSl_nil {α : Type} {f : Mem → Nat → Option α} {xs : List α} {o : Word} {m : Mem}
    (h : PSlR f xs o 0 m) : xs = [] := by
  have := decPL_length _ h.1; simpa using this

/-! ## `block_rec_name_set_ok` -/

theorem partsContains_decI (ws : List Word) (x : Word) (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) : (ws.map (decI : Word → NIdx)).contains (decI x) = ws.contains x := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.contains_cons]
    rw [ih (fun w' h' => hws w' (List.mem_cons_of_mem _ h')),
      L.Arena.decI_beq x w hx (hws w (List.mem_cons_self ..))]
    by_cases h : x = w <;> simp [h]

/-- The program bundle of the name set. -/
structure IndPartsProg3 (p : Prog) : Prop extends IndPartsProg2 p where
  want : p.lookup "block_rec_want" = some blockRecWant
  got : p.lookup "block_rec_got" = some blockRecGot
  contains : p.lookup "sl_contains" = some slContains
  allIn : p.lookup "sl_all_in" = some slAllIn
  setEq : p.lookup "sl_set_eq" = some slSetEq
  nameSet : p.lookup "block_rec_name_set_ok" = some blockRecNameSetOk

end L.Ind

end
