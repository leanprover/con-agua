import ConAgua.Arena.IndInstallSpec9

/-!
# Refinements of `IndInstall`, part 10 (lane `indproofs2`, helper `install`): `checkBlockAgree`

Recursion on the other members, member 0's telescope opened per member as the twin does
(`open_pis_at_fvars_f`'s stub), then helper `install`'s `check_block_agree_one` (the twin's
`agreeBodyAM`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem installIteBind {α β : Type} (c : Prop) [Decidable c] (x y : AM α) (f : α → AM β) :
    ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  split <;> rfl

/-- The twin's `checkBlockAgree` at a member: member 0's telescope, the member's body, the rest. -/
theorem installAgree_cons (fe : IFEnv) (nP : Nat) (cvTa₀ cvTa : IConstantVal) (s₀ s : LIdx)
    (rest : List (IConstantVal × LIdx)) :
    ConRon.Arena.checkBlockAgree V fe nP cvTa₀ s₀ ((cvTa, s) :: rest) =
      (openPisAtFvarsF nP cvTa₀.type 0 >>= fun x =>
        unwrapOr x (.internal "block: type former telescope") >>= fun tq₀ =>
        agreeBodyAM fe nP tq₀.1 cvTa s s₀ >>= fun _ =>
        ConRon.Arena.checkBlockAgree V fe nP cvTa₀ s₀ rest) := by
  simp only [ConRon.Arena.checkBlockAgree, agreeBodyAM, bind_assoc, installIteBind, pure_bind]

/-- After the rest. -/
def iagK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([0], m)

mutual
/-- **The model of `check_block_agree(vis, nP, c0, s0, o, l)`** at exec fuel `n`. -/
def iagW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, nP, c0, s0, o, l =>
    if l = 0 then some ([0], m)
    else iagK1 p n vis nP c0 s0 o l (callW p n "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (c0 + 3), 0] m)
/-- After member 0's telescope. -/
def iagK1 (p : Prog) (n : Nat) (vis nP c0 s0 o l : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else iagK2 p n vis nP c0 s0 o l (callW p n "check_block_agree_one" [vis, nP, r.tail.headD 0,
      r.tail.tail.headD 0, s0, rdW (m.arr64 IW) (rdW (m.arr64 IW) o),
      rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 1)] m)
/-- After the member's agreements: the rest. -/
def iagK2 (p : Prog) (n : Nat) (vis nP c0 s0 o l : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => iagK3 (iagW p n m vis nP c0 s0 (o + 1) (l - 1))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis nP c0 s0 o l : Word) (r : List Word)
theorem iagW_zero : iagW p 0 m vis nP c0 s0 o l = none := by simp [iagW]
theorem iagW_nil (h : l = 0) : iagW p (n + 1) m vis nP c0 s0 o l = some ([0], m) := by simp [iagW, h]
theorem iagW_cons (h : l ≠ 0) : iagW p (n + 1) m vis nP c0 s0 o l =
    iagK1 p n vis nP c0 s0 o l (callW p n "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (c0 + 3), 0] m) := by
  simp [iagW, h]
theorem iagK1_none (h : r.headD 0 = 0) : iagK1 p n vis nP c0 s0 o l (some (r, m)) = none := by
  simp only [iagK1, h, ↓reduceIte]
theorem iagK1_some (h : ¬ r.headD 0 = 0) : iagK1 p n vis nP c0 s0 o l (some (r, m)) =
    iagK2 p n vis nP c0 s0 o l (callW p n "check_block_agree_one" [vis, nP, r.tail.headD 0,
      r.tail.tail.headD 0, s0, rdW (m.arr64 IW) (rdW (m.arr64 IW) o),
      rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 1)] m) := by simp only [iagK1, h, ↓reduceIte, if_false]
theorem iagK2_some : iagK2 p n vis nP c0 s0 o l (some (r, m)) =
    iagK3 (iagW p n m vis nP c0 s0 (o + 1) (l - 1)) := by simp [iagK2]
theorem iagK3_some : iagK3 (some (r, m)) = some ([0], m) := rfl
end arms
attribute [ind_grind] iagW_nil iagW_cons iagK1_none iagK1_some iagK2_some iagK3_some

theorem iag_spec (p : Prog) (hp : p.lookup "check_block_agree" = some checkBlockAgree) (n : Nat) :
    ∀ (s₀ : St) (vis nP c0 s0 o l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_agree" [vis, nP, c0, s0, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ iagW p n s₀.mem vis nP c0 s0 o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis nP c0 s0 o l; rw [invoke_eq _ hp]; simp only [callFn, checkBlockAgree]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis nP c0 s0 o l
    rw [invoke_eq _ hp]
    simp only [callFn, checkBlockAgree]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "open_pis_at_fvars_f", callW_spec p n "check_block_agree_one", ih] <;>
      finish (gen := 20) [rdW_eq]

/-- The lookups of `check_block_agree`. -/
structure AgreeProg (p : Prog) : Prop where
  doms : p.lookup "check_block_doms_at" = some checkBlockDomsAt
  lvl : p.lookup "lvl_eq_fueled" = some lvlEqFueled
  one : p.lookup "check_block_agree_one" = some checkBlockAgreeOne
  agree : p.lookup "check_block_agree" = some checkBlockAgree
  ad : AdF p

end L.Ind
