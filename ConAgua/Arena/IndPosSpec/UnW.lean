import ConAgua.Arena.IndPosSpec.NestHoles
import ConAgua.Arena.IndGrindAttr

/-!
# UnW

`invoke_exec0`, `ucW`, `ucK`, `ucW_nil`, `ucW_cons`, `ucK_no` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order
namespace L.Ind
open L.Arena

/-- A call at exec fuel `0` never returns. -/
theorem invoke_exec0 (p : Prog) (f : FnName) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p 0) f vs ⦃fun _ _ => False; ⊤⦄ := by
  simp only [invoke, callFn, lookupFn]
  vcgen [exec] <;> grind

mutual
def ucW (cR : CallM) : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | k + 1, m, ctx, o, l =>
    if l = 0 then some ([1], m) else ucK cR k ctx o l (nuWf cR k m ctx (rdW (m.arr64 IW) (rdW (m.arr64 IW) o)))
def ucK (cR : CallM) (k : Nat) (ctx o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => if r.headD 0 = 0 then some ([0], m1) else ucW cR k m1 ctx (o + 1) (l - 1)
end

section arms
variable (cR : CallM) (k : Nat) (m m1 : Mem) (ctx o l : Word) (r : List Word)
theorem ucW_nil (h : l = 0) : ucW cR (k + 1) m ctx o l = some ([1], m) := by simp [ucW, h]
theorem ucW_cons (h : ¬ l = 0) : ucW cR (k + 1) m ctx o l =
    ucK cR k ctx o l (nuWf cR k m ctx (rdW (m.arr64 IW) (rdW (m.arr64 IW) o))) := by simp [ucW, h]
theorem ucK_no (h : r.headD 0 = 0) : ucK cR k ctx o l (some (r, m1)) = some ([0], m1) := by rw [ucK, ite_eq_left h]
theorem ucK_yes (h : ¬ r.headD 0 = 0) : ucK cR k ctx o l (some (r, m1)) = ucW cR k m1 ctx (o + 1) (l - 1) := by
  rw [ucK, ite_eq_right h]
end arms
attribute [ind_grind] ucW_nil ucW_cons ucK_no ucK_yes

mutual
def unW (cR : CallM) : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | k + 1, m, ctx, off, l =>
    if l = 0 then some m
    else unK cR k ctx off l (ucW cR k m ctx (rdW (m.arr64 IW) (rdW (m.arr64 IW) off))
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 1)))
def unK (cR : CallM) (k : Nat) (ctx off l : Word) : Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m1) => if r.headD 0 = 0 then none else unW cR k m1 ctx (off + 1) (l - 1)
end

section arms
variable (cR : CallM) (k : Nat) (m m1 : Mem) (ctx off l : Word) (r : List Word)
theorem unW_nil (h : l = 0) : unW cR (k + 1) m ctx off l = some m := by simp [unW, h]
theorem unW_cons (h : ¬ l = 0) : unW cR (k + 1) m ctx off l =
    unK cR k ctx off l (ucW cR k m ctx (rdW (m.arr64 IW) (rdW (m.arr64 IW) off))
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 1))) := by simp [unW, h]
theorem unK_yes (h : ¬ r.headD 0 = 0) : unK cR k ctx off l (some (r, m1)) = unW cR k m1 ctx (off + 1) (l - 1) := by
  rw [unK, ite_eq_right h]
end arms
attribute [ind_grind] unW_nil unW_cons unK_yes

end L.Ind

end
