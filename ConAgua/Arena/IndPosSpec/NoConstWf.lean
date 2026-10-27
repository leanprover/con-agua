import ConAgua.Arena.IndPosSpec.NestOccGo
import ConAgua.Arena.IndPosSpec.PiBWStage

/-!
# NoConstWf

`noConstWf`, `nestOcc_spec'`, `noConstWf_ok`, `pdoW`, `pdoK1`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `pi_doms_occ` refines `piDomsOcc` -/

/-- `nest_occ` at any exec fuel. -/
def noConstWf : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, lo, hi, e => noConstW n m no nl lo hi e

theorem nestOcc_spec' (p : Prog) (hl : NoLook p) (n : Nat) (s₀ : St) (no nl lo hi e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_occ" [no, nl, lo, hi, e]
    ⦃fun r s' => LocEq s' s₀ ∧ noConstWf n s₀.mem no nl lo hi e = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases n with
  | zero => rw [invoke_eq _ hl.hp]; simp only [callFn, nestOcc]; vcgen [exec] <;> grind
  | succ n => exact nestOcc_spec p hl.hv hl.hc hl.hf hl.hput hl.hgo hl.hnode hl.hcl hl.hp n s₀ no nl lo hi e

/-- `nest_occ` from the stage relation, its names a decoded slice below the top. -/
theorem noConstWf_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl lo hi e r : Word) (names : List NIdx) (mp0 : Std.HashMap EIdx Bool)
    (hb : noConstWf n m no nl lo hi e = some (r, m')) (hS : StageR dn vis fe m a) (hh : H e)
    (hn : decHL m no.toNat nl.toNat = some names) (hnb : no.toNat + nl.toNat < 2 ^ 64)
    (hM : noMR m mp0) :
    ∃ b, (ConRon.Arena.nestOcc names lo.toNat hi.toNat (decE e)).run a = .ok (b, a) ∧ (r != 0) = b ∧
      noMR m' ∅ ∧ StageR dn vis fe m' a ∧ IWGrow m m' ∧ MFr [NOM] [204, 205] m m' := by
  cases n with
  | zero => simp [noConstWf] at hb
  | succ n =>
    obtain ⟨ws, hws, rfl, hwlt⟩ := slR_of_decHL m nl.toNat no.toNat names hn hnb
    simp only [UInt64.ofNat_toNat] at hws
    exact noConstW_ok n dn fe vis m m' a no nl lo hi e r ws mp0 hb hS hh hws hwlt hM

mutual
def pdoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, no, nl, lo, hi, n, e =>
    if n = 0 then some ([0], m)
    else if e >>> 28 ≠ 6 then some ([0], m)
    else if eViewW m e = [] then none
    else pdoK1 k no nl lo hi n (eViewW m e) (noConstWf k m no nl lo hi ((eViewW m e).tail.headD 0))
def pdoK1 (k : Nat) (no nl lo hi n : Word) (v : List Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r ≠ 0 then some ([1], m1) else pdoW k m1 no nl lo hi (n - 1) (v.tail.tail.headD 0)
end

end L.Ind

end
