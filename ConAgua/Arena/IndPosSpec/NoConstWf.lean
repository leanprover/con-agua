module

public import ConAgua.Arena.IndPosSpec.NestOccGo
public import ConAgua.Arena.IndPosSpec.PiBWStage
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndPosSpec.NoGoStep
import all ConAgua.Arena.IndPos
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndPos2

@[expose] public section

/-!
# NoConstWf

`noConstWf`, `nestOcc_spec'`, `noConstWf_ok`, `piDomsOcc_spec` (`pdoW`).
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
    (hb : noConstWf n m no nl lo hi e = some (r, m')) (hS : StageR vis fe m a) (hh : H e)
    (hn : decHL m no.toNat nl.toNat = some names) (hnb : no.toNat + nl.toNat < 2 ^ 64)
    (hM : noMR m mp0) :
    ∃ b, (ConRon.Arena.nestOcc names lo.toNat hi.toNat (decE e)).run a = .ok (b, a) ∧ (r != 0) = b ∧
      noMR m' ∅ ∧ StageR vis fe m' a ∧ IWGrow m m' ∧ MFr [NOM] [204, 205] m m' := by
  cases n with
  | zero => simp [noConstWf] at hb
  | succ n =>
    obtain ⟨ws, hws, rfl, hwlt⟩ := slR_of_decHL m nl.toNat no.toNat names hn hnb
    simp only [UInt64.ofNat_toNat] at hws
    exact noConstW_ok n dn fe vis m m' a no nl lo hi e r ws mp0 hb hS hh hws hwlt hM

/-- **`pi_doms_occ` is its model `pdoW`** (generated). -/
l_model piDomsOcc_spec (p : Prog) (hl : NoLook p) (hp : p.lookup "pi_doms_occ" = some piDomsOccL)
  fns [hp ↦ pdoW list]
  specs [eView_spec p hl.hv n, nestOcc_spec' p hl n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

end L.Ind

end
