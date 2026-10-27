import ConAgua.Arena.IndPosSpec.NcGoW

/-!
# NestContainer: `ConRon.Arena.nestContainer`

The refinement theorems `nestContainer_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem CNOk.dec {m : Mem} {p : Nat} {x : IConstantVal × Nat} {P : Nat → Prop} (h : CNOk m p x P) :
    decCN m p = some x := by
  obtain ⟨-, -, q, hq, hcv, hn⟩ := h
  have : decCVp m q = some x.1 := (erecP_ext m).decCV hcv
  simp [decCN, hq, this, hn]

theorem CsAt.decPL {m : Mem} {o : Nat} {xs : List (IConstantVal × Nat)} {P : Nat → Prop}
    (h : CsAt m o xs P) : decPL m (decCN m) o xs.length = some xs :=
  decPL_of_get _ xs o fun j hj => by
    obtain ⟨w, hw, hc⟩ := h j hj
    exact ⟨w.toNat, by simp [iwN, nat?, iwA, hw], hc.dec⟩

/-- `NcOut` survives the pool's growth. -/
theorem NcOut.grow {m m' : Mem} {r : List Word} {x : Option (Nat × List (IConstantVal × Nat))}
    (h : NcOut m r x) (hg : IWGrow m m') : NcOut m' r x := by
  cases x with
  | none => exact h
  | some p =>
    obtain ⟨n, cs⟩ := p
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨h1, h2, h3, Nat.le_trans h4 hg.1, h5.grow h4 hg⟩

section census
variable (p : Prog) (hl : NtLook p)
include hl

/-- **`nest_container` refines `nestContainer`** (through the `strip_pis`/`get_app_fn` stubs of
`nest_ctor_entry`; L aborts where a constructor's parameter and field counts' sum wraps). -/
@[refines ConRon.Arena.nestContainer]
theorem nestContainer_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis C : Word) (hC : H C) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_container" [vis, C]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestContainer fe (decI C)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestContainer fe (decI C)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ NcOut s'.mem r (AM.res (ConRon.Arena.nestContainer fe (decI C)) a₀); ⊤⦄ := by
  refine triple_post (nt_spec p hl k s₀ vis C) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := ntW_ok dn fe vis C hC k _ _ a₀ r hm hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census

end L.Ind

end
