import ConAgua.Arena.RecCheckSpec.TaCW

/-!
# TargetAbsGo: `ConRon.Arena.targetAbsGo`, `ConRon.Arena.targetAbs`

The refinement theorems `targetAbsGo_refines`, `targetAbs_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section census
variable (p : Prog) (L : TaLook p)
include L

/-- **`target_abs_go` (with `target_abs_const`, `target_abs_node`) refines `targetAbsGo`**, from a memo
related to the twin's. -/
@[refines ConRon.Arena.targetAbsGo]
theorem targetAbsGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl lvls ho hl f h : Word) (names : List NIdx) (holes : List EIdx)
    (mp : Std.HashMap EIdx EIdx) (hh : H h) (hlv : H lvls) (hS : StageR dn vis fe s₀.mem a₀)
    (hdec : decHL s₀.mem no.toNat nl.toNat = some names) (hit : no.toNat + nl.toNat ≤ iwTop s₀.mem)
    (hho : decHL s₀.mem ho.toNat hl.toNat = some holes) (hht : ho.toNat + hl.toNat ≤ iwTop s₀.mem)
    (hM : taMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_abs_go" [no, nl, lvls, ho, hl, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetAbsGo names (decI lvls) holes mp f.toNat (decE h)) a₀ ∧
      decE (r.headD 0) = (AM.res (ConRon.Arena.targetAbsGo names (decI lvls) holes mp f.toNat (decE h)) a₀).1 ∧
      taMR s'.mem (AM.res (ConRon.Arena.targetAbsGo names (decI lvls) holes mp f.toNat (decE h)) a₀).2 ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetAbsGo names (decI lvls) holes mp f.toNat (decE h)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post ((taGo_spec p L n).1 s₀ no nl lvls ho hl f h) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨⟨t, mp'⟩, a', hrun, rfl, hS', hg, hM'⟩ := taGoOK dn fe vis n _ a₀ no nl lvls ho hl f h names holes mp hS
    hh hlv ⟨hdec, hit, hho, hht⟩ hM _ _ hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hres], by rw [hres]; exact hM', by rw [hst]; exact hS', hg⟩

/-- **`target_abs` refines `targetAbs`**: clear the `ta` memo (any well-formed one on entry), one
memoised walk. -/
@[refines ConRon.Arena.targetAbs]
theorem targetAbs_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl lvls ho hl e : Word) (names : List NIdx) (holes : List EIdx)
    (mp0 : Std.HashMap EIdx EIdx) (he : H e) (hlv : H lvls) (hS : StageR dn vis fe s₀.mem a₀)
    (hdec : decHL s₀.mem no.toNat nl.toNat = some names) (hit : no.toNat + nl.toNat ≤ iwTop s₀.mem)
    (hho : decHL s₀.mem ho.toNat hl.toNat = some holes) (hht : ho.toNat + hl.toNat ≤ iwTop s₀.mem)
    (hM : taMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_abs" [no, nl, lvls, ho, hl, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetAbs names (decI lvls) holes (decE e)) a₀ ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.targetAbs names (decI lvls) holes (decE e)) a₀ ∧
      (∃ mp1, taMR s'.mem mp1) ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetAbs names (decI lvls) holes (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (targetAbs_spec p L n s₀ no nl lvls ho hl e) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨a', mp1, hrun, hM', hS', hg⟩ := taAW_ok n dn fe vis _ _ a₀ no nl lvls ho hl e _ names holes mp0 hm hS he hlv
    hdec hit hho hht hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hres], ⟨mp1, hM'⟩, by rw [hst]; exact hS', hg⟩

end census

end L.Ind

end
