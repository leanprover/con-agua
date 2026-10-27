import ConAgua.Arena.IndPosSpec.FgW2
import ConAgua.Arena.IndPosSpec.NestOccAny
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# NestContParamsClosed

`new1W_rec`, `cpW_nil`, `cpW_cons`, `cpK1_b`, `cpK1_ok`, `cpK2_out` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem new1W_rec {m m' : Mem} {x : Word} {r : List Word} (h : new1W m x = some (r, m')) :
    posRecW m [x] = some (r.headD 0, m') ∧ r = [r.headD 0, 1] := by
  rw [posRecW_eq m [x] 1 rfl]
  simp only [new1W] at h
  rcases ha : allocW m 1 with _ | ⟨q, m1⟩ <;> rw [ha] at h; · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  simp [wrIW]

end L.Ind

namespace L.Ind

open L.Arena

section arms
variable (n : Nat) (m m1 : Mem) (hp dO dL bb : Word) (r : List Word)
theorem cpW_nil (h : dL = 0) : cpW (n + 1) m hp dO dL = some ([1], m) := by simp [cpW, h]
theorem cpW_cons (h : ¬ dL = 0) : cpW (n + 1) m hp dO dL = cpK1 n hp dO dL (bvbW n m (rdW (m.arr64 IW) dO) CWF) := by
  simp [cpW, h]
theorem cpK1_b (h : bb ≠ 0) : cpK1 n hp dO dL (some (bb, m1)) = some ([0], m1) := by simp [cpK1, h]
theorem cpK1_ok (h : ¬ bb ≠ 0) : cpK1 n hp dO dL (some (bb, m1)) =
    cpK2 n hp dO dL (fvbF m1 [CWF, rdW (m1.arr64 IW) dO]) := by simp [cpK1, h]
theorem cpK2_out (h : hp < r.headD 0) : cpK2 n hp dO dL (some (r, m1)) = some ([0], m1) := by
  rw [cpK2, ite_eq_left h]
theorem cpK2_in (h : ¬ hp < r.headD 0) : cpK2 n hp dO dL (some (r, m1)) = cpW n m1 hp (dO + 1) (dL - 1) := by
  rw [cpK2, ite_eq_right h]
end arms
attribute [ind_grind] cpW_nil cpW_cons cpK1_b cpK1_ok cpK2_out cpK2_in

theorem nestContParamsClosed_spec (p : Prog) (hb : BvbProg p) (hf : HfF p)
    (hp : p.lookup "nest_cont_params_closed" = some nestContParamsClosedL) (n : Nat) :
    ∀ (s₀ : St) (hpw dO dL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_params_closed" [hpw, dO, dL]
    ⦃fun r s' => LocEq s' s₀ ∧ cpW n s₀.mem hpw dO dL = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ hpw dO dL
    rw [invoke_eq _ hp]; simp only [callFn, nestContParamsClosedL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ hpw dO dL
    simp only [invoke_eq _ hp, callFn, nestContParamsClosedL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        bvarBL_spec p hb n, fvbF_spec p hf n, ih] <;>
      finish (gen := 20) [rdW_eq]

end L.Ind

namespace L.Ind

open L.Arena

theorem pos2Pin_spec (p : Prog) (hp : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_at" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ pos2PinW s₀.mem i = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, pinAtL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [pos2PinW, pinW_eq, rdW_eq]

/-- The model of `nest_cont_checks(ctx, hp, n, dsOff, dsLen, idxOff, idxLen)`. -/
def p2ccW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | k + 1, m, ctx, hp, nn, dO, dL, iO, iL =>
    p2ccK1 k hp nn dO dL (noaW k m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1))
      (rdW (m.arr64 IW) (ctx + 4)) hp iO iL)

section arms
variable (k : Nat) (m1 m2 : Mem) (hp nn dO dL : Word) (r : List Word)
theorem p2ccK2_nz (h : ¬ r.headD 0 = 0) : p2ccK2 (some (r, m2)) = some ([0], m2) := by rw [p2ccK2, ite_eq_right h]
end arms
attribute [ind_grind] p2ccK2_nz

theorem nestContChecks_spec (p : Prog) (hl : NoLook p) (hoa : p.lookup "nest_occ_any" = some nestOccAnyL)
    (hpa : p.lookup "pin_at" = some pinAtL) (hb : BvbProg p) (hf : HfF p)
    (hpc : p.lookup "nest_cont_params_closed" = some nestContParamsClosedL)
    (hp : p.lookup "nest_cont_checks" = some nestContChecksL) (n : Nat) (s₀ : St)
    (ctx hpw nn dO dL iO iL : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_checks" [ctx, hpw, nn, dO, dL, iO, iL]
    ⦃fun r s' => LocEq s' s₀ ∧ p2ccW n s₀.mem ctx hpw nn dO dL iO iL = some ([r.headD 0], s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestContChecksL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestOccAny_spec p hl hoa n, pos2Pin_spec p hpa n, nestContParamsClosed_spec p hb hf hpc n] <;>
      finish (gen := 20) [p2ccW, p2ccK1, rdW_eq]

end L.Ind

end
