module

public import ConAgua.Arena.IndPosSpec.NestOccAny

public import ConAgua.Arena.IndPosSpec.CrLook
public import ConAgua.Arena.IndPosSpec.NkcW
public import ConAgua.Arena.IndPosSpec.PfLook
public import ConAgua.Arena.IndPosSpec.RootHoles
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndPos2
import all ConAgua.Arena.IndSum
import ConAgua.Arena.IndPosSpec.UnW

@[expose] public section

/-!
# U4W

`structUsedLater_spec'`, `nestCtorsU4_spec` (`u4W`, generated), `u4W_kId`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

end L.Ind

namespace L.Ind

open L.Arena

end L.Ind

namespace L.Ind

open L.Arena

theorem structUsedLater_spec' (p : Prog) (L : UslLook p) (n : Nat) (s₀ : St) (cty nP j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_used_later" [cty, nP, j]
    ⦃fun r s' => LocEq s' s₀ ∧ ustWf n s₀.mem cty nP j = some (r.headD 0, s'.mem); ⊤⦄ := by
  match n with
  | 0 => rw [invoke_eq _ L.hp]; simp only [callFn, structUsedLaterL]; vcgen [exec] <;> grind
  | 1 =>
    rw [invoke_eq _ L.hp]; simp only [callFn, structUsedLaterL]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, invoke_exec0 p] <;> grind
  | n + 2 => exact structUsedLater_spec p L.hv L.hf L.hput L.hins L.hgo L.hbp L.hst L.hcl L.hfast L.hp n s₀ cty nP j

/-- **`nest_ctors_u4(ko, nF, closed, i)` is its model `u4W`** (generated). -/
l_model nestCtorsU4_spec (p : Prog) (L : UslLook p) (hp : p.lookup "nest_ctors_u4" = some nestCtorsU4L)
  fns [hp ↦ u4W list]
  specs [structUsedLater_spec' p L n]
  grind [arena_grind]

theorem u4W_kIdem (x : Option (List Word × Mem)) :
    u4W.k_nest_ctors_u4 (u4W.k_nest_ctors_u4 x) = u4W.k_nest_ctors_u4 x := by
  rcases x with _ | ⟨r, m⟩ <;> simp [u4W.k_nest_ctors_u4]

/-- The generated result step `u4W.k_nest_ctors_u4` is the identity on `u4W`'s results. -/
theorem u4W_kId (n : Nat) (m : Mem) (ko nF cl i : Word) :
    u4W.k_nest_ctors_u4 (u4W n m ko nF cl i) = u4W n m ko nF cl i := by
  rcases n with _ | n
  · simp [u4W.eq_1, u4W.k_nest_ctors_u4]
  by_cases h1 : nF ≤ i
  · rw [u4W.arm1 (hc1 := h1)]; simp [u4W.k_nest_ctors_u4]
  by_cases h2 : rdW (m.arr64 IW) (ko + i) ≠ 0
  · rw [u4W.arm2 (hc1 := h1) (hc2 := h2)]
    generalize ustWf _ _ _ _ _ = x; rcases x with _ | ⟨su, m1⟩
    · simp [u4W.k_struct_used_later, u4W.k_nest_ctors_u4]
    by_cases h3 : su ≠ 0
    · rw [u4W.k_struct_used_later.arm1 (hc1 := h3)]; simp [u4W.k_nest_ctors_u4]
    · rw [u4W.k_struct_used_later.arm2 (hc1 := Classical.not_not.mp h3), u4W.j1.arm1, u4W_kIdem]
  · rw [u4W.arm3 (hc1 := h1) (hc2 := Classical.not_not.mp h2), u4W.j1.arm1, u4W_kIdem]

end L.Ind

namespace L.Ind

open L.Arena

end L.Ind

namespace L.Ind

open L.Arena

/-- The lookups of `nest_ctors_crest`. -/
structure CtLook (p : Prog) : Prop where
  cr : CrLook p
  ha : p.lookup "iw_alloc" = some iwAlloc
  hc : p.lookup "er_copy" = some erCopy
  he : p.lookup "er_to_iw" = some erToIw
  hcv : p.lookup "cv_lps" = some cvLps
  hsc : p.lookup "sl_contains" = some slContains
  hnd : p.lookup "sl_nodup" = some slNodup
  hp : p.lookup "nest_ctors_crest" = some nestCtorsCrestL

end L.Ind

end
