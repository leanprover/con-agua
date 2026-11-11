module

public import ConAgua.Arena.IndPosSpec.CfW
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.Arena.IndPosSpec.NbLook
import ConAgua.Arena.IndPosSpec.UnW
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos2
import all ConAgua.Arena.IndSum

@[expose] public section

/-!
# GgW2

`posRecW_iwFr`, `snocW_iwFr`, `slNew1_specW` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `posRecW` writes the record pool only. -/
theorem posRecW_iwFr {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m')) :
    MemFrame [IW] [200] m m' := by
  simp only [posRecW] at h
  rcases hal : allocW m (UInt64.ofNat ws.length) with _ | ⟨q1, m1⟩ <;> rw [hal] at h; · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact (allocW_iwFrame hal).trans (wrIW_frame _ _ _)

/-- `snocW` writes the record pool only. -/
theorem snocW_iwFr {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} (h : snocW n m o l x = some (r, m')) :
    MemFrame [IW] [200] m m' := by
  unfold snocW at h
  split at h; · simp at h
  split at h; · simp at h
  rename_i q m1 hal
  split at h; · simp at h
  rename_i m2 hc
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ((allocW_iwFrame hal).trans (L.Ind.copyW_iwFrame _ _ _ _ _ _ hc)).trans (set64IW_frame _ _ _)

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem slNew1_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "sl_new1" = some slNew1) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "sl_new1" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ new1W s₀.mem x = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, slNew1]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, iwAlloc_specW p ha n] <;>
      finish [new1W, allocMem, allocW]

end L.Ind

namespace L.Ind

open L.Arena

end L.Ind

namespace L.Ind

open L.Arena

end L.Ind

namespace L.Ind

open L.Arena

end L.Ind

end

end

section

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

theorem nestHoleAt_spec' (p : Prog) (L : PfLook p) (k : Nat) (s₀ : St) (ctx po pl i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_hole_at" [ctx, po, pl, i]
    ⦃fun r s' => LocEq s' s₀ ∧ haWf k s₀.mem ctx po pl i = some (r, s'.mem); ⊤⦄ :=
  nestHoleAt_spec p L.ha L.h3 L.hsg L.h4 L.hrg L.hr L.hc L.hap L.hha k s₀ ctx po pl i


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

theorem nestCtorsU4_spec (p : Prog) (L : UslLook p) (hp : p.lookup "nest_ctors_u4" = some nestCtorsU4L)
    (n : Nat) : ∀ (s₀ : St) (ko nF cl i : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors_u4" [ko, nF, cl, i]
    ⦃fun r s' => LocEq s' s₀ ∧ u4W n s₀.mem ko nF cl i = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ ko nF cl i
    rw [invoke_eq _ hp]; simp only [callFn, nestCtorsU4L]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ko nF cl i
    simp only [invoke_eq _ hp, callFn, nestCtorsU4L]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, structUsedLater_spec' p L n, ih] <;>
      finish (gen := 20) [rdW_eq]

end L.Ind

namespace L.Ind

open L.Arena

end L.Ind

end

end


section


/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the L side — every
function of the block refines its word model, by one induction on the exec fuel. -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

-- `posRec3_eq`, `rec3_specW_iw`: `CtxFields.lean`.

theorem pos2_getElem_getD (a : Array Word) (i : Nat) (h : i < a.size) : a[i] = a[i]?.getD 0 := by
  simp [h]

theorem nestWalkStack_spec' (p : Prog) (L : NbLook p) (n : Nat) (s₀ : St) (ctx off l po pl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_walk_stack" [ctx, off, l, po, pl]
    ⦃fun r s' => LocEq s' s₀ ∧ nwsWf n s₀.mem ctx off l po pl = some (r, s'.mem); ⊤⦄ :=
  nestWalkStack_spec p L.dc L.hws n s₀ ctx off l po pl

end L.Ind

end

end
