module

import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndPosSpec.MapOKStep
public import ConAgua.Arena.IndPosSpec.SgF
public import ConAgua.Arena.IndPosSpec.SgGoW2
public import ConAgua.Arena.IndGrindAttr
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPosSpec.DepthGo
import ConAgua.Arena.IndPosSpec.NestKeyMap
import ConAgua.Arena.IndPosSpec.PosmemoRxMfr
import ConAgua.Arena.IndPosSpec.SnocWStage
public import ConAgua.Arena.IndPosSpec.BvbWMfr
public import ConAgua.Arena.IndPosSpec.CrLook
public import ConAgua.Arena.IndPosSpec.Pos2CvLpsWStage

@[expose] public section

/-!
# SgGoW

`rpConstW_fr`, `PosMR.setRf`, `sgK1_big`, `sgGoW_ok`.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem rpConstW_fr {n : Nat} {m m' : Mem} {no nl us b nn e r : Word}
    (h : rpConstW n m no nl us b nn e = some (r, m')) : RfFr m m' :=
  RfFr.of_mfr (rpConstW_mfr h) (by decide) (by decide)

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

/-- Across the banked `replace_fvars` walk. -/
theorem PosMR.setRf {m m' : Mem} (h : PosMR m) (hf : RxFr m m') (hn : ∃ M G g, RfInv m' M G g) :
    PosMR m' := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, -⟩ := h
  exact ⟨⟨a, noMR_mfr hf (by decide) (by decide) ha⟩, ⟨b, dpMR_mfr hf (by decide) (by decide) hb⟩,
    ⟨c, rpMR_mfr hf (by decide) (by decide) hc⟩, ⟨d, hbMR_mfr hf (by decide) (by decide) hd⟩, hn⟩

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

section arms
variable (k : Nat) (m m1 m2 : Mem) (ctx f dO dL q j y z : Word)
theorem sgK1_big (h : 4294967296 ≤ y) : sgK1 k ctx f dO dL q j (some (y, m1)) = none := by simp [sgK1, h]
end arms
attribute [ind_grind] sgK1_big

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem sgGoW_ok (k : Nat) :
    ∀ (m0 m m' : Mem) (a : AState) (ctx f dO dL q j : Word) (c : NestCtx) (holes ds acc : List EIdx)
      (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word),
    sgGoW k m ctx f dO dL q j = some m' → StageR vis fe m a → IWGrow m0 m → iwTop m0 ≤ q.toNat →
    q.toNat + dL.toNat ≤ iwTop m → decCtx m0 ctx.toNat = some c → CtxIn m0 ctx.toNat (· < iwTop m0) →
    CtxSl m0 ctx.toNat → c.nP + c.names.length < 2 ^ 64 → FMOk m0 f.toNat (.keyMap c.params holes) →
    decHL m0 dO.toNat dL.toNat = some ds → (∀ j < dL.toNat, dO.toNat + j < iwTop m0) → j.toNat ≤ dL.toNat →
    decHL m q.toNat j.toNat = some acc → RfInv m M G g → PosMR m →
    ∃ ys a', ((ds.drop j.toNat).mapM (sgF c holes)).run a = .ok (ys, a') ∧
      decHL m' q.toNat dL.toNat = some (acc ++ ys) ∧ StageR vis fe m' a' ∧ IWGrow m0 m' ∧
      iwTop m ≤ iwTop m' ∧ (∃ M' G', RfInv m' M' G' g ∧ GKeep M M' G g ∧ G ≤ G') ∧ PosMR m' := by
  sorry

end rel

end L.Ind

end

end
