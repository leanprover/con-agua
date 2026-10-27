import ConAgua.Arena.IndPosSpec.NcnW2

/-!
# NestCtorNf: `ConRon.Arena.nestCtorNf`

The refinement theorems `nestCtorNf_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section census
variable (p : Prog) (L : RxLook p) (hp : p.lookup "nest_ctor_nf" = some nestCtorNfL)
include L hp

/-- **`nest_ctor_nf` refines `nestCtorNf`** (through `mk_app_n`'s stub in the hole images). -/
@[refines ConRon.Arena.nestCtorNf]
theorem nestCtorNf_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis ctx po pl us dO dL cv closed : Word) (c : NestCtx) (prog : List NestHole) (ds : List EIdx)
    (cvv : IConstantVal) (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word) (hS : StageR dn vis fe s₀.mem a₀)
    (hc : decCtx s₀.mem ctx.toNat = some c) (hin : CtxIn s₀.mem ctx.toNat (· < iwTop s₀.mem))
    (hs : HSl s₀.mem po.toNat pl.toNat prog) (hb : c.nP + c.names.length + pl.toNat < 2 ^ 64) (hus : H us)
    (hds : decHL s₀.mem dO.toNat dL.toNat = some ds) (hdsb : ∀ j < dL.toNat, dO.toNat + j < iwTop s₀.mem)
    (hcl : H closed) (hcv : decCV (erecP s₀.mem) cv.toNat = some cvv) (hR : RfInv s₀.mem M G g) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_ctor_nf" [ctx, po, pl, us, dO, dL, cv, closed]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestCtorNf c prog (decI us) ds cvv (decE closed)) a₀ ∧
      decNCN s'.mem (r.headD 0).toNat =
        some (AM.res (ConRon.Arena.nestCtorNf c prog (decI us) ds cvv (decE closed)) a₀) ∧
      (r.headD 0).toNat + 5 ≤ iwTop s'.mem ∧
      RxPost dn fe vis s₀.mem s'.mem (AM.st (ConRon.Arena.nestCtorNf c prog (decI us) ds cvv (decE closed)) a₀)
        M G g; ⊤⦄ := by
  refine triple_post (nestCtorNf_spec p L hp k s₀ ctx po pl us dO dL cv closed) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hdec, hb5, hpost⟩ := ncnW_ok dn fe vis k _ _ a₀ ctx po pl us dO dL cv closed _ c prog ds cvv
    M G g hm hS hc hin hs hb hus hds hdsb hcl hcv hR
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hdec.get (decNCN_mono _), hb5, by rw [hst]; exact hpost⟩

end census

end L.Ind

end
