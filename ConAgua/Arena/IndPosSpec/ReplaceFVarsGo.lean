import ConAgua.Arena.IndPosSpec.MapOKStep

/-!
# ReplaceFVarsGo: `ConRon.Arena.fvMapAt`, `ConRon.Arena.nestHoleImg`, `ConRon.Arena.replaceFVarsGo`, `ConRon.Arena.replaceFVars`

The refinement theorems `replaceFVars_refines`, `replaceFVarsGo_refines`, `fvMapAt_refines`, `nestHoleImg_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section census
variable (p : Prog) (L : RxLook p)
include L

/-- **`replace_fvars` refines `replaceFVars`** (through the `mk_app_n` stub of the hole images): one
memoised walk in a fresh bank of the banked memo, the caller's banks untouched. -/
@[refines ConRon.Arena.replaceFVars]
theorem replaceFVars_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis f e : Word) (fm : FvMap) (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word)
    (hS : StageR dn vis fe s₀.mem a₀) (hfm : FMOk s₀.mem f.toNat fm) (he : H e) (hR : RfInv s₀.mem M G g) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "replace_fvars" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.replaceFVars fm (decE e)) a₀ ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.replaceFVars fm (decE e)) a₀ ∧ H (r.headD 0) ∧
      RxPost dn fe vis s₀.mem s'.mem (AM.st (ConRon.Arena.replaceFVars fm (decE e)) a₀) M G g; ⊤⦄ := by
  refine triple_post ((rxSpec_all p L n).2.2.2.2.2.2.2 s₀ f e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hH, hpost⟩ := (rxOK_all dn fe vis n).2.2.2.2.2.2 _ _ a₀ f e fm _ M G g hm hS hfm he hR
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres], hH, by rw [hst]; exact hpost⟩

/-- **`replace_fvars_go` (with `replace_fvars_node`) refines `replaceFVarsGo`**, from a memo whose
current bank is the twin's. -/
@[refines ConRon.Arena.replaceFVarsGo]
theorem replaceFVarsGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis f fu h : Word) (fm : FvMap) (mp : Std.HashMap EIdx EIdx)
    (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word)
    (hS : StageR dn vis fe s₀.mem a₀) (hfm : FMOk s₀.mem f.toNat fm) (hh : H h) (hR : RfInv s₀.mem M G g)
    (hb : Bank M g mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "replace_fvars_go" [f, fu, h]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.replaceFVarsGo fm mp fu.toNat (decE h)) a₀ ∧
      decE (r.headD 0) = (AM.res (ConRon.Arena.replaceFVarsGo fm mp fu.toNat (decE h)) a₀).1 ∧
      GoPost dn fe vis s₀.mem s'.mem (AM.st (ConRon.Arena.replaceFVarsGo fm mp fu.toNat (decE h)) a₀) M G g
        (AM.res (ConRon.Arena.replaceFVarsGo fm mp fu.toNat (decE h)) a₀).2; ⊤⦄ := by
  refine triple_post ((rxSpec_all p L n).2.2.2.2.2.1 s₀ f fu h) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨mp', a', M', G', hrun, h1, h2, h3, h4, h5, h6⟩ :=
    (rxOK_all dn fe vis n).2.2.2.2.2.1 _ _ a₀ f fu h fm mp _ M G g hm hS hfm hh hR hb
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres], by rw [hst, hres]; exact ⟨M', G', h1, h2, h3, h4, h5, h6⟩⟩

/-- **`fv_map_at` refines `fvMapAt`** (the four maps; the hole images through `mk_app_n`'s stub). -/
@[refines ConRon.Arena.fvMapAt]
theorem fvMapAt_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis f i : Word) (fm : FvMap) (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word)
    (hS : StageR dn vis fe s₀.mem a₀) (hfm : FMOk s₀.mem f.toNat fm) (hR : RfInv s₀.mem M G g) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "fv_map_at" [f, i]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.fvMapAt fm i.toNat) a₀ ∧
      OptE (r.headD 0) (r.tail.headD 0) (AM.res (ConRon.Arena.fvMapAt fm i.toNat) a₀) ∧
      RxPost dn fe vis s₀.mem s'.mem (AM.st (ConRon.Arena.fvMapAt fm i.toNat) a₀) M G g; ⊤⦄ := by
  refine triple_post ((rxSpec_all p L n).1 s₀ f i) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hout, hpost⟩ := (rxOK_all dn fe vis n).1 _ _ a₀ f i fm _ _ M G g hm hS hfm hR
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hout, by rw [hst]; exact hpost⟩

/-- **`nest_hole_img` (with its root, frame and `ds` helpers) refines `nestHoleImg`**. -/
@[refines ConRon.Arena.nestHoleImg]
theorem nestHoleImg_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis ctx po pl nn i : Word) (c : NestCtx) (prog : List NestHole)
    (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word) (hS : StageR dn vis fe s₀.mem a₀)
    (hc : decCtx s₀.mem ctx.toNat = some c) (hin : CtxIn s₀.mem ctx.toNat (· < iwTop s₀.mem))
    (hs : HSl s₀.mem po.toNat pl.toNat prog) (hb : c.nP + c.names.length + nn.toNat < 2 ^ 64)
    (hR : RfInv s₀.mem M G g) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_hole_img" [ctx, po, pl, nn, i]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestHoleImg c prog nn.toNat i.toNat) a₀ ∧
      OptE (r.headD 0) (r.tail.headD 0) (AM.res (ConRon.Arena.nestHoleImg c prog nn.toNat i.toNat) a₀) ∧
      RxPost dn fe vis s₀.mem s'.mem (AM.st (ConRon.Arena.nestHoleImg c prog nn.toNat i.toNat) a₀) M G g; ⊤⦄ := by
  refine triple_post ((rxSpec_all p L n).2.1 s₀ ctx po pl nn i) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hout, hpost⟩ := (rxOK_all dn fe vis n).2.1 _ _ a₀ ctx po pl nn i c prog _ _ M G g hm hS hc
    hin hs hb hR
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hout, by rw [hst]; exact hpost⟩

end census

end L.Ind

end
