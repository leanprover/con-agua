import ConAgua.Arena.IndPosSpec.NbLook
import ConAgua.Arena.IndPosSpec.NbPosW

/-!
# Nb

`whnfWalkFuel_spec'`, `NbSpec`.
-/

set_option linter.unusedSectionVars false

/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the L side — every
function of the block refines its word model, by one induction on the exec fuel. -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Leaf callees at any exec fuel -/

theorem whnfWalkFuel_spec' (p : Prog) (L : NbLook p) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "whnf_walk_fuel" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ wfWf n s₀.mem e = some ([r.headD 0], s'.mem); ⊤⦄ := by
  match n with
  | 0 => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | 1 =>
    rw [invoke_eq _ L.hwf]; simp only [callFn, whnfWalkFuel]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, invoke_exec0 p] <;> grind
  | n + 2 =>
    refine triple_post (whnfWalkFuel_spec p L.ct.cr.rx.hl.hv L.hdf L.hdp L.hdg L.hdn L.hdc L.hdd L.hwf n s₀ e) ?_
    rintro r s' ⟨h1, h2⟩
    exact ⟨h1, by simp [wfWf, h2]⟩

section spec
variable (p : Prog)

/-- The specs of the block at exec fuel `n`. -/
def NbSpec (cR : CallM) (n : Nat) : Prop :=
  (∀ (s₀ : St) (vis ctx fu po pl dep kb e ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_pos" [vis, ctx, fu, po, pl, dep, kb, e, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbPosW cR n s₀.mem vis ctx fu po pl dep kb e ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl dep kb w ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_pos_bind" [vis, ctx, fu, po, pl, dep, kb, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbBindW cR n s₀.mem vis ctx fu po pl dep kb w ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl kb hi w ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_pos_app" [vis, ctx, fu, po, pl, kb, hi, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbAppW cR n s₀.mem vis ctx fu po pl kb hi w ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl kb nn us aO aL ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_cont" [vis, ctx, fu, po, pl, kb, nn, us, aO, aL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbContW cR n s₀.mem vis ctx fu po pl kb nn us aO aL ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_cont_key" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbKeyW cR n s₀.mem vis ctx fu po pl kb nn us dO dL nPc cty ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_cont_new" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbNewW cR n s₀.mem vis ctx fu po pl kb nn us dO dL nPc cty ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_frame" [vis, ctx, fu, po, pl, hi, us, dO, dL, nPc, gO, gL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbFrameW cR n s₀.mem vis ctx fu po pl hi us dO dL nPc gO gL ns =
      some ([r.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_ctors" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cO, cL, ns,
      oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧ nbCtorsW cR n s₀.mem vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_ctors_one" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cv, nF, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbOneW cR n s₀.mem vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx root fu po pl hi nF crest ns : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_ctors_walk" [vis, ctx, root, fu, po, pl, hi, nF, crest, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbWalkW cR n s₀.mem vis ctx root fu po pl hi nF crest ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
        r.tail.tail.tail.tail.headD 0], s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (vis ctx fu po pl base nF j cur ns kO kL dO dL : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nest_fields" [vis, ctx, fu, po, pl, base, nF, j, cur, ns, kO, kL, dO, dL]
    ⦃fun r s' => LocEq s' s₀ ∧ nbFieldsW cR n s₀.mem vis ctx fu po pl base nF j cur ns kO kL dO dL =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
        r.tail.tail.tail.tail.headD 0, r.tail.tail.tail.tail.tail.headD 0], s'.mem); ⊤⦄)

end spec

end L.Ind

end
