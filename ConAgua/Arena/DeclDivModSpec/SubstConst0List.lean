import ConAgua.Arena.LdRd
import ConAgua.Arena.DeclDivModSpec.Sc0List
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# SubstConst0List: `ConRon.Arena.divModCertApplied`, `ConRon.Arena.substConst0List`

The refinement theorems `divModCertApplied_refines`, `substConst0List_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section subst
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- **`subst_const_all` refines `substConstAll`** at the walk fuel `4000000000`. -/
def SubstCAll : Prop := ∀ nm r h : Word, H nm → H r → H h →
  CallRef p "subst_const_all" [nm, r, 4000000000, h] (StageR dn vis fe)
    (substConstAll (decI nm) (decE r) coreWalkFuel (decE h)) (KeepPost dn vis fe decW0E)

end subst

section applied
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

@[refines ConRon.Arena.divModCertApplied]
theorem divModCertApplied_refines (hD : DmProg5 p) (pr ho hl : Word) (hyps : List EIdx) :
    RefAM p "div_mod_cert_applied" [pr, ho, hl]
      (fun m s => StageR dn vis fe m s ∧ H pr ∧ decHL m ho.toNat hl.toNat = some hyps ∧
        ho.toNat + hl.toNat ≤ iwTop m)
      (divModCertApplied (decE pr) hyps) (KeepPost dn vis fe decW0E) :=
  (applied_ref hD pr ho hl hyps).refAM

@[refines ConRon.Arena.substConst0List]
theorem substConst0List_refines (hD : DmProg5 p) (hs0 : SubstC0 p dn vis fe) (nm r o l : Word)
    (hn : H nm) (hr : H r) (hyps : List EIdx) :
    RefAM p "subst_const0_list" [nm, r, o, l]
      (fun m s => StageR dn vis fe m s ∧ decHL m o.toNat l.toNat = some hyps ∧
        o.toNat + l.toNat ≤ iwTop m)
      (substConst0List (decI nm) (decE r) hyps)
      (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) :=
  CallRef.refAM (fun k m a res m' ⟨hS, hd, hb⟩ hc =>
    sc0List_ref hD hs0 nm r hn hr hyps o l k m a res m' hS hd hb hc)

set_option maxHeartbeats 1600000 in
theorem cra_specW (p : Prog) (hp : p.lookup "consts_resolve_all" = some constsResolveAllL)
    (cl : CallM) (hcl : CallSpec p cl) (n : Nat) (s₀ : St) (vs o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "consts_resolve_all" [vs, o, l]
    ⦃fun res s' => LocEq s' s₀ ∧ craW p cl n s₀.mem vs o l = some (res, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, constsResolveAllL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      hcl n "consts_resolve_ffast", callW_spec p n "consts_resolve_all"] <;>
    finish (gen := 30) (instances := 10000) [craW, ntBW, rdW_eq]

set_option maxHeartbeats 3200000 in
theorem cg_specW (p : Prog) (hb : BvbProg p) (hf : HfF p) (hp : p.lookup "div_mod_cert_guard" = some divModCertGuardL)
    (cl : CallM) (hcl : CallSpec p cl) (n : Nat) (s₀ : St) (vs c annVal ho hl eqE proof : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "div_mod_cert_guard" [vs, c, annVal, ho, hl, eqE, proof]
    ⦃fun res s' => LocEq s' s₀ ∧ dmCgW p cl n s₀.mem vs c annVal ho hl eqE proof = some (res, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divModCertGuardL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, lbbF_spec p hb n, hffF_spec p hf n,
    hcl n "all_level_params_defined", hcl n "consts_resolve_ffast", callW_spec p n "subst_const_all",
    callW_spec p n "subst_const0_list", callW_spec p n "consts_resolve_all", callW_spec p n "subst_const0"]
  all_goals subst_vars
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, List.headD_cons,
    List.headD_nil, List.tail_cons, List.tail_nil, Locals.init_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at *)
  all_goals grind (gen := 30) (instances := 10000) [lang_grind, arena_grind, dmCgW, ntBW]

theorem fuelW_eq : (4000000000 : Word).toNat = coreWalkFuel := rfl

end applied

end L.Ind

end
