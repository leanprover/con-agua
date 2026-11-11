module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.InstList
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.InstList

@[expose] public section

/-!
# The specs of `instantiateList`'s arms, and the entry

As `Inst1Spec.lean`, for both walks: the arms' steps, the induction on the fuel
(`instList_spec`), the entry `inst_list(e, o, l, d)` (`instantiateListFast`) and the program
`instListProg`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **The pure walk and its arms are their models** (`instantiateList vs`). -/
l_model ilW_spec (p : Prog) (hp : InstListProg p)
  fns [hp.get "il_go" ↦ ilW, hp.get "il_app" ↦ ilAppW, hp.get "il_lam" ↦ ilLamW,
    hp.get "il_forall" ↦ ilForallW, hp.get "il_let" ↦ ilLetW, hp.get "il_proj" ↦ ilProjW,
    hp.get "il_bvar" ↦ ilBVarW]
  specs [derBv_spec p (hp.get "der_bv") n,
    mkApp_spec p (hp.get "der_b") (hp.get "app_find") (hp.get "app_push") (hp.get "intern_app")
      (hp.get "mk_app") n,
    mkLam_spec p (hp.get "der_b") (hp.get "lam_find") (hp.get "lam_push") (hp.get "intern_lam")
      (hp.get "mk_lam") n,
    mkForall_spec p (hp.get "der_b") (hp.get "forall_find") (hp.get "forall_push")
      (hp.get "intern_forall") (hp.get "mk_forall") n,
    mkLet_spec p (hp.get "der_b") (hp.get "letE_find") (hp.get "letE_push") (hp.get "intern_letE")
      (hp.get "mk_let") n,
    mkProj_spec p (hp.get "der_b") (hp.get "proj_find") (hp.get "proj_push") (hp.get "intern_proj")
      (hp.get "mk_proj") n,
    internBVar_spec p (hp.get "bvar_find") (hp.get "bvar_push") (hp.get "intern_bvar") n]
  grind [arena_grind] fold [slW] extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
    evalE_idxAE, evalE_idxGE, evalE_tagE] finish [viewOK, viewOKA, tierW, idxW, slW] gen 20

/-- **The memo walk and its arms are their models** (`instantiateListGo vs`). -/
l_model ilgW_spec (p : Prog) (hp : InstListProg p)
  fns [hp.get "ilg_go" ↦ ilgW, hp.get "ilg_app" ↦ ilgAppW, hp.get "ilg_lam" ↦ ilgLamW,
    hp.get "ilg_forall" ↦ ilgForallW, hp.get "ilg_let" ↦ ilgLetW, hp.get "ilg_proj" ↦ ilgProjW]
  specs [derBv_spec p (hp.get "der_bv") n, (ilW_spec p hp n).1,
    memoFindG_spec ilSch p _ (hp.get "ilm_find") n, memoPutG_spec ilSch p _ (hp.get "ilm_put") n,
    mkApp_spec p (hp.get "der_b") (hp.get "app_find") (hp.get "app_push") (hp.get "intern_app")
      (hp.get "mk_app") n,
    mkLam_spec p (hp.get "der_b") (hp.get "lam_find") (hp.get "lam_push") (hp.get "intern_lam")
      (hp.get "mk_lam") n,
    mkForall_spec p (hp.get "der_b") (hp.get "forall_find") (hp.get "forall_push")
      (hp.get "intern_forall") (hp.get "mk_forall") n,
    mkLet_spec p (hp.get "der_b") (hp.get "letE_find") (hp.get "letE_push") (hp.get "intern_letE")
      (hp.get "mk_let") n,
    mkProj_spec p (hp.get "der_b") (hp.get "proj_find") (hp.get "proj_push") (hp.get "intern_proj")
      (hp.get "mk_proj") n]
  grind [arena_grind] extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
    evalE_idxAE, evalE_idxGE, evalE_tagE] finish [viewOK, viewOKA, tierW, idxW] gen 20

/-! ## `inst_list(e, o, l, d)`: `instantiateListFast`, between two clears

The walk's depth counter starts at `coreWalkFuel` (`4000000000`). -/

/-- After the walk: clear the memo again. -/
def ilclrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) =>
    if rdW (m₁.arr64 CTL) 50 + 2 = 0 then none else some (r &&& 4294967295, mclearFitG ilSch m₁)

/-- **The model of `inst_list`.** -/
def instListW (n : Nat) (m : Mem) (e o l d : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 50 + 2 = 0 then none else ilclrK (ilgW n (mclearFitG ilSch m) e d o l 4000000000)

theorem instListW_eq (n : Nat) (m : Mem) (e o l d : Word) (h0 : rdW (m.arr64 CTL) 50 + 2 ≠ 0) :
    instListW n m e o l d = ilclrK (ilgW n (mclearFitG ilSch m) e d o l 4000000000) := by
  simp [instListW, h0]

theorem ilclrK_some (r : Word) (m₁ : Mem) (h0 : rdW (m₁.arr64 CTL) 50 + 2 ≠ 0) :
    ilclrK (some (r, m₁)) = some (r &&& 4294967295, mclearFitG ilSch m₁) := by simp [ilclrK, h0]

grind_pattern [arena_grind] instListW_eq => instListW n m e o l d
grind_pattern [arena_grind] ilclrK_some => ilclrK (some (r, m₁))

/-- con-ron: ConRon/Arena/ExprOps.lean:647-654 ConRon.Arena.instantiateListFast -/
@[no_expose, l_impl ConRon.Arena.instantiateListFast]
def instListL : FunDecl := lfn (e, o, l, d) locals (r, u) {
  if ILMEMO.u64[3] == 0 && CTL.u64[51] <= ⟪FITLO⟫ { u := call ilm_clear() } else { u := call ilm_fit() };
  r := call ilg_go(e, d, o, l, 4000000000);
  if ILMEMO.u64[3] == 0 && CTL.u64[51] <= ⟪FITLO⟫ { u := call ilm_clear() } else { u := call ilm_fit() };
  return r & 4294967295
}

/-- `clear_fit`'s fast path for `ilSch`. -/
theorem ilm_fast (m : Mem) (h3 : rdW (m.arr64 ILMEMO) 3 = 0) (hc : rdW (m.arr64 CTL) 51 ≤ FITLO) :
    mclearFitG ilSch m = mclearG ilSch m :=
  mclearFitG_fast ilSch m (by decide) h3 hc

theorem instList_spec' (p : Prog) (hp : InstListProg p) (he : p.lookup "inst_list" = some instListL)
    (n : Nat) (s₀ : St) (e o l d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "inst_list" [e, o, l, d]
    ⦃fun r s' => LocEq s' s₀ ∧ instListW n s₀.mem e o l d = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (ilgW_spec p hp n).1
  rw [invoke_eq _ he]
  simp only [callFn, instListL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoClearG_spec ilSch p _ (hp.get "ilm_clear") n,
      memoClearFitG_spec ilSch p _ (hp.get "ilm_fit") n, ih] <;>
    finish [ilm_fast, cntG]

/-- Both walks, their memo and `liftProg` (the `mk_*`, the stores), as one program. -/
def instListProg : Prog := instListWalkProg ++ [("inst_list", instListL)]

end L.Arena
