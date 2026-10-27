module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.ArRange
import ConAgua.Arena.LdRd
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The specs of `abstractRange`'s arms, and the entry

As `Abs1Spec.lean`; the entry `ar_entry(e, d, k, c)` (`abstractRangeFast`) adds the `k = 0`
identity before the two clears.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

section specs
variable (p : Prog) (hp : ArProg p)

include hp in
theorem arApp_step (n : Nat) (ih : ArGoSpec p n) (s₀ : St) (h c d k fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ar_app" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arAppW (n + 1) s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold ArGoSpec at ih
  rw [invoke_eq _ (hp.get "ar_app")]
  simp only [callFn, arApp]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, evalE_tld, tld, evalE_cnt,
    tcntM, evalE_tierE, evalE_idxE,
    memoFindG_spec abSch p _ (hp.get "ab_find") n, memoPutG_spec abSch p _ (hp.get "ab_put") n,
        ih,
    mkApp_spec p (hp.get "der_b") (hp.get "app_find") (hp.get "app_push") (hp.get "intern_app")
        (hp.get "mk_app") n]
  all_goals subst_vars
  all_goals (try simp only [LocEq] at *)
  all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval,
    Nat.reduceEqDiff, reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
  all_goals grind [lang_grind, arena_grind, asetK, arAppW, rbAppW, viewOK, tierW, idxW]

include hp in
theorem arLam_step (n : Nat) (ih : ArGoSpec p n) (s₀ : St) (h c d k fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ar_lam" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arLamW (n + 1) s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold ArGoSpec at ih
  rw [invoke_eq _ (hp.get "ar_lam")]
  simp only [callFn, arLam]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, evalE_tld, tld, evalE_cnt,
    tcntM, evalE_tierE, evalE_idxE,
    memoFindG_spec abSch p _ (hp.get "ab_find") n, memoPutG_spec abSch p _ (hp.get "ab_put") n,
        ih,
    mkLam_spec p (hp.get "der_b") (hp.get "lam_find") (hp.get "lam_push") (hp.get "intern_lam")
        (hp.get "mk_lam") n]
  all_goals subst_vars
  all_goals (try simp only [LocEq] at *)
  all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval,
    Nat.reduceEqDiff, reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
  all_goals grind [lang_grind, arena_grind, asetK, arLamW, rbLamW, viewOK, tierW, idxW]

include hp in
theorem arForall_step (n : Nat) (ih : ArGoSpec p n) (s₀ : St) (h c d k fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ar_forall" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arForallW (n + 1) s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold ArGoSpec at ih
  rw [invoke_eq _ (hp.get "ar_forall")]
  simp only [callFn, arForall]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, evalE_tld, tld, evalE_cnt,
    tcntM, evalE_tierE, evalE_idxE,
    memoFindG_spec abSch p _ (hp.get "ab_find") n, memoPutG_spec abSch p _ (hp.get "ab_put") n,
        ih,
    mkForall_spec p (hp.get "der_b") (hp.get "forall_find") (hp.get "forall_push")
        (hp.get "intern_forall") (hp.get "mk_forall") n]
  all_goals subst_vars
  all_goals (try simp only [LocEq] at *)
  all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval,
    Nat.reduceEqDiff, reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
  all_goals grind [lang_grind, arena_grind, asetK, arForallW, rbForallW, viewOK, tierW, idxW]

include hp in
theorem arLet_step (n : Nat) (ih : ArGoSpec p n) (s₀ : St) (h c d k fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ar_let" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arLetW (n + 1) s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold ArGoSpec at ih
  rw [invoke_eq _ (hp.get "ar_let")]
  simp only [callFn, arLet]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, evalE_tld, tld, evalE_cnt,
    tcntM, evalE_tierE, evalE_idxE,
    memoFindG_spec abSch p _ (hp.get "ab_find") n, memoPutG_spec abSch p _ (hp.get "ab_put") n,
        ih,
    mkLet_spec p (hp.get "der_b") (hp.get "letE_find") (hp.get "letE_push")
        (hp.get "intern_letE") (hp.get "mk_let") n]
  all_goals subst_vars
  all_goals (try simp only [LocEq] at *)
  all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval,
    Nat.reduceEqDiff, reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
  all_goals grind [lang_grind, arena_grind, asetK, arLetW, rbLetW, viewOK, tierW, idxW]

include hp in
theorem arProj_step (n : Nat) (ih : ArGoSpec p n) (s₀ : St) (h c d k fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ar_proj" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arProjW (n + 1) s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold ArGoSpec at ih
  rw [invoke_eq _ (hp.get "ar_proj")]
  simp only [callFn, arProj]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, evalE_tld, tld, evalE_cnt,
    tcntM, evalE_tierE, evalE_idxE,
    memoFindG_spec abSch p _ (hp.get "ab_find") n, memoPutG_spec abSch p _ (hp.get "ab_put") n,
        ih,
    mkProj_spec p (hp.get "der_b") (hp.get "proj_find") (hp.get "proj_push")
        (hp.get "intern_proj") (hp.get "mk_proj") n]
  all_goals subst_vars
  all_goals (try simp only [LocEq] at *)
  all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval,
    Nat.reduceEqDiff, reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
  all_goals grind [lang_grind, arena_grind, asetK, arProjW, rbProjW, viewOK, tierW, idxW]

include hp in
/-- **`abs_go`, `ab_node` and the arms are their models**, at every fuel. -/
theorem arGo_spec (n : Nat) : ArGoSpec p n ∧ ArNodeSpec p n ∧ ArArmSpec p n := by
  induction n with
  | zero =>
    refine ⟨fun s₀ h c d k fu => ?_, fun s₀ h c d k fu => ?_,
      fun s₀ h c d k fu => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    first
    | (rw [invoke_eq _ (hp.get "ar_go")]; simp only [callFn, arGo]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ (hp.get "ar_node")]; simp only [callFn, arNode]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ (hp.get "ar_app")]; simp only [callFn, arApp]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ (hp.get "ar_lam")]; simp only [callFn, arLam]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ (hp.get "ar_forall")]; simp only [callFn, arForall]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ (hp.get "ar_let")]; simp only [callFn, arLet]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ (hp.get "ar_proj")]; simp only [callFn, arProj]; vcgen [exec] <;> grind)
  | succ n ih =>
    exact ⟨arGo_step p hp n ih.2.1, arNode_step p hp n ih.2.2, fun s₀ h c d k fu =>
      ⟨arApp_step p hp n ih.1 s₀ h c d k fu, arLam_step p hp n ih.1 s₀ h c d k fu,
        arForall_step p hp n ih.1 s₀ h c d k fu, arLet_step p hp n ih.1 s₀ h c d k fu,
        arProj_step p hp n ih.1 s₀ h c d k fu⟩⟩

end specs

/-! ## `ar_entry(e, d, k, c)`: `abstractRangeFast`

The walk's depth counter starts at `coreWalkFuel` (`4000000000`). -/

/-- **The model of `ar_entry`.** -/
def arEntryW (n : Nat) (m : Mem) (e d k c : Word) : Option (Word × Mem) :=
  if k = 0 then some (e &&& 4294967295, m)
  else if rdW (m.arr64 CTL) 48 + 2 = 0 then none
  else aclrK (arW n (mclearG abSch m) e c d k 4000000000)

theorem arEntryW_zero (n : Nat) (m : Mem) (e d k c : Word) (hk : k = 0) :
    arEntryW n m e d k c = some (e &&& 4294967295, m) := by simp [arEntryW, hk]

theorem arEntryW_eq (n : Nat) (m : Mem) (e d k c : Word) (hk : k ≠ 0)
    (h0 : rdW (m.arr64 CTL) 48 + 2 ≠ 0) :
    arEntryW n m e d k c = aclrK (arW n (mclearG abSch m) e c d k 4000000000) := by
  simp [arEntryW, hk, h0]

grind_pattern [arena_grind] arEntryW_zero => arEntryW n m e d k c
grind_pattern [arena_grind] arEntryW_eq => arEntryW n m e d k c

/-- con-ron: ConRon/Arena/ExprOps.lean:1874-1885 ConRon.Arena.abstractRangeFast -/
@[l_impl ConRon.Arena.abstractRangeFast]
def arEntry : FunDecl := lfn (e, d, k, c) locals (r, u) {
  if k == 0 { return e & 4294967295 };
  u := call ab_clear();
  r := call ar_go(e, c, d, k, 4000000000);
  u := call ab_clear();
  return r & 4294967295
}

theorem arEntry_spec (p : Prog) (hp : ArProg p) (he : p.lookup "ar_entry" = some arEntry)
    (n : Nat) (s₀ : St) (e d k c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "ar_entry" [e, d, k, c]
    ⦃fun r s' => LocEq s' s₀ ∧ arEntryW n s₀.mem e d k c = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (arGo_spec p hp n).1
  unfold ArGoSpec at ih
  rw [invoke_eq _ he]
  simp only [callFn, arEntry]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      memoClearG_spec abSch p _ (hp.get "ab_clear") n, ih] <;>
    finish

/-- The walk, `absProg` (its memo, `ab_fvb`, `fvarRangeProg`, `liftProg`), as one program. -/
def arProg : Prog := arWalkProg ++ [("ar_entry", arEntry)] ++ [("abs_entry", absEntry)]

end L.Arena
