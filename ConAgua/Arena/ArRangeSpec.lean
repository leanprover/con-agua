module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.ArRange
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.ArRange

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

/-- **`ar_go`, `ar_node` and the arms are their models.** -/
l_model arGo_spec (p : Prog) (hp : ArProg p)
  fns [hp.get "ar_go" ↦ arW, hp.get "ar_node" ↦ arNodeW, hp.get "ar_app" ↦ arAppW,
    hp.get "ar_lam" ↦ arLamW, hp.get "ar_forall" ↦ arForallW, hp.get "ar_let" ↦ arLetW,
    hp.get "ar_proj" ↦ arProjW]
  specs [abFvb_spec p hp.base n,
    internBVar_spec p (hp.get "bvar_find") (hp.get "bvar_push") (hp.get "intern_bvar") n,
    memoFindG_spec abSch p _ (hp.get "ab_find") n, memoPutG_spec abSch p _ (hp.get "ab_put") n,
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
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] gen 20

/-! ### The memo write of the generated continuations is `asetK` -/

theorem arAppW.j1_eq (h c r : Word) (m : Mem) : arAppW.j1 h c r m = asetK h c (some (r, m)) := by
  by_cases hf : mfindG abSch m h c = []
  · simp [arAppW.j1, asetK, msetG, hf]
  · rw [arAppW.j1.arm1 _ _ _ _ hf]
    simp only [asetK, msetG_eq _ _ _ _ _ hf]
    cases mputG abSch m h c r _ _ <;> rfl

theorem arAppW.k_mk_app_eq (h c : Word) (o : Option (Word × Mem)) :
    arAppW.k_mk_app h c o = asetK h c o := by
  cases o with
  | none => rfl
  | some q => obtain ⟨r, m⟩ := q; simp [arAppW.k_mk_app, arAppW.j1_eq]

theorem arAppW.k_ar_go_2.set (h c f a x y : Word) (m₂ : Mem) :
    arAppW.k_ar_go_2 h c f a x (some (y, m₂)) = asetK h c (rbAppW m₂ h f a x y) := by
  by_cases hc : x = f ∧ y = a
  · rw [arAppW.k_ar_go_2.arm1 _ _ _ _ _ _ _ hc, arAppW.j1_eq]; simp [rbAppW, hc]
  · rw [arAppW.k_ar_go_2.arm2 _ _ _ _ _ _ _ hc, arAppW.k_mk_app_eq]; simp [rbAppW, hc]

theorem arLamW.k_ar_go_2.set (h c f a x y : Word) (m₂ : Mem) :
    arLamW.k_ar_go_2 h c f a x (some (y, m₂)) = asetK h c (rbLamW m₂ h f a x y) := by
  by_cases hc : x = f ∧ y = a
  · rw [arLamW.k_ar_go_2.arm1 _ _ _ _ _ _ _ hc, arAppW.j1_eq]; simp [rbLamW, hc]
  · rw [arLamW.k_ar_go_2.arm2 _ _ _ _ _ _ _ hc, arAppW.k_mk_app_eq]; simp [rbLamW, hc]

theorem arForallW.k_ar_go_2.set (h c f a x y : Word) (m₂ : Mem) :
    arForallW.k_ar_go_2 h c f a x (some (y, m₂)) = asetK h c (rbForallW m₂ h f a x y) := by
  by_cases hc : x = f ∧ y = a
  · rw [arForallW.k_ar_go_2.arm1 _ _ _ _ _ _ _ hc, arAppW.j1_eq]; simp [rbForallW, hc]
  · rw [arForallW.k_ar_go_2.arm2 _ _ _ _ _ _ _ hc, arAppW.k_mk_app_eq]; simp [rbForallW, hc]

theorem arLetW.k_ar_go_3.set (h c f a b x y z : Word) (m₃ : Mem) :
    arLetW.k_ar_go_3 h c f a b x y (some (z, m₃)) = asetK h c (rbLetW m₃ h f a b x y z) := by
  by_cases hc : x = f ∧ y = a ∧ z = b
  · rw [arLetW.k_ar_go_3.arm1 _ _ _ _ _ _ _ _ _ hc, arAppW.j1_eq]; simp [rbLetW, hc]
  · rw [arLetW.k_ar_go_3.arm2 _ _ _ _ _ _ _ _ _ hc, arAppW.k_mk_app_eq]; simp [rbLetW, hc]

theorem arProjW.k_ar_go.set (h c nm ix e x : Word) (m₁ : Mem) :
    arProjW.k_ar_go h c nm ix e (some (x, m₁)) = asetK h c (rbProjW m₁ h nm ix e x) := by
  by_cases hc : x = e
  · rw [arProjW.k_ar_go.arm1 _ _ _ _ _ _ _ hc, arAppW.j1_eq]; simp [rbProjW, hc]
  · rw [arProjW.k_ar_go.arm2 _ _ _ _ _ _ _ hc, arAppW.k_mk_app_eq]; simp [rbProjW, hc]

theorem arW.k_ab_fvb.ite (n : Nat) (h c d k fu x : Word) (m₁ : Mem) :
    arW.k_ab_fvb n h c d k fu (some (x, m₁)) =
      if x ≤ d then some (h, m₁) else arNodeW n m₁ h c d k (fu - 1) := by
  by_cases hc : x ≤ d
  · rw [arW.k_ab_fvb.arm1 _ _ _ _ _ _ _ _ hc, ite_eq_left hc]
  · rw [arW.k_ab_fvb.arm2 _ _ _ _ _ _ _ _ hc, ite_eq_right hc]


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

/-- con-ron: ConRon/Arena/ExprOps.lean:1905-1916 ConRon.Arena.abstractRangeFast -/
@[no_expose, l_impl ConRon.Arena.abstractRangeFast]
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
  rw [invoke_eq _ he]
  simp only [callFn, arEntry]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      memoClearG_spec abSch p _ (hp.get "ab_clear") n, ih] <;>
    finish

/-- The walk, `absProg` (its memo, `ab_fvb`, `fvarRangeProg`, `liftProg`), as one program. -/
def arProg : Prog := arWalkProg ++ [("ar_entry", arEntry)] ++ [("abs_entry", absEntry)]

end L.Arena
