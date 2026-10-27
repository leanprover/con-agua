module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.Abs1
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The specs of `abstract1`'s arms, and the entry

As `Inst1Spec.lean`: the five arms' steps, the induction on the fuel (`absGo_spec`), the entry
`abs_entry` (`abstract1Fast`) and the program `absProg`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

section specs
variable (p : Prog) (hp : AbsProg p)

set_option maxHeartbeats 1000000 in
include hp in
theorem absApp_step (n : Nat) (ih : AbsGoSpec p n) (s₀ : St) (h k d fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "abs_app" [h, k, d, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ absAppW (n + 1) s₀.mem h k d fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold AbsGoSpec at ih
  rw [invoke_eq _ (hp.get "abs_app")]
  simp only [callFn, absApp]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      memoFindG_spec abSch p _ (hp.get "ab_find") n, memoPutG_spec abSch p _ (hp.get "ab_put") n,
          ih,
      mkApp_spec p (hp.get "der_b") (hp.get "app_find") (hp.get "app_push") (hp.get "intern_app")
          (hp.get "mk_app") n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem absLam_step (n : Nat) (ih : AbsGoSpec p n) (s₀ : St) (h k d fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "abs_lam" [h, k, d, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ absLamW (n + 1) s₀.mem h k d fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold AbsGoSpec at ih
  rw [invoke_eq _ (hp.get "abs_lam")]
  simp only [callFn, absLam]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      memoFindG_spec abSch p _ (hp.get "ab_find") n, memoPutG_spec abSch p _ (hp.get "ab_put") n,
          ih,
      mkLam_spec p (hp.get "der_b") (hp.get "lam_find") (hp.get "lam_push") (hp.get "intern_lam")
          (hp.get "mk_lam") n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem absForall_step (n : Nat) (ih : AbsGoSpec p n) (s₀ : St) (h k d fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "abs_forall" [h, k, d, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ absForallW (n + 1) s₀.mem h k d fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold AbsGoSpec at ih
  rw [invoke_eq _ (hp.get "abs_forall")]
  simp only [callFn, absForall]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      memoFindG_spec abSch p _ (hp.get "ab_find") n, memoPutG_spec abSch p _ (hp.get "ab_put") n,
          ih,
      mkForall_spec p (hp.get "der_b") (hp.get "forall_find") (hp.get "forall_push")
          (hp.get "intern_forall") (hp.get "mk_forall") n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem absLet_step (n : Nat) (ih : AbsGoSpec p n) (s₀ : St) (h k d fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "abs_let" [h, k, d, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ absLetW (n + 1) s₀.mem h k d fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold AbsGoSpec at ih
  rw [invoke_eq _ (hp.get "abs_let")]
  simp only [callFn, absLet]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      memoFindG_spec abSch p _ (hp.get "ab_find") n, memoPutG_spec abSch p _ (hp.get "ab_put") n,
          ih,
      mkLet_spec p (hp.get "der_b") (hp.get "letE_find") (hp.get "letE_push")
          (hp.get "intern_letE") (hp.get "mk_let") n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem absProj_step (n : Nat) (ih : AbsGoSpec p n) (s₀ : St) (h k d fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "abs_proj" [h, k, d, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ absProjW (n + 1) s₀.mem h k d fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold AbsGoSpec at ih
  rw [invoke_eq _ (hp.get "abs_proj")]
  simp only [callFn, absProj]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      memoFindG_spec abSch p _ (hp.get "ab_find") n, memoPutG_spec abSch p _ (hp.get "ab_put") n,
          ih,
      mkProj_spec p (hp.get "der_b") (hp.get "proj_find") (hp.get "proj_push")
          (hp.get "intern_proj") (hp.get "mk_proj") n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

include hp in
/-- **`abs_go`, `ab_node` and the arms are their models**, at every fuel. -/
theorem absGo_spec (n : Nat) : AbsGoSpec p n ∧ AbsNodeSpec p n ∧ AbsArmSpec p n := by
  induction n with
  | zero =>
    refine ⟨fun s₀ h k d fu => ?_, fun s₀ h k d fu => ?_, fun s₀ h k d fu => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    first
    | (rw [invoke_eq _ (hp.get "abs_go")]; simp only [callFn, absGo]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ (hp.get "ab_node")]; simp only [callFn, absNode]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ (hp.get "abs_app")]; simp only [callFn, absApp]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ (hp.get "abs_lam")]; simp only [callFn, absLam]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ (hp.get "abs_forall")]; simp only [callFn,
        absForall]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ (hp.get "abs_let")]; simp only [callFn, absLet]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ (hp.get "abs_proj")]; simp only [callFn, absProj]; vcgen [exec] <;> grind)
  | succ n ih =>
    exact ⟨absGo_step p hp n ih.2.1, absNode_step p hp n ih.2.2, fun s₀ h k d fu =>
      ⟨absApp_step p hp n ih.1 s₀ h k d fu, absLam_step p hp n ih.1 s₀ h k d fu,
        absForall_step p hp n ih.1 s₀ h k d fu, absLet_step p hp n ih.1 s₀ h k d fu,
        absProj_step p hp n ih.1 s₀ h k d fu⟩⟩

end specs

/-! ## `abs_entry(e, d, k)`: `abstract1Fast`, between two clears

The walk's depth counter starts at `coreWalkFuel` (`4000000000`, `ConRon/Arena/Core.lean`): the
core calls `abstract1Fast coreWalkFuel`. -/

/-- After the walk: clear the memo again; the handle word is returned masked to 32 bits (the
callers' contract `HW`; `decE` reads the same handle). -/
def aclrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) =>
    if rdW (m₁.arr64 CTL) 48 + 2 = 0 then none else some (r &&& 4294967295, mclearG abSch m₁)

/-- **The model of `abs_entry`.** -/
def absEntryW (n : Nat) (m : Mem) (e d k : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 48 + 2 = 0 then none else aclrK (absW n (mclearG abSch m) e k d 4000000000)

theorem absEntryW_eq (n : Nat) (m : Mem) (e d k : Word) (h0 : rdW (m.arr64 CTL) 48 + 2 ≠ 0) :
    absEntryW n m e d k = aclrK (absW n (mclearG abSch m) e k d 4000000000) := by
  simp [absEntryW, h0]

theorem aclrK_some (r : Word) (m₁ : Mem) (h0 : rdW (m₁.arr64 CTL) 48 + 2 ≠ 0) :
    aclrK (some (r, m₁)) = some (r &&& 4294967295, mclearG abSch m₁) := by simp [aclrK, h0]

grind_pattern [arena_grind] absEntryW_eq => absEntryW n m e d k
grind_pattern [arena_grind] aclrK_some => aclrK (some (r, m₁))

/-- con-ron: ConRon/Arena/ExprOps.lean:1719-1725 ConRon.Arena.abstract1Fast -/
@[l_impl ConRon.Arena.abstract1Fast]
def absEntry : FunDecl := lfn (e, d, k) locals (r, u) {
  u := call ab_clear();
  r := call abs_go(e, k, d, 4000000000);
  u := call ab_clear();
  return r & 4294967295
}

theorem absEntry_spec (p : Prog) (hp : AbsProg p) (he : p.lookup "abs_entry" = some absEntry)
    (n : Nat) (s₀ : St) (e d k : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "abs_entry" [e, d, k]
    ⦃fun r s' => LocEq s' s₀ ∧ absEntryW n s₀.mem e d k = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (absGo_spec p hp n).1
  unfold AbsGoSpec at ih
  rw [invoke_eq _ he]
  simp only [callFn, absEntry]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec abSch p _
        (hp.get "ab_clear") n,
      ih] <;>
    finish

/-- The walk, its memo, `fvarRangeProg` and `liftProg` (the `mk_*`, the stores), as one program. -/
def absProg : Prog := absWalkProg ++ [("abs_entry", absEntry)]

theorem absProg_ok : AbsProg absProg := (ProgHas.refl _).left

end L.Arena
