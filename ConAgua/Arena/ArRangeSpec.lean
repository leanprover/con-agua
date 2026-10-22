module

public import ConAgua.Arena.ArRange
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr

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

set_option maxHeartbeats 1000000 in
include hp in
theorem arApp_step (n : Nat) (ih : ArGoSpec p n) (s₀ : St) (h c d k fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ar_app" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arAppW (n + 1) s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold ArGoSpec at ih
  rw [invoke_eq _ hp.app]
  simp only [callFn, arApp]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec abSch p _ hp.base.abf n, memoPutG_spec abSch p _ hp.base.abp n, ih,
      mkApp_spec p hp.base.base.derb hp.base.base.appf hp.base.base.appp hp.base.base.appi hp.base.base.mkapp n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem arLam_step (n : Nat) (ih : ArGoSpec p n) (s₀ : St) (h c d k fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ar_lam" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arLamW (n + 1) s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold ArGoSpec at ih
  rw [invoke_eq _ hp.lam]
  simp only [callFn, arLam]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec abSch p _ hp.base.abf n, memoPutG_spec abSch p _ hp.base.abp n, ih,
      mkLam_spec p hp.base.base.derb hp.base.base.lamf hp.base.base.lamp hp.base.base.lami hp.base.base.mklam n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem arForall_step (n : Nat) (ih : ArGoSpec p n) (s₀ : St) (h c d k fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ar_forall" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arForallW (n + 1) s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold ArGoSpec at ih
  rw [invoke_eq _ hp.fa]
  simp only [callFn, arForall]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec abSch p _ hp.base.abf n, memoPutG_spec abSch p _ hp.base.abp n, ih,
      mkForall_spec p hp.base.base.derb hp.base.base.faf hp.base.base.fap hp.base.base.fai hp.base.base.mkfa n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem arLet_step (n : Nat) (ih : ArGoSpec p n) (s₀ : St) (h c d k fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ar_let" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arLetW (n + 1) s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold ArGoSpec at ih
  rw [invoke_eq _ hp.le]
  simp only [callFn, arLet]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec abSch p _ hp.base.abf n, memoPutG_spec abSch p _ hp.base.abp n, ih,
      mkLet_spec p hp.base.base.derb hp.base.base.lef hp.base.base.lep hp.base.base.lei hp.base.base.mklet n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem arProj_step (n : Nat) (ih : ArGoSpec p n) (s₀ : St) (h c d k fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ar_proj" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arProjW (n + 1) s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold ArGoSpec at ih
  rw [invoke_eq _ hp.pj]
  simp only [callFn, arProj]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec abSch p _ hp.base.abf n, memoPutG_spec abSch p _ hp.base.abp n, ih,
      mkProj_spec p hp.base.base.derb hp.base.base.pjf hp.base.base.pjp hp.base.base.pji hp.base.base.mkpj n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

include hp in
/-- **`abs_go`, `ab_node` and the arms are their models**, at every fuel. -/
theorem arGo_spec (n : Nat) : ArGoSpec p n ∧ ArNodeSpec p n ∧ ArArmSpec p n := by
  induction n with
  | zero =>
    refine ⟨fun s₀ h c d k fu => ?_, fun s₀ h c d k fu => ?_,
      fun s₀ h c d k fu => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    first
    | (rw [invoke_eq _ hp.go]; simp only [callFn, arGo]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.node]; simp only [callFn, arNode]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.app]; simp only [callFn, arApp]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.lam]; simp only [callFn, arLam]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.fa]; simp only [callFn, arForall]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.le]; simp only [callFn, arLet]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.pj]; simp only [callFn, arProj]; vcgen [exec] <;> grind)
  | succ n ih =>
    exact ⟨arGo_step p hp n ih.2.1, arNode_step p hp n ih.2.2, fun s₀ h c d k fu =>
      ⟨arApp_step p hp n ih.1 s₀ h c d k fu, arLam_step p hp n ih.1 s₀ h c d k fu,
        arForall_step p hp n ih.1 s₀ h c d k fu, arLet_step p hp n ih.1 s₀ h c d k fu,
        arProj_step p hp n ih.1 s₀ h c d k fu⟩⟩

end specs

/-! ## `ar_entry(e, d, k, c)`: `abstractRangeFast`

The walk's depth counter starts at `coreWalkFuel` (`4000000000`, ROADMAP §3 (b)). -/

/-- **The model of `ar_entry`.** -/
def arEntryW (n : Nat) (m : Mem) (e d k c : Word) : Option (Word × Mem) :=
  if k = 0 then some (e, m)
  else if rdW (m.arr64 CTL) 48 + 2 = 0 then none
  else aclrK (arW n (mclearG abSch m) e c d k 4000000000)

theorem arEntryW_zero (n : Nat) (m : Mem) (e d k c : Word) (hk : k = 0) :
    arEntryW n m e d k c = some (e, m) := by simp [arEntryW, hk]

theorem arEntryW_eq (n : Nat) (m : Mem) (e d k c : Word) (hk : k ≠ 0)
    (h0 : rdW (m.arr64 CTL) 48 + 2 ≠ 0) :
    arEntryW n m e d k c = aclrK (arW n (mclearG abSch m) e c d k 4000000000) := by
  simp [arEntryW, hk, h0]

grind_pattern [arena_grind] arEntryW_zero => arEntryW n m e d k c
grind_pattern [arena_grind] arEntryW_eq => arEntryW n m e d k c

/-- con-ron: ConRon/Arena/ExprOps.lean:1874-1885 ConRon.Arena.abstractRangeFast -/
@[l_impl ConRon.Arena.abstractRangeFast]
def arEntry : FunDecl := lfn (e, d, k, c) locals (r, u) {
  if k == 0 { return e };
  u := call ab_clear();
  r := call ar_go(e, c, d, k, 4000000000);
  u := call ab_clear();
  return r
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
      memoClearG_spec abSch p _ hp.base.abc n, ih] <;>
    finish

/-- The walk, `absProg` (its memo, `ab_fvb`, `fvarRangeProg`, `liftProg`), as one program. -/
def arProg : Prog :=
  [("ar_go", arGo), ("ar_node", arNode), ("ar_app", arApp), ("ar_lam", arLam),
    ("ar_forall", arForall), ("ar_let", arLet), ("ar_proj", arProj), ("ar_entry", arEntry)] ++
  absProg

theorem arProg_ok : ArProg arProg := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  constructor <;> rfl

end L.Arena
