module

public import ConAgua.Arena.Abs1
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr

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
theorem absApp_step (n : Nat) (ih : AbsGoSpec p n) (s₀ : St) (h k d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "abs_app" [h, k, d]
    ⦃fun r s' => LocEq s' s₀ ∧ absAppW (n + 1) s₀.mem h k d = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold AbsGoSpec at ih
  rw [invoke_eq _ hp.app]
  simp only [callFn, absApp]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec abSch p _ hp.abf n, memoPutG_spec abSch p _ hp.abp n, ih,
      mkApp_spec p hp.base.derb hp.base.appf hp.base.appp hp.base.appi hp.base.mkapp n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem absLam_step (n : Nat) (ih : AbsGoSpec p n) (s₀ : St) (h k d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "abs_lam" [h, k, d]
    ⦃fun r s' => LocEq s' s₀ ∧ absLamW (n + 1) s₀.mem h k d = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold AbsGoSpec at ih
  rw [invoke_eq _ hp.lam]
  simp only [callFn, absLam]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec abSch p _ hp.abf n, memoPutG_spec abSch p _ hp.abp n, ih,
      mkLam_spec p hp.base.derb hp.base.lamf hp.base.lamp hp.base.lami hp.base.mklam n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem absForall_step (n : Nat) (ih : AbsGoSpec p n) (s₀ : St) (h k d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "abs_forall" [h, k, d]
    ⦃fun r s' => LocEq s' s₀ ∧ absForallW (n + 1) s₀.mem h k d = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold AbsGoSpec at ih
  rw [invoke_eq _ hp.fa]
  simp only [callFn, absForall]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec abSch p _ hp.abf n, memoPutG_spec abSch p _ hp.abp n, ih,
      mkForall_spec p hp.base.derb hp.base.faf hp.base.fap hp.base.fai hp.base.mkfa n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem absLet_step (n : Nat) (ih : AbsGoSpec p n) (s₀ : St) (h k d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "abs_let" [h, k, d]
    ⦃fun r s' => LocEq s' s₀ ∧ absLetW (n + 1) s₀.mem h k d = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold AbsGoSpec at ih
  rw [invoke_eq _ hp.le]
  simp only [callFn, absLet]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec abSch p _ hp.abf n, memoPutG_spec abSch p _ hp.abp n, ih,
      mkLet_spec p hp.base.derb hp.base.lef hp.base.lep hp.base.lei hp.base.mklet n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem absProj_step (n : Nat) (ih : AbsGoSpec p n) (s₀ : St) (h k d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "abs_proj" [h, k, d]
    ⦃fun r s' => LocEq s' s₀ ∧ absProjW (n + 1) s₀.mem h k d = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold AbsGoSpec at ih
  rw [invoke_eq _ hp.pj]
  simp only [callFn, absProj]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec abSch p _ hp.abf n, memoPutG_spec abSch p _ hp.abp n, ih,
      mkProj_spec p hp.base.derb hp.base.pjf hp.base.pjp hp.base.pji hp.base.mkpj n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

include hp in
/-- **`abs_go`, `ab_node` and the arms are their models**, at every fuel. -/
theorem absGo_spec (n : Nat) : AbsGoSpec p n ∧ AbsNodeSpec p n ∧ AbsArmSpec p n := by
  induction n with
  | zero =>
    refine ⟨fun s₀ h k d => ?_, fun s₀ h k d => ?_, fun s₀ h k d => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    first
    | (rw [invoke_eq _ hp.go]; simp only [callFn, absGo]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.node]; simp only [callFn, absNode]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.app]; simp only [callFn, absApp]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.lam]; simp only [callFn, absLam]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.fa]; simp only [callFn, absForall]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.le]; simp only [callFn, absLet]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.pj]; simp only [callFn, absProj]; vcgen [exec] <;> grind)
  | succ n ih =>
    exact ⟨absGo_step p hp n ih.2.1, absNode_step p hp n ih.2.2, fun s₀ h k d =>
      ⟨absApp_step p hp n ih.1 s₀ h k d, absLam_step p hp n ih.1 s₀ h k d,
        absForall_step p hp n ih.1 s₀ h k d, absLet_step p hp n ih.1 s₀ h k d,
        absProj_step p hp n ih.1 s₀ h k d⟩⟩

end specs

/-! ## `abs_entry(e, d, k)`: `abstract1Fast`, between two clears -/

/-- After the walk: clear the memo again. -/
def aclrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => if rdW (m₁.arr64 CTL) 48 + 2 = 0 then none else some (r, mclearG abSch m₁)

/-- **The model of `abs_entry`.** -/
def absEntryW (n : Nat) (m : Mem) (e d k : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 48 + 2 = 0 then none else aclrK (absW n (mclearG abSch m) e k d)

theorem absEntryW_eq (n : Nat) (m : Mem) (e d k : Word) (h0 : rdW (m.arr64 CTL) 48 + 2 ≠ 0) :
    absEntryW n m e d k = aclrK (absW n (mclearG abSch m) e k d) := by
  simp [absEntryW, h0]

theorem aclrK_some (r : Word) (m₁ : Mem) (h0 : rdW (m₁.arr64 CTL) 48 + 2 ≠ 0) :
    aclrK (some (r, m₁)) = some (r, mclearG abSch m₁) := by simp [aclrK, h0]

grind_pattern [arena_grind] absEntryW_eq => absEntryW n m e d k
grind_pattern [arena_grind] aclrK_some => aclrK (some (r, m₁))

/-- con-ron: ConRon/Arena/ExprOps.lean:1718-1724 ConRon.Arena.abstract1Fast -/
@[l_impl ConRon.Arena.abstract1Fast]
def absEntry : FunDecl := lfn (e, d, k) locals (r, u) {
  u := call ab_clear();
  r := call abs_go(e, k, d);
  u := call ab_clear();
  return r
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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec abSch p _ hp.abc n,
      ih] <;>
    finish

/-- The walk, its memo, `fvarRangeProg` and `liftProg` (the `mk_*`, the stores), as one program. -/
def absProg : Prog :=
  [("ab_find", memoFindG abSch), ("ab_put", memoPutG abSch), ("ab_clear", memoClearG abSch),
    ("ab_fvb", abFvb), ("abs_go", absGo), ("ab_node", absNode), ("abs_app", absApp),
    ("abs_lam", absLam), ("abs_forall", absForall), ("abs_let", absLet), ("abs_proj", absProj),
    ("abs_entry", absEntry)] ++ fvarRangeProg ++ liftProg

theorem absProg_ok : AbsProg absProg := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  constructor <;> rfl

end L.Arena
