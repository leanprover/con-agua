module

public import ConAgua.Arena.InstList
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr

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

section specs
variable (p : Prog) (hp : InstListProg p)

set_option maxHeartbeats 1000000 in
include hp in
theorem ilApp_step (n : Nat) (ih : IlGoSpec p n) (s₀ : St) (h d o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "il_app" [h, d, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ilAppW (n + 1) s₀.mem h d o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold IlGoSpec at ih
  rw [invoke_eq _ hp.app]
  simp only [callFn, ilApp]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      ih,
      mkApp_spec p hp.base.derb hp.base.appf hp.base.appp hp.base.appi hp.base.mkapp n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem ilLam_step (n : Nat) (ih : IlGoSpec p n) (s₀ : St) (h d o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "il_lam" [h, d, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ilLamW (n + 1) s₀.mem h d o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold IlGoSpec at ih
  rw [invoke_eq _ hp.lam]
  simp only [callFn, ilLam]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      ih,
      mkLam_spec p hp.base.derb hp.base.lamf hp.base.lamp hp.base.lami hp.base.mklam n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem ilForall_step (n : Nat) (ih : IlGoSpec p n) (s₀ : St) (h d o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "il_forall" [h, d, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ilForallW (n + 1) s₀.mem h d o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold IlGoSpec at ih
  rw [invoke_eq _ hp.fa]
  simp only [callFn, ilForall]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      ih,
      mkForall_spec p hp.base.derb hp.base.faf hp.base.fap hp.base.fai hp.base.mkfa n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem ilLet_step (n : Nat) (ih : IlGoSpec p n) (s₀ : St) (h d o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "il_let" [h, d, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ilLetW (n + 1) s₀.mem h d o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold IlGoSpec at ih
  rw [invoke_eq _ hp.le]
  simp only [callFn, ilLet]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      ih,
      mkLet_spec p hp.base.derb hp.base.lef hp.base.lep hp.base.lei hp.base.mklet n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem ilProj_step (n : Nat) (ih : IlGoSpec p n) (s₀ : St) (h d o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "il_proj" [h, d, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ilProjW (n + 1) s₀.mem h d o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold IlGoSpec at ih
  rw [invoke_eq _ hp.pj]
  simp only [callFn, ilProj]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      ih,
      mkProj_spec p hp.base.derb hp.base.pjf hp.base.pjp hp.base.pji hp.base.mkpj n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem ilBVar_step (n : Nat) (ih : IlGoSpec p n) (s₀ : St) (h d o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "il_bvar" [h, d, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ilBVarW (n + 1) s₀.mem h d o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold IlGoSpec at ih
  rw [invoke_eq _ hp.bv]
  simp only [callFn, ilBVar]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      ih,
      derB_spec p hp.base.derb n, internBVar_spec p hp.base.bvf hp.base.bvp hp.base.bvi n] <;>
    finish (gen := 20) [viewOK, tierW, idxW, slW]

set_option maxHeartbeats 1000000 in
include hp in
theorem ilgApp_step (n : Nat) (ih : IlgGoSpec p n) (s₀ : St) (h d o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ilg_app" [h, d, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ilgAppW (n + 1) s₀.mem h d o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold IlgGoSpec at ih
  rw [invoke_eq _ hp.gapp]
  simp only [callFn, ilgApp]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec ilSch p _ hp.ilf n, memoPutG_spec ilSch p _ hp.ilp n, ih,
      mkApp_spec p hp.base.derb hp.base.appf hp.base.appp hp.base.appi hp.base.mkapp n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem ilgLam_step (n : Nat) (ih : IlgGoSpec p n) (s₀ : St) (h d o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ilg_lam" [h, d, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ilgLamW (n + 1) s₀.mem h d o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold IlgGoSpec at ih
  rw [invoke_eq _ hp.glam]
  simp only [callFn, ilgLam]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec ilSch p _ hp.ilf n, memoPutG_spec ilSch p _ hp.ilp n, ih,
      mkLam_spec p hp.base.derb hp.base.lamf hp.base.lamp hp.base.lami hp.base.mklam n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem ilgForall_step (n : Nat) (ih : IlgGoSpec p n) (s₀ : St) (h d o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ilg_forall" [h, d, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ilgForallW (n + 1) s₀.mem h d o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold IlgGoSpec at ih
  rw [invoke_eq _ hp.gfa]
  simp only [callFn, ilgForall]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec ilSch p _ hp.ilf n, memoPutG_spec ilSch p _ hp.ilp n, ih,
      mkForall_spec p hp.base.derb hp.base.faf hp.base.fap hp.base.fai hp.base.mkfa n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem ilgLet_step (n : Nat) (ih : IlgGoSpec p n) (s₀ : St) (h d o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ilg_let" [h, d, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ilgLetW (n + 1) s₀.mem h d o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold IlgGoSpec at ih
  rw [invoke_eq _ hp.gle]
  simp only [callFn, ilgLet]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec ilSch p _ hp.ilf n, memoPutG_spec ilSch p _ hp.ilp n, ih,
      mkLet_spec p hp.base.derb hp.base.lef hp.base.lep hp.base.lei hp.base.mklet n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

set_option maxHeartbeats 1000000 in
include hp in
theorem ilgProj_step (n : Nat) (ih : IlgGoSpec p n) (s₀ : St) (h d o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ilg_proj" [h, d, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ilgProjW (n + 1) s₀.mem h d o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold IlgGoSpec at ih
  rw [invoke_eq _ hp.gpj]
  simp only [callFn, ilgProj]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec ilSch p _ hp.ilf n, memoPutG_spec ilSch p _ hp.ilp n, ih,
      mkProj_spec p hp.base.derb hp.base.pjf hp.base.pjp hp.base.pji hp.base.mkpj n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

include hp in
/-- **Both walks and their arms are their models**, at every fuel. -/
theorem instList_spec (n : Nat) :
    IlGoSpec p n ∧ IlArmSpec p n ∧ IlgGoSpec p n ∧ IlgArmSpec p n := by
  induction n with
  | zero =>
    refine ⟨fun s₀ h d o l => ?_, fun s₀ h d o l => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
      fun s₀ h d o l => ?_, fun s₀ h d o l => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    first
    | (rw [invoke_eq _ hp.go]; simp only [callFn, ilGo]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.app]; simp only [callFn, ilApp]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.lam]; simp only [callFn, ilLam]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.fa]; simp only [callFn, ilForall]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.le]; simp only [callFn, ilLet]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.pj]; simp only [callFn, ilProj]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.bv]; simp only [callFn, ilBVar]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.ggo]; simp only [callFn, ilgGo]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.gapp]; simp only [callFn, ilgApp]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.glam]; simp only [callFn, ilgLam]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.gfa]; simp only [callFn, ilgForall]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.gle]; simp only [callFn, ilgLet]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.gpj]; simp only [callFn, ilgProj]; vcgen [exec] <;> grind)
  | succ n ih =>
    obtain ⟨ihG, ihA, ihGG, ihGA⟩ := ih
    exact ⟨ilGo_step p hp n ihA, fun s₀ h d o l =>
      ⟨ilApp_step p hp n ihG s₀ h d o l, ilLam_step p hp n ihG s₀ h d o l,
        ilForall_step p hp n ihG s₀ h d o l, ilLet_step p hp n ihG s₀ h d o l,
        ilProj_step p hp n ihG s₀ h d o l, ilBVar_step p hp n ihG s₀ h d o l⟩,
      ilgGo_step p hp n ihGA ihG, fun s₀ h d o l =>
      ⟨ilgApp_step p hp n ihGG s₀ h d o l, ilgLam_step p hp n ihGG s₀ h d o l,
        ilgForall_step p hp n ihGG s₀ h d o l, ilgLet_step p hp n ihGG s₀ h d o l,
        ilgProj_step p hp n ihGG s₀ h d o l⟩⟩

end specs

/-! ## `inst_list(e, o, l, d)`: `instantiateListFast`, between two clears -/

/-- After the walk: clear the memo again. -/
def ilclrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => if rdW (m₁.arr64 CTL) 50 + 2 = 0 then none else some (r, mclearG ilSch m₁)

/-- **The model of `inst_list`.** -/
def instListW (n : Nat) (m : Mem) (e o l d : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 50 + 2 = 0 then none else ilclrK (ilgW n (mclearG ilSch m) e d o l)

theorem instListW_eq (n : Nat) (m : Mem) (e o l d : Word) (h0 : rdW (m.arr64 CTL) 50 + 2 ≠ 0) :
    instListW n m e o l d = ilclrK (ilgW n (mclearG ilSch m) e d o l) := by
  simp [instListW, h0]

theorem ilclrK_some (r : Word) (m₁ : Mem) (h0 : rdW (m₁.arr64 CTL) 50 + 2 ≠ 0) :
    ilclrK (some (r, m₁)) = some (r, mclearG ilSch m₁) := by simp [ilclrK, h0]

grind_pattern [arena_grind] instListW_eq => instListW n m e o l d
grind_pattern [arena_grind] ilclrK_some => ilclrK (some (r, m₁))

/-- con-ron: ConRon/Arena/ExprOps.lean:642-649 ConRon.Arena.instantiateListFast -/
@[l_impl ConRon.Arena.instantiateListFast]
def instListL : FunDecl := lfn (e, o, l, d) locals (r, u) {
  u := call ilm_clear();
  r := call ilg_go(e, d, o, l);
  u := call ilm_clear();
  return r
}

theorem instList_spec' (p : Prog) (hp : InstListProg p) (he : p.lookup "inst_list" = some instListL)
    (n : Nat) (s₀ : St) (e o l d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "inst_list" [e, o, l, d]
    ⦃fun r s' => LocEq s' s₀ ∧ instListW n s₀.mem e o l d = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (instList_spec p hp n).2.2.1
  unfold IlgGoSpec at ih
  rw [invoke_eq _ he]
  simp only [callFn, instListL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec ilSch p _ hp.ilc n,
      ih] <;>
    finish

/-- Both walks, their memo and `liftProg` (the `mk_*`, the stores), as one program. -/
def instListProg : Prog :=
  [("ilm_find", memoFindG ilSch), ("ilm_put", memoPutG ilSch), ("ilm_clear", memoClearG ilSch),
    ("il_go", ilGo), ("il_app", ilApp), ("il_lam", ilLam), ("il_forall", ilForall),
    ("il_let", ilLet), ("il_proj", ilProj), ("il_bvar", ilBVar), ("ilg_go", ilgGo),
    ("ilg_app", ilgApp), ("ilg_lam", ilgLam), ("ilg_forall", ilgForall), ("ilg_let", ilgLet),
    ("ilg_proj", ilgProj), ("inst_list", instListL)] ++ liftProg

theorem instListProg_ok : InstListProg instListProg := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  constructor <;> rfl

end L.Arena
