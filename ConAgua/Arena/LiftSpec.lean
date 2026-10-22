module

public import ConAgua.Arena.Lift
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr

@[expose] public section

/-!
# The specs of `liftLooseBVars`' arms, and the entry

`Lift.lean` has the L code, the models and `lift_go`'s step; here the five arms' steps (one
`vcgen` + `finish` each), the induction on the fuel (`liftGo_spec`), the entry `lift_entry`
(`liftLooseBVarsFast`) and the program `liftProg`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

section specs
variable (p : Prog) (hp : LiftProg p)

include hp in
theorem liftApp_step (n : Nat) (ih : LiftGoSpec p n) (s₀ : St) (h c k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lift_app" [h, c, k]
    ⦃fun r s' => LocEq s' s₀ ∧ liftAppW (n + 1) s₀.mem h c k = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold LiftGoSpec at ih
  rw [invoke_eq _ hp.app]
  simp only [callFn, liftApp]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec lfSch p _ hp.lff n, memoPutG_spec lfSch p _ hp.lfp n, ih,
      mkApp_spec p hp.derb hp.derf hp.appf hp.appp hp.appi hp.mkapp n] <;>
    finish (gen := 20) [tierW, idxW]

include hp in
theorem liftLam_step (n : Nat) (ih : LiftGoSpec p n) (s₀ : St) (h c k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lift_lam" [h, c, k]
    ⦃fun r s' => LocEq s' s₀ ∧ liftLamW (n + 1) s₀.mem h c k = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold LiftGoSpec at ih
  rw [invoke_eq _ hp.lam]
  simp only [callFn, liftLam]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec lfSch p _ hp.lff n, memoPutG_spec lfSch p _ hp.lfp n, ih,
      mkLam_spec p hp.derb hp.derf hp.lamf hp.lamp hp.lami hp.mklam n] <;>
    finish (gen := 20) [tierW, idxW]

include hp in
theorem liftForall_step (n : Nat) (ih : LiftGoSpec p n) (s₀ : St) (h c k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lift_forall" [h, c, k]
    ⦃fun r s' => LocEq s' s₀ ∧ liftForallW (n + 1) s₀.mem h c k = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold LiftGoSpec at ih
  rw [invoke_eq _ hp.fa]
  simp only [callFn, liftForall]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec lfSch p _ hp.lff n, memoPutG_spec lfSch p _ hp.lfp n, ih,
      mkForall_spec p hp.derb hp.derf hp.faf hp.fap hp.fai hp.mkfa n] <;>
    finish (gen := 20) [tierW, idxW]

include hp in
theorem liftLet_step (n : Nat) (ih : LiftGoSpec p n) (s₀ : St) (h c k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lift_let" [h, c, k]
    ⦃fun r s' => LocEq s' s₀ ∧ liftLetW (n + 1) s₀.mem h c k = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold LiftGoSpec at ih
  rw [invoke_eq _ hp.le]
  simp only [callFn, liftLet]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec lfSch p _ hp.lff n, memoPutG_spec lfSch p _ hp.lfp n, ih,
      mkLet_spec p hp.derb hp.derf hp.lef hp.lep hp.lei hp.mklet n] <;>
    finish (gen := 20) [tierW, idxW]

include hp in
theorem liftProj_step (n : Nat) (ih : LiftGoSpec p n) (s₀ : St) (h c k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lift_proj" [h, c, k]
    ⦃fun r s' => LocEq s' s₀ ∧ liftProjW (n + 1) s₀.mem h c k = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold LiftGoSpec at ih
  rw [invoke_eq _ hp.pj]
  simp only [callFn, liftProj]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec lfSch p _ hp.lff n, memoPutG_spec lfSch p _ hp.lfp n, ih,
      mkProj_spec p hp.derb hp.derf hp.pjf hp.pjp hp.pji hp.mkpj n] <;>
    finish (gen := 20) [tierW, idxW]

include hp in
/-- **`lift_go` and its arms are their models**, at every fuel. -/
theorem liftGo_spec (n : Nat) : LiftGoSpec p n ∧ LiftArmSpec p n := by
  induction n with
  | zero =>
    refine ⟨fun s₀ h c k => ?_, fun s₀ h c k => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    first
    | (rw [invoke_eq _ hp.go]; simp only [callFn, liftGo]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.app]; simp only [callFn, liftApp]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.lam]; simp only [callFn, liftLam]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.fa]; simp only [callFn, liftForall]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.le]; simp only [callFn, liftLet]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.pj]; simp only [callFn, liftProj]; vcgen [exec] <;> grind)
  | succ n ih =>
    exact ⟨liftGo_step p hp n ih.2, fun s₀ h c k =>
      ⟨liftApp_step p hp n ih.1 s₀ h c k, liftLam_step p hp n ih.1 s₀ h c k,
        liftForall_step p hp n ih.1 s₀ h c k, liftLet_step p hp n ih.1 s₀ h c k,
        liftProj_step p hp n ih.1 s₀ h c k⟩⟩

end specs

/-! ## `lift_entry(h, k, c)`: `liftLooseBVarsFast`, between two clears -/

/-- After the walk: clear the lift memo again. -/
def lclrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => if rdW (m₁.arr64 CTL) 42 + 2 = 0 then none else some (r, mclearG lfSch m₁)

/-- **The model of `lift_entry`.** -/
def liftEntryW (n : Nat) (m : Mem) (h k c : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 42 + 2 = 0 then none else lclrK (liftW n (mclearG lfSch m) h c k)

theorem liftEntryW_eq (n : Nat) (m : Mem) (h k c : Word) (h0 : rdW (m.arr64 CTL) 42 + 2 ≠ 0) :
    liftEntryW n m h k c = lclrK (liftW n (mclearG lfSch m) h c k) := by
  simp [liftEntryW, h0]

theorem lclrK_some (r : Word) (m₁ : Mem) (h0 : rdW (m₁.arr64 CTL) 42 + 2 ≠ 0) :
    lclrK (some (r, m₁)) = some (r, mclearG lfSch m₁) := by simp [lclrK, h0]

grind_pattern [arena_grind] liftEntryW_eq => liftEntryW n m h k c
grind_pattern [arena_grind] lclrK_some => lclrK (some (r, m₁))

@[l_impl ConRon.Arena.liftLooseBVarsFast]
def liftEntry : FunDecl := lfn (h, k, c) locals (r, u) {
  u := call lf_clear();
  r := call lift_go(h, c, k);
  u := call lf_clear();
  return r
}

theorem liftEntry_spec (p : Prog) (hp : LiftProg p) (he : p.lookup "lift_entry" = some liftEntry)
    (n : Nat) (s₀ : St) (h k c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "lift_entry" [h, k, c]
    ⦃fun r s' => LocEq s' s₀ ∧ liftEntryW n s₀.mem h k c = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (liftGo_spec p hp n).1
  unfold LiftGoSpec at ih
  rw [invoke_eq _ he]
  simp only [callFn, liftEntry]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec lfSch p _ hp.lfc n,
      ih] <;>
    finish

/-- The walk, the memo, the `mk_*` and the stores they call, as one program. -/
def liftProg : Prog :=
  [("der_b", derB), ("der_f", derF), ("lf_find", memoFindG lfSch), ("lf_put", memoPutG lfSch),
    ("lf_clear", memoClearG lfSch), ("lift_go", liftGo), ("lift_app", liftApp),
    ("lift_lam", liftLam), ("lift_forall", liftForall), ("lift_let", liftLet),
    ("lift_proj", liftProj), ("lift_entry", liftEntry), ("mk_app", mkApp), ("mk_lam", mkLam),
    ("mk_forall", mkForall), ("mk_let", mkLet), ("mk_proj", mkProj)] ++
  bvarProg ++ appProg ++ lamProg ++ forallProg ++ letProg ++ projProg

theorem liftProg_ok : LiftProg liftProg :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end L.Arena
