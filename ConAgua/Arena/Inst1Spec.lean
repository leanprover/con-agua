module

public import ConAgua.Arena.Inst1
public import ConAgua.Arena.LiftSpec
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr

@[expose] public section

/-!
# The specs of `instantiate1`'s arms, and the entry

As `LiftSpec.lean`: the five arms' steps, the induction on the fuel (`instGo_spec`), the entry
`inst_entry` (`instantiate1Fast`) and the program `instProg`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

section specs
variable (p : Prog) (hp : InstProg p)

include hp in
theorem instApp_step (n : Nat) (ih : InstGoSpec p n) (s₀ : St) (h d v fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "inst_app" [h, d, v, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ instAppW (n + 1) s₀.mem h d v fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold InstGoSpec at ih
  rw [invoke_eq _ hp.app]
  simp only [callFn, instApp]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec imSch p _ hp.iff n, memoPutG_spec imSch p _ hp.ifp n, ih,
      mkApp_spec p hp.base.derb hp.base.appf hp.base.appp hp.base.appi hp.base.mkapp n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

include hp in
theorem instLam_step (n : Nat) (ih : InstGoSpec p n) (s₀ : St) (h d v fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "inst_lam" [h, d, v, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ instLamW (n + 1) s₀.mem h d v fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold InstGoSpec at ih
  rw [invoke_eq _ hp.lam]
  simp only [callFn, instLam]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec imSch p _ hp.iff n, memoPutG_spec imSch p _ hp.ifp n, ih,
      mkLam_spec p hp.base.derb hp.base.lamf hp.base.lamp hp.base.lami hp.base.mklam n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

include hp in
theorem instForall_step (n : Nat) (ih : InstGoSpec p n) (s₀ : St) (h d v fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "inst_forall" [h, d, v, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ instForallW (n + 1) s₀.mem h d v fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold InstGoSpec at ih
  rw [invoke_eq _ hp.fa]
  simp only [callFn, instForall]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec imSch p _ hp.iff n, memoPutG_spec imSch p _ hp.ifp n, ih,
      mkForall_spec p hp.base.derb hp.base.faf hp.base.fap hp.base.fai hp.base.mkfa n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

include hp in
theorem instLet_step (n : Nat) (ih : InstGoSpec p n) (s₀ : St) (h d v fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "inst_let" [h, d, v, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ instLetW (n + 1) s₀.mem h d v fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold InstGoSpec at ih
  rw [invoke_eq _ hp.le]
  simp only [callFn, instLet]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec imSch p _ hp.iff n, memoPutG_spec imSch p _ hp.ifp n, ih,
      mkLet_spec p hp.base.derb hp.base.lef hp.base.lep hp.base.lei hp.base.mklet n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

include hp in
theorem instProj_step (n : Nat) (ih : InstGoSpec p n) (s₀ : St) (h d v fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "inst_proj" [h, d, v, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ instProjW (n + 1) s₀.mem h d v fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  unfold InstGoSpec at ih
  rw [invoke_eq _ hp.pj]
  simp only [callFn, instProj]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec imSch p _ hp.iff n, memoPutG_spec imSch p _ hp.ifp n, ih,
      mkProj_spec p hp.base.derb hp.base.pjf hp.base.pjp hp.base.pji hp.base.mkpj n] <;>
    finish (gen := 20) [viewOK, tierW, idxW]

include hp in
/-- **`lift_go` and its arms are their models**, at every fuel. -/
theorem instGo_spec (n : Nat) : InstGoSpec p n ∧ InstArmSpec p n := by
  induction n with
  | zero =>
    refine ⟨fun s₀ h d v fu => ?_, fun s₀ h d v fu => ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    first
    | (rw [invoke_eq _ hp.go]; simp only [callFn, instGo]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.app]; simp only [callFn, instApp]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.lam]; simp only [callFn, instLam]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.fa]; simp only [callFn, instForall]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.le]; simp only [callFn, instLet]; vcgen [exec] <;> grind)
    | (rw [invoke_eq _ hp.pj]; simp only [callFn, instProj]; vcgen [exec] <;> grind)
  | succ n ih =>
    exact ⟨instGo_step p hp n ih.2, fun s₀ h d v fu =>
      ⟨instApp_step p hp n ih.1 s₀ h d v fu, instLam_step p hp n ih.1 s₀ h d v fu,
        instForall_step p hp n ih.1 s₀ h d v fu, instLet_step p hp n ih.1 s₀ h d v fu,
        instProj_step p hp n ih.1 s₀ h d v fu⟩⟩

end specs

/-! ## `inst_entry(e, v, d)`: `instantiate1Fast`, between two clears

The walk's depth counter starts at `coreWalkFuel` (`4000000000`, ROADMAP §3 (b)). -/

/-- After the walk: clear the memo again; the handle word is returned masked to 32 bits (the
callers' contract `HW`; `decE` reads the same handle). -/
def iclrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) =>
    if rdW (m₁.arr64 CTL) 44 + 2 = 0 then none else some (r &&& 4294967295, mclearG imSch m₁)

/-- **The model of `inst_entry`.** -/
def instEntryW (n : Nat) (m : Mem) (e v d : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 44 + 2 = 0 then none else iclrK (instW n (mclearG imSch m) e d v 4000000000)

theorem instEntryW_eq (n : Nat) (m : Mem) (e v d : Word) (h0 : rdW (m.arr64 CTL) 44 + 2 ≠ 0) :
    instEntryW n m e v d = iclrK (instW n (mclearG imSch m) e d v 4000000000) := by
  simp [instEntryW, h0]

theorem iclrK_some (r : Word) (m₁ : Mem) (h0 : rdW (m₁.arr64 CTL) 44 + 2 ≠ 0) :
    iclrK (some (r, m₁)) = some (r &&& 4294967295, mclearG imSch m₁) := by simp [iclrK, h0]

grind_pattern [arena_grind] instEntryW_eq => instEntryW n m e v d
grind_pattern [arena_grind] iclrK_some => iclrK (some (r, m₁))

/-- con-ron: ConRon/Arena/ExprOps.lean:377-384 ConRon.Arena.instantiate1Fast -/
@[l_impl ConRon.Arena.instantiate1Fast]
def instEntry : FunDecl := lfn (e, v, d) locals (r, u) {
  u := call if_clear();
  r := call inst_go(e, d, v, 4000000000);
  u := call if_clear();
  return r & 4294967295
}

theorem instEntry_spec (p : Prog) (hp : InstProg p) (he : p.lookup "inst_entry" = some instEntry)
    (n : Nat) (s₀ : St) (e v d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "inst_entry" [e, v, d]
    ⦃fun r s' => LocEq s' s₀ ∧ instEntryW n s₀.mem e v d = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (instGo_spec p hp n).1
  unfold InstGoSpec at ih
  rw [invoke_eq _ he]
  simp only [callFn, instEntry]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec imSch p _ hp.ifc n,
      ih] <;>
    finish

/-- The walk, the memo and `liftProg` (the `mk_*`, the stores), as one program. -/
def instProg : Prog :=
  [("if_find", memoFindG imSch), ("if_put", memoPutG imSch), ("if_clear", memoClearG imSch),
    ("inst_go", instGo), ("inst_app", instApp), ("inst_lam", instLam),
    ("inst_forall", instForall), ("inst_let", instLet), ("inst_proj", instProj),
    ("inst_entry", instEntry)] ++ liftProg

theorem instProg_ok : InstProg instProg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end L.Arena
