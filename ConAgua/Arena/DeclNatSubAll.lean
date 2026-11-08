module

public import ConAgua.Arena.DeclNatSub
public import ConAgua.Arena.DeclDivModSpec.SubstConst0List
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.DeclArmsNat

@[expose] public section

/-!
# The structural-`Nat` gate: constant substitution under binders (lane `decls4`, helper `decls4-sca`)

`subst_const_all` refines `substConstAll`, after `DeclNatSub`'s `subst_const0`: the model `scaW` of
one call, then the refinement by induction on the twin's fuel. The binary arms (`app`, `lam`,
`forallE`) share `sca_bin`; `letE` and `proj` have their own.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem scaGetD3 (r : List Word) : r.getD 3 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl

section suball
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

structure NatSubAllProg (p : Prog) : Prop extends NatSubProg p where
  lSubstConstAll : p.lookup "subst_const_all" = some substConstAllL

/-- **`subst_const_all` is its model `scaW`** (generated). -/
l_model sca_specW (p : Prog) (hp : p.lookup "subst_const_all" = some substConstAllL)
  fns [hp ↦ scaW list]
  specs [callW_spec p n "e_view", callW_spec p n "pin_word", callW_spec p n "subst_const_all", callW_spec p n "mk_app", callW_spec p n "mk_lam", callW_spec p n "mk_forall", callW_spec p n "mk_let", callW_spec p n "mk_proj"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW instances 10000

/-- The induction hypothesis of `sca_ref`: every returning call at a fuel word of value `f`. -/
def ScaIH (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (nm r : Word)
    (f : Nat) : Prop :=
  ∀ (fuel : Word), fuel.toNat = f → ∀ (h : Word) (k : Nat) (m : Mem) (a : AState)
    (res : List Word) (m' : Mem), StageR vis fe m a → H nm → H r → H h →
    callW p k "subst_const_all" [nm, r, fuel, h] m = some (res, m') →
    ∃ x a', (substConstAll (decI nm) (decE r) f (decE h)).run a = .ok (x, a') ∧
      KeepPost vis fe decW0E m m' a' res x

/-- A binary arm: both children, then the interner `mk` (refining `I`). -/
theorem sca_bin {nm r : Word} {f : Nat} (ih : ScaIH p dn vis fe nm r f) (mk : FnName)
    (I : EIdx → EIdx → AM EIdx)
    (hmk : ∀ t b, CallRef p mk [t, b] (StageR vis fe) (I (decE t) (decE b))
      (KeepPost vis fe decW0E))
    {fuel x y : Word} (hf : (fuel - 1).toNat = f) {k : Nat} {m1 : Mem} {a1 : AState}
    {res : List Word} {m' : Mem} (hS1 : StageR vis fe m1 a1) (hn : H nm) (hr : H r)
    (hx : H x) (hy : H y)
    (hw : (ntBW (callW p k "subst_const_all" [nm, r, fuel - 1, x] m1) fun r1 m2 =>
      ntBW (callW p k "subst_const_all" [nm, r, fuel - 1, y] m2) fun r2 m3 =>
      ntBW (callW p k mk [r1.headD 0, r2.headD 0] m3) fun r3 m4 => some ([r3.headD 0], m4)) =
      some (res, m')) :
    ∃ e a', (do
        let f' ← substConstAll (decI nm) (decE r) f (decE x)
        let a' ← substConstAll (decI nm) (decE r) f (decE y)
        I f' a').run a1 = .ok (e, a') ∧ KeepPost vis fe decW0E m1 m' a' res e := by
  cases h2 : callW p k "subst_const_all" [nm, r, fuel - 1, x] m1 with
  | none => rw [h2] at hw; simp [ntBW] at hw
  | some q2 =>
  obtain ⟨r1, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hl2, hx2⟩ := ih (fuel - 1) hf x k m1 a1 r1 m2 hS1 hn hr hx h2
  cases h3 : callW p k "subst_const_all" [nm, r, fuel - 1, y] m2 with
  | none => rw [h3] at hw; simp [ntBW] at hw
  | some q3 =>
  obtain ⟨r2, m3⟩ := q3
  rw [h3, bW_some] at hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hl3, hx3⟩ := ih (fuel - 1) hf y k m2 a2 r2 m3 hS2 hn hr hy h3
  cases h4 : callW p k mk [r1.headD 0, r2.headD 0] m3 with
  | none => rw [h4] at hw; simp [ntBW] at hw
  | some q4 =>
  obtain ⟨r3, m4⟩ := q4
  rw [h4, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨x4, a4, hrun4, hS4, hg4, hl4, hx4⟩ := hmk (r1.headD 0) (r2.headD 0) k m3 a3 r3 m4 hS3 h4
  refine ⟨x4, a4, ?_, hS4, hg2.trans (hg3.trans hg4), hl4, hx4⟩
  simp only [StateT.run_bind, hrun2, hrun3, exc_ok_bind', ← hx2, ← hx3]
  exact hrun4

/-- The `letE` arm. -/
theorem sca_let (hM : MasterProg p) {nm r : Word} {f : Nat} (ih : ScaIH p dn vis fe nm r f)
    {fuel x y z : Word} (hf : (fuel - 1).toNat = f) {k : Nat} {m1 : Mem} {a1 : AState}
    {res : List Word} {m' : Mem} (hS1 : StageR vis fe m1 a1) (hn : H nm) (hr : H r)
    (hx : H x) (hy : H y) (hz : H z)
    (hw : (ntBW (callW p k "subst_const_all" [nm, r, fuel - 1, x] m1) fun r1 m2 =>
      ntBW (callW p k "subst_const_all" [nm, r, fuel - 1, y] m2) fun r2 m3 =>
      ntBW (callW p k "subst_const_all" [nm, r, fuel - 1, z] m3) fun r3 m4 =>
      ntBW (callW p k "mk_let" [r1.headD 0, r2.headD 0, r3.headD 0] m4) fun r5 m5 =>
      some ([r5.headD 0], m5)) = some (res, m')) :
    ∃ e a', (do
        let t' ← substConstAll (decI nm) (decE r) f (decE x)
        let v' ← substConstAll (decI nm) (decE r) f (decE y)
        let b' ← substConstAll (decI nm) (decE r) f (decE z)
        internE (.letE t' v' b')).run a1 = .ok (e, a') ∧ KeepPost vis fe decW0E m1 m' a' res e := by
  sorry

/-- The `proj` arm. -/
theorem sca_proj (hM : MasterProg p) {nm r : Word} {f : Nat} (ih : ScaIH p dn vis fe nm r f)
    {fuel x y z : Word} (hf : (fuel - 1).toNat = f) {k : Nat} {m1 : Mem} {a1 : AState}
    {res : List Word} {m' : Mem} (hS1 : StageR vis fe m1 a1) (hn : H nm) (hr : H r) (hz : H z)
    (hw : (ntBW (callW p k "subst_const_all" [nm, r, fuel - 1, z] m1) fun r1 m2 =>
      ntBW (callW p k "mk_proj" [x, y, r1.headD 0] m2) fun r3 m3 => some ([r3.headD 0], m3)) =
      some (res, m')) :
    ∃ e a', (do
        let e' ← substConstAll (decI nm) (decE r) f (decE z)
        internE (.proj (decI x) y.toNat e')).run a1 = .ok (e, a') ∧
      KeepPost vis fe decW0E m1 m' a' res e := by
  sorry

theorem sca_ref (hN : NatSubAllProg p) (nm r : Word) : ∀ f, ScaIH p dn vis fe nm r f := by
  sorry

@[refines ConRon.Arena.substConstAll]
theorem substConstAll_refines (hN : NatSubAllProg p) (nm r fuel h : Word) :
    RefAM p "subst_const_all" [nm, r, fuel, h]
      (fun m a => StageR vis fe m a ∧ H nm ∧ H r ∧ H h)
      (substConstAll (decI nm) (decE r) fuel.toNat (decE h)) (KeepPost vis fe decW0E) := by
  sorry

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`subst_const_all` at the walk fuel**: `DeclDivModSpec/SubstConst0List`'s `SubstCAll`. -/
theorem substCAll_of (hN : NatSubAllProg p) : ∀ dn vis fe, SubstCAll p dn vis fe := by
  sorry

-/

end suball

end L.Ind
