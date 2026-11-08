module

public import ConAgua.Arena.DeclNatLit
import ConAgua.Arena.DeclNatDeps
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclNatGate
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.DeclArmsNat

@[expose] public section

/-!
# The structural-`Nat` gate: `bool_ctor_ok` and `nat_op_guard` (lane `decls3`, helper `decls3-nat`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

structure NatGuardProg (p : Prog) : Prop extends NatLitProg p where
  lBoolCtorOk : p.lookup "bool_ctor_ok" = some boolCtorOkL
  lNatOpGuard : p.lookup "nat_op_guard" = some natOpGuardL
  lBoolCtors : p.lookup "nat_op_bool_ctors" = some natOpBoolCtorsL

/-- A constant value record `[name, lps.off, lps.len, type]` at `q`: the length word and the type
word, and that they stay under growth. -/
theorem cvWordsAt {m : Mem} {q : Word} {cv : IConstantVal} (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (h : decCV (erecP m) q.toNat = some cv) :
    ∃ wt, ((rdW (m.arr64 EREC) (q + 2) = 0) ↔ cv.levelParams.isEmpty = true) ∧
      rdW (m.arr64 EREC) (q + 3) = wt ∧ wt.toNat < 2 ^ 32 ∧ cv.type = decI wt ∧
      ∀ m', IWGrow m m' → rdW (m'.arr64 EREC) (q + 2) = rdW (m.arr64 EREC) (q + 2) ∧
        rdW (m'.arr64 EREC) (q + 3) = wt := by
  sorry

section guard
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-! ### `bool_ctor_ok` -/

/-- **`bool_ctor_ok` is its model `boolCtorOkW`** (generated). -/
l_model boolCtorOk_specW (p : Prog) (hp : p.lookup "bool_ctor_ok" = some boolCtorOkL)
  fns [hp ↦ boolCtorOkW list]
  specs [callW_spec p n "ci_to_cv", callW_spec p n "pin_at", callW_spec p n "const_e"]
  grind [arena_grind] bind ntBW

theorem boolCtorOk_ref (hN : NatGuardProg p) (c : Word) (ci : IConstantInfo) :
    CallRef p "bool_ctor_ok" [c]
      (fun m a => StageR vis fe m a ∧ decCI (erecP m) c.toNat = some ci)
      (boolCtorOk ci) (KeepPost vis fe decW0B) := by
  sorry

@[refines ConRon.Arena.boolCtorOk]
theorem boolCtorOk_refines (hN : NatGuardProg p) (c : Word) (ci : IConstantInfo) :
    RefAM p "bool_ctor_ok" [c]
      (fun m a => StageR vis fe m a ∧ decCI (erecP m) c.toNat = some ci)
      (boolCtorOk ci) (KeepPost vis fe decW0B) :=
  (boolCtorOk_ref hN c ci).refAM


/-- A pin read followed by the lookup of the pinned name: memory unchanged, the twin's pin read,
the decoded lookup. -/
theorem pinFind_call (hN : NatGuardProg p) {i : Word} (hi : i.toNat < 51) {k : Nat} {m m1 m2 : Mem}
    {a : AState} {r1 rf : List Word} (hS : StageR vis fe m a)
    (h1 : callW p k "pin_at" [i] m = some (r1, m1))
    (h2 : callW p k "env_find" [r1.headD 0, vis] m1 = some (rf, m2)) :
    m1 = m ∧ m2 = m ∧ pinW m 0 ≠ 0 ∧ H (r1.headD 0) ∧ r1.headD 0 = pinW m (1 + i.toNat) ∧
      (pinAt i.toNat).run a = .ok (decI (r1.headD 0), a) ∧
      decFd dn m rf (fe.find? (decI (r1.headD 0))) := by
  obtain ⟨hm1, h0, hr1⟩ := pinAt_call hN.lPinAt (j := 1 + i.toNat) rfl h1
  subst hm1
  have hF := hS.check.pins.full h0
  have hp : H (r1.headD 0) := by rw [hr1]; exact hF.names_lt i.toNat hi
  obtain ⟨hm2, hfd⟩ := envFind_call hN.toMasterProg (r1.headD 0) hp hS.check.env h2
  refine ⟨rfl, hm2, h0, hp, hr1, ?_, hfd⟩
  have := pinAt_run hF i.toNat hi
  rw [hr1]; exact this


/-! ### `nat_op_bool_ctors` -/

/-- **`nat_op_bool_ctors` is its model `boolCtorsW`** (generated). -/
l_model boolCtors_specW (p : Prog) (hp : p.lookup "nat_op_bool_ctors" = some natOpBoolCtorsL)
  fns [hp ↦ boolCtorsW list]
  specs [callW_spec p n "pin_at", callW_spec p n "env_find", callW_spec p n "bool_ctor_ok"]
  grind [arena_grind] bind ntBW

/-! ### `nat_op_guard` -/

/-- **`nat_op_guard` is its model `natOpGuardW`** (generated). -/
l_model natOpGuard_specW (p : Prog) (hp : p.lookup "nat_op_guard" = some natOpGuardL)
  fns [hp ↦ natOpGuardW list]
  specs [callW_spec p n "nat_lit_supported", callW_spec p n "nat_op_deps", callW_spec p n "nat_op_deps_stored", callW_spec p n "pin_at", callW_spec p n "nat_div_mod_names", callW_spec p n "sl_contains", callW_spec p n "nat_op_bool_ctors"]
  grind [arena_grind] heartbeats 3200000 bind ntBW

/-- The `Bool` constructors' conjunct of `natOpGuard`, as a twin value. -/
def natBoolCtorsT (fe : IFEnv) : AM Bool := do
  let bt ← boolTrueName
  let okT ← match fe.find? bt with
    | some ci => boolCtorOk ci
    | none => pure false
  if !okT then pure false else do
    let bf ← boolFalseName
    match fe.find? bf with
    | some ci => boolCtorOk ci
    | none => pure false

theorem boolCtors_ref (hN : NatGuardProg p) :
    CallRef p "nat_op_bool_ctors" [vis] (StageR vis fe) (natBoolCtorsT fe)
      (KeepPost vis fe decW0B) := by
  sorry

theorem ntGetD0 (r : List Word) : r.getD 0 0 = r.headD 0 := by cases r <;> simp
theorem ntGetD1 (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  cases r with
  | nil => simp
  | cons a t => cases t <;> simp

theorem natOpGuard_unfold (fe : IFEnv) (c : NIdx) : natOpGuard fe c = (do
    if !(← natLitSupported fe) then pure false else do
      let deps ← natOpDeps c
      if !(← natOpDepsStored fe deps) then pure false else do
        let be ← natBeqName
        let bl ← natBleName
        let dm ← natDivModNames
        if c == be || c == bl || dm.contains c then natBoolCtorsT fe else pure true) := rfl

theorem natOpGuard_ref (hN : NatGuardProg p) (c : Word) :
    CallRef p "nat_op_guard" [vis, c] (fun m a => StageR vis fe m a ∧ H c)
      (natOpGuard fe (decI c)) (KeepPost vis fe decW0B) := by
  sorry


@[refines ConRon.Arena.natOpGuard]
theorem natOpGuard_refines (hN : NatGuardProg p) (c : Word) :
    RefAM p "nat_op_guard" [vis, c] (fun m a => StageR vis fe m a ∧ H c)
      (natOpGuard fe (decI c)) (KeepPost vis fe decW0B) :=
  (natOpGuard_ref hN c).refAM

end guard

end L.Ind
