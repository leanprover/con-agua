module

public import ConAgua.Arena.DeclNatEq
import ConAgua.Arena.RecClassSpec.Classes
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Arena.DeclArmsNat
import all ConAgua.Arena.IndIface

@[expose] public section

/-!
# The structural-`Nat` gate: constant substitution (lane `decls3`, helper `decls3-nat`)

`subst_const0`, `subst_const0_pairs`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem viewR_shape {rv : List Word} {v : ENodeView} (h : ViewR rv v) :
    (rv.headD 0 = 3 ∧ ∃ c us, v = .const c us ∧ H (rv.tail.headD 0) ∧ decI (rv.tail.headD 0) = c ∧
      H (rv.tail.tail.headD 0) ∧ decI (rv.tail.tail.headD 0) = us) ∨
    (rv.headD 0 = 4 ∧ ∃ f a, v = .app f a ∧ H (rv.tail.headD 0) ∧ decE (rv.tail.headD 0) = f ∧
      H (rv.tail.tail.headD 0) ∧ decE (rv.tail.tail.headD 0) = a) ∨
    (rv.headD 0 ≠ 3 ∧ rv.headD 0 ≠ 4 ∧ (∀ c us, v ≠ .const c us) ∧ ∀ f a, v ≠ .app f a) := by
  cases v <;> simp only [ViewR] at h
  case const c us =>
    left
    obtain ⟨h0, h1, h2, h3, h4⟩ := h
    refine ⟨h0, _, _, rfl, ?_, ?_, ?_, ?_⟩ <;> simp_all [H]
  case app f a =>
    right; left
    obtain ⟨h0, h1, h2, h3, h4⟩ := h
    refine ⟨h0, _, _, rfl, ?_, ?_, ?_, ?_⟩ <;> simp_all [H]
  all_goals
    right; right
    refine ⟨?_, ?_, fun _ _ => by simp, fun _ _ => by simp⟩ <;> simp_all

theorem decNL_getW : ∀ (m : Mem) (l o : Nat) (xs : List Nat), decNL m o l = some xs →
    xs.length = l ∧ ∀ (j : Nat) (hj : j < xs.length), ∃ w : Word, iwA m (o + j) = some w ∧
      w.toNat = xs[j]
  | m, 0, o, xs, h => by simp [decNL] at h; subst h; simp
  | m, l + 1, o, xs, h => by
    rw [decNL_succ] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, xs', hxs, rfl⟩ := h
    obtain ⟨hl, hg⟩ := decNL_getW m l (o + 1) xs' hxs
    refine ⟨by simp [hl], fun j hj => ?_⟩
    cases j with
    | zero =>
      simp only [iwN, nat?, Option.map_eq_some_iff] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨w, by simpa using hw, by simp⟩
    | succ j =>
      obtain ⟨w, hw, hwx⟩ := hg j (by simpa using hj)
      exact ⟨w, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hw, by simpa using hwx⟩

theorem EqL.decNL {m : Mem} {o l : Nat} {ps : List (EIdx × EIdx)} (h : EqL m o l ps) :
    ∃ xs, decNL m o l = some xs := by
  obtain ⟨h1, h2, h3⟩ := h
  have hget : ∀ j (hj : j < ps.length), ∃ p : Word, iwA m (o + j) = some p := fun j hj => by
    obtain ⟨p, a, b, hp, -⟩ := h3 j hj
    exact ⟨p, hp⟩
  refine ⟨(List.range ps.length).map (fun j => ((iwN m (o + j)).getD 0)), ?_⟩
  have := decNL_of_get m ((List.range ps.length).map (fun j => ((iwN m (o + j)).getD 0))) o (fun j hj => by
    simp only [List.length_map, List.length_range] at hj
    obtain ⟨p, hp⟩ := hget j hj
    simp [iwN, nat?, hp])
  simpa [h2] using this

theorem eqL_cons {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {x o l : Word} {r : List Word} {es : List (EIdx × EIdx)} {ea eb : Word}
    (h : consW n m x o l = some (r, m')) (hS : StageR vis fe m a)
    (hE : EqL m o.toNat l.toNat es) (hx : RecAt m x ea eb) (hea : H ea) (heb : H eb) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      EqL m' (r.headD 0).toNat (r.tail.headD 0).toNat ((decE ea, decE eb) :: es) := by
  sorry

section sub
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

structure NatSubProg (p : Prog) : Prop extends NatEqProg p where
  lSubstConst0 : p.lookup "subst_const0" = some substConst0L
  lSlCons : p.lookup "sl_cons" = some slCons
  lIwCopy : p.lookup "iw_copy" = some iwCopy
  lSubstConst0Pairs : p.lookup "subst_const0_pairs" = some substConst0PairsL

/-- **`subst_const0` is its model `sc0W`** (generated). -/
l_model sc0_specW (p : Prog) (hp : p.lookup "subst_const0" = some substConst0L)
  fns [hp ↦ sc0W list]
  specs [callW_spec p n "e_view", callW_spec p n "pin_word", callW_spec p n "subst_const0", callW_spec p n "mk_app"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW instances 10000

theorem sc0_ref (hN : NatSubProg p) (nm r : Word) :
    ∀ (f : Nat) (fuel : Word), fuel.toNat = f → ∀ (h : Word) (k : Nat) (m : Mem) (a : AState)
      (res : List Word) (m' : Mem), StageR vis fe m a → H nm → H r → H h →
      callW p k "subst_const0" [nm, r, fuel, h] m = some (res, m') →
      ∃ x a', (substConst0 (decI nm) (decE r) f (decE h)).run a = .ok (x, a') ∧
        KeepPost vis fe decW0E m m' a' res x := by
  sorry


@[refines ConRon.Arena.substConst0]
theorem substConst0_refines (hN : NatSubProg p) (nm r fuel h : Word) :
    RefAM p "subst_const0" [nm, r, fuel, h]
      (fun m a => StageR vis fe m a ∧ H nm ∧ H r ∧ H h)
      (substConst0 (decI nm) (decE r) fuel.toNat (decE h)) (KeepPost vis fe decW0E) :=
  CallRef.refAM (fun k m a res m' ⟨hS, hn, hr, hh⟩ hc =>
    sc0_ref hN nm r fuel.toNat fuel rfl h k m a res m' hS hn hr hh hc)

/-! ### `subst_const0_pairs` -/

/-- **`subst_const0_pairs` is its model `pairsW`** (generated). -/
l_model pairs_specW (p : Prog) (hp : p.lookup "subst_const0_pairs" = some substConst0PairsL)
  fns [hp ↦ pairsW list]
  specs [callW_spec p n "subst_const0", callW_spec p n "subst_const0_pairs", callW_spec p n "rec2", callW_spec p n "sl_cons"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW instances 10000

theorem pairs_ref (hN : NatSubProg p) (nm r : Word) (hn : H nm) (hr : H r) :
    ∀ (ps : List (EIdx × EIdx)) (o l : Word) (k : Nat) (m : Mem) (a : AState) (res : List Word)
      (m' : Mem), StageR vis fe m a → EqL m o.toNat l.toNat ps → o.toNat + l.toNat < 2 ^ 64 →
      callW p k "subst_const0_pairs" [nm, r, o, l] m = some (res, m') →
      ∃ x a', (substConst0Pairs (decI nm) (decE r) ps).run a = .ok (x, a') ∧
        KeepPost vis fe decEqRL m m' a' res x := by
  sorry

@[refines ConRon.Arena.substConst0Pairs]
theorem substConst0Pairs_refines (hN : NatSubProg p) (nm r o l : Word) (ps : List (EIdx × EIdx)) :
    RefAM p "subst_const0_pairs" [nm, r, o, l]
      (fun m a => StageR vis fe m a ∧ H nm ∧ H r ∧ EqL m o.toNat l.toNat ps ∧
        o.toNat + l.toNat < 2 ^ 64)
      (substConst0Pairs (decI nm) (decE r) ps) (KeepPost vis fe decEqRL) :=
  CallRef.refAM (fun k m a res m' ⟨hS, hn, hr, hE, hb⟩ hc =>
    pairs_ref hN nm r hn hr ps o l k m a res m' hS hE hb hc)

end sub

end L.Ind
