module

public import ConAgua.Arena.DeclCanonExpr2
import ConAgua.Arena.DeclMasterStage
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclCvg
import ConAgua.Arena.IndMaster
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.DeclArmsCanon

@[expose] public section

/-!
# `canon_names_go`, `canon_names` (lane `decls3`, helper `decls3-canon`)

The numbered names `⟨0⟩ … ⟨n-1⟩`, interned. The one place the canonical comparison writes the
name tables; the expression store (and `LitInj`) is untouched.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

mutual
/-- **The model of `canon_names_go(i, n)`**. -/
def gnW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, i, n =>
    if n = 0 then some ([0, 0], m)
    else gK1 k i n (nainternW m)

/-- After `intern_nanon`. -/
def gK1 (k : Nat) (i n : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (a, m1) => if 4294967296 ≤ a then none else gK2 k i n (nninternW m1 a i)

/-- After `intern_nnum`. -/
def gK2 (k : Nat) (i n : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (h, m2) => if 4294967296 ≤ h then none else gK3 k h (gnW k m2 (i + 1) (n - 1))

/-- After the recursion. -/
def gK3 (k : Nat) (h : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => gK4 (consW k m3 h (r.headD 0) (r.tail.headD 0))

/-- After `sl_cons`. -/
def gK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m4) => some ([r.headD 0, r.tail.headD 0], m4)
end

section arms
variable (k : Nat) (m m1 m2 m3 m4 : Mem) (i n a h : Word) (r : List Word)
theorem gnW_succ : gnW (k + 1) m i n =
    (if n = 0 then some ([0, 0], m) else gK1 k i n (nainternW m)) := by rw [gnW]
theorem gK1_some : gK1 k i n (some (a, m1)) =
    (if 4294967296 ≤ a then none else gK2 k i n (nninternW m1 a i)) := by rw [gK1]
theorem gK2_some : gK2 k i n (some (h, m2)) =
    (if 4294967296 ≤ h then none else gK3 k h (gnW k m2 (i + 1) (n - 1))) := by rw [gK2]
theorem gK3_some : gK3 k h (some (r, m3)) = gK4 (consW k m3 h (r.headD 0) (r.tail.headD 0)) := by
  rw [gK3]
theorem gK4_some : gK4 (some (r, m4)) = some ([r.headD 0, r.tail.headD 0], m4) := by rw [gK4]
end arms

grind_pattern [ind_grind] gnW_succ => gnW (k + 1) m i n
grind_pattern [ind_grind] gK1_some => gK1 k i n (some (a, m1))
grind_pattern [ind_grind] gK2_some => gK2 k i n (some (h, m2))
grind_pattern [ind_grind] gK3_some => gK3 k h (some (r, m3))
grind_pattern [ind_grind] gK4_some => gK4 (some (r, m4))

section specs5
variable (p : Prog) (hp : CanonProg p)
include hp

set_option maxHeartbeats 4000000 in
theorem canonNamesGo_spec (n : Nat) : ∀ (s₀ : St) (i k : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "canon_names_go" [i, k]
    ⦃fun r s' => LocEq s' s₀ ∧ gnW n s₀.mem i k = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ i k
    rw [invoke_eq _ (hp.get "canon_names_go")]; simp only [callFn, canonNamesGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ i k
    rw [invoke_eq _ (hp.get "canon_names_go")]
    simp only [callFn, canonNamesGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        internNAnon_spec p (hp.get "nanon_find") (hp.get "nanon_push") (hp.get "intern_nanon") n,
        internNNum_spec p (hp.get "nnum_find") (hp.get "nnum_push") (hp.get "intern_nnum") n,
        slCons_specW p (hp.get "iw_alloc") (hp.get "iw_copy") (hp.get "sl_cons") n, ih] <;>
      finish (gen := 20)

end specs5


theorem gnW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (i n : Word) (r : List Word),
    gnW k m i n = some (r, m') → StageR vis fe m a → i.toNat + n.toNat < 2 ^ 64 → PoolSmall m →
    ∃ (hs : List NIdx) (a' : AState),
      (ConRon.Arena.canonNamesGo i.toNat n.toNat).run a = .ok (hs, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ decRL (fun m => decHL m) 0 m' r hs ∧ a'.store.view = a.store.view ∧ PoolSmall m' := by
  sorry


/-- **The model of `canon_names(n)`**. -/
def cnW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | k + 1, m, n =>
    match gnW k m 0 n with
    | none => none
    | some (r, m') => some ([r.headD 0, r.tail.headD 0], m')

theorem canonNames_spec (p : Prog) (hp : CanonProg p) (n : Nat) (s₀ : St) (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "canon_names" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ cnW n s₀.mem k = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "canon_names")]
  simp only [callFn, canonNames]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        canonNamesGo_spec p hp n] <;>
      finish (gen := 20) [cnW]

theorem LitInj.of_view {a a' : AState} (h : LitInj a) (hv : a'.store.view = a.store.view) :
    LitInj a' := by
  intro x y l hx hy
  rw [hv] at hx hy
  exact h x y l hx hy

/-- The post of `canon_names`: the list of numerals as an `IW` slice, the pool still addressable,
the literal hash-consing kept. -/
def NamesPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (r : List Word) (cs : List NIdx) : Prop :=
  KeepPost vis fe (fun m r (cs : List NIdx) => decRL (fun m => decHL m) 0 m r cs) m m' a r cs ∧
    PoolSmall m' ∧ LitInj a

theorem cnW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {n : Nat}
    {m m' : Mem} {a : AState} {k : Word} {r : List Word} (hr : cnW n m k = some (r, m'))
    (hS : StageR vis fe m a) (hP : PoolSmall m) :
    ∃ (hs : List NIdx) (a' : AState), (ConRon.Arena.canonNames k.toNat).run a = .ok (hs, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ decRL (fun m => decHL m) 0 m' r hs ∧
      a'.store.view = a.store.view ∧ PoolSmall m' := by
  sorry

/-- **`canon_names` refines `canonNames`.** -/
@[refines ConRon.Arena.canonNames]
theorem canonNames_refines (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (k : Word) :
    RefAM p "canon_names" [k]
      (fun m a => StageR vis fe m a ∧ PoolSmall m ∧ LitInj a)
      (ConRon.Arena.canonNames k.toNat) (NamesPost dn vis fe) := by
  sorry

/-- **`canon_names_go` refines `canonNamesGo`.** -/
@[refines ConRon.Arena.canonNamesGo]
theorem canonNamesGo_refines (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (i k : Word) :
    RefAM p "canon_names_go" [i, k]
      (fun m a => StageR vis fe m a ∧ PoolSmall m ∧ LitInj a ∧ i.toNat + k.toNat < 2 ^ 64)
      (ConRon.Arena.canonNamesGo i.toNat k.toNat) (NamesPost dn vis fe) := by
  sorry

end L.Ind
