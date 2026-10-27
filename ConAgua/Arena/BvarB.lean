module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.Walk
public import ConAgua.L.ProgHas
import ConAgua.Census.Attr
public import ConAgua.Arena.ExprMk
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `bvarB` and `looseBVarsBoundedFast`: the loose-bvar field read

con-ron's `bvarB fuel e` (`fvarB`'s sibling): the packed bvar range (`der_b`), or, on the
saturated branch alone, the exact memoized `bvarBoundMemo` (`bb_memo`, `Walk.lean`); and
`looseBVarsBoundedFast fuel k e = (bvarB fuel e ≤ k)`. `bvar_b(f, e)` and
`loose_bvars_bounded_fast(f, k, e)` are the stub interfaces' names (lanes `decls`, `indproofs`);
`f` is the twin's fuel, passed to `bb_memo` as the walk's depth counter.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **The model of `bb_memo` at L fuel `n`** (`none` at `0`). -/
def bbN : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, h, f => bbMemoW n m h f

/-- **The model of `bvar_b`.** -/
def bvbW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, h, f => if derBW m h = 32767 then bbN n m h f else some (derBW m h, m)

/-- After `bvar_b`: the bound is at most `k`. -/
def lbbK (k : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => some (if x ≤ k then 1 else 0, m₁)

section eqs
variable (n : Nat) (m m₁ : Mem) (h k x f : Word)
theorem bbN_succ : bbN (n + 1) m h f = bbMemoW n m h f := rfl
theorem bvbW_sat (hs : derBW m h = 32767) : bvbW (n + 1) m h f = bbN n m h f := by simp [bvbW, hs]
theorem bvbW_pk (hs : derBW m h ≠ 32767) : bvbW (n + 1) m h f = some (derBW m h, m) := by
  simp [bvbW, hs]
theorem lbbK_some : lbbK k (some (x, m₁)) = some (if x ≤ k then 1 else 0, m₁) := rfl
end eqs

grind_pattern [arena_grind] bbN_succ => bbN (n + 1) m h f
grind_pattern [arena_grind] bvbW_sat => bvbW (n + 1) m h f
grind_pattern [arena_grind] bvbW_pk => bvbW (n + 1) m h f
attribute [arena_grind =] lbbK_some

/-- con-ron: ConRon/Arena/ExprOps.lean:1565-1572 ConRon.Arena.bvarB -/
@[l_impl ConRon.Arena.bvarB]
def bvarBL : FunDecl := lfn (f, e) locals (x, r) {
  x := call der_b(e);
  if x == 32767 { r := call bb_memo(e, f); return r };
  return x
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1588-1592 ConRon.Arena.looseBVarsBoundedFast -/
@[l_impl ConRon.Arena.looseBVarsBoundedFast]
def lbbFastL : FunDecl := lfn (f, k, e) locals (x) {
  x := call bvar_b(f, e);
  return u64(x <= k)
}

/-- The two reads, `der_b` and the bvar-bound walk, as one program. -/
def bvbProg : Prog :=
  [("bvar_b", bvarBL), ("loose_bvars_bounded_fast", lbbFastL), ("der_b", derB)] ++ walkProg

/-- What the specs need of the program: `bvbProg`'s functions. -/
def BvbProg (p : Prog) : Prop := ProgHas p bvbProg

/-- The old field `CoreWalks` reads. -/
theorem BvbProg.lbb {p : Prog} (hp : BvbProg p) :
    p.lookup "loose_bvars_bounded_fast" = some lbbFastL := hp.get _

section specs
variable (p : Prog) (hp : BvbProg p)

include hp in
theorem bbN_spec (n : Nat) (s₀ : St) (h f : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "bb_memo" [h, f]
    ⦃fun r s' => LocEq s' s₀ ∧ bbN n s₀.mem h f = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases n with
  | zero => rw [invoke_eq _ (hp.get "bb_memo")]; simp only [callFn, bbMemo]; vcgen [exec] <;> grind
  | succ n =>
    exact bbMemo_spec p (hp.get "bm_find") (hp.get "bm_put") (hp.get "bb_go")
      (hp.get "bb_node") (hp.get "bm_clear") (hp.get "bb_memo") n s₀ h f

include hp in
theorem bvarBL_spec (n : Nat) (s₀ : St) (f h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "bvar_b" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ bvbW n s₀.mem h f = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "bvar_b")]
  simp only [callFn, bvarBL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, derB_spec p (hp.get "der_b") n,
        bbN_spec p hp n] <;>
      finish

include hp in
theorem lbbFastL_spec (n : Nat) (s₀ : St) (f k h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "loose_bvars_bounded_fast" [f, k, h]
    ⦃fun r s' => LocEq s' s₀ ∧ lbbK k (bvbW n s₀.mem h f) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "loose_bvars_bounded_fast")]
  simp only [callFn, lbbFastL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, bvarBL_spec p hp n] <;>
    finish

end specs

theorem bvbProg_ok : BvbProg bvbProg := ProgHas.refl _

end L.Arena
