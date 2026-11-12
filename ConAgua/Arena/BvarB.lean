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
import ConAgua.L.ModelGen
import all ConAgua.Arena.Walk

@[expose] public section

/-!
# `bvarB` and `looseBVarsBoundedFast`: the loose-bvar field read

con-ron's `bvarB fuel e` (`fvarB`'s sibling): the packed bvar range (`der_bv`), or, on the
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

section eqs
variable (n : Nat) (m : Mem) (h f : Word)
theorem bbN_succ : bbN (n + 1) m h f = bbMemoW n m h f := rfl
end eqs

grind_pattern [arena_grind] bbN_succ => bbN (n + 1) m h f

/-- con-ron: ConRon/Arena/ExprOps.lean:1572-1579 ConRon.Arena.bvarB -/
@[no_expose, l_impl ConRon.Arena.bvarB]
def bvarBL : FunDecl := lfn (f, e) locals (x, r) {
  x := call der_bv(e);
  if x == 32767 { r := call bb_memo(e, f); return r };
  return x
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1595-1599 ConRon.Arena.looseBVarsBoundedFast -/
@[no_expose, l_impl ConRon.Arena.looseBVarsBoundedFast]
def lbbFastL : FunDecl := lfn (f, k, e) locals (x) {
  x := call bvar_b(f, e);
  return u64(x <= k)
}

/-- The two reads, `der_bv` and the bvar-bound walk, as one program. -/
def bvbProg : Prog :=
  [("bvar_b", bvarBL), ("loose_bvars_bounded_fast", lbbFastL), ("der_bv", derBv)] ++ walkProg

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

end specs

/-- **`bvar_b(f, e)` is its model `bvbW`** (generated): the packed range, or the walk when it is
saturated. -/
l_model bvarBL_spec (p : Prog) (hp : BvbProg p)
  fns [(hp.get "bvar_b") ↦ bvbW]
  specs [derBv_spec p (hp.get "der_bv") n, bbN_spec p hp n]
  grind [arena_grind]

/-- **`loose_bvars_bounded_fast(f, k, e)` is its model `lbbW`** (generated). -/
l_model lbbFastL_spec (p : Prog) (hp : BvbProg p)
  fns [(hp.get "loose_bvars_bounded_fast") ↦ lbbW]
  specs [bvarBL_spec p hp n]
  grind [arena_grind]


theorem bvbProg_ok : BvbProg bvbProg := ProgHas.refl _

end L.Arena
