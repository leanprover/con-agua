import ConAgua.Arena.LevelSubstL
import ConAgua.Arena.LevelArena
import ConAgua.Arena.Tiers
import ConAgua.Arena.ZeroStore
import ConAgua.Arena.ParamStore
import ConAgua.Arena.MaxStore
import ConAgua.Arena.ImaxStore
import ConAgua.Census.Attr

/-!
# Interning a level pointer back into the store: `lv_intern`, `lv_sub_int`

con-ron's level-substituting functions (`substLMemoAt`, `substLevelsAt`, `substParamLevels`,
`recFireLevels`) read a level back (`readLevelM`), run con-leche's `Level.subst` on the transient
tree and **intern the result** (`internLevel`). L has no trees: lane `levels`' `lv_substl`
(`LevelSubstL.lean`) runs `subst` on level pointers (a store handle, or a node of the scratch heap
`LH`, `LevelHeap.lean`) and returns a pointer. What is new here is the way back into the store
(finding (3) of lane `whnf`, DESIGN.md):

* `lv_intern(p)`: `internLevel l` for the level `l` the pointer `p` denotes (`LvR`), node by node
  in the twin's order (the children first, `u` before `v`), **every** node, whether `p` is a heap
  node or a store handle, as the twin re-interns the whole readback. A `param`'s name word is a
  stored name handle, re-interned by the twin as `internName` of its readback, which returns the
  handle and changes nothing (`NStoreWF`'s `consP`/`consS`).
* `lv_sub_int(u, ko, kc, vo, vc)`: a fresh heap (`CTL[192] := 0`, as `lvl_eq`), `lv_substl` with
  the keys the `EREC` name slice `(ko, kc)` and the values the `POOL` level-list slice
  `(vo, vc)`, then `lv_intern`: `internLevel (Level.subst ks vs l)`.

The keys and values arrays of lane `levels`' generic functions are fixed here: `lv_lookup` is
`lvLookupG EREC POOL` (and `lv_spw` is `lvSpwG EREC`, for `caps_never_zero`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-- `lv_lookup` with the keys in the record pool (a declaration's level parameters) and the values
in the limb pool (a level list's handles). -/
abbrev lvLookupLP : FunDecl := lvLookupG EREC POOL
/-- `lv_spw` with the datum's names in the record pool. -/
abbrev lvSpwLP : FunDecl := lvSpwG EREC

/-! ## `lv_intern(p)` -/

/-- con-ron: ConRon/Arena/Monad.lean:472-490 ConRon.Arena.internLevel -/
@[l_impl ConRon.Arena.internLevel]
def lvIntern : FunDecl := lfn (p) locals (g, a, b, x, y, h) {
  (g, a, b) := call lv_node(p);
  if g == 0 {
    h := call intern_zero();
    if h >= 4294967296 { abort };
    return h
  };
  if g == 4 {
    h := call intern_param(a);
    if h >= 4294967296 { abort };
    return h
  };
  x := call lv_intern(a);
  if g == 1 {
    h := call intern_succ(x);
    if h >= 4294967296 { abort };
    return h
  };
  y := call lv_intern(b);
  if g == 2 {
    h := call intern_max(x, y);
    if h >= 4294967296 { abort };
    return h
  };
  if g != 3 { abort };
  h := call intern_imax(x, y);
  if h >= 4294967296 { abort };
  return h
}

/-- A node interned: the handle checked. -/
def liNodeK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (h, m') => if 4294967296 ≤ h then none else some (h, m')

/-- After the second child. -/
def liTwoK (g x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) =>
    if g = 2 then liNodeK (minternW m₂ x y)
    else if g = 3 then liNodeK (iminternW m₂ x y)
    else none

mutual
/-- **The model of `lv_intern`** at L fuel `n`. -/
def lvInternW : Nat → Mem → Word → Option (Word × Mem)
  | 0, _, _ => none
  | n + 1, m, p =>
    if lvG m p = 0 then liNodeK (zinternW m)
    else if lvG m p = 4 then liNodeK (pinternW m (lvA m p))
    else liOneK n (lvG m p) (lvB m p) (lvInternW n m (lvA m p))

/-- After the first child. -/
def liOneK (n : Nat) (g b : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) =>
    if g = 1 then liNodeK (sinternW m₁ x)
    else liTwoK g x (lvInternW n m₁ b)
end

section arms
variable (n : Nat) (m m₁ : Mem) (p g b x y h : Word)
theorem liNodeK_some (hh : ¬ 4294967296 ≤ h) : liNodeK (some (h, m)) = some (h, m) := by
  simp [liNodeK, hh]
theorem liTwoK_max (hg : g = 2) : liTwoK g x (some (y, m)) = liNodeK (minternW m x y) := by
  simp [liTwoK, hg]
theorem liTwoK_imax (hg : g = 3) : liTwoK g x (some (y, m)) = liNodeK (iminternW m x y) := by
  simp [liTwoK, hg]
theorem lvInternW_zero (h0 : lvG m p = 0) : lvInternW (n + 1) m p = liNodeK (zinternW m) := by
  rw [lvInternW]; simp [h0]
theorem lvInternW_param (h0 : lvG m p ≠ 0) (h4 : lvG m p = 4) :
    lvInternW (n + 1) m p = liNodeK (pinternW m (lvA m p)) := by
  rw [lvInternW]; simp [h0, h4]
theorem lvInternW_rec (h0 : lvG m p ≠ 0) (h4 : lvG m p ≠ 4) :
    lvInternW (n + 1) m p = liOneK n (lvG m p) (lvB m p) (lvInternW n m (lvA m p)) := by
  rw [lvInternW]; simp [h0, h4]
theorem liOneK_succ (hg : g = 1) : liOneK n g b (some (x, m)) = liNodeK (sinternW m x) := by
  simp [liOneK, hg]
theorem liOneK_two (hg : g ≠ 1) : liOneK n g b (some (x, m)) = liTwoK g x (lvInternW n m b) := by
  simp [liOneK, hg]
end arms

attribute [arena_grind =] liNodeK_some liTwoK_max liTwoK_imax liOneK_succ liOneK_two
grind_pattern [arena_grind] lvInternW_zero => lvInternW (n + 1) m p
grind_pattern [arena_grind] lvInternW_param => lvInternW (n + 1) m p
grind_pattern [arena_grind] lvInternW_rec => lvInternW (n + 1) m p

/-- The functions `lv_intern` calls. -/
structure LvInternProg (p : Prog) : Prop where
  lv_intern : p.lookup "lv_intern" = some lvIntern
  lv_node : p.lookup "lv_node" = some lvNode
  zero_find : p.lookup "zero_find" = some zeroFind
  zero_push : p.lookup "zero_push" = some zeroPush
  intern_zero : p.lookup "intern_zero" = some internZero
  succ_find : p.lookup "succ_find" = some succFind
  succ_push : p.lookup "succ_push" = some succPush
  intern_succ : p.lookup "intern_succ" = some internSucc
  max_find : p.lookup "max_find" = some maxFind
  max_push : p.lookup "max_push" = some maxPush
  intern_max : p.lookup "intern_max" = some internMax
  imax_find : p.lookup "imax_find" = some imaxFind
  imax_push : p.lookup "imax_push" = some imaxPush
  intern_imax : p.lookup "intern_imax" = some internImax
  param_find : p.lookup "param_find" = some paramFind
  param_push : p.lookup "param_push" = some paramPush
  intern_param : p.lookup "intern_param" = some internParam

section spec
variable (p : Prog) (hL : LvInternProg p)
include hL

/-- **`lv_intern` computes its model.** -/
theorem lvIntern_spec (n : Nat) : ∀ (s₀ : St) (q : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lv_intern" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ lvInternW n s₀.mem q = some (r.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ q
    rw [invoke_eq _ hL.lv_intern]; simp only [callFn, lvIntern]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ q
    rw [invoke_eq _ hL.lv_intern]
    simp only [callFn, lvIntern]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvNode_spec p hL.lv_node n,
        internZero_spec p hL.zero_find hL.zero_push hL.intern_zero n,
        internSucc_spec p hL.succ_find hL.succ_push hL.intern_succ n,
        internMax_spec p hL.max_find hL.max_push hL.intern_max n,
        internImax_spec p hL.imax_find hL.imax_push hL.intern_imax n,
        internParam_spec p hL.param_find hL.param_push hL.intern_param n, ih] <;>
      finish

end spec

/-! ## `lv_sub_int(u, ko, kc, vo, vc)`: substitute, then intern -/

/-- con-ron: ConRon/Arena/ExprOps.lean:2079-2087 ConRon.Arena.substLMemoAt
con-ron: ConRon/Arena/Core.lean:1942-1950 ConRon.Arena.substLevelsAt -/
def lvSubInt : FunDecl := lfn (u, ko, kc, vo, vc) locals (x, h) {
  CTL.u64[192] := 0;
  x := call lv_substl(u, ko, kc, vo, vc);
  h := call lv_intern(x);
  return h
}

/-- After the substitution: intern its result. -/
def subIntK (n : Nat) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => lvInternW n m₁ x

@[arena_grind =] theorem subIntK_some (n : Nat) (x : Word) (m₁ : Mem) :
    subIntK n (some (x, m₁)) = lvInternW n m₁ x := rfl

/-- **The model of `lv_sub_int`.** -/
def lvSubIntW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, u, ko, kc, vo, vc => subIntK n (substLW EREC POOL n (m.set64 CTL 192 0) u ko kc vo vc)

/-! ## `caps_never_zero(po, pc, us, swd, so, sc)` -/

/-- con-ron: ConRon/Arena/Core.lean:340-346 ConRon.Arena.capsNeverZero -/
@[l_impl ConRon.Arena.capsNeverZero]
def capsNeverZeroL : FunDecl := lfn (po, pc, us, swd, so, sc) locals (vo, vc, x) {
  (vo, vc) := call ls_node(us);
  CTL.u64[192] := 0;
  x := call lv_substpw(swd, so, sc, po, pc, vo, vc);
  return x
}

/-- **The model of `caps_never_zero`.** -/
def capsNeverZeroW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, po, pc, us, swd, so, sc => substPWW EREC POOL EREC n (m.set64 CTL 192 0) swd so sc po pc ((lsNodeW m us).headD 0)
    ((lsNodeW m us).tail.headD 0)

/-- The functions `lv_sub_int` and `caps_never_zero` call. -/
structure LvSubProg (p : Prog) : Prop extends LvInternProg p where
  lv_sub_int : p.lookup "lv_sub_int" = some lvSubInt
  lv_substl : p.lookup "lv_substl" = some lvSubstL
  lv_lookup : p.lookup "lv_lookup" = some lvLookupLP
  lh_mk : p.lookup "lh_mk" = some lhMk
  caps_never_zero : p.lookup "caps_never_zero" = some capsNeverZeroL
  ls_node : p.lookup "ls_node" = some lsNode
  lv_substpw : p.lookup "lv_substpw" = some lvSubstPW
  lv_spw : p.lookup "lv_spw" = some lvSpwLP
  lv_zero : p.lookup "lv_zero" = some lvZero
  lh_push : p.lookup "lh_push" = some lhPush

section spec2
variable (p : Prog) (hL : LvSubProg p)
include hL

theorem lvSubInt_spec (n : Nat) (s₀ : St) (u ko kc vo vc : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lv_sub_int" [u, ko, kc, vo, vc]
    ⦃fun r s' => LocEq s' s₀ ∧ lvSubIntW n s₀.mem u ko kc vo vc = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.lv_sub_int]
  simp only [callFn, lvSubInt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64,
        lvSubstL_spec EREC POOL p hL.lv_lookup hL.lv_node hL.lh_mk hL.lv_substl n,
        lvIntern_spec p hL.toLvInternProg n] <;>
      finish [lvSubIntW]

theorem capsNeverZero_spec (n : Nat) (s₀ : St) (po pc us swd so sc : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "caps_never_zero" [po, pc, us, swd, so, sc]
    ⦃fun r s' => LocEq s' s₀ ∧
      capsNeverZeroW n s₀.mem po pc us swd so sc = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.caps_never_zero]
  simp only [callFn, capsNeverZeroL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, lsNode_spec p hL.ls_node n,
        lvSubstPW_spec EREC POOL EREC p hL.lv_lookup hL.lv_node hL.lh_push hL.lv_zero hL.lv_spw
          hL.lv_substpw n] <;>
      finish (gen := 20) [capsNeverZeroW]

end spec2

end L.Arena
