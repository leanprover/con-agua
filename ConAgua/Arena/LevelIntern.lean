import ConAgua.Arena.LevelSubstLP
import ConAgua.Arena.LevelArena
import ConAgua.Arena.Tiers
import ConAgua.Arena.WhnfBase
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
* `lv_sub_int(u, ko, kc, vo, vc)`: a fresh heap (`CTL[192] := 0`, as `lvl_eq`), `lp_substl` with
  the keys the `EREC` name slice `(ko, kc)` and the values the `POOL` level-list slice
  `(vo, vc)`, then `lv_intern`: `internLevel (Level.subst ks vs l)`.

The keys and values arrays of lane `levels`' generic functions are fixed here, under this
family's own names (`LevelSubstLP.lean`): `lp_lookup` (keys on the spine stack, copied there by
`keys_push`, so that lane `induct`'s `IW` slices and the record pool's slices are served by one
function; values in the pool), `lp_substl`, `lp_spw` (`caps_never_zero`'s datum names in `EREC`),
`lp_substpw`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `lv_intern(p)` -/

/-- con-ron: ConRon/Arena/Monad.lean:470-487 ConRon.Arena.internLevel -/
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

/-- con-ron: ConRon/Arena/ExprOps.lean:2071-2086 ConRon.Arena.substLMemoAt
con-ron: ConRon/Arena/Core.lean:1940-1950 ConRon.Arena.substLevelsAt -/
def lvSubInt : FunDecl := lfn (u, ko, kc, vo, vc) locals (x, h) {
  CTL.u64[192] := 0;
  x := call lp_substl(u, ko, kc, vo, vc);
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
  | n + 1, m, u, ko, kc, vo, vc => subIntK n (substLW SPN POOL n (m.set64 CTL 192 0) u ko kc vo vc)

/-! ## `keys_push(src, l)`: a record-pool name slice onto the spine stack -/

/-- con-ron: none — the substitution's keys copied onto the spine stack (`lp_lookup`'s key array) -/
def ekCopy : FunDecl := lfn (s, d, l) locals (r) {
  if l == 0 { return 0 };
  SPN.u64[d] := EREC.u64[s];
  r := call ek_copy(s + 1, d + 1, l - 1);
  return r
}

/-- **The model of `ek_copy`.** -/
def ekCopyW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, s, d, l =>
    if l = 0 then some m else ekCopyW n (m.set64 SPN d (rdW (m.arr64 EREC) s)) (s + 1) (d + 1) (l - 1)

theorem ekCopyW_zero (n : Nat) (m : Mem) (s d l : Word) (h : l = 0) :
    ekCopyW (n + 1) m s d l = some m := by simp [ekCopyW, h]
theorem ekCopyW_succ (n : Nat) (m : Mem) (s d l : Word) (h : l ≠ 0) :
    ekCopyW (n + 1) m s d l = ekCopyW n (m.set64 SPN d (rdW (m.arr64 EREC) s)) (s + 1) (d + 1) (l - 1) := by
  simp [ekCopyW, h]
grind_pattern [arena_grind] ekCopyW_zero => ekCopyW (n + 1) m s d l
grind_pattern [arena_grind] ekCopyW_succ => ekCopyW (n + 1) m s d l

/-- con-ron: none — the substitution's keys copied onto the spine stack (`lp_lookup`'s key array) -/
def keysPush : FunDecl := lfn (po, pc) locals (b, r) {
  b := CTL.u64[136];
  if len(SPN.u64) < b { abort };
  if len(SPN.u64) - b < pc { abort };
  r := call ek_copy(po, b, pc);
  CTL.u64[136] := b + pc;
  return b
}

/-- After the copy: the top raised. -/
def kpK (b pc : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m₁ => some (b, m₁.set64 CTL 136 (b + pc))

@[arena_grind =] theorem kpK_some (b pc : Word) (m₁ : Mem) :
    kpK b pc (some m₁) = some (b, m₁.set64 CTL 136 (b + pc)) := rfl

/-- **The model of `keys_push`.** -/
def keysPushW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, po, pc =>
    if m.len64 SPN < spTop m then none
    else if m.len64 SPN - spTop m < pc then none
    else kpK (spTop m) pc (ekCopyW n m po (spTop m) pc)

theorem lvSubIntW_succ (n : Nat) (m : Mem) (u ko kc vo vc : Word) :
    lvSubIntW (n + 1) m u ko kc vo vc = subIntK n (substLW SPN POOL n (m.set64 CTL 192 0) u ko kc vo vc) := by
  rw [lvSubIntW]
attribute [arena_grind =] lvSubIntW_succ

/-! ## `caps_never_zero(po, pc, us, swd, so, sc)` -/

/-- con-ron: ConRon/Arena/Core.lean:340-346 ConRon.Arena.capsNeverZero -/
@[l_impl ConRon.Arena.capsNeverZero]
def capsNeverZeroL : FunDecl := lfn (po, pc, us, swd, so, sc) locals (vo, vc, b, x) {
  (vo, vc) := call ls_node(us);
  b := call keys_push(po, pc);
  CTL.u64[192] := 0;
  x := call lp_substpw(swd, so, sc, b, pc, vo, vc);
  CTL.u64[136] := b;
  return x
}

/-- After the substitution: the stack top put back. -/
def capsK2 (b : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₂) => some (x, m₂.set64 CTL 136 b)

/-- After the keys: the substitution. -/
def capsK1 (n : Nat) (swd so sc pc vo vc : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b, m₁) => capsK2 b (substPWW SPN POOL EREC n (m₁.set64 CTL 192 0) swd so sc b pc vo vc)

@[arena_grind =] theorem capsK2_some (b x : Word) (m₂ : Mem) :
    capsK2 b (some (x, m₂)) = some (x, m₂.set64 CTL 136 b) := rfl
@[arena_grind =] theorem capsK1_some (n : Nat) (swd so sc pc vo vc b : Word) (m₁ : Mem) :
    capsK1 n swd so sc pc vo vc (some (b, m₁)) =
      capsK2 b (substPWW SPN POOL EREC n (m₁.set64 CTL 192 0) swd so sc b pc vo vc) := rfl

/-- **The model of `caps_never_zero`** (none on a handle `ls_node` aborts on). -/
def capsNeverZeroW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, po, pc, us, swd, so, sc =>
    if lsNodeW m us = [] then none else
    capsK1 n swd so sc pc ((lsNodeW m us).headD 0) ((lsNodeW m us).tail.headD 0) (keysPushW n m po pc)

/-- The functions `lv_sub_int` and `caps_never_zero` call. -/
structure LvSubProg (p : Prog) : Prop extends LvInternProg p where
  lv_sub_int : p.lookup "lv_sub_int" = some lvSubInt
  lp_substl : p.lookup "lp_substl" = some lpSubstL
  lp_lookup : p.lookup "lp_lookup" = some lpLookup
  lh_mk : p.lookup "lh_mk" = some lhMk
  caps_never_zero : p.lookup "caps_never_zero" = some capsNeverZeroL
  keys_push : p.lookup "keys_push" = some keysPush
  ek_copy : p.lookup "ek_copy" = some ekCopy
  ls_node : p.lookup "ls_node" = some lsNode
  lp_substpw : p.lookup "lp_substpw" = some lpSubstPW
  lp_spw : p.lookup "lp_spw" = some lpSpw
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
        lpSubstL_spec p hL.lp_lookup hL.lv_node hL.lh_mk hL.lp_substl n,
        lvIntern_spec p hL.toLvInternProg n] <;>
      finish

theorem ekCopy_spec (n : Nat) : ∀ (s₀ : St) (s d l : Word),
    ⦃fun st => st = s₀⦄
    invoke p (exec p n) "ek_copy" [s, d, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ ekCopyW n s₀.mem s d l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ s d l; rw [invoke_eq _ hL.ek_copy]; simp only [callFn, ekCopy]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ s d l
    rw [invoke_eq _ hL.ek_copy]
    simp only [callFn, ekCopy]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish

theorem keysPush_spec (n : Nat) (s₀ : St) (po pc : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "keys_push" [po, pc]
    ⦃fun r s' => LocEq s' s₀ ∧ keysPushW n s₀.mem po pc = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.keys_push]
  simp only [callFn, keysPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        ekCopy_spec p hL n] <;>
      finish [keysPushW, spTop]

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
        keysPush_spec p hL n,
        lpSubstPW_spec p hL.lp_lookup hL.lv_node hL.lh_push hL.lv_zero hL.lp_spw
          hL.lp_substpw n] <;>
      finish (gen := 20) [capsNeverZeroW]

end spec2

end L.Arena
