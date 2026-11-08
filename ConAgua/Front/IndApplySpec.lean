module

public import ConAgua.Front.IndApply
import ConAgua.L.ModelGen
public import ConAgua.Arena.LevelEquiv
public import ConAgua.Front.IndAlloc
public import ConAgua.Arena.IndView
public import ConAgua.Front.ApplyDecl
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LdRd
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Front.IndApply

@[expose] public section

/-!
# The apply step of an `inductive` line: word models and specs, I (`validateIndD`'s side)

One model per L function of `IndApply.lean`, following the code: fuel-indexed (`n`) where the
function is recursive or calls a recursive function (the callee at `n - 1`), a match on a
callee's result a named continuation with `rfl` arm lemmas; `none` where the code aborts. The
specs are `vcgen` + `finish`. The refinements are in `IndApplyRefine*.lean`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Ind (eViewW eView_spec)

namespace L.Front.Ind

/-! ## `store_fuel` -/

/-- After `ctl_sum`'s recursive call: the word added. -/
def addK (x : Word) : Option Word → Option Word
  | none => none
  | some r => some (x + r)

@[arena_grind =] theorem addK_some (x r : Word) : addK x (some r) = some (x + r) := by
  sorry

/-- After the three sums. -/
def sfK (a b c : Option Word) : Option Word :=
  match a, b, c with
  | some a, some b, some c => some (a + b + c + 1)
  | _, _, _ => none

include hL

/-- After `ind_pi_tele_len`'s recursive call. -/
def teleK : Option Word → Option Word
  | none => none
  | some r => some (r + 1)

@[arena_grind =] theorem teleK_some (r : Word) : teleK (some r) = some (r + 1) := rfl

/-- **The model of `ind_pi_tele_len(f, h)`.** -/
def teleW : Nat → Mem → Word → Word → Option Word
  | 0, _, _, _ => none
  | n + 1, m, f, h =>
    if f = 0 then none
    else if eViewW m h = [] then none
    else if (eViewW m h).headD 0 = 6 then teleK (teleW n m (f - 1) ((eViewW m h).tail.tail.headD 0))
    else some 0

section
include hL

/-- After `pi_sort_tele_len`'s recursive call. -/
def stK : Option (Word × Word) → Option (Word × Word)
  | none => none
  | some (ok, r) => if ok = 0 then some (0, 0) else some (1, r + 1)

@[arena_grind =] theorem stK_some (ok r : Word) :
    stK (some (ok, r)) = if ok = 0 then some (0, 0) else some (1, r + 1) := rfl

/-- **The model of `pi_sort_tele_len(f, h)`**: `(ok, n)`. -/
def sortTeleW : Nat → Mem → Word → Word → Option (Word × Word)
  | 0, _, _, _ => none
  | n + 1, m, f, h =>
    if f = 0 then none
    else if eViewW m h = [] then none
    else if (eViewW m h).headD 0 = 6 then stK (sortTeleW n m (f - 1) ((eViewW m h).tail.tail.headD 0))
    else if (eViewW m h).headD 0 = 2 then some (1, 0)
    else some (0, 0)

section
include hL

/-- `name_rec_pre`'s `str` arm, at node `i` of tier `t`: its string is `rec`. -/
def nrpStr (m : Mem) (t i : Word) : Option (Word × Word) :=
  if tfld m NSTR t i 2 ≠ 3 then some (0, 0)
  else if prd m (tfld m NSTR t i 1) = 114 ∧
      prd m (tfld m NSTR t i 1 + 1) = 101 ∧
      prd m (tfld m NSTR t i 1 + 2) = 99 then some (1, tfld m NSTR t i 0)
  else some (0, 0)

/-- **The model of `name_rec_pre(h)`**: `(1, T)` for a `str` node `T.rec`, else `(0, 0)`. -/
def nrpW (m : Mem) (h : Word) : Option (Word × Word) :=
  if 4294967295 < h then none
  else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tagW h = 0 then (if tcnt m NANON (tierW h) ≤ idxW h then none else some (0, 0))
  else if tagW h = 2 then (if tcnt m NNUM (tierW h) ≤ idxW h then none else some (0, 0))
  else if tagW h ≠ 1 then none
  else if tcnt m NSTR (tierW h) ≤ idxW h then none
  else nrpStr m (tierW h) (idxW h)

section
include hL

set_option maxHeartbeats 1600000 in
/-! ## `IFL` slices -/

/-- **The model of `ifl_contains(o, l, x, j)`.** -/
def containsW : Nat → Mem → Word → Word → Word → Word → Option Word
  | 0, _, _, _, _, _ => none
  | n + 1, m, o, l, x, j =>
    if l ≤ j then some 0
    else if rdW (m.arr64 IFL) (o + j) = x then some 1
    else containsW n m o l x (j + 1)

section
include hL

/-- After `ifl_nodup`'s `ifl_contains`: `rest` the recursive call's result. -/
def nodupK (rest : Option Word) : Option Word → Option Word
  | none => none
  | some b => if b ≠ 0 then some 0 else rest

@[arena_grind =] theorem nodupK_none (rest : Option Word) : nodupK rest none = none := rfl
@[arena_grind =] theorem nodupK_some (rest : Option Word) (b : Word) :
    nodupK rest (some b) = if b ≠ 0 then some 0 else rest := rfl

/-- **The model of `ifl_nodup(o, l, j)`.** -/
def nodupW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, o, l, j =>
    if l ≤ j then some 1
    else nodupK (nodupW n m o l (j + 1)) (containsW n m o l (rdW (m.arr64 IFL) (o + j)) (j + 1))

section
include hL

/-- **The model of `ifl_find_last(o, x, j)`**: `(ok, k)`. -/
def findLastW : Nat → Mem → Word → Word → Word → Option (Word × Word)
  | 0, _, _, _, _ => none
  | n + 1, m, o, x, j =>
    if j = 0 then some (0, 0)
    else if rdW (m.arr64 IFL) (o + j - 1) = x then some (1, j - 1)
    else findLastW n m o x (j - 1)

section
include hL

/-! ## `validateIndD`'s loops: models -/

/-- A table lookup (`name_get`, `expr_get`): the handle word of a bound id. -/
def lkW (m : Mem) (b : ArrId) (x : Word) : Option Word :=
  if tblOK m b x = true then some (tblW m b x) else none

/-- After a call returning a list of words: the list and the memory. -/
def lK {α : Type} (rest : List Word → Mem → Option α) : Option (List Word × Mem) → Option α
  | none => none
  | some (r, m) => rest r m

@[arena_grind =] theorem lK_none {α : Type} (rest : List Word → Mem → Option α) : lK rest none = none := rfl
@[arena_grind =] theorem lK_some {α : Type} (rest : List Word → Mem → Option α) (r : List Word) (m : Mem) :
    lK rest (some (r, m)) = rest r m := rfl

/-- After a lookup: the push of the handle. -/
def lkPushK (m : Mem) : Option Word → Option (Word × Mem)
  | none => none
  | some h => pushLW m h

@[arena_grind =] theorem lkPushK_none (m : Mem) : lkPushK m none = none := rfl
@[arena_grind =] theorem lkPushK_some (m : Mem) (h : Word) : lkPushK m (some h) = pushLW m h := rfl

/-- After a push: the rest of the loop, on the memory after. -/
def restK (rest : Mem → Option Mem) : Option (Word × Mem) → Option Mem
  | none => none
  | some (_, m) => rest m

@[arena_grind =] theorem restK_none (rest : Mem → Option Mem) : restK rest none = none := rfl
@[arena_grind =] theorem restK_some (rest : Mem → Option Mem) (o : Word) (m : Mem) :
    restK rest (some (o, m)) = rest m := rfl

/-- The lookup of `vi_map_go`: `name_get` (`f = 0`) or `expr_get`. -/
def mapLk (m : Mem) (f x : Word) : Option Word := if f = 0 then lkW m NID x else lkW m EID x

/-- **The model of `vi_map_go(o, l, sz, s, f, j)`.** -/
def mapGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, o, l, sz, s, f, j =>
    if l ≤ j then some m
    else restK (fun m₁ => mapGoW n m₁ o l sz s f (j + 1))
      (lkPushK m (mapLk m f (rdW (m.arr64 IFR) (o + sz * j + s))))

/-- After `ifl_alloc(0)` and a loop: the slice `(lo, x)` and the memory. -/
def sliceK (lo x : Word) : Option Mem → Option ((Word × Word) × Mem)
  | none => none
  | some m => some ((lo, x), m)

@[arena_grind =] theorem sliceK_none (lo x : Word) : sliceK lo x none = none := rfl
@[arena_grind =] theorem sliceK_some (lo x : Word) (m : Mem) :
    sliceK lo x (some m) = some ((lo, x), m) := rfl

/-- After `ifl_alloc`: the rest, given the index and the memory. -/
def allocK {α : Type} (rest : Word → Mem → Option α) : Option (Word × Mem) → Option α
  | none => none
  | some (o, m) => rest o m

@[arena_grind =] theorem allocK_none {α : Type} (rest : Word → Mem → Option α) :
    allocK rest none = none := rfl
@[arena_grind =] theorem allocK_some {α : Type} (rest : Word → Mem → Option α) (o : Word) (m : Mem) :
    allocK rest (some (o, m)) = rest o m := rfl

/-- **The model of `vi_map(o, l, sz, s, f)`**: the slice `(lo, l)`. -/
def mapW : Nat → Mem → Word → Word → Word → Word → Word → Option ((Word × Word) × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, o, l, sz, s, f =>
    allocK (fun lo m₁ => sliceK lo l (mapGoW n m₁ o l sz s f 0)) (allocW m IFL 0)

/-- After a call that returns only its memory: the rest. -/
def mK {α : Type} (rest : Mem → Option α) : Option Mem → Option α
  | none => none
  | some m => rest m

@[arena_grind =] theorem mK_none {α : Type} (rest : Mem → Option α) : mK rest none = none := rfl
@[arena_grind =] theorem mK_some {α : Type} (rest : Mem → Option α) (m : Mem) :
    mK rest (some m) = rest m := by
  sorry

/-- After `vi_listed_go`: the slice from `lo` to the top. -/
def listedK (lo : Word) : Option Mem → Option ((Word × Word) × Mem)
  | none => none
  | some m => some ((lo, rdW (m.arr64 IFL) 0 + 1 - lo), m)

@[arena_grind =] theorem listedK_none (lo : Word) : listedK lo none = none := rfl
@[arena_grind =] theorem listedK_some (lo : Word) (m : Mem) :
    listedK lo (some m) = some ((lo, rdW (m.arr64 IFL) 0 + 1 - lo), m) := rfl

/-! ## `validateIndD`'s loops: specs -/

section specs2
include hL

end specs2

/-- After a call that returns a word: the rest. -/
def wK {α : Type} (rest : Word → Option α) : Option Word → Option α
  | none => none
  | some x => rest x

@[arena_grind =] theorem wK_none {α : Type} (rest : Word → Option α) : wK rest none = none := rfl
@[arena_grind =] theorem wK_some {α : Type} (rest : Word → Option α) (x : Word) :
    wK rest (some x) = rest x := rfl

/-- After a call that returns two words and its memory: the rest. -/
def pmK {α : Type} (rest : Word → Word → Mem → Option α) : Option ((Word × Word) × Mem) → Option α
  | none => none
  | some ((a, b), m) => rest a b m

@[arena_grind =] theorem pmK_none {α : Type} (rest : Word → Word → Mem → Option α) :
    pmK rest none = none := rfl
@[arena_grind =] theorem pmK_some {α : Type} (rest : Word → Word → Mem → Option α) (a b : Word)
    (m : Mem) : pmK rest (some ((a, b), m)) = rest a b m := rfl

/-- `vi_k_expected` after `lv_equiv`. -/
def keK3 (c : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (q, m) => if rdW (m.arr64 IFR) (c + 4) = 0 ∧ q = 2 then some (2, m) else some (1, m)

@[arena_grind =] theorem keK3_none (c : Word) : keK3 c none = none := rfl
@[arena_grind =] theorem keK3_some (c q : Word) (m : Mem) :
    keK3 c (some (q, m)) = if rdW (m.arr64 IFR) (c + 4) = 0 ∧ q = 2 then some (2, m) else some (1, m) :=
  rfl

/-- `vi_k_expected` after `lh_mk`. -/
def keK2 (n : Nat) (c s : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (z, m) => keK3 c (equivW n m s z)

@[arena_grind =] theorem keK2_none (n : Nat) (c s : Word) : keK2 n c s none = none := rfl
@[arena_grind =] theorem keK2_some (n : Nat) (c s z : Word) (m : Mem) :
    keK2 n c s (some (z, m)) = keK3 c (equivW n m s z) := rfl

/-- `vi_k_expected` after `pi_result_d`. -/
def keK1 (n : Nat) (m : Mem) (oo : Word) : Option Word → Option (Word × Mem)
  | none => none
  | some r =>
    if eViewW m r = [] then none
    else if (eViewW m r).headD 0 ≠ 2 then some (0, m)
    else keK2 n (rdW (m.arr64 IFL) oo) ((eViewW m r).tail.headD 0) (lhMkW (m.set64 CTL 192 0) 0 0 0)

@[arena_grind =] theorem keK1_none (n : Nat) (m : Mem) (oo : Word) : keK1 n m oo none = none := rfl
@[arena_grind =] theorem keK1_some (n : Nat) (m : Mem) (oo r : Word) :
    keK1 n m oo (some r) =
      if eViewW m r = [] then none
      else if (eViewW m r).headD 0 ≠ 2 then some (0, m)
      else keK2 n (rdW (m.arr64 IFL) oo) ((eViewW m r).tail.headD 0) (lhMkW (m.set64 CTL 192 0) 0 0 0) := rfl

/-- **The model of `vi_nested(to, tn, j)`.** -/
def nestedW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, to, tn, j =>
    if tn ≤ j then some 0
    else if rdW (m.arr64 IFR) (to + 11 * j + 9) ≠ 0 then some 1
    else nestedW n m to tn (j + 1)

section specs4
include hL

end specs4

end L.Front.Ind
