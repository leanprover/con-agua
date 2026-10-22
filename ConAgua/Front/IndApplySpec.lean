import ConAgua.Front.IndApply
import ConAgua.Front.IndAlloc
import ConAgua.Arena.IndView

/-!
# The apply step of an `inductive` line: word models and specs, I (`validateIndD`'s side)

One model per L function of `IndApply.lean`, following the code: fuel-indexed (`n`) where the
function is recursive or calls a recursive function (the callee at `n - 1`), a match on a
callee's result a named continuation with `rfl` arm lemmas; `none` where the code aborts. The
specs are `vcgen` + `finish`. The refinements are in `IndApplyRefine*.lean`.
-/

set_option experimental.vcgen true
set_option linter.unusedSectionVars false

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Ind (eViewW eView_spec)

namespace L.Front.Ind

/-- Every function the apply step calls, at its name in `p`. -/
structure IndApplyLookups (p : Prog) : Prop where
  decl : DeclLookups p
  level : L.Arena.LevelProg p
  e_view : p.lookup "e_view" = some L.Ind.eView
  lv_equiv : p.lookup "lv_equiv" = some lvEquiv
  ifl_alloc : p.lookup "ifl_alloc" = some iflAlloc
  ifl_push : p.lookup "ifl_push" = some iflPush
  ctl_sum : p.lookup "ctl_sum" = some ctlSum
  store_fuel : p.lookup "store_fuel" = some storeFuel
  pi_result_d : p.lookup "pi_result_d" = some piResultD
  ind_pi_tele_len : p.lookup "ind_pi_tele_len" = some indPiTeleLen
  pi_sort_tele_len : p.lookup "pi_sort_tele_len" = some piSortTeleLen
  name_rec_pre : p.lookup "name_rec_pre" = some nameRecPre
  ifl_contains : p.lookup "ifl_contains" = some iflContains
  ifl_nodup : p.lookup "ifl_nodup" = some iflNodup
  ifl_find_last : p.lookup "ifl_find_last" = some iflFindLast
  vi_unsafe : p.lookup "vi_unsafe" = some viUnsafe
  vi_np_go : p.lookup "vi_np_go" = some viNpGo
  vi_nparams : p.lookup "vi_nparams" = some viNparams
  vi_map_go : p.lookup "vi_map_go" = some viMapGo
  vi_map : p.lookup "vi_map" = some viMap
  vi_ids_go : p.lookup "vi_ids_go" = some viIdsGo
  vi_listed_go : p.lookup "vi_listed_go" = some viListedGo
  vi_listed : p.lookup "vi_listed" = some viListed
  vi_ctor : p.lookup "vi_ctor" = some viCtor
  vi_order_in : p.lookup "vi_order_in" = some viOrderIn
  vi_order_go : p.lookup "vi_order_go" = some viOrderGo
  vi_order : p.lookup "vi_order" = some viOrder
  vi_k_expected : p.lookup "vi_k_expected" = some viKExpected
  vi_rec_idx : p.lookup "vi_rec_idx" = some viRecIdx
  vi_rec : p.lookup "vi_rec" = some viRec
  vi_nested : p.lookup "vi_nested" = some viNested
  vi_recs_go : p.lookup "vi_recs_go" = some viRecsGo
  vi_recs : p.lookup "vi_recs" = some viRecs
  validate_ind_d : p.lookup "validate_ind_d" = some validateIndD

/-! ## `store_fuel` -/

/-- After `ctl_sum`'s recursive call: the word added. -/
def addK (x : Word) : Option Word → Option Word
  | none => none
  | some r => some (x + r)

@[arena_grind =] theorem addK_none (x : Word) : addK x none = none := rfl
@[arena_grind =] theorem addK_some (x r : Word) : addK x (some r) = some (x + r) := rfl

/-- **The model of `ctl_sum(k, c)`.** -/
def ctlSumW : Nat → Mem → Word → Word → Option Word
  | 0, _, _, _ => none
  | n + 1, m, k, c => if c = 0 then some 0 else addK (rdW (m.arr64 CTL) k) (ctlSumW n m (k + 1) (c - 1))

/-- After the three sums. -/
def sfK (a b c : Option Word) : Option Word :=
  match a, b, c with
  | some a, some b, some c => some (a + b + c + 1)
  | _, _, _ => none

/-- **The model of `store_fuel()`**: the twenty node counts, `+ 1`. -/
def storeFuelW : Nat → Mem → Option Word
  | 0, _ => none
  | n + 1, m => sfK (ctlSumW n m 2 4) (ctlSumW n m 16 8) (ctlSumW n m 26 8)

/-! ## Telescopes -/

/-- **The model of `pi_result_d(f, h)`.** -/
def piResW : Nat → Mem → Word → Word → Option Word
  | 0, _, _, _ => none
  | n + 1, m, f, h =>
    if f = 0 then none
    else if eViewW m h = [] then none
    else if (eViewW m h).headD 0 = 6 then piResW n m (f - 1) ((eViewW m h).tail.tail.headD 0)
    else some h

/-- After `ind_pi_tele_len`'s recursive call. -/
def teleK : Option Word → Option Word
  | none => none
  | some r => some (r + 1)

@[arena_grind =] theorem teleK_none : teleK none = none := rfl
@[arena_grind =] theorem teleK_some (r : Word) : teleK (some r) = some (r + 1) := rfl

/-- **The model of `ind_pi_tele_len(f, h)`.** -/
def teleW : Nat → Mem → Word → Word → Option Word
  | 0, _, _, _ => none
  | n + 1, m, f, h =>
    if f = 0 then none
    else if eViewW m h = [] then none
    else if (eViewW m h).headD 0 = 6 then teleK (teleW n m (f - 1) ((eViewW m h).tail.tail.headD 0))
    else some 0

/-- After `pi_sort_tele_len`'s recursive call. -/
def stK : Option (Word × Word) → Option (Word × Word)
  | none => none
  | some (ok, r) => if ok = 0 then some (0, 0) else some (1, r + 1)

@[arena_grind =] theorem stK_none : stK none = none := rfl
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

/-- `name_rec_pre`'s `str` arm, at the node's first word `k`: its string is `rec`. -/
def nrpStr (m : Mem) (k : Word) : Option (Word × Word) :=
  if rdW (m.arr64 NSREC) (k + 2) ≠ 3 then some (0, 0)
  else if rdW (m.arr64 POOL) (rdW (m.arr64 NSREC) (k + 1)) = 114 ∧
      rdW (m.arr64 POOL) (rdW (m.arr64 NSREC) (k + 1) + 1) = 101 ∧
      rdW (m.arr64 POOL) (rdW (m.arr64 NSREC) (k + 1) + 2) = 99 then some (1, rdW (m.arr64 NSREC) k)
  else some (0, 0)

/-- **The model of `name_rec_pre(h)`**: `(1, T)` for a `str` node `T.rec`, else `(0, 0)`. -/
def nrpW (m : Mem) (h : Word) : Option (Word × Word) :=
  if 4294967295 < h then none
  else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if h >>> 28 = 0 then (if rdW (m.arr64 CTL) (34 + tierW h) ≤ idxW h then none else some (0, 0))
  else if h >>> 28 = 2 then (if rdW (m.arr64 CTL) (38 + tierW h) ≤ idxW h then none else some (0, 0))
  else if h >>> 28 ≠ 1 then none
  else if rdW (m.arr64 CTL) (36 + tierW h) ≤ idxW h then none
  else nrpStr m (idxW h * 8 + tierW h * 4)

/-! ## `IFL` slices -/

/-- **The model of `ifl_contains(o, l, x, j)`.** -/
def containsW : Nat → Mem → Word → Word → Word → Word → Option Word
  | 0, _, _, _, _, _ => none
  | n + 1, m, o, l, x, j =>
    if l ≤ j then some 0
    else if rdW (m.arr64 IFL) (o + j) = x then some 1
    else containsW n m o l x (j + 1)

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

/-- **The model of `ifl_find_last(o, x, j)`**: `(ok, k)`. -/
def findLastW : Nat → Mem → Word → Word → Word → Option (Word × Word)
  | 0, _, _, _, _ => none
  | n + 1, m, o, x, j =>
    if j = 0 then some (0, 0)
    else if rdW (m.arr64 IFL) (o + j - 1) = x then some (1, j - 1)
    else findLastW n m o x (j - 1)

/-! ## Specs -/

section specs
variable (p : Prog) (hL : IndApplyLookups p)
include hL

theorem ctlSum_spec (n : Nat) : ∀ (s₀ : St) (k c : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ctl_sum" [k, c]
    ⦃fun r s' => s' = s₀ ∧ ctlSumW n s₀.mem k c = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ k c; rw [invoke_eq _ hL.ctl_sum]; simp only [callFn, ctlSum]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ k c
    rw [invoke_eq _ hL.ctl_sum]
    simp only [callFn, ctlSum]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [ctlSumW]

theorem storeFuel_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "store_fuel" []
    ⦃fun r s' => s' = s₀ ∧ storeFuelW n s₀.mem = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hL.store_fuel]
  simp only [callFn, storeFuel]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ctlSum_spec p hL n] <;>
        finish [storeFuelW, sfK]

theorem piRes_spec (n : Nat) : ∀ (s₀ : St) (f h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_result_d" [f, h]
    ⦃fun r s' => s' = s₀ ∧ piResW n s₀.mem f h = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ f h; rw [invoke_eq _ hL.pi_result_d]; simp only [callFn, piResultD]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ f h
    rw [invoke_eq _ hL.pi_result_d]
    simp only [callFn, piResultD]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        eView_spec p hL.e_view n] <;> finish [piResW]

theorem tele_spec (n : Nat) : ∀ (s₀ : St) (f h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_pi_tele_len" [f, h]
    ⦃fun r s' => s' = s₀ ∧ teleW n s₀.mem f h = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ f h; rw [invoke_eq _ hL.ind_pi_tele_len]; simp only [callFn, indPiTeleLen]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ f h
    rw [invoke_eq _ hL.ind_pi_tele_len]
    simp only [callFn, indPiTeleLen]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        eView_spec p hL.e_view n] <;> finish [teleW]

theorem sortTele_spec (n : Nat) : ∀ (s₀ : St) (f h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_sort_tele_len" [f, h]
    ⦃fun r s' => s' = s₀ ∧ sortTeleW n s₀.mem f h = some (r.headD 0, r.tail.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ f h; rw [invoke_eq _ hL.pi_sort_tele_len]; simp only [callFn, piSortTeleLen]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ f h
    rw [invoke_eq _ hL.pi_sort_tele_len]
    simp only [callFn, piSortTeleLen]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        eView_spec p hL.e_view n] <;> finish [sortTeleW]

set_option maxHeartbeats 1600000 in
theorem nrp_spec (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "name_rec_pre" [h]
    ⦃fun r s' => s' = s₀ ∧ nrpW s₀.mem h = some (r.headD 0, r.tail.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hL.name_rec_pre]
  simp only [callFn, nameRecPre]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64] <;> finish [nrpW, nrpStr, tierW, idxW]

theorem contains_spec (n : Nat) : ∀ (s₀ : St) (o l x j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ifl_contains" [o, l, x, j]
    ⦃fun r s' => s' = s₀ ∧ containsW n s₀.mem o l x j = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l x j; rw [invoke_eq _ hL.ifl_contains]; simp only [callFn, iflContains]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l x j
    rw [invoke_eq _ hL.ifl_contains]
    simp only [callFn, iflContains]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [containsW]

theorem nodup_spec (n : Nat) : ∀ (s₀ : St) (o l j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ifl_nodup" [o, l, j]
    ⦃fun r s' => s' = s₀ ∧ nodupW n s₀.mem o l j = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l j; rw [invoke_eq _ hL.ifl_nodup]; simp only [callFn, iflNodup]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l j
    rw [invoke_eq _ hL.ifl_nodup]
    simp only [callFn, iflNodup]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        contains_spec p hL n] <;> finish [nodupW]

theorem findLast_spec (n : Nat) : ∀ (s₀ : St) (o x j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ifl_find_last" [o, x, j]
    ⦃fun r s' => s' = s₀ ∧ findLastW n s₀.mem o x j = some (r.headD 0, r.tail.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ o x j; rw [invoke_eq _ hL.ifl_find_last]; simp only [callFn, iflFindLast]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o x j
    rw [invoke_eq _ hL.ifl_find_last]
    simp only [callFn, iflFindLast]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [findLastW]

end specs


/-! ## `validateIndD`'s loops: models -/

/-- A table lookup (`name_get`, `expr_get`): the handle word of a bound id. -/
def lkW (m : Mem) (b : ArrId) (x : Word) : Option Word :=
  if tblOK m b x = true then some (tblW m b x) else none

/-- **The model of `vi_unsafe(to, tn, j)`.** -/
def unsafeW : Nat → Mem → Word → Word → Word → Option Unit
  | 0, _, _, _, _ => none
  | n + 1, m, to, tn, j =>
    if tn ≤ j then some ()
    else if rdW (m.arr64 IFR) (to + 11 * j + 7) ≠ 0 then none
    else unsafeW n m to tn (j + 1)

/-- **The model of `vi_np_go(to, tn, d, j)`.** -/
def npGoW : Nat → Mem → Word → Word → Word → Word → Option Unit
  | 0, _, _, _, _, _ => none
  | n + 1, m, to, tn, d, j =>
    if tn ≤ j then some ()
    else if rdW (m.arr64 IFR) (to + 11 * j + 10) ≠ d then none
    else npGoW n m to tn d (j + 1)

/-- After a check that returns nothing: the word `x`. -/
def unitK (x : Word) : Option Unit → Option Word
  | none => none
  | some _ => some x

@[arena_grind =] theorem unitK_none (x : Word) : unitK x none = none := rfl
@[arena_grind =] theorem unitK_some (x : Word) (u : Unit) : unitK x (some u) = some x := rfl

/-- **The model of `vi_nparams(to, tn)`.** -/
def nparamsW : Nat → Mem → Word → Word → Option Word
  | 0, _, _, _ => none
  | n + 1, m, to, tn =>
    if tn = 0 then some 0
    else unitK (rdW (m.arr64 IFR) (to + 10)) (npGoW n m to tn (rdW (m.arr64 IFR) (to + 10)) 0)

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

/-- **The model of `vi_ids_go(o, l, k)`.** -/
def idsGoW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, o, l, k =>
    if l ≤ k then some m
    else restK (fun m₁ => idsGoW n m₁ o l (k + 1)) (lkPushK m (lkW m NID (rdW (m.arr64 IFL) (o + k))))

/-- After a call that returns only its memory: the rest. -/
def memK {α : Type} (rest : Mem → Option α) : Option Mem → Option α
  | none => none
  | some m => rest m

@[arena_grind =] theorem memK_none {α : Type} (rest : Mem → Option α) : memK rest none = none := rfl
@[arena_grind =] theorem memK_some {α : Type} (rest : Mem → Option α) (m : Mem) :
    memK rest (some m) = rest m := rfl

/-- **The model of `vi_listed_go(to, tn, j)`.** -/
def listedGoW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, to, tn, j =>
    if tn ≤ j then some m
    else memK (fun m₁ => listedGoW n m₁ to tn (j + 1))
      (idsGoW n m (rdW (m.arr64 IFR) (to + 11 * j + 3)) (rdW (m.arr64 IFR) (to + 11 * j + 4)) 0)

/-- After `vi_listed_go`: the slice from `lo` to the top. -/
def listedK (lo : Word) : Option Mem → Option ((Word × Word) × Mem)
  | none => none
  | some m => some ((lo, rdW (m.arr64 IFL) 0 + 1 - lo), m)

@[arena_grind =] theorem listedK_none (lo : Word) : listedK lo none = none := rfl
@[arena_grind =] theorem listedK_some (lo : Word) (m : Mem) :
    listedK lo (some m) = some ((lo, rdW (m.arr64 IFL) 0 + 1 - lo), m) := rfl

/-- **The model of `vi_listed(to, tn)`.** -/
def listedW : Nat → Mem → Word → Word → Option ((Word × Word) × Mem)
  | 0, _, _, _ => none
  | n + 1, m, to, tn => allocK (fun lo m₁ => listedK lo (listedGoW n m₁ to tn 0)) (allocW m IFL 0)

/-! ## `validateIndD`'s loops: specs -/

section specs2
variable (p : Prog) (hL : IndApplyLookups p)
include hL

theorem unsafe_spec (n : Nat) : ∀ (s₀ : St) (to tn j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_unsafe" [to, tn, j]
    ⦃fun _ s' => s' = s₀ ∧ unsafeW n s₀.mem to tn j = some (); ⊤⦄ := by
  induction n with
  | zero => intro s₀ to tn j; rw [invoke_eq _ hL.vi_unsafe]; simp only [callFn, viUnsafe]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ to tn j
    rw [invoke_eq _ hL.vi_unsafe]
    simp only [callFn, viUnsafe]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [unsafeW]

theorem npGo_spec (n : Nat) : ∀ (s₀ : St) (to tn d j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_np_go" [to, tn, d, j]
    ⦃fun _ s' => s' = s₀ ∧ npGoW n s₀.mem to tn d j = some (); ⊤⦄ := by
  induction n with
  | zero => intro s₀ to tn d j; rw [invoke_eq _ hL.vi_np_go]; simp only [callFn, viNpGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ to tn d j
    rw [invoke_eq _ hL.vi_np_go]
    simp only [callFn, viNpGo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [npGoW]

theorem nparams_spec (n : Nat) (s₀ : St) (to tn : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_nparams" [to, tn]
    ⦃fun r s' => s' = s₀ ∧ nparamsW n s₀.mem to tn = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hL.vi_nparams]
  simp only [callFn, viNparams]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, npGo_spec p hL n] <;>
        finish [nparamsW]

theorem mapGo_spec (n : Nat) : ∀ (s₀ : St) (o l sz s f j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_map_go" [o, l, sz, s, f, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ mapGoW n s₀.mem o l sz s f j = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l sz s f j; rw [invoke_eq _ hL.vi_map_go]; simp only [callFn, viMapGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l sz s f j
    rw [invoke_eq _ hL.vi_map_go]
    simp only [callFn, viMapGo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        nameGet_spec p hL.decl.expr.front n, exprGet_spec p hL.decl.expr n,
        iflPush_spec p hL.ifl_alloc hL.ifl_push n] <;> finish [mapGoW, mapLk, lkW]

theorem map_spec (n : Nat) (s₀ : St) (o l sz s f : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_map" [o, l, sz, s, f]
    ⦃fun r s' => LocEq s' s₀ ∧ mapW n s₀.mem o l sz s f = some ((r.headD 0, r.tail.headD 0), s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.vi_map]
  simp only [callFn, viMap]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        iflAlloc_spec p hL.ifl_alloc n, mapGo_spec p hL n] <;> finish [mapW]

theorem idsGo_spec (n : Nat) : ∀ (s₀ : St) (o l k : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_ids_go" [o, l, k]
    ⦃fun _ s' => LocEq s' s₀ ∧ idsGoW n s₀.mem o l k = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l k; rw [invoke_eq _ hL.vi_ids_go]; simp only [callFn, viIdsGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l k
    rw [invoke_eq _ hL.vi_ids_go]
    simp only [callFn, viIdsGo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        nameGet_spec p hL.decl.expr.front n,
        iflPush_spec p hL.ifl_alloc hL.ifl_push n] <;> finish [idsGoW, lkW]

theorem listedGo_spec (n : Nat) : ∀ (s₀ : St) (to tn j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_listed_go" [to, tn, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ listedGoW n s₀.mem to tn j = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ to tn j; rw [invoke_eq _ hL.vi_listed_go]; simp only [callFn, viListedGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ to tn j
    rw [invoke_eq _ hL.vi_listed_go]
    simp only [callFn, viListedGo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        idsGo_spec p hL n] <;> finish [listedGoW]

theorem listed_spec (n : Nat) (s₀ : St) (to tn : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_listed" [to, tn]
    ⦃fun r s' => LocEq s' s₀ ∧ listedW n s₀.mem to tn = some ((r.headD 0, r.tail.headD 0), s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.vi_listed]
  simp only [callFn, viListed]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        iflAlloc_spec p hL.ifl_alloc n, listedGo_spec p hL n] <;> finish [listedW]

end specs2

end L.Front.Ind
