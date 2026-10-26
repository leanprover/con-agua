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
  vi_tail : p.lookup "vi_tail" = some viTail
  validate_ind_d : p.lookup "validate_ind_d" = some validateIndD

/-! ## `store_fuel` -/

/-- After `ctl_sum`'s recursive call: the word added. -/
def addK (x : Word) : Option Word → Option Word
  | none => none
  | some r => some (x + r)

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
  else if h >>> 28 = 0 then (if tcnt m NANON (tierW h) ≤ idxW h then none else some (0, 0))
  else if h >>> 28 = 2 then (if tcnt m NNUM (tierW h) ≤ idxW h then none else some (0, 0))
  else if h >>> 28 ≠ 1 then none
  else if tcnt m NSTR (tierW h) ≤ idxW h then none
  else nrpStr m (tierW h) (idxW h)

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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, evalE_tld, tld, evalE_cnt, tcntM,
        evalE_tierE, evalE_idxE] <;> finish [nrpW, nrpStr, tierW, idxW]

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
def mK {α : Type} (rest : Mem → Option α) : Option Mem → Option α
  | none => none
  | some m => rest m

@[arena_grind =] theorem mK_none {α : Type} (rest : Mem → Option α) : mK rest none = none := rfl
@[arena_grind =] theorem mK_some {α : Type} (rest : Mem → Option α) (m : Mem) :
    mK rest (some m) = rest m := rfl

/-- **The model of `vi_listed_go(to, tn, j)`.** -/
def listedGoW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, to, tn, j =>
    if tn ≤ j then some m
    else mK (fun m₁ => listedGoW n m₁ to tn (j + 1))
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

/-! ## The constructors in the block's order, `kExpected?`, the recursors: models -/

/-- After a call that returns a word: the rest. -/
def wK {α : Type} (rest : Word → Option α) : Option Word → Option α
  | none => none
  | some x => rest x

@[arena_grind =] theorem wK_none {α : Type} (rest : Word → Option α) : wK rest none = none := rfl
@[arena_grind =] theorem wK_some {α : Type} (rest : Word → Option α) (x : Word) :
    wK rest (some x) = rest x := rfl

/-- After a check that returns nothing: the rest. -/
def uK {α : Type} (rest : Option α) : Option Unit → Option α
  | none => none
  | some _ => rest

@[arena_grind =] theorem uK_none {α : Type} (rest : Option α) : uK rest none = none := rfl
@[arena_grind =] theorem uK_some {α : Type} (rest : Option α) (u : Unit) : uK rest (some u) = rest := rfl

/-- After a call that returns two words: the rest. -/
def pK {α : Type} (rest : Word → Word → Option α) : Option (Word × Word) → Option α
  | none => none
  | some (a, b) => rest a b

@[arena_grind =] theorem pK_none {α : Type} (rest : Word → Word → Option α) : pK rest none = none := rfl
@[arena_grind =] theorem pK_some {α : Type} (rest : Word → Word → Option α) (a b : Word) :
    pK rest (some (a, b)) = rest a b := rfl

/-- After a call that returns two words and its memory: the rest. -/
def pmK {α : Type} (rest : Word → Word → Mem → Option α) : Option ((Word × Word) × Mem) → Option α
  | none => none
  | some ((a, b), m) => rest a b m

@[arena_grind =] theorem pmK_none {α : Type} (rest : Word → Word → Mem → Option α) :
    pmK rest none = none := rfl
@[arena_grind =] theorem pmK_some {α : Type} (rest : Word → Word → Mem → Option α) (a b : Word)
    (m : Mem) : pmK rest (some ((a, b), m)) = rest a b m := rfl

/-- `vi_ctor` after the `induct` check: the telescope. -/
def ctorTail (n : Nat) (m : Mem) (np fuel c : Word) : Option Word :=
  wK (fun t => wK (fun x => if np + rdW (m.arr64 IFR) (c + 4) ≠ x then none else some c)
    (teleW n m fuel t)) (lkW m EID (rdW (m.arr64 IFR) (c + 2)))

/-- `vi_ctor` at the record `c`: the checks. -/
def ctorAt (n : Nat) (m : Mem) (j tt np fuel c : Word) : Option Word :=
  if rdW (m.arr64 IFR) (c + 6) ≠ 0 ∧ rdW (m.arr64 IFR) (c + 7) ≠ j then none
  else if rdW (m.arr64 IFR) (c + 8) ≠ 0 then
    wK (fun x => if x ≠ tt then none else ctorTail n m np fuel c) (lkW m NID (rdW (m.arr64 IFR) (c + 9)))
  else ctorTail n m np fuel c

/-- **The model of `vi_ctor(nn, j, tt, np, fuel, cno, cn, co)`**: the record's pointer. -/
def ctorW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option Word
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, nn, j, tt, np, fuel, cno, cn, co =>
    pK (fun f k => if f = 0 then none else ctorAt n m j tt np fuel (co + 10 * k)) (findLastW n m cno nn cn)

/-- **The model of `vi_order_in(fo, cno, co, cn, fuel, np, oo, t, tt, jj, pos)`**: the position
after. -/
def orderInW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, fo, cno, co, cn, fuel, np, oo, t, tt, jj, pos =>
    if rdW (m.arr64 IFR) (t + 4) ≤ jj then some (pos, m)
    else wK (fun c => orderInW n (m.set64 IFL (oo + pos) c) fo cno co cn fuel np oo t tt (jj + 1) (pos + 1))
      (ctorW n m (rdW (m.arr64 IFL) (fo + pos)) jj tt np fuel cno cn co)

/-- **The model of `vi_order_go(to, tn, tyn, fo, cno, co, cn, fuel, np, oo, ti, pos)`.** -/
def orderGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Option Mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, to, tn, tyn, fo, cno, co, cn, fuel, np, oo, ti, pos =>
    if tn ≤ ti then some m
    else allocK (fun q m₁ => orderGoW n m₁ to tn tyn fo cno co cn fuel np oo (ti + 1) q)
      (orderInW n m fo cno co cn fuel np oo (to + 11 * ti) (rdW (m.arr64 IFL) (tyn + ti)) 0 pos)

/-- **The model of `vi_order(to, tn, tyn, fo, cno, co, cn, fuel, np)`**: the slice's offset. -/
def orderW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, to, tn, tyn, fo, cno, co, cn, fuel, np =>
    allocK (fun oo m₁ => mK (fun m₂ => some (oo, m₂)) (orderGoW n m₁ to tn tyn fo cno co cn fuel np oo 0 0))
      (allocW m IFL cn)

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

/-- **The model of `vi_k_expected(to, tn, tyt, oo, fuel)`**: `kExpected?` and the memory. -/
def kExpW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, to, tn, tyt, oo, fuel =>
    if tn ≠ 1 then some (1, m)
    else if rdW (m.arr64 IFR) (to + 4) ≠ 1 then some (1, m)
    else keK1 n m oo (piResW n m fuel (rdW (m.arr64 IFL) tyt))

/-- **The model of `vi_rec_idx(tt, ni, np, tn, tyn, tyt, fuel, j)`.** -/
def recIdxW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option Unit
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, tt, ni, np, tn, tyn, tyt, fuel, j =>
    if tn ≤ j then some ()
    else if rdW (m.arr64 IFL) (tyn + j) = tt then
      pK (fun ok k => if ok ≠ 0 ∧ np + ni ≠ k then none else recIdxW n m tt ni np tn tyn tyt fuel (j + 1))
        (sortTeleW n m fuel (rdW (m.arr64 IFL) (tyt + j)))
    else recIdxW n m tt ni np tn tyn tyt fuel (j + 1)

/-- **The model of `vi_rec(r, np, tn, cn, ke, tyn, tyt, fuel)`.** -/
def recW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option Unit
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, r, np, tn, cn, ke, tyn, tyt, fuel =>
    wK (fun rn =>
      if rdW (m.arr64 IFR) (r + 8) ≠ np then none
      else if rdW (m.arr64 IFR) (r + 7) ≠ tn then none
      else if rdW (m.arr64 IFR) (r + 6) ≠ cn then none
      else if ke ≠ 0 ∧ rdW (m.arr64 IFR) (r + 4) ≠ ke - 1 then none
      else pK (fun f tt => if f ≠ 0 then recIdxW n m tt (rdW (m.arr64 IFR) (r + 5)) np tn tyn tyt fuel 0
          else some ()) (nrpW m rn))
      (lkW m NID (rdW (m.arr64 IFR) r))

/-- **The model of `vi_nested(to, tn, j)`.** -/
def nestedW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, to, tn, j =>
    if tn ≤ j then some 0
    else if rdW (m.arr64 IFR) (to + 11 * j + 9) ≠ 0 then some 1
    else nestedW n m to tn (j + 1)

/-- **The model of `vi_recs_go(ro, rn, np, tn, cn, ke, tyn, tyt, fuel, j)`.** -/
def recsGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option Unit
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, ro, rn, np, tn, cn, ke, tyn, tyt, fuel, j =>
    if rn ≤ j then some ()
    else uK (recsGoW n m ro rn np tn cn ke tyn tyt fuel (j + 1))
      (recW n m (ro + 11 * j) np tn cn ke tyn tyt fuel)

/-- **The model of `vi_recs(to, tn, ro, rn, np, cn, ke, tyn, tyt, fuel)`.** -/
def recsW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option Unit
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, to, tn, ro, rn, np, cn, ke, tyn, tyt, fuel =>
    wK (fun u => if u ≠ 0 then some () else recsGoW n m ro rn np tn cn ke tyn tyt fuel 0)
      (nestedW n m to tn 0)

/-- **The model of `vi_tail(to, tn, co, cn, ro, rn, np, tyn, tyt, fo, cno)`**: the ordered
constructors' offset. -/
def tailW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, to, tn, co, cn, ro, rn, np, tyn, tyt, fo, cno =>
    wK (fun fuel => allocK (fun oo m₅ => allocK (fun ke m₆ =>
        uK (some (oo, m₆)) (recsW n m₆ to tn ro rn np cn ke tyn tyt fuel))
      (kExpW n m₅ to tn tyt oo fuel)) (orderW n m to tn tyn fo cno co cn fuel np))
    (storeFuelW n m)

/-- **The model of `validate_ind_d(to, tn, co, cn, ro, rn)`**: `(ordered.off, nPd)` and the
memory. -/
def validateW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option ((Word × Word) × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, to, tn, co, cn, ro, rn =>
    uK (wK (fun np =>
      pmK (fun tyn _ m₁ => pmK (fun tyt _ m₂ => pmK (fun fo x m₃ => pmK (fun cno _ m₄ =>
        wK (fun u => if u = 0 then none else if x ≠ cn then none else
          allocK (fun oo m₅ => some ((oo, np), m₅))
            (tailW n m₄ to tn co cn ro rn np tyn tyt fo cno))
        (nodupW n m₄ fo x 0)) (mapW n m₃ co cn 10 0 0)) (listedW n m₂ to tn))
        (mapW n m₁ to tn 11 2 1)) (mapW n m to tn 11 0 0))
      (nparamsW n m to tn)) (unsafeW n m to tn 0)

/-! ## The constructors in the block's order, `kExpected?`, the recursors: specs -/

section specs3
variable (p : Prog) (hL : IndApplyLookups p)
include hL

set_option maxHeartbeats 2000000 in
theorem ctor_spec (n : Nat) (s₀ : St) (nn j tt np fuel cno cn co : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_ctor" [nn, j, tt, np, fuel, cno, cn, co]
    ⦃fun r s' => s' = s₀ ∧ ctorW n s₀.mem nn j tt np fuel cno cn co = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hL.vi_ctor]
  simp only [callFn, viCtor]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        findLast_spec p hL n, nameGet_spec p hL.decl.expr.front n, exprGet_spec p hL.decl.expr n,
        tele_spec p hL n] <;> finish (gen := 20) [ctorW, ctorAt, ctorTail, lkW]

theorem orderIn_spec (n : Nat) : ∀ (s₀ : St) (fo cno co cn fuel np oo t tt jj pos : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "vi_order_in" [fo, cno, co, cn, fuel, np, oo, t, tt, jj, pos]
    ⦃fun r s' => LocEq s' s₀ ∧
      orderInW n s₀.mem fo cno co cn fuel np oo t tt jj pos = some (r.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ fo cno co cn fuel np oo t tt jj pos
    rw [invoke_eq _ hL.vi_order_in]; simp only [callFn, viOrderIn]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ fo cno co cn fuel np oo t tt jj pos
    rw [invoke_eq _ hL.vi_order_in]
    simp only [callFn, viOrderIn]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih,
        ctor_spec p hL n] <;> finish (gen := 20) [orderInW]

theorem orderGo_spec (n : Nat) : ∀ (s₀ : St) (to tn tyn fo cno co cn fuel np oo ti pos : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "vi_order_go" [to, tn, tyn, fo, cno, co, cn, fuel, np, oo, ti, pos]
    ⦃fun _ s' => LocEq s' s₀ ∧
      orderGoW n s₀.mem to tn tyn fo cno co cn fuel np oo ti pos = some s'.mem; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ to tn tyn fo cno co cn fuel np oo ti pos
    rw [invoke_eq _ hL.vi_order_go]; simp only [callFn, viOrderGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ to tn tyn fo cno co cn fuel np oo ti pos
    rw [invoke_eq _ hL.vi_order_go]
    simp only [callFn, viOrderGo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        orderIn_spec p hL n] <;> finish (gen := 20) [orderGoW]

theorem order_spec (n : Nat) (s₀ : St) (to tn tyn fo cno co cn fuel np : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_order" [to, tn, tyn, fo, cno, co, cn, fuel, np]
    ⦃fun r s' => LocEq s' s₀ ∧
      orderW n s₀.mem to tn tyn fo cno co cn fuel np = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.vi_order]
  simp only [callFn, viOrder]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        iflAlloc_spec p hL.ifl_alloc n, orderGo_spec p hL n] <;> finish (gen := 20) [orderW]

theorem kExp_spec (n : Nat) (s₀ : St) (to tn tyt oo fuel : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_k_expected" [to, tn, tyt, oo, fuel]
    ⦃fun r s' => LocEq s' s₀ ∧ kExpW n s₀.mem to tn tyt oo fuel = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.vi_k_expected]
  simp only [callFn, viKExpected]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        piRes_spec p hL n, eView_spec p hL.e_view n, lhMk_spec p hL.level.alloc n,
        lvEquiv_spec p hL.level hL.lv_equiv n] <;> finish (gen := 20) [kExpW]

theorem recIdx_spec (n : Nat) : ∀ (s₀ : St) (tt ni np tn tyn tyt fuel j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_rec_idx" [tt, ni, np, tn, tyn, tyt, fuel, j]
    ⦃fun _ s' => s' = s₀ ∧ recIdxW n s₀.mem tt ni np tn tyn tyt fuel j = some (); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ tt ni np tn tyn tyt fuel j
    rw [invoke_eq _ hL.vi_rec_idx]; simp only [callFn, viRecIdx]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ tt ni np tn tyn tyt fuel j
    rw [invoke_eq _ hL.vi_rec_idx]
    simp only [callFn, viRecIdx]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        sortTele_spec p hL n] <;> finish (gen := 20) [recIdxW]

theorem rec_spec (n : Nat) (s₀ : St) (r np tn cn ke tyn tyt fuel : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_rec" [r, np, tn, cn, ke, tyn, tyt, fuel]
    ⦃fun _ s' => s' = s₀ ∧ recW n s₀.mem r np tn cn ke tyn tyt fuel = some (); ⊤⦄ := by
  rw [invoke_eq _ hL.vi_rec]
  simp only [callFn, viRec]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nameGet_spec p hL.decl.expr.front n, nrp_spec p hL n, recIdx_spec p hL n] <;>
        finish (gen := 20) [recW, lkW]

theorem nested_spec (n : Nat) : ∀ (s₀ : St) (to tn j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_nested" [to, tn, j]
    ⦃fun r s' => s' = s₀ ∧ nestedW n s₀.mem to tn j = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ to tn j; rw [invoke_eq _ hL.vi_nested]; simp only [callFn, viNested]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ to tn j
    rw [invoke_eq _ hL.vi_nested]
    simp only [callFn, viNested]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish (gen := 20) [nestedW]

theorem recsGo_spec (n : Nat) : ∀ (s₀ : St) (ro rn np tn cn ke tyn tyt fuel j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_recs_go" [ro, rn, np, tn, cn, ke, tyn, tyt, fuel, j]
    ⦃fun _ s' => s' = s₀ ∧ recsGoW n s₀.mem ro rn np tn cn ke tyn tyt fuel j = some (); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ ro rn np tn cn ke tyn tyt fuel j
    rw [invoke_eq _ hL.vi_recs_go]; simp only [callFn, viRecsGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ro rn np tn cn ke tyn tyt fuel j
    rw [invoke_eq _ hL.vi_recs_go]
    simp only [callFn, viRecsGo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ih, rec_spec p hL n] <;>
        finish (gen := 20) [recsGoW]

theorem recs_spec (n : Nat) (s₀ : St) (to tn ro rn np cn ke tyn tyt fuel : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_recs" [to, tn, ro, rn, np, cn, ke, tyn, tyt, fuel]
    ⦃fun _ s' => s' = s₀ ∧ recsW n s₀.mem to tn ro rn np cn ke tyn tyt fuel = some (); ⊤⦄ := by
  rw [invoke_eq _ hL.vi_recs]
  simp only [callFn, viRecs]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, nested_spec p hL n,
        recsGo_spec p hL n] <;> finish (gen := 20) [recsW]

theorem tail_spec (n : Nat) (s₀ : St) (to tn co cn ro rn np tyn tyt fo cno : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vi_tail" [to, tn, co, cn, ro, rn, np, tyn, tyt, fo, cno]
    ⦃fun r s' => LocEq s' s₀ ∧
      tailW n s₀.mem to tn co cn ro rn np tyn tyt fo cno = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.vi_tail]
  simp only [callFn, viTail]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        storeFuel_spec p hL n, order_spec p hL n, kExp_spec p hL n,
        recs_spec p hL n] <;> finish (gen := 20) [tailW]

theorem validate_spec (n : Nat) (s₀ : St) (to tn co cn ro rn : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "validate_ind_d" [to, tn, co, cn, ro, rn]
    ⦃fun r s' => LocEq s' s₀ ∧
      validateW n s₀.mem to tn co cn ro rn = some ((r.headD 0, r.tail.headD 0), s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.validate_ind_d]
  simp only [callFn, validateIndD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        unsafe_spec p hL n, nparams_spec p hL n, map_spec p hL n, listed_spec p hL n,
        nodup_spec p hL n, tail_spec p hL n] <;> finish (gen := 20) [validateW]

end specs3

end L.Front.Ind
