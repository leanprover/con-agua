import ConAgua.Front.IndApply
import ConAgua.L.ModelGen
import ConAgua.Arena.LevelEquiv
import ConAgua.Front.IndAlloc
import ConAgua.Arena.IndView
import ConAgua.Front.ApplyDecl
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LdRd
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

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

l_model ctlSum_spec (p : Prog) (hL : IndApplyLookups p)
  fns [hL.ctl_sum ↦ ctlSumW ro]
  grind [arena_grind] extra [ld64_rd_spec]

/-- After the three sums. -/
def sfK (a b c : Option Word) : Option Word :=
  match a, b, c with
  | some a, some b, some c => some (a + b + c + 1)
  | _, _, _ => none

/-- **The model of `store_fuel()`**: the twenty node counts, `+ 1`. -/
def storeFuelW : Nat → Mem → Option Word
  | 0, _ => none
  | n + 1, m => sfK (ctlSumW n m 2 4) (ctlSumW n m 16 8) (ctlSumW n m 26 8)

section
variable (p : Prog) (hL : IndApplyLookups p)
include hL

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

end

/-! ## Telescopes -/

l_model piRes_spec (p : Prog) (hL : IndApplyLookups p)
  fns [hL.pi_result_d ↦ piResW ro]
  specs [eView_spec p hL.e_view n]
  grind [arena_grind] extra [ld64_rd_spec]

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
variable (p : Prog) (hL : IndApplyLookups p)
include hL

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

end

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
variable (p : Prog) (hL : IndApplyLookups p)
include hL

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

end

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

section
variable (p : Prog) (hL : IndApplyLookups p)
include hL

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

end

/-! ## `IFL` slices -/

/-- **The model of `ifl_contains(o, l, x, j)`.** -/
def containsW : Nat → Mem → Word → Word → Word → Word → Option Word
  | 0, _, _, _, _, _ => none
  | n + 1, m, o, l, x, j =>
    if l ≤ j then some 0
    else if rdW (m.arr64 IFL) (o + j) = x then some 1
    else containsW n m o l x (j + 1)

section
variable (p : Prog) (hL : IndApplyLookups p)
include hL

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

end

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
variable (p : Prog) (hL : IndApplyLookups p)
include hL

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

end

/-- **The model of `ifl_find_last(o, x, j)`**: `(ok, k)`. -/
def findLastW : Nat → Mem → Word → Word → Word → Option (Word × Word)
  | 0, _, _, _, _ => none
  | n + 1, m, o, x, j =>
    if j = 0 then some (0, 0)
    else if rdW (m.arr64 IFL) (o + j - 1) = x then some (1, j - 1)
    else findLastW n m o x (j - 1)

section
variable (p : Prog) (hL : IndApplyLookups p)
include hL

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

end

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

theorem nameGetL_spec (p : Prog) (hL : IndApplyLookups p) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "name_get" [i]
    ⦃fun r s' => s' = s₀ ∧ lkW s₀.mem NID i = some (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨h1, h2, h3⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (nameGet_spec p hL.decl.expr.front n s₀ i)
  refine ⟨h1, ?_⟩
  subst h3; subst h1
  simp [lkW, h2]

l_model idsGo_spec (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_ids_go ↦ idsGoW void]
  specs [nameGetL_spec p hL n, iflPush_spec p hL.ifl_alloc hL.ifl_push n]
  grind [arena_grind]

/-- After a call that returns only its memory: the rest. -/
def mK {α : Type} (rest : Mem → Option α) : Option Mem → Option α
  | none => none
  | some m => rest m

@[arena_grind =] theorem mK_none {α : Type} (rest : Mem → Option α) : mK rest none = none := rfl
@[arena_grind =] theorem mK_some {α : Type} (rest : Mem → Option α) (m : Mem) :
    mK rest (some m) = rest m := rfl

l_model listedGo_spec (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_listed_go ↦ listedGoW void]
  specs [idsGo_spec p hL n]
  grind [arena_grind]

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

/-- **The model of `vi_k_expected(to, tn, tyt, oo, fuel)`**: `kExpected?` and the memory. -/
def kExpW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, to, tn, tyt, oo, fuel =>
    if tn ≠ 1 then some (1, m)
    else if rdW (m.arr64 IFR) (to + 4) ≠ 1 then some (1, m)
    else keK1 n m oo (piResW n m fuel (rdW (m.arr64 IFL) tyt))

/-- **The model of `vi_nested(to, tn, j)`.** -/
def nestedW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, to, tn, j =>
    if tn ≤ j then some 0
    else if rdW (m.arr64 IFR) (to + 11 * j + 9) ≠ 0 then some 1
    else nestedW n m to tn (j + 1)

section specs4
variable (p : Prog) (hL : IndApplyLookups p)
include hL

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

end specs4

end L.Front.Ind
