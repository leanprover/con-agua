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

l_model storeFuel_spec (p : Prog) (hL : IndApplyLookups p)
  fns [hL.store_fuel ↦ storeFuelW ro]
  specs [ctlSum_spec p hL n]
  grind [arena_grind]

/-! ## Telescopes -/

l_model tele_spec (p : Prog) (hL : IndApplyLookups p)
  fns [hL.ind_pi_tele_len ↦ teleW ro]
  specs [eView_spec p hL.e_view n]
  grind [arena_grind]

l_model sortTele_spec (p : Prog) (hL : IndApplyLookups p)
  fns [hL.pi_sort_tele_len ↦ sortTeleW ro tuple]
  specs [eView_spec p hL.e_view n]
  grind [arena_grind]

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
        evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] <;> finish [nrpW, nrpStr, tierW, idxW]

end

/-! ## `IFL` slices -/

l_model contains_spec (p : Prog) (hL : IndApplyLookups p)
  fns [hL.ifl_contains ↦ containsW ro]
  grind [arena_grind] extra [ld64_rd_spec]

l_model nodup_spec (p : Prog) (hL : IndApplyLookups p)
  fns [hL.ifl_nodup ↦ nodupW ro]
  specs [contains_spec p hL n]
  grind [arena_grind] extra [ld64_rd_spec]

l_model findLast_spec (p : Prog) (hL : IndApplyLookups p)
  fns [hL.ifl_find_last ↦ findLastW ro tuple]
  grind [arena_grind] extra [ld64_rd_spec]

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

theorem exprGetL_spec (p : Prog) (hL : IndApplyLookups p) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "expr_get" [i]
    ⦃fun r s' => s' = s₀ ∧ lkW s₀.mem EID i = some (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨h1, h2, h3⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (exprGet_spec p hL.decl.expr n s₀ i)
  refine ⟨h1, ?_⟩
  subst h3; subst h1
  simp [lkW, h2]

l_model mapGo_spec (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_map_go ↦ mapGoW void]
  specs [nameGetL_spec p hL n, exprGetL_spec p hL n, iflPush_spec p hL.ifl_alloc hL.ifl_push n]
  grind [arena_grind] extra [ld64_rd_spec]

l_model map_spec (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_map ↦ mapW tuple]
  specs [iflAlloc_spec p hL.ifl_alloc n, mapGo_spec p hL n]
  grind [arena_grind]

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

l_model listed_spec (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_listed ↦ listedW tuple]
  specs [iflAlloc_spec p hL.ifl_alloc n, listedGo_spec p hL n]
  grind [arena_grind] extra [ld64_rd_spec]

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

l_model nested_spec (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_nested ↦ nestedW ro]
  grind [arena_grind] extra [ld64_rd_spec]

end L.Front.Ind
