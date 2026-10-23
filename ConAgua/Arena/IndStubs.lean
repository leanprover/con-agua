import ConAgua.Arena.IndIface
import ConAgua.Arena.WhnfBase

/-!
# The stubs' specs (lane `induct`)

What each callee of the inductive stage that another lane owns must prove. The L side of every
stub is one opaque word model `stubM f` and one statement `stubM_spec` (a returning call of `f` is
its model); the twin side is a `RelAM` statement per stub (a model run from a memory in the stage
relation at the view `vis` of `fe`, the arguments decoding to the twin's, is a successful twin run,
the stage relation holds after it at the same environment, the pools only grew, and the results
decode the twin's result). **All are proved by `sorry` until the owning lane lands the function**
(DESIGN.md, lane `induct`, "`sorry`s"): a refinement through a stub inherits the `sorry`, the
honest census status of a function whose callees are not proved yet. The shape is the one this
lane's refinements use for every callee (`IndSumSpec.lean`: callee models inside `vcgen`, twin
facts afterwards), so a stub enters a proof exactly as a translated function does.

`H w`: a handle word (below `2^32`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A handle word. -/
abbrev H (w : Word) : Prop := w.toNat < 2 ^ 32

/-! ## The stubs as word models

Each stub's L side is one opaque **word model** `stubM f` (the memory and result words a call of
`f` produces), and its twin side a `RelAM` statement: a model run from a related memory is a twin
run with the relation after. This is the shape lane `induct`'s refinements use for every callee
(`IndSumSpec.lean`'s template: callee **model** specs inside `vcgen`, twin facts afterwards), so
a stub enters a proof exactly as a translated function does. The owning lane replaces `stubM f`
by its function's model and proves both statements. -/

/-- The word model of the stub `f`: what a call `f(args)` leaves. Opaque: nothing is known about
it but the two `sorry`'d statements below. -/
opaque stubM (f : FnName) : Mem → List Word → Option (List Word × Mem)

/-- **The L side of every stub**: a returning call of `f` is its word model (for any program:
`sorry` until `f`'s lane lands it, its model in place of `stubM f`). -/
theorem stubM_spec (p : Prog) (f : FnName) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
    ⦃fun r s' => LocEq s' s₀ ∧ stubM f s₀.mem args = some (r, s'.mem); ⊤⦄ := sorry

/-- The names `stubM` stands for: the stubs proper and the master callees without a stage model
(`lvl_eq`, `lvl_eq_c`, `lvls_eq_c`, `lv_leq_top`). -/
def stubNames : List FnName :=
  stubFns.map (·.1) ++ ["lvl_eq", "lvl_eq_c", "lvls_eq_c", "lv_leq_top"]

/-- **The write set of every stub** (lane `indproofs2`): a stub leaves the stage's per-call memos
alone (arrays `MAM`‥`MCM` = 201‥208, their control words `CTL[202]`‥`CTL[219]`), and keeps every
array's size. `sorry` until the owning lanes land the functions, like `stubM_spec`; with it a memo
relation (`maMR`, `hbMR`, …) is carried across a stub call (`MemoRV` reads the memo's array and
control words only). Replaces helper `memo`'s `stubHbFrame` (lane `indproofs`). -/
theorem stubM_memoFrame (f : FnName) (hf : f ∈ stubNames) (m m' : Mem) (args r : List Word)
    (h : stubM f m args = some (r, m')) :
    ∃ (A : List ArrId) (C : List Word), (∀ b ∈ A, b < 201 ∨ 208 < b) ∧
      (∀ x ∈ C, x.toNat < 202 ∨ 219 < x.toNat) ∧ MemFrame A C m m' := sorry

/-- **The `abstract1` walk's memo is well formed** (lane `indproofs4`, helper `abs`): array 49
(`ABMEMO`) with epoch word `CTL[48]` (`Abs1.lean`'s `abSch`, the core's `coreAbSch`) at some map.
`abstract1_fast` clears it on entry and exit, so it needs this of the memory it starts from and
leaves it so (`IndRealAbs.lean`); `StageR` says nothing about array 49, so callers thread it. -/
def AbMemo (m : Mem) : Prop :=
  ∃ mp : Std.HashMap (EIdx × Nat) EIdx, MemoRG (⟨49, 48⟩ : MemoSch) lfKey decE m mp

/-- **The `instantiate1Lift` walk's memo is well formed** (helper `indproofs4-memo`): array 51
(`ILFM`) with epoch word `CTL[52]` (`WalkLift.lean`'s `i1lSch`), what `instantiate1_lift_fast`
needs (`IndRealMemo.lean`). -/
def I1Memo (m : Mem) : Prop :=
  ∃ mp : Std.HashMap (EIdx × Nat) EIdx, MemoRG (⟨51, 52⟩ : MemoSch) lfKey decE m mp

/-- **The `constsResolveF` walk's memo table is related to some memo** (helper `indproofs4-memo`):
array 155 (`CRM`) with epoch word `CTL[158]` (`ConstsResolveF.lean`'s `crSch`; lane `tails`'
`CrOK`, `ConstsResolveFRefine2.lean`), what `consts_resolve_ffast` needs. -/
def CrMemo (m : Mem) : Prop :=
  ∃ mp : Std.HashMap EIdx Bool,
    MemoRV (⟨155, 158⟩ : MemoSch) bmKey (fun _ w b => w = if b then 1 else 0) m mp

/-- **The `instantiateList` walk's memo is well formed** (helper `indproofs4-memo`): array 50
with epoch word `CTL[50]` (`InstList.lean`'s `ilSch`, the core's `coreIlSch`), what `inst_list`
(under `open_pis_at_fvars_f`) needs. -/
def IlMemo (m : Mem) : Prop :=
  ∃ mp : Std.HashMap (EIdx × Nat) EIdx, MemoRG (⟨50, 50⟩ : MemoSch) lfKey decE m mp

/-- **The rest of the memory's half of `TwinOK`** (lane `indstaget`): the core's other walk memos
(`WalkMemos`: arrays 151‥153, 52‥54), the three arrays whose sizes `TwinOK` bounds, the pin flag.
Carried in `AbsOK` so that every model frame (`AFr`) carries it too: what lifts a stage theorem
to `StageC` (`IndT/Lift.lean`). -/
def WkOK (m : Mem) : Prop :=
  WalkMemos m ∧ (m.arr64 EREC).size < 2 ^ 63 ∧ (m.arr64 SPN).size < 2 ^ 63 ∧
    (m.arr64 145).size < 2 ^ 63 ∧ pinW m 0 ≠ 0

/-- **The walk memos outside the stage relation are well formed** (lane `indproofs4`, helpers
`abs`, `memo`): the memos of `abstract1` (array 49), `instantiate1Lift` (51), `constsResolveF`
(155) and `instantiateList` (50). Each walk clears its memo on entry and exit, so it needs the
memo well formed in the memory it starts from and leaves it so; `StageR` says nothing about these
arrays, so the stage's theorems thread it as a hypothesis and a post. (The name is helper `abs`'s,
from when it held the `abstract1` memo only.) The core's `CoreMemos` holds the first and the last
(`IndRealAbsT.lean`). -/
def AbsOK (m : Mem) : Prop := AbMemo m ∧ I1Memo m ∧ CrMemo m ∧ IlMemo m ∧ WkOK m

/-- **Every stub keeps the walk memos well formed** (lane `indproofs4`, helpers `abs`, `memo`).
`sorry` until the owning lanes land the functions, like `stubM_memoFrame`; true of the real
functions: those that do not reach the four walks leave their arrays and epoch words alone, the
walks clear and keep their memos, and the core's (`whnf`, `infer_type`, …) keep `CoreMemos`
(arrays 49, 50) and write neither 51 nor 155. -/
theorem stubM_absOK (f : FnName) (hf : f ∈ stubNames) (m m' : Mem) (args r : List Word)
    (h : stubM f m args = some (r, m')) (hA : AbsOK m) : AbsOK m' := sorry

/-- **The twin side of a stub**: a model run of `f(args)` from a memory satisfying `pre` against
`a` is a successful twin run of `op` with `post` after. -/
def RelAM {α : Type} (f : FnName) (args : List Word) (pre : Mem → AState → Prop) (op : AM α)
    (post : Mem → Mem → AState → List Word → α → Prop) : Prop :=
  ∀ (m m' : Mem) (a : AState) (r : List Word), stubM f m args = some (r, m') → pre m a →
    ∃ x a', op.run a = .ok (x, a') ∧ post m m' a' r x

section specs
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

local notation "V" => ConLeche.CheckMode.verified

/-- `whnf(vis, dep, e)`. -/
theorem whnf_spec (dep e : Word) (he : H e) :
    RelAM "whnf_top" [vis, dep, e] (StageR dn vis fe)
      (whnf V fe checkFuel dep.toNat (decI e)) (KeepPost dn vis fe decW0E) := sorry

/-- `infer_type_core(vis, dep, e)`. -/
theorem inferTypeCore_spec (dep e : Word) (he : H e) :
    RelAM "infer_type_core" [vis, dep, e] (StageR dn vis fe)
      (inferTypeCore V fe checkFuel dep.toNat (decI e)) (KeepPost dn vis fe decW0E) := sorry

/-- `ensure_sort_core(vis, dep, t)`. -/
theorem ensureSortCore_spec (dep t : Word) (ht : H t) :
    RelAM "ensure_sort_core" [vis, dep, t] (StageR dn vis fe)
      (ensureSortCore V fe checkFuel dep.toNat (decI t)) (KeepPost dn vis fe decW0L) := sorry

/-- `is_def_eq_core(vis, dep, a, b)`. -/
theorem isDefEqCore_spec (dep a b : Word) (ha : H a) (hb : H b) :
    RelAM "is_def_eq_core" [vis, dep, a, b] (StageR dn vis fe)
      (isDefEqCore V fe checkFuel dep.toNat (decI a) (decI b)) (KeepPost dn vis fe decW0B) := sorry

/-- `check_constant_val(vis, cv)` (`cv` an `EREC` pointer). -/
theorem checkConstantVal_spec (q : Word) (cv : IConstantVal) :
    RelAM "check_constant_val" [vis, q]
      (fun m a => StageR dn vis fe m a ∧ decCVp m q.toNat = some cv)
      (checkConstantVal V fe cv) (KeepPost dn vis fe decUnit) := sorry

/-- `consts_resolve_ffast(vis, e)`. -/
theorem constsResolveFFast_spec (e : Word) (he : H e) :
    RelAM "consts_resolve_ffast" [vis, e] (StageR dn vis fe)
      (constsResolveFFast fe (decI e)) (KeepPost dn vis fe decW0B) := sorry

/-- `open_pis_at_fvars_f(n, e, i)`. -/
theorem openPisAtFvarsF_spec (k e i : Word) (he : H e) :
    RelAM "open_pis_at_fvars_f" [k, e, i] (StageR dn vis fe)
      (openPisAtFvarsF k.toNat (decI e) i.toNat) (KeepPost dn vis fe decOLE) := sorry

/-- `inst_lp_fast(fuel, ks.off, ks.len, us, e)`. -/
theorem instLPFast_spec (f o l us e : Word) (hu : H us) (he : H e) (ks : List NIdx) :
    RelAM "inst_lp_fast" [f, o, l, us, e]
      (fun m a => StageR dn vis fe m a ∧ decHL m o.toNat l.toNat = some ks)
      (instLPFast f.toNat ks (decI us) (decI e)) (KeepPost dn vis fe decW0E) := sorry

/-- `inst_pis_at_lift(fuel, off, len, e)`. -/
theorem instPisAtLift_spec (f o l e : Word) (he : H e) (xs : List EIdx) :
    RelAM "inst_pis_at_lift" [f, o, l, e]
      (fun m a => StageR dn vis fe m a ∧ decHL m o.toNat l.toNat = some xs)
      (instPisAtLift f.toNat xs (decI e)) (KeepPost dn vis fe decOE) := sorry



/-- `all_level_params_defined(lps.off, lps.len, e)`. -/
theorem allLevelParamsDefined_spec (o l e : Word) (he : H e) (lps : List NIdx) :
    RelAM "all_level_params_defined" [o, l, e]
      (fun m a => StageR dn vis fe m a ∧ decHL m o.toNat l.toNat = some lps)
      (allLevelParamsDefined lps (decI e)) (KeepPost dn vis fe decW0B) := sorry

/-- `name_rec_i(n, i)`. -/
theorem nameRecI_spec (n i : Word) (hn : H n) :
    RelAM "name_rec_i" [n, i] (StageR dn vis fe)
      (internNNode (.str (decI n) s!"rec_{i.toNat}")) (KeepPost dn vis fe decW0N) := sorry

/-- A `PropWhen` from its three words (`decPW`'s layout: `0` `never`, `1` `ifAllZero` with the
names the handle slice `(o, l)` of `a`). -/
def pwWords (a : Array Word) (t o l : Word) : Option ConLeche.PropWhen :=
  match t.toNat with
  | 0 => some .never
  | 1 => do
    let ns : List NIdx ← hslice? a o.toNat l.toNat
    pure (.ifAllZero (← ns.mapM dn))
  | _ => none

/-- `lv_zero_caps`' result `(tag, off, len)`: the zero-ness of the level `lv`, decoded in every
array that agrees with the record pool below its top. -/
def decZC (m : Mem) (r : List Word) (lv : ConLeche.Level) : Prop :=
  ∀ a : Array Word, (∀ i < erTop m, a[i]? = (erA m)[i]?) →
    pwWords dn a (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0) = some (ConLeche.Level.zeronessOf lv)

/-- `lv_zero_caps(l)` (lane `indproofs2`, stub contract): the level read back, its zero-ness as
three words. -/
theorem lvZeroCaps_spec (l : Word) (hl : H l) :
    RelAM "lv_zero_caps" [l] (StageR dn vis fe) (readLevelM (decI l))
      (KeepPost dn vis fe (decZC dn)) := sorry

end specs

/-! ## Master callees without a model yet (lane indproofs) -/

section masterSpecs
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- Result decoder of `lvl_eq`: `0` for `none`, `1` for `some false`, `2` for `some true`. -/
def decLvlEq (_m : Mem) (r : List Word) (x : Option Bool) : Prop :=
  r.headD 0 = (match x with | none => 0 | some false => 1 | some true => 2)

/-- `lvl_eq_c(u, v)`: `lvlEq?` on two level handles, through the verdict cache `lvlEqC` as the
twin's `lvlEq?` (lane `whnf`'s `lvl_eq_c`; the uncached `lvl_eq` leaves the cache behind the
twin's). No stage-level (`StageR`) model yet: lane `whnf`'s `lvlEqC_refines` holds under `CoreS`,
which carries invariants `StageR` lacks (DESIGN.md, lane `decls3`). -/
theorem lvlEqStub_spec (u v : Word) (hu : H u) (hv : H v) :
    RelAM "lvl_eq_c" [u, v] (StageR dn vis fe) (lvlEq? (decI u) (decI v))
      (KeepPost dn vis fe decLvlEq) := sorry

/-- `lv_leq_top(u, v)`: `Level.leq` on the two level handles' readbacks (`readLevelM`), as `0`
(none), `1` (false), `2` (true). Master's `leqTopW_ok` (`LevelEquivRel.lean`) relates it to `leq`
for level pointers under `LvR`; no stage-level (`StageR`) model yet: the handles' readbacks need
the `CoreS` bridge, as `lvl_eq_c`'s (lane `indproofs2`, for `check_struct_field_sorts_i`). -/
theorem lvLeqTopStub_spec (u v : Word) (hu : H u) (hv : H v) :
    RelAM "lv_leq_top" [u, v] (StageR dn vis fe)
      (do let lu ← readLevelM (decI u); let lv ← readLevelM (decI v); pure (ConLeche.Level.leq lu lv))
      (KeepPost dn vis fe decLvlEq) := sorry

end masterSpecs

end L.Ind
