import ConAgua.Arena.IndIface

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
    RelAM "whnf" [vis, dep, e] (StageR dn vis fe)
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

/-- `strip_pis(k, e)`. -/
theorem stripPis_spec (k e : Word) (he : H e) :
    RelAM "strip_pis" [k, e] (StageR dn vis fe)
      (stripPis k.toNat (decI e)) (KeepPost dn vis fe decOLE) := sorry

/-- `strip_lams(k, e)`. -/
theorem stripLams_spec (k e : Word) (he : H e) :
    RelAM "strip_lams" [k, e] (StageR dn vis fe)
      (stripLams k.toNat (decI e)) (KeepPost dn vis fe decOLE) := sorry

/-- `open_pis_at_fvars_f(n, e, i)`. -/
theorem openPisAtFvarsF_spec (k e i : Word) (he : H e) :
    RelAM "open_pis_at_fvars_f" [k, e, i] (StageR dn vis fe)
      (openPisAtFvarsF k.toNat (decI e) i.toNat) (KeepPost dn vis fe decOLE) := sorry

/-- `get_app_fn(fuel, e)`. -/
theorem getAppFn_spec (f e : Word) (he : H e) :
    RelAM "get_app_fn" [f, e] (StageR dn vis fe)
      (getAppFn f.toNat (decI e)) (KeepPost dn vis fe decW0E) := sorry

/-- `get_app_args(fuel, e)`. -/
theorem getAppArgs_spec (f e : Word) (he : H e) :
    RelAM "get_app_args" [f, e] (StageR dn vis fe)
      (getAppArgs f.toNat (decI e)) (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) := sorry

/-- `mk_app_n(f, off, len)`. -/
theorem mkAppN_spec (f o l : Word) (hf : H f) (xs : List EIdx) :
    RelAM "mk_app_n" [f, o, l] (fun m a => StageR dn vis fe m a ∧ decHL m o.toNat l.toNat = some xs)
      (mkAppN (decI f) xs) (KeepPost dn vis fe decW0E) := sorry

/-- `fvar_type_d(e)`. -/
theorem fvarTypeD_spec (e : Word) (he : H e) :
    RelAM "fvar_type_d" [e] (StageR dn vis fe)
      (fvarTypeD (decI e)) (KeepPost dn vis fe decW0E) := sorry

/-- `fvar_type_ds(off, len)`. -/
theorem fvarTypeDs_spec (o l : Word) (xs : List EIdx) :
    RelAM "fvar_type_ds" [o, l] (fun m a => StageR dn vis fe m a ∧ decHL m o.toNat l.toNat = some xs)
      (fvarTypeDs xs) (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) := sorry

/-- `pi_result(fuel, e)`. -/
theorem piResult_spec (f e : Word) (he : H e) :
    RelAM "pi_result" [f, e] (StageR dn vis fe)
      (piResult f.toNat (decI e)) (KeepPost dn vis fe decW0E) := sorry

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

/-- `instantiate1_fast(fuel, e, v, d)`. -/
theorem instantiate1Fast_spec (f e v d : Word) (he : H e) (hv : H v) :
    RelAM "instantiate1_fast" [f, e, v, d] (StageR dn vis fe)
      (instantiate1Fast f.toNat (decI e) (decI v) d.toNat) (KeepPost dn vis fe decW0E) := sorry

/-- `instantiate1_lift_fast(fuel, e, v, d)`. -/
theorem instantiate1LiftFast_spec (f e v d : Word) (he : H e) (hv : H v) :
    RelAM "instantiate1_lift_fast" [f, e, v, d] (StageR dn vis fe)
      (instantiate1LiftFast f.toNat (decI e) (decI v) d.toNat) (KeepPost dn vis fe decW0E) := sorry

/-- `abstract1_fast(fuel, e, d, k)`. -/
theorem abstract1Fast_spec (f e d k : Word) (he : H e) :
    RelAM "abstract1_fast" [f, e, d, k] (StageR dn vis fe)
      (abstract1Fast f.toNat (decI e) d.toNat k.toNat) (KeepPost dn vis fe decW0E) := sorry

/-- `bvar_b(fuel, e)`. -/
theorem bvarB_spec (f e : Word) (he : H e) :
    RelAM "bvar_b" [f, e] (StageR dn vis fe)
      (bvarB f.toNat (decI e)) (KeepPost dn vis fe decW0Nat) := sorry

/-- `fvar_b(fuel, e)`. -/
theorem fvarB_spec (f e : Word) (he : H e) :
    RelAM "fvar_b" [f, e] (StageR dn vis fe)
      (fvarB f.toNat (decI e)) (KeepPost dn vis fe decW0Nat) := sorry

/-- `has_fvar_fast(fuel, e)`. -/
theorem hasFvarFast_spec (f e : Word) (he : H e) :
    RelAM "has_fvar_fast" [f, e] (StageR dn vis fe)
      (hasFvarFast f.toNat (decI e)) (KeepPost dn vis fe decW0B) := sorry

/-- `loose_bvars_bounded_fast(fuel, k, e)`. -/
theorem looseBVarsBoundedFast_spec (f k e : Word) (he : H e) :
    RelAM "loose_bvars_bounded_fast" [f, k, e] (StageR dn vis fe)
      (looseBVarsBoundedFast f.toNat k.toNat (decI e)) (KeepPost dn vis fe decW0B) := sorry

/-- `all_level_params_defined(lps.off, lps.len, e)`. -/
theorem allLevelParamsDefined_spec (o l e : Word) (he : H e) (lps : List NIdx) :
    RelAM "all_level_params_defined" [o, l, e]
      (fun m a => StageR dn vis fe m a ∧ decHL m o.toNat l.toNat = some lps)
      (allLevelParamsDefined lps (decI e)) (KeepPost dn vis fe decW0B) := sorry

/-- `intern_ls_iw(off, len)`. -/
theorem internLsIw_spec (o l : Word) (us : List LIdx) :
    RelAM "intern_ls_iw" [o, l] (fun m a => StageR dn vis fe m a ∧ decHL m o.toNat l.toNat = some us)
      (internLsNode us) (KeepPost dn vis fe (fun _ r (x : LsIdx) => H (r.headD 0) ∧ decI (r.headD 0) = x)) :=
  sorry

/-- `name_rec(n)`. -/
theorem nameRec_spec (n : Word) (hn : H n) :
    RelAM "name_rec" [n] (StageR dn vis fe)
      (internNNode (.str (decI n) "rec")) (KeepPost dn vis fe decW0N) := sorry

/-- `name_rec_i(n, i)`. -/
theorem nameRecI_spec (n i : Word) (hn : H n) :
    RelAM "name_rec_i" [n, i] (StageR dn vis fe)
      (internNNode (.str (decI n) s!"rec_{i.toNat}")) (KeepPost dn vis fe decW0N) := sorry

/-- `proj_table_name(T)`. -/
theorem projTableName_spec (t : Word) (ht : H t) :
    RelAM "proj_table_name" [t] (StageR dn vis fe)
      (projTableName (decI t)) (KeepPost dn vis fe decW0N) := sorry

/-- `is_proj_fn_shape(n)`. -/
theorem isProjFnShape_spec (n : Word) (hn : H n) :
    RelAM "is_proj_fn_shape" [n] (StageR dn vis fe)
      (NIdx.isProjFnShape (decI n)) (KeepPost dn vis fe decW0B) := sorry

/-- `reserved_rec_name(n)`. -/
theorem reservedRecName_spec (n : Word) (hn : H n) :
    RelAM "reserved_rec_name" [n] (StageR dn vis fe)
      (reservedRecName (decI n)) (KeepPost dn vis fe decW0B) := sorry

/-- `rec_rule_bits(vis, ctor)`: the two bits `recRuleBits` writes (`k`, `eta`), which depend on the
rule's constructor only. -/
theorem recRuleBits_spec (c : Word) (hc : H c) (rl : IRecRule) (hrl : rl.ctor = decI c) :
    RelAM "rec_rule_bits" [vis, c] (StageR dn vis fe)
      (recRuleBits fe rl)
      (KeepPost dn vis fe (fun _ r (x : IRecRule) =>
        x = { rl with k := r.headD 0 != 0, eta := r.tail.headD 0 != 0 })) := sorry

/-- `ind_params_ok(nP, off, len)` (the block's constant records, an `IW` list of `EREC`
pointers). -/
theorem indParamsOk_spec (nP o l : Word) (blk : List IConstantInfo) :
    RelAM "ind_params_ok" [nP, o, l]
      (fun m a => StageR dn vis fe m a ∧ decPL m (fun q => decCI (erA m) dn q) o.toNat l.toNat = some blk)
      (indParamsOk nP.toNat blk) (KeepPost dn vis fe decW0B) := sorry

end specs


/-! ## Master callees without a model yet (lane indproofs)

Master functions the stage calls whose word models exist only under `ArenaR` (the `intern*_refinesA`
lemmas), not under `StageR`: lifting them across `CheckR` (`ArenaD` including `DerR`, the upper
tiers) is not done, so a stage proof treats them as stubs, with these `RelAM` statements. -/

section masterstubs
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- `intern_bvar(k)`: interning `.bvar k` (master, under `StageR` only through this statement). -/
theorem recInternBVar_spec (k : Word) :
    RelAM "intern_bvar" [k] (StageR dn vis fe)
      (internE (.bvar k.toNat)) (KeepPost dn vis fe decW0E) := sorry

end masterstubs

end L.Ind
