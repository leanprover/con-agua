module

public import ConAgua.Arena.Knot
public import ConAgua.Arena.RefECore
public import ConAgua.Arena.DefEq
public import ConAgua.Arena.Env
public import ConAgua.Arena.WhnfSpineRefine
public import ConAgua.Checker.NoVerdictFns
public import ConAgua.L.ErrSpec
import ConAgua.Arena.RefWalk
import ConAgua.Arena.Verdict
import ConAgua.Arena.IndView
-- import ConAgua.Arena.PropReadLoops
import ConAgua.Arena.RecLayout.CIDec
import ConAgua.Arena.RecLayout.CapsDec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LdRd
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.DefEq
import all ConAgua.Arena.Pins

@[expose] public section

/-!
# The constructor shortcut's readers: `ctor_target`, `ctor_target_for`, `ctor_head_against`

con-ron's `ctorTarget`, `ctorTargetFor`, `ctorHeadAgainst` (#592, `defeqBody`'s constructor
shortcut). Each by its generated `unified` model and a declarative refinement (`RefE`, the walk
kit): the callees `has_fvar` (`HasFvarOK`, a knot callee bundle), `get_app_fn`, `env_find`,
`pin_at` and `app_count_at` are lifted; the record words are read through `erRd`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- The lookups of the constructor shortcut's readers. -/
structure CtorProg (p : Prog) : Prop where
  envrow : p.lookup "env_row_get" = some envRowGetL
  baserow : p.lookup "base_row_get" = some baseRowGetL
  envfind : p.lookup "env_find" = some envFindL
  gaf : p.lookup "get_app_fn" = some getAppFnL
  pinat : p.lookup "pin_at" = some pinAtL
  aca : p.lookup "app_count_at" = some appCountAtL
  ct : p.lookup "ctor_target" = some ctorTargetL
  ctf : p.lookup "ctor_target_for" = some ctorTargetForL
  cha : p.lookup "ctor_head_against" = some ctorHeadAgainstL

/-- **`ctor_target`'s model, both outcomes** (generated; its callees lifted). -/
l_model ctE_spec (p : Prog) (hf : p.lookup "ctor_target" = some ctorTargetL)
  fns [hf ↦ ctE list]
  specs [callW_spec p n "has_fvar", callW_spec p n "get_app_fn", callW_spec p n "env_find",
    callW_spec p n "pin_at", callW_spec p n "app_count_at"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`ctor_target_for`'s model, both outcomes** (generated; `has_fvar` lifted, `ctor_target` by
its model). -/
l_model ctfE_spec (p : Prog) (hf : p.lookup "ctor_target_for" = some ctorTargetForL)
    (ht : p.lookup "ctor_target" = some ctorTargetL)
  fns [hf ↦ ctfE list]
  specs [callW_spec p n "has_fvar", ctE_spec p ht n]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`ctor_head_against`'s model, both outcomes** (generated; its callees lifted). -/
l_model chaE_spec (p : Prog) (hf : p.lookup "ctor_head_against" = some ctorHeadAgainstL)
  fns [hf ↦ chaE list]
  specs [callW_spec p n "get_app_fn", callW_spec p n "env_find"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## The twin's answers, decoded -/

/-- `ctor_target`'s answer: `(0, _)` none, `(1, c)` the constructor `c`. -/
def decCT (r : List Word) : Option NIdx := if r.headD 0 = 0 then none else some (decI (r.tail.headD 0))

/-- `ctor_target`'s answer word is a name handle. -/
def ResCT (r : List Word) : Prop := (r.tail.headD 0).toNat < 2 ^ 32

/-- `ctor_head_against`'s answer: `(0, _)` none, `(1, v)` `some (v ≠ 0)`. -/
def decCHA (r : List Word) : Option Bool := if r.headD 0 = 0 then none else some (r.tail.headD 0 != 0)

theorem resCT_zero : ResCT [0, 0] := by unfold ResCT; decide

/-! ## `ctor_target` -/

section ct
variable (p : Prog) (hq : CtorProg p) (hfv : HasFvarOK p)

include hq hfv in
/-- **`ctor_target` refines `ctorTarget`, both outcomes** (its errors are class `0`: a dangling
read, the spine counter). -/
theorem ct_ref {G : Prop} (n : Nat) (m : Mem) (a : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb e : Word) (hS : CoreS dn m a vis fe M eb)
    (he : HW e) :
    RefE G (ctE p n m vis e) (ctorTarget fe (decE e)) a (CorePost decCT dn m vis fe M eb ResCT) := by
  cases n with
  | zero => exact RefE.of_cls0 rfl
  | succ n =>
  simp only [ctE]
  unfold ctorTarget
  refine RefE.bind_callW (fun _ => rfl) (hfv n ⟨m, Locals.init []⟩ a dn vis fe M eb e hS he)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [ctE.k_has_fvar]
  have hR₁ := hS₁.arena.base
  refine RefE.split (d := decBool r₁ = true) (fun h => by simpa [decBool] using h)
    (fun h => by simpa [decBool] using h)
    (fun _ _ => RefE.ret rfl (CorePost.ret hS₁ rfl resCT_zero)) fun _ _ => ?_
  -- the head
  refine RefE.bindLift (fun _ => rfl) fun r₂ m₂ c₂ => ?_
  obtain ⟨s₂, hs₂, hm₂, -, hh, hgaf⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (getAppFn_refines' p hq.gaf n ⟨m₁, Locals.init []⟩ _ hR₁ e he) c₂
  have e₂ : m₂ = m₁ := hs₂.symm.trans hm₂
  subst e₂
  refine ⟨_, _, hgaf, ?_⟩
  dsimp only [ctE.k_get_app_fn]
  generalize r₂.headD 0 = h at hh hgaf
  rw [L.Arena.decE_tag_const_beq _ hh]
  refine RefE.splitNot (d := decide (tagW h = 3) = true) (fun h3 => by simpa using h3)
    (fun h3 => by simpa using h3)
    (fun _ _ => RefE.ret rfl (CorePost.ret hS₁ rfl resCT_zero)) fun h3 _ => ?_
  have h3 : tagW h = 3 := by simpa using h3
  refine RefE.abort0 rfl fun hs => RefE.abort0 rfl fun hc => ?_
  obtain ⟨hv, hnw, -⟩ := L.Ind.view_const_f _ _ hR₁ h hh ⟨hs, by simpa using hc⟩ h3
  refine RefE.bind_right (view_run _ _ _ hv) ?_
  dsimp only
  generalize tfld _ CONST (tierW h) (idxW h) 0 = c at hnw ⊢
  -- the constructor's record
  refine RefE.onlySim (fun _ => rfl) (fun r₃ m₃ c₃ => triple_of_callW (s₀ := ⟨_, Locals.init []⟩)
    (envFind_refines p hq.envrow hq.baserow hq.envfind n _ vis c hS₁.env hnw) c₃) fun r₃ m₃ hq₃ => ?_
  obtain ⟨s₃, hs₃, hm₃, -, hfind, hfound⟩ := hq₃
  have e₃ : m₃ = m₂ := hs₃.symm.trans hm₃
  subst e₃
  dsimp only [ctE.k_env_find]
  by_cases h0 : r₃.headD 0 = 0
  · rw [ite_eq_left h0]
    have hnone : fe.find? (decI c) = none := by rw [hfind]; simp only [envFound, h0, ↓reduceIte]
    rw [hnone]
    exact RefE.ret rfl (CorePost.ret hS₁ rfl resCT_zero)
  rw [ite_eq_right h0]
  obtain ⟨ci, hci⟩ := hfound h0
  have hf' : fe.find? (decI c) = some ci := by
    rw [hfind]; simp only [envFound, h0, ↓reduceIte]; exact hci
  rw [hf']
  have hctor := L.Arena.decCI_ctorR (erRdOK _) hci
  by_cases h4 : erRd m₃ (r₃.tail.headD 0) ≠ 4
  · rw [ite_eq_left h4]
    cases ci <;> first
      | exact absurd rfl (hctor.2 h4 _ _ _ _)
      | exact RefE.ret rfl (CorePost.ret hS₁ rfl resCT_zero)
  rw [ite_eq_right h4]
  obtain ⟨cv, rfl, hT⟩ := hctor.1 (Classical.not_not.mp h4)
  dsimp only
  generalize erRd m₃ (r₃.tail.headD 0 + CI.ctorNparams) = np
  generalize erRd m₃ (r₃.tail.headD 0 + CI.ctorNfields) = nf
  generalize erRd m₃ (r₃.tail.headD 0 + CI.ctorInduct) = T at hT ⊢
  sorry

end ct

end L.Arena
