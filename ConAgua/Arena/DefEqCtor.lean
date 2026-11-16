module

public import ConAgua.Arena.Knot
public import ConAgua.Arena.RefECore
public import ConAgua.Arena.DefEq
public import ConAgua.Arena.PropRead
public import ConAgua.Arena.WhnfSpineRefine
public import ConAgua.Checker.NoVerdictFns
import ConAgua.Arena.RefWalk
import ConAgua.Arena.IndView
import ConAgua.Arena.PropReadLoops
import ConAgua.Arena.RecLayout.CIDec
import ConAgua.Arena.RecLayout.CapsDec
import ConAgua.Arena.GrindAttr
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

/-- **A run of `app_count_at` at the twin's `coreWalkFuel`**: the memory unchanged, the count is
`numArgs`. -/
theorem aca_callW {p : Prog} (hq : CtorProg p) {n : Nat} {m m' : Mem} {a : AState}
    (hR : ArenaR m a) {e : Word} (he : HW e) {r : List Word}
    (hc : callW p n "app_count_at" [e, 4000000000] m = some (r, m')) :
    m' = m ∧ (numArgs coreWalkFuel (decE e)).run a = .ok ((r.headD 0).toNat, a) := by
  obtain ⟨s', hs', -, hm, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (appCountAtL_spec p hq.aca n _ e 4000000000) hc
  obtain ⟨-, hnum, -, -⟩ := acaW_ok hR he hW
  exact ⟨hs'.symm.trans hm, hnum⟩

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
  -- `Nat`'s name
  refine RefE.bindLift (fun _ => rfl) fun r₄ m₄ c₄ => ?_
  obtain ⟨s₄, hs₄, hm₄, -, hnn, hpin⟩ := triple_of_callW (s₀ := ⟨m₃, Locals.init []⟩)
    (pinAt_refines p hq.pinat n ⟨m₃, Locals.init []⟩ _ ⟨fun _ => hS₁.pins⟩ 1) c₄
  have e₄ : m₄ = m₃ := hs₄.symm.trans hm₄
  subst e₄
  refine ⟨_, _, hpin, ?_⟩
  dsimp only [ctE.k_pin_at]
  rw [L.Arena.decI_beq _ _ hT hnn]
  refine RefE.split (d := decide (T = r₄.headD 0) = true) (fun h => by simpa using h)
    (fun h => by simpa using h)
    (fun _ _ => RefE.ret rfl (CorePost.ret hS₁ rfl resCT_zero)) fun _ _ => ?_
  -- the spine's length
  refine RefE.bindLift (fun _ => rfl) fun r₅ m₅ c₅ => ?_
  obtain ⟨e₅, hnum⟩ := aca_callW hq hS₁.arena.base he c₅
  subst e₅
  refine ⟨_, _, hnum, ?_⟩
  dsimp only [ctE.k_app_count_at]
  generalize r₅.headD 0 = cnt
  by_cases hcnt : cnt.toNat = np.toNat + nf.toNat
  · have h1 : ¬ cnt < np := fun h => by have := UInt64.lt_iff_toNat_lt.mp h; omega
    have h2 : ¬ cnt - np ≠ nf := fun h => h (UInt64.toNat_inj.mp (by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]; omega))
    rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left (by simpa using hcnt)]
    -- the family's record
    refine RefE.onlySim (fun _ => rfl) (fun r₆ m₆ c₆ => triple_of_callW (s₀ := ⟨_, Locals.init []⟩)
      (envFind_refines p hq.envrow hq.baserow hq.envfind n _ vis T hS₁.env hT) c₆) fun r₆ m₆ hq₆ => ?_
    obtain ⟨s₆, hs₆, hm₆, -, hfind₆, hfound₆⟩ := hq₆
    have e₆ : m₆ = m₅ := hs₆.symm.trans hm₆
    subst e₆
    dsimp only [ctE.k_env_find_2]
    by_cases g0 : r₆.headD 0 = 0
    · rw [ite_eq_left g0]
      have hnone : fe.find? (decI T) = none := by rw [hfind₆]; simp only [envFound, g0, ↓reduceIte]
      rw [hnone]
      exact RefE.ret rfl (CorePost.ret hS₁ rfl resCT_zero)
    rw [ite_eq_right g0]
    obtain ⟨ci, hci₆⟩ := hfound₆ g0
    have hf₆ : fe.find? (decI T) = some ci := by
      rw [hfind₆]; simp only [envFound, g0, ↓reduceIte]; exact hci₆
    rw [hf₆]
    have hsp := L.Arena.decCI_splitE hci₆
    by_cases g3 : erRd m₆ (r₆.tail.headD 0) ≠ 3
    · rw [ite_eq_left g3]
      cases ci <;> first
        | exact absurd rfl (hsp.2.2.2.1 g3 _ _)
        | exact RefE.ret rfl (CorePost.ret hS₁ rfl resCT_zero)
    rw [ite_eq_right g3]
    obtain ⟨cvT, caps, rfl, -⟩ := hsp.2.2.1 (Classical.not_not.mp g3)
    obtain ⟨heta, -, hnz, -⟩ := L.Arena.decCI_indInfo_rd (erRdOK _) hci₆
    dsimp only
    rw [heta, hnz]
    by_cases gz : erRd m₆ (r₆.tail.headD 0 + (CI.indCaps + Caps.neverZero)) = 0
    · rw [ite_eq_left gz]
      refine RefE.ret (y := none) ?_ (CorePost.ret hS₁ rfl resCT_zero)
      rw [ite_eq_right (by rw [gz]; simp)]; rfl
    rw [ite_eq_right gz]
    by_cases ge : erRd m₆ (r₆.tail.headD 0 + (CI.indCaps + Caps.eta)) ≠ 0
    · rw [ite_eq_left ge]
      refine RefE.ret (y := none) ?_ (CorePost.ret hS₁ rfl resCT_zero)
      rw [ite_eq_right (by rw [show (erRd m₆ (r₆.tail.headD 0 + (CI.indCaps + Caps.eta)) != 0) = true from
        bne_iff_ne.mpr ge]; simp)]; rfl
    rw [ite_eq_right ge]
    have ge' : erRd m₆ (r₆.tail.headD 0 + (CI.indCaps + Caps.eta)) = 0 := Classical.not_not.mp ge
    refine RefE.ret (y := some (decI c)) ?_ (CorePost.ret hS₁ (by simp [decCT]) (by simpa [ResCT] using hnw))
    rw [ite_eq_left (by rw [show (erRd m₆ (r₆.tail.headD 0 + (CI.indCaps + Caps.neverZero)) != 0) = true from
      bne_iff_ne.mpr gz, ge']; decide)]; rfl
  have hne : (cnt.toNat == np.toNat + nf.toNat) = false := by simpa using hcnt
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : cnt < np
  · rw [ite_eq_left h1]; exact RefE.ret rfl (CorePost.ret hS₁ rfl resCT_zero)
  rw [ite_eq_right h1, ite_eq_left (fun h => hcnt (by
    have h1' : np.toNat ≤ cnt.toNat := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h1)
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h1')] at this
    omega))]
  exact RefE.ret rfl (CorePost.ret hS₁ rfl resCT_zero)

include hq hfv in
/-- **`ctor_target_for` refines `ctorTargetFor`, both outcomes**: the eager bit (`eager`), else
`has_fvar` of the other side, then `ct_ref`. -/
theorem ctf_ref {G : Prop} (n : Nat) (m : Mem) (a : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode o e : Word) (eager : Bool)
    (heager : eager = decide ((mode >>> 1) &&& 1 ≠ 0)) (hS : CoreS dn m a vis fe M eb) (ho : HW o)
    (he : HW e) :
    RefE G (ctfE p n m mode vis o e) (ctorTargetFor fe eager (decE o) (decE e)) a
      (CorePost decCT dn m vis fe M eb ResCT) := by
  cases n with
  | zero => exact RefE.of_cls0 rfl
  | succ n =>
  simp only [ctfE]
  unfold ctorTargetFor
  subst heager
  refine RefE.splitNot (d := decide ((mode >>> 1) &&& 1 ≠ 0) = true) (fun h => by simpa using h)
    (fun h => by simpa using h) (fun _ _ => ?_) fun _ _ => ?_
  · refine RefE.bind_callW (fun _ => rfl) (hfv n ⟨m, Locals.init []⟩ a dn vis fe M eb o hS ho)
      fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
    dsimp only [ctfE.k_has_fvar]
    refine RefE.split (d := decBool r₁ = true) (fun h => by simpa [decBool] using h)
      (fun h => by simpa [decBool] using h)
      (fun _ _ => RefE.ret rfl (CorePost.ret hS₁ rfl resCT_zero)) fun _ _ => ?_
    simp only [ctfE.j1]
    exact RefE.lastE (K := ctfE.k_ctor_target p) (f := fun v => ([v.1.headD 0, v.1.tail.headD 0], v.2))
      (fun _ => rfl) (fun _ => rfl) id (ct_ref p hq hfv n m₁ _ dn vis fe M₁ eb e hS₁ he)
      fun _ _ _ _ h => ⟨h.after, h.res, h.valid⟩
  · simp only [ctfE.j1]
    exact RefE.lastE (K := ctfE.k_ctor_target p) (f := fun v => ([v.1.headD 0, v.1.tail.headD 0], v.2))
      (fun _ => rfl) (fun _ => rfl) id (ct_ref p hq hfv n m a dn vis fe M eb e hS he)
      fun _ _ _ _ h => ⟨h.after, h.res, h.valid⟩

end ct

/-! ## `ctor_head_against` -/

/-- **`ctor_head_against` refines `ctorHeadAgainst`, both outcomes** (reads only; its errors are
class `0`). -/
theorem cha_ref {G : Prop} (p : Prog) (hq : CtorProg p) (n : Nat) (m : Mem) (a : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb c w : Word)
    (hS : CoreS dn m a vis fe M eb) (hc : c.toNat < 2 ^ 32) (hw : HW w) :
    RefE G (chaE p n m vis c w) (ctorHeadAgainst fe (decI c) (decE w)) a
      (CorePost decCHA dn m vis fe M eb (fun _ => True)) := by
  cases n with
  | zero => exact RefE.of_cls0 rfl
  | succ n =>
  simp only [chaE]
  unfold ctorHeadAgainst
  have hR := hS.arena.base
  refine RefE.bindLift (fun _ => rfl) fun r₂ m₂ c₂ => ?_
  obtain ⟨s₂, hs₂, hm₂, -, hh, hgaf⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (getAppFn_refines' p hq.gaf n ⟨m, Locals.init []⟩ _ hR w hw) c₂
  have e₂ : m₂ = m := hs₂.symm.trans hm₂
  subst e₂
  refine ⟨_, _, hgaf, ?_⟩
  dsimp only [chaE.k_get_app_fn]
  generalize r₂.headD 0 = h at hh hgaf
  rw [L.Arena.decE_tag_const_beq _ hh]
  refine RefE.splitNot (d := decide (tagW h = 3) = true) (fun h3 => by simpa using h3)
    (fun h3 => by simpa using h3)
    (fun _ _ => RefE.ret rfl (CorePost.ret hS rfl trivial)) fun h3 _ => ?_
  have h3 : tagW h = 3 := by simpa using h3
  refine RefE.abort0 rfl fun hs => RefE.abort0 rfl fun hcc => ?_
  obtain ⟨hv, hnw, -⟩ := L.Ind.view_const_f _ _ hR h hh ⟨hs, by simpa using hcc⟩ h3
  refine RefE.bind_right (view_run _ _ _ hv) ?_
  dsimp only
  generalize tfld _ CONST (tierW h) (idxW h) 0 = d at hnw ⊢
  rw [L.Arena.decI_beq _ _ hnw hc]
  refine RefE.split (d := decide (d = c) = true) (fun h => by simpa using h) (fun h => by simpa using h)
    (fun _ _ => RefE.ret rfl (CorePost.ret hS rfl trivial)) fun _ _ => ?_
  refine RefE.onlySim (fun _ => rfl) (fun r₃ m₃ c₃ => triple_of_callW (s₀ := ⟨_, Locals.init []⟩)
    (envFind_refines p hq.envrow hq.baserow hq.envfind n _ vis d hS.env hnw) c₃) fun r₃ m₃ hq₃ => ?_
  obtain ⟨s₃, hs₃, hm₃, -, hfind, hfound⟩ := hq₃
  have e₃ : m₃ = m₂ := hs₃.symm.trans hm₃
  subst e₃
  dsimp only [chaE.k_env_find]
  by_cases h0 : r₃.headD 0 = 0
  · rw [ite_eq_left h0]
    have hnone : fe.find? (decI d) = none := by rw [hfind]; simp only [envFound, h0, ↓reduceIte]
    rw [hnone]
    exact RefE.ret rfl (CorePost.ret hS rfl trivial)
  rw [ite_eq_right h0]
  obtain ⟨ci, hci⟩ := hfound h0
  have hf' : fe.find? (decI d) = some ci := by
    rw [hfind]; simp only [envFound, h0, ↓reduceIte]; exact hci
  rw [hf']
  have hctor := L.Arena.decCI_ctorR (erRdOK _) hci
  by_cases h4 : erRd m₃ (r₃.tail.headD 0) ≠ 4
  · rw [ite_eq_left h4]
    cases ci <;> first
      | exact absurd rfl (hctor.2 h4 _ _ _ _)
      | exact RefE.ret rfl (CorePost.ret hS rfl trivial)
  rw [ite_eq_right h4]
  obtain ⟨cv, rfl, -⟩ := hctor.1 (Classical.not_not.mp h4)
  exact RefE.ret rfl (CorePost.ret hS rfl trivial)

end L.Arena
