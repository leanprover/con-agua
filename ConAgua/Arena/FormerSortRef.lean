module

import ConAgua.Arena.InferBodyIntern
public import ConAgua.Arena.WhnfIota
public import Std.Tactic.BVDecide.Normalize.Bool
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndView
import ConAgua.Arena.RefWalk
import ConRon.Bridge.Rel
import ConAgua.Arena.InferBodyLet
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.WhnfIota
public import ConAgua.Checker.NoVerdictFns
public import ConAgua.Arena.RefECore
public import ConAgua.Arena.KnotE

@[expose] public section

/-!
# `former_sort_loop`: official's walk to a family's sort (`formerSortLoop`)

One unified model and one refinement for both outcomes (`RefE` with `CorePost`): the `whnf` slot
through its run, `intern_fvar` and `inst_entry` lifted, the recursive call through its run.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **`former_sort_loop`'s unified model** (the `whnf` slot and the recursive call through their
runs, the interning and `inst_entry` lifted). -/
l_model fslE_spec (p : Prog) (hf : p.lookup "former_sort_loop" = some formerSortLoopL)
  fns [hf ↦ fslE list]
  specs [callW_spec p n "intern_fvar", callW_spec p n "inst_entry"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `former_sort_loop`'s result words read back: `(0, _)` is `none`, `(1, u)` the sort `u`. -/
def decOS (r : List Word) : Option LIdx :=
  if r.headD 0 = 0 then none else some (decI (r.tail.headD 0))

/-- The result words' validity: a found sort is a handle word. -/
def OkOS (r : List Word) : Prop := r.headD 0 ≠ 0 → (r.tail.headD 0).toNat < 2 ^ 32

theorem internFVar_coreSpec' {p : Prog} (hpf : p.lookup "fvar_find" = some fvarFind)
    (hpp : p.lookup "fvar_push" = some fvarPush) (hpi : p.lookup "intern_fvar" = some internFVar)
    (n : Nat) (s₀ : St) {a : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn s₀.mem a vis fe M eb) (u ty : Word) (hty : HW ty) :
    CoreSpec p n "intern_fvar" [u, ty] (internE (.fvar u.toNat (decE ty))) decH s₀ a dn vis fe M eb :=
  L.M.triple_of_run fun _ _ _ hp hr => by
    subst hp
    obtain ⟨hl, hfv⟩ := L.M.of_run (P := fun s => s = _) rfl hr
      (internFVar_spec p hpf hpp hpi n _ u ty)
    exact ⟨hl, internFVar_core hS u ty hty _ hfv⟩

/-- What `former_sort_loop`'s refinement needs of a program. -/
structure FslProg (p : Prog) : Prop where
  fsl : p.lookup "former_sort_loop" = some formerSortLoopL
  fvf : p.lookup "fvar_find" = some fvarFind
  fvp : p.lookup "fvar_push" = some fvarPush
  fvi : p.lookup "intern_fvar" = some internFVar
  inst : IotaInst1OK p

theorem getSort_of_get' (t : ETables) (i : EIdx) (u : LIdx) (ht : i.tag = ETag.sort)
    (h : t.get i = some (.sort u)) : t.getSort i = some u := by
  unfold ETables.get at h
  rw [ht] at h
  simp only [show (ETag.sort == ETag.bvar) = false by decide,
    show (ETag.sort == ETag.fvar) = false by decide, show (ETag.sort == ETag.sort) = true by decide,
    ite_true, ite_false, Bool.false_eq_true] at h
  unfold ETables.getSort
  cases e : t.sorts.node? i.idxNat with
  | none => rw [e] at h; cases h
  | some r => rw [e] at h; simp at h; simp [h]

theorem viewSort_of_view' (st : EStore) (i : EIdx) (u : LIdx) (ht : i.tag = ETag.sort)
    (h : st.view i = some (.sort u)) : st.viewSort i = some u := by
  unfold EStore.view at h; unfold EStore.viewSort EStore.persGetSort
  split at h
  · rw [ite_eq_left (by assumption)]; exact getSort_of_get' _ _ _ ht h
  · rw [ite_eq_right (by assumption)]
    split at h
    · rw [ite_eq_left (by assumption)]; exact getSort_of_get' _ _ _ ht h
    · cases h

theorem viewSort_run' {a : AState} {h : EIdx} {u : Option LIdx} (hv : a.store.viewSort h = u) :
    (viewSort h).run a = .ok (u, a) := by
  simp [viewSort, hv, StateT.run_get]; rfl

theorem viewBind_runF {a : AState} {h : EIdx} {u : Option (EIdx × EIdx)} (hv : a.store.viewBind h = u) :
    (viewBind h).run a = .ok (u, a) := by
  simp [viewBind, hv, StateT.run_get]; rfl

theorem decE_tag_forall_beq' (e : Word) (hh : HW e) :
    ((decE e).tag == ETag.forallE) = decide (tagW e = 6) :=
  decE_tag_beq e hh 6 (by decide)

section fsl
variable (p : Prog) (hp : FslProg p)
include hp

/-- **`former_sort_loop` refines `formerSortLoop`, both outcomes**, at every L fuel up to `n + 1`:
the errors are the `whnf` slot's (and the recursive call's). -/
theorem fsl_ref (n F : Nat) (hk : KnotUpTo p n) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) :
    ∀ (k : Nat), k ≤ n + 1 → ∀ (m : Mem) (a : AState) (M : ModeMaps) (d c e : Word),
      CoreS dn m a vis fe M eb → HW e →
      RefE (KnotUpToE p n) (fslE p k m mode vis d c e)
        (formerSortLoop (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat c.toNat (decE e)) a
        (CorePost decOS dn m vis fe M eb OkOS) := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ _; rw [fslE.eq_def]; exact RefE.of_cls0 (by simp)
  | succ k ih =>
  intro hkn m a M d c e hS he
  have hkn' : k ≤ n := by omega
  have hK := hk k hkn'
  have hs : SlotPre ⟨m, Locals.init []⟩ a dn vis fe M eb mode := ⟨hS, hm4, hebm⟩
  rw [fslE.eq_def]; dsimp only
  by_cases hc : c = 0
  · have hc0 : c.toNat = 0 := by simp [hc]
    rw [hc0, formerSortLoop]
    refine RefE.bind_callE (fun _ => fslE.k_whnf.none ..) (hK.whnf F _ a dn vis fe M eb mode d e (by omega) (by omega) hs he)
      (fun hG => (hG k hkn').whnf F _ a dn vis fe M eb mode d e (by omega) (by omega) hs he)
      fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
    simp only [fslE.k_whnf, hc, ↓reduceIte]
    by_cases g1 : tagW (r₁.headD 0) = 2
    · rw [ite_eq_right (show ¬ tagW (r₁.headD 0) ≠ 2 from by simpa using g1)]
      have ht : ((decH r₁).tag == ETag.sort) = true := by
        simp only [decH]; rw [decE_tag_sort_beq _ h₁.resOk]; simpa using g1
      rw [ite_eq_left ht]
      refine RefE.abort0 (by rfl) fun g2 => ?_
      refine RefE.abort0 (by rfl) fun g3 => ?_
      obtain ⟨hv, hu⟩ := L.Ind.view_sort_f m₁ _ hS₁.arena.base (r₁.headD 0) h₁.resOk
        ⟨g2, UInt64.not_le.mp g3⟩ g1
      have hvs := viewSort_of_view' _ _ _ (by
        have := decE_tag_sort_beq (e := r₁.headD 0) h₁.resOk; rw [g1] at this; simpa using this) hv
      exact RefE.bind_right (viewSort_run' hvs) (RefE.ret rfl ⟨⟨M₁, hS₁, KeptAll.refl _ _, StackKept.refl _⟩,
        by simp [decOS], fun _ => hu⟩)
    · rw [ite_eq_left (show tagW (r₁.headD 0) ≠ 2 from g1)]
      have ht : ¬ ((decH r₁).tag == ETag.sort) = true := by
        simp only [decH]; rw [decE_tag_sort_beq _ h₁.resOk]; simpa using g1
      rw [ite_eq_right ht]
      exact RefE.ret rfl ⟨⟨M₁, hS₁, KeptAll.refl _ _, StackKept.refl _⟩, by simp [decOS], by simp [OkOS]⟩
  · have hcs : c.toNat = (c - 1).toNat + 1 := by
      have : c.toNat ≠ 0 := fun h => hc (UInt64.toNat_inj.mp (by simpa using h))
      rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp; omega
    rw [hcs, formerSortLoop]
    refine RefE.bind_callE (fun _ => fslE.k_whnf.none ..) (hK.whnf F _ a dn vis fe M eb mode d e (by omega) (by omega) hs he)
      (fun hG => (hG k hkn').whnf F _ a dn vis fe M eb mode d e (by omega) (by omega) hs he)
      fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
    simp only [fslE.k_whnf, hc, ↓reduceIte]
    by_cases g1 : tagW (r₁.headD 0) = 6
    · rw [ite_eq_right (show ¬ tagW (r₁.headD 0) ≠ 6 from by simpa using g1)]
      have ht : ((decH r₁).tag == ETag.forallE) = true := by
        simp only [decH]; rw [decE_tag_forall_beq' _ h₁.resOk]; simpa using g1
      rw [ite_eq_left ht]
      refine RefE.abort0 (by rfl) fun g2 => ?_
      refine RefE.abort0 (by rfl) fun g3 => ?_
      obtain ⟨hv, hty, hb⟩ := view_forall m₁ _ hS₁.arena.base (r₁.headD 0) h₁.resOk ⟨g2, UInt64.not_le.mp g3⟩ g1
      refine RefE.bind_right (viewBind_runF (ConRon.Bridge.viewBind_of_view hv (Or.inr rfl))) ?_
      dsimp only
      refine RefE.abort0 (by rfl) fun hd => ?_
      refine RefE.bind_callW (fun _ => fslE.k_intern_fvar.none ..)
        (internFVar_coreSpec' hp.fvf hp.fvp hp.fvi k ⟨m₁, Locals.init []⟩ hS₁ d _ hty)
        fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ _ => ?_
      rw [fslE.k_intern_fvar.arm1]
      refine RefE.bind_callW (fun _ => fslE.k_inst_entry.none ..)
        (hp.inst k ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb _ (r₃.headD 0) 0 hS₃ hb)
        fun r₄ m₄ _ h₄ => RefE.after_core (w := id) h₄ fun M₄ hS₄ _ => ?_
      rw [fslE.k_inst_entry.arm1]
      have h1 := ih (by omega) m₄ _ M₄ (d + 1) (c - 1) (r₄.headD 0) hS₄ h₄.resOk
      rw [toNat_succ_of_ne hd] at h1
      exact RefE.tail_relist (g := fun r => [r.headD 0, r.tail.headD 0])
        (fun _ => fslE.k_former_sort_loop.none ..) (fun ⟨_, _⟩ => fslE.k_former_sort_loop.arm1 ..)
        (fun r => by simp [decOS]) (fun r h => by simpa [OkOS] using h) id h1
    · rw [ite_eq_left (show tagW (r₁.headD 0) ≠ 6 from g1)]
      have ht : ¬ ((decH r₁).tag == ETag.forallE) = true := by
        simp only [decH]; rw [decE_tag_forall_beq' _ h₁.resOk]; simpa using g1
      rw [ite_eq_right ht]
      exact RefE.ret rfl ⟨⟨M₁, hS₁, KeptAll.refl _ _, StackKept.refl _⟩, by simp [decOS], by simp [OkOS]⟩

end fsl

end L.Arena
