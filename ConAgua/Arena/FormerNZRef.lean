module

public import ConAgua.Arena.FormerSortRef
public import ConAgua.Arena.LevelZero
import ConAgua.Arena.LevelArena
import ConAgua.Arena.CoreLevels
import ConAgua.Arena.PropReadRefine
import ConAgua.Arena.IndView
import ConAgua.Arena.WhnfSpineRefine
import all ConAgua.Arena.WhnfIota
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.LevelZero

@[expose] public section

/-!
# `lv_never` under `CoreS` (`(zeronessOf l).isNever`), the leaves of `former_never_zero_at`
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **`lv_never`'s model**: `lv_zero` lifted, the heap top put back. -/
l_model lvNeverW_spec (p : Prog) (hf : p.lookup "lv_never" = some lvNever)
  fns [hf ↦ lvNeverW] specs [callW_spec p n "lv_zero"] grind [arena_grind] fold [tierW, idxW]

/-- **`lv_never` is `(zeronessOf l).isNever` under `CoreS`**: the level heap above its top and the
top are all it writes (the top put back). -/
theorem lvNever_core {p : Prog} (hpn : p.lookup "lv_node" = some lvNode)
    (hpp : p.lookup "lh_push" = some lhPush) (hpz : p.lookup "lv_zero" = some lvZero)
    {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {u : Word} (hu : HW u) {L : Level}
    (hd : denoteL a.store.ls (decI u) = some L) {w : Word}
    (h : lvNeverW p n m u = some (w, m')) :
    w = (if (Level.zeronessOf L).isNever then 1 else 0) ∧ CoreS dn m' a vis fe M eb ∧ StackKept m m' := by
  rcases n with _ | n
  · simp [lvNeverW] at h
  rw [lvNeverW.arm1] at h
  rcases hc : callW p n "lv_zero" [u] m with _ | ⟨r, m₁⟩
  · rw [hc, lvNeverW.k_lv_zero.none] at h; cases h
  rw [hc, lvNeverW.k_lv_zero.arm1] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s', hs', -, hz⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lvZero_spec p hpn hpp hpz n ⟨m, Locals.init []⟩ u) hc
  rw [hs'] at hz
  have hl := denoteL_lvR hS.arena.base (decI u) L hd
  rw [decI_word_self u hu] at hl
  obtain ⟨he, hZ⟩ := zeroW_ok n _ _ _ _ _ hl hz
  have hf : MemFrame [LH] [192] m (m₁.set64 CTL 192 (rdW (m.arr64 CTL) 192)) :=
    he.memFrame.trans ((MemFrame.setCtl m₁ 192 _).mono (by simp) (by simp))
  obtain ⟨hS', hK⟩ := hS.frame hf (by simp [LH]) (by simp)
  refine ⟨?_, hS', hK⟩
  rcases hZ with ⟨hx, hpw⟩ | ⟨hx, ps, hpw, -⟩
  · rw [hx, hpw]; simp [PropWhen.isNever]
  · rw [hx, hpw]; simp [PropWhen.isNever]

/-- **`former_res_sort`'s model**: `pi_result` lifted. -/
l_model frsV_spec (p : Prog) (hf : p.lookup "former_res_sort" = some formerResSortL)
  fns [hf ↦ frsV] specs [callW_spec p n "pi_result"] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

/-- **`former_res_sort` refines `formerResSort`**, the found sort's word included (the twin's
state kept). -/
theorem frsV_ok {p : Prog} (hpr : p.lookup "pi_result" = some piResultL) {n : Nat} {m m' : Mem}
    {a : AState} {ty : Word} {r : List Word} (hR : ArenaR m a) (hty : HW ty)
    (h : frsV p n m ty = some (r, m')) :
    m' = m ∧ (ConRon.Arena.formerResSort (decE ty)).run a = .ok (decOS r, a) ∧ OkOS r := by
  rcases n with _ | n
  · simp [frsV] at h
  rw [frsV.arm1] at h
  rcases hc : callW p n "pi_result" [ty] m with _ | ⟨r1, m1⟩
  · rw [hc] at h; simp [frsV.k_pi_result] at h
  rw [hc] at h
  obtain ⟨s', hs', hm, -, hw, hrun⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (piResult_refines' p hpr n _ a hR ty hty) hc
  simp only at hm
  subst hs'
  rw [hm] at h
  have hrun' : (ConRon.Arena.formerResSort (decE ty)).run a =
      (if ((decE (r1.headD 0)).tag == ETag.sort) = true then
        (do match ← viewSort (decE (r1.headD 0)) with
          | none => failDanglingE
          | some s => pure (some s) : AM (Option LIdx)).run a
      else .ok (none, a)) := by
    simp only [ConRon.Arena.formerResSort, StateT.run_bind, hrun, except_ok_bind]
    split <;> rfl
  rw [decE_tag_sort_beq (hh := hw)] at hrun'
  simp only [frsV.k_pi_result] at h
  by_cases ht : tagW (r1.headD 0) = 2
  · rw [ite_eq_right (by simpa using ht)] at h
    split at h
    · cases h
    rename_i h1
    split at h
    · cases h
    rename_i h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hv := pr_viewSort_ok m a hR (r1.headD 0) hw ⟨h1, by have := UInt64.not_le.mp h2; exact this⟩ ht
    obtain ⟨-, hu⟩ := L.Ind.view_sort_f m a hR (r1.headD 0) hw ⟨h1, UInt64.not_le.mp h2⟩ ht
    refine ⟨rfl, ?_, fun _ => hu⟩
    rw [hrun', ite_eq_left (by simpa using ht)]
    simp only [StateT.run_bind]
    rw [viewSort_run' hv]
    simp [decOS]; rfl
  · rw [ite_eq_left (by simpa using ht)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_, by simp [OkOS]⟩
    rw [hrun', ite_eq_right (by simpa using ht)]
    simp [decOS]

end L.Arena
