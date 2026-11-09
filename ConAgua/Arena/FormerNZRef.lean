module

public import ConAgua.Arena.FormerSortRef
public import ConAgua.Arena.LevelZero
public import ConAgua.Arena.LevelSubstL
import ConAgua.Arena.LevelArena
import ConAgua.Arena.CoreLevels
import ConAgua.Arena.PropReadRefine
import ConAgua.Arena.IndView
import ConAgua.Arena.DerRel
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
    m' = m ∧ (ConRon.Arena.formerResSort (decE ty)).run a = .ok (decOS r, a) ∧ OkOS r ∧
      (r.headD 0 ≠ 0 → ∃ h, a.store.view h = some (.sort (decI (r.tail.headD 0)))) := by
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
    obtain ⟨hvw, hu⟩ := L.Ind.view_sort_f m a hR (r1.headD 0) hw ⟨h1, UInt64.not_le.mp h2⟩ ht
    refine ⟨rfl, ?_, fun _ => hu, fun _ => ⟨_, hvw⟩⟩
    rw [hrun', ite_eq_left (by simpa using ht)]
    simp only [StateT.run_bind]
    rw [viewSort_run' hv]
    simp [decOS]; rfl
  · rw [ite_eq_left (by simpa using ht)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_, by simp [OkOS], by simp⟩
    rw [hrun', ite_eq_right (by simpa using ht)]
    simp [decOS]

/-- **`former_z`'s model**: `former_res_sort` and `lv_zero` lifted. -/
l_model frzW_spec (p : Prog) (hf : p.lookup "former_z" = some formerZL)
  fns [hf ↦ frzW] specs [callW_spec p n "former_res_sort", callW_spec p n "lv_zero"]
  grind [arena_grind] fold [tierW, idxW]

/-- **The relation across a write of the level readback cache** (`readLevelM`). -/
theorem CoreS.readLC' {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    (X : Std.HashMap LIdx Level) (hX : ReadLCOK { a with caches := { a.caches with readLC := X } }) :
    CoreS dn m { a with caches := { a.caches with readLC := X } } vis fe M eb :=
  ⟨⟨ArenaR.caches_irrel _ hS.arena.base, DerR.of_store _ _ _ hS.arena.der rfl⟩, hS.core.readLC X,
    hS.pins, hS.env, hX, fun h l e => hS.readLs h l e, hS.nwf, hS.erec, hS.spn, hS.memos, hS.bstk,
    hS.den.caches rfl rfl rfl, hS.mode⟩

/-- **`former_z` refines `formerZ`** (the twin's state kept): the datum `(kd, o, c)` with the names
on the heap above the top at entry. -/
theorem frz_ok {p : Prog} (hpr : p.lookup "pi_result" = some piResultL)
    (hfr : p.lookup "former_res_sort" = some formerResSortL) (hpn : p.lookup "lv_node" = some lvNode)
    (hpp : p.lookup "lh_push" = some lhPush) (hpz : p.lookup "lv_zero" = some lvZero)
    {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {ty : Word} (hty : HW ty)
    {cv : IConstantVal} (hcv : cv.type = decE ty) {r : List Word} (h : frzW p n m ty = some (r, m')) :
    ∃ pw a', (ConRon.Arena.formerZ cv).run a = .ok (pw, a') ∧ a'.store = a.store ∧
      CoreS dn m' a' vis fe M eb ∧ StackKept m m' ∧ HeapExt m m' ∧
      PWR (nameN a.store.lss.ls.ns) m' LH (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0) pw ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ (htop m').toNat := by
  rcases n with _ | n
  · simp [frzW] at h
  rw [frzW.arm1] at h
  rcases hc : callW p n "former_res_sort" [ty] m with _ | ⟨r1, m1⟩
  · rw [hc, frzW.k_former_res_sort.none] at h; cases h
  rw [hc] at h
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (frsV_spec p hfr n ⟨m, Locals.init []⟩ ty) hc
  rw [hs1] at hW1
  obtain ⟨rfl, hrun1, hok1, hv1⟩ := frsV_ok hpr hS.arena.base hty hW1
  by_cases h0 : r1.headD 0 = 0
  · rw [frzW.k_former_res_sort.arm1 _ _ _ _ _ h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨.ifAllZero [], a, by
      simp only [ConRon.Arena.formerZ, hcv, StateT.run_bind, hrun1, except_ok_bind, decOS, h0, ↓reduceIte]; rfl,
      rfl, hS, StackKept.refl _, HeapExt.refl _,
      Or.inr ⟨by simp, [], rfl, by simpa using NmsR.nil⟩, by simp [htop]⟩
  rw [frzW.k_former_res_sort.arm2 _ _ _ _ _ h0] at h
  obtain ⟨hh, hview⟩ := hv1 h0
  obtain ⟨l, hl⟩ := hS.den.sort _ _ hview
  have hu : HW (r1.tail.headD 0) := hok1 h0
  have hlv : LvR (nameN a.store.lss.ls.ns) m1 (r1.tail.headD 0) l := by
    have := denoteL_lvR hS.arena.base (decI (r1.tail.headD 0)) l hl
    rwa [decI_word_self _ hu] at this
  rcases hc2 : callW p n "lv_zero" [r1.tail.headD 0] m1 with _ | ⟨r2, m2⟩
  · rw [hc2, frzW.k_lv_zero.none] at h; cases h
  rw [hc2] at h
  obtain ⟨s2, hs2, -, hz2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (lvZero_spec p hpn hpp hpz n ⟨m1, Locals.init []⟩ _) hc2
  rw [hs2] at hz2
  obtain ⟨he, hZ⟩ := zeroW_ok n _ _ _ _ _ hlv hz2
  obtain ⟨X, hX, hXok⟩ := readLevelM_run' a _ l hl hS.readL
  have hrun : (ConRon.Arena.formerZ cv).run a =
      .ok (Level.zeronessOf l, { a with caches := { a.caches with readLC := X } }) := by
    simp only [ConRon.Arena.formerZ, hcv, StateT.run_bind, hrun1, except_ok_bind, decOS, ite_eq_right h0]
    rw [hX]; rfl
  have hS₁ := hS.readLC' X hXok
  obtain ⟨hS₂, hK₂⟩ := hS₁.frame he.memFrame (by simp [LH]) (by simp)
  rcases hZ with ⟨hx, hpw⟩ | ⟨hx, ps, hpw, hnm⟩
  · rw [frzW.k_lv_zero.arm1 _ _ _ _ (by rw [hx]; decide)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, hrun, rfl, hS₂, hK₂, he, Or.inl ⟨rfl, hpw⟩, by simp⟩
  · rw [frzW.k_lv_zero.arm2 _ _ _ _ hx] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ht := he.top
    refine ⟨_, _, hrun, rfl, hS₂, hK₂, he, Or.inr ⟨by simp, ps, hpw, by simpa [htop] using hnm⟩, ?_⟩
    simp only [List.headD_cons, List.tail_cons]
    have : (rdW (m2.arr64 CTL) 192 - rdW (m1.arr64 CTL) 192).toNat =
        (rdW (m2.arr64 CTL) 192).toNat - (rdW (m1.arr64 CTL) 192).toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa [htop] using ht)]
    simp only [htop] at ht ⊢; omega

end L.Arena
