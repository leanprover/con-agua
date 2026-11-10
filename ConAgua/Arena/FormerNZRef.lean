module

public import ConAgua.Arena.FormerSortRef
public import ConAgua.Arena.PropReadW
import ConAgua.Arena.InferFieldSort
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Rel
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.StoreDenIntern
import ConAgua.Arena.KnotMono
import ConAgua.Arena.CoreLevels
import ConAgua.Arena.PropReadRefine
import ConAgua.Arena.DerRel
import all ConAgua.Arena.WhnfIota
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.LevelZero
import ConAgua.L.WordOff
import ConAgua.Arena.InstLPLevel

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
    rw [L.Arena.viewSort_run hv]
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
  have hS₁ := hS.withReadLC X hXok
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

/-- **`former_never_zero`'s model**: `former_z`, `ls_node`, `lv_spw` lifted, the heap top put back. -/
l_model fnzW_spec (p : Prog) (hf : p.lookup "former_never_zero" = some formerNeverZeroL)
  fns [hf ↦ fnzW] specs [callW_spec p n "former_z", callW_spec p n "ls_node", callW_spec p n "lv_spw"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- An `indInfo` record's constant value decodes at `q + 1`. -/
theorem decCI_ind_cv {R : Nat → Option Word} {q : Nat} {cv : IConstantVal} {caps : IIndCaps}
    (h : decCI R q = some (.indInfo cv caps)) : decCV R (q + 1) = some cv := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, -, h⟩ := h
  rcases k with _ | _ | _ | _ | _ | _ | k <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq, and_false, exists_false] at h
  obtain ⟨cv', hcv, caps', -, he⟩ := h
  cases he; exact hcv

/-- **`former_never_zero` refines `formerNeverZero`** (the heap top put back): the datum of
`former_z` substituted (`lv_spw`, the keys the family's level parameters, the values `us`). -/
theorem fnz_ok {p : Prog} (hpp : PropReadProg p) (hpr : p.lookup "pi_result" = some piResultL)
    (hfr : p.lookup "former_res_sort" = some formerResSortL) (hfz : p.lookup "former_z" = some formerZL)
    {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {q us : Word} {cvT : IConstantVal}
    {caps : IIndCaps} (hci : decCI (erecP m) q.toNat = some (.indInfo cvT caps))
    (hks : ∃ ks, cvT.levelParams.mapM (denoteN a.store.ns) = some ks) (hus : HW us)
    (hlsd : ∃ ls, denoteLs a.store.lss (decI us) = some ls) {w : Word}
    (h : fnzW p n m q us = some (w, m')) :
    ∃ a', (ConRon.Arena.formerNeverZero cvT (decI us)).run a = .ok (w != 0, a') ∧ CoreS dn m' a' vis fe M eb ∧
      StackKept m m' ∧ HW w := by
  rcases n with _ | n
  · simp [fnzW] at h
  rw [fnzW.arm1] at h
  obtain ⟨hl, -, hty, hty32⟩ := decCV_rd (erRdOK m) (L.Arena.decCI_ind_cv hci)
  change fnzW.k_former_z p n us (erRd m (q + 2)) (erRd m (q + 3)) (rdW (m.arr64 CTL) 192)
    (callW p n "former_z" [erRd m (q + 4)] m) = some (w, m') at h
  rcases c1 : callW p n "former_z" [erRd m (q + 4)] m with _ | ⟨r1, m1⟩
  · rw [c1, fnzW.k_former_z.none] at h; cases h
  rw [c1, fnzW.k_former_z.arm1] at h
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (frzW_spec p hfz n ⟨m, Locals.init []⟩ _) c1
  rw [hs1] at hW1
  obtain ⟨pw, a1, hrun1, hst1, hS1, hK1, he1, hpwr, hb1⟩ :=
    frz_ok hpr hfr (hpp.get "lv_node") (hpp.get "lh_push") (hpp.get "lv_zero") hS hty32 hty hW1
  -- the values
  obtain ⟨vs, hv⟩ := hlsd
  obtain ⟨ids, hvw, hdl⟩ := denoteLs_view a (decI us) vs hv
  have hR1 := hS1.arena.base
  rw [← hst1] at hvw hdl
  obtain ⟨e2, t2, s2⟩ := lsNodeW_store hR1 hus hvw
  rcases c2 : callW p n "ls_node" [us] m1 with _ | ⟨r2, m2⟩
  · rw [c2, fnzW.k_ls_node.none] at h; cases h
  obtain ⟨t, ht, hts, -, hr2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (lsNode_spec p (hpp.get "ls_node") n _ us) c2
  have hm2 : m1 = m2 := by rw [← ht, hts]
  subst hm2
  rw [e2] at hr2
  subst hr2
  rw [c2] at h
  -- the twin
  obtain ⟨ks, hk⟩ := hks
  rw [← hst1] at hk
  obtain ⟨X, hX, hcX⟩ := L.Arena.readNamesM_run' cvT.levelParams a1 ks hk hS1.den.readN
  obtain ⟨Y, hY, hcY⟩ := readLevelsM_run' { a1 with caches := { a1.caches with readNC := X } }
    (decI us) vs (by rw [← hst1] at hv; exact hv) (by exact hS1.readLs)
  have hrun : ∀ b, (ConLeche.Level.substPW ks vs pw).isNever = b →
      (ConRon.Arena.formerNeverZero cvT (decI us)).run a =
        .ok (b, { a1 with caches := { a1.caches with readNC := X, readLsC := Y } }) := by
    intro b hb
    simp only [ConRon.Arena.formerNeverZero, StateT.run_bind, hrun1, except_ok_bind, hX, hY, hb]
    rfl
  have hS1' := CoreS.readCaches hS1 X Y (by exact hcY) hcX
  have he1' : erecP m1 = erecP m := erecP_frame he1.memFrame (by decide) (by decide) (by decide) (by decide)
  rcases hpwr with ⟨hw0, rfl⟩ | ⟨hw0, ps, rfl, hnm⟩
  · rw [fnzW.k_ls_node.arm1 _ _ _ _ _ _ _ _ _ _ hw0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hS', hK'⟩ := hS1'.frame ((MemFrame.setCtl m1 192 (rdW (m.arr64 CTL) 192)).mono
      (A' := [LH]) (C' := [192]) (by simp) (by simp))
      (fun b hb => by simp at hb; subst hb; decide) (fun x hx => by simp at hx; subst hx; decide)
    exact ⟨_, hrun true rfl, hS', hK1.trans hK', by unfold HW; decide⟩
  · rw [fnzW.k_ls_node.arm2 _ _ _ _ _ _ _ _ _ _ hw0] at h
    simp only [List.headD_cons, List.tail_cons] at h
    have hN := nameN_rel _ hS1.nwf
    have hvs := (lvsR_of_slice hR1 ids vs _ _ s2 (by have := m1.top.toNat_lt; have := hR1.lit.1.top41; omega)
      hdl).toAR
    have hkr : NmsK (nameN a1.store.lss.ls.ns) m1 (keyT EREC) (erRd m (q + 2)) (erRd m (q + 3)) ks :=
      nmsAR_of_hslice _ _ _ cvT.levelParams ks _ _ rfl (by rw [he1']; exact hl) hk
    rcases c3 : callW p n "lv_spw" [r1.tail.headD 0, r1.tail.tail.headD 0, erRd m (q + 2),
        erRd m (q + 3), tfld m1 LVLS (tierW us) (idxW us) 0, tfld m1 LVLS (tierW us) (idxW us) 1] m1
      with _ | ⟨r3, m3⟩
    · rw [c3, fnzW.k_lv_spw.none] at h; cases h
    rw [c3, fnzW.k_lv_spw.arm1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨t3, ht3, -, hz⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (lvSpw_spec EREC POOL LH p (hpp.get "lv_lookup") (hpp.get "lv_node") (hpp.get "lh_push")
        (hpp.get "lv_zero") (hpp.get "lv_spw") n ⟨m1, Locals.init []⟩ _ _ _ _ _ _) c3
    rw [ht3] at hz
    obtain ⟨he3, hZ⟩ := spwW_ok_lh hN (keyT_heap (by decide)) (by decide) ks vs n _ _ _ _ _ _ _ _ _ _
      (by rw [hst1]; exact hnm) (by simpa using hb1) hkr hvs hz
    obtain ⟨hS3, hK3⟩ := hS1'.frame (he3.memFrame.trans ((MemFrame.setCtl m3 192 (rdW (m.arr64 CTL) 192)).mono
      (A' := [LH]) (C' := [192]) (by simp) (by simp)))
      (fun b hb => by simp at hb; subst hb; decide) (fun x hx => by simp at hx; subst hx; decide)
    have hsub : ConLeche.Level.substPW ks vs (.ifAllZero ps) = PropWhen.bindZ.go (spwF ks vs) ps := rfl
    rcases hZ with ⟨hx, hpw⟩ | ⟨hx, qs, hpw, -⟩
    · rw [hx]; exact ⟨_, hrun true (by rw [hsub, hpw]; rfl), hS3, hK1.trans hK3, by unfold HW; decide⟩
    · rw [hx]; exact ⟨_, hrun false (by rw [hsub, hpw]; rfl), hS3, hK1.trans hK3, by unfold HW; decide⟩

/-- **`former_never_zero_at`'s unified model** (`former_sort_loop` through its unified model, the
other callees lifted). -/
l_model fnzaE_spec (p : Prog) (hf : p.lookup "former_never_zero_at" = some formerNeverZeroAtL)
  (hs : p.lookup "former_sort_loop" = some formerSortLoopL)
  fns [hf ↦ fnzaE list]
  specs [callW_spec p n "former_res_sort", callW_spec p n "former_never_zero", callW_spec p n "inst_lp",
    fslE_spec p hs n, callW_spec p n "lv_never"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `formerSortLoop`'s found sort is a sort node of the store it ends at. -/
theorem fsl_sortView (r : CoreFnsA) : ∀ (n d : Nat) (e : EIdx) (a a' : AState) (s : LIdx),
    (ConRon.Arena.formerSortLoop r d n e).run a = .ok (some s, a') → ∃ h, a'.store.view h = some (.sort s)
  | 0, d, e, a, a', s, h => by
    simp only [ConRon.Arena.formerSortLoop, StateT.run_bind] at h
    rcases hw : (r.whnf d e).run a with ce | ⟨w, a1⟩ <;> rw [hw] at h
    · cases h
    simp only [except_ok_bind] at h
    split at h
    · rename_i htg
      rw [StateT.run_bind, L.Arena.viewSort_run rfl, except_ok_bind] at h
      split at h
      · cases h
      · rename_i u hu
        simp only [StateT.run_pure] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨w, ConRon.Bridge.view_of_viewSort (by simpa using htg) hu⟩
    · cases h
  | n + 1, d, e, a, a', s, h => by
    simp only [ConRon.Arena.formerSortLoop, StateT.run_bind] at h
    rcases hw : (r.whnf d e).run a with ce | ⟨w, a1⟩ <;> rw [hw] at h
    · cases h
    simp only [except_ok_bind] at h
    split at h
    · rw [StateT.run_bind, viewBind_runF rfl, except_ok_bind] at h
      split at h
      · cases h
      · rename_i dom b _
        simp only [StateT.run_bind] at h
        rcases h1 : (internE (.fvar d dom)).run a1 with ce | ⟨fv, a2⟩ <;> rw [h1] at h
        · cases h
        simp only [except_ok_bind] at h
        rcases h2 : (instantiate1Fast coreWalkFuel b fv 0).run a2 with ce | ⟨b2, a3⟩ <;> rw [h2] at h
        · cases h
        simp only [except_ok_bind] at h
        exact fsl_sortView r n (d + 1) b2 a3 a' s h
    · cases h

/-- An `indInfo` record's `nIdx` (`q + 11`) and `nparams` (`q + 17`) words. -/
theorem decCI_ind_n {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {cv : IConstantVal} {caps : IIndCaps} (h : decCI R q.toNat = some (.indInfo cv caps)) :
    caps.nIdx = (rd (q + 11)).toNat ∧ caps.nparams = (rd (q + 17)).toNat := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, -, h⟩ := h
  rcases k with _ | _ | _ | _ | _ | _ | k <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq, and_false, exists_false] at h
  obtain ⟨cv', -, caps', hcaps, he⟩ := h
  cases he
  simp only [decCaps, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hcaps
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ni, hni, _, _, np, hnp, _, _, hc⟩ := hcaps
  simp only [Option.some.injEq] at hc
  subst hc
  simp only [nat?, Option.map_eq_some_iff] at hni hnp
  obtain ⟨w1, hw1, rfl⟩ := hni
  obtain ⟨w2, hw2, rfl⟩ := hnp
  have e1 : rd (q + 11) = w1 := hR.offN (k := 11) (by simpa [Nat.add_assoc] using hw1) (by decide)
  have e2 : rd (q + 17) = w2 := hR.offN (k := 17) (by simpa [Nat.add_assoc] using hw2) (by decide)
  exact ⟨by rw [e1], by rw [e2]⟩

/-- What `former_never_zero_at`'s refinement needs of a program. -/
structure FnzaProg (p : Prog) : Prop extends FslProg p where
  fnza : p.lookup "former_never_zero_at" = some formerNeverZeroAtL
  pr : p.lookup "pi_result" = some piResultL
  frs : p.lookup "former_res_sort" = some formerResSortL
  fz : p.lookup "former_z" = some formerZL
  fnz : p.lookup "former_never_zero" = some formerNeverZeroL
  lvn : p.lookup "lv_never" = some lvNever
  prop : PropReadProg p
  ilp : InstLPOK p

/-- **`formerNeverZeroAt` keeps the store's `sort`/`const` views** (the knot only extends the
store, `knot_smono`). -/
theorem formerNeverZeroAt_fwd {mode : ConLeche.CheckMode} {eager : Bool} {fe : IFEnv} {F : Nat}
    {cvT : IConstantVal} {caps : IIndCaps} {us : LsIdx} {a a' : AState} {b : Bool}
    (h : (formerNeverZeroAt (coreKnot mode eager fe id F) cvT caps us).run a = .ok (b, a')) :
    ∀ x w, IsSC w → a.store.view x = some w → a'.store.view x = some w :=
  fun x w _ hv => ((KM.ConRon.Arena.formerNeverZeroAt _ cvT caps us (knot_smono mode fe F eager)).run h).view x w hv

section fnza
variable (p : Prog) (hp : FnzaProg p)
include hp

/-- **`former_never_zero_at` refines `formerNeverZeroAt`, both outcomes**: the errors are
`former_sort_loop`'s (the `whnf` slot's). -/
theorem fnza_ref (n F : Nat) (hk : KnotUpTo p n) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (m : Mem) (a : AState) (M : ModeMaps)
    (q us : Word) (cvT : IConstantVal) (caps : IIndCaps) (hS : CoreS dn m a vis fe M eb)
    (hci : decCI (erecP m) q.toNat = some (.indInfo cvT caps))
    (hks : ∃ ks, cvT.levelParams.mapM (denoteN a.store.ns) = some ks) (hus : HW us)
    (hlsd : ∃ ls, denoteLs a.store.lss (decI us) = some ls) :
    RefE (KnotUpToE p n) (fnzaE p (n + 1) m mode vis q us)
      (formerNeverZeroAt (coreKnot (decMode mode) (decEager mode) fe id F) cvT caps (decI us)) a
      (CorePost decBool dn m vis fe M eb ResH) := by
  obtain ⟨hl, -, hty, hty32⟩ := decCV_rd (erRdOK m) (L.Arena.decCI_ind_cv hci)
  obtain ⟨hni, hnp⟩ := decCI_ind_n (erRdOK m) hci
  simp only [erRd] at hl hty hty32 hni hnp
  rw [fnzaE.eq_2]
  split
  · exact RefE.of_cls0 rfl
  rename_i hov
  have hn' := L.toNat_add_of_not_lt hov
  unfold ConRon.Arena.formerNeverZeroAt
  refine RefE.bindLift (fun _ => fnzaE.k_former_res_sort.none ..) fun r1 m1 c1 => ?_
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (frsV_spec p hp.frs n ⟨m, Locals.init []⟩ _) c1
  rw [hs1] at hW1
  obtain ⟨hm1, hrun1, -, -⟩ := frsV_ok hp.pr hS.arena.base hty32 hW1
  clear hs1
  subst hm1
  refine ⟨_, _, by rw [hty]; exact hrun1, ?_⟩
  by_cases g1 : r1.headD 0 ≠ 0
  · rw [fnzaE.k_former_res_sort.arm1 _ _ _ _ _ _ _ _ _ _ _ _ g1]
    simp only [decOS, show ¬ r1.headD 0 = 0 from g1, ↓reduceIte]
    rcases c2 : callW p n "former_never_zero" [q, us] m1 with _ | ⟨r2, m2⟩
    · rw [liftE_none, fnzaE.k_former_never_zero.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some, fnzaE.k_former_never_zero.arm1]
    obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (fnzW_spec p hp.fnz n ⟨m1, Locals.init []⟩ q us) c2
    rw [hs2] at hW2
    obtain ⟨a', hrun2, hS2, hK2, hw2⟩ := fnz_ok hp.prop hp.pr hp.frs hp.fz hS hci hks hus hlsd hW2
    exact RefE.ret hrun2 ⟨⟨M, hS2, KeptAll.refl _ _, hK2⟩, rfl, hw2⟩
  have g1' : r1.headD 0 = 0 := by simpa using g1
  rw [fnzaE.k_former_res_sort.arm2 _ _ _ _ _ _ _ _ _ _ _ _ g1']
  simp only [decOS, g1', ↓reduceIte]
  rw [hty]
  refine RefE.bind_callW (s₀ := ⟨m1, Locals.init []⟩) (fun _ => fnzaE.k_inst_lp.none ..)
    (hp.ilp n ⟨m1, Locals.init []⟩ a dn vis fe M eb _ _ us _ cvT.levelParams hS hty32 hus hl)
    fun r3 m3 _ h3 => RefE.after_core (w := id) h3 fun M3 hS3 _ => ?_
  rw [fnzaE.k_inst_lp.arm1]
  have hf := fsl_ref p hp.toFslProg n F hk hnF hn62 dn vis fe eb mode hm4 hebm n (by omega) m3 _ M3 0
    (erRd m1 (q + 17) + erRd m1 (q + 11)) (r3.headD 0) hS3 h3.resOk
  simp only [L.Ind.erRd_foldN] at hn' hni hnp; rw [hn', ← hni, ← hnp, show ((0 : Word)).toNat = 0 from rfl] at hf
  refine RefE.bind_coreE (w := id) (fun _ => fnzaE.k_former_sort_loop.none ..) id hf
    fun r4 m4 _ h4 M4 hS4 _ => ?_
  by_cases g4 : r4.headD 0 = 0
  · rw [fnzaE.k_former_sort_loop.arm1 _ _ _ _ g4]
    simp only [decOS, g4, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS4 rfl (by unfold ResH HW; decide))
  rw [fnzaE.k_former_sort_loop.arm2 _ _ _ _ g4]
  simp only [decOS, g4, ↓reduceIte]
  have hu : HW (r4.tail.headD 0) := h4.resOk g4
  have hrun4 := AM.run_of_ok _ _ h4.run
  rw [h4.res] at hrun4
  rw [show decOS r4 = some (decI (r4.tail.headD 0)) by simp only [decOS, g4, ↓reduceIte]] at hrun4
  obtain ⟨hh, hvw⟩ := fsl_sortView _ _ _ _ _ _ _ hrun4
  obtain ⟨l, hdl⟩ := hS4.den.sort _ _ hvw
  obtain ⟨X, hX, hXok⟩ := readLevelM_run' _ _ l hdl hS4.readL
  refine RefE.bind_right hX ?_
  have hS5 := hS4.withReadLC X hXok
  rcases c5 : callW p n "lv_never" [r4.tail.headD 0] m4 with _ | ⟨r5, m5⟩
  · rw [liftE_none, fnzaE.k_former_never_zero.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, fnzaE.k_former_never_zero.arm1]
  obtain ⟨s5, hs5, -, hW5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
    (lvNeverW_spec p hp.lvn n ⟨m4, Locals.init []⟩ _) c5
  rw [hs5] at hW5
  obtain ⟨hw5, hS6, hK6⟩ := lvNever_core (hp.prop.get "lv_node") (hp.prop.get "lh_push")
    (hp.prop.get "lv_zero") hS5 hu hdl hW5
  refine RefE.ret rfl ⟨⟨M4, hS6, KeptAll.refl _ _, hK6⟩, ?_, ?_⟩
  · show _ = decBool [r5.headD 0]
    rw [hw5]; cases (ConLeche.Level.zeronessOf l).isNever <;> rfl
  · show HW (r5.headD 0)
    rw [hw5]; split <;> (unfold HW; decide)

end fnza

end L.Arena
