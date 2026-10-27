import ConAgua.Arena.IndSumSpec.ColW
import ConAgua.Arena.IndSumSpec.StructProjArgP

/-!
# Row: `ConRon.Arena.paramLevels.go`, `ConRon.Arena.structProjGuards.col`, `ConRon.Arena.structProjGuards.row`

The refinement theorems `paramLevelsGo_refines`, `structProjGuardsCol_refines`, `structProjGuardsRow_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section arms
variable (k : Nat) (m m1 m2 m3 : Mem) (o l u q : Word) (r : List Word)
theorem plK2_some : plK2 k u (some (r, m2)) = plK3 (consW k m2 u (r.headD 0) (r.tail.headD 0)) := rfl
theorem plK3_some : plK3 (some (r, m3)) = some ([r.headD 0, r.tail.headD 0], m3) := rfl
end arms

grind_pattern [ind_grind] plK2_some => plK2 k u (some (r, m2))
grind_pattern [ind_grind] plK3_some => plK3 (some (r, m3))

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hg : p.lookup "sl_get" = some slGet)
  (hpf : p.lookup "param_find" = some paramFind) (hpp : p.lookup "param_push" = some paramPush)
  (hip : p.lookup "intern_param" = some internParam)
  (hp : p.lookup "param_levels_go" = some paramLevelsGoL)
include ha hc hsc hg hpf hpp hip hp

theorem plgW_spec (k : Nat) : ∀ (s₀ : St) (o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "param_levels_go" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ plgW k s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ o l; rw [invoke_eq _ hp]; simp only [callFn, paramLevelsGoL]
    vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ o l
    rw [invoke_eq _ hp]
    simp only [callFn, paramLevelsGoL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        iwAlloc_specW p ha k, slGet_specW p hg k, internParam_spec p hpf hpp hip k,
        slCons_specW p ha hc hsc k, ih] <;>
      finish (gen := 20) [getW]

end spec

theorem plgW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (o l : Word) (lps : List NIdx) (r : List Word),
    plgW k m o l = some (r, m') → StageR dn vis fe m a → decHL m o.toNat l.toNat = some lps →
    o.toNat + l.toNat < 2 ^ 64 → o.toNat + l.toNat ≤ iwTop m →
    ∃ us a', (paramLevels.go lps).run a = .ok (us, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some us ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  induction k with
  | zero => intro m m' a o l lps r h; simp [plgW] at h
  | succ k ih =>
    intro m m' a o l lps r h hS hd hb ht
    by_cases hl : l = 0
    · subst hl
      rw [plgW_nil k m o 0 rfl] at h
      obtain ⟨q, m1, h0, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [plK0_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS1, hg1, hq, htop⟩ := allocW_stage h0 hS
      have : lps = [] := by simpa [decHL, hslice?] using hd.symm
      subst this
      exact ⟨[], a, rfl, hS1, hg1, by simp [decHL, hslice?], by simp [htop, hq]⟩
    · obtain ⟨w, lps', rfl, hw, hw32, hd'⟩ := decHL_cons hd hl hb
      obtain ⟨hsum, -⟩ := toNat_succ_of_lt hb hl
      rw [plgW_cons k m o l hl, hw] at h
      obtain ⟨u, m1, h1, h⟩ := kSome_inv h (by simp [plK1]) (fun _ _ => rfl)
      by_cases hu : 4294967296 ≤ u
      · rw [plK1_big k m1 o l u hu] at h; cases h
      rw [plK1_ok k m1 o l u hu] at h
      have hu32 : u.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ u.toNat := hu; omega
      obtain ⟨a1, hrun1, hS1, hg1⟩ := internParam_stage hS w hw32 h1
      obtain ⟨r2, m2, h2, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [plK2_some] at h
      obtain ⟨us, a2, hrun2, hS2, hg2, hd2, ht2⟩ := ih m1 m2 a1 (o + 1) (l - 1) lps' r2 h2 hS1
        (by rw [decHL_grow hg1 (by omega)]; exact hd') (by omega) (by have := hg1.1; omega)
      obtain ⟨r3, m3, h3, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [plK3_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage h3 hS2 (Nat.le_of_eq ht2) hu32 hd2
      refine ⟨decI u :: us, a2, ?_, hS3, (hg1.trans hg2).trans hg3, by simpa using hd3, by simpa using ht3⟩
      simp only [paramLevels.go, StateT.run_bind, hrun1]
      simp only [bind, Except.bind, hrun2]
      rfl

section census
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hg : p.lookup "sl_get" = some slGet)
  (hpf : p.lookup "param_find" = some paramFind) (hpp : p.lookup "param_push" = some paramPush)
  (hip : p.lookup "intern_param" = some internParam)
  (hp : p.lookup "param_levels_go" = some paramLevelsGoL)
include ha hc hsc hg hpf hpp hip hp

/-- **`param_levels_go` refines `paramLevels.go`** under the stage relation. -/
@[refines ConRon.Arena.paramLevels.go]
theorem paramLevelsGo_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (o l : Word) (lps : List NIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (hd : decHL s₀.mem o.toNat l.toNat = some lps) (hb : o.toNat + l.toNat < 2 ^ 64)
    (ht : o.toNat + l.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "param_levels_go" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (paramLevels.go lps) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (paramLevels.go lps) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat = some (AM.res (paramLevels.go lps) a₀) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop s'.mem; ⊤⦄ := by
  refine triple_post (plgW_spec p ha hc hsc hg hpf hpp hip hp k s₀ o l) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨us, a', hrun, hS', hg', hd', ht'⟩ := plgW_ok dn vis fe k _ _ _ _ _ _ _ hm hS hd hb ht
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg', by rw [hres]; exact hd', ht'⟩

theorem plW_spec (hq : p.lookup "param_levels" = some paramLevelsL) (hil : IlF p) (k : Nat) (s₀ : St) (o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "param_levels" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ plW k s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq]
  simp only [callFn, paramLevelsL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        plgW_spec p ha hc hsc hg hpf hpp hip hp k, ilF_spec p hil k] <;>
      finish

end census

end L.Ind

namespace L.Ind

open L.Arena

section arms
variable (n : Nat) (m m1 m2 : Mem) (uo ul so sl z j k acc mx : Word) (r : List Word)
theorem colW_nil (hk : k = 0) : colW (n + 1) m uo ul so sl z j k acc = some ([acc], m) := by
  simp [colW, hk]
theorem colW_used (hk : k ≠ 0) (hu : getDW m uo ul j 0 ≠ 0) :
    colW (n + 1) m uo ul so sl z j k acc =
      colK n uo ul so sl z j k (minternW m acc (getDW m so sl j z)) := by
  simp [colW, hk, hu]
theorem colW_skip (hk : k ≠ 0) (hu : getDW m uo ul j 0 = 0) :
    colW (n + 1) m uo ul so sl z j k acc = colK2 (colW n m uo ul so sl z (j + 1) (k - 1) acc) := by
  simp [colW, hk, hu]
theorem colK_big (h : 4294967296 ≤ mx) : colK n uo ul so sl z j k (some (mx, m1)) = none := by
  simp [colK, h]
theorem colK_ok (h : ¬ 4294967296 ≤ mx) : colK n uo ul so sl z j k (some (mx, m1)) =
    colK2 (colW n m1 uo ul so sl z (j + 1) (k - 1) mx) := by simp only [colK, ite_eq_right h]
theorem colK2_some : colK2 (some (r, m2)) = some ([r.headD 0], m2) := rfl
end arms

grind_pattern [ind_grind] colW_nil => colW (n + 1) m uo ul so sl z j k acc
grind_pattern [ind_grind] colW_used => colW (n + 1) m uo ul so sl z j k acc
grind_pattern [ind_grind] colW_skip => colW (n + 1) m uo ul so sl z j k acc
grind_pattern [ind_grind] colK_big => colK n uo ul so sl z j k (some (mx, m1))
grind_pattern [ind_grind] colK_ok => colK n uo ul so sl z j k (some (mx, m1))
grind_pattern [ind_grind] colK2_some => colK2 (some (r, m2))

section spec
variable (p : Prog) (hgd : p.lookup "sl_getd" = some slGetD)
  (hmf : p.lookup "max_find" = some maxFind) (hmp : p.lookup "max_push" = some maxPush)
  (him : p.lookup "intern_max" = some internMax)
  (hp : p.lookup "struct_proj_guards_col" = some structProjGuardsColL)
include hgd hmf hmp him hp

theorem colW_spec (n : Nat) : ∀ (s₀ : St) (uo ul so sl z j k acc : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_guards_col" [uo, ul, so, sl, z, j, k, acc]
    ⦃fun r s' => LocEq s' s₀ ∧ colW n s₀.mem uo ul so sl z j k acc = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ uo ul so sl z j k acc; rw [invoke_eq _ hp]; simp only [callFn, structProjGuardsColL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ uo ul so sl z j k acc
    rw [invoke_eq _ hp]
    simp only [callFn, structProjGuardsColL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        slGetD_specW p hgd n, internMax_spec p hmf hmp him n, ih] <;>
      finish (gen := 20)

end spec

/-- A slice of `IW` Booleans (`0` false, any other word true). -/
def decBL (m : Mem) (o l : Nat) : Option (List Bool) := (List.range l).mapM fun j => iwB m (o + j)

theorem decBL_grow {m m' : Mem} (hg : IWGrow m m') {o l : Nat} (h : o + l ≤ iwTop m) :
    decBL m' o l = decBL m o l := by
  simp only [decBL]
  apply mapM_opt_congr
  intro j hj
  have hj' : j < l := List.mem_range.mp hj
  simp only [iwB, bool?, iwA]
  rw [hg.2.2.1 (o + j) (by omega)]

/-- `sl_getd(o, l, j, 0)` of a Boolean slice is the twin's `getD j false`. -/
theorem getDW_bool {m : Mem} {o l : Word} {bs : List Bool} (h : decBL m o.toNat l.toNat = some bs)
    (hb : o.toNat + l.toNat < 2 ^ 64) (j : Word) :
    (getDW m o l j 0 ≠ 0) ↔ bs.getD j.toNat false = true := by
  have hl : bs.length = l.toNat := by simpa using mapM_opt_length _ _ _ h
  unfold getDW
  by_cases hj : l ≤ j
  · have : l.toNat ≤ j.toNat := UInt64.le_iff_toNat_le.mp hj
    simp [hj, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : bs.length ≤ j.toNat)]
  · have hjl : j.toNat < l.toNat := by
      have : ¬ l.toNat ≤ j.toNat := fun h' => hj (UInt64.le_iff_toNat_le.mpr h'); omega
    rw [ite_eq_right hj]
    have hget := mapM_opt_get (fun i => iwB m (o.toNat + i)) (List.range l.toNat) bs h j.toNat
      (by simpa using hjl)
    simp only [List.getElem_range, iwB, bool?, iwA] at hget
    have hoj : (o + j).toNat = o.toNat + j.toNat := by rw [UInt64.toNat_add]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp only [rdW, hoj]
    cases hw : (m.arr64 IW)[o.toNat + j.toNat]? with
    | none => rw [hw] at hget; simp at hget
    | some w =>
      rw [hw] at hget
      simp only [Option.map_some, Option.some.injEq] at hget
      simp [← hget]

/-- `sl_getd(o, l, j, z)` of a handle slice is the twin's `getD j z`. -/
theorem getDW_handle {k : IdxKind} {m : Mem} {o l : Word} {xs : List (Idx k)}
    (h : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat < 2 ^ 64) (j z : Word)
    (hz : H z) :
    (getDW m o l j z).toNat < 2 ^ 32 ∧ decI (getDW m o l j z) = xs.getD j.toNat (decI z) := by
  have hl := decHL_length m h
  unfold getDW
  by_cases hj : l ≤ j
  · have : l.toNat ≤ j.toNat := UInt64.le_iff_toNat_le.mp hj
    simp [hj, hz, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : xs.length ≤ j.toNat)]
  · have hjl : j.toNat < l.toNat := by
      have : ¬ l.toNat ≤ j.toNat := fun h' => hj (UInt64.le_iff_toNat_le.mpr h'); omega
    rw [ite_eq_right hj]
    obtain ⟨w, hw, hw32, hwd⟩ := decHL_get' h j.toNat hjl hb
    have hoj : o + j = UInt64.ofNat (o.toNat + j.toNat) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
    rw [hoj, hw, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact ⟨hw32, by simp [hwd]⟩

theorem colW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (uo ul so sl z j k acc : Word) (r : List Word)
      (used : List Bool) (sorts : List LIdx),
    colW n m uo ul so sl z j k acc = some (r, m') → StageR dn vis fe m a →
    decBL m uo.toNat ul.toNat = some used → decHL m so.toNat sl.toNat = some sorts →
    uo.toNat + ul.toNat < 2 ^ 64 → so.toNat + sl.toNat < 2 ^ 64 →
    uo.toNat + ul.toNat ≤ iwTop m → so.toNat + sl.toNat ≤ iwTop m →
    H z → H acc → j.toNat + k.toNat < 2 ^ 64 →
    ∃ x a', (structProjGuards.col sorts (decI z) used j.toNat k.toNat (decI acc)).run a =
        .ok (x, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ H (r.headD 0) ∧ decI (r.headD 0) = x := by
  induction n with
  | zero => intro m m' a uo ul so sl z j k acc r used sorts h; simp [colW] at h
  | succ n ih =>
    intro m m' a uo ul so sl z j k acc r used sorts h hS hu hs hub hsb hut hst hz hacc hjk
    by_cases hk : k = 0
    · subst hk
      rw [colW_nil n m uo ul so sl z j 0 acc rfl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨decI acc, a, by simp [structProjGuards.col]; rfl, hS, IWGrow.refl m, by simpa using hacc,
        by simp⟩
    have hk1 : 1 ≤ k.toNat := by
      rcases Nat.eq_zero_or_pos k.toNat with h0 | h0
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hk
      · omega
    have hkm : (k - 1).toNat = k.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hk1))]; simp
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hks : k.toNat = (k.toNat - 1) + 1 := by omega
    have hU := getDW_bool hu hub j
    obtain ⟨hsj32, hsj⟩ := getDW_handle hs hsb j z hz
    by_cases hd : getDW m uo ul j 0 ≠ 0
    · rw [colW_used n m uo ul so sl z j k acc hk hd] at h
      obtain ⟨mx, m1, h1, h⟩ := kSome_inv h (by simp [colK]) (fun _ _ => rfl)
      by_cases hmx : 4294967296 ≤ mx
      · rw [colK_big n m1 uo ul so sl z j k mx hmx] at h; cases h
      rw [colK_ok n m1 uo ul so sl z j k mx hmx] at h
      have hmx32 : mx.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ mx.toNat := hmx; omega
      obtain ⟨a1, hrun1, hS1, hg1⟩ := internMax_stage hS acc _ hacc hsj32 h1
      obtain ⟨r2, m2, h2, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [colK2_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨x, a2, hrun2, hS2, hg2, hH, hx⟩ := ih m1 m2 a1 uo ul so sl z (j + 1) (k - 1) mx r2
        used sorts h2 hS1 (by rw [decBL_grow hg1 hut]; exact hu) (by rw [decHL_grow hg1 hst]; exact hs)
        hub hsb (by have := hg1.1; omega) (by have := hg1.1; omega) hz hmx32 (by omega)
      refine ⟨x, a2, ?_, hS2, hg1.trans hg2, by simpa using hH, by simpa using hx⟩
      rw [hks]
      simp only [structProjGuards.col, hU.mp hd, ite_true]
      rw [StateT.run_bind, ← hsj, hrun1]
      simp only [bind, Except.bind]
      rw [hj1, hkm] at hrun2
      exact hrun2
    · have hd' : getDW m uo ul j 0 = 0 := by simpa using hd
      rw [colW_skip n m uo ul so sl z j k acc hk hd'] at h
      obtain ⟨r2, m2, h2, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [colK2_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨x, a2, hrun2, hS2, hg2, hH, hx⟩ := ih m m2 a uo ul so sl z (j + 1) (k - 1) acc r2
        used sorts h2 hS hu hs hub hsb hut hst hz hacc (by omega)
      refine ⟨x, a2, ?_, hS2, hg2, by simpa using hH, by simpa using hx⟩
      have hf : used.getD j.toNat false = false := by
        cases e : used.getD j.toNat false
        · rfl
        · exact absurd (hU.mpr e) hd
      rw [hks]
      simp only [structProjGuards.col, hf]
      rw [hj1, hkm] at hrun2
      exact hrun2

/-- **`struct_proj_guards_col` refines `structProjGuards.col`** under the stage relation. -/
@[refines ConRon.Arena.structProjGuards.col]
theorem structProjGuardsCol_refines (p : Prog) (hgd : p.lookup "sl_getd" = some slGetD)
    (hmf : p.lookup "max_find" = some maxFind) (hmp : p.lookup "max_push" = some maxPush)
    (him : p.lookup "intern_max" = some internMax)
    (hp : p.lookup "struct_proj_guards_col" = some structProjGuardsColL) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (uo ul so sl z j k acc : Word) (used : List Bool) (sorts : List LIdx)
    (hS : StageR dn vis fe s₀.mem a₀) (hu : decBL s₀.mem uo.toNat ul.toNat = some used)
    (hs : decHL s₀.mem so.toNat sl.toNat = some sorts)
    (hub : uo.toNat + ul.toNat < 2 ^ 64) (hsb : so.toNat + sl.toNat < 2 ^ 64)
    (hut : uo.toNat + ul.toNat ≤ iwTop s₀.mem) (hst : so.toNat + sl.toNat ≤ iwTop s₀.mem)
    (hz : H z) (hacc : H acc) (hjk : j.toNat + k.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_guards_col" [uo, ul, so, sl, z, j, k, acc]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (structProjGuards.col sorts (decI z) used j.toNat k.toNat (decI acc)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (structProjGuards.col sorts (decI z) used j.toNat k.toNat (decI acc)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ H (r.headD 0) ∧
      decI (r.headD 0) = AM.res (structProjGuards.col sorts (decI z) used j.toNat k.toNat (decI acc)) a₀; ⊤⦄ := by
  refine triple_post (colW_spec p hgd hmf hmp him hp n s₀ uo ul so sl z j k acc) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hH, hx⟩ :=
    colW_ok dn vis fe n _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm hS hu hs hub hsb hut hst hz hacc hjk
  obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst']; exact hS', hg, hH, by rw [hres]; exact hx⟩

section arms
variable (n : Nat) (m m1 m2 : Mem) (uo ul so sl z i k g : Word) (rg rr : List Word)
theorem rowW_nil (hk : k = 0) : rowW (n + 1) m uo ul so sl z i k = plK0 (allocW m 0) := by
  simp [rowW, hk]
theorem rowW_cons (hk : k ≠ 0) : rowW (n + 1) m uo ul so sl z i k =
    rowK1 n uo ul so sl z i k (colW n m uo ul so sl z 0 i (getDW m so sl i z)) := by
  simp [rowW, hk]
theorem rowK1_some : rowK1 n uo ul so sl z i k (some (rg, m1)) =
    rowK2 n (rg.headD 0) (rowW n m1 uo ul so sl z (i + 1) (k - 1)) := by rw [rowK1]
theorem rowK2_some : rowK2 n g (some (rr, m2)) = plK3 (consW n m2 g (rr.headD 0) (rr.tail.headD 0)) := rfl
end arms

grind_pattern [ind_grind] rowW_nil => rowW (n + 1) m uo ul so sl z i k
grind_pattern [ind_grind] rowW_cons => rowW (n + 1) m uo ul so sl z i k
grind_pattern [ind_grind] rowK1_some => rowK1 n uo ul so sl z i k (some (rg, m1))
grind_pattern [ind_grind] rowK2_some => rowK2 n g (some (rr, m2))

section spec
variable (p : Prog) (hgd : p.lookup "sl_getd" = some slGetD)
  (hmf : p.lookup "max_find" = some maxFind) (hmp : p.lookup "max_push" = some maxPush)
  (him : p.lookup "intern_max" = some internMax)
  (hcol : p.lookup "struct_proj_guards_col" = some structProjGuardsColL)
  (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hp : p.lookup "struct_proj_guards_row" = some structProjGuardsRowL)
include hgd hmf hmp him hcol ha hc hsc hp

theorem rowW_spec (n : Nat) : ∀ (s₀ : St) (uo ul so sl z i k : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_guards_row" [uo, ul, so, sl, z, i, k]
    ⦃fun r s' => LocEq s' s₀ ∧ rowW n s₀.mem uo ul so sl z i k = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ uo ul so sl z i k; rw [invoke_eq _ hp]; simp only [callFn, structProjGuardsRowL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ uo ul so sl z i k
    rw [invoke_eq _ hp]
    simp only [callFn, structProjGuardsRowL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        iwAlloc_specW p ha n, slGetD_specW p hgd n, colW_spec p hgd hmf hmp him hcol n,
        slCons_specW p ha hc hsc n, ih] <;>
      finish (gen := 20)

end spec

theorem rowW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (uo ul so sl z i k : Word) (r : List Word)
      (used : List Bool) (sorts : List LIdx),
    rowW n m uo ul so sl z i k = some (r, m') → StageR dn vis fe m a →
    decBL m uo.toNat ul.toNat = some used → decHL m so.toNat sl.toNat = some sorts →
    uo.toNat + ul.toNat < 2 ^ 64 → so.toNat + sl.toNat < 2 ^ 64 →
    uo.toNat + ul.toNat ≤ iwTop m → so.toNat + sl.toNat ≤ iwTop m →
    H z → i.toNat + k.toNat < 2 ^ 64 →
    ∃ gs a', (structProjGuards.row sorts (decI z) used i.toNat k.toNat).run a = .ok (gs, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some gs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  induction n with
  | zero => intro m m' a uo ul so sl z i k r used sorts h; simp [rowW] at h
  | succ n ih =>
    intro m m' a uo ul so sl z i k r used sorts h hS hu hs hub hsb hut hst hz hik
    by_cases hk : k = 0
    · subst hk
      rw [rowW_nil n m uo ul so sl z i 0 rfl] at h
      obtain ⟨q, m1, h0, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [plK0_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS1, hg1, hq, htop⟩ := allocW_stage h0 hS
      exact ⟨[], a, by simp [structProjGuards.row]; rfl, hS1, hg1, by simp [decHL, hslice?],
        by simp [htop, hq]⟩
    have hk1 : 1 ≤ k.toNat := by
      rcases Nat.eq_zero_or_pos k.toNat with h0 | h0
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hk
      · omega
    have hkm : (k - 1).toNat = k.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hk1))]; simp
    have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hks : k.toNat = (k.toNat - 1) + 1 := by omega
    obtain ⟨hsi32, hsi⟩ := getDW_handle hs hsb i z hz
    rw [rowW_cons n m uo ul so sl z i k hk] at h
    obtain ⟨rg, m1, h1, h⟩ := kSome_inv h (by simp [rowK1]) (fun _ _ => rfl)
    rw [rowK1_some] at h
    obtain ⟨g, a1, hrun1, hS1, hg1, hH1, hg⟩ := colW_ok dn vis fe n m m1 a uo ul so sl z 0 i _ rg
      used sorts h1 hS hu hs hub hsb hut hst hz hsi32 (by simp; omega)
    obtain ⟨rr, m2, h2, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
    rw [rowK2_some] at h
    obtain ⟨gs, a2, hrun2, hS2, hg2, hd2, ht2⟩ := ih m1 m2 a1 uo ul so sl z (i + 1) (k - 1) rr
      used sorts h2 hS1 (by rw [decBL_grow hg1 hut]; exact hu) (by rw [decHL_grow hg1 hst]; exact hs)
      hub hsb (by have := hg1.1; omega) (by have := hg1.1; omega) hz (by omega)
    obtain ⟨r3, m3, h3, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
    rw [plK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage h3 hS2 (Nat.le_of_eq ht2) hH1 hd2
    refine ⟨g :: gs, a2, ?_, hS3, (hg1.trans hg2).trans hg3, by rw [← hg]; exact hd3, ht3⟩
    rw [hks]
    simp only [structProjGuards.row, StateT.run_bind]
    rw [hsi, show (0 : Word).toNat = 0 from rfl] at hrun1
    rw [hrun1]
    simp only [bind, Except.bind]
    rw [hi1, hkm] at hrun2
    rw [hrun2]
    rfl

/-- **`struct_proj_guards_row` refines `structProjGuards.row`** under the stage relation. -/
@[refines ConRon.Arena.structProjGuards.row]
theorem structProjGuardsRow_refines (p : Prog) (hgd : p.lookup "sl_getd" = some slGetD)
    (hmf : p.lookup "max_find" = some maxFind) (hmp : p.lookup "max_push" = some maxPush)
    (him : p.lookup "intern_max" = some internMax)
    (hcol : p.lookup "struct_proj_guards_col" = some structProjGuardsColL)
    (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "struct_proj_guards_row" = some structProjGuardsRowL) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (uo ul so sl z i k : Word) (used : List Bool) (sorts : List LIdx)
    (hS : StageR dn vis fe s₀.mem a₀) (hu : decBL s₀.mem uo.toNat ul.toNat = some used)
    (hs : decHL s₀.mem so.toNat sl.toNat = some sorts)
    (hub : uo.toNat + ul.toNat < 2 ^ 64) (hsb : so.toNat + sl.toNat < 2 ^ 64)
    (hut : uo.toNat + ul.toNat ≤ iwTop s₀.mem) (hst : so.toNat + sl.toNat ≤ iwTop s₀.mem)
    (hz : H z) (hik : i.toNat + k.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_guards_row" [uo, ul, so, sl, z, i, k]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (structProjGuards.row sorts (decI z) used i.toNat k.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (structProjGuards.row sorts (decI z) used i.toNat k.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (structProjGuards.row sorts (decI z) used i.toNat k.toNat) a₀) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop s'.mem; ⊤⦄ := by
  refine triple_post (rowW_spec p hgd hmf hmp him hcol ha hc hsc hp n s₀ uo ul so sl z i k) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨gs, a', hrun, hS', hg, hd, ht⟩ :=
    rowW_ok dn vis fe n _ _ _ _ _ _ _ _ _ _ _ _ _ hm hS hu hs hub hsb hut hst hz hik
  obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst']; exact hS', hg, by rw [hres]; exact hd, ht⟩

/-! ## `struct_ps_at` under the stage relation -/

theorem psGoW_stage (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (o nP N k : Word) (r : List Word),
    psGoW n m o nP N k = some (r, m') → StageR dn vis fe m a →
    o.toNat + nP.toNat < 2 ^ 64 → k.toNat + N.toNat ≤ nP.toNat →
    ∃ xs a', (structPsAt.go o.toNat nP.toNat N.toNat k.toNat).run a = .ok (xs, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  induction n with
  | zero => intro m m' a o nP N k r h; simp [psGoW] at h
  | succ n ih =>
    intro m m' a o nP N k r h hS hon hkN
    by_cases hN : N = 0
    · subst hN
      rw [psGoW_nil n m o nP 0 k rfl] at h
      obtain ⟨q, m1, h0, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [psK0_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS1, hg1, hq, htop⟩ := allocW_stage h0 hS
      exact ⟨[], a, by simp [structPsAt.go]; rfl, hS1, hg1, by simp [decHL, hslice?], by simp [htop, hq]⟩
    · rw [psGoW_cons n m o nP N k hN] at h
      obtain ⟨b, m1, hI, h⟩ := kSome_inv h (by simp [psK1]) (fun _ _ => rfl)
      by_cases hb : 4294967296 ≤ b
      · rw [psK1_big n m1 o nP N k b hb] at h; simp at h
      rw [psK1_ok n m1 o nP N k b hb] at h
      have hb32 : b.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ b.toNat := hb; omega
      have hN1 : 1 ≤ N.toNat := by
        have : N.toNat ≠ 0 := fun h0 => hN (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      obtain ⟨a1, hrun1, hS1, hg1⟩ := internBVar_stage hS _ hI
      obtain ⟨r2, m2, hr, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [psK2_some] at h
      have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hN1' : (N - 1).toNat = N.toNat - 1 := by rw [UInt64.toNat_sub]; simp; omega
      obtain ⟨xs, a2, hrun2, hS2, hg2, hd2, ht2⟩ :=
        ih m1 m2 a1 o nP (N - 1) (k + 1) r2 hr hS1 hon (by rw [hk1, hN1']; omega)
      obtain ⟨r3, m3, hcw, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [psK3_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage hcw hS2 (Nat.le_of_eq ht2) hb32 hd2
      refine ⟨decE b :: xs, a2, ?_, hS3, (hg1.trans hg2).trans hg3, by simpa [decE_eq] using hd3,
        by simpa using ht3⟩
      have hu : (o + nP - 1 - k).toNat = o.toNat + nP.toNat - 1 - k.toNat := by
        rw [UInt64.toNat_sub, UInt64.toNat_sub, UInt64.toNat_add]; simp; omega
      have hNs : N.toNat = (N.toNat - 1) + 1 := by omega
      rw [hNs]
      simp only [structPsAt.go]
      rw [StateT.run_bind, ← hu, hrun1]
      simp only [bind, Except.bind]
      rw [← hk1, ← hN1']
      simp only [StateT.run] at hrun2
      simp only [StateT.bind, StateT.run, hrun2]
      rfl

theorem psAtW_stage (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat)
    (m m' : Mem) (a : AState) (o nP : Word) (r : List Word)
    (h : psAtW n m o nP = some (r, m')) (hS : StageR dn vis fe m a) (hon : o.toNat + nP.toNat < 2 ^ 64) :
    ∃ xs a', (structPsAt o.toNat nP.toNat).run a = .ok (xs, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  cases n with
  | zero => cases h
  | succ n =>
    rw [psAtW_succ] at h
    obtain ⟨r0, m0, hg, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
    rw [psK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨xs, a', hrun, hS', hgr, hd, ht⟩ := psGoW_stage dn vis fe n m m0 a o nP nP 0 r0 hg hS hon (by simp)
    exact ⟨xs, a', by simpa [structPsAt] using hrun, hS', hgr, by simpa using hd, by simpa using ht⟩

end L.Ind

end
