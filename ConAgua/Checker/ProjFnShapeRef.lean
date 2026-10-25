import ConAgua.Checker.Entry
import ConAgua.Front.IndApplyRefine
import ConAgua.Arena.DeclCanonLvl
import ConAgua.Census.Attr
import ConAgua.Arena.IndRealIpf

/-!
# `is_proj_fn_shape` against the twin

The word model `pfsW` of `is_proj_fn_shape` (`isProjFnShapeL`), its spec (from
`L.Ind.isProjFnShape_specW`, `IndRealIpf.lean`, through `pfsW = ipfW`; a `vcgen` of its own over
`evalC` took ~5 min and 790 paths), and the
refinement of `NIdx.isProjFnShape`: two `viewN`s (a `num` node, then its `str` prefix) and the
prefix's string compared to `"proj"` / `"projTable"` as a `POOL` slice. The L code aborts exactly
where a twin `viewN` fails (a handle past its tier's count, or in the scratch tier while it is off).
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

open Std.WP
open scoped Lean.Order
open L L.Arena
open ConRon.Arena

namespace L.Checker

/-! ## The model -/

/-- `is_proj_fn_shape`'s string test, at the `str` node's first word `k`. -/
def pfsStr (m : Mem) (t i : Word) : Option Word :=
  if tfld m NSTR t i 2 ≠ 4 ∧ tfld m NSTR t i 2 ≠ 9 then some 0
  else if ¬ (prd m (tfld m NSTR t i 1) = 112 ∧
      prd m (tfld m NSTR t i 1 + 1) = 114 ∧
      prd m (tfld m NSTR t i 1 + 2) = 111 ∧
      prd m (tfld m NSTR t i 1 + 3) = 106) then some 0
  else if tfld m NSTR t i 2 = 4 then some 1
  else if ¬ (prd m (tfld m NSTR t i 1 + 4) = 84 ∧
      prd m (tfld m NSTR t i 1 + 5) = 97 ∧
      prd m (tfld m NSTR t i 1 + 6) = 98 ∧
      prd m (tfld m NSTR t i 1 + 7) = 108 ∧
      prd m (tfld m NSTR t i 1 + 8) = 101) then some 0
  else some 1

/-- `is_proj_fn_shape`'s prefix step: the `num` node's prefix word `q`. -/
def pfsPre (m : Mem) (q : Word) : Option Word :=
  if 4294967295 < q then none
  else if q >>> 28 ≠ 1 then some 0
  else if tierW q ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m NSTR (tierW q) ≤ idxW q then none
  else pfsStr m (tierW q) (idxW q)

/-- **The model of `is_proj_fn_shape(n)`.** -/
def pfsW (m : Mem) (n : Word) : Option Word :=
  if 4294967295 < n then none
  else if n >>> 28 ≠ 2 then some 0
  else if tierW n ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m NNUM (tierW n) ≤ idxW n then none
  else pfsPre m (tfld m NNUM (tierW n) (idxW n) 0)

/-! ## The spec -/

theorem pfsStr_eq (m : Mem) (t i : Word) :
    pfsStr m t i = some (L.Ind.ipfStrW m (tfld m NSTR t i 1) (tfld m NSTR t i 2)) := by
  unfold pfsStr L.Ind.ipfStrW
  simp only [Classical.not_and_iff_not_or_not, Classical.not_not]
  repeat' split
  all_goals first | rfl | simp_all

/-- The model is `IndRealIpf.lean`'s word body `ipfW`. -/
theorem pfsW_eq (m : Mem) (n : Word) : pfsW m n = L.Ind.ipfW m n := by
  simp only [pfsW, pfsPre, pfsStr_eq, L.Ind.ipfW, L.Ind.ipfS, nnQ, nsO, nsL]

/-- The spec, from `L.Ind.isProjFnShape_specW` (`vcgen` with `L.evalC_spec`). -/
theorem pfs_spec (p : Prog) (hp : p.lookup "is_proj_fn_shape" = some isProjFnShapeL) (n : Nat)
    (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "is_proj_fn_shape" [h]
    ⦃fun r s' => s' = s₀ ∧ pfsW s₀.mem h = some (r.headD 0); ⊤⦄ := by
  cases n with
  | zero =>
    rw [invoke_eq _ hp]
    simp only [callFn, isProjFnShapeL]
    vcgen [exec] <;> grind
  | succ n =>
    refine triple_post (L.Ind.isProjFnShape_specW p hp n s₀ h) ?_
    rintro r ⟨mem, loc⟩ ⟨hl, hm, hw⟩
    obtain ⟨mem₀, loc₀⟩ := s₀
    simp only [LocEq] at hl
    simp only at hm hw
    subst hl hm
    exact ⟨rfl, by rw [pfsW_eq]; exact hw⟩

/-! ## Against the twin -/

theorem strWords_proj : strWords "proj" = [112, 114, 111, 106] := by decide
theorem strWords_projTable :
    strWords "projTable" = [112, 114, 111, 106, 84, 97, 98, 108, 101] := by decide

theorem str_eq_iff (s t : String) : s = t ↔ strWords s = strWords t :=
  ⟨fun h => h ▸ rfl, strWords_inj s t⟩

theorem ite10_false {b : Bool} (h : ¬ b = true) : (if b = true then (1 : Word) else 0) = 0 := by
  simp [h]
theorem ite10_true {b : Bool} (h : b = true) : (if b = true then (1 : Word) else 0) = 1 := by
  simp [h]

/-- **The string test**: on a `str` node's offset and length words holding `s`. -/
theorem pfsStr_ok (m : Mem) (t i : Word) (s : String) (r : Word)
    (hol : (tfld m NSTR t i 1).toNat + (tfld m NSTR t i 2).toNat ≤ m.top.toNat)
    (ht : m.top.toNat < 2 ^ 41)
    (hsl : sliceL (vpool m) (tfld m NSTR t i 1).toNat
      (tfld m NSTR t i 2).toNat = strWords s)
    (h : pfsStr m t i = some r) :
    r = if (s == "proj" || s == "projTable") then 1 else 0 := by
  unfold pfsStr at h
  generalize tfld m NSTR t i 1 = o at hol hsl h
  generalize tfld m NSTR t i 2 = lw at hol hsl h
  have hlen := sliceL_length (vpool m) o.toNat lw.toNat
  rw [hsl] at hlen
  have hp4 : (strWords "proj").length = 4 := by rw [strWords_proj]; rfl
  have hp9 : (strWords "projTable").length = 9 := by rw [strWords_projTable]; rfl
  by_cases h4 : lw = 4
  · subst h4
    have hl : (4 : Word).toNat = 4 := rfl
    rw [hl] at hlen hsl
    have hT : s ≠ "projTable" := fun he => by subst he; omega
    have v0 : (vpool m)[o.toNat]?.getD 0 = prd m o := vpool_getD m o (by omega)
    have v1 : (vpool m)[o.toNat + 1]?.getD 0 = prd m (o + 1) := by
      have e : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      rw [← e]; exact vpool_getD m _ (by omega)
    have v2 : (vpool m)[o.toNat + 2]?.getD 0 = prd m (o + 2) := by
      have e : (o + 2).toNat = o.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
      rw [← e]; exact vpool_getD m _ (by omega)
    have v3 : (vpool m)[o.toNat + 3]?.getD 0 = prd m (o + 3) := by
      have e : (o + 3).toNat = o.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
      rw [← e]; exact vpool_getD m _ (by omega)
    simp [sliceL, List.ofFn_succ, v0, v1, v2, v3] at hsl
    have hb : (s == "proj" || s == "projTable") = true ↔
        (prd m o = 112 ∧ prd m (o + 1) = 114 ∧
          prd m (o + 2) = 111 ∧ prd m (o + 3) = 106) := by
      simp [hT, str_eq_iff, ← hsl, strWords_proj]
    simp (config := { decide := true }) only [UInt64.reduceToNat, ne_eq, not_true_eq_false,
      not_false_eq_true, false_and, and_false, and_true, true_and, ite_true, ite_false,
      eq_self_iff_true] at h
    split at h
    · rename_i hc; cases h; exact (ite10_false fun hh => hc (hb.mp hh)).symm
    · rename_i hc; cases h; exact (ite10_true (hb.mpr (Classical.not_not.mp hc))).symm
  by_cases h9 : lw = 9
  · subst h9
    have hl : (9 : Word).toNat = 9 := rfl
    rw [hl] at hlen hsl
    have hP : s ≠ "proj" := fun he => by subst he; omega
    have v0 : (vpool m)[o.toNat]?.getD 0 = prd m o := vpool_getD m o (by omega)
    have v1 : (vpool m)[o.toNat + 1]?.getD 0 = prd m (o + 1) := by
      have e : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      rw [← e]; exact vpool_getD m _ (by omega)
    have v2 : (vpool m)[o.toNat + 2]?.getD 0 = prd m (o + 2) := by
      have e : (o + 2).toNat = o.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
      rw [← e]; exact vpool_getD m _ (by omega)
    have v3 : (vpool m)[o.toNat + 3]?.getD 0 = prd m (o + 3) := by
      have e : (o + 3).toNat = o.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
      rw [← e]; exact vpool_getD m _ (by omega)
    have v4 : (vpool m)[o.toNat + 4]?.getD 0 = prd m (o + 4) := by
      have e : (o + 4).toNat = o.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
      rw [← e]; exact vpool_getD m _ (by omega)
    have v5 : (vpool m)[o.toNat + 5]?.getD 0 = prd m (o + 5) := by
      have e : (o + 5).toNat = o.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
      rw [← e]; exact vpool_getD m _ (by omega)
    have v6 : (vpool m)[o.toNat + 6]?.getD 0 = prd m (o + 6) := by
      have e : (o + 6).toNat = o.toNat + 6 := by rw [UInt64.toNat_add]; simp; omega
      rw [← e]; exact vpool_getD m _ (by omega)
    have v7 : (vpool m)[o.toNat + 7]?.getD 0 = prd m (o + 7) := by
      have e : (o + 7).toNat = o.toNat + 7 := by rw [UInt64.toNat_add]; simp; omega
      rw [← e]; exact vpool_getD m _ (by omega)
    have v8 : (vpool m)[o.toNat + 8]?.getD 0 = prd m (o + 8) := by
      have e : (o + 8).toNat = o.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
      rw [← e]; exact vpool_getD m _ (by omega)
    simp [sliceL, List.ofFn_succ, v0, v1, v2, v3, v4, v5, v6, v7, v8] at hsl
    have hb : (s == "proj" || s == "projTable") = true ↔
        (prd m o = 112 ∧ prd m (o + 1) = 114 ∧
          prd m (o + 2) = 111 ∧ prd m (o + 3) = 106 ∧
          prd m (o + 4) = 84 ∧ prd m (o + 5) = 97 ∧
          prd m (o + 6) = 98 ∧ prd m (o + 7) = 108 ∧
          prd m (o + 8) = 101) := by
      simp [hP, str_eq_iff, ← hsl, strWords_projTable]
    simp (config := { decide := true }) only [UInt64.reduceToNat, ne_eq, not_true_eq_false,
      not_false_eq_true, false_and, and_false, and_true, true_and, ite_true, ite_false,
      eq_self_iff_true] at h
    split at h
    · rename_i hc; cases h; exact (ite10_false fun hh => hc ((hb.mp hh).elim fun a b => ⟨a, b.1, b.2.1, b.2.2.1⟩)).symm
    rename_i hc
    split at h
    · rename_i hc'; cases h
      exact (ite10_false fun hh => hc' ((hb.mp hh).elim fun _ b => b.2.2.2)).symm
    · rename_i hc'; cases h
      have c1 := Classical.not_not.mp hc
      have c2 := Classical.not_not.mp hc'
      exact (ite10_true (hb.mpr ⟨c1.1, c1.2.1, c1.2.2.1, c1.2.2.2, c2⟩)).symm
  · simp only [ne_eq, h4, h9, not_false_eq_true, and_self, ite_true, Option.some.injEq] at h
    subst h
    have hP : s ≠ "proj" := fun he => by
      subst he; exact h4 (UInt64.toNat_inj.mp (by simp; omega))
    have hT : s ≠ "projTable" := fun he => by
      subst he; exact h9 (UInt64.toNat_inj.mp (by simp; omega))
    simp [hP, hT]

theorem tag_eq_iff (w : Word) (hw : w.toNat < 2 ^ 32) (c : UInt32) (hc : c.toNat < 16) :
    (decI w : NIdx).tag = c ↔ w >>> 28 = c.toUInt64 := by
  rw [L.Front.Ind.decN_tag w hw]
  have h16 := L.Front.Ind.shr28_lt w hw
  constructor
  · intro e
    apply UInt64.toNat_inj.mp
    have := congrArg UInt32.toNat e
    simp only [UInt64.toNat_toUInt32] at this
    simp only [UInt32.toNat_toUInt64]
    omega
  · intro e
    rw [e]
    apply UInt32.toNat_inj.mp
    simp [UInt64.toNat_toUInt32]

/-- **`is_proj_fn_shape`'s model against the twin**: where the model returns, the twin's run
succeeds, keeps the state, and returns the model's word as a `Bool`. -/
theorem pfsW_ok {m : Mem} {a : AState} (hR : ArenaR m a) (w r : Word) (h : pfsW m w = some r) :
    ∃ b, (NIdx.isProjFnShape (decI w)).run a = .ok (b, a) ∧ r = if b = true then 1 else 0 := by
  unfold pfsW at h
  split at h
  · cases h
  rename_i hb
  have hw : w.toNat < 2 ^ 32 := by
    have : ¬ (4294967295 : Nat) < w.toNat := hb
    omega
  split at h
  · rename_i hg
    cases h
    refine ⟨false, ?_, rfl⟩
    have : ((decI w : NIdx).tag == NTag.num) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, NTag.num]
      rw [tag_eq_iff w hw 2 (by decide)]
      exact hg
    simp only [NIdx.isProjFnShape, this]
    rfl
  rename_i hg0
  have hg : w >>> 28 = 2 := by simpa using hg0
  split at h
  · cases h
  rename_i hs
  have hv := L.Front.Ind.nview_tier hR w hw hs
  have ht1 : tierW w ≤ 1 := tierW_le w
  split at h
  · cases h
  rename_i hc
  obtain ⟨x, hx, hq, -⟩ := ConsR.node hR.nnum (tierW w) ht1 (idxW w)
    (UInt64.not_le.mp hc)
  have hview : (viewN (decI w)).run a = .ok (.num x.pre x.n, a) := by
    apply L.Front.Ind.viewN_run
    rw [EStore.ns, hv, NTables.get, L.Front.Ind.decN_tag w hw, hg]
    simp only [NTag.anonymous, NTag.str, NTag.num, L.Front.Ind.decN_idx, Tbl.node?]
    by_cases ht : tierW w = 0
    · simp only [ht, ↓reduceIte] at hx; simp [ht, hx]
    · simp only [ht, ↓reduceIte] at hx; simp [ht, hx]
  have htagT : ((decI w : NIdx).tag == NTag.num) = true := by
    simp only [beq_iff_eq, NTag.num]
    rw [tag_eq_iff w hw 2 (by decide)]
    exact hg
  rw [hq] at h
  generalize hqw : x.pre.word.toUInt64 = q at h
  have hq32 : q.toNat < 2 ^ 32 := hqw ▸ word_lt x.pre
  have hpre : x.pre = decI q := by rw [← hqw, decI_word]
  unfold pfsPre at h
  have hq' : ¬ (4294967295 < q) := fun hh => by
    have := UInt64.lt_iff_toNat_lt.mp hh
    simp only [UInt64.reduceToNat] at this
    omega
  simp only [hq', ↓reduceIte] at h
  simp only [NIdx.isProjFnShape, htagT, ite_true]
  rw [L.Front.Ind.run_bind _ _ a _ hview]
  simp only [hpre]
  split at h
  · rename_i hg
    cases h
    refine ⟨false, ?_, rfl⟩
    have : ((decI q : NIdx).tag == NTag.str) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, NTag.str]
      rw [tag_eq_iff q hq32 1 (by decide)]
      exact hg
    simp only [this]
    rfl
  rename_i hg0
  have hg' : q >>> 28 = 1 := by simpa using hg0
  have htagS : ((decI q : NIdx).tag == NTag.str) = true := by
    simp only [beq_iff_eq, NTag.str]
    rw [tag_eq_iff q hq32 1 (by decide)]
    exact hg'
  split at h
  · cases h
  rename_i hs'
  have hv' := L.Front.Ind.nview_tier hR q hq32 hs'
  have ht1' : tierW q ≤ 1 := tierW_le q
  split at h
  · cases h
  rename_i hc'
  obtain ⟨y, hy, hrel⟩ := ConsR.node hR.nstr (tierW q) ht1' (idxW q)
    (UInt64.not_le.mp hc')
  have hview' : (viewN (decI q)).run a = .ok (.str y.pre y.s, a) := by
    apply L.Front.Ind.viewN_run
    rw [EStore.ns, hv', NTables.get, L.Front.Ind.decN_tag q hq32, hg']
    simp only [NTag.anonymous, NTag.str, L.Front.Ind.decN_idx, Tbl.node?]
    by_cases ht : tierW q = 0
    · simp only [ht, ↓reduceIte] at hy; simp [ht, hy]
    · simp only [ht, ↓reduceIte] at hy; simp [ht, hy]
  obtain ⟨-, hol, hsl, -⟩ := hrel
  refine ⟨y.s == "proj" || y.s == "projTable", ?_, pfsStr_ok m _ _ y.s r hol.le hR.lit.1.top41 hsl h⟩
  simp only [htagS, ite_true]
  rw [L.Front.Ind.run_bind _ _ a _ hview']
  rfl

/-! ## The refinement -/

set_option linter.unusedVariables false in
/-- **`is_proj_fn_shape` refines `NIdx.isProjFnShape`.** -/
@[refines ConRon.Arena.NIdx.isProjFnShape]
theorem isProjFnShape_refines (p : Prog)
    (hp : p.lookup "is_proj_fn_shape" = some L.Checker.isProjFnShapeL)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Word) (hn : n.toNat < 2 ^ 32) :
    L.Ind.RefAM p "is_proj_fn_shape" [n] (L.Ind.StageR dn vis fe)
      (NIdx.isProjFnShape (decI n)) (L.Ind.KeepPost dn vis fe L.Ind.decW0B) := by
  refine L.Ind.refAM_same p _ _ _ _ dn vis fe _ (fun _ _ h => h) ?_
  intro k s₀ a₀ hS
  refine triple_post (pfs_spec p hp k s₀ n) ?_
  rintro r s' ⟨rfl, hw⟩
  obtain ⟨b, hb, hr⟩ := pfsW_ok hS.1.arena.1 n _ hw
  exact ⟨rfl, rfl, b, hb, L.Ind.decW0B_of' hr⟩

end L.Checker
