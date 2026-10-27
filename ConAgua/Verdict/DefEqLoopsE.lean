import ConAgua.Verdict.DefEqTailE
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# The `defeq` loops' error claims: `defeq_lst`, `defeq_list_rev` (lane `verdicts-b`, helper `k3`)

The error halves of `DefEqMidLoops.lean`: the loops' error models (`l_model … errors`, the loop
`lstE.loop1`, `lrevE.loop1`), their claims by induction on the fuel (`lstE_ok`, `lrevE_ok`, the
shape of `lstW_ok`, `lrevW_ok`): a failure is an iteration's `defeq` slot call's (`KnotUpToE`),
after the earlier iterations' ok runs (their ok refinements).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `defeq_lst` -/

l_model defeqLst_specE (p : Prog) (hp : p.lookup "defeq_lst" = some defeqLstL)
  fns [hp ↦ lstE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

theorem lstE_loop1_zero (p : Prog) (m : Mem) (mode vis d ao an bo bn i : Word) :
    lstE.loop1 p 0 m mode vis d ao an bo bn i = .error .outOfFuel := by
  unfold lstE.loop1; rfl

section lstRef
variable (p : Prog)

/-- **The loop's error claim** on the slices from index `i` (the error half of `lstW_ok`). -/
theorem lstE_ok (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (mode d ao an bo bn : Word) (hmode : mode < 4) (m₀ : Mem) (xs ys : List EIdx)
    (hx : SpineR m₀ ao an xs.toArray) (hy : SpineR m₀ bo bn ys.toArray)
    (hxt : ao.toNat + an.toNat ≤ (spTop m₀).toNat) (hyt : bo.toNat + bn.toNat ≤ (spTop m₀).toNat) :
    ∀ k, k ≤ n + 1 → ∀ (i : Word) (m : Mem) (a : AState) (M : ModeMaps) (eb : Word) (er : Err),
      CoreS dn m a vis fe M eb → eb = (mode >>> 1) &&& 1 → StackKept m₀ m → i ≤ an → i ≤ bn →
      lstE.loop1 p k m mode vis d ao an bo bn i = .error er →
      ErrClaim (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat (xs.drop i.toNat)
        (ys.drop i.toNat)) a er := by
  intro k
  induction k with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ h
    rw [lstE_loop1_zero] at h; cases h
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
    intro hkn i m a M eb er hS heb hst hia hib h
    by_cases hex : an ≤ i ∨ bn ≤ i
    · rw [lstE.loop1.arm1 (hc1 := rfl) (hc2 := hex)] at h; cases h
    have hia2 : i.toNat < an.toNat := by
      rcases Nat.lt_or_ge i.toNat an.toNat with h | h
      · exact h
      · exact absurd (.inl (UInt64.le_iff_toNat_le.mpr h)) hex
    have hib2 : i.toNat < bn.toNat := by
      rcases Nat.lt_or_ge i.toNat bn.toNat with h | h
      · exact h
      · exact absurd (.inr (UInt64.le_iff_toNat_le.mpr h)) hex
    rw [lstE.loop1.arm2 (hc1 := rfl) (hc2 := hex), show rdW (m.arr64 SPN) = spW m from rfl] at h
    obtain ⟨hlx, hgx, hwx⟩ := slice_get hx i hia2
    obtain ⟨hly, hgy, hwy⟩ := slice_get hy i hib2
    rw [slice_kept hst hxt i hia2, slice_kept hst hyt i hib2] at h
    rw [List.drop_eq_getElem_cons hlx, List.drop_eq_getElem_cons hly, defEqList_cons, hgx, hgy]
    cases hc : callE p k "defeq" [mode, vis, d, spW m₀ (ao + i), spW m₀ (bo + i)] m with
    | error e =>
      rw [hc, lstE.k_defeq.none] at h; cases h
      exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
        ((hkE k (by omega)).defeq F _ a dn vis fe M eb mode d _ _ (by omega) (by omega)
          ⟨hS, hmode, heb⟩ hwx hwy) hc)
    | ok q =>
    obtain ⟨r, m₁⟩ := q
    rw [hc] at h
    have h₁ := CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
      ((hk k (by omega)).defeq F _ a dn vis fe M eb mode d _ _ (by omega) (by omega)
        ⟨hS, hmode, heb⟩ hwx hwy) (callW_of_callE hc)
    refine ErrClaim.bind_coreS h₁ (fun M₁ hS₁ hst₁ => ?_)
    by_cases h0 : r.headD 0 = 0
    · rw [lstE.k_defeq.arm1 (hc1 := h0)] at h; cases h
    rw [lstE.k_defeq.arm2 (hc1 := h0)] at h
    rw [decBool_t h0, ite_eq_left rfl]
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; have := an.toNat_lt; omega
    have := ih (by omega) (i + 1) m₁ _ M₁ eb er hS₁ heb (hst.trans hst₁)
      (UInt64.le_iff_toNat_le.mpr (by omega)) (UInt64.le_iff_toNat_le.mpr (by omega)) h
    rw [hi1] at this
    exact this

/-- **`defeq_lst`'s error claim** (`DefeqLstE`, the error half of `defeqLst_refines`). -/
theorem defeqLst_refinesE (hp : p.lookup "defeq_lst" = some defeqLstL) : DefeqLstE p := by
  intro n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d ao an bo bn xs ys hs hx hy hxt hyt
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (defeqLst_specE p hp (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d ao an bo bn) hc0 (Err.code_ne_of_cls hkc)
  rw [lstE.arm1] at hW
  have := lstE_ok p n hk hkE F hF hn dn vis fe mode d ao an bo bn hs.mode4 s₀.mem xs.toList ys.toList
    (by simpa using hx) (by simpa using hy) hxt hyt (n + 1) (Nat.le_refl _) 0 s₀.mem a₀ M eb er hs.rel
    hs.eb_mode (StackKept.refl _) UInt64.zero_le UInt64.zero_le hW
  simpa only [UInt64.toNat_zero, List.drop_zero] using this

end lstRef

/-! ## `defeq_list_rev` -/

l_model defeqListRev_specE (p : Prog) (hp : p.lookup "defeq_list_rev" = some defeqListRevL)
  fns [hp ↦ lrevE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

theorem lrevE_loop1_zero (p : Prog) (m : Mem) (mode vis d ao an bo bn i j : Word) :
    lrevE.loop1 p 0 m mode vis d ao an bo bn i j = .error .outOfFuel := by
  unfold lrevE.loop1; rfl

section lrevRef
variable (p : Prog)

/-- **The reversed loop's error claim** (the error half of `lrevW_ok`). -/
theorem lrevE_ok (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (mode d ao an bo bn : Word) (hmode : mode < 4) (m₀ : Mem) (xs ys : List EIdx)
    (hx : SpineR m₀ ao an xs.toArray) (hy : SpineR m₀ bo bn ys.toArray)
    (hxt : ao.toNat + an.toNat ≤ (spTop m₀).toNat) (hyt : bo.toNat + bn.toNat ≤ (spTop m₀).toNat) :
    ∀ k, k ≤ n + 1 → ∀ (i j : Word) (m : Mem) (a : AState) (M : ModeMaps) (eb : Word) (er : Err),
      CoreS dn m a vis fe M eb → eb = (mode >>> 1) &&& 1 → StackKept m₀ m → i.toNat ≤ an.toNat →
      j.toNat ≤ bn.toNat → an.toNat - i.toNat = bn.toNat - j.toNat →
      lrevE.loop1 p k m mode vis d ao an bo bn i j = .error er →
      ErrClaim (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat (xs.take i.toNat).reverse
        (ys.take j.toNat).reverse) a er := by
  intro k
  induction k with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
    rw [lrevE_loop1_zero] at h; cases h
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
    intro hkn i j m a M eb er hS heb hst hia hjb hd h
    have h0i : (i = 0) ↔ i.toNat = 0 :=
      ⟨fun h => h ▸ rfl, fun h => UInt64.toNat_inj.mp (by simpa using h)⟩
    have h0j : (j = 0) ↔ j.toNat = 0 :=
      ⟨fun h => h ▸ rfl, fun h => UInt64.toNat_inj.mp (by simpa using h)⟩
    by_cases hex : i = 0 ∨ j = 0
    · rw [lrevE.loop1.arm1 (hc1 := rfl) (hc2 := hex)] at h; cases h
    have hi0 : i ≠ 0 := fun h => hex (.inl h)
    have hj0 : j ≠ 0 := fun h => hex (.inr h)
    have hi1 := word_pred i hi0
    have hj1 := word_pred j hj0
    have hin : i.toNat ≠ 0 := fun h => hi0 (h0i.mpr h)
    have hjn : j.toNat ≠ 0 := fun h => hj0 (h0j.mpr h)
    rw [lrevE.loop1.arm2 (hc1 := rfl) (hc2 := hex), show rdW (m.arr64 SPN) = spW m from rfl] at h
    obtain ⟨hlx, hgx, hwx⟩ := slice_get hx (i - 1) (by omega)
    obtain ⟨hly, hgy, hwy⟩ := slice_get hy (j - 1) (by omega)
    rw [slice_kept hst hxt (i - 1) (by omega), slice_kept hst hyt (j - 1) (by omega)] at h
    have ei : i.toNat = (i - 1).toNat + 1 := by omega
    have ej : j.toNat = (j - 1).toNat + 1 := by omega
    rw [ei, ej, take_rev_succ xs _ hlx, take_rev_succ ys _ hly, defEqList_cons, hgx, hgy]
    cases hc : callE p k "defeq" [mode, vis, d, spW m₀ (ao + (i - 1)), spW m₀ (bo + (j - 1))] m with
    | error e =>
      rw [hc, lrevE.k_defeq.none] at h; cases h
      exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
        ((hkE k (by omega)).defeq F _ a dn vis fe M eb mode d _ _ (by omega) (by omega)
          ⟨hS, hmode, heb⟩ hwx hwy) hc)
    | ok q =>
    obtain ⟨r, m₁⟩ := q
    rw [hc] at h
    have h₁ := CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
      ((hk k (by omega)).defeq F _ a dn vis fe M eb mode d _ _ (by omega) (by omega)
        ⟨hS, hmode, heb⟩ hwx hwy) (callW_of_callE hc)
    refine ErrClaim.bind_coreS h₁ (fun M₁ hS₁ hst₁ => ?_)
    by_cases h0 : r.headD 0 = 0
    · rw [lrevE.k_defeq.arm1 (hc1 := h0)] at h; cases h
    rw [lrevE.k_defeq.arm2 (hc1 := h0)] at h
    rw [decBool_t h0, ite_eq_left rfl]
    exact ih (by omega) (i - 1) (j - 1) m₁ _ M₁ eb er hS₁ heb (hst.trans hst₁) (by omega)
      (by omega) (by omega) h

/-- **`defeq_list_rev`'s error claim** (the error half of `defeqListRev_refines`). -/
theorem defeqListRev_refinesE (hp : p.lookup "defeq_list_rev" = some defeqListRevL) (n : Nat)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ao an bo bn : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (xs ys : List EIdx)
    (hx : SpineR s₀.mem ao an xs.toArray) (hy : SpineR s₀.mem bo bn ys.toArray)
    (hxt : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat)
    (hyt : bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpecE p (n + 1) "defeq_list_rev" [mode, vis, d, ao, an, bo, bn]
      (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat xs.reverse ys.reverse) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (defeqListRev_specE p hp (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d ao an bo bn) hc0 (Err.code_ne_of_cls hkc)
  rw [lrevE.arm1] at hW
  have hxl := slice_len hx
  have hyl := slice_len hy
  have := lrevE_ok p n hk hkE F hF hn dn vis fe mode d ao an bo bn hs.mode4 s₀.mem xs ys hx hy hxt hyt
    (n + 1) (Nat.le_refl _) an bn s₀.mem a₀ M eb er hs.rel hs.eb_mode
    (StackKept.refl _) (Nat.le_refl _) (Nat.le_refl _) (by omega) hW
  rwa [← hxl, ← hyl, List.take_length, List.take_length] at this

end lrevRef

end L.Arena

/-! ## `defeq_list` (`WhnfIota.lean`'s) -/

namespace L.Arena

l_model defeqList_specE (p : Prog) (hp : p.lookup "defeq_list" = some defeqListL)
  fns [hp ↦ dlE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

theorem dlE_loop1_zero (p : Prog) (m : Mem) (mode vis d ao an bo bn i : Word) :
    dlE.loop1 p 0 m mode vis d ao an bo bn i = .error .outOfFuel := by
  unfold dlE.loop1; rfl

/-- **The `defeq_list` loop's error claim** (the error half of `dlW_ok`), by induction on the
fuel. -/
theorem dlE_ok (p : Prog) (n F : Nat) (hknot : KnotUpTo p n) (hknotE : KnotUpToE p n) (hnF : n ≤ F)
    (hn62 : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ao an bo bn : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (aas bs : Array EIdx) :
    ∀ (k : Nat) (m : Mem) (a : AState) (M : ModeMaps) (i : Word) (er : Err),
      i.toNat ≤ an.toNat → i.toNat ≤ bn.toNat → k ≤ n + 1 →
      CoreS dn m a vis fe M eb → SpineN m ao an aas → SpineN m bo bn bs →
      (an ≠ 0 → ao.toNat + an.toNat ≤ (spTop m).toNat) →
      (bn ≠ 0 → bo.toNat + bn.toNat ≤ (spTop m).toNat) →
      dlE.loop1 p k m mode vis d ao an bo bn i = .error er →
      ErrClaim (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat (aas.toList.drop i.toNat)
        (bs.toList.drop i.toNat)) a er := by
  intro k
  induction k with
  | zero =>
    intro m a M i er _ _ _ _ _ _ _ _ hL
    rw [dlE_loop1_zero] at hL; cases hL
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
    intro m a M i er hia hib hk hS hsa hsb hta htb hL
    rcases Classical.em ¬(i < an ∧ i < bn) with hn | hn
    · rw [dlE.loop1.arm2 (hc1 := hn)] at hL; cases hL
    replace hn := Classical.not_not.mp hn
    rw [dlE.loop1.arm1 (hc1 := hn)] at hL
    have hia' : i.toNat < an.toNat := hn.1
    have hib' : i.toNat < bn.toNat := hn.2
    have hna : an ≠ 0 := fun h => by rw [h] at hia'; simp at hia'
    have hnb : bn ≠ 0 := fun h => by rw [h] at hib'; simp at hib'
    have hsa' := hsa.2 hna
    have hsb' := hsb.2 hnb
    have hsza : i.toNat < aas.size := by rw [hsa'.size]; exact hia'
    have hszb : i.toNat < bs.size := by rw [hsb'.size]; exact hib'
    have hdra : aas.toList.drop i.toNat = aas[i.toNat] :: aas.toList.drop (i.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hsza)]; simp
    have hdrb : bs.toList.drop i.toNat = bs[i.toNat] :: bs.toList.drop (i.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hszb)]; simp
    have hga : aas[i.toNat] = decE (rdW (m.arr64 SPN) (ao + i)) := by
      have := hsa'.get i.toNat hsza
      simpa [spW, toUInt64_toNat_self] using this
    have hgb : bs[i.toNat] = decE (rdW (m.arr64 SPN) (bo + i)) := by
      have := hsb'.get i.toNat hszb
      simpa [spW, toUInt64_toNat_self] using this
    have hxa : HW (rdW (m.arr64 SPN) (ao + i)) := by
      have := hsa'.lt i.toNat hia'
      unfold HW; simpa [spW, toUInt64_toNat_self] using this
    have hxb : HW (rdW (m.arr64 SPN) (bo + i)) := by
      have := hsb'.lt i.toNat hib'
      unfold HW; simpa [spW, toUInt64_toNat_self] using this
    rw [hga] at hdra
    rw [hgb] at hdrb
    rw [hdra, hdrb, defEqList_cons]
    cases hc : callE p k "defeq" [mode, vis, d, rdW (m.arr64 SPN) (ao + i), rdW (m.arr64 SPN) (bo + i)]
        m with
    | error e =>
      rw [hc, dlE.k_defeq.none] at hL; cases hL
      exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
        ((hknotE k (by omega)).defeq F ⟨m, Locals.init []⟩ a dn vis fe M eb mode d _ _ (by omega)
          (by omega) ⟨hS, hm4, hebm⟩ hxa hxb) hc)
    | ok q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hc] at hL
    have e₁ := CoreSpec.of_callW
      ((hknot k (by omega)).defeq F ⟨m, Locals.init []⟩ a dn vis fe M eb mode d _ _ (by omega)
        (by omega) ⟨hS, hm4, hebm⟩ hxa hxb) (callW_of_callE hc)
    refine ErrClaim.bind_coreS e₁ (fun M₁ hS₁ hSt₁ => ?_)
    by_cases h0 : r₁.headD 0 = 0
    · rw [dlE.k_defeq.arm1 (hc1 := h0)] at hL; cases hL
    rw [dlE.k_defeq.arm2 (hc1 := h0)] at hL
    rw [decBool_t h0, ite_eq_left rfl]
    have hsa₁ : SpineN m₁ ao an aas := hsa'.toN.keep hSt₁.size hSt₁.below (hta hna) hS.spn
    have hsb₁ : SpineN m₁ bo bn bs := hsb'.toN.keep hSt₁.size hSt₁.below (htb hnb) hS.spn
    have hta₁ : an ≠ 0 → ao.toNat + an.toNat ≤ (spTop m₁).toNat := fun h => by
      rw [hSt₁.1]; exact hta h
    have htb₁ : bn ≠ 0 → bo.toNat + bn.toNat ≤ (spTop m₁).toNat := fun h => by
      rw [hSt₁.1]; exact htb h
    have h1 : (i + 1).toNat = i.toNat + 1 := uint64_succ_toNat an i hn.1
    have := ih m₁ _ M₁ (i + 1) er (by omega) (by omega) (by omega) hS₁ hsa₁ hsb₁ hta₁ htb₁ hL
    rw [h1] at this
    exact this

/-- **`defeq_list`'s error claim** (the error half of `defeqList_refines`). -/
theorem defeqList_refinesE (p : Prog) (hp : IotaProg' p) :
    ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d ao an bo bn : Word) (aas bs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 →
    SpineN s₀.mem ao an aas → SpineN s₀.mem bo bn bs →
    (an ≠ 0 → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) →
    (bn ≠ 0 → bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat) →
    CoreSpecE p (n + 1) "defeq_list" [mode, vis, d, ao, an, bo, bn]
      (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat aas.toList bs.toList) s₀ a₀ := by
  intro n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d ao an bo bn aas bs hS hm4 hebm hsa hsb hta htb
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (defeqList_specE p hp.defeqList (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d ao an bo bn) hc0 (Err.code_ne_of_cls hkc)
  rw [dlE.arm1] at hW
  have := dlE_ok p n F hk hkE hnF hn62 dn vis fe eb mode d ao an bo bn hm4 hebm aas bs (n + 1) _ a₀ MM 0
    er (by simp) (by simp) (Nat.le_refl _) hS hsa hsb hta htb hW
  simpa using this

end L.Arena
