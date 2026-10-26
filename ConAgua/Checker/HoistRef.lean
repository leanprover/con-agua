import ConAgua.Checker.HoistTargetsRef
import ConAgua.Checker.HoistOrderRef
import ConAgua.Census.Attr

/-!
# `hoist_nat_op_ground` refines `hoistNatOpGround` (lane `front4`)

The assembly: the name index (`hoistIndexGo_ok`), two fresh slices (targets, stack), the targets
zeroed, the targets pass (`targets_ok`: the twin's `hoistTargets`), `hoist_any` (`isEmpty`), and
the reorder (`hoistApply_ok`: `applyHoist`'s sorted order). When L returns, the twin returns, in
the same state, the records in the order L's result slice gives (`OrdR`); `movedNames` (the second
component) is not computed (docs/deviations.md D30).
-/

open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

theorem getElem?_of_rd2 {m m' : Mem} (hs : (m'.arr64 IW).size = (m.arr64 IW).size) {x : Nat}
    (hx : x < 2 ^ 64) (h : rd m' x = rd m x) : (m'.arr64 IW)[x]? = (m.arr64 IW)[x]? := by
  have e : (UInt64.ofNat x).toNat = x := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hx
  simp only [rd, rdW, e] at h
  by_cases hl : x < (m.arr64 IW).size
  · rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem hl] at *
    simp at h; rw [h]
  · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]

/-- The stream relation needs only the `IW` words below `B`, `DECL` and `DLP`. -/
theorem ordR_low {m m' : Mem} {ord : Word} {ds : Array IDeclaration} (B : Nat) (hO : OrdR m ord ds)
    (hB : ord.toNat + ds.size ≤ B) (hBs : B < 2 ^ 64)
    (hIW : ∀ x : Nat, x < B → (m'.arr64 IW)[x]? = (m.arr64 IW)[x]?)
    (hD : m'.arr64 DECL = m.arr64 DECL) (hP : m'.arr64 DLP = m.arr64 DLP) : OrdR m' ord ds := by
  intro k hk
  have hn : (ord + UInt64.ofNat k).toNat = ord.toNat + k := addW_toNat _ _ (by omega)
  have hr : rdW (m'.arr64 IW) (ord + UInt64.ofNat k) = rdW (m.arr64 IW) (ord + UInt64.ofNat k) := by
    simp only [rdW, hn]; rw [hIW _ (by omega)]
  rw [hr, hD, hP]
  exact hO k hk

/-- An allocation is an `AFr`. -/
theorem allocW_afr {m m₁ : Mem} {k q : Word} (hw : allocW m k = some (q, m₁)) (hI : IWOK m) :
    AFr m m₁ ∧ q.toNat = iwTop m ∧ iwTop m₁ = iwTop m + k.toNat ∧ iwTop m + k.toNat ≤ (m.arr64 IW).size := by
  obtain ⟨hq, hm1, hk, hroom, htop⟩ := allocW_post hw hI
  have hf : MemFrame [IW] [200] m m₁ := by
    rw [hm1]; exact (MemFrame.setCtl m 200 _).mono (by simp) (by simp)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  have hsz := hf.2.2.1
  have hER : m₁.arr64 EREC = m.arr64 EREC := hf.1 EREC (by decide) (by decide)
  have h129 : erTop m₁ = erTop m := by simp only [erTop]; rw [hf.2.1 129 (by decide)]
  refine ⟨⟨hf, hk.1, ?_⟩, by rw [hq]; rfl, htop, hroom⟩
  exact ⟨by rw [htop, hsz IW]; exact hroom, by rw [h129, hER]; exact h2, by rw [hsz IW]; exact h3,
    by rw [hER]; exact h4, by rw [hsz CTL]; exact h5⟩

/-- **The hoist on the model**: when `hoist_nat_op_ground(ord, c)` returns `r`, the twin's
`hoistNatOpGround ds` succeeds in the same state, and the slice `IW[r ‥ r + c)` is its records'
order (`OrdR`). -/
theorem hNatOpGround_ok (p : Prog) (hx : HoistExt p) (n : Nat) (m m' : Mem) (a : AState)
    (ds : Array IDeclaration) (ord cw r : Word) (hA : ArenaR m a) (hseen : ∃ s, SeenR m s)
    (hnix : ∃ idx, NixR m idx) (hO : OrdR m ord ds) (hc : ds.size = cw.toNat)
    (hc60 : cw.toNat < 2 ^ 60) (hI : IWOK m)
    (hord : ord.toNat + cw.toNat ≤ iwTop m) (hP : PinsR m a.pins)
    (h : hNatOpGroundW p n m ord cw = some (r, m')) :
    ∃ res, (hoistNatOpGround ds).run a = .ok (res, a) ∧ res.1.size = cw.toNat ∧ OrdR m' r res.1 ∧
      ArenaR m' a ∧ IWOK m' ∧ IWGrow m m' ∧ r.toNat + cw.toNat ≤ iwTop m' ∧ PinsR m' a.pins ∧
      MemFrame [IW, HSEEN, HNIX] [73, 74, 75, 76, 200] m m' := by
  have hsz := hI.2.2.1
  have htsz : iwTop m ≤ (m.arr64 IW).size := hI.1
  cases n with
  | zero => rw [hNatOpGroundW.eq_1] at h; cases h
  | succ n =>
  by_cases hw : rdW (m.arr64 CTL) hnSch.cs + 2 = 0
  · simp [hNatOpGroundW, hw] at h
  rw [hNatOpGroundW.arm1 _ _ _ _ _ hw] at h
  -- the name index
  obtain ⟨idx₀, hR₀⟩ := hnix
  have hfc := mclearG_frame hnSch m
  have hRc : NixR (mclearG hnSch m) ∅ := memoRV_clear hnSch hnSch_wf nmKey _ m idx₀ hR₀ hw
  have hIWc : (mclearG hnSch m).arr64 IW = m.arr64 IW := hfc.1 IW (by simp) (by decide)
  have hOc : OrdR (mclearG hnSch m) ord ds :=
    ordR_low (iwTop m) hO (by omega) (by omega) (fun x _ => by rw [hIWc])
      (hfc.1 DECL (by simp) (by decide)) (hfc.1 DLP (by simp) (by decide))
  rcases hix : hIndexGoW n (mclearG hnSch m) ord cw 0 with _ | ⟨z₁, m₁⟩ <;> rw [hix] at h
  · simp [hNatOpGroundW.k_hoist_index_go.eq_1] at h
  rw [hNatOpGroundW.k_hoist_index_go.arm1] at h
  obtain ⟨hR₁, hf₁⟩ := hoistIndexGo_ok n _ m₁ ord cw 0 z₁ ds ∅ hOc hc hc60 (by omega)
    UInt64.zero_le hRc hix
  simp only [UInt64.toNat_zero] at hR₁
  have hf₀₁ : MemFrame [HNIX] [75, 76] m m₁ := (hfc.mono (by simp) (by simp)).trans hf₁
  have hIW₁ : m₁.arr64 IW = m.arr64 IW := hf₀₁.1 IW (by decide) (by decide)
  have htop₁ : iwTop m₁ = iwTop m := by simp only [iwTop]; rw [hf₀₁.2.1 200 (by decide)]
  have hI₁ : IWOK m₁ := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hI
    have hER : m₁.arr64 EREC = m.arr64 EREC := hf₀₁.1 EREC (by decide) (by decide)
    have h129 : erTop m₁ = erTop m := by simp only [erTop]; rw [hf₀₁.2.1 129 (by decide)]
    exact ⟨by rw [htop₁, hIW₁]; exact h1, by rw [h129, hER]; exact h2, by rw [hIW₁]; exact h3,
      by rw [hER]; exact h4, by rw [hf₀₁.2.2.1 CTL]; exact h5⟩
  -- the targets and the stack
  rcases ha₁ : allocW m₁ cw with _ | ⟨tg, m₂⟩ <;> rw [ha₁] at h
  · simp [hNatOpGroundW.k_iw_alloc.eq_1] at h
  rw [hNatOpGroundW.k_iw_alloc.arm1] at h
  obtain ⟨hA₂, htg, htop₂, hroom₂⟩ := allocW_afr ha₁ hI₁
  rcases ha₂ : allocW m₂ cw with _ | ⟨ws, m₃⟩ <;> rw [ha₂] at h
  · simp [hNatOpGroundW.k_iw_alloc_2.eq_1] at h
  rw [hNatOpGroundW.k_iw_alloc_2.arm1] at h
  obtain ⟨hA₃, hws, htop₃, hroom₃⟩ := allocW_afr ha₂ hA₂.2.2
  have hsz₂ : (m₂.arr64 IW).size = (m.arr64 IW).size := by rw [hA₂.1.2.2.1 IW, hIW₁]
  have hsz₃ : (m₃.arr64 IW).size = (m.arr64 IW).size := by rw [hA₃.1.2.2.1 IW, hsz₂]
  rcases hz : hZeroW n m₃ tg cw 0 with _ | ⟨z₄, m₄⟩ <;> rw [hz] at h
  · simp [hNatOpGroundW.k_hoist_zero.eq_1] at h
  rw [hNatOpGroundW.k_hoist_zero.arm1] at h
  obtain ⟨hf₄, hrd₄⟩ := hZero_ok n m₃ m₄ tg cw 0 z₄ (by rw [hsz₃]; omega) (by rw [hsz₃]; exact hsz) hz
  have hsz₄ : (m₄.arr64 IW).size = (m.arr64 IW).size := by rw [hf₄.2.2.1 IW, hsz₃]
  have htop₄ : iwTop m₄ = iwTop m₃ := by simp only [iwTop]; rw [hf₄.2.1 200 (by simp)]
  -- the cells below the targets are the original ones
  have hlow : ∀ x : Nat, x < tg.toNat → (m₄.arr64 IW)[x]? = (m.arr64 IW)[x]? := by
    intro x hx
    have e4 : (m₄.arr64 IW)[x]? = (m₃.arr64 IW)[x]? :=
      getElem?_of_rd2 (by rw [hsz₄, hsz₃]) (by omega) (by rw [hrd₄ x (by omega), ite_eq_right (by simp; omega)])
    rw [e4, hA₃.2.1.2.2.1 x (by omega), hA₂.2.1.2.2.1 x (by omega), hIW₁]
  have hfA : MemFrame [IW, HNIX] [75, 76, 200] m m₄ :=
    ((hf₀₁.mono (by simp) (by simp)).trans ((hA₂.1.trans hA₃.1).mono (by simp) (by simp))).trans
      (hf₄.mono (by simp) (by simp))
  have hD₄ : m₄.arr64 DECL = m.arr64 DECL := hfA.1 DECL (by decide) (by decide)
  have hDLP₄ : m₄.arr64 DLP = m.arr64 DLP := hfA.1 DLP (by decide) (by decide)
  have hI₄ : IWOK m₄ := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hA₃.2.2
    have hER : m₄.arr64 EREC = m₃.arr64 EREC := hf₄.1 EREC (by decide) (by decide)
    have h129 : erTop m₄ = erTop m₃ := by simp only [erTop]; rw [hf₄.2.1 129 (by simp)]
    exact ⟨by rw [htop₄, hf₄.2.2.1 IW]; exact h1, by rw [h129, hER]; exact h2,
      by rw [hf₄.2.2.1 IW]; exact h3, by rw [hER]; exact h4, by rw [hf₄.2.2.1 CTL]; exact h5⟩
  have hA4 : ∀ b ∈ [IW, HNIX], 64 ≤ b ∧ b < 256 := by decide
  have hC4 : ∀ x ∈ ([75, 76, 200] : List Word), 64 ≤ x.toNat := by simp
  have hE₄ : HEnv m₄ a ds (nameIndex ds ∅ 0) ord tg ws cw.toNat := by
    obtain ⟨s, hs⟩ := hseen
    refine ⟨ArenaR.frame_ext _ _ hA4 hC4 m m₄ hfA a hA,
      ⟨s, memoRG_frame hsSch hsSch_wf bmKey _ _ _ (by decide) (by decide) m m₄ hfA _ hs⟩,
      ordR_low tg.toNat hO (by omega) (by omega) hlow hD₄ hDLP₄, hc, hc60,
      memoRV_frame hnSch hnSch_wf nmKey _ [IW] [200] (by decide) (by decide) m₁ m₄
        ((hA₂.1.trans hA₃.1).trans (hf₄.mono (by simp) (by simp))) (fun _ _ h => h) _ hR₁,
      fun n j hj => by
        have := nameIndex_lt ds ∅ 0 (by intro n j h; simp at h) n j hj; omega,
      by omega, by omega, by rw [hsz₄]; omega, by rw [hsz₄]; exact hsz, by omega, hI₄⟩
  have hT₄ : TgtR m₄ tg cw.toNat ∅ := by
    refine ⟨fun k hk => ?_, fun k _ => by simp⟩
    rw [addrN, ← rd, hrd₄ _ (by omega), ite_eq_left (by simp; omega)]
    simp [tgW]
  have hP₄ : PinsR m₄ a.pins := hP.congr (hfA.1 PINS (by decide) (by decide))
  -- the targets pass
  rcases ht : hTargetsGoW p n m₄ ord cw tg ws 0 with _ | ⟨z₅, m₅⟩ <;> rw [ht] at h
  · simp [hNatOpGroundW.k_hoist_targets_go.eq_1] at h
  rw [hNatOpGroundW.k_hoist_targets_go.arm1] at h
  obtain ⟨T, hrunT, hE₅, hT₅, hTv₅, hlt₅, hP₅, hlow₅⟩ :=
    targets_ok hx cw rfl n m₄ m₅ ∅ 0 z₅ hE₄ hT₄ (fun _ _ h => by simp at h)
      (fun _ _ h => by simp at h) (fun _ _ h => by simp at h) (by simp) hP₄ ht
  simp only [UInt64.toNat_zero] at hrunT
  have hrunH : (hoistTargets ds).run a = .ok (T, a) := hrunT
  -- `hoist_any`
  rcases hy : hAnyW n m₅ tg cw 0 with _ | ⟨av, m₆⟩ <;> rw [hy] at h
  · simp [hNatOpGroundW.k_hoist_any.eq_1] at h
  obtain ⟨hm6, hav⟩ := hoistAny_ok n m₅ m₆ tg cw 0 av T hT₅ (by have := hE₅.rg3; omega) hlt₅ hy
  subst m₆
  simp only [UInt64.toNat_zero] at hav
  have hfrm₅ : MemFrame [IW, HSEEN, HNIX] [73, 74, 75, 76, 200] m m₅ :=
    (hfA.mono (by simp) (by simp)).trans (hlow₅.1.mono (by simp) (by simp))
  -- the pool only grew up to here
  have hgrow₅ : IWGrow m m₅ := by
    have hER : m₅.arr64 EREC = m.arr64 EREC := by
      rw [hlow₅.1.1 EREC (by decide) (by decide), hfA.1 EREC (by decide) (by decide)]
    have h129 : erTop m₅ = erTop m := by
      simp only [erTop]; rw [hlow₅.1.2.1 129 (by decide), hfA.2.1 129 (by decide)]
    refine ⟨by have := hlow₅.2.2; omega, by rw [h129]; exact Nat.le_refl _, fun x hx => ?_, fun x _ => by rw [hER]⟩
    rw [hlow₅.2.1 x (by omega), hlow x (by omega)]
  have hrun0 : (hoistNatOpGround ds).run a =
      ((if T.isEmpty then pure (ds, #[]) else pure (applyHoist ds T) :
        AM (Array IDeclaration × Array NIdx)).run a) := by
    simp only [hoistNatOpGround]
    rw [HoistTwin.run_bind, hrunH]
  by_cases hav0 : av = 0
  · rw [hNatOpGroundW.k_hoist_any.arm1 _ _ _ _ _ _ _ hav0] at h
    cases h
    have hempty : T.isEmpty = true :=
      tgt_isEmpty T _ hT₅.2 (fun j _ hj => (hav.mp hav0) j (Nat.zero_le _) hj)
    refine ⟨(ds, #[]), by rw [hrun0, hempty]; rfl, hc, hE₅.ordR, hE₅.arena, hE₅.iwok,
      hgrow₅, by have := hgrow₅.1; omega, hP₅, hfrm₅⟩
  · rw [hNatOpGroundW.k_hoist_any.arm2 _ _ _ _ _ _ _ hav0] at h
    have hne : T.isEmpty = false := by
      cases e : T.isEmpty with
      | false => rfl
      | true =>
        exfalso; apply hav0; apply hav.mpr
        exact fun j _ _ => Std.HashMap.getElem?_of_isEmpty e
    have hord₅ : ord.toNat + cw.toNat ≤ iwTop m₅ := by have := hgrow₅.1; omega
    have htg₅ : tg.toNat + cw.toNat ≤ iwTop m₅ := by have := hE₅.top; have := hE₅.rg2; omega
    obtain ⟨hI', hgrow', hf', hout, hout', hget⟩ :=
      hoistApply_ok n m₅ m' ord cw tg r T hE₅.iwok hord₅ htg₅ hT₅ hlt₅ h
    have hlen : (hoistOrder T cw.toNat).length = cw.toNat := by simp [hoistOrder, List.length_mergeSort]
    have hmem : ∀ k ∈ hoistOrder T cw.toNat, k < ds.size := by
      intro k hk
      have := (List.mergeSort_perm (List.range cw.toNat) _).mem_iff.mp hk
      rw [hc]; exact List.mem_range.mp this
    have hord_eq : (List.range ds.size).mergeSort (fun a b => !hoistLt T b a) = hoistOrder T cw.toNat := by
      rw [hc]; rfl
    have hres1 : (applyHoist ds T).1 = ((hoistOrder T cw.toNat).map fun k => ds[k]!).toArray := by
      simp only [applyHoist]
      rw [hord_eq]
      exact reorder_eq ds _ hmem
    have hD' : m'.arr64 DECL = m₅.arr64 DECL := hf'.1 DECL (by decide) (by decide)
    have hP' : m'.arr64 DLP = m₅.arr64 DLP := hf'.1 DLP (by decide) (by decide)
    refine ⟨applyHoist ds T, by rw [hrun0, hne]; rfl, by rw [hres1]; simp [hlen],
      ?_, ?_, hI', hgrow₅.trans hgrow', hout', hP₅.congr (hf'.1 PINS (by decide) (by decide)),
      hfrm₅.trans (hf'.mono (by simp) (by simp))⟩
    · intro k hk
      have hk' : k < cw.toNat := by rw [hres1] at hk; simpa [hlen] using hk
      have hkk := hget k hk'
      have hok := hE₅.ordR ((hoistOrder T cw.toNat)[k]'(by rw [hlen]; exact hk'))
        (hmem _ (List.getElem_mem _))
      rw [hkk, hD', hP']
      simp only [hres1, List.getElem_toArray, List.getElem_map]
      rw [getElem!_pos ds _ (hmem _ (List.getElem_mem _))]
      exact hok
    · have hA5 : ∀ b ∈ [IW], 64 ≤ b ∧ b < 256 := by decide
      have hC5 : ∀ x ∈ ([200] : List Word), 64 ≤ x.toNat := by simp
      exact ArenaR.frame_ext _ _ hA5 hC5 m₅ m' hf' a hE₅.arena

/-- **`hoist_nat_op_ground(ord, c)` refines `hoistNatOpGround`** (its first component; the second,
`movedNames`, is dropped by `preparePrelude` and not computed: docs/deviations.md D30). When L
returns `r`, the twin succeeds in the same state and `IW[r ‥ r + c)` is the order of its records;
the memory still represents the store and the pins, and the pool only grew. -/
@[refines_part ConRon.Arena.Frontend.hoistNatOpGround
  "the reordered records (movedNames, dropped by preparePrelude, is not computed: D30)"]
theorem hoistNatOpGround_refines (p : Prog) (hp : HoistProg p) (hx : HoistExt p) (n : Nat) (s₀ : St)
    (a : AState) (ds : Array IDeclaration) (ord cw : Word) (hA : ArenaR s₀.mem a)
    (hseen : ∃ s, SeenR s₀.mem s) (hnix : ∃ idx, NixR s₀.mem idx) (hO : OrdR s₀.mem ord ds)
    (hc : ds.size = cw.toNat) (hc60 : cw.toNat < 2 ^ 60) (hI : IWOK s₀.mem)
    (hord : ord.toNat + cw.toNat ≤ iwTop s₀.mem) (hP : PinsR s₀.mem a.pins) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "hoist_nat_op_ground" [ord, cw]
    ⦃fun r s' => ∃ res, (hoistNatOpGround ds).run a = .ok (res, a) ∧ res.1.size = cw.toNat ∧
      OrdR s'.mem (r.headD 0) res.1 ∧ ArenaR s'.mem a ∧ IWOK s'.mem ∧ IWGrow s₀.mem s'.mem ∧
      (r.headD 0).toNat + cw.toNat ≤ iwTop s'.mem ∧ PinsR s'.mem a.pins ∧
      MemFrame [IW, HSEEN, HNIX] [73, 74, 75, 76, 200] s₀.mem s'.mem; ⊤⦄ :=
  triple_post (hoistNatOpGround_spec p hp hx n s₀ ord cw) (fun r s' h =>
    hNatOpGround_ok p hx n s₀.mem s'.mem a ds ord cw (r.headD 0) hA hseen hnix hO hc hc60 hI hord hP h.2)

/-! ## The links

The pieces are stated over the generated models (`hWalkW`, …), each of which is its L function by
the generated spec (`hoistWalk_spec`, …, `Hoist.lean`): the chain L = model ⊑ twin. -/

attribute [refines ConRon.Arena.Frontend.usedConstsGo] hoistWalk_ok
attribute [refines ConRon.Arena.Frontend.usedConstsRules] hoistRulesGo_ok
attribute [refines ConRon.Arena.Frontend.usedConstsBlock] hoistBlockGo_ok
attribute [refines ConRon.Arena.Frontend.IDeclaration.usedConsts] hoistDepsOf_ok
attribute [refines ConRon.Arena.Frontend.nameIndex] hoistIndexGo_ok
attribute [refines ConRon.Arena.Frontend.hoistClosure] closure_ok
attribute [refines ConRon.Arena.Frontend.hoistTargetsGo.hoistDeps] deps_ok
attribute [refines ConRon.Arena.Frontend.hoistTargetsGo] targets_ok
attribute [refines ConRon.Arena.Frontend.isNatOpRecord] natOpRec_ok
attribute [refines ConRon.Arena.Frontend.hoistTargets] hNatOpGround_ok
attribute [refines ConRon.Arena.Frontend.reorder ConRon.Arena.Frontend.hoistKey
  ConRon.Arena.Frontend.hoistLt] hoistApply_ok
attribute [refines_part ConRon.Arena.Frontend.applyHoist
  "the sorted records (movedNames, dropped by preparePrelude, is not computed: D30)"] hoistApply_ok

end L.Checker
