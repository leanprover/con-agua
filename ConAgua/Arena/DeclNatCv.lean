import ConAgua.Arena.DeclNatSpec

/-!
# `ci_to_cv` refines `IConstantInfo.toConstantVal` (lane `decls3`, helper `decls3-nat`)

The stored record's inline constant value, or for a projection table a fresh one (the table's
name and level parameters, `Sort 1` interned as the twin interns it). The result decodes in the
record prefix `erecP` of the memory after (`decCV (erecP m') q`), whichever arm ran.
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The inline constant value of a non-projection record. -/
def ciCv? : IConstantInfo → Option IConstantVal
  | .axiomInfo v | .defnInfo v _ _ | .thmInfo v => some v
  | .indInfo v _ | .ctorInfo v _ _ | .recInfo v _ _ _ => some v
  | .projInfo _ => none

theorem decCI_shape {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {ci : IConstantInfo} (h : decCI a dn p = some ci) :
    ∃ w, a[p]? = some w ∧
      ((w.toNat ≤ 5 ∧ ∃ cv, ciCv? ci = some cv ∧ decCV a (p + 1) = some cv) ∨
       (w.toNat = 6 ∧ ∃ tbl, ci = .projInfo tbl ∧ decTbl a p = some tbl)) := by
  unfold decCI at h
  cases hk : nat? a p with
  | none => simp [hk] at h
  | some k =>
  have hw : ∃ w, a[p]? = some w ∧ w.toNat = k := by
    simp only [nat?, Option.map_eq_some_iff] at hk
    obtain ⟨w, hw, hk⟩ := hk; exact ⟨w, hw, hk⟩
  obtain ⟨w, hw, hwk⟩ := hw
  rw [hk] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨a1, ha1, h⟩ := h
  cases ha1
  refine ⟨w, hw, ?_⟩
  rcases k with _ | _ | _ | _ | _ | _ | _ | k
  · -- the tag 6 case is the seventh; the first six are inline constant values
    simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, h⟩ := h
    left
    exact ⟨by omega, cv, by subst h; rfl, hcv⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, h⟩ := h
    left
    exact ⟨by omega, cv, by obtain ⟨_, -, _, -, rfl⟩ := h; rfl, hcv⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, h⟩ := h
    left
    exact ⟨by omega, cv, by subst h; rfl, hcv⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, h⟩ := h
    left
    exact ⟨by omega, cv, by obtain ⟨_, -, rfl⟩ := h; rfl, hcv⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, h⟩ := h
    left
    exact ⟨by omega, cv, by obtain ⟨_, -, _, -, rfl⟩ := h; rfl, hcv⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, h⟩ := h
    left
    exact ⟨by omega, cv, by obtain ⟨_, -, _, -, _, -, _, -, _, -, rfl⟩ := h; rfl, hcv⟩
  · simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨tbl, htbl, rfl⟩ := h
    right
    exact ⟨by omega, tbl, rfl, htbl⟩
  · simp at h

/-- The words of a decoded projection table: the table name, the level-parameter slice. -/
theorem decTbl_words {a : Array Word} {p : Nat} {tbl : IProjTable} (h : decTbl a p = some tbl) :
    ∃ w0 lo ll, a[p + 1]? = some w0 ∧ w0.toNat < 2 ^ 32 ∧ tbl.tableName = decI w0 ∧
      a[p + 3]? = some lo ∧ a[p + 4]? = some ll ∧
      hslice? a lo.toNat ll.toNat = some tbl.levelParams := by
  simp only [decTbl, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨tn, htn, sn, -, lv, hlv, rest⟩ := h
  simp only [hlist?, bind, Option.bind_eq_some_iff] at hlv
  obtain ⟨o', ho2, l', hl2, hsl⟩ := hlv
  simp only [nat?, Option.map_eq_some_iff] at ho2 hl2
  obtain ⟨lo, hlo, rfl⟩ := ho2
  obtain ⟨ll, hll, rfl⟩ := hl2
  obtain ⟨w0, hw0, hlt, rfl⟩ := hd?_some htn
  obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, rfl⟩ := rest
  exact ⟨w0, lo, ll, hw0, hlt, rfl, hlo, by simpa using hll, hsl⟩


/-- A freshly written constant value `[name, lo, ll, ty]` decodes, its level-parameter slice
being one that already decoded below `N`. -/
theorem decCV_fresh {a a' : Array Word} {q N : Nat} {w0 lo ll ty : Word} {lps : List NIdx}
    (h0 : a'[q]? = some w0) (hw0 : w0.toNat < 2 ^ 32) (h1 : a'[q + 1]? = some lo)
    (h2 : a'[q + 2]? = some ll) (hsl : hslice? a lo.toNat ll.toNat = some lps)
    (hN : 0 < ll.toNat → lo.toNat + ll.toNat ≤ N) (hlow : ∀ i < N, a'[i]? = a[i]?)
    (h3 : a'[q + 3]? = some ty) (hty : ty.toNat < 2 ^ 32) :
    decCV a' q = some ⟨decI w0, lps, decI ty⟩ := by
  have hs : (hslice? a' lo.toNat ll.toNat : Option (List NIdx)) = hslice? a lo.toNat ll.toNat := by
    simp only [hslice?]
    exact mapM_congr_of _ _ _ (fun j hj => by
      have := List.mem_range.mp hj
      have := hN (by omega)
      simp only [hd?, hlow (lo.toNat + j) (by omega)])
  simp only [decCV, bind, Option.bind, pure, hd?, h0, hw0, if_true, hlist?, nat?, h1,
    show q + 1 + 1 = q + 2 by omega, h2, Option.map_some, hs, hsl, h3, hty]

/-- `intern_zero` / `intern_sort` handle words are below `2^32`. -/
theorem zinternW_hw (m : Mem) (a : AState) (hR : ZeroR m a) (w : Word) (m' : Mem)
    (hI : zinternW m = some (w, m')) : w.toNat < 2 ^ 32 := by
  rw [zinternW_eq] at hI
  exact internM_hw zeroSch ZRecRel zhash zeroSch_wf m _ _ _ hR (zMt m) _ _ _ _
    (probe_homeG zeroSch m 0 _ _ (zprobeW_arm m 0) _)
    (probe_homeG zeroSch m 1 _ _ (zprobeW_arm m 1) _) _ (zpushOK_room m) _ _ w m' hI

theorem sointernW_hw (m : Mem) (a : AState) (hR : SortR m a) (u : Word) (w : Word) (m' : Mem)
    (hI : sointernW m u = some (w, m')) : w.toNat < 2 ^ 32 := by
  rw [sointernW_eq] at hI
  exact internM_hw sortSch SoRecRel sohash sortSch_wf m _ _ _ hR (soMt m u) _ _ _ _
    (probe_homeG sortSch m 0 _ _ (soprobeW_arm m u 0) _)
    (probe_homeG sortSch m 1 _ _ (soprobeW_arm m u 1) _) _ (sopushOK_room m) _ _ w m' hI


section cvref
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

structure NatCvProg (p : Prog) : Prop extends NatGateProg p where
  lCiToCv : p.lookup "ci_to_cv" = some ciToCv
  lCvNew : p.lookup "cv_new" = some cvNew
  lErecAlloc : p.lookup "erec_alloc" = some erecAlloc

theorem internZero_ref (hM : MasterProg p) :
    CallRef p "intern_zero" [] (StageR dn vis fe) (internLNode .zero)
      (KeepPost dn vis fe decW0L) := by
  refine CallRef.of_triple fun n s₀ a₀ hS => ?_
  refine triple_post (internZero_spec p hM.lZeroFind hM.lZeroPush hM.lInternZero n s₀) ?_
  rintro r s' ⟨hl, hI⟩
  obtain ⟨a', hrun, hS', hg⟩ := internZero_stage hS hI
  exact ⟨hl, decI (r.headD 0), a', hrun, hS', hg, zinternW_hw _ _ hS.1.arena.1.zero _ _ hI, rfl⟩

theorem internSort_ref (hM : MasterProg p) (u : Word) (hu : H u) :
    CallRef p "intern_sort" [u] (StageR dn vis fe) (internE (.sort (decI u)))
      (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_triple fun n s₀ a₀ hS => ?_
  refine triple_post (internSort_spec p hM.lSortFind hM.lSortPush hM.lInternSort n s₀ u) ?_
  rintro r s' ⟨hl, hI⟩
  obtain ⟨a', hrun, hS', hg⟩ := internSort_stage hS u hu hI
  exact ⟨hl, decE (r.headD 0), a', hrun, hS', hg, sointernW_hw _ _ hS.1.arena.1.sort u _ _ hI, rfl⟩

/-- The model of `ci_to_cv(p)`. -/
def ciToCvW (p : Prog) (n : Nat) (m : Mem) (q : Word) : Option (List Word × Mem) :=
  if rdW (m.arr64 EREC) q ≤ 5 then some ([q + 1], m)
  else if rdW (m.arr64 EREC) q ≠ 6 then none
  else
  bW (callW p n "intern_zero" [] m) fun r1 m1 =>
  bW (callW p n "intern_succ" [r1.headD 0] m1) fun r2 m2 =>
  bW (callW p n "intern_sort" [r2.headD 0] m2) fun r3 m3 =>
  bW (callW p n "cv_new" [rdW (m3.arr64 EREC) (q + 1), rdW (m3.arr64 EREC) (q + 3),
    rdW (m3.arr64 EREC) (q + 4), r3.headD 0] m3) fun r4 m4 => some ([r4.headD 0], m4)

theorem ciToCv_specW (p : Prog) (hp : p.lookup "ci_to_cv" = some ciToCv) (n : Nat) (s₀ : St)
    (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ci_to_cv" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ ciToCvW p n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, ciToCv]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "intern_zero", callW_spec p n "intern_succ", callW_spec p n "intern_sort",
      callW_spec p n "cv_new"] <;>
    finish (gen := 20) [ciToCvW, bW]



theorem IWGrow.erec_get {m m' : Mem} (h : IWGrow m m') {i : Nat} {v : Word}
    (hv : (erecP m)[i]? = some v) : (m'.arr64 EREC)[i]? = some v := by
  simp only [erecP, Array.getElem?_extract] at hv
  split at hv
  · rename_i hi
    have hi' : i < erTop m := by simp [erTop, erecTop] at hi ⊢; omega
    rw [h.2.2.2 i hi']; simpa using hv
  · simp at hv

theorem erecP_get' {m : Mem} {i : Nat} (h : i < erTop m) (hs : erTop m ≤ (m.arr64 EREC).size) :
    (erecP m)[i]? = (m.arr64 EREC)[i]? := by
  simp only [erecP, Array.getElem?_extract, erecTop, erTop] at h hs ⊢
  rw [if_pos (by omega)]; simp

theorem erecP_size_le' (m : Mem) : (erecP m).size ≤ erTop m := by
  simp only [erecP, Array.size_extract, erecTop, erTop]; omega

theorem toConstantVal_inline {ci : IConstantInfo} {cv : IConstantVal} (h : ciCv? ci = some cv) :
    ci.toConstantVal = pure cv := by
  cases ci <;> simp_all [ciCv?, IConstantInfo.toConstantVal]

theorem rdW_erec_of {m : Mem} {q : Word} {w : Word} (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (h : (erecP m)[q.toNat]? = some w) : rdW (m.arr64 EREC) q = w := by
  simp [rdW, erecP_get h]

theorem word_add_nat (q : Word) (k : Nat) (h : q.toNat + k < 2 ^ 64) :
    (q + UInt64.ofNat k).toNat = q.toNat + k := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (show k < UInt64.size by unfold UInt64.size; omega)]
  omega


theorem ciToCv_ref (hN : NatCvProg p) (q : Word) (ci : IConstantInfo) :
    CallRef p "ci_to_cv" [q]
      (fun m a => StageR dn vis fe m a ∧ decCI (erecP m) dn q.toNat = some ci)
      ci.toConstantVal
      (fun m m' a' r cv => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        decCV (erecP m') (r.headD 0).toNat = some cv) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hci⟩ hc => ?_
  have hw := callW_model (M := fun mm => ciToCvW p k mm q) (ciToCv_specW p hN.lCiToCv k · q) hc
  unfold ciToCvW at hw
  have hsz := hS.2.2.2.2.1
  obtain ⟨w, hwq, hcase⟩ := decCI_shape hci
  have hrd : rdW (m.arr64 EREC) q = w := rdW_erec_of hsz hwq
  rcases hcase with ⟨hle, cv, hcv, hdec⟩ | ⟨h6, tbl, rfl, htbl⟩
  · -- an inline constant value
    have hle' : rdW (m.arr64 EREC) q ≤ 5 := by
      rw [hrd]; exact UInt64.le_iff_toNat_le.mpr (by simpa using hle)
    rw [if_pos hle'] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hq1 : (q + 1).toNat = q.toNat + 1 := by
      have := (Array.getElem?_eq_some_iff.mp (erecP_get hwq)).1
      rw [UInt64.toNat_add]; simp; omega
    refine ⟨cv, a, ?_, hS, IWGrow.refl _, ?_⟩
    · rw [toConstantVal_inline hcv]; rfl
    · simpa [hq1] using hdec
  · -- a projection table
    have hn5 : ¬ rdW (m.arr64 EREC) q ≤ 5 := by
      rw [hrd]; intro e; have := UInt64.le_iff_toNat_le.mp e; simp at this; omega
    have hn6 : ¬ rdW (m.arr64 EREC) q ≠ 6 := by
      rw [hrd]; intro e; apply e; exact UInt64.toNat_inj.mp (by simpa using h6)
    rw [if_neg hn5, if_neg hn6] at hw
    obtain ⟨w0, lo, ll, hw0, hlt0, htn, hlo, hll, hsl⟩ := decTbl_words htbl
    cases h1 : callW p k "intern_zero" [] m with
    | none => rw [h1] at hw; simp at hw
    | some q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, bW_some] at hw
    obtain ⟨x1, a1, hr1, hS1, hg1, hx1l, hx1⟩ := internZero_ref (dn := dn) (vis := vis) (fe := fe)
      hN.toMasterProg k m a r1 m1 hS h1
    cases h2 : callW p k "intern_succ" [r1.headD 0] m1 with
    | none => rw [h2] at hw; simp at hw
    | some q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [h2, bW_some] at hw
    obtain ⟨x2, a2, hr2, hS2, hg2, hx2l, hx2⟩ := internSucc_ref (dn := dn) (vis := vis) (fe := fe)
      hN.toMasterProg (r1.headD 0) hx1l k m1 a1 r2 m2 hS1 h2
    cases h3 : callW p k "intern_sort" [r2.headD 0] m2 with
    | none => rw [h3] at hw; simp at hw
    | some q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, bW_some] at hw
    obtain ⟨x3, a3, hr3, hS3, hg3, hx3l, hx3⟩ := internSort_ref (dn := dn) (vis := vis) (fe := fe)
      hN.toMasterProg (r2.headD 0) hx2l k m2 a2 r3 m3 hS2 h3
    have hg03 : IWGrow m m3 := hg1.trans (hg2.trans hg3)
    -- the words read at `m3` are the decoded ones
    have hq1 : (q + 1).toNat = q.toNat + 1 := by
      have := (Array.getElem?_eq_some_iff.mp (erecP_get hwq)).1
      rw [UInt64.toNat_add]; simp; omega
    have hq3' : q.toNat + 4 < (m.arr64 EREC).size := by
      have := (Array.getElem?_eq_some_iff.mp (erecP_get hll)).1; exact this
    have hq3 : (q + 3).toNat = q.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
    have hq4 : (q + 4).toNat = q.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
    have e1 : rdW (m3.arr64 EREC) (q + 1) = w0 := by
      simp [rdW, hq1, hg03.erec_get hw0]
    have e3 : rdW (m3.arr64 EREC) (q + 3) = lo := by
      simp [rdW, hq3, hg03.erec_get hlo]
    have e4 : rdW (m3.arr64 EREC) (q + 4) = ll := by
      simp [rdW, hq4, hg03.erec_get hll]
    rw [e1, e3, e4] at hw
    cases h4 : callW p k "cv_new" [w0, lo, ll, r3.headD 0] m3 with
    | none => rw [h4] at hw; simp at hw
    | some q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [h4, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (cvNew_specW p hN.lErecAlloc hN.lCvNew k _ w0 lo ll (r3.headD 0)) h4
    change cvNewW m3 w0 lo ll (r3.headD 0) = some (r4.headD 0, s'.mem) at hW
    unfold cvNewW at hW
    cases h5 : erAllocW m3 4 with
    | none => rw [h5] at hW; cases hW
    | some qq =>
    obtain ⟨q4, m31⟩ := qq
    rw [h5] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hq4e, hm4⟩ := hW
    obtain ⟨hS4, hg4, hq4t, htop4, hget4⟩ := erRec_stage h5 hS3 [w0, lo, ll, r3.headD 0] rfl
    rw [← hm4, cvNewMem_eq]
    refine ⟨⟨tbl.tableName, tbl.levelParams, x3⟩, a3, ?_, hS4, hg03.trans hg4, ?_⟩
    · simp only [IConstantInfo.toConstantVal, StateT.run_bind, hr1, exc_ok_bind', ← hx1, hr2, ← hx2,
        hr3, StateT.run_pure]
      rfl
    · rw [← hq4e]
      -- the fresh record decodes in the prefix
      have hgg : IWGrow m (wrER m31 q4 [w0, lo, ll, r3.headD 0]) := hg03.trans hg4
      have hidx : ∀ j, j < 4 → (erecP (wrER m31 q4 [w0, lo, ll, r3.headD 0]))[q4.toNat + j]? =
          [w0, lo, ll, r3.headD 0][j]? := by
        intro j hj
        rw [erecP_get' (by have := htop4; have := hq4t; simp only [List.length_cons, List.length_nil] at *; omega) hS4.2.2.1, hget4 j hj]
      have hbound : 0 < ll.toNat → lo.toNat + ll.toNat ≤ erTop m := fun hpos =>
        Nat.le_trans (hslice?_bound _ _ _ _ hsl hpos) (erecP_size_le' m)
      rw [htn, ← hx3]
      refine decCV_fresh (a := erecP m) (N := erTop m) ?_ hlt0 ?_ ?_ hsl hbound ?_ ?_ hx3l
      · simpa using hidx 0 (by decide)
      · simpa using hidx 1 (by decide)
      · simpa using hidx 2 (by decide)
      · intro i hi
        rw [erecP_get' (by have := hgg.2.1; omega) hS4.2.2.1, erecP_get' hi hS.2.2.1]
        exact hgg.2.2.2 i hi
      · simpa using hidx 3 (by decide)


@[refines ConRon.Arena.IConstantInfo.toConstantVal]
theorem ciToCv_refines (hN : NatCvProg p) (q : Word) (ci : IConstantInfo) :
    RefAM p "ci_to_cv" [q]
      (fun m a => StageR dn vis fe m a ∧ decCI (erecP m) dn q.toNat = some ci)
      ci.toConstantVal
      (fun m m' a' r cv => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        decCV (erecP m') (r.headD 0).toNat = some cv) :=
  (ciToCv_ref hN q ci).refAM

end cvref

end L.Ind
