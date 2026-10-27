import ConAgua.Arena.IndSumSpec.WtW

/-!
# DecCVpGrow

`decCVp_grow`, `ctsK2_big`, `hd?_rdW`, `getSort_of_get`, `viewSort_of_view`, `eViewW_head2` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Constant values read from `EREC` below its top -/

theorem decCVp_grow {m m' : Mem} (hg : IWGrow m m') {cq : Nat} (hcq : cq + 4 ≤ erTop m)
    (hsl : ∀ lo ll, nat? (erA m) (cq + 1) = some lo → nat? (erA m) (cq + 2) = some ll →
      lo + ll ≤ erTop m ∨ ll = 0) {cv : IConstantVal} (h : decCVp m cq = some cv) :
    decCVp m' cq = some cv := by
  have e : ∀ i, i < erTop m → (erA m')[i]? = (erA m)[i]? := fun i hi => hg.2.2.2 i hi
  simp only [decCVp] at h ⊢
  simp only [decCV, bind, Option.bind, pure, hlist?] at h ⊢
  have e0 : (hd? (erA m') cq : Option NIdx) = hd? (erA m) cq := by simp only [hd?, e cq (by omega)]
  have e1 : nat? (erA m') (cq + 1) = nat? (erA m) (cq + 1) := by simp only [nat?, e (cq + 1) (by omega)]
  have e2 : nat? (erA m') (cq + 1 + 1) = nat? (erA m) (cq + 1 + 1) := by
    simp only [nat?, e (cq + 1 + 1) (by omega)]
  have e3 : (hd? (erA m') (cq + 3) : Option EIdx) = hd? (erA m) (cq + 3) := by
    simp only [hd?, e (cq + 3) (by omega)]
  rw [e0, e1, e2, e3]
  cases h1 : nat? (erA m) (cq + 1) with
  | none => rw [h1] at h; revert h; cases (hd? (erA m) cq : Option NIdx) <;> simp
  | some lo =>
  cases h2 : nat? (erA m) (cq + 1 + 1) with
  | none => rw [h1, h2] at h; revert h; cases (hd? (erA m) cq : Option NIdx) <;> simp
  | some ll =>
  have hN := hsl lo ll h1 (by simpa using h2)
  have hs : (hslice? (erA m') lo ll : Option (List NIdx)) = hslice? (erA m) lo ll := by
    simp only [hslice?]
    exact mapM_congr_of _ _ _ (fun j hj => by
      have := List.mem_range.mp hj
      simp only [hd?, e (lo + j) (by omega)])
  rw [h1, h2] at h
  simp only [hs]
  exact h

section arms
variable (cR : CallM) (k : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis cv n cvTa0 bo bl s ss q : Word) (r1 rt r5 : List Word)
theorem ctsK2_big (h : 4294967296 ≤ ss) : ctsK2 cR k vis cv bo bl s (some (ss, m2)) = none := by
  simp [ctsK2, h]
end arms

grind_pattern [ind_grind] ctsK2_big => ctsK2 cR k vis cv bo bl s (some (ss, m2))
/-- A record's handle field, as the word L reads. -/
theorem hd?_rdW {k : IdxKind} {a : Array Word} {i : Nat} {x : Idx k} (h : hd? a i = some x)
    (hi : i < 2 ^ 64) : ∃ w, rdW a (UInt64.ofNat i) = w ∧ w.toNat < 2 ^ 32 ∧ decI w = x := by
  simp only [hd?] at h
  cases hw : a[i]? with
  | none => simp [hw] at h
  | some w =>
    simp only [hw] at h
    by_cases hl : w.toNat < 2 ^ 32
    · simp [hl] at h
      have hiw : (UInt64.ofNat i).toNat = i := by simp; omega
      exact ⟨w, by simp [rdW, hiw, hw], hl, h⟩
    · simp [hl] at h

/-! ## `check_sum_tele` -/

theorem getSort_of_get (t : ETables) (i : EIdx) (u : LIdx) (ht : i.tag = ETag.sort)
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

theorem viewSort_of_view (st : EStore) (i : EIdx) (u : LIdx) (ht : i.tag = ETag.sort)
    (h : st.view i = some (.sort u)) : st.viewSort i = some u := by
  unfold EStore.view at h; unfold EStore.viewSort EStore.persGetSort
  split at h
  · rw [ite_eq_left (by assumption)]; exact getSort_of_get _ _ _ ht h
  · rw [ite_eq_right (by assumption)]
    split at h
    · rw [ite_eq_left (by assumption)]; exact getSort_of_get _ _ _ ht h
    · cases h

theorem eViewW_head2 (m : Mem) (h : Word) (hg : h >>> 28 = 2) (hne : eViewW m h ≠ []) :
    (eViewW m h).headD 0 = 2 := by
  revert hne; unfold eViewW
  simp only [hg, show ((2 : Word) = 0) = False from by decide, show ((2 : Word) = 1) = False from by decide,
    ite_false, ite_true]
  repeat' split
  all_goals simp

theorem viewSort_run {a : AState} {h : EIdx} {u : Option LIdx} (hv : a.store.viewSort h = u) :
    (viewSort h).run a = .ok (u, a) := by
  simp [viewSort, hv, StateT.run_get]; rfl

/-- After the slow arm. -/
def ctK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0, r.tail.headD 0], m2)
/-- After `strip_pis`: the syntactic sort, or the slow arm. -/
def ctK1 (cR : CallM) (k : Nat) (vis cv n cvTa0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 1 ∧ r1.tail.tail.tail.headD 0 >>> 28 = 2 then
      if eViewW m1 (r1.tail.tail.tail.headD 0) = [] then none
      else some ([cvTa0, (eViewW m1 (r1.tail.tail.tail.headD 0)).tail.headD 0], m1)
    else ctK2 (ctsW cR k m1 vis cv n cvTa0)
/-- **The model of `check_sum_tele`.** -/
def ctW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, vis, cv, n, cvTa0 =>
    ctK1 cR k vis cv n cvTa0 (stripF 6 m [n, rdW (m.arr64 EREC) (cvTa0 + 3)])

section arms
variable (cR : CallM) (k : Nat) (m m1 m2 : Mem) (vis cv n cvTa0 : Word) (r r1 : List Word)
theorem ctW_succ : ctW cR (k + 1) m vis cv n cvTa0 =
    ctK1 cR k vis cv n cvTa0 (stripF 6 m [n, rdW (m.arr64 EREC) (cvTa0 + 3)]) := rfl
theorem ctK1_fast (h : r1.headD 0 = 1 ∧ r1.tail.tail.tail.headD 0 >>> 28 = 2)
    (hne : eViewW m1 (r1.tail.tail.tail.headD 0) ≠ []) : ctK1 cR k vis cv n cvTa0 (some (r1, m1)) =
      some ([cvTa0, (eViewW m1 (r1.tail.tail.tail.headD 0)).tail.headD 0], m1) := by
  simp only [ctK1, ite_eq_left h, ite_eq_right hne]
theorem ctK1_fast0 (h : r1.headD 0 = 1 ∧ r1.tail.tail.tail.headD 0 >>> 28 = 2)
    (hne : eViewW m1 (r1.tail.tail.tail.headD 0) = []) : ctK1 cR k vis cv n cvTa0 (some (r1, m1)) = none := by
  simp only [ctK1, ite_eq_left h, ite_eq_left hne]
theorem ctK1_slow (h : ¬ (r1.headD 0 = 1 ∧ r1.tail.tail.tail.headD 0 >>> 28 = 2)) :
    ctK1 cR k vis cv n cvTa0 (some (r1, m1)) = ctK2 (ctsW cR k m1 vis cv n cvTa0) := by
  simp only [ctK1, ite_eq_right h]
theorem ctK2_some : ctK2 (some (r, m2)) = some ([r.headD 0, r.tail.headD 0], m2) := rfl
end arms

grind_pattern [ind_grind] ctW_succ => ctW cR (k + 1) m vis cv n cvTa0
grind_pattern [ind_grind] ctK1_fast => ctK1 cR k vis cv n cvTa0 (some (r1, m1))
grind_pattern [ind_grind] ctK1_fast0 => ctK1 cR k vis cv n cvTa0 (some (r1, m1))
grind_pattern [ind_grind] ctK1_slow => ctK1 cR k vis cv n cvTa0 (some (r1, m1))
grind_pattern [ind_grind] ctK2_some => ctK2 (some (r, m2))

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hv : p.lookup "e_view" = some eView)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hwt : p.lookup "whnf_telescope" = some whnfTelescopeL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "forall_find" = some forallFind)
  (hpp : p.lookup "forall_push" = some forallPush) (hpi : p.lookup "intern_forall" = some internForallL)
  (hmk : p.lookup "mk_forall" = some mkForall)
  (hct : p.lookup "close_telescope" = some closeTelescope)
  (hea : p.lookup "erec_alloc" = some erecAlloc) (hcn : p.lookup "cv_new" = some cvNew)
  (hsl : p.lookup "check_sum_tele_slow" = some checkSumTeleSlowL)
  (hp : p.lookup "check_sum_tele" = some checkSumTeleL) (hst : StripProg p) (hi1 : I1Prog p) (hab : AbF p)
include ha hc hsc hv hff hfp hif hwt hsf hsp his hd hpf hpp hpi hmk hct hea hcn hsl hp hst hi1 hab

theorem ctW_spec (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St) (vis cv n cvTa0 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "check_sum_tele" [vis, cv, n, cvTa0]
    ⦃fun r s' => LocEq s' s₀ ∧ ctW cR k s₀.mem vis cv n cvTa0 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkSumTeleL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stripPis_specF p hst k, eView_spec p hv k,
        ctsW_spec p ha hc hsc hv hff hfp hif hwt hsf hsp his hd hpf hpp hpi hmk hct hea hcn hsl hi1 hab cR hcR k] <;>
      finish (gen := 20)

end spec

theorem tag_sort_iff (b : Word) (hb : b.toNat < 2 ^ 32) :
    (decE b).tag = ETag.sort ↔ b >>> 28 = 2 := by
  rw [decE_tag b hb]
  have hlt : (b >>> 28).toNat < 16 := by
    rw [UInt64.toNat_shiftRight]; simp; omega
  constructor
  · intro h
    apply UInt64.toNat_inj.mp
    have := congrArg UInt32.toNat h
    simp [ETag.sort] at this
    simp only [UInt64.toNat_shiftRight] at hlt ⊢
    simp; omega
  · intro h; rw [h]; rfl

end L.Ind

end
