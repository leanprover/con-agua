import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclRec

/-!
# `ci_to_cv` in L (lane `decls3`, helper `decls3-canon`)

Word model (continuations, as `ihW`), `vcgen` spec, and the relational lemma against
`IConstantInfo.toConstantVal`: a record of kind `≤ 5` answers its inline constant value (`p + 1`);
a projection table interns `Sort 1` (`intern_zero`, `intern_succ`, `intern_sort`) and allocates a
fresh constant value (`cv_new`) with the table's name and level parameters.
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- After `cv_new`. -/
def ctcK4 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m) => some ([q], m)

/-- After `intern_sort`. -/
def ctcK3 (p : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (t, m3) =>
    if 4294967296 ≤ t then none
    else ctcK4 (cvNewW m3 (rdW (m3.arr64 EREC) (p + 1)) (rdW (m3.arr64 EREC) (p + 3))
      (rdW (m3.arr64 EREC) (p + 4)) t)

/-- After `intern_succ`. -/
def ctcK2 (p : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (o, m2) => if 4294967296 ≤ o then none else ctcK3 p (sointernW m2 o)

/-- After `intern_zero`. -/
def ctcK1 (p : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (z, m1) => if 4294967296 ≤ z then none else ctcK2 p (sinternW m1 z)

/-- **The model of `ci_to_cv`.** -/
def ctcW (m : Mem) (p : Word) : Option (List Word × Mem) :=
  if rdW (m.arr64 EREC) p ≤ 5 then some ([p + 1], m)
  else if rdW (m.arr64 EREC) p ≠ 6 then none
  else ctcK1 p (zinternW m)

section arms
variable (m m1 m2 m3 : Mem) (p z o t : Word)
theorem ctcW_def : ctcW m p = (if rdW (m.arr64 EREC) p ≤ 5 then some ([p + 1], m)
    else if rdW (m.arr64 EREC) p ≠ 6 then none else ctcK1 p (zinternW m)) := rfl
theorem ctcK1_some : ctcK1 p (some (z, m1)) =
    (if 4294967296 ≤ z then none else ctcK2 p (sinternW m1 z)) := rfl
theorem ctcK2_some : ctcK2 p (some (o, m2)) =
    (if 4294967296 ≤ o then none else ctcK3 p (sointernW m2 o)) := rfl
theorem ctcK3_some : ctcK3 p (some (t, m3)) =
    (if 4294967296 ≤ t then none
    else ctcK4 (cvNewW m3 (rdW (m3.arr64 EREC) (p + 1)) (rdW (m3.arr64 EREC) (p + 3))
      (rdW (m3.arr64 EREC) (p + 4)) t)) := rfl
theorem ctcK4_some (q : Word) : ctcK4 (some (q, m)) = some ([q], m) := rfl
end arms

grind_pattern [ind_grind] ctcW_def => ctcW m p
grind_pattern [ind_grind] ctcK1_some => ctcK1 p (some (z, m1))
grind_pattern [ind_grind] ctcK2_some => ctcK2 p (some (o, m2))
grind_pattern [ind_grind] ctcK3_some => ctcK3 p (some (t, m3))
grind_pattern [ind_grind] ctcK4_some => ctcK4 (some (q, m))

section specs
variable (p : Prog) (hp : CanonProg p)
include hp

theorem ciToCv_spec' (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ci_to_cv" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ ctcW s₀.mem x = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "ci_to_cv")]
  simp only [callFn, ciToCv]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        internZero_spec p (hp.get "zero_find") (hp.get "zero_push") (hp.get "intern_zero") n,
        internSucc_spec p (hp.get "succ_find") (hp.get "succ_push") (hp.get "intern_succ") n,
        internSort_spec p (hp.get "sort_find") (hp.get "sort_push") (hp.get "intern_sort") n,
        cvNew_specW p (hp.get "erec_alloc") (hp.get "cv_new") n] <;>
      finish (gen := 20) [rdW_eq]

end specs


/-! ## The relational lemma -/

theorem hslice_agree {kk : IdxKind} {a b : Array Word} {t : Nat} (h : ∀ i < t, b[i]? = a[i]?)
    {o c : Nat} (hc : o + c ≤ t) : (hslice? b o c : Option (List (Idx kk))) = hslice? a o c := by
  simp only [hslice?]
  exact mapM_congr_of _ _ _ fun j hj => by
    simp only [List.mem_range] at hj
    simp only [hd?, h (o + j) (by omega)]

/-- **A fresh constant value** `⟨nm, lps, ty⟩` written at `q‥q+3` decodes to itself. -/
theorem decCV_new {a a' : Array Word} {N q : Nat} {nm lo ll ty : Word} {lps : List NIdx}
    (hnm : nm.toNat < 2 ^ 32) (hty : ty.toNat < 2 ^ 32) (h0 : a'[q]? = some nm)
    (h1 : a'[q + 1]? = some lo) (h2 : a'[q + 2]? = some ll) (h3 : a'[q + 3]? = some ty)
    (hs : hslice? a lo.toNat ll.toNat = some lps) (hlow : ∀ i < N, a'[i]? = a[i]?)
    (hb : ll.toNat = 0 ∨ lo.toNat + ll.toNat ≤ N) :
    decCV a' q = some ⟨decI nm, lps, decI ty⟩ := by
  have hsl : hslice? a' lo.toNat ll.toNat = some lps := by
    rcases hb with h | h
    · rw [h] at hs ⊢; simpa [hslice?] using hs
    · rw [hslice_agree hlow h]; exact hs
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
  refine ⟨decI nm, ?_, lps, ?_, decI ty, ?_, rfl⟩
  · simp [hd?, h0, hnm]
  · simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff]
    exact ⟨lo.toNat, ⟨lo, h1, rfl⟩, ll.toNat, ⟨ll, h2, rfl⟩, hsl⟩
  · simp [hd?, h3, hty]


theorem erecP_rd {m : Mem} {j : Nat} {w : Word} (h : (erecP m)[j]? = some w) :
    (m.arr64 EREC)[j]? = some w := by
  rw [← erecP_getE (erecP_lt h)]; exact h

theorem ctcW_small {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    (hS : StageR dn vis fe m a) {x : Word} {ci : IConstantInfo}
    (hci : decCI (erecP m) dn x.toNat = some ci) (h5 : rdW (m.arr64 EREC) x ≤ 5) :
    ∃ cv, decCV (erecP m) (x + 1).toNat = some cv ∧ ci.toConstantVal.run a = .ok (cv, a) := by
  obtain ⟨wk, e, hk⟩ := ciD hci
  have hrd : rdW (m.arr64 EREC) x = wk := rdW_zero' (erecP_rd e)
  rw [hrd] at h5
  have h5' : wk.toNat ≤ 5 := UInt64.le_iff_toNat_le.mp h5
  have hsz : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  have hsz' : (erecP m).size < 2 ^ 64 := Nat.lt_of_le_of_lt (by simp [erecP]; exact Nat.min_le_right _ _) hsz
  have step : ∀ {cv : IConstantVal}, decCV (erecP m) (x.toNat + 1) = some cv →
      decCV (erecP m) (x + 1).toNat = some cv := by
    intro cv hcv
    obtain ⟨w, hw, -⟩ := decCV_name hcv
    have := toNat_add_of_get hsz' (k := 1) (kn := 1) rfl hw
    rw [this]; exact hcv
  rcases hk with ⟨k0, cv, hcv, rfl⟩ | ⟨k0, cv, v, hi, hcv, hv, hhi, rfl⟩ | ⟨k0, cv, hcv, rfl⟩ |
      ⟨k0, cv, caps, hcv, hcaps, rfl⟩ | ⟨k0, cv, np, nf, hcv, hnp, hnf, rfl⟩ |
      ⟨k0, cv, mi, rp, o, c, rules, hcv, hmi, hrp, ho, hc, hr, rfl⟩ | ⟨k0, tbl, ht, rfl⟩
  · exact ⟨cv, step hcv, by simp [IConstantInfo.toConstantVal]; rfl⟩
  · exact ⟨cv, step hcv, by simp [IConstantInfo.toConstantVal]; rfl⟩
  · exact ⟨cv, step hcv, by simp [IConstantInfo.toConstantVal]; rfl⟩
  · exact ⟨cv, step hcv, by simp [IConstantInfo.toConstantVal]; rfl⟩
  · exact ⟨cv, step hcv, by simp [IConstantInfo.toConstantVal]; rfl⟩
  · exact ⟨cv, step hcv, by simp [IConstantInfo.toConstantVal]; rfl⟩
  · omega


/-- A word of a record below the old top reads the same after the pool grew. -/
theorem cnRdW_grow {m m3 : Mem} (hg : IWGrow m m3) (hsz3 : (m3.arr64 EREC).size < 2 ^ 64) {x k : Word}
    {kn : Nat} {w : Word} (hk : k.toNat = kn) (h : (erecP m)[x.toNat + kn]? = some w) :
    rdW (m3.arr64 EREC) (x + k) = w := by
  have hlt := erecP_lt h
  have h' : (m3.arr64 EREC)[x.toNat + kn]? = some w := by
    rw [hg.2.2.2 _ hlt]; exact erecP_rd h
  exact rdW_off hsz3 (by rw [hk]; exact h')

theorem ctcW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} (hS : StageR dn vis fe m a) {x : Word} {r : List Word} {ci : IConstantInfo}
    (h : ctcW m x = some (r, m')) (hci : decCI (erecP m) dn x.toNat = some ci) :
    ∃ cv a', ci.toConstantVal.run a = .ok (cv, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      decCV (erecP m') (r.headD 0).toNat = some cv := by
  rw [ctcW_def] at h
  by_cases h5 : rdW (m.arr64 EREC) x ≤ 5
  · rw [if_pos h5] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨cv, hd, hrun⟩ := ctcW_small hS hci h5
    exact ⟨cv, a, hrun, hS, IWGrow.refl _, by simpa using hd⟩
  rw [if_neg h5] at h
  by_cases h6 : rdW (m.arr64 EREC) x ≠ 6
  · rw [if_pos h6] at h; simp at h
  rw [if_neg h6] at h
  have h6' : rdW (m.arr64 EREC) x = 6 := by simpa using h6
  obtain ⟨wk, e, hk⟩ := ciD hci
  have hrd : rdW (m.arr64 EREC) x = wk := rdW_zero' (erecP_rd e)
  have hwk : wk.toNat = 6 := by rw [← hrd, h6']; rfl
  rcases hk with ⟨k0, _⟩ | ⟨k0, _⟩ | ⟨k0, _⟩ | ⟨k0, _⟩ | ⟨k0, _⟩ | ⟨k0, _⟩ | ⟨-, tbl, ht, rfl⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  simp only [decTbl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at ht
  obtain ⟨n1, h1, n2, h2, l3, h3, n5, h5', c6, h6', n7, h7, s8, h8, b9, h9, g11, h11, n13, h13, ex⟩ := ht
  have ex := Option.some.inj ex; subst ex
  obtain ⟨wn, hwn, hn32, rfl⟩ := hd?_some h1
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h3
  obtain ⟨o3, ho3, c3, hc3, hs3⟩ := h3
  obtain ⟨wo, hwo, rfl⟩ := natD ho3
  obtain ⟨wl, hwl, rfl⟩ := natD hc3
  have hbnd : wl.toNat = 0 ∨ wo.toNat + wl.toNat ≤ erTop m := by
    rcases Nat.eq_zero_or_pos wl.toNat with h0 | h0
    · exact .inl h0
    · right
      have := hslice?_bound (erecP m) _ _ _ hs3 h0
      have h2 : (erecP m).size ≤ erTop m := by
        simp [erecP]; exact Nat.min_le_left _ _
      omega
  -- the three internings
  cases hz : zinternW m with
  | none => rw [hz] at h; simp [ctcK1] at h
  | some zm =>
  obtain ⟨z, m1⟩ := zm
  rw [hz, ctcK1_some] at h
  by_cases hz32 : 4294967296 ≤ z
  · rw [if_pos hz32] at h; simp at h
  rw [if_neg hz32] at h
  have hz' : z.toNat < 2 ^ 32 := by
    have : ¬ (4294967296 : Word).toNat ≤ z.toNat := fun e => hz32 (UInt64.le_iff_toNat_le.mpr e)
    simpa using this
  obtain ⟨a1, hr1, hS1, hg1⟩ := internZero_stage hS hz
  cases hs : sinternW m1 z with
  | none => rw [hs] at h; simp [ctcK2] at h
  | some om =>
  obtain ⟨o, m2⟩ := om
  rw [hs, ctcK2_some] at h
  by_cases ho32 : 4294967296 ≤ o
  · rw [if_pos ho32] at h; simp at h
  rw [if_neg ho32] at h
  have ho' : o.toNat < 2 ^ 32 := by
    have : ¬ (4294967296 : Word).toNat ≤ o.toNat := fun e => ho32 (UInt64.le_iff_toNat_le.mpr e)
    simpa using this
  obtain ⟨a2, hr2, hS2, hg2⟩ := internSucc_stage hS1 z hz' hs
  cases hso : sointernW m2 o with
  | none => rw [hso] at h; simp [ctcK3] at h
  | some tm =>
  obtain ⟨t, m3⟩ := tm
  rw [hso, ctcK3_some] at h
  by_cases ht32 : 4294967296 ≤ t
  · rw [if_pos ht32] at h; simp at h
  rw [if_neg ht32] at h
  have ht' : t.toNat < 2 ^ 32 := by
    have : ¬ (4294967296 : Word).toNat ≤ t.toNat := fun e => ht32 (UInt64.le_iff_toNat_le.mpr e)
    simpa using this
  obtain ⟨a3, hr3, hS3, hg3⟩ := internSort_stage hS2 o ho' hso
  have hg13 : IWGrow m m3 := hg1.trans (hg2.trans hg3)
  have hsz3 : (m3.arr64 EREC).size < 2 ^ 64 := hS3.2.2.2.2.1
  have rn := cnRdW_grow hg13 hsz3 (x := x) (k := 1) (kn := 1) rfl hwn
  have rlo := cnRdW_grow hg13 hsz3 (x := x) (k := 3) (kn := 3) rfl hwo
  have rll := cnRdW_grow hg13 hsz3 (x := x) (k := 4) (kn := 3 + 1) rfl hwl
  rw [rn, rlo, rll] at h
  simp only [ctcK4] at h
  rcases hcn : cvNewW m3 wn wo wl t with _ | ⟨q, m4⟩ <;> simp only [hcn, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  simp only [cvNewW] at hcn
  rcases hal : erAllocW m3 4 with _ | ⟨q1, m5⟩ <;> simp only [hal, reduceCtorEq] at hcn
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hcn)
  rw [cvNewMem_eq]
  obtain ⟨hS4, hg4, hq, htop, hget⟩ := erRec_stage hal hS3 [wn, wo, wl, t] (by simp)
  refine ⟨⟨decI wn, l3, decE t⟩, a3, ?_, hS4, hg13.trans hg4, ?_⟩
  · simp only [IConstantInfo.toConstantVal, StateT.run_bind, hr1, exc_ok_bind', hr2, hr3,
      StateT.run_pure]
    rfl
  · have hq' : q1.toNat = erTop m3 := hq
    have hge : erTop m ≤ erTop m3 := hg13.2.1
    have g := fun j (hj : j < 4) => hget j hj
    have htop' : erTop (wrER m5 q1 [wn, wo, wl, t]) = erTop m3 + 4 := by simpa using htop
    have hsz4 : ∀ j, j < 4 → q1.toNat + j < erTop (wrER m5 q1 [wn, wo, wl, t]) := by
      intro j hj; rw [htop']; omega
    have eA : ∀ j (hj : j < 4), (erecP (wrER m5 q1 [wn, wo, wl, t]))[q1.toNat + j]? =
        [wn, wo, wl, t][j]? := by
      intro j hj
      rw [erecP_getE (hsz4 j hj)]; exact g j hj
    have hlow : ∀ i < erTop m, (erecP (wrER m5 q1 [wn, wo, wl, t]))[i]? =
        (erecP m)[i]? := by
      intro i hi
      have h1 : i < erTop (wrER m5 q1 [wn, wo, wl, t]) := by rw [htop']; omega
      rw [erecP_getE h1, erecP_getE hi]
      exact (hg13.trans hg4).2.2.2 i hi
    have hs' : hslice? (erecP m) wo.toNat wl.toNat = some l3 := hs3
    have := decCV_new (a := erecP m) (a' := erecP (wrER m5 q1 [wn, wo, wl, t]))
      (N := erTop m) (q := q1.toNat) (nm := wn) (lo := wo) (ll := wl) (ty := t) (lps := l3)
      hn32 ht' (by simpa [hq'] using eA 0 (by decide)) (by simpa [hq'] using eA 1 (by decide))
      (by simpa [hq'] using eA 2 (by decide)) (by simpa [hq'] using eA 3 (by decide)) hs' hlow hbnd
    simpa [decE_eq] using this


section refs
variable (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
include hp

/-- **`ci_to_cv` refines `IConstantInfo.toConstantVal`**: the result decodes in `erecP` of the
memory after (records below the pool's top). -/
@[refines ConRon.Arena.IConstantInfo.toConstantVal]
theorem ciToCv_refines (q : Word) (ci : IConstantInfo) :
    RefAM p "ci_to_cv" [q]
      (fun m a => StageR dn vis fe m a ∧ decCI (erecP m) dn q.toNat = some ci)
      ci.toConstantVal
      (KeepPost dn vis fe (fun m r (cv : IConstantVal) => decCV (erecP m) (r.headD 0).toNat = some cv)) := by
  intro n s₀ a₀ ⟨hS, hci⟩
  refine triple_post (ciToCv_spec' p hp n s₀ q) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨cv, a', hrun, hS', hg, hd⟩ := ctcW_ok hS hm hci
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hd⟩

end refs

end L.Ind
