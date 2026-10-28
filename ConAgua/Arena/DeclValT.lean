import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.CrOKFrame
import ConAgua.Arena.DeclCvgT
import ConAgua.Arena.IndT.WalkC

/-!
# The value checks under `StageT` (lane `loopt2`)

`DeclValRef.lean`'s relational lemmas run the value checks' models from the stage relation, the
core's entry points read through their stubs. Here they read the program's own calls
(`realCall p`) and run from `StageT`, as `check_value_group` does (`DeclCvgT.lean`). The value
checks end with `env_push`, which changes the environment; after it the stage relation holds at
the extended environment and the core's memos are still well formed (`CoreMemos`: `env_push`
writes the index rows, `ECON` and `CTL[128]` only), which is what the loop carries to the next
declaration.
-/

open ConRon.Arena

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- **`env_push` writes the index rows, `ECON` and its count** (`CTL[128]`). -/
theorem envPushW_frame {m m' : Mem} {vis q : Word} {r : List Word}
    (h : envPushW m vis q = some (r, m')) :
    MemFrame [EIXA, EIXS, EIXN, ECON, EIXA1, EIXS1, EIXN1] [128] m m' := by
  simp only [envPushW] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  rotate_left
  · cases h
  rename_i hc
  obtain ⟨ht, -⟩ := hc
  have hrow : (rowArr (rdW (m.arr64 EREC) (q + 1)) : TieredArray) ∈
      ([EIXA, EIXS, EIXN, ECON, EIXA1, EIXS1, EIXN1] : List TieredArray) := by
    rcases rowArr_names (rdW (m.arr64 EREC) (q + 1)) with h | h | h | h | h | h <;> rw [h] <;> decide
  have hf1 : MemFrame [EIXA, EIXS, EIXN, ECON, EIXA1, EIXS1, EIXN1] [128] m
      (rowSet m (rdW (m.arr64 EREC) (q + 1)) (vis + 1) q) := by
    unfold rowSet
    exact ((MemFrame.set64 m _ (TieredArray.t0_ne (rowArr_ne _ (by decide))) _ _).mono
      (by intro b hb; simp at hb; subst hb; exact hrow) (by simp)).trans
      ((MemFrame.set64 _ _ (TieredArray.t0_ne (rowArr_ne _ (by decide))) _ _).mono
        (by intro b hb; simp at hb; subst hb; exact hrow) (by simp))
  simp only [envPushK] at h
  split at h
  · cases h
  split at h
  rotate_left
  · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact (hf1.trans ((MemFrame.set64 _ ECON (by decide) _ _).mono (by simp) (by simp))).trans
    ((MemFrame.setCtl _ 128 _).mono (by simp) (by simp))

/-- **`install_header` under `StageT`** (`ihW_ok`'s, lane `loopt2`): the copy by its frame
(`StageT.of_iw`), the closedness walks by their `StageT` refinements, the
two walks real (lane `indstaget`): `all_level_params_defined` by `apdF_okT` (the parameters' names
read back at the entry, the guards before it keeping the twin's store), `consts_resolve_ffast` by
`crfF_okT` (its memo `CrOK` carried across the guards by their frames). `AbsOK` is kept too
(`absOK_apdF`, `absOK_crfF`). -/
theorem ihW_okT {p : Prog} (hApd : ApdF p) (hCrf : CrfF p) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal}
    (h : ihW (realCall p) n m vis q = some (r, m')) (hS : StageT dn vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hlpsN : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    ∃ a', (installHeader fe cv).run a = .ok ((), a') ∧ StageT dn vis fe m' a' ∧
      IWGrow m m' ∧ L.Stubs.CrOK m' ∧ AFr m m' := by
  have hq0 : decCV (erA m) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt (IWGrow.refl m)) hq
  obtain ⟨wx, hwx, hwxl, hname⟩ := decCV_name hq0
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hq0
  have ex : rdW (m.arr64 EREC) q = wx := rdW_of_get? rfl hwx
  have et : rdW (m.arr64 EREC) (q + 3) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hwt
  cases n with
  | zero => simp [ihW] at h
  | succ n =>
  rw [ihW_step, ex, et] at h
  -- `env_find(x, vis)`
  cases h1 : envFindW m wx vis with
  | none => rw [h1] at h; simp [ihK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, ihK1_some] at h
  by_cases hb1 : r1.headD 0 ≠ 0
  · rw [ite_eq_left hb1] at h; simp at h
  rw [ite_eq_right hb1] at h
  obtain ⟨rfl, hfind⟩ := envFindW_miss h1 hS.stage.1.env hwxl (by simpa using hb1)
  -- `reserved_contains(x)`
  cases h2 : resContW n m1 wx with
  | none => rw [h2] at h; simp [ihK2] at h
  | some c =>
  rw [h2, ihK2_some] at h
  by_cases hb2 : c ≠ 0
  · rw [ite_eq_left hb2] at h; simp at h
  rw [ite_eq_right hb2] at h
  have hc0 : c = 0 := by simpa using hb2
  subst hc0
  obtain ⟨rl, hrunR, hrl⟩ := resContW_miss hwxl h2 hS.stage.1.pins
  -- `cv_lps(q)`
  have hq3 : decCV (erA m1) q.toNat = some cv := hq0
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hq3
  have e1 : rdW (m1.arr64 EREC) (q + 1) = w1 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw1
  have e2 : rdW (m1.arr64 EREC) (q + 2) = w2 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw2
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m1.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (L.Ind.hslice?_bound _ _ _ _ hsl h0)
  cases n with
  | zero => simp [cvLpsW, ihK4] at h
  | succ n =>
  rw [cvLpsW_step, e1, e2] at h
  cases h4 : erToIwW n m1 w1 w2 with
  | none => rw [h4] at h; simp [ihK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, ihK4_some] at h
  obtain ⟨-, hr4t, hdec4, hS4R, hg4, htop4⟩ := erToIwW_stage h4 hS.stage hsrc
  have hS4 := StageT.of_iw hS hS4R (erToIwW_frame h4 hS.stage hsrc)
  have hCr4 := CrOK.frame hCr (erToIwW_frame h4 hS.stage hsrc) (by decide) (by decide)
  have hA4 : AFr m1 m4 := erToIwW_afr h4
  rw [hr4t] at h
  have hdecL : decHL m4 (r4.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [hdec4]; exact hsl
  -- `sl_nodup(o, l)`
  cases h5 : nodupW (n + 1) m4 (r4.headD 0) w2 with
  | none => rw [h5] at h; simp [ihK5] at h
  | some d =>
  rw [h5, ihK5_some] at h
  by_cases hb5 : d = 0
  · rw [ite_eq_left hb5] at h; simp at h
  rw [ite_eq_right hb5] at h
  have htopb : iwTop m4 < 2 ^ 64 := by simp only [iwTop]; exact UInt64.toNat_lt _
  obtain ⟨ws, hws, hlps, hwsl⟩ := slR_of_decHL m4 _ _ _ hdecL (by omega)
  simp only [UInt64.ofNat_toNat] at hws
  have hd := nodupW_ok _ _ _ _ _ _ hws h5
  have hnd : nameNodup cv.levelParams = true := by
    rw [hlps, nameNodup_map ws hwsl]
    by_cases hn : ws.Nodup
    · simp [hn]
    · simp [hn] at hd; exact absurd hd hb5
  -- the four walks, as in `ivg_ref`
  cases h6 : lbbF m4 [4000000000, 0, wt] with
  | none => rw [h6] at h; simp [ihK6] at h
  | some rm6 =>
  obtain ⟨r6, m6⟩ := rm6
  rw [h6, ihK6_some] at h
  obtain ⟨x6, a6, hrun6, hS6, hg6, hx6, -⟩ :=
    lbbF_okT dn vis fe 4000000000 0 wt hwtl m4 m6 a r6 h6 hS4
  have hCr6 := CrOK.frame hCr4 (lbbF_frame h6) (by decide) (by decide)
  have hA6 : AFr m1 m6 := hA4.trans (AFr.of_frame (lbbF_frame h6))
  by_cases hb6 : r6.headD 0 = 0
  · rw [ite_eq_left hb6] at h; simp at h
  rw [ite_eq_right hb6] at h
  cases h7 : hffF m6 [4000000000, wt] with
  | none => rw [h7] at h; simp [ihK7] at h
  | some rm7 =>
  obtain ⟨r7, m7⟩ := rm7
  rw [h7, ihK7_some] at h
  obtain ⟨x7, a7, hrun7, hS7, hg7, hx7, -⟩ :=
    hffF_okT dn vis fe 4000000000 wt hwtl m6 m7 a6 r7 h7 hS6
  have hCr7 := CrOK.frame hCr6 (hffF_frame h7) (by decide) (by decide)
  have hA7 : AFr m1 m7 := hA6.trans (AFr.of_frame (hffF_frame h7))
  by_cases hb7 : r7.headD 0 ≠ 0
  · rw [ite_eq_left hb7] at h; simp at h
  rw [ite_eq_right hb7, hr4t] at h
  cases h8 : realCall p (n + 1) "all_level_params_defined" [r4.headD 0, w2, wt] m7 with
  | none => rw [h8] at h; simp [ihK8] at h
  | some rm8 =>
  obtain ⟨r8, m8⟩ := rm8
  rw [h8, ihK8_some] at h
  replace h8 := apdF_of_callW hApd h8
  have hdec7 : decHL m7 (r4.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [decHL_grow (hg6.trans hg7) (by omega), hdecL]
  have hst7 : a7.store = a.store := by
    rw [hffF_store hrun7, lbbF_store hrun6]
  obtain ⟨x8, a8, hrun8, hS8, hg8, hx8, -⟩ :=
    apdF_okT dn vis fe (r4.headD 0) w2 wt hwtl cv.levelParams m7 m8 a7 r8 h8
      ⟨hS7, hdec7, by rw [hst7]; exact hlpsN⟩
  have hCr8 := CrOK.frame hCr7 (apdF_frame h8) (by decide) (by decide)
  have hA8 : AFr m1 m8 := fun hA => absOK_apdF h8 (hA7 hA) hS8
  by_cases hb8 : r8.headD 0 = 0
  · rw [ite_eq_left hb8] at h; simp at h
  rw [ite_eq_right hb8] at h
  cases h9 : realCall p (n + 1) "consts_resolve_ffast" [vis, wt] m8 with
  | none => rw [h9] at h; simp [ihK9] at h
  | some rm9 =>
  obtain ⟨r9, m9⟩ := rm9
  rw [h9, ihK9_some] at h
  replace h9 := crfF_of_callW hCrf h9
  obtain ⟨x9, a9, hrun9, ⟨hS9, hg9, hx9, -⟩, hCr9⟩ :=
    crfF_okT dn vis fe wt hwtl m8 m9 a8 r9 h9 ⟨hS8, hCr8.crMemo⟩
  have hA9 : AFr m1 m9 := fun hA => absOK_crfF h9 (hA8 hA) hCr9 hS9
  by_cases hb9 : r9.headD 0 = 0
  · rw [ite_eq_left hb9] at h; simp at h
  rw [ite_eq_right hb9] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have ex6 : x6 = true := by rw [← hx6]; simpa using hb6
  have ex7 : x7 = false := by rw [← hx7]; simpa using hb7
  have ex8 : x8 = true := by rw [← hx8]; simpa using hb8
  have ex9 : x9 = true := by rw [← hx9]; simpa using hb9
  rw [fuelW] at hrun6 hrun7
  rw [show ((0 : Word).toNat) = 0 from rfl] at hrun6
  rw [← hname] at hfind hrl
  rw [← hty] at hrun6 hrun7 hrun8 hrun9
  refine ⟨a9, ?_, hS9, hg4.trans (hg6.trans (hg7.trans (hg8.trans hg9))), hCr9.crOK, hA9⟩
  simp only [installHeader, StateT.run_bind, hfind, Option.isSome_none, Bool.false_eq_true,
    ite_false, hrunR, exc_ok_bind', hrl, hnd, hrun6, ex6, hrun7, ex7, hrun8, ex8,
    hrun9, ex9, ite_true, StateT.run_pure]
  rfl

end L.Arena
