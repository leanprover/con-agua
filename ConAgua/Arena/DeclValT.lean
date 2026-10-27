import ConAgua.Arena.DeclValRef
import ConAgua.Arena.DeclCvgT
import ConAgua.Arena.IndT.WalkC
import ConAgua.Arena.IndT.Base
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.DeclValSpec

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
    MemFrame [132, 133, 134, ECON, 140, 141, 142] [128] m m' := by
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
  have hrow : rowArr (rdW (m.arr64 EREC) (q + 1)) ∈ [132, 133, 134, ECON, 140, 141, 142] := by
    have htr : rowTier (rdW (m.arr64 EREC) (q + 1)) < 2 := Nat.mod_lt _ (by decide)
    rcases (by omega : rowTag (rdW (m.arr64 EREC) (q + 1)) = 0 ∨ rowTag (rdW (m.arr64 EREC) (q + 1)) = 1 ∨
      rowTag (rdW (m.arr64 EREC) (q + 1)) = 2) with h1 | h1 | h1 <;>
    rcases (by omega : rowTier (rdW (m.arr64 EREC) (q + 1)) = 0 ∨
      rowTier (rdW (m.arr64 EREC) (q + 1)) = 1) with h2 | h2 <;>
    simp [rowArr, h1, h2]
  have hf1 : MemFrame [132, 133, 134, ECON, 140, 141, 142] [128] m (rowSet m (rdW (m.arr64 EREC) (q + 1)) (vis + 1) q) := by
    unfold rowSet
    exact ((MemFrame.set64 m _ (by simp only [rowArr, CTL, ArrId]; omega) _ _).mono
      (by intro b hb; simp at hb; subst hb; exact hrow) (by simp)).trans
      ((MemFrame.set64 _ _ (by simp only [rowArr, CTL, ArrId]; omega) _ _).mono
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
  -- the four walks, as in `ivgW_ok`
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

/-- **`check_constant_val` under `StageT`** (`ccvW_ok`'s). -/
theorem ccvW_okT {p : Prog} (hq : KnotStageProg p) (hApd : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {q : Word} {r : List Word}
    {cv : IConstantVal}
    (h : ccvW (realCall p) n m vis q = some (r, m')) (hS : StageT dn vis fe m a)
    (hqd : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    ∃ a', (checkConstantVal V fe cv).run a = .ok ((), a') ∧ StageT dn vis fe m' a' ∧
      IWGrow m m' ∧ L.Stubs.CrOK m' := by
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hqd
  have et : rdW (m.arr64 EREC) (q + 3) = wt :=
    rdW_of_get? (k := q.toNat + 3) (toNat_add_small q 3 hqb).symm (erecP_get hwt)
  cases n with
  | zero => simp [ccvW] at h
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [ccvW_step, et] at h
  cases h1 : ihW (realCall p) n m vis q with
  | none => rw [h1] at h; simp [ccvK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, ccvK1_some] at h
  obtain ⟨a1, hrun1, hS1, hg1, hCr1, -⟩ := ihW_okT hApd hkp.crf h1 hS hqd hqb hlps hCr
  cases h2 : realCall p n "infer_type_core" [vis, 0, wt] m1 with
  | none => rw [h2] at h; simp [ccvK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, ccvK2_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ := hq.inferTypeCore_sim n hn' hS1 0 wt hwtl r2 m2 h2
  have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
  cases h3 : realCall p n "ensure_sort_core" [vis, 0, r2.headD 0] m2 with
  | none => rw [h3] at h; simp [ccvK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, ccvK3_some] at h
  obtain ⟨x3, a3, hrun3, hS3, hg3, -⟩ := hq.ensureSortCore_sim n hn' hS2 0 (r2.headD 0) hx2l r3 m3 h3
  have hCr3 := hkp.call (im_mem _ rfl) h3 hCr2
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have h00 : (0 : Word).toNat = 0 := rfl
  rw [h00, ← hty] at hrun2
  rw [h00, hx2] at hrun3
  refine ⟨a3, ?_, hS3, hg1.trans (hg2.trans hg3), hCr3⟩
  rw [checkConstantVal_eq]
  simp only [StateT.run_bind, hrun1, exc_ok_bind', hrun2, hrun3, StateT.run_pure]
  rfl

/-- `ccvW_okT`'s walk memos: `AbsOK` across `check_constant_val` (`ihW`'s frame, the core calls'
`absOK_core`). -/
theorem ccvW_okTA {p : Prog} (hq : KnotStageProg p) (hApd : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {q : Word} {r : List Word}
    {cv : IConstantVal}
    (h : ccvW (realCall p) n m vis q = some (r, m')) (hS : StageT dn vis fe m a)
    (hqd : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m)
    (hA : AbsOK m) : AbsOK m' := by
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hqd
  have et : rdW (m.arr64 EREC) (q + 3) = wt :=
    rdW_of_get? (k := q.toNat + 3) (toNat_add_small q 3 hqb).symm (erecP_get hwt)
  cases n with
  | zero => simp [ccvW] at h
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [ccvW_step, et] at h
  cases h1 : ihW (realCall p) n m vis q with
  | none => rw [h1] at h; simp [ccvK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, ccvK1_some] at h
  obtain ⟨a1, hrun1, hS1, hg1, hCr1, hf1⟩ := ihW_okT hApd hkp.crf h1 hS hqd hqb hlps hCr
  cases h2 : realCall p n "infer_type_core" [vis, 0, wt] m1 with
  | none => rw [h2] at h; simp [ccvK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, ccvK2_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ := hq.inferTypeCore_sim n hn' hS1 0 wt hwtl r2 m2 h2
  have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
  have hA2 := absOK_core hq.closed (by decide) h2 (hf1 hA) hS2
  cases h3 : realCall p n "ensure_sort_core" [vis, 0, r2.headD 0] m2 with
  | none => rw [h3] at h; simp [ccvK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, ccvK3_some] at h
  obtain ⟨x3, a3, hrun3, hS3, hg3, -⟩ := hq.ensureSortCore_sim n hn' hS2 0 (r2.headD 0) hx2l r3 m3 h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact absOK_core hq.closed (by decide) h3 hA2 hS3

/-- **`lvl_eq_fueled` under `StageT`**: `lvl_eq_c` through `lvlEqC_simT`; an answer other than
`0` is the twin's `some true` (the callers abort on `0`). -/
theorem lfW_okT {p : Prog} (hq : KnotStageProg p) (hL : LvlCacheProg p)
    (hpc : p.lookup "lvl_eq_c" = some lvlEqCL) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {n : Nat} {m m' : Mem} {a : AState} {u v : Word} {r : List Word}
    (h : lfW (realCall p) n m u v = some (r, m')) (hS : StageT dn vis fe m a) (hu : H u) (hv : H v)
    (lu lv : ConLeche.Level) (hdu : denoteL a.store.ls (decI u) = some lu)
    (hdv : denoteL a.store.ls (decI v) = some lv) :
    ∃ x a', (lvlEq? (decI u) (decI v)).run a = .ok (x, a') ∧ StageT dn vis fe m' a' ∧
      IWGrow m m' ∧ (r.headD 0 ≠ 0 → x = some true) := by
  cases n with
  | zero => simp [lfW] at h
  | succ n =>
  simp only [lfW] at h
  cases hs : realCall p n "lvl_eq_c" [u, v] m with
  | none => simp [hs] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  simp only [hs] at h
  by_cases h0 : r1.headD 0 = 0
  · rw [ite_eq_left h0] at h; exact absurd h (by simp)
  rw [ite_eq_right h0] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨x, a1, hrun, hSt, hg, hdec, -⟩ :=
    lvlEqC_simT p hq.closed hL hpc n hS u v hu hv lu lv hdu hdv r1 m1 hs
  refine ⟨x, a1, hrun, hSt, hg, fun hne => ?_⟩
  have h2 : r1.headD 0 = 2 := Classical.byContradiction fun h2 => by
    simp only [List.headD_cons] at hne
    exact hne (ite_eq_right h2)
  rw [← hdec, h2]; rfl

/-- `lvl_eq_fueled`'s model keeps `consts_resolve_ffast`'s memo (its one call is a program call). -/
theorem lfW_crOK {p : Prog} (hkp : CrKeep p) {n : Nat} {m m' : Mem} {u v : Word} {r : List Word}
    (h : lfW (realCall p) n m u v = some (r, m')) (hCr : L.Stubs.CrOK m) : L.Stubs.CrOK m' := by
  cases n with
  | zero => simp [lfW] at h
  | succ n =>
  simp only [lfW] at h
  cases hs : realCall p n "lvl_eq_c" [u, v] m with
  | none => simp [hs] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  simp only [hs] at h
  split at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hkp.call (im_mem _ rfl) hs hCr

/-- **The value checks' common tail under `StageT`** (`dvK1_ok`'s): after the push, the stage
relation at the extended environment and the core's memos well formed. -/
theorem dvK1_okT {p : Prog} (hq : KnotStageProg p) (hRp : RecProg p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {n : Nat} (hn : n ≤ 2 ^ 62) {m1 m' : Mem} {c wv wt : Word} {r : List Word}
    {cv : IConstantVal} {ci : IConstantInfo} {a1 : AState} {r1 : List Word} (msg : String)
    (h : dvK1 p (realCall p) n vis c wv wt (some (r1, m1)) = some (r, m'))
    (hS1 : StageT dn vis fe m1 a1)
    (hci : decCI (erecP m1) dn c.toNat = some ci) (hcb : c.toNat + 5 < 2 ^ 64)
    (hwv : wv.toNat < 2 ^ 32) (hwt : wt.toNat < 2 ^ 32) (hty : cv.type = decI wt) :
    ∃ a', (do
        let vtype ← inferTypeCore V fe checkFuel 0 (decI wv)
        unless ← isDefEqCore V fe checkFuel 0 vtype cv.type do
          fail (.invalid msg)
        pure (fe.push ci) : AM IFEnv).run a1 = .ok (fe.push ci, a') ∧
      StageR dn (r.headD 0) (fe.push ci) m' a' ∧ CoreMemos m' ∧ IWGrow m1 m' := by
  rw [dvK1_some] at h
  cases h2 : realCall p n "infer_type_core" [vis, 0, wv] m1 with
  | none => rw [h2] at h; simp [dvK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, dvK2_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ := hq.inferTypeCore_sim n hn hS1 0 wv hwv r2 m2 h2
  cases h3 : realCall p n "is_def_eq_core" [vis, 0, r2.headD 0, wt] m2 with
  | none => rw [h3] at h; simp [dvK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, dvK3_some] at h
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ :=
    hq.isDefEqCore_sim n hn hS2 0 (r2.headD 0) wt hx2l hwt r3 m3 h3
  by_cases hb3 : r3.headD 0 = 0
  · rw [ite_eq_left hb3] at h; simp at h
  rw [ite_eq_right hb3] at h
  have ex3 : x3 = true := by rw [← hx3]; simpa [decBool] using hb3
  -- the push
  have hx13 : ArrExt (erecP m1) (erecP m3) := IWGrow.erecPExt (hg2.trans hg3)
  have hci3 := ArrExt.decCI hx13 hci
  obtain ⟨w, hw1, hwl, -⟩ := decCI_name hci3
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  have hw : (rdW (m3.arr64 EREC) (c + 1)).toNat < 2 ^ 32 := by
    rw [rdW_of_get? hc1.symm (erecP_get hw1)]; exact hwl
  cases h4 : callW p n "env_push" [vis, c] m3 with
  | none => rw [h4] at h; simp [dvK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, dvK4_some] at h
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (envPush_specW p hRp n ⟨m3, Locals.init []⟩ vis c hw) h4
  subst hs4
  obtain ⟨hS4, hg4⟩ := envPushW_ok hW4 hS3.stage hci3
  have hM4 : CoreMemos s4.mem := hS3.twin.memos.frame (envPushW_frame hW4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have h00 : (0 : Word).toNat = 0 := rfl
  rw [h00] at hrun2
  rw [h00, hx2, ← hty] at hrun3
  refine ⟨a3, ?_, by simpa using hS4, hM4, hg2.trans (hg3.trans hg4)⟩
  simp only [StateT.run_bind, hrun2, exc_ok_bind', hrun3, ex3, ite_true, StateT.run_pure]
  rfl

/-- **`check_defn_val`/`check_opaque_val` under `StageT`** (`dvW_ok`'s). -/
theorem dvW_okT {p : Prog} (hq : KnotStageProg p) (hRp : RecProg p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {c : Word} {r : List Word}
    {cv : IConstantVal} {v : EIdx} {ci : IConstantInfo} (msg : String)
    (h : dvW p (realCall p) n m vis c = some (r, m')) (hS : StageT dn vis fe m a)
    (hci : decCI (erecP m) dn c.toNat = some ci) (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) (hCr : L.Stubs.CrOK m) :
    ∃ a', (dvT fe cv v ci msg).run a = .ok (fe.push ci, a') ∧
      StageR dn (r.headD 0) (fe.push ci) m' a' ∧ CoreMemos m' ∧ IWGrow m m' := by
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hcb : c.toNat + 5 < 2 ^ 64 := erecP_bound hwv hS.stage.2
  have ev : rdW (m.arr64 EREC) (c + 5) = wv :=
    rdW_of_get? (toNat_add_small c 5 (by omega)).symm (erecP_get hwv)
  have et : rdW (m.arr64 EREC) (c + 4) = wt :=
    rdW_of_get? (toNat_add_small c 4 (by omega)).symm (erecP_get (by simpa [Nat.add_assoc] using hwt))
  cases n with
  | zero => simp [dvW] at h
  | succ n =>
  rw [dvW_step, ev, et] at h
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  cases h1 : ivgW (realCall p) n m vis (c + 1) wv with
  | none => rw [h1] at h; simp [dvK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1] at h
  obtain ⟨a1, hrun1, hS1, hg1, -⟩ :=
    ivgW_okT hap hkp h1 hS (by rw [hc1]; exact ArrExt.decCV (erecP_ext m) hcv) (by rw [hc1]; omega)
      hwvl hlps hCr
  obtain ⟨a', hrun', hS', hM', hg'⟩ := dvK1_okT hq hRp (by omega) msg h hS1
    (ArrExt.decCI (IWGrow.erecPExt hg1) hci) hcb hwvl hwtl hty
  refine ⟨a', ?_, hS', hM', hg1.trans hg'⟩
  simp only [dvT, StateT.run_bind, hrun1, exc_ok_bind']
  simpa only [StateT.run_bind] using hrun'

/-- **`check_thm_val` under `StageT`** (`tvW_ok`'s). -/
theorem tvW_okT {p : Prog} (hq : KnotStageProg p) (hRp : RecProg p) (hL : LvlCacheProg p)
    (hpc : p.lookup "lvl_eq_c" = some lvlEqCL) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {c : Word} {r : List Word}
    {cv : IConstantVal} {v : EIdx}
    (h : tvW p (realCall p) n m vis c = some (r, m')) (hS : StageT dn vis fe m a)
    (hci : decCI (erecP m) dn c.toNat = some (.thmInfo cv))
    (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v)
    (hpre : ∃ env cP, ConLeche.EnvWF env ∧ ConRon.Bridge.CheckOK V env fe a ∧
      Frontend.denoteCV a.store cv = some cP ∧ ConLeche.Expr.WScoped 0 cP.type)
    (hCr : L.Stubs.CrOK m) :
    ∃ a', (checkThmVal V fe cv v).run a = .ok (fe.push (.thmInfo cv), a') ∧
      StageR dn (r.headD 0) (fe.push (.thmInfo cv)) m' a' ∧ CoreMemos m' ∧ IWGrow m m' := by
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hcb : c.toNat + 5 < 2 ^ 64 := erecP_bound hwv hS.stage.2
  have ev : rdW (m.arr64 EREC) (c + 5) = wv :=
    rdW_of_get? (toNat_add_small c 5 (by omega)).symm (erecP_get hwv)
  have et : rdW (m.arr64 EREC) (c + 4) = wt :=
    rdW_of_get? (toNat_add_small c 4 (by omega)).symm (erecP_get (by simpa [Nat.add_assoc] using hwt))
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  have h00 : (0 : Word).toNat = 0 := rfl
  cases n with
  | zero => simp [tvW] at h
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [tvW_step, ev, et] at h
  -- the type's type and sort
  cases h1 : realCall p n "infer_type_core" [vis, 0, wt] m with
  | none => rw [h1] at h; simp [tvK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, tvK1_some] at h
  have hCr1 := hkp.call (im_mem _ rfl) h1 hCr
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1l, hx1⟩ := hq.inferTypeCore_sim n hn' hS 0 wt hwtl r1 m1 h1
  cases h2 : realCall p n "ensure_sort_core" [vis, 0, r1.headD 0] m1 with
  | none => rw [h2] at h; simp [tvK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, tvK2_some] at h
  have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    hq.ensureSortCore_sim n hn' hS1 0 (r1.headD 0) hx1l r2 m2 h2
  -- the zero level
  cases h3 : pinWordW m2 53 with
  | none => rw [h3] at h; simp [tvK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, tvK3_some] at h
  have hflag : pinW m2 0 ≠ 0 := hS2.flag
  simp only [pinWordW, hflag, ite_false, Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have hF := hS2.stage.1.pins.full hflag
  have hz : rdW (m2.arr64 PINS) 53 = pinW m2 53 := by simp [rdW, pinW]
  simp only [List.headD_cons, hz] at h
  -- the two levels read back
  obtain ⟨xs, hxs⟩ := ensureSort_view (r := pureFnsA V fe checkFuel) (fe := fe)
    (d := (0 : Word).toNat) (e := decI (r1.headD 0)) hrun2
  obtain ⟨lu, hdu⟩ := hS2.twin.den.sort _ _ hxs
  rw [← hx2] at hdu
  obtain ⟨lz, hdz⟩ := hS2.twin.den.zero
  rw [hF.zeroLevel] at hdz
  -- the comparison
  cases h4 : lfW (realCall p) n m2 (r2.headD 0) (pinW m2 53) with
  | none => rw [h4] at h; simp [tvK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, tvK4_some] at h
  have hCr4 := lfW_crOK hkp h4 hCr2
  obtain ⟨x4, a4, hrun4, hS4, hg4, hr4⟩ :=
    lfW_okT hq hL hpc h4 hS2 hx2l hF.lv_lt.2.1 lu lz hdu hdz
  -- the parameters' names read back at the guards: the prefix extends the store
  have hlps4 : ∃ ks, cv.levelParams.mapM (denoteN a4.store.ns) = some ks := by
    obtain ⟨env, cP, henv, hck, hcvd, hws⟩ := hpre
    have hr1 := hrun1
    rw [h00, ← hty] at hr1
    have hr2 := hrun2
    rw [hx1] at hr2
    obtain ⟨hck2, hx02⟩ := thmPrefix_ext henv hck hcvd hws hr1 hr2
    obtain ⟨-, hst4, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a2) rfl hrun4
      (ConRon.Bridge.Core.lvlEq?_spec a2 _ _ hck2)
    rw [hst4]
    exact denoteCV_lps (ConRon.Bridge.denoteCV_ext hcvd hx02)
  by_cases hb4 : r4.headD 0 = 0
  · rw [ite_eq_left hb4] at h; simp at h
  rw [ite_eq_right hb4] at h
  have ex4 := hr4 hb4
  -- the value's guards, then the common tail
  cases h5 : ivgW (realCall p) n m4 vis (c + 1) wv with
  | none => rw [h5] at h; simp [dvK1] at h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5] at h
  have hg14 := hg1.trans (hg2.trans hg4)
  obtain ⟨a5, hrun5, hS5, hg5, -⟩ :=
    ivgW_okT hap hkp h5 hS4 (by rw [hc1]; exact ArrExt.decCV (IWGrow.erecExt hg14) hcv)
      (by rw [hc1]; omega) hwvl hlps4 hCr4
  obtain ⟨a', hrun', hS', hM', hg'⟩ := dvK1_okT hq hRp hn' "type mismatch in theorem" h hS5
    (ArrExt.decCI (IWGrow.erecPExt (hg14.trans hg5)) hci) hcb hwvl hwtl hty
  refine ⟨a', ?_, hS', hM', hg14.trans (hg5.trans hg')⟩
  rw [h00, ← hty] at hrun1
  rw [h00, hx1] at hrun2
  rw [hx2, ex4] at hrun4
  rw [checkThmVal_eq]
  simp only [StateT.run_bind, hrun1, exc_ok_bind', hrun2, zeroLevel, pinZeroLevel_run hF, hrun4,
    liftFueled, StateT.run_pure, ite_true, pure_bind]
  simp only [dvT, StateT.run_bind, hrun5, exc_ok_bind']
  simpa only [StateT.run_bind] using hrun'

end L.Arena
