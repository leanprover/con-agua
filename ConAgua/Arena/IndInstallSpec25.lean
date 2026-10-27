import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.IndSumSpec.StructProjGuards

/-!
# Refinements of `IndInstall`, part 25 (lane `indproofs3`, helper `tail`): memo frames for
`checkBlockTables`

The table loop calls `struct_proj_guards` once per structure-like member, and each call needs the
`has_loose_bvar_b` memo well formed in the memory at hand (`spgW_ok`'s `hbMR`). It is carried
across the loop: `struct_proj_guards` leaves it well formed (`spgW_hb`); the projection table's
install writes outside the memo region (`tblW_okM`, part 26, from the frames below).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem binternW_mfr {m m' : Mem} {u r : Word} (h : binternW m u = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (binternW_frame m u r m' h) (by simp [BREC, BSLOT]) (by simp)
theorem minternW_mfr {m m' : Mem} {u v r : Word} (h : minternW m u v = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (minternW_frame m u v r m' h) (by simp [MREC, MSLOT, MHP]) (by simp)
theorem mkProjW_mfr {m m' : Mem} {a b c r : Word} (h : mkProjW m a b c = some (r, m')) : MFr [] [] m m' :=
  MFr.of_low (mkProjW_low h)
theorem erAllocW_mfr {m m' : Mem} {k q : Word} (h : erAllocW m k = some (q, m')) : MFr [] [] m m' := by
  rw [erAllocW_mem h]; exact MFr.of_frame (MemFrame.setCtl m 129 _) (by simp) (by simp)
theorem set64ER_mfr (m : Mem) (k v : Word) : MFr [] [] m (m.set64 EREC k v) :=
  MFr.of_frame (MemFrame.set64 m EREC (by decide) k v) (by simp [EREC]) (by simp)

/-! ## `struct_proj_guards` -/

theorem colW_mfr : ∀ (n : Nat) (m m' : Mem) (uo ul so sl z j k acc : Word) (r : List Word),
    colW n m uo ul so sl z j k acc = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, _, _, h => by simp [colW] at h
  | n + 1, m, m', uo, ul, so, sl, z, j, k, acc, r, h => by
    simp only [colW, colK.eq_def, colK2.eq_def] at h
    mfr_auto h [colW_mfr n _ _ _ _ _ _ _ _ _ _ _, minternW_mfr]

theorem rowW_mfr : ∀ (n : Nat) (m m' : Mem) (uo ul so sl z i k : Word) (r : List Word),
    rowW n m uo ul so sl z i k = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [rowW] at h
  | n + 1, m, m', uo, ul, so, sl, z, i, k, r, h => by
    simp only [rowW, rowK1.eq_def, rowK2.eq_def, plK0.eq_def, plK3.eq_def] at h
    mfr_auto h [rowW_mfr n _ _ _ _ _ _ _ _ _ _, colW_mfr n _ _ _ _ _ _ _ _ _ _ _, allocW_mfr, consW_mfr]

end L.Ind

namespace L.Ind
open L.Arena

/-- **`struct_proj_guards` leaves the `hb` memo well formed** (its walk's memo after the clear). -/
theorem spgW_hb {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) {m m' : Mem}
    {a : AState} {cty nP nF so sl : Word} {r : List Word} {mp : Std.HashMap (EIdx × Nat) Bool}
    (hc' : H cty) (hb : nP.toNat + nF.toNat + 1 < 2 ^ 64)
    (hS : StageR dn vis fe m a) (hM : hbMR m mp) (h : spgW n m cty nP nF so sl = some (r, m')) :
    ∃ mp', hbMR m' mp' := by
  unfold spgW at h
  cases hz' : pinWordV m 53 with
  | none => rw [hz'] at h; simp [spgK1] at h
  | some z =>
  rw [hz'] at h
  by_cases h0 : rdW (m.arr64 CTL) hbSch.cs + 2 = 0
  · rw [spgK1_some_zero n m cty nP nF so sl z h0] at h; cases h
  rw [spgK1_some n m cty nP nF so sl z h0] at h
  have hf0 := mclearG_frame hbSch m
  have hM0 := memoRV_clear hbSch hbSch_wf lfKey hbVR m mp hM h0
  obtain ⟨hS0, -⟩ := StageR.frame_hi hS hf0 (by simp) (by
      intro x hx; simp [hbSch] at hx; rcases hx with rfl | rfl <;> decide) (by simp) (by simp [hbSch])
  obtain ⟨⟨u, m2⟩, hu, h⟩ := of_K h rfl; rw [spgK2_some] at h
  obtain ⟨-, mp', -, -, -, -, -, hM2, -, -⟩ :=
    ulW_ok n _ _ a cty nP nF 0 u ∅ (by simpa using hb) hc' hS0 hM0 hu
  obtain ⟨⟨rr, m3⟩, hr, h⟩ := of_K h rfl; rw [spgK3_some] at h
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨mp', hbMR_mfr (rowW_mfr _ _ _ _ _ _ _ _ _ _ _ hr) (by simp) (by simp) hM2⟩

/-! ## `check_struct_proj_table` -/

theorem lpsW_mfrT {n : Nat} {m m' : Mem} {q : Word} {r : List Word} (h : lpsW n m q = some (r, m')) :
    MFr [] [] m m' := by
  cases n with
  | zero => simp [lpsW] at h
  | succ n =>
    simp only [lpsW] at h
    mfr_auto h [erToIwW_mfr]

theorem psGoW_mfr : ∀ (n : Nat) (m m' : Mem) (o nP N k : Word) (r : List Word),
    psGoW n m o nP N k = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, h => by simp [psGoW] at h
  | n + 1, m, m', o, nP, N, k, r, h => by
    simp only [psGoW, psK0.eq_def, psK1.eq_def, psK2.eq_def, psK3.eq_def] at h
    mfr_auto h [psGoW_mfr n _ _ _ _ _ _ _, binternW_mfr, allocW_mfr, consW_mfr]

theorem projPsW_mfr {n : Nat} {m m' : Mem} {nP : Word} {r : List Word} (h : projPsW n m nP = some (r, m')) :
    MFr [] [] m m' := by
  cases n with
  | zero => simp [projPsW] at h
  | succ n =>
    cases n with
    | zero => simp [projPsW, psAtW, psK3] at h
    | succ n =>
      simp only [projPsW, psAtW, psK3.eq_def] at h
      cases h1 : psGoW n m 1 nP nP 0 with
      | none => simp [h1] at h
      | some x =>
        obtain ⟨r1, m1⟩ := x
        simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]; exact psGoW_mfr _ _ _ _ _ _ _ _ h1

theorem spaW_mfr {m m' : Mem} {T j : Word} {r : List Word} (h : spaW m T j = some (r, m')) : MFr [] [] m m' := by
  simp only [spaW, spaK.eq_def, spaK2.eq_def] at h
  mfr_auto h [binternW_mfr, mkProjW_mfr]

theorem i1lF_mfr {m m' : Mem} {args r : List Word} (h : i1lF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_low ⟨_, _, i1lF_frame h, lt64A_of_all rfl, lt64_of_all rfl⟩

theorem ipalF_mfr {m m' : Mem} {args r : List Word} (h : ipalF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_low ⟨_, _, ipalF_frame h, lt64A_of_all rfl, lt64_of_all rfl⟩

theorem pbW_mfr : ∀ (n : Nat) (m m' : Mem) (T k i h : Word) (r : List Word),
    pbW n m T k i h = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, hh => by rw [pbW.eq_1] at hh; cases hh
  | n + 1, m, m', T, k, i, h, r, hh => by
    simp only [pbW.eq_2, pbW.k_struct_proj_arg_p.eq_def, pbW.k_instantiate1_lift_fast.eq_def,
      pbW.k_struct_proj_bodies_go.eq_def, pbW.k_sl_cons.eq_def] at hh
    mfr_auto hh [pbW_mfr n _ _ _ _ _ _ _, spaW_mfr, i1lF_mfr, consW_mfr]

theorem spbW_mfr {k : Nat} {m m' : Mem} {T nP nF cty : Word} {r : List Word}
    (h : spbW k m T nP nF cty = some (r, m')) : MFr [] [] m m' := by
  cases k with
  | zero => simp [spbW] at h
  | succ k =>
    simp only [spbW, spbK1.eq_def, spbK2.eq_def, spbK3.eq_def] at h
    mfr_auto h [projPsW_mfr, ipalF_mfr, pbW_mfr _ _ _ _ _ _ _ _]

theorem crfF_mfr {m m' : Mem} {args r : List Word} (h : crfF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (crfF_frame h)
    (fun b hb => .inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb; decide))
    (fun x hx => .inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide))

/-- `sctW`'s frame, from its reading `c` of `all_level_params_defined`'s (`sctW_mfr_stub`: the stub's). -/
theorem sctW_mfr {c : CallM}
    (hc : ∀ (k : Nat) (args : List Word) (m m' : Mem) (r : List Word),
      c k "all_level_params_defined" args m = some (r, m') → MFr [] [] m m') :
    ∀ (n : Nat) (m m' : Mem) (vis nP lo ll bO bL : Word) (r : List Word),
    sctW c n m vis nP lo ll bO bL = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [sctW] at h
  | n + 1, m, m', vis, nP, lo, ll, bO, bL, r, h => by
    simp only [sctW, sctK1.eq_def, sctK2.eq_def, sctK3.eq_def, sctK4.eq_def, sctK5.eq_def] at h
    mfr_auto h [sctW_mfr hc n _ _ _ _ _ _ _ _ _, hc _ _ _ _ _, crfF_mfr, MFr.ofHffF, MFr.ofLbbF]

theorem efgW_mfr : ∀ (n : Nat) (m m' : Mem) (q o l : Word) (r : List Word),
    efgW n m q o l = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, h => by simp [efgW] at h
  | n + 1, m, m', q, o, l, r, h => by
    simp only [efgW, efgK.eq_def] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    · refine MFr.trans (set64ER_mfr m q (rdW (m.arr64 IW) o)) ?_
      mfr_auto h [efgW_mfr n _ _ _ _ _ _]

theorem efW_mfr {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : efW n m o l = some (r, m')) :
    MFr [] [] m m' := by
  simp only [efW, efK1.eq_def, efK2.eq_def] at h
  mfr_auto h [erAllocW_mfr, efgW_mfr _ _ _ _ _ _ _]

theorem wrER_mfr (ws : List Word) (m : Mem) (q : Word) : MFr [] [] m (wrER m q ws) :=
  MFr.of_frame (wrER_frame ws m q) (by simp [EREC]) (by simp)

theorem envPushW_mfr {m m' : Mem} {vis q : Word} {r : List Word} (h : envPushW m vis q = some (r, m')) :
    MFr [] [] m m' := by
  simp only [envPushW] at h
  split at h; · cases h
  split at h; · cases h
  split at h
  rotate_left; · cases h
  rename_i hc
  obtain ⟨ht, -⟩ := hc
  have hra : rowArr (rdW (m.arr64 EREC) (q + 1)) ≠ CTL := by simp only [rowArr, CTL, ArrId]; omega
  have hmem : rowArr (rdW (m.arr64 EREC) (q + 1)) < 201 := by
    have : rowTier (rdW (m.arr64 EREC) (q + 1)) < 2 := Nat.mod_lt _ (by decide)
    simp only [rowArr, ArrId]; omega
  have h1 : MFr [] [] m (rowSet m (rdW (m.arr64 EREC) (q + 1)) (vis + 1) q) :=
    MFr.of_frame ((MemFrame.set64 m _ hra _ _).trans (MemFrame.set64 _ _ hra _ _))
      (by intro b hb; simp at hb; subst hb; exact .inl hmem) (by simp)
  refine MFr.trans h1 ?_
  simp only [envPushK.eq_def] at h
  split at h; · cases h
  split at h
  rotate_left; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  exact MFr.trans (MFr.of_frame (MemFrame.set64 _ ECON (by decide) _ _) (by simp [ECON]) (by simp))
    (MFr.of_frame (MemFrame.setCtl _ 128 _) (by simp) (by simp))

end L.Ind
