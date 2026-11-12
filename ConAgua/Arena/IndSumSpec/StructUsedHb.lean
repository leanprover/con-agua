module

public import ConAgua.Arena.IndTwin
public import ConAgua.Arena.IndPosSpec.NestCrest
public import ConAgua.Arena.IndSumSpec.HlbiWalk
import ConAgua.Arena.IndSumSpec.StructProjArgP
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.StripTele
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.BvarB
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.Walk
import all ConAgua.Arena.MemoLib

@[expose] public section

/-!
# The `hb` memo across `struct_used_later` and across a core call

`struct_used_later` (a leaf of the core stage, `IndTwin.lean`) runs the `hb` walk; what it does to
the walk's memo, at any arguments and fuel:

* the `hb` walk keeps the memo well formed at any memory (`hbGoW_keep`): a node it reaches has a
  handle below `2^32` (`e_view` of a larger word is empty), so every key it stores is a valid one,
  and every value it stores is `0`/`1`; so does `struct_used_later`'s model (`ustW_keep`);
* a core call keeps it (`callW_coreHb`: the core's write set misses it, the leaf
  `struct_used_later` keeps it, `open_pis_at_fvars_f` does not write it), so the positivity
  check's memos survive a core call (`PosMR.ofCore`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The `hb` walk keeps its memo at any memory -/

/-- A node `e_view` reads is a handle below `2^32`. -/
theorem eViewW_H {m : Mem} {h : Word} (hv : eViewW m h ≠ []) : H h := by
  refine Classical.byContradiction fun hc => hv ?_
  have : 4294967295 < h := UInt64.lt_iff_toNat_lt.mpr (by simp only [H, Nat.not_lt] at hc; simp; omega)
  simp [eViewW, this]

/-- What the walk keeps: a `0`/`1` answer and a well-formed memo. -/
def HbKeep (r : Word) (m : Mem) : Prop := (r = 0 ∨ r = 1) ∧ ∃ mp, hbMR m mp

theorem hbO1_keep {n : Nat} {f i2 y r : Word} {m' : Mem} {x : Option (Word × Mem)}
    (ih : ∀ m m' f i h r, hbGoW n m f i h = some (r, m') → (∃ mp, hbMR m mp) → HbKeep r m')
    (hx : ∀ r1 m1, x = some (r1, m1) → HbKeep r1 m1) (h : hbO1 n f i2 y x = some (r, m')) :
    HbKeep r m' := by
  rcases x with _ | ⟨r1, m1⟩
  · simp [hbO1] at h
  have k1 := hx r1 m1 rfl
  by_cases e : r1 = 1
  · rw [hbO1_one (hr := e)] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨.inr rfl, k1.2⟩
  rw [hbO1_ne (hr := e)] at h
  exact ih _ _ _ _ _ _ h k1.2

theorem hbL1_keep {n : Nat} {f i y z r : Word} {m' : Mem} {x : Option (Word × Mem)}
    (ih : ∀ m m' f i h r, hbGoW n m f i h = some (r, m') → (∃ mp, hbMR m mp) → HbKeep r m')
    (hx : ∀ r1 m1, x = some (r1, m1) → HbKeep r1 m1) (h : hbL1 n f i y z x = some (r, m')) :
    HbKeep r m' := by
  rcases x with _ | ⟨r1, m1⟩
  · simp [hbL1] at h
  have k1 := hx r1 m1 rfl
  by_cases e : r1 = 1
  · rw [hbL1_one (hr := e)] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨.inr rfl, k1.2⟩
  rw [hbL1_ne (hr := e)] at h
  rcases h2 : hbGoW n m1 (f - 1) i y with _ | ⟨r2, m2⟩
  · rw [h2] at h; simp [hbL2] at h
  rw [h2] at h
  have k2 := ih _ _ _ _ _ _ h2 k1.2
  by_cases e2 : r2 = 1
  · rw [hbL2_one (hr := e2)] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨.inr rfl, k2.2⟩
  rw [hbL2_ne (hr := e2)] at h
  exact ih _ _ _ _ _ _ h k2.2

/-- **The `hb` walk keeps a well-formed memo and answers `0`/`1`**, at any memory. -/
theorem hbGoW_keep : ∀ (n : Nat) (m m' : Mem) (f i h r : Word), hbGoW n m f i h = some (r, m') →
    (∃ mp, hbMR m mp) → HbKeep r m'
  | 0, _, _, _, _, _, _, hh, _ => by simp [hbGoW] at hh
  | n + 1, m, m', f, i, h, r, hh, ⟨mp, hM⟩ => by
    have ih := hbGoW_keep n
    by_cases hf0 : f = 0
    · rw [hbGoW_zeroF n m f i h hf0] at hh; cases hh
    rw [hbGoW_succ n m f i h hf0] at hh
    rcases h1 : bvbW n m (f - 1) h with _ | ⟨x, m1⟩
    · rw [h1] at hh; simp [hbK1] at hh
    rw [h1] at hh
    have hM1 : hbMR m1 mp := hbMR_mfr (bvbW_mfr h1) (by simp) (by simp) hM
    by_cases hle : x ≤ i
    · rw [hbK1_some_le (hle := hle)] at hh; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
      exact ⟨.inl rfl, mp, hM1⟩
    rw [hbK1_some_gt (hle := hle)] at hh
    generalize hv : eViewW m1 h = v at hh
    by_cases hv0 : v = []
    · subst hv0; simp [hbK2] at hh
    have hH : H h := eViewW_H (by rw [hv]; exact hv0)
    by_cases hg0 : v.headD 0 = 0
    · rw [hbK2_bvar (hv := hv0) (hg := hg0)] at hh; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
      exact ⟨by split <;> simp, mp, hM1⟩
    by_cases hgl : v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 3 ∨ v.headD 0 = 8
    · rw [hbK2_leaf (hv := hv0) (hg0 := hg0) (hg := hgl)] at hh
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
      exact ⟨.inl rfl, mp, hM1⟩
    by_cases hi : 4294967296 ≤ i
    · rw [hbK2_big (hv := hv0) (hg0 := hg0) (hg := hgl) (hi := hi)] at hh; cases hh
    rw [hbK2_node (hv := hv0) (hg0 := hg0) (hg := hgl) (hi := hi)] at hh
    by_cases hfr : mfindG hbSch m1 h i = []
    · rw [hbK3_abort (hr := hfr)] at hh; cases hh
    by_cases hhit : (mfindG hbSch m1 h i).headD 0 ≠ 0
    · rw [hbK3_hit (hr := hfr) (hh := hhit)] at hh; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
      obtain ⟨b, -, hb2⟩ := memoRV_hit hbSch lfKey hbVR m1 mp hM1 h i hfr hhit hH
      refine ⟨?_, mp, hM1⟩
      rcases b with _ | _ <;> simp only [hbVR, mvG, Bool.false_eq_true, ite_false, ite_true] at hb2
      · exact .inl hb2
      · exact .inr hb2
    rw [hbK3_miss (hr := hfr) (hh := hhit)] at hh
    have node : ∀ {m m' : Mem} {f i g x y z r : Word}, hbNodeW n f m i g x y z = some (r, m') →
        (∃ mp, hbMR m mp) → HbKeep r m' := by
      intro m m' f i g x y z r h hm
      have hx : ∀ i', ∀ r1 m1, hbGoW n m (f - 1) i' x = some (r1, m1) → HbKeep r1 m1 :=
        fun i' r1 m1 e => ih _ _ _ _ _ _ e hm
      by_cases g4 : g = 4
      · rw [hbNodeW_4 (hg := g4)] at h; exact hbO1_keep ih (hx i) h
      by_cases g56 : g = 5 ∨ g = 6
      · rw [hbNodeW_56 (hg := g56)] at h; exact hbO1_keep ih (hx i) h
      by_cases g7 : g = 7
      · rw [hbNodeW_7 (hg := g7)] at h; exact hbL1_keep ih (hx i) h
      rw [hbNodeW_9 (hg1 := g4) (hg2 := g56) (hg3 := g7)] at h
      exact ih _ _ _ _ _ _ h hm
    rcases h2 : hbNodeW n f m1 i (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
      (v.tail.tail.tail.headD 0) with _ | ⟨r2, m2⟩
    · rw [h2] at hh; simp [hbK4] at hh
    rw [h2, hbK4_some] at hh
    obtain ⟨hr2, mp2, hM2⟩ := node h2 ⟨mp, hM1⟩
    rw [hbInsW_eq] at hh
    cases hm : msetG hbSch m2 h i r2 with
    | none => rw [hm] at hh; simp at hh
    | some m3 =>
      rw [hm] at hh
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      exact ⟨hr2, _, memoRV_set hbSch hbSch_wf lfKey hbVR hbVR_stable m2 mp2 hM2 h i r2 hH (r2 = 1)
        (by simp only [hbVR]; rcases hr2 with rfl | rfl <;> rfl) m3 hm⟩

/-- **`has_loose_b_var_b_fast` keeps a well-formed memo**, at any memory. -/
theorem hbFastW_keep {n : Nat} {m m' : Mem} {i e r : Word} (h : hbFastW n m i e = some (r, m'))
    (hM : ∃ mp, hbMR m mp) : ∃ mp, hbMR m' mp := by
  obtain ⟨mp, hM⟩ := hM
  by_cases h0 : rdW (m.arr64 CTL) hbSch.cs + 2 = 0
  · rw [hbFastW.abort1 (hc1 := h0)] at h; cases h
  rw [L.Ind.hbFastW.arm1 n _ i e h0] at h
  exact (hbGoW_keep n _ _ _ _ _ _ h ⟨_, memoRV_clear hbSch hbSch_wf lfKey hbVR m mp hM h0⟩).2

/-- **`struct_used_later`'s model keeps a well-formed `hb` memo**, at any memory. -/
theorem ustW_keep {n : Nat} {m m' : Mem} {cty nP j r : Word} (h : ustW n m cty nP j = some (r, m'))
    (hM : ∃ mp, hbMR m mp) : ∃ mp, hbMR m' mp := by
  simp only [ustW] at h
  obtain ⟨rs, m1, hst, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  obtain ⟨mp, hM⟩ := hM
  have hM1 : hbMR m1 mp := memoRV_frame hbSch hbSch_wf lfKey hbVR [IW] [200] (by simp [hbSch, HBM, IW])
    (by simp [hbSch]) m m1 (stripF_frame hst) (fun _ _ h => h) mp hM
  by_cases hz : rs.headD 0 = 0
  · rw [ustK1_some_zero hz] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨mp, hM1⟩
  rw [ustK1_some_ne hz] at h
  exact hbFastW_keep h ⟨mp, hM1⟩

/-! ## The window query keeps the `hb` memo at any memory -/

/-- The insertion closing an arm keeps a well-formed memo. -/
theorem hlbiIns_keep {m m' : Mem} {h d r r' : Word} (hh : H h) (hk : HbKeep r m)
    (hi : hbInsW m h d r = some (r', m')) : HbKeep r' m' := by
  obtain ⟨hr, mp, hM⟩ := hk
  have hb : r = if (r == 1) then 1 else 0 := by rcases hr with rfl | rfl <;> rfl
  obtain ⟨rfl, hM', -⟩ := hbIns_ok hh hb hM hi
  exact ⟨hr, _, hM'⟩

theorem hlbiK2_keep {d h r : Word} {m' : Mem} {x : Option (Word × Mem)} (hh : H h)
    (hx : ∀ r1 m1, x = some (r1, m1) → HbKeep r1 m1) (k : hlbiW.k_has_loose_bvar_in_go_2 d h x = some (r, m')) :
    HbKeep r m' := by
  rcases x with _ | ⟨r1, m1⟩
  · rw [hlbiW.k_has_loose_bvar_in_go_2.none] at k; cases k
  rw [hlbiW.k_has_loose_bvar_in_go_2.arm1, hlbiW.j1.arm1] at k
  exact hlbiIns_keep hh (hx _ _ rfl) k

/-- **`has_loose_bvar_in_go`'s model keeps a well-formed `hb` memo and answers `0`/`1`.** -/
theorem hlbiW_keep : ∀ (n : Nat) (m m' : Mem) (f w d h r : Word), hlbiW n m f w d h = some (r, m') →
    (∃ mp, hbMR m mp) → HbKeep r m'
  | 0, _, _, _, _, _, _, _, hh, _ => by rw [hlbiW.eq_1] at hh; cases hh
  | n + 1, m, m', f, w, d, h, r, hh, ⟨mp, hM⟩ => by
    have ih := hlbiW_keep n
    by_cases hf0 : f = 0
    · rw [hlbiW.abort1 (hc1 := hf0)] at hh; cases hh
    rw [hlbiW.arm1 n m f w d h hf0] at hh
    rcases h1 : bvbW n m (f - 1) h with _ | ⟨bb, m1⟩
    · rw [h1, hlbiW.k_bvar_b.none] at hh; cases hh
    rw [h1] at hh
    have hM1 : hbMR m1 mp := hbMR_mfr (bvbW_mfr h1) (by simp) (by simp) hM
    have k1 : ∃ mp, hbMR m1 mp := ⟨mp, hM1⟩
    by_cases hle : bb ≤ d
    · rw [hlbiW.k_bvar_b.arm1 (hc1 := hle)] at hh; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
      exact ⟨.inl rfl, k1⟩
    by_cases hvn : eViewW m1 h = []
    · rw [hlbiW.k_bvar_b.abort1 (hc1 := hle) (hc2 := hvn)] at hh; cases hh
    have hH : H h := eViewW_H hvn
    by_cases hg0 : (eViewW m1 h).headD 0 = 0
    · rw [hlbiW.k_bvar_b.arm2 (hc1 := hle) (hc2 := hvn) (hc3 := hg0)] at hh
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
      refine ⟨?_, k1⟩
      split <;> split <;> simp
    by_cases hgl : (eViewW m1 h).headD 0 = 1 ∨ (eViewW m1 h).headD 0 = 2 ∨ (eViewW m1 h).headD 0 = 3 ∨
        (eViewW m1 h).headD 0 = 8
    · rw [hlbiW.k_bvar_b.arm3 (hc1 := hle) (hc2 := hvn) (hc3 := hg0) (hc4 := hgl)] at hh
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
      exact ⟨.inl rfl, k1⟩
    by_cases hd : 4294967296 ≤ d
    · rw [hlbiW.k_bvar_b.abort2 (hc1 := hle) (hc2 := hvn) (hc3 := hg0) (hc4 := hgl) (hc5 := hd)] at hh; cases hh
    by_cases hfr : mfindG hbSch m1 h d = []
    · rw [hlbiW.k_bvar_b.abort3 (hc1 := hle) (hc2 := hvn) (hc3 := hg0) (hc4 := hgl) (hc5 := hd) (hc6 := hfr)] at hh
      cases hh
    by_cases hhit : (mfindG hbSch m1 h d).headD 0 ≠ 0
    · rw [hlbiW.k_bvar_b.arm4 (hc1 := hle) (hc2 := hvn) (hc3 := hg0) (hc4 := hgl) (hc5 := hd) (hc6 := hfr)
        (hc7 := hhit)] at hh
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
      obtain ⟨b, -, hb2⟩ := memoRV_hit hbSch lfKey hbVR m1 mp hM1 h d hfr hhit hH
      refine ⟨?_, k1⟩
      rcases b with _ | _ <;> simp only [hbVR, mvG, Bool.false_eq_true, ite_false, ite_true] at hb2
      · exact .inl hb2
      · exact .inr hb2
    have hmiss : (mfindG hbSch m1 h d).headD 0 = 0 := by simpa using hhit
    -- an arm: the first call, then (unless it answered `1`) the rest, then the insertion
    have rec1 : ∀ {m0 : Mem} {d0 x : Word}, (∃ mp, hbMR m0 mp) →
        ∀ r1 m2, hlbiW n m0 (f - 1) w d0 x = some (r1, m2) → HbKeep r1 m2 :=
      fun hm r1 m2 e => ih _ _ _ _ _ _ _ e hm
    have orK : ∀ {K : Option (Word × Mem) → Option (Word × Mem)} {m0 : Mem} {d0 x : Word} {r : Word} {m' : Mem},
        (∃ mp, hbMR m0 mp) → K none = none → (∀ r1 m2, r1 = 1 → K (some (r1, m2)) = hbInsW m2 h d 1) →
        (∀ r1 m2, r1 ≠ 1 → ∀ r m', K (some (r1, m2)) = some (r, m') → (∃ mp, hbMR m2 mp) → HbKeep r m') →
        K (hlbiW n m0 (f - 1) w d0 x) = some (r, m') → HbKeep r m' := by
      intro K m0 d0 x r m' hm hK0 hK1 hK2 k
      rcases e : hlbiW n m0 (f - 1) w d0 x with _ | ⟨r1, m2⟩
      · rw [e, hK0] at k; cases k
      rw [e] at k
      have k2 := rec1 hm r1 m2 e
      by_cases e1 : r1 = 1
      · rw [hK1 _ _ e1] at k; exact hlbiIns_keep hH ⟨.inr rfl, k2.2⟩ k
      · exact hK2 _ _ e1 _ _ k k2.2
    by_cases g4 : (eViewW m1 h).headD 0 = 4
    · rw [hlbiW.k_bvar_b.arm5 (hc1 := hle) (hc2 := hvn) (hc3 := hg0) (hc4 := hgl) (hc5 := hd) (hc6 := hfr)
        (hc7 := hmiss) (hc8 := g4)] at hh
      exact orK k1 (hlbiW.k_has_loose_bvar_in_go.none ..)
        (fun r1 m2 e => by rw [hlbiW.k_has_loose_bvar_in_go.arm1 (hc1 := e), hlbiW.j1.arm1])
        (fun r1 m2 e r m' k hm => by
          rw [hlbiW.k_has_loose_bvar_in_go.arm2 (hc1 := e)] at k; exact hlbiK2_keep hH (rec1 hm) k) hh
    by_cases g56 : (eViewW m1 h).headD 0 = 5 ∨ (eViewW m1 h).headD 0 = 6
    · rw [hlbiW.k_bvar_b.arm6 (hc1 := hle) (hc2 := hvn) (hc3 := hg0) (hc4 := hgl) (hc5 := hd) (hc6 := hfr)
        (hc7 := hmiss) (hc8 := g4) (hc9 := g56)] at hh
      exact orK k1 (hlbiW.k_has_loose_bvar_in_go_3.none ..)
        (fun r1 m2 e => by rw [hlbiW.k_has_loose_bvar_in_go_3.arm1 (hc1 := e), hlbiW.j1.arm1])
        (fun r1 m2 e r m' k hm => by
          rw [hlbiW.k_has_loose_bvar_in_go_3.arm2 (hc1 := e)] at k; exact hlbiK2_keep hH (rec1 hm) k) hh
    by_cases g7 : (eViewW m1 h).headD 0 = 7
    · rw [hlbiW.k_bvar_b.arm7 (hc1 := hle) (hc2 := hvn) (hc3 := hg0) (hc4 := hgl) (hc5 := hd) (hc6 := hfr)
        (hc7 := hmiss) (hc8 := g4) (hc9 := g56) (hc10 := g7)] at hh
      exact orK k1 (hlbiW.k_has_loose_bvar_in_go_4.none ..)
        (fun r1 m2 e => by rw [hlbiW.k_has_loose_bvar_in_go_4.arm1 (hc1 := e), hlbiW.j1.arm1])
        (fun r1 m2 e r m' k hm => by
          rw [hlbiW.k_has_loose_bvar_in_go_4.arm2 (hc1 := e)] at k
          exact orK hm (hlbiW.k_has_loose_bvar_in_go_5.none ..)
            (fun r1 m2 e => by rw [hlbiW.k_has_loose_bvar_in_go_5.arm1 (hc1 := e), hlbiW.j1.arm1])
            (fun r1 m3 e r m' k hm => by
              rw [hlbiW.k_has_loose_bvar_in_go_5.arm2 (hc1 := e)] at k; exact hlbiK2_keep hH (rec1 hm) k) k) hh
    rw [hlbiW.k_bvar_b.arm8 (hc1 := hle) (hc2 := hvn) (hc3 := hg0) (hc4 := hgl) (hc5 := hd) (hc6 := hfr)
      (hc7 := hmiss) (hc8 := g4) (hc9 := g56) (hc10 := g7)] at hh
    exact hlbiK2_keep hH (rec1 k1) hh

/-- **`has_loose_bvar_in`'s model keeps a well-formed `hb` memo and answers `0`/`1`**, at any
memory. -/
theorem hlbiFW_keep {n : Nat} {m m' : Mem} {d w e r : Word} (h : hlbiFW n m d w e = some (r, m'))
    (hM : ∃ mp, hbMR m mp) : HbKeep r m' := by
  obtain ⟨mp, hM⟩ := hM
  by_cases hw0 : w = 0
  · rw [hlbiFW.arm1 (hc1 := hw0)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨.inl rfl, mp, hM⟩
  by_cases h0 : rdW (m.arr64 CTL) hbSch.cs + 2 = 0
  · rw [hlbiFW.abort1 (hc1 := hw0) (hc2 := h0)] at h; cases h
  rw [hlbiFW.arm2 (hc1 := hw0) (hc2 := h0)] at h
  exact hlbiW_keep n _ _ _ _ _ _ _ h ⟨_, memoRV_clear hbSch hbSch_wf lfKey hbVR m mp hM h0⟩

/-! ## The two queries at any arguments, as leaves -/

theorem hbFast_specV {p : Prog} (hp : ProgHas p hbLeafP) (n : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "has_loose_b_var_b_fast" vs
    ⦃fun r s' => LocEq s' s₀ ∧ hbFastW n s₀.mem (vs.getD 0 0) (vs.getD 1 0) = some (r.headD 0, s'.mem); ⊤⦄ := by
  have hu : UsF p := ProgHas.right (l₁ := [_, _]) hp
  have hv : p.lookup "e_view" = some eView := hu.get _
  have hf : p.lookup "hb_find" = some (memoFindG hbSch) := hu.get _
  have hput : p.lookup "hb_put" = some (memoPutG hbSch) := hu.get _
  have hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL := hu.get _
  have hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL := hu.get _
  have hbp : BvbProg p := ProgHas.right hu
  have hcl : p.lookup "hb_clear" = some (memoClearG hbSch) := hu.get _
  have hfast : p.lookup "has_loose_b_var_b_fast" = some hasLooseBVarBFastL := hu.get _
  rw [invoke_eq _ hfast]
  simp only [callFn, hasLooseBVarBFastL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      memoClearG_spec hbSch p _ hcl n, hbGo_spec' p hv hf hput hins hgo hbp n] <;>
    finish [hbFastW, Locals.init]

theorem hlbi_specV {p : Prog} (hp : ProgHas p hbLeafP) (n : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "has_loose_bvar_in" vs
    ⦃fun r s' => LocEq s' s₀ ∧
      hlbiFW n s₀.mem (vs.getD 0 0) (vs.getD 1 0) (vs.getD 2 0) = some (r.headD 0, s'.mem); ⊤⦄ := by
  have hu : UsF p := ProgHas.right (l₁ := [_, _]) hp
  have hv : p.lookup "e_view" = some eView := hu.get _
  have hf : p.lookup "hb_find" = some (memoFindG hbSch) := hu.get _
  have hput : p.lookup "hb_put" = some (memoPutG hbSch) := hu.get _
  have hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL := hu.get _
  have hbp : BvbProg p := ProgHas.right hu
  have hcl : p.lookup "hb_clear" = some (memoClearG hbSch) := hu.get _
  have hgo : p.lookup "has_loose_bvar_in_go" = some hasLooseBVarInGoL := hp.get _
  have hin : p.lookup "has_loose_bvar_in" = some hasLooseBVarInL := hp.get _
  rw [invoke_eq _ hin]
  simp only [callFn, hasLooseBVarInL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      memoClearG_spec hbSch p _ hcl n, hlbiGo_spec p hv hf hput hins hgo hbp n] <;>
    finish [hlbiFW, Locals.init]

/-- The leaves' run: a call frame within `usA`/`usC`, and the model at any arguments. -/
theorem hlLeaf_run {p : Prog} (hp : ProgHas p hbLeafP) {g : FnName} (hg : g = "has_loose_b_var_b_fast" ∨ g = "has_loose_bvar_in")
    {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word} (hc : callW p n g vs m = some (r, m')) :
    MemFrame hbWA hbWC m m' ∧ ((∃ mp, hbMR m mp) → HbKeep (r.headD 0) m') := by
  have hfr := (run_memFrame (closedW_of_agree hbLeafP_closed (hp.agree hbLeafFns))
    (by rcases hg with rfl | rfl <;> decide) (run_of_callW hc)).1
  refine ⟨hfr, fun hM => ?_⟩
  rcases hg with rfl | rfl
  · obtain ⟨s'', hm, -, hu⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (hbFast_specV hp n _ vs) (callW_mono hc (Nat.le_add_right n 1))
    rw [hm] at hu
    obtain ⟨-, mp, h⟩ := hbFastW_keep hu hM
    have := (hbGoW_keep n _ _ _ _ _ _ (by
      by_cases h0 : rdW (m.arr64 CTL) hbSch.cs + 2 = 0
      · rw [hbFastW.abort1 (hc1 := h0)] at hu; cases hu
      rw [L.Ind.hbFastW.arm1 n _ _ _ h0] at hu; exact hu)
      (by obtain ⟨mp, hM⟩ := hM
          exact ⟨_, memoRV_clear hbSch hbSch_wf lfKey hbVR m mp hM (by
            intro h0; rw [hbFastW.abort1 (hc1 := h0)] at hu; cases hu)⟩))
    exact this
  · obtain ⟨s'', hm, -, hu⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (hlbi_specV hp n _ vs) (callW_mono hc (Nat.le_add_right n 1))
    rw [hm] at hu
    exact hlbiFW_keep hu hM

/-! ## The `hb` memo across a core call -/

/-- A frame outside the `hb` memo keeps it well formed. -/
theorem hbMR_keep {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (HBM : TieredArray) ∉ A) (hC : (214 : Word) ∉ C) (h : ∃ mp, hbMR m mp) : ∃ mp, hbMR m' mp :=
  let ⟨mp, hm⟩ := h
  ⟨mp, memoRV_frame hbSch hbSch_wf lfKey hbVR A C hA hC m m' hf (fun _ _ h => h) mp hm⟩

theorem coreHb_wframe :
    WFrame CTL coreStageA coreStageC (fun m₀ m => (∃ mp, hbMR m₀ mp) → ∃ mp, hbMR m mp) where
  refl _ h := h
  st64 m₀ m a i v h ha h0 := by
    rcases ha with ⟨hc, ha⟩ | ⟨rfl, hi⟩
    · refine hbMR_keep (MemFrame.set64 m a hc i v) (fun hb => ?_) (by simp) (h h0)
      simp only [List.mem_singleton] at hb
      have := coreStageA_stage a ha
      rw [← hb] at this
      revert this; decide
    · refine hbMR_keep (MemFrame.setCtl m i v) (by simp) (fun hx => ?_) (h h0)
      simp only [List.mem_singleton] at hx
      have := coreStageC_stage i hi
      rw [← hx] at this
      revert this; decide
  setG _ m g v h h0 :=
    hbMR_keep (A := []) (C := []) (m := m) (m' := m.setG g v)
      ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩ (by simp) (by simp) (h h0)

/-- **`struct_used_later` keeps the `hb` memo**, at any arguments and fuel. -/
theorem coreHb_us {p : Prog} (hp : UsF p) (n : Nat) (m₀ : Mem) (vs : List Word) :
    ⦃fun s => (∃ mp, hbMR m₀ mp) → ∃ mp, hbMR s.mem mp⦄ invoke p (exec p n) "struct_used_later" vs
    ⦃fun _ s => (∃ mp, hbMR m₀ mp) → ∃ mp, hbMR s.mem mp; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨-, hc⟩ := M.of_run (P := fun t => t = s) rfl hrun (callW_spec p n "struct_used_later" vs s)
  obtain ⟨s'', hm, -, hu⟩ := triple_of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
    (structUsedLater_specV hp n _ vs) (callW_mono hc (Nat.le_add_right n 2))
  rw [hm] at hu
  exact fun h0 => ustW_keep hu (hs h0)

/-- **`open_pis_at_fvars_f` keeps the `hb` memo** (it does not write it). -/
theorem coreHb_opf {p : Prog} (hp : OpfF p) (n : Nat) (m₀ : Mem) (vs : List Word) :
    ⦃fun s => (∃ mp, hbMR m₀ mp) → ∃ mp, hbMR s.mem mp⦄ invoke p (exec p n) "open_pis_at_fvars_f" vs
    ⦃fun _ s => (∃ mp, hbMR m₀ mp) → ∃ mp, hbMR s.mem mp; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨-, hc⟩ := M.of_run (P := fun t => t = s) rfl hrun (opfF_spec p hp n s vs)
  exact fun h0 => hbMR_keep (opfF_frame hc) (by decide) (by decide) (hs h0)

/-- **A core call keeps the `hb` memo well formed.** -/
theorem callW_coreHb {p : Prog} (hcl : CoreStageClosed p) {f : FnName} (hf : f ∈ stageCoreFns)
    {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word} (h : callW p n f vs m = some (r, m'))
    (hM : ∃ mp, hbMR m mp) : ∃ mp, hbMR m' mp := by
  have hL : ∀ g ∈ coreLeaves, ∀ n m₀ vs,
      ⦃fun s => (∃ mp, hbMR m₀ mp) → ∃ mp, hbMR s.mem mp⦄ invoke p (exec p n) g vs
      ⦃fun _ s => (∃ mp, hbMR m₀ mp) → ∃ mp, hbMR s.mem mp; ⊤⦄ := by
    intro g hg n m₀ vs
    simp only [coreLeaves, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact coreHb_us hcl.us n m₀ vs
    · exact coreHb_opf hcl.opf n m₀ vs
    all_goals
      apply M.triple_of_run
      intro s r s' hs hrun
      obtain ⟨-, hc⟩ := M.of_run (P := fun t => t = s) rfl hrun (callW_spec p n _ vs s)
      exact fun h0 => ((hlLeaf_run hcl.hl (by simp) hc).2 (hs h0)).2
  obtain ⟨s', hs', hk⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (invoke_frameL p hcl.closed coreHb_wframe hL n f hf vs _) h
  exact hs' ▸ hk hM

/-- **The positivity check's memos across a core call.** -/
theorem PosMR.ofCore {p : Prog} {m m' : Mem} (hP : PosMR m) (hcl : CoreStageClosed p) {f : FnName}
    (hf : f ∈ stageCoreFns) {n : Nat} {vs : List Word} {r : List Word}
    (h : callW p n f vs m = some (r, m')) : PosMR m' :=
  hP.setHb (callW_coreFrame hcl hf h).mfr (callW_coreHb hcl hf h hP.hb)

end L.Ind

end
