import ConAgua.Arena.IndPosSpec6
import ConAgua.Arena.IndSumSpec5
import ConAgua.Arena.IndPos2SpecE
import ConAgua.Arena.IndPosSpec5

/-! # The positivity check's walk memos in the memory at hand (lane `indproofs2`, helper `posmemo`)

`PosMR m`: each per-call memo the positivity check's walks use is well formed in `m` (at some
twin map): `nest_occ` (`noMR`), `depth` (`dpMR`), `replace_apps` (`rpMR`), `has_loose_bvar_b`
(`hbMR`), and the banked `replace_fvars` memo has its invariant (`RfInv`). The walks clear their
memo on entry (the twin starts from `∅`), so a caller needs only *some* well-formed memo; a
relational lemma takes `PosMR m` for the memory it starts from and returns `PosMR m'` for the one
it leaves. It is carried across any writer outside the memo region (`MFr [] []`: stubs by
`stubM_memoFrame`, the stores' interns, `IW` records) by `PosMR.fr`, and across a walk by the
walk's own post (its memo) plus its frame (the others), `PosMR.setNo` etc.

This replaces helper `pos2`'s `PosMemo` (memos well formed in *every* stage state, which is false:
`StageR` does not constrain arrays 201‥208). -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem hbMR_mfr {S0 : List ArrId} {T0 : List Word} {m m' : Mem} (hf : MFr S0 T0 m m') (hS : HBM ∉ S0)
    (hT : (214 : Word) ∉ T0) {mp : Std.HashMap (EIdx × Nat) Bool} (h : hbMR m mp) : hbMR m' mp := by
  obtain ⟨A, C, f, hA, hC⟩ := hf.memo HBM 214 (by decide) (by decide) hS hT
  exact memoRV_frame hbSch hbSch_wf lfKey hbVR A C hA hC m m' f (fun _ _ h => h) mp h

/-- **The walk memos of the positivity check, well formed in `m`.** -/
structure PosMR (m : Mem) : Prop where
  no : ∃ mp, noMR m mp
  dp : ∃ mp, dpMR m mp
  rp : ∃ mp, rpMR m mp
  hb : ∃ mp, hbMR m mp
  rf : ∃ M G g, RfInv m M G g

/-- The five memos' arrays and stamp words. -/
abbrev PosAv (S : List ArrId) (T : List Word) : Prop :=
  (NOM ∉ S ∧ DPM ∉ S ∧ RAM ∉ S ∧ HBM ∉ S ∧ RFM ∉ S) ∧
  ((204 : Word) ∉ T ∧ (206 : Word) ∉ T ∧ (210 : Word) ∉ T ∧ (214 : Word) ∉ T ∧ (208 : Word) ∉ T ∧
    (218 : Word) ∉ T ∧ (219 : Word) ∉ T)

theorem PosMR.mfr {S : List ArrId} {T : List Word} {m m' : Mem} (h : PosMR m) (hf : MFr S T m m')
    (hv : PosAv S T) : PosMR m' := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨t1, t2, t3, t4, t5, t6, t7⟩⟩ := hv
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨M, G, g, hR⟩⟩ := h
  exact ⟨⟨a, noMR_mfr hf h1 t1 ha⟩, ⟨b, dpMR_mfr hf h2 t2 hb⟩, ⟨c, rpMR_mfr hf h3 t3 hc⟩,
    ⟨d, hbMR_mfr hf h4 t4 hd⟩, ⟨M, G, g, hR.mfr hf h5 ⟨t5, t6, t7⟩⟩⟩

/-- Across a writer outside the memo region. -/
theorem PosMR.fr {m m' : Mem} (h : PosMR m) (hf : MFr [] [] m m') : PosMR m' := h.mfr hf (by simp [PosAv])

/-- Across a `nest_occ` walk: its memo from the walk, the others by its frame. -/
theorem PosMR.setNo {m m' : Mem} (h : PosMR m) (hf : MFr [NOM] [204, 205] m m')
    (hn : ∃ mp, noMR m' mp) : PosMR m' := by
  obtain ⟨-, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨M, G, g, hR⟩⟩ := h
  exact ⟨hn, ⟨b, dpMR_mfr hf (by decide) (by decide) hb⟩, ⟨c, rpMR_mfr hf (by decide) (by decide) hc⟩,
    ⟨d, hbMR_mfr hf (by decide) (by decide) hd⟩, ⟨M, G, g, hR.mfr hf (by decide) (by decide)⟩⟩

/-- Across a `depth` walk. -/
theorem PosMR.setDp {m m' : Mem} (h : PosMR m) (hf : MFr [DPM] [206, 207] m m')
    (hn : ∃ mp, dpMR m' mp) : PosMR m' := by
  obtain ⟨⟨a, ha⟩, -, ⟨c, hc⟩, ⟨d, hd⟩, ⟨M, G, g, hR⟩⟩ := h
  exact ⟨⟨a, noMR_mfr hf (by decide) (by decide) ha⟩, hn, ⟨c, rpMR_mfr hf (by decide) (by decide) hc⟩,
    ⟨d, hbMR_mfr hf (by decide) (by decide) hd⟩, ⟨M, G, g, hR.mfr hf (by decide) (by decide)⟩⟩

/-- Across a `replace_apps` walk. -/
theorem PosMR.setRp {m m' : Mem} (h : PosMR m) (hf : MFr [RAM] [210, 211] m m')
    (hn : ∃ mp, rpMR m' mp) : PosMR m' := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, -, ⟨d, hd⟩, ⟨M, G, g, hR⟩⟩ := h
  exact ⟨⟨a, noMR_mfr hf (by decide) (by decide) ha⟩, ⟨b, dpMR_mfr hf (by decide) (by decide) hb⟩, hn,
    ⟨d, hbMR_mfr hf (by decide) (by decide) hd⟩, ⟨M, G, g, hR.mfr hf (by decide) (by decide)⟩⟩

/-- Across a `has_loose_bvar_b` walk. -/
theorem PosMR.setHb {m m' : Mem} (h : PosMR m) (hf : MFr [HBM] [214, 215] m m')
    (hn : ∃ mp, hbMR m' mp) : PosMR m' := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, -, ⟨M, G, g, hR⟩⟩ := h
  exact ⟨⟨a, noMR_mfr hf (by decide) (by decide) ha⟩, ⟨b, dpMR_mfr hf (by decide) (by decide) hb⟩,
    ⟨c, rpMR_mfr hf (by decide) (by decide) hc⟩, hn, ⟨M, G, g, hR.mfr hf (by decide) (by decide)⟩⟩

/-- Across the banked `replace_fvars` walk. -/
theorem PosMR.setRf {m m' : Mem} (h : PosMR m) (hf : RxFr m m') (hn : ∃ M G g, RfInv m' M G g) :
    PosMR m' := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, -⟩ := h
  exact ⟨⟨a, noMR_mfr hf (by decide) (by decide) ha⟩, ⟨b, dpMR_mfr hf (by decide) (by decide) hb⟩,
    ⟨c, rpMR_mfr hf (by decide) (by decide) hc⟩, ⟨d, hbMR_mfr hf (by decide) (by decide) hd⟩, hn⟩

theorem posmemo_erCopyW_iw : ∀ (n : Nat) (m m' : Mem) (d s l : Word), erCopyW n m d s l = some m' →
    MemFrame [IW] [200] m m'
  | 0, _, _, _, _, _, h => by simp [erCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [erCopyW_nil n m d s l hl] at h; cases h; exact MemFrame.refl _ _ _
    · rw [erCopyW_step n m d s l hl] at h
      exact (set64IW_frame _ _ _).trans (posmemo_erCopyW_iw n _ _ _ _ _ h)

theorem erToIwW_mfr {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : erToIwW n m o l = some (r, m')) :
    MFr [] [] m m' := by
  unfold erToIwW at h
  split at h; · simp at h
  rename_i q m1 hal
  split at h; · simp at h
  rename_i m2 hc
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact (allocW_mfr hal).trans (MFr.of_iw (posmemo_erCopyW_iw _ _ _ _ _ _ hc))

theorem consW_mfr {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} (h : consW n m x o l = some (r, m')) :
    MFr [] [] m m' := by
  unfold consW at h
  split at h; · simp at h
  split at h; · simp at h
  rename_i q m1 hal
  split at h; · simp at h
  rename_i m2 hc
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ((allocW_mfr hal).trans (MFr.set_iw _ _ _)).trans (MFr.of_iw (posmemo_copyW_iw _ _ _ _ _ _ hc))

theorem piBW_mfr : ∀ (n : Nat) (m m' : Mem) (fuel h : Word) (r : List Word), piBW n m fuel h = some (r, m') →
    MFr [] [] m m'
  | 0, _, _, _, _, _, hh => by simp [piBW] at hh
  | n + 1, m, m', fuel, h, r, hh => by
    simp only [piBW, piBK1, piBK2.eq_def, piBK3.eq_def] at hh
    mfr_auto hh [piBW_mfr n _ _ _ _ _, consW_mfr]

/-! ## Frames of the models, by `mfr_auto` (`IndPos2SpecC`) -/

/-- Across `fvar_b` (its write set, the `fvarRange` memo). -/
theorem MFr.ofFvbF {m m' : Mem} {args r : List Word} (h : fvbF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (fvbF_frame h)
    (fun b hb => .inl (by simp only [frA, List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb; decide))
    (fun x hx => .inl (by simp only [frC, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide))
/-- Across `has_fvar_fast`. -/
theorem MFr.ofHffF {m m' : Mem} {args r : List Word} (h : hffF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (hffF_frame h)
    (fun b hb => .inl (by simp only [frA, List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb; decide))
    (fun x hx => .inl (by simp only [frC, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide))
/-- Across `loose_bvars_bounded_fast`. -/
theorem MFr.ofLbbF {m m' : Mem} {args r : List Word} (h : lbbF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (lbbF_frame h)
    (fun b hb => .inl (by simp only [walkA, List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb; decide))
    (fun x hx => .inl (by simp only [walkC, List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide))
/-- Across `get_app_fn_f` (writes nothing). -/
theorem MFr.ofGafF {m m' : Mem} {args r : List Word} (h : gafF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (gafF_frame h) (by simp) (by simp)
/-- Across `get_app_args_f` (the stack, the pool, their tops). -/
theorem MFr.ofGaaF {m m' : Mem} {args r : List Word} (h : gaaF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (gaaF_frame h)
    (fun b hb => .inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide))
    (fun x hx => .inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide))
/-- Across `strip_pis`/`strip_lams` (their write set, `stripF_frame`). -/
theorem MFr.ofStripF {tg : Word} {m m' : Mem} {args r : List Word} (h : stripF tg m args = some (r, m')) :
    MFr [] [] m m' := MFr.of_iw (stripF_frame h)

theorem mkForallW_mfr {m m' : Mem} {t b r : Word} (h : mkForallW m t b = some (r, m')) : MFr [] [] m m' :=
  MFr.of_low (mkForallW_low h)
theorem fvinternW_mfr {m m' : Mem} {u ty r : Word} (h : fvinternW m u ty = some (r, m')) : MFr [] [] m m' :=
  MFr.of_low (fvinternW_low h)
theorem ceinternW_mfr {m m' : Mem} {f x r : Word} (h : ceinternW m f x = some (r, m')) : MFr [] [] m m' :=
  MFr.of_low (ceinternW_low h)
theorem envFindW_mfr {m m' : Mem} {w vis : Word} {r : List Word} (h : envFindW m w vis = some (r, m')) :
    MFr [] [] m m' := by rw [envFindW_mem h]; exact MFr.refl _ _ _

/-- Across `abstract1_fast` (its write set, the `abstract1` memo and the store, below 64). -/
theorem MFr.ofAbF {m m' : Mem} {args r : List Word} (h : abF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_low ⟨_, _, abF_frame h, lt64A_of_all rfl, lt64_of_all rfl⟩

theorem closeW_mfr : ∀ (n : Nat) (m m' : Mem) (dO dl i body : Word) (r : List Word),
    closeW n m dO dl i body = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, h => by simp [closeW] at h
  | n + 1, m, m', dO, dl, i, body, r, h => by
    unfold closeW closeK1 closeK2 closeK3 at h
    mfr_auto h [closeW_mfr n _ _ _ _ _ _ _, MFr.ofAbF, MFr.ofI1F, mkForallW_mfr]

theorem stripW_mfr {m m' : Mem} {ciq : Word} {r : List Word} (h : stripW m ciq = some (r, m')) : MFr [] [] m m' := by
  unfold stripW stripK at h
  mfr_auto h [MFr.ofStripF]

theorem entryW_mfr {m m' : Mem} {C ciq : Word} {r : List Word} (h : entryW m C ciq = some (r, m')) :
    MFr [] [] m m' := by
  unfold entryW entryK1 entryK2 entryK3 at h
  mfr_auto h [stripW_mfr, MFr.ofStub, MFr.ofI1F, MFr.ofGafF]

theorem ncGoW_mfr : ∀ (k : Nat) (m m' : Mem) (vis C co cl cs ol fp : Word) (r : List Word),
    ncGoW k m vis C co cl cs ol fp = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [ncGoW] at h
  | k + 1, m, m', vis, C, co, cl, cs, ol, fp, r, h => by
    unfold ncGoW ncK1 ncK2 ncK3 at h
    mfr_auto h [ncGoW_mfr k _ _ _ _ _ _ _ _ _ _, envFindW_mfr, entryW_mfr, posRecW_mfr,
      fun h => (MFr.set_iw _ _ _).trans (ncGoW_mfr k _ _ _ _ _ _ _ _ _ _ h)]

theorem ncWf_mfr {k : Nat} {m m' : Mem} {vis C co cl : Word} {r : List Word} (h : ncWf k m vis C co cl = some (r, m')) :
    MFr [] [] m m' := by
  cases k with
  | zero => simp [ncWf] at h
  | succ k =>
  simp only [ncWf] at h
  unfold ncW ncB at h
  mfr_auto h [allocW_mfr, ncGoW_mfr _ _ _ _ _ _ _ _ _ _ _]

theorem ntWf_mfr {k : Nat} {m m' : Mem} {vis C : Word} {r : List Word} (h : ntWf k m vis C = some (r, m')) :
    MFr [] [] m m' := by
  cases k with
  | zero => simp [ntWf] at h
  | succ k =>
  simp only [ntWf] at h
  unfold ntW ntK1 ntK2 at h
  mfr_auto h [envFindW_mfr, ncWf_mfr]

theorem dcGoW_mfr : ∀ (n : Nat) (m m' : Mem) (hi off l : Word) (r : List Word),
    dcGoW n m hi off l = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, h => by simp [dcGoW] at h
  | n + 1, m, m', hi, off, l, r, h => by
    unfold dcGoW dcK at h
    mfr_auto h [MFr.ofFvbF, dcGoW_mfr n _ _ _ _ _ _]

theorem dcWf_mfr {n : Nat} {m m' : Mem} {ctx off l : Word} {r : List Word} (h : dcWf n m ctx off l = some (r, m')) :
    MFr [] [] m m' := by
  cases n with
  | zero => simp [dcWf] at h
  | succ n => exact dcGoW_mfr _ _ _ _ _ _ _ h

theorem nwsW_mfr {n : Nat} {m m' : Mem} {ctx off l po pl : Word} {r : List Word}
    (h : nwsW n m ctx off l po pl = some (r, m')) : MFr [] [] m m' := by
  unfold nwsW nwsK at h
  mfr_auto h [dcWf_mfr]

theorem gcW_mfr : ∀ (k : Nat) (m m' : Mem) (vis nPc off l oo ol : Word) (r : List Word),
    gcW k m vis nPc off l oo ol = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [gcW] at h
  | k + 1, m, m', vis, nPc, off, l, oo, ol, r, h => by
    unfold gcW gcK1 gcK2 at h
    mfr_auto h [ntWf_mfr, appendW_mfr, gcW_mfr k _ _ _ _ _ _ _ _ _]

theorem rhGoW_mfr : ∀ (k : Nat) (m m' : Mem) (no nl lv po pl nP q j : Word),
    rhGoW k m no nl lv po pl nP q j = some m' → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [rhGoW] at h
  | k + 1, m, m', no, nl, lv, po, pl, nP, q, j, h => by
    unfold rhGoW rhK1 rhK2 at h
    mfr_auto h [posRecW_mfr, fun h => (MFr.set_iw _ _ _).trans (rhGoW_mfr k _ _ _ _ _ _ _ _ _ _ h)]

theorem haW_mfr {k : Nat} {m m' : Mem} {ctx po pl i : Word} {r : List Word}
    (h : haW k m ctx po pl i = some (r, m')) : MFr [] [] m m' := by
  have rh : ∀ {m m' : Mem} {ctx : Word} {r : List Word}, rhWf k m ctx = some (r, m') → MFr [] [] m m' := by
    intro m m' ctx r h
    cases k with
    | zero => simp [rhWf] at h
    | succ k =>
    simp only [rhWf] at h
    unfold rhW rhA rhB at h
    mfr_auto h [allocW_mfr, rhGoW_mfr _ _ _ _ _ _ _ _ _ _ _]
  unfold haW haK1 haK2 at h
  mfr_auto h [rh, appendW_mfr]

theorem naW_mfr {k : Nat} {m m' : Mem} {vis c : Word} {r : List Word} (h : naW k m vis c = some (r, m')) :
    MFr [] [] m m' := by
  unfold naW naK1 naK2 at h
  mfr_auto h [envFindW_mfr, piBW_mfr _ _ _ _ _ _]

theorem resHeadW_mfr {m m' : Mem} {e : Word} {r : List Word} (h : resHeadW m e = some (r, m')) : MFr [] [] m m' := by
  unfold resHeadW resHeadK at h
  mfr_auto h [MFr.ofStub, MFr.ofI1F, MFr.ofGafF]

theorem bvbW_mfr {n : Nat} {m m' : Mem} {h f x : Word} (hb : bvbW n m h f = some (x, m')) : MFr [] [] m m' := by
  have hfr : BbFrame m m' := by
    match n, hb with
    | n + 1, hb =>
      by_cases hs : derBW m h = 32767
      · rw [bvbW_sat (n := n) (m := m) (h := h) (f := f) hs] at hb
        match n, hb with
        | k + 1, hb => rw [bbN_succ] at hb; exact bbMemoW_frame k m m' h f x hb
      · rw [bvbW_pk (n := n) (m := m) (h := h) (f := f) hs] at hb
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
        exact MemFrame.refl _ _ _
  exact MFr.of_frame hfr (by simp [BMEMO]) (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> decide)

/-- The `has_loose_bvar_b` walk's write set among the memos. -/
abbrev HbFr (m m' : Mem) : Prop := MFr [HBM] [214, 215] m m'

theorem hbInsW_mfr {m m' : Mem} {e i r x : Word} (h : hbInsW m e i r = some (x, m')) : HbFr m m' := by
  unfold hbInsW at h
  rcases hs : msetG hbSch m e i r with _ | m2 <;> rw [hs] at h; · simp at h
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact ⟨_, _, msetG_frame hbSch hbSch_wf m m2 e i r hs, by simp [hbSch], by simp [hbSch]⟩

theorem hbGoW_mfr : ∀ (n : Nat) (m m' : Mem) (f i h r : Word), hbGoW n m f i h = some (r, m') → HbFr m m'
  | 0, _, _, _, _, _, _, hh => by simp [hbGoW] at hh
  | n + 1, m, m', f, i, h, r, hh => by
    have node : ∀ {m m' : Mem} {f i g x y z r : Word}, hbNodeW n f m i g x y z = some (r, m') → HbFr m m' := by
      intro m m' f i g x y z r h
      unfold hbNodeW hbO1 hbL1 hbL2 at h
      mfr_auto h [hbGoW_mfr n _ _ _ _ _ _]
    unfold hbGoW hbK1 hbK2 hbK3 hbK4 at hh
    mfr_auto hh [bvbW_mfr, node, hbInsW_mfr]

theorem hbFastW_mfr {n : Nat} {m m' : Mem} {i e r : Word} (h : hbFastW n m i e = some (r, m')) : HbFr m m' := by
  unfold hbFastW at h
  split at h
  · simp at h
  exact MFr.trans ⟨_, _, mclearG_frame hbSch m, by simp, by simp [hbSch]⟩ (hbGoW_mfr _ _ _ _ _ _ _ h)

theorem ncnW_mfr {k : Nat} {m m' : Mem} {ctx po pl us dO dL cv closed r : Word}
    (h : ncnW k m ctx po pl us dO dL cv closed = some (r, m')) : RxFr m m' := by
  unfold ncnW ncnK1 ncnK2 ncnK3 at h
  mfr_auto h [posRecW_mfr, rxDsW_mfr, rxW_mfr]

/-- `nest_crest`'s write set among the memos: `replace_apps`' and the banked `replace_fvars`'. -/
abbrev CrFr (m m' : Mem) : Prop := MFr [RAM, RFM] [210, 211, 208, 209, 218, 219] m m'

theorem pcrW_mfr {k : Nat} {m m' : Mem} {no nl us dO dL hO hL cty : Word} {r : List Word}
    (h : pcrW k m no nl us dO dL hO hL cty = some (r, m')) : CrFr m m' := by
  unfold pcrW pcrK1 pcrK2 pcrK3 at h
  mfr_auto h [pccW_mfr, posRecW_mfr, rxW_mfr]

/-- Across `nest_crest`. -/
theorem PosMR.setCr {m m' : Mem} (h : PosMR m) (hf : CrFr m m') (hrp : ∃ mp, rpMR m' mp)
    (hrf : ∃ M G g, RfInv m' M G g) : PosMR m' := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, -, ⟨d, hd⟩, -⟩ := h
  exact ⟨⟨a, noMR_mfr hf (by decide) (by decide) ha⟩, ⟨b, dpMR_mfr hf (by decide) (by decide) hb⟩, hrp,
    ⟨d, hbMR_mfr hf (by decide) (by decide) hd⟩, hrf⟩

end L.Ind
