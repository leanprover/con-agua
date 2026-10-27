import ConAgua.Arena.PromoteL
import ConAgua.Arena.PromoteNRef
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# `promote_l` refines `promoteL`, `promote_ls` refines `promoteLs`

`pl_rel` by induction on L's fuel (`promote_l`, `pl_arm`), with `pn_rel` for the parameter
names; then `promote_l_pool` (`promoteLList` over a pool slice, the results above the pool top)
and `pls_arm`/`promote_ls`. The twin side: the arms named (`promoteL_succ`), the view of a level
(`lvNodeW_view`: L's words are the arena's view, `LevelArena.lean`) and of a level list
(`lsNodeW_view`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## The twin, with the arm named -/

/-- The twin's arm of `promoteL` after a memo miss. -/
def plArmT (m : PMemo) (fuel : Nat) (h : LIdx) : AM (PMemo × LIdx) := do
  match ← viewL h with
  | .zero => do pure (m, ← internPersistentL .zero)
  | .succ u => do
    let (m, u) ← promoteL m fuel u
    pure (m, ← internPersistentL (.succ u))
  | .max u v => do
    let (m, u) ← promoteL m fuel u
    let (m, v) ← promoteL m fuel v
    pure (m, ← internPersistentL (.max u v))
  | .imax u v => do
    let (m, u) ← promoteL m fuel u
    let (m, v) ← promoteL m fuel v
    pure (m, ← internPersistentL (.imax u v))
  | .param n => do
    let (m, n) ← promoteN m fuel n
    pure (m, ← internPersistentL (.param n))

/-- The twin's `promoteL` at fuel `fuel + 1`, with the arm named. -/
def plStepT (m : PMemo) (fuel : Nat) (h : LIdx) : AM (PMemo × LIdx) :=
  if h.isPersistent then pure (m, h)
  else match m.lM[h]? with
    | some r => pure (m, r)
    | none => do
      let (m, r) ← plArmT m fuel h
      pure ({ m with lM := m.lM.insert h r }, r)

theorem promoteL_succ (m : PMemo) (fuel : Nat) (h : LIdx) :
    promoteL m (fuel + 1) h = plStepT m fuel h := by
  rw [promoteL, plStepT]
  by_cases hp : h.isPersistent
  · simp only [hp, ↓reduceIte]
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]
    cases hm : m.lM[h]? with
    | some r => rfl
    | none =>
      simp only [plArmT, bind_assoc]
      apply bind_congr; intro v
      cases v <;> simp

/-! ## The view of a level -/

theorem viewL_run {a : AState} {h : LIdx} {v : LNodeView} (hw : a.store.lss.ls.view h = some v) :
    (viewL h).run a = .ok (v, a) := by
  simp only [viewL, EStore.ls, StateT.run_bind, StateT.run_get, pure_bind, hw]; rfl

/-- **L's view of a level handle is the arena's**: a returning `lv_node` read a node the arena
views. -/
theorem lvNodeW_view {m : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : h.toNat < 2 ^ 32)
    (hne : lvNodeW m h ≠ []) : ∃ v, a.store.lss.ls.view (decI h) = some v := by
  have hfl := ConsR.flag hR.zero
  have hidx := decL_idx h
  have ht1 := tierW_le h
  unfold lvNodeW at hne
  simp only [h32 hh, ne_eq, not_true_eq_false, ↓reduceIte] at hne
  by_cases hsc : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hsc] at hne
  simp only [hsc, ↓reduceIte] at hne
  have hview : a.store.lss.ls.view (decI h) =
      (if tierW h = 0 then a.store.lss.ls.pers else a.store.lss.ls.scr).get (decI h) := by
    unfold LStore.view
    rw [decL_pers h hh]
    by_cases ht : tierW h = 0
    · simp [ht]
    · have hon : a.store.lss.ls.scratchOn = true := by
        rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun e => hsc ⟨ht, e⟩
      simp [ht, hon]
  rw [hview]
  have e0 : ((decI h : LIdx).tag = 0 ↔ h >>> 28 = 0) := decL_tag_eq h hh 0 (by decide)
  have e1 : ((decI h : LIdx).tag = 1 ↔ h >>> 28 = 1) := decL_tag_eq h hh 1 (by decide)
  have e2 : ((decI h : LIdx).tag = 2 ↔ h >>> 28 = 2) := decL_tag_eq h hh 2 (by decide)
  have e3 : ((decI h : LIdx).tag = 3 ↔ h >>> 28 = 3) := decL_tag_eq h hh 3 (by decide)
  have e4 : ((decI h : LIdx).tag = 4 ↔ h >>> 28 = 4) := decL_tag_eq h hh 4 (by decide)
  simp only [LTables.get, LTag.zero, LTag.succ, LTag.max, LTag.imax, LTag.param, beq_iff_eq,
    e0, e1, e2, e3, e4]
  by_cases g0 : h >>> 28 = 0
  · simp (config := { decide := true }) only [g0, ↓reduceIte] at hne ⊢
    by_cases hc : tcnt m ZERO (tierW h) ≤ idxW h
    · simp [hc] at hne
    obtain ⟨x, hx, -⟩ := ConsR.node hR.zero (tierW h) ht1
      (idxW h) (UInt64.not_le.mp hc)
    exact ⟨_, by rw [Tbl.node?, hidx, apply_ite LTables.zeros, hx]; rfl⟩
  by_cases g1 : h >>> 28 = 1
  · simp (config := { decide := true }) only [g1, ↓reduceIte] at hne ⊢
    by_cases hc : tcnt m SUCC (tierW h) ≤ idxW h
    · simp [hc] at hne
    obtain ⟨x, hx, -⟩ := ConsR.node hR.succ (tierW h) ht1
      (idxW h) (UInt64.not_le.mp hc)
    exact ⟨_, by rw [Tbl.node?, hidx, apply_ite LTables.succs, hx]; rfl⟩
  by_cases g2 : h >>> 28 = 2
  · simp (config := { decide := true }) only [g2, ↓reduceIte] at hne ⊢
    by_cases hc : tcnt m MAX (tierW h) ≤ idxW h
    · simp [hc] at hne
    obtain ⟨x, hx, -⟩ := ConsR.node hR.max (tierW h) ht1
      (idxW h) (UInt64.not_le.mp hc)
    exact ⟨_, by rw [Tbl.node?, hidx, apply_ite LTables.maxs, hx]; rfl⟩
  by_cases g3 : h >>> 28 = 3
  · simp (config := { decide := true }) only [g3, ↓reduceIte] at hne ⊢
    by_cases hc : tcnt m IMAX (tierW h) ≤ idxW h
    · simp [hc] at hne
    obtain ⟨x, hx, -⟩ := ConsR.node hR.imax (tierW h) ht1
      (idxW h) (UInt64.not_le.mp hc)
    exact ⟨_, by rw [Tbl.node?, hidx, apply_ite LTables.imaxs, hx]; rfl⟩
  by_cases g4 : h >>> 28 = 4
  · simp (config := { decide := true }) only [g4, ↓reduceIte] at hne ⊢
    by_cases hc : tcnt m PARAM (tierW h) ≤ idxW h
    · simp [hc] at hne
    obtain ⟨x, hx, -⟩ := ConsR.node hR.param (tierW h) ht1
      (idxW h) (UInt64.not_le.mp hc)
    exact ⟨_, by rw [Tbl.node?, hidx, apply_ite LTables.params, hx]; rfl⟩
  simp [g0, g1, g2, g3, g4] at hne

/-! ## The relation for levels -/

/-- The arrays and `CTL` words a level promotion writes (the names' and the level tables'). -/
abbrev lArrs : List ArrId :=
  [POOL, PT0, NAREC, tier1 NAREC, NASLOT, tier1 NASLOT, NSREC, tier1 NSREC, NSSLOT, tier1 NSSLOT, NNREC,
    tier1 NNREC, NNSLOT, tier1 NNSLOT, PNM, ZREC, tier1 ZREC, ZSLOT, tier1 ZSLOT, SREC, tier1 SREC,
    SSLOT, tier1 SSLOT, MREC, tier1 MREC, MSLOT, tier1 MSLOT, IREC, tier1 IREC, ISLOT, tier1 ISLOT,
    PREC, tier1 PREC, PSLOT, tier1 PSLOT, PLM, SHP, tier1 SHP, MHP, tier1 MHP, IHP, tier1 IHP]
abbrev lCtl : List Word := [34, 35, 36, 37, 38, 39, 141, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 143]

/-- **What a successful run of a level promotion gives** (`PNOk` at the level frame). -/
def PLOk {α : Type} (op : AM (PMemo × α)) (dec : Word → α) (m : Mem) (a : AState) (pm : PMemo)
    (r : Word) (m' : Mem) : Prop :=
  ∃ a' pm', op.run a = .ok ((pm', dec r), a') ∧ ArenaD m' a' ∧ PMemoR m' pm' ∧ PW r ∧
    cp a' = cp a ∧ MemFrame lArrs lCtl m m' ∧ pm'.eM = pm.eM ∧ pm'.lsM = pm.lsM ∧ SlKeep m m'

theorem plSch_wf : plSch.WF := ⟨by decide, by decide⟩

/-- The level memo gains an entry. -/
theorem PMemoR.setL {m m' : Mem} {pm : PMemo} (hP : PMemoR m pm) (h r : Word) (hh : h.toNat < 2 ^ 32)
    (hr : PW r) (hs : msetG plSch m h 0 r = some m') :
    PMemoR m' { pm with lM := pm.lM.insert (decI h) (decI r) } := by
  have hf := msetG_frame plSch plSch_wf m m' h 0 r hs
  exact ⟨memoRV_frame pnSch pnSch_wf _ _ _ _ (by decide) (by decide) m m' hf
      (fun _ _ h => h) _ hP.n,
    memoRV_set plSch plSch_wf (hKey .level) (VP .level) (vp_stable _ _) m pm.lM hP.l h 0 r
      ⟨hh, rfl⟩ (decI r) ⟨rfl, hr.1, hr.2⟩ m' hs,
    memoRV_frame plsSch ⟨by decide, by decide⟩ _ _ _ _ (by decide) (by decide) m m' hf
      (fun _ _ h => h) _ hP.ls,
    memoRV_frame peSch ⟨by decide, by decide⟩ _ _ _ _ (by decide) (by decide) m m' hf
      (fun _ _ h => h) _ hP.e⟩

theorem nFrame_l {m m' : Mem} (h : MemFrame nArrs nCtl m m') : MemFrame lArrs lCtl m m' :=
  h.mono (by simp) (by simp)

/-- **The end of a chain into `PLOk`.** -/
theorem PLOk.of_sim {α : Type} {op : AM (PMemo × α)} {dec : Word → α} {m : Mem} {a : AState}
    {pm : PMemo} {mo : Option (Word × Mem)} (h : Sim mo op a fun r x m' a' => x.2 = dec r ∧
      ArenaD m' a' ∧ PMemoR m' x.1 ∧ PW r ∧ cp a' = cp a ∧ MemFrame lArrs lCtl m m' ∧
      x.1.eM = pm.eM ∧ x.1.lsM = pm.lsM ∧ SlKeep m m')
    {r : Word} {m' : Mem} (hm : mo = some (r, m')) : PLOk op dec m a pm r m' := by
  obtain ⟨⟨pm', y⟩, a', h1, e, h2⟩ := h r m' hm
  subst e; exact ⟨a', pm', h1, h2⟩

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`promote_l` and `pl_arm` refine `promoteL` and its arm**, at every L fuel. -/
theorem pl_rel : ∀ n : Nat,
    (∀ (m : Mem) (a : AState) (pm : PMemo) (f h : Word) (r : List Word) (m' : Mem),
      ArenaD m a → PMemoR m pm → h.toNat < 2 ^ 32 →
      callW p n "promote_l" [f, h] m = some (r, m') →
      PLOk (promoteL pm f.toNat (decI h)) decI m a pm (r.headD 0) m') ∧
    (∀ (m : Mem) (a : AState) (pm : PMemo) (f h : Word) (r : List Word) (m' : Mem),
      ArenaD m a → PMemoR m pm → h.toNat < 2 ^ 32 →
      callW p n "pl_arm" [f, h] m = some (r, m') →
      PLOk (plArmT pm f.toNat (decI h)) decI m a pm (r.headD 0) m') := by
  intro n
  induction n with
  | zero =>
    exact ⟨fun _ _ _ _ _ _ _ _ _ _ hc => (by rw [callW_zero'] at hc; cases hc),
      fun _ _ _ _ _ _ _ _ _ _ hc => (by rw [callW_zero'] at hc; cases hc)⟩
  | succ n ih =>
  refine ⟨?_, ?_⟩
  · intro m a pm f h r m' hD hP hh hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (promoteL_spec p hp n ⟨m, Locals.init []⟩ f h) hc
    simp only at hW
    by_cases hf : f = 0
    · simp [plW, hf] at hW
    rw [toNat_pred f hf, promoteL_succ]
    unfold plStepT
    by_cases ht : tierW h = 0
    · rw [plW_pers p n m f h hf ht] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have hpers : (decI h : LIdx).isPersistent = true := PW.pers ⟨hh, ht⟩
      rw [ite_eq_left hpers, ← hr]
      exact ⟨a, pm, rfl, hD, hP, ⟨hh, ht⟩, rfl, MemFrame.refl _ _ _, rfl, rfl, SlKeep.refl _⟩
    have hnp : (decI h : LIdx).isPersistent = false := by
      rw [isPersistent_decI h hh]; exact beq_eq_false_iff_ne.mpr ht
    rw [ite_eq_right (by simp [hnp])]
    have hk : (hKey .level).ok h 0 := ⟨hh, rfl⟩
    by_cases h0 : mfindG plSch m h 0 = []
    · simp [plW, hf, ht, h0] at hW
    by_cases h1 : (mfindG plSch m h 0).headD 0 ≠ 0
    · obtain ⟨v, hv, hvr⟩ := memoRV_hit plSch (hKey .level) (VP .level) m pm.lM hP.l h 0 h0 h1 hk
      rw [plW_hit p n m f h hf ht h0 h1] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have hv' : pm.lM[decI h]? = some v := hv
      rw [hv']
      obtain ⟨rfl, hw1, hw2⟩ := hvr
      rw [← hr]
      exact ⟨_, pm, rfl, hD, hP, ⟨hw1, hw2⟩, rfl, MemFrame.refl _ _ _, rfl, rfl, SlKeep.refl _⟩
    have h1' : (mfindG plSch m h 0).headD 0 = 0 := by simpa using h1
    rw [plW_miss p n m f h hf ht h0 h1'] at hW
    have hmiss : pm.lM[decI h]? = none :=
      memoRV_miss plSch (hKey .level) (VP .level) m pm.lM hP.l h 0 hk h0 h1'
    rw [hmiss]
    cases hca : callW p n "pl_arm" [f - 1, h] m with
    | none => rw [hca] at hW; cases hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hca] at hW
    cases hs : msetG plSch m₁ h 0 (r₁.headD 0) with
    | none => simp only [memoK, hs] at hW; cases hW
    | some m₂ =>
    rw [memoK_some _ _ _ _ _ hs] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨a₁, pm₁, hrun, hD₁, hP₁, hpw, hcp, hfr, he, hls, hsk⟩ :=
      ih.2 m a pm (f - 1) h r₁ m₁ hD hP hh hca
    refine ⟨a₁, { pm₁ with lM := pm₁.lM.insert (decI h) (decI (r₁.headD 0)) }, ?_,
      hD₁.memo plSch plSch_wf (by decide) (by decide) (by decide) h _ hs,
      hP₁.setL h _ hh hpw hs, by rw [← hr]; exact hpw, hcp, ?_, he, hls,
      hsk.trans (SlKeep.of_frame (msetG_frame plSch plSch_wf _ _ _ _ _ hs) (by decide) (by decide))⟩
    · rw [run_bind_ok hrun, ← hr]; rfl
    · exact hfr.trans ((msetG_frame plSch plSch_wf _ _ _ _ _ hs).mono (by simp) (by simp))
  · intro m a pm f h r m' hD hP hh hc
    obtain ⟨s', rfl, -, hW⟩ := callW_triple (plArm_spec p hp n ⟨m, Locals.init []⟩ f h) hc
    simp only at hW
    have hh' : ¬ 4294967295 < h := fun e => by
      have : (4294967295 : Nat) < h.toNat := e
      omega
    by_cases hne : lvNodeW m h = []
    · simp [plArmW, hne] at hW
    rw [plArmW_eq p n m f h hh' hne] at hW
    obtain ⟨v, hv⟩ := lvNodeW_view hD.1 hh hne
    rw [lvNodeW_store hD.1 hh hv] at hW
    unfold plArmT
    have hv0 := viewL_run hv
    cases n with
    | zero => cases v <;> simp [plK, lvEnc, callW_zero', hd1, pl1K, pl2K] at hW
    | succ n =>
    cases v with
    | zero =>
      simp only [plK, lvEnc, List.headD_cons, ↓reduceIte] at hW
      refine PLOk.of_sim (Sim.bind_twin hv0 ?_) hW
      refine (Sim.hd1 (sim_pi (fun n s₀ => piZero_spec p hp n s₀) fun n _ _ h =>
        piZero_rel p hp n m a hD _ _ h)).mono ?_
      rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₁, hpw, hcp, hfr⟩
      exact ⟨rfl, hD₁, hP.frameLo (by simp [ZREC, ZSLOT]) (by simp) hfr, hpw, hcp,
        hfr.mono (by simp) (by simp), rfl, rfl, SlKeep.of_frame hfr (by decide) (by decide)⟩
    | succ u =>
      simp (config := { decide := true }) only [plK, lvEnc, List.headD_cons, List.tail_cons,
        ↓reduceIte] at hW
      refine PLOk.of_sim (Sim.bind_twin hv0 ?_) hW
      refine Sim.bindK rfl (fun _ _ => rfl) ((Sim.ofP (ih.1 m a pm f _ · · hD hP (word_lt u))).congr
        (by rw [decI_word])) ?_
      rintro r₁ ⟨pm₁, _⟩ m₁ a₁ ⟨rfl, hD₁, hP₁, hpw₁, hcp₁, hfr₁, he₁, hls₁, hsk₁⟩
      dsimp only [pl1K]
      refine (Sim.hd1 (sim_pi (fun n s₀ => piSucc_spec p hp n s₀ _) fun n _ _ h =>
        piSucc_rel p hp n m₁ a₁ hD₁ _ hpw₁ _ _ h)).mono ?_
      rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₂, hpw₂, hcp₂, hfr₂⟩
      exact ⟨rfl, hD₂, hP₁.frameLo (by simp [SREC, SSLOT, SHP]) (by simp) hfr₂, hpw₂,
        hcp₂.trans hcp₁, hfr₁.trans (hfr₂.mono (by simp) (by simp)), he₁, hls₁,
        hsk₁.trans (SlKeep.of_frame hfr₂ (by decide) (by decide))⟩
    | max u w =>
      simp (config := { decide := true }) only [plK, lvEnc, List.headD_cons, List.tail_cons,
        ↓reduceIte] at hW
      refine PLOk.of_sim (Sim.bind_twin hv0 ?_) hW
      refine Sim.bindK rfl (fun _ _ => rfl) ((Sim.ofP (ih.1 m a pm f _ · · hD hP (word_lt u))).congr
        (by rw [decI_word])) ?_
      rintro r₁ ⟨pm₁, _⟩ m₁ a₁ ⟨rfl, hD₁, hP₁, hpw₁, hcp₁, hfr₁, he₁, hls₁, hsk₁⟩
      dsimp only [pl2K]
      refine Sim.bindK rfl (fun _ _ => rfl) ((Sim.ofP (ih.1 m₁ a₁ pm₁ f _ · · hD₁ hP₁ (word_lt w))).congr
        (by rw [decI_word])) ?_
      rintro r₂ ⟨pm₂, _⟩ m₂ a₂ ⟨rfl, hD₂, hP₂, hpw₂, hcp₂, hfr₂, he₂, hls₂, hsk₂⟩
      dsimp only [pl2K.pl2K₂]
      refine (Sim.hd1 (sim_pi (fun n s₀ => piMax_spec p hp n s₀ _ _) fun n _ _ h =>
        piMax_rel p hp n m₂ a₂ hD₂ _ _ hpw₁ hpw₂ _ _ h)).mono ?_
      rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₃, hpw₃, hcp₃, hfr₃⟩
      exact ⟨rfl, hD₃, hP₂.frameLo (by simp [MREC, MSLOT, MHP]) (by simp) hfr₃, hpw₃,
        hcp₃.trans (hcp₂.trans hcp₁), (hfr₁.trans hfr₂).trans (hfr₃.mono (by simp) (by simp)),
        he₂.trans he₁, hls₂.trans hls₁,
        (hsk₁.trans hsk₂).trans (SlKeep.of_frame hfr₃ (by decide) (by decide))⟩
    | imax u w =>
      simp (config := { decide := true }) only [plK, lvEnc, List.headD_cons, List.tail_cons,
        ↓reduceIte] at hW
      refine PLOk.of_sim (Sim.bind_twin hv0 ?_) hW
      refine Sim.bindK rfl (fun _ _ => rfl) ((Sim.ofP (ih.1 m a pm f _ · · hD hP (word_lt u))).congr
        (by rw [decI_word])) ?_
      rintro r₁ ⟨pm₁, _⟩ m₁ a₁ ⟨rfl, hD₁, hP₁, hpw₁, hcp₁, hfr₁, he₁, hls₁, hsk₁⟩
      dsimp only [pl2K]
      refine Sim.bindK rfl (fun _ _ => rfl) ((Sim.ofP (ih.1 m₁ a₁ pm₁ f _ · · hD₁ hP₁ (word_lt w))).congr
        (by rw [decI_word])) ?_
      rintro r₂ ⟨pm₂, _⟩ m₂ a₂ ⟨rfl, hD₂, hP₂, hpw₂, hcp₂, hfr₂, he₂, hls₂, hsk₂⟩
      dsimp only [pl2K.pl2K₂]
      refine (Sim.hd1 (sim_pi (fun n s₀ => piImax_spec p hp n s₀ _ _) fun n _ _ h =>
        piImax_rel p hp n m₂ a₂ hD₂ _ _ hpw₁ hpw₂ _ _ h)).mono ?_
      rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₃, hpw₃, hcp₃, hfr₃⟩
      exact ⟨rfl, hD₃, hP₂.frameLo (by simp [IREC, ISLOT, IHP]) (by simp) hfr₃, hpw₃,
        hcp₃.trans (hcp₂.trans hcp₁), (hfr₁.trans hfr₂).trans (hfr₃.mono (by simp) (by simp)),
        he₂.trans he₁, hls₂.trans hls₁,
        (hsk₁.trans hsk₂).trans (SlKeep.of_frame hfr₃ (by decide) (by decide))⟩
    | param x =>
      simp (config := { decide := true }) only [plK, lvEnc, List.headD_cons, List.tail_cons,
        ↓reduceIte] at hW
      refine PLOk.of_sim (Sim.bind_twin hv0 ?_) hW
      refine Sim.bindK rfl (fun _ _ => rfl) ((Sim.ofP ((pn_rel p hp (n + 1)).1 m a pm f _ · · hD hP
        (word_lt x))).congr (by rw [decI_word])) ?_
      rintro r₁ ⟨pm₁, _⟩ m₁ a₁ ⟨rfl, hD₁, hP₁, hpw₁, hcp₁, hfr₁, he₁, hl₁, hls₁, hsk₁⟩
      dsimp only [pl1K]
      refine (Sim.hd1 (sim_pi (fun n s₀ => piParam_spec p hp n s₀ _) fun n _ _ h =>
        piParam_rel p hp n m₁ a₁ hD₁ _ hpw₁ _ _ h)).mono ?_
      rintro _ ⟨_, _⟩ _ _ ⟨rfl, rfl, hD₂, hpw₂, hcp₂, hfr₂⟩
      exact ⟨rfl, hD₂, hP₁.frameLo (by simp [PREC, PSLOT]) (by simp) hfr₂, hpw₂,
        hcp₂.trans hcp₁, (nFrame_l hfr₁).trans (hfr₂.mono (by simp) (by simp)), he₁, hls₁,
        hsk₁.trans (SlKeep.of_frame hfr₂ (by decide) (by decide))⟩

/-- **`promote_l` refines `promoteL`** (`PLOk`). -/
@[refines ConRon.Arena.promoteL]
theorem promoteL_refines (n : Nat) (s₀ : St) (a₀ : AState) (pm : PMemo) (f h : Word)
    (hD : ArenaD s₀.mem a₀) (hP : PMemoR s₀.mem pm) (hh : h.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "promote_l" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      PLOk (promoteL pm f.toNat (decI h)) decI s₀.mem a₀ pm (r.headD 0) s'.mem; ⊤⦄ :=
  triple_post (callW_spec p n "promote_l" [f, h] s₀) fun _ _ ⟨hl, hc⟩ =>
    ⟨hl, (pl_rel p hp n).1 _ _ _ _ _ _ _ hD hP hh hc⟩

end rel

end L.Arena
