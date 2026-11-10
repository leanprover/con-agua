module

public import ConAgua.Arena.IndPosSpec.NcnW
import ConAgua.Arena.IndPosSpec.NestContParamsClosed
import ConAgua.Arena.IndSumSpec.StructUsedHb
public import ConAgua.Arena.IndPosSpec.P2ctK1
public import ConAgua.Arena.IndPosSpec.NestGroupCtors
public import ConAgua.Arena.IndPosSpec.NestHoles
import ConAgua.Arena.IndPosSpec.PosmemoRxMfr
import ConAgua.Arena.RecClassSpec.Classes
public import ConAgua.Arena.IndPosSpec.FgW2

@[expose] public section

/-!
# The `abstract1` memo across the positivity check's models (lane `indproofs4`, helper `abs`)

`AFr` (`IndRealAbs.lean`) for the models of the positivity check's callees, mirroring their `MFr`
frames (`IndPosSpec/DepthGo`, `IndPosSpec/RpGoStep`‥`M`, `IndPosSpec/NestCrest`), proved by `afr_auto` from the callees'.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem fvbF_afr {m m' : Mem} {args r : List Word} (h : fvbF m args = some (r, m')) : AFr m m' :=
  AFr.of_frame (fvbF_frame h)

theorem cvLpsA_afr {n : Nat} {m m' : Mem} {q : Word} {r : List Word} (h : L.Arena.cvLpsW n m q = some (r, m')) :
    AFr m m' := by
  cases n with
  | zero => simp [L.Arena.cvLpsW] at h
  | succ n => exact erToIwW_afr h

theorem bvbW_afr {n : Nat} {m m' : Mem} {h f x : Word} (hb : bvbW n m h f = some (x, m')) : AFr m m' := by
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
  exact AFr.of_frame hfr

theorem canonW_afr (n : Nat) {m m' : Mem} {no nl us nn c v : Word} {r : List Word}
    (h : canonW n m no nl us nn c v = some (r, m')) : AFr m m' := by
  cases n with
  | zero => simp [canonW] at h
  | succ n =>
  unfold canonW canonK0 canonK1 canonK2 canonK3 at h
  afr_auto h [sointernW_afr, fvinternW_afr]

theorem ahW_afr {n : Nat} {m m' : Mem} {no nl us b nn e : Word} {r : List Word}
    (h : ahWf (n + 1) m no nl us b nn e = some (r, m')) : AFr m m' := by
  simp only [ahWf, ahWf.k_ph_app.eq_def, ahWf.k_nest_canon_sub.eq_def] at h
  afr_auto h [canonW_afr n]

-- from IndPosSpec/DepthGo
theorem posRecW_afr {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m')) :
    AFr m m' := by
  simp only [posRecW] at h
  split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  exact (allocW_afr ‹_›).trans (AFr.iw (wrIW_frame _ _ _))

-- from IndPosSpec/DepthGo
theorem phsGoW_afr (k : Nat) : ∀ (m m' : Mem) (q n i : Word), phsGoW k m q n i = some m' → AFr m m' := by
  induction k with
  | zero => intro m m' q n i h; simp [phsGoW.eq_1] at h
  | succ k ih =>
    intro m m' q n i h
    simp only [phsGoW.eq_2, phsGoW.k_pin_word.eq_def, phsGoW.k_intern_sort.eq_def, phsGoW.k_intern_fvar.eq_def,
      phsGoW.k_nest_phs_go_id] at h
    afr_auto h [sointernW_afr, fvinternW_afr, fun h => (set64IW_afr _ _ _).trans (ih _ _ _ _ _ h)]

-- from IndPosSpec/DepthGo
theorem phsW_afr {k : Nat} {m m' : Mem} {nn : Word} {r : List Word} (h : phsW k m nn = some (r, m')) : AFr m m' := by
  simp only [phsW.arm1, phsW.k_iw_alloc.eq_def, phsW.k_nest_phs_go.eq_def] at h
  afr_auto h [allocW_afr, phsGoW_afr k _ _ _ _ _]

-- from IndPosSpec/DepthGo
theorem rpMkW_afr {m m' : Mem} {g a2 x2 c2 y x r : Word} (h : rpMkW m g a2 x2 c2 y x = some (r, m')) : AFr m m' := by
  unfold rpMkW at h
  afr_auto h [mkAppW_afr, mkLamW_afr, mkForallW_afr, mkLetW_afr, mkProjW_afr]

theorem msetG_afrS {S : MemoSch} (hS : S.WF) (ha : memoFreeA [S.arr] = true) (hc : memoFreeC [S.cs + 1] = true)
    {m m' : Mem} {k1 k2 v : Word} (h : msetG S m k1 k2 v = some m') : AFr m m' :=
  AFr.of_frame (msetG_frame S hS m m' k1 k2 v h) ha hc

theorem mclearG_afrS (S : MemoSch) (hc : memoFreeC [S.cs, S.cs + 1] = true) (m : Mem) :
    AFr m (mclearG S m) :=
  AFr.of_frame (mclearG_frame S m) rfl hc

-- from IndPosSpec/DepthGo
theorem rpGoW_afr (n : Nat) :
    (∀ (m m' : Mem) (no nl us b nn f h r : Word), rpGoW n m no nl us b nn f h = some (r, m') → AFr m m') ∧
    (∀ (m m' : Mem) (no nl us b nn f1 h g x y z r : Word),
      rpNodeW n m no nl us b nn f1 h g x y z = some (r, m') → AFr m m') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ _ h => by simp [rpGoW] at h,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [rpNodeW] at h⟩
  | succ j =>
  have ahF : ∀ {m m' : Mem} {no nl us b nn e : Word} {rr : List Word},
      ahWf j m no nl us b nn e = some (rr, m') → AFr m m' := by
    intro m m' no nl us b nn e rr h
    cases j with
    | zero => simp [ahWf] at h
    | succ i => exact ahW_afr h
  have ndF : ∀ {m m' : Mem} {no nl us b nn f1 h g x y z r : Word},
      rpNodeW j m no nl us b nn f1 h g x y z = some (r, m') → AFr m m' := by
    intro m m' no nl us b nn f1 h g x y z r hn
    cases j with
    | zero => simp [rpNodeW] at hn
    | succ i => exact (ih (i + 1) (by omega)).2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn
  refine ⟨fun m m' no nl us b nn f h r hg => ?_, fun m m' no nl us b nn f1 h g x y z r hn => ?_⟩
  · simp only [rpGoW] at hg
    split at hg; · cases hg
    simp only [rpG1] at hg
    split at hg; · cases hg
    split at hg; · rw [← (Prod.mk.inj (Option.some.inj hg)).2]; exact AFr.refl _
    split at hg
    · rcases ha : ahWf j m no nl us b nn h with _ | ⟨rr, m1⟩ <;> rw [ha] at hg; · cases hg
      rw [rpH_some] at hg; rw [← (Prod.mk.inj (Option.some.inj hg)).2]; exact ahF ha
    simp only [rpG3] at hg
    split at hg; · cases hg
    split at hg; · rw [← (Prod.mk.inj (Option.some.inj hg)).2]; exact AFr.refl _
    simp only [rpG4.eq_def, rpG5.eq_def] at hg
    split at hg; · cases hg
    rename_i hn; split at hg; · cases hg
    rename_i hs; rw [← (Prod.mk.inj (Option.some.inj hg)).2]; exact (ndF hn).trans (msetG_afrS raSch_wf rfl rfl hs)
  · simp only [rpNodeW, rpA1.eq_def, rpB1.eq_def, rpB2.eq_def, rpL1.eq_def, rpL2.eq_def, rpL3.eq_def,
      rpP1.eq_def] at hn
    have ihG := (ih j (by omega)).1
    afr_auto hn [ahF, ihG _ _ _ _ _ _ _ _ _ _, rpMkW_afr]

-- from IndPosSpec/DepthGo
theorem rpConstW_afr {n : Nat} {m m' : Mem} {no nl us b nn e r : Word}
    (h : rpConstW n m no nl us b nn e = some (r, m')) : AFr m m' := by
  simp only [rpConstW, rpClrK.eq_def] at h
  split at h; · cases h
  split at h; · cases h
  rename_i hg; split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
  exact ((mclearG_afrS raSch rfl m).trans ((rpGoW_afr n).1 _ _ _ _ _ _ _ _ _ _ hg)).trans (mclearG_afrS raSch rfl _)

-- from IndPosSpec/DepthGo
theorem pccW_afr {k : Nat} {m m' : Mem} {no nl us nn cty : Word} {r : List Word}
    (h : pccW k m no nl us nn cty = some (r, m')) : AFr m m' := by
  simp only [pccW, pccA.eq_def, pccB.eq_def, pccC.eq_def] at h
  afr_auto h [phsW_afr, instW_afr _ _ _ _ _ _ _, rpConstW_afr]

-- from IndPosSpec/DepthGo
theorem posmemo_rx_afr (n : Nat) :
    (∀ (m m' : Mem) (f i a b : Word), rxMapW n m f i = some (a, b, m') → AFr m m') ∧
    (∀ (m m' : Mem) (ctx po pl nn i a b : Word), rxImgW n m ctx po pl nn i = some (a, b, m') → AFr m m') ∧
    (∀ (m m' : Mem) (ctx po pl n1 i a b : Word), rxFrameW n m ctx po pl n1 i = some (a, b, m') → AFr m m') ∧
    (∀ (m m' : Mem) (f o l a b : Word), rxDsW n m f o l = some (a, b, m') → AFr m m') ∧
    (∀ (m m' : Mem) (f o l q j : Word), rxDsGoW n m f o l q j = some m' → AFr m m') ∧
    (∀ (m m' : Mem) (f e r : Word), rxW n m f e = some (r, m') → AFr m m') ∧
    (∀ (m m' : Mem) (f fu h r : Word), rxGoW n m f fu h = some (r, m') → AFr m m') ∧
    (∀ (m m' : Mem) (f f1 g x y z r : Word), rxNodeW n m f f1 g x y z = some (r, m') → AFr m m') := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [rxMapW, rxImgW, rxFrameW, rxDsW, rxDsGoW, rxW, rxGoW, rxNodeW]
  | succ n ih =>
  obtain ⟨iMap, iImg, iFr, iDs, iDsGo, iRx, iGo, iNode⟩ := ih
  have pfr : ∀ (m m' : Mem) (ctx po pl n1 h a b : Word),
      pfrK1 n ctx po pl n1 (some (h, m)) = some (a, b, m') → AFr m m' := by
    intro m m' ctx po pl n1 h a b hh
    simp only [pfrK1, pfrK2.eq_def, pfrK3.eq_def, frK4.eq_def, frK5.eq_def] at hh
    afr_auto hh [posRecW_afr, iDs _ _ _ _ _ _ _, ceinternW_afr, mknF_afr]
    simp only [Option.some.injEq, Prod.mk.injEq] at hh; obtain ⟨-, -, rfl⟩ := hh; exact AFr.refl _
  refine ⟨fun m m' f i a b hh => ?_, fun m m' ctx po pl nn i a b hh => ?_,
    fun m m' ctx po pl n1 i a b hh => ?_, fun m m' f o l a b hh => ?_, fun m m' f o l q j hh => ?_,
    fun m m' f e r hh => ?_, fun m m' f fu h r hh => ?_, fun m m' f f1 g x y z r hh => ?_⟩
  · simp only [rxMapW, erK1.eq_def, erK2.eq_def, erK3.eq_def] at hh
    afr_auto hh [iImg _ _ _ _ _ _ _ _ _, sointernW_afr, fvinternW_afr]
    all_goals simp only [Option.some.injEq, Prod.mk.injEq] at hh; obtain ⟨-, -, rfl⟩ := hh; exact AFr.refl _
  · simp only [rxImgW, rxRootW, rtK1.eq_def, rtK2.eq_def] at hh
    afr_auto hh [iImg _ _ _ _ _ _ _ _ _, iFr _ _ _ _ _ _ _ _ _, ceinternW_afr, mknF_afr]
    all_goals simp only [Option.some.injEq, Prod.mk.injEq] at hh; obtain ⟨-, -, rfl⟩ := hh; exact AFr.refl _
  · simp only [rxFrameW, frK0.eq_def] at hh
    split at hh; · exact pfr _ _ _ _ _ _ _ _ _ hh
    split at hh; · cases hh
    rename_i h1; rcases h2 : posRecW _ [_, 0] with _ | ⟨k, m2⟩ <;> rw [h2] at hh; · simp [pfrK1] at hh
    exact ((posRecW_afr h1).trans (posRecW_afr h2)).trans (pfr _ _ _ _ _ _ _ _ _ hh)
  · simp only [rxDsW, dsA.eq_def, dsB.eq_def] at hh
    afr_auto hh [allocW_afr, iDsGo _ _ _ _ _ _ _]
    simp only [Option.some.injEq, Prod.mk.injEq] at hh; obtain ⟨-, -, rfl⟩ := hh; exact AFr.refl _
  · simp only [rxDsGoW, dgK.eq_def] at hh
    afr_auto hh [iRx _ _ _ _ _, fun h => (set64IW_afr _ _ _).trans (iDsGo _ _ _ _ _ _ _ h)]
  · simp only [rxW, rxK1.eq_def, rxK2] at hh
    refine (AFr.of_frame (benterG_frame 218 m)).trans ?_
    afr_auto hh [iGo _ _ _ _ _ _]
  · simp only [rxGoW] at hh
    split at hh; · cases hh
    simp only [rxG1] at hh
    split at hh; · cases hh
    split at hh; · rw [← (Prod.mk.inj (Option.some.inj hh)).2]; exact AFr.refl _
    split at hh
    · rcases hm : rxMapW n m f _ with _ | ⟨ok, r1, m1⟩ <;> rw [hm] at hh; · cases hh
      rw [rxH_some] at hh; rw [← (Prod.mk.inj (Option.some.inj hh)).2]; exact iMap _ _ _ _ _ _ hm
    simp only [rxG3] at hh
    split at hh; · cases hh
    split at hh; · rw [← (Prod.mk.inj (Option.some.inj hh)).2]; exact AFr.refl _
    simp only [rxG4.eq_def, rxG5.eq_def] at hh
    split at hh; · cases hh
    rename_i hn; split at hh; · cases hh
    rename_i hs; rw [← (Prod.mk.inj (Option.some.inj hh)).2]
    exact (iNode _ _ _ _ _ _ _ _ _ hn).trans (msetG_afrS rfSch_wf rfl rfl hs)
  · simp only [rxNodeW, rxB1.eq_def, rxB2.eq_def, rxL1.eq_def, rxL2.eq_def, rxL3.eq_def, rxP1.eq_def] at hh
    afr_auto hh [iGo _ _ _ _ _ _, rpMkW_afr]

-- from IndPosSpec/DepthGo
theorem rxW_afr {n : Nat} {m m' : Mem} {f e r : Word} (h : rxW n m f e = some (r, m')) : AFr m m' :=
  (posmemo_rx_afr n).2.2.2.2.2.1 _ _ _ _ _ h

-- from IndPosSpec/DepthGo
theorem rxDsW_afr {n : Nat} {m m' : Mem} {f o l a b : Word} (h : rxDsW n m f o l = some (a, b, m')) : AFr m m' :=
  (posmemo_rx_afr n).2.2.2.1 _ _ _ _ _ _ _ h

-- from IndPosSpec/NtyW

-- from IndPosSpec/NtyW

-- from IndPosSpec/FgW
theorem nagW_afr : ∀ (n : Nat) (m m' : Mem) (us dO dL gO gL kO kL : Word) (r : List Word),
    nagW n m us dO dL gO gL kO kL = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [nagW.eq_1] at h
  | n + 1, m, m', us, dO, dL, gO, gL, kO, kL, r, h => by
    simp only [nagW.eq_2, nagW.k_rec4.eq_def, nagW.k_nest_keys_contains.eq_def, nagW.k_sl_snoc.eq_def,
      nagW.k_nest_accept_group.eq_def] at h
    afr_auto h [posRecW_afr, snocW_afr, nagW_afr n _ _ _ _ _ _ _ _ _ _]

-- from IndPosSpec/FgW
theorem matesW_afr : ∀ (n : Nat) (m m' : Mem) (c off l oO oL : Word) (r : List Word),
    matesW n m c off l oO oL = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, h => by simp [matesW.eq_1] at h
  | n + 1, m, m', c, off, l, oO, oL, r, h => by
    simp only [matesW.eq_2, matesW.k_sl_contains.eq_def, matesW.k_sl_snoc.eq_def,
      matesW.k_nest_frame_mates_go.eq_def] at h
    afr_auto h [snocW_afr, matesW_afr n _ _ _ _ _ _ _ _]

-- from IndPosSpec/FgW
theorem nboW_afr {p : Prog} (hg : p.lookup "env_row_get" = some envRowGetL)
    (hb : p.lookup "base_row_get" = some baseRowGetL) (hp : p.lookup "env_find" = some envFindL)
    {n : Nat} {m m' : Mem} {vis c : Word} {r : List Word} (h : nboW p n m vis c = some (r, m')) :
    AFr m m' := by
  rw [nboW_mem hg hb hp h]; exact AFr.refl _

theorem nfmW_afr {p : Prog} (hg : p.lookup "env_row_get" = some envRowGetL)
    (hb : p.lookup "base_row_get" = some baseRowGetL) (hp : p.lookup "env_find" = some envFindL)
    {n : Nat} {m m' : Mem} {vis c : Word} {r : List Word} (h : nfmW p n m vis c = some (r, m')) :
    AFr m m' := by
  cases n with
  | zero => simp [nfmW.eq_1] at h
  | succ n =>
  simp only [nfmW.arm1, nfmW.k_nest_block_of.eq_def, nfmW.k_nest_frame_mates_go.eq_def] at h
  afr_auto h [nboW_afr hg hb hp, matesW_afr _ _ _ _ _ _ _ _ _]

-- from IndPosSpec/FgW
theorem fhW_afr : ∀ (n : Nat) (m m' : Mem) (hi gO gL aO aL : Word) (r : List Word),
    fhW n m hi gO gL aO aL = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, h => by simp [fhW] at h
  | n + 1, m, m', hi, gO, gL, aO, aL, r, h => by
    unfold fhW fhK1 fhK2 at h
    afr_auto h [fvinternW_afr, snocW_afr, fhW_afr n _ _ _ _ _ _ _ _]

-- from IndPosSpec/FgW
theorem caW_afr : ∀ (n : Nat) (m m' : Mem) (us dO dL gO gL aO aL : Word) (r : List Word),
    caW n m us dO dL gO gL aO aL = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [caW] at h
  | n + 1, m, m', us, dO, dL, gO, gL, aO, aL, r, h => by
    unfold caW caK1 caK2 at h
    afr_auto h [posRecW_afr, snocW_afr, caW_afr n _ _ _ _ _ _ _ _ _ _]

-- from IndPosSpec/FgW
theorem new1W_afr {m m' : Mem} {x : Word} {r : List Word} (h : new1W m x = some (r, m')) : AFr m m' :=
  posRecW_afr (new1W_rec h).1

-- from IndPosSpec/FgW
theorem cpW_afr : ∀ (n : Nat) (m m' : Mem) (hp dO dL : Word) (r : List Word),
    cpW n m hp dO dL = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [cpW.eq_1] at h
  | n + 1, m, m', hp, dO, dL, r, h => by
    simp only [cpW.eq_2, cpW.k_bvar_b.eq_def, cpW.k_fvar_b.eq_def, cpW.k_nest_cont_params_closed.eq_def] at h
    afr_auto h [bvbW_afr, fvbF_afr, cpW_afr n _ _ _ _ _ _]

-- from IndPosSpec/NestCrest
theorem piBW_afr : ∀ (n : Nat) (m m' : Mem) (fuel h : Word) (r : List Word), piBW n m fuel h = some (r, m') →
    AFr m m'
  | 0, _, _, _, _, _, hh => by simp [piBW] at hh
  | n + 1, m, m', fuel, h, r, hh => by
    simp only [piBW, piBK1, piBK2.eq_def, piBK3.eq_def] at hh
    afr_auto hh [piBW_afr n _ _ _ _ _, consW_afr]

-- from IndPosSpec/FgW
theorem fgW_afr : ∀ (n : Nat) (m m' : Mem) (hi us dO dL gO gL pO pL nO nL : Word) (r : List Word),
    fgW n m hi us dO dL gO gL pO pL nO nL = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [fgW] at h
  | n + 1, m, m', hi, us, dO, dL, gO, gL, pO, pL, nO, nL, r, h => by
    unfold fgW fgK1 fgKb fgK2 fgK3 fgK4 at h
    afr_auto h [posRecW_afr, piBW_afr _ _ _ _ _ _, snocW_afr, fgW_afr n _ _ _ _ _ _ _ _ _ _ _ _ _]

-- from IndPosSpec/NestCrest
theorem stripW_afr {m m' : Mem} {ciq : Word} {r : List Word} (h : stripW m ciq = some (r, m')) : AFr m m' := by
  simp only [stripW.eq_1, stripW.k_strip_pis.eq_def] at h
  afr_auto h [stripF_afr]

-- from IndPosSpec/NestCrest
theorem entryW_afr {m m' : Mem} {C ciq : Word} {r : List Word} (h : entryW m C ciq = some (r, m')) :
    AFr m m' := by
  simp only [entryW.eq_1, entryW.k_nest_ctor_entry_strip.eq_def, entryW.k_get_app_fn_f.eq_def] at h
  afr_auto h [stripW_afr, stub_afr, i1F_afr, gafF_afr]

-- from IndPosSpec/NestCrest
theorem ncGoW_afr : ∀ (k : Nat) (m m' : Mem) (vis C co cl cs ol fp : Word) (r : List Word),
    ncGoW k m vis C co cl cs ol fp = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [ncGoW.eq_1] at h
  | k + 1, m, m', vis, C, co, cl, cs, ol, fp, r, h => by
    simp only [ncGoW.eq_2, ncGoW.k_nest_ctor_entry.eq_def, ncGoW.k_rec2.eq_def, ncGoW.j2.eq_1, ncGoW.j1.eq_1,
      ncGoW.k_nest_container_ctors_go.eq_def] at h
    afr_auto h [ncGoW_afr k _ _ _ _ _ _ _ _ _ _, entryW_afr, posRecW_afr,
      fun h => (set64IW_afr _ _ _).trans (ncGoW_afr k _ _ _ _ _ _ _ _ _ _ h)]

-- from IndPosSpec/NestCrest
theorem ncWf_afr {k : Nat} {m m' : Mem} {vis C co cl : Word} {r : List Word} (h : ncWf k m vis C co cl = some (r, m')) :
    AFr m m' := by
  cases k with
  | zero => simp [ncWf.eq_1] at h
  | succ k =>
  simp only [ncWf.arm1, ncWf.k_iw_alloc.eq_def, ncWf.k_nest_container_ctors_go.eq_def] at h
  afr_auto h [allocW_afr, ncGoW_afr _ _ _ _ _ _ _ _ _ _ _]

-- from IndPosSpec/NestCrest
theorem ntWf_afr {k : Nat} {m m' : Mem} {vis C : Word} {r : List Word} (h : ntWf k m vis C = some (r, m')) :
    AFr m m' := by
  cases k with
  | zero => simp [ntWf.eq_1] at h
  | succ k =>
  simp only [ntWf.eq_2, ntWf.k_nest_container_ctors.eq_def] at h
  afr_auto h [ncWf_afr]

-- from IndPosSpec/NestCrest
theorem dcGoW_afr : ∀ (n : Nat) (m m' : Mem) (hi off l : Word) (r : List Word),
    dcGoW n m hi off l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [dcGoW.eq_1] at h
  | n + 1, m, m', hi, off, l, r, h => by
    simp only [dcGoW.eq_2, dcGoW.k_fvar_b.eq_def, dcGoW.k_nest_ds_closed_go.eq_def] at h
    afr_auto h [fvbF_afr, dcGoW_afr n _ _ _ _ _ _]

-- from IndPosSpec/NestCrest
theorem dcWf_afr {n : Nat} {m m' : Mem} {ctx off l : Word} {r : List Word} (h : dcWf n m ctx off l = some (r, m')) :
    AFr m m' := by
  cases n with
  | zero => simp [dcWf.eq_1] at h
  | succ n =>
    simp only [dcWf.eq_2, dcWf.k_nest_ds_closed_go.eq_def] at h
    afr_auto h [dcGoW_afr _ _ _ _ _ _ _]

-- from IndPosSpec/NestCrest
theorem nwsW_afr {n : Nat} {m m' : Mem} {ctx off l po pl : Word} {r : List Word}
    (h : nwsWf (n + 1) m ctx off l po pl = some (r, m')) : AFr m m' := by
  simp only [nwsWf.eq_2, nwsWf.k_nest_ds_closed.eq_def] at h
  afr_auto h [dcWf_afr]

-- from IndPosSpec/NestCrest
theorem rhGoW_afr : ∀ (k : Nat) (m m' : Mem) (no nl lv po pl nP nio nil q j : Word),
    rhGoW k m no nl lv po pl nP nio nil q j = some m' → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [rhGoW.eq_1] at h
  | k + 1, m, m', no, nl, lv, po, pl, nP, nio, nil, q, j, h => by
    simp only [rhGoW.eq_2, rhGoW.k_rec4.eq_def, rhGoW.k_rec3.eq_def, rhGoW.k_nest_ctx_root_holes_go_id] at h
    afr_auto h [posRecW_afr, fun h => (set64IW_afr _ _ _).trans (rhGoW_afr k _ _ _ _ _ _ _ _ _ _ _ _ h)]

-- from IndPosSpec/NestCrest
theorem haW_afr {k : Nat} {m m' : Mem} {ctx po pl i : Word} {r : List Word}
    (h : haWf (k + 1) m ctx po pl i = some (r, m')) : AFr m m' := by
  have rh : ∀ {m m' : Mem} {ctx : Word} {r : List Word}, rhWf k m ctx = some (r, m') → AFr m m' := by
    intro m m' ctx r h
    cases k with
    | zero => simp [rhWf.eq_1] at h
    | succ k =>
    simp only [rhWf.arm1, rhWf.k_iw_alloc.eq_def, rhWf.k_nest_ctx_root_holes_go.eq_def] at h
    afr_auto h [allocW_afr, rhGoW_afr _ _ _ _ _ _ _ _ _ _ _ _ _]
  simp only [haWf.eq_2, haWf.k_nest_ctx_root_holes.eq_def, haWf.k_sl_append.eq_def] at h
  afr_auto h [rh, appendW_afr]

-- from IndPosSpec/NestCrest
theorem resHeadW_afr {m m' : Mem} {e : Word} {r : List Word} (h : resHeadW m e = some (r, m')) : AFr m m' := by
  simp only [resHeadW.eq_1, resHeadW.k_get_app_fn_f.eq_def] at h
  afr_auto h [stub_afr, i1F_afr, gafF_afr]

/-- The `has_loose_bvar_b` walk keeps `AbsOK`: its write set (`hbFastW_frame`) is the `hb` memo's
and the `BMEMO` walk's, and it keeps the `hb` memo well formed (`hbFastW_keep`). -/
theorem hbFastW_afr {n : Nat} {m m' : Mem} {i e r : Word} (h : hbFastW n m i e = some (r, m')) : AFr m m' :=
  fun hA => hA.frameHb (hbFastW_frame h) (by decide) (by decide) (hbFastW_keep h hA.hb)

-- from IndPosSpec/NestCrest
theorem ncnW_afr {k : Nat} {m m' : Mem} {ctx po pl us dO dL cv closed r : Word}
    (h : ncnW k m ctx po pl us dO dL cv closed = some (r, m')) : AFr m m' := by
  simp only [ncnW.arm1, ncnW.k_rec5.eq_def, ncnW.k_nest_hole_img_ds.eq_def, ncnW.k_replace_fvars.eq_def] at h
  afr_auto h [posRecW_afr, rxDsW_afr, rxW_afr]

-- from IndPosSpec/NestCrest
theorem pcrW_afr {k : Nat} {m m' : Mem} {no nl us dO dL hO hL cty : Word} {r : List Word}
    (h : pcrW k m no nl us dO dL hO hL cty = some (r, m')) : AFr m m' := by
  unfold pcrW pcrK1 pcrK2 pcrK3 at h
  afr_auto h [pccW_afr, posRecW_afr, rxW_afr]

/-! ## The walks' memos -/

theorem noW_afr (n : Nat) :
    (∀ (m m' : Mem) (no nl lo hi f h r : Word), noGoW n m no nl lo hi f h = some (r, m') → AFr m m') ∧
    (∀ (m m' : Mem) (no nl lo hi f1 g x y z r : Word), noNodeW n m no nl lo hi f1 g x y z = some (r, m') →
      AFr m m') := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ h => by simp [noGoW] at h,
      fun _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [noNodeW] at h⟩
  | succ n ih =>
    refine ⟨fun m m' no nl lo hi f h r hh => ?_, fun m m' no nl lo hi f1 g x y z r hh => ?_⟩
    · simp only [noGoW, noG1, noG3, noG4.eq_def, noG5.eq_def, noC.eq_def] at hh
      afr_auto hh [ih.2 _ _ _ _ _ _ _ _ _ _ _ _, msetG_afrS noSch_wf rfl rfl]
    · simp only [noNodeW, noB1.eq_def, noL1.eq_def, noL2.eq_def] at hh
      afr_auto hh [ih.1 _ _ _ _ _ _ _ _ _]

theorem noConstWf_afr {n : Nat} {m m' : Mem} {no nl lo hi e r : Word}
    (h : noConstWf n m no nl lo hi e = some (r, m')) : AFr m m' := by
  cases n with
  | zero => simp [noConstWf] at h
  | succ n =>
  simp only [noConstWf, noConstW] at h
  split at h; · cases h
  refine (mclearG_afrS noSch rfl m).trans ?_
  rcases hg : noGoW n (mclearG noSch m) no nl lo hi CWF e with _ | ⟨r1, m1⟩; · rw [hg] at h; simp [noClrK] at h
  rw [hg] at h; simp only [noClrK] at h
  split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact ((noW_afr n).1 _ _ _ _ _ _ _ _ _ hg).trans (mclearG_afrS noSch rfl m1)

/-- `pi_doms_occ` keeps `AbsOK`. -/
theorem pdoW_afr : ∀ (k : Nat) (m m' : Mem) (no nl lo hi n e : Word) (r : List Word),
    pdoW k m no nl lo hi n e = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [pdoW] at h
  | k + 1, m, m', no, nl, lo, hi, n, e, r, h => by
    simp only [pdoW, pdoK1.eq_def] at h
    afr_auto h [noConstWf_afr, pdoW_afr k _ _ _ _ _ _ _ _ _]

/-- **`AbsOK` across `nest_uniform_ok`'s callees** (`nuW_ok`'s last conclusion). -/
theorem nuAfr : NuAfr :=
  ⟨fun _ _ _ _ _ _ _ _ _ h => pccW_afr h, pdoW_afr, fun _ _ _ _ _ _ _ _ _ h => noConstWf_afr h⟩

theorem dpW_afr (n : Nat) :
    (∀ (m m' : Mem) (f h r : Word), dpGoW n m f h = some (r, m') → AFr m m') ∧
    (∀ (m m' : Mem) (f1 g x y z r : Word), dpNodeW n m f1 g x y z = some (r, m') → AFr m m') := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ h => by simp [dpGoW] at h, fun _ _ _ _ _ _ _ _ h => by simp [dpNodeW] at h⟩
  | succ n ih =>
    refine ⟨fun m m' f h r hh => ?_, fun m m' f1 g x y z r hh => ?_⟩
    · simp only [dpGoW, dpG1, dpG3, dpG4.eq_def, dpG5.eq_def] at hh
      afr_auto hh [ih.2 _ _ _ _ _ _ _ _, msetG_afrS dpSch_wf rfl rfl]
    · simp only [dpNodeW, dpB1.eq_def, dpB2.eq_def, dpL1.eq_def, dpL2.eq_def, dpL3.eq_def, dpP1.eq_def, dpFin] at hh
      afr_auto hh [ih.1 _ _ _ _ _]

theorem wfW_afr {n : Nat} {m m' : Mem} {e r : Word} (h : wfW n m e = some (r, m')) : AFr m m' := by
  simp only [wfW, dpConstW] at h
  split at h; · cases h
  rename_i x heq
  split at heq; · cases heq
  revert heq
  rcases hg : dpGoW n (mclearG dpSch m) CWF e with _ | ⟨r1, m1⟩; · simp [dpConstW.k_depth_go]
  simp only [dpConstW.k_depth_go]
  intro heq
  split at heq; · cases heq
  simp only [Option.some.injEq, Prod.mk.injEq] at heq; obtain ⟨-, rfl⟩ := heq
  split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact ((mclearG_afrS dpSch rfl m).trans ((dpW_afr n).1 _ _ _ _ _ hg)).trans (mclearG_afrS dpSch rfl m1)

theorem noaW_afr : ∀ (k : Nat) (m m' : Mem) (no nl lo hi off l : Word) (r : List Word),
    noaW k m no nl lo hi off l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [noaW.eq_1] at h
  | k + 1, m, m', no, nl, lo, hi, off, l, r, h => by
    simp only [noaW.eq_2, noaW.k_nest_occ.eq_def, noaW.k_nest_occ_any.eq_def] at h
    afr_auto h [noConstWf_afr, noaW_afr k _ _ _ _ _ _ _ _ _]

theorem ustWf_afr {n : Nat} {m m' : Mem} {cty nP j r : Word} (h : ustWf n m cty nP j = some (r, m')) :
    AFr m m' := by
  match n, h with
  | n + 2, h =>
    simp only [ustWf, ustW, ustK1.eq_def] at h
    afr_auto h [stripF_afr, hbFastW_afr]

theorem u4W_afr : ∀ (n : Nat) (m m' : Mem) (ko nF cl i : Word) (r : List Word),
    u4W n m ko nF cl i = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, h => by simp [u4W] at h
  | n + 1, m, m', ko, nF, cl, i, r, h => by
    simp only [u4W, u4K.eq_def] at h
    afr_auto h [ustWf_afr, u4W_afr n _ _ _ _ _ _ _]

theorem roW_afr {k : Nat} {m m' : Mem} {ctx hi cur : Word} {r : List Word} (h : roW k m ctx hi cur = some (r, m')) :
    AFr m m' := by
  cases k with
  | zero => simp [roW] at h
  | succ k =>
  simp only [roW, roK0.eq_def, roK1.eq_def, roK2.eq_def] at h
  afr_auto h [resHeadW_afr, stub_afr, gaaF_afr, ftdF_afr, ftdsF_afr, noaW_afr _ _ _ _ _ _ _ _ _ _]

theorem pos2PinW_afr {m m' : Mem} {i : Word} {r : List Word} (h : pos2PinW m i = some (r, m')) : AFr m m' := by
  simp only [pos2PinW] at h
  afr_auto h []

end L.Ind
