module

public import ConAgua.Arena.IndPosSpec.BvbWMfr
import ConAgua.Arena.IndPosSpec.GgW
import ConAgua.Arena.IndPosSpec.Mfr
import ConAgua.Arena.IndPosSpec.NestContParamsClosed
import ConAgua.Arena.IndPosSpec.SnocWMfr
public import ConAgua.Arena.IndPosSpec.U4W
public import ConAgua.Arena.IndGrindAttr
import ConAgua.Arena.IndPosSpec.DepthGo
import ConAgua.Arena.IndPosSpec.MentionsAnyGo
import ConAgua.Arena.IndPosSpec.SnocWDecK
import ConAgua.Arena.IndPosSpec.SnocWStage
public import ConAgua.Arena.IndPosSpec.FgW2
import ConAgua.L.WordOff

@[expose] public section

/-!
# FgW

`PosAv`, `PosMR.mfr`, `PosMR.fr`, `PosMR.setNo`, `PosMR.setRp`, `consW_mfr` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The five memos' arrays and stamp words. -/
abbrev PosAv (S : List TieredArray) (T : List Word) : Prop :=
  ((NOM : TieredArray) ∉ S ∧ (DPM : TieredArray) ∉ S ∧ (RAM : TieredArray) ∉ S ∧
    (HBM : TieredArray) ∉ S ∧ (RFM : TieredArray) ∉ S) ∧
  ((204 : Word) ∉ T ∧ (206 : Word) ∉ T ∧ (210 : Word) ∉ T ∧ (214 : Word) ∉ T ∧ (208 : Word) ∉ T ∧
    (218 : Word) ∉ T ∧ (219 : Word) ∉ T)

theorem PosMR.mfr {S : List TieredArray} {T : List Word} {m m' : Mem} (h : PosMR m) (hf : MFr S T m m')
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

/-- Across a `replace_apps` walk. -/
theorem PosMR.setRp {m m' : Mem} (h : PosMR m) (hf : MFr [RAM] [210, 211] m m')
    (hn : ∃ mp, rpMR m' mp) : PosMR m' := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, -, ⟨d, hd⟩, ⟨M, G, g, hR⟩⟩ := h
  exact ⟨⟨a, noMR_mfr hf (by decide) (by decide) ha⟩, ⟨b, dpMR_mfr hf (by decide) (by decide) hb⟩, hn,
    ⟨d, hbMR_mfr hf (by decide) (by decide) hd⟩, ⟨M, G, g, hR.mfr hf (by decide) (by decide)⟩⟩

theorem consW_mfr {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} (h : consW n m x o l = some (r, m')) :
    MFr [] [] m m' := by
  unfold consW at h
  split at h; · simp at h
  split at h; · simp at h
  rename_i q m1 hal
  split at h; · simp at h
  rename_i m2 hc
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ((allocW_mfr hal).trans (MFr.set_iw _ _ _)).trans (MFr.of_iw (L.Ind.copyW_iwFrame _ _ _ _ _ _ hc))

theorem piBW_mfr : ∀ (n : Nat) (m m' : Mem) (fuel h : Word) (r : List Word), piBW n m fuel h = some (r, m') →
    MFr [] [] m m'
  | 0, _, _, _, _, _, hh => by simp [piBW] at hh
  | n + 1, m, m', fuel, h, r, hh => by
    simp only [piBW, piBK1, piBK2.eq_def, piBK3.eq_def] at hh
    mfr_auto hh [piBW_mfr n _ _ _ _ _, consW_mfr]

theorem fvinternW_mfr {m m' : Mem} {u ty r : Word} (h : fvinternW m u ty = some (r, m')) : MFr [] [] m m' :=
  MFr.of_low (fvinternW_low h)
/-- `nest_crest`'s write set among the memos: `replace_apps`' and the banked `replace_fvars`'. -/
abbrev CrFr (m m' : Mem) : Prop := MFr [RAM, RFM] [210, 211, 208, 209, 218, 219] m m'

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `nest_frame_mates_go` keeps the stage relation (it writes `IW` by `sl_snoc` only). -/
theorem matesW_stage {vis : Word} {fe : IFEnv} {a : AState} (n : Nat) :
    ∀ (m m' : Mem) (c off l oO oL : Word) (r : List Word),
    matesW n m c off l oO oL = some (r, m') → StageR vis fe m a → StageR vis fe m' a := by
  induction n with
  | zero => intro m m' c off l oO oL r h; simp [matesW.eq_1] at h
  | succ n ih =>
    intro m m' c off l oO oL r h hS
    by_cases hl : l = 0
    · rw [matesW.arm1 (hc1 := hl)] at h; cases h; exact hS
    rw [matesW.arm2 (hc1 := hl), erRd_foldN] at h
    rcases hb : containsW n m oO oL (erRd m off) with _ | b <;> rw [hb] at h
    · rw [matesW.k_sl_contains.none] at h; cases h
    by_cases hk : erRd m off = c ∨ b ≠ 0
    · rw [matesW.k_sl_contains.arm1 (hc1 := hk)] at h
      cases hr : matesW n m c (off + 1) (l - 1) oO oL with
      | none => rw [hr, matesW.k_nest_frame_mates_go.none] at h; cases h
      | some pr => rw [hr, matesW.k_nest_frame_mates_go.arm1] at h; cases h; exact ih _ _ _ _ _ _ _ _ hr hS
    · rw [matesW.k_sl_contains.arm2 (hc1 := hk), erRd_foldN] at h
      cases hs : snocW n m oO oL (erRd m off) with
      | none => rw [hs, matesW.k_sl_snoc.none] at h; cases h
      | some pr =>
        obtain ⟨r2, m2⟩ := pr
        rw [hs, matesW.k_sl_snoc.arm1] at h
        cases hr : matesW n m2 c (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0) with
        | none => rw [hr, matesW.k_nest_frame_mates_go.none] at h; cases h
        | some pr => rw [hr, matesW.k_nest_frame_mates_go.arm1] at h; cases h; exact ih _ _ _ _ _ _ _ _ hr (snocW_stage hs hS)


end L.Ind

namespace L.Ind

open L.Arena

/-! ## Hole slices grown -/

/-- A hole slice grown by one record (`sl_snoc`). -/
theorem pos2_hsl_snoc {m m' : Mem} {o l q : Nat} {hs : List NestHole} {h : NestHole} {w : Word}
    (hH : HSl m o l hs) (hg : IWGrow m m') (hq : q + l + 1 ≤ iwTop m')
    (hw : ∀ i < l, (m'.arr64 IW)[q + i]? = (m.arr64 IW)[o + i]?) (hx : (m'.arr64 IW)[q + l]? = some w)
    (hd : decNH m' w.toNat = some h) (hin : NHIn m' w.toNat (· < iwTop m')) :
    HSl m' q (l + 1) (hs ++ [h]) := by
  obtain ⟨h1, h2, h3⟩ := hH
  refine ⟨by simp [h1], by omega, fun i hi => ?_⟩
  by_cases hil : i < l
  · obtain ⟨w', hw', hd', hn'⟩ := h3 i hil
    obtain ⟨e, hn''⟩ := hn'.grow hg
    refine ⟨w', by rw [hw i hil]; exact hw', ?_, hn''⟩
    rw [e, hd', List.getElem?_append_left (by omega)]
  · have : i = l := by omega
    subst this
    refine ⟨w, hx, ?_, hin⟩
    rw [hd, List.getElem?_append_right (by omega)]; simp [h1]

/-- A hole record `[key, base, nIdx]` (`rec3`). -/
theorem pos2_hole_rec {m' : Mem} {p key hi x : Word} {K : NestKey}
    (hp : p.toNat + 3 ≤ iwTop m')
    (hget : ∀ j < [key, hi, x].length, (m'.arr64 IW)[p.toNat + j]? = [key, hi, x][j]?)
    (hK : decNK m' key.toNat = some K) (hKin : NKIn m' key.toNat (· < iwTop m')) :
    decNH m' p.toNat = some ⟨K, hi.toNat, x.toNat⟩ ∧ NHIn m' p.toNat (· < iwTop m') := by
  have g0 : (m'.arr64 IW)[p.toNat]? = some key := by simpa using hget 0 (by simp)
  have g1 : (m'.arr64 IW)[p.toNat + 1]? = some hi := by simpa using hget 1 (by simp)
  have g2 : (m'.arr64 IW)[p.toNat + 2]? = some x := by simpa using hget 2 (by simp)
  have e0 : iwN m' p.toNat = some key.toNat := by simp [iwN, nat?, iwA, aread_apply, g0]
  refine ⟨decNH_of_words g0 g1 g2 hK, by omega, by omega, by omega, fun k hk => ?_⟩
  rw [e0] at hk; cases hk; exact hKin

/-- One frame stack entry of `nestFrame`: the hole at `base := hi`, its index count the binder
count of its instantiated former (`piBinders`), as the Bridge's `nestFrame_eq` states it. -/
def frEntryT (us : LsIdx) (ds : List EIdx) (hi : Nat) (x : NIdx × EIdx) : AM NestHole := do
  let q ← ConRon.Arena.piBinders coreWalkFuel x.2
  pure ({ key := ⟨x.1, us, ds⟩, base := hi, nIdx := q.1.length } : NestHole)

end L.Ind

namespace L.Ind

open L.Arena

/-- A group's head pointer and its words. -/
theorem GrpAt.head {m : Mem} {o : Nat} {x : NIdx × EIdx} {grp : List (NIdx × EIdx)} (h : GrpAt m o (x :: grp))
    (ho : o < 2 ^ 64) (htop : iwTop m < 2 ^ 64) :
    ∃ w c t : Word, rdW (m.arr64 IW) (UInt64.ofNat o) = w ∧ w.toNat + 1 < iwTop m ∧ rdW (m.arr64 IW) w = c ∧
      H c ∧ decI c = x.1 ∧ rdW (m.arr64 IW) (w + 1) = t ∧ H t ∧ decI t = x.2 := by
  obtain ⟨w, c, t, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h 0 (by simp)
  have e1 : (w + 1).toNat = w.toNat + 1 := L.toNat_add_of_lt _ _ (by simp; omega)
  refine ⟨w, c, t, ?_, h2, by simp [rdW, h3], h4, by simpa using h5, by simp [rdW, e1, h6], h7, by simpa using h8⟩
  simp only [Nat.add_zero] at h1
  simp [rdW, UInt64.toNat_ofNat_of_lt' ho, h1]

/-- **`nest_frame_grp`**: the stack grown by the group's holes (base `hi`, each with its former's
binder count), the group's names. -/
theorem fgW_ok (_dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (hi us dO dL : Word)
    (ds : List EIdx) (hus : H us) : ∀ (n : Nat) (m m' : Mem) (a : AState) (gO gL pO pL nO nL : Word)
    (grp : List (NIdx × EIdx)) (accP : List NestHole) (accN : List NIdx) (r : List Word),
    fgW n m hi us dO dL gO gL pO pL nO nL = some (r, m') → StageR vis fe m a →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp →
    HSl m pO.toNat pL.toNat accP → decHL m nO.toNat nL.toNat = some accN → nO.toNat + nL.toNat ≤ iwTop m →
    ∃ fr, (grp.mapM (frEntryT (decI us) ds hi.toNat)).run a = .ok (fr, a) ∧
    StageR vis fe m' a ∧ IWGrow m m' ∧
      HSl m' (r.headD 0).toNat (r.tail.headD 0).toNat (accP ++ fr) ∧
      decHL m' (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat = some (accN ++ grp.map (·.1)) ∧
      (r.tail.tail.headD 0).toNat + (r.tail.tail.tail.headD 0).toNat ≤ iwTop m' := by
  intro n
  induction n with
  | zero => intro m m' a gO gL pO pL nO nL grp accP accN r h; simp [fgW] at h
  | succ n ih =>
    intro m m' a gO gL pO pL nO nL grp accP accN r h hS hds hgl hgb hgrp hP hN hNb
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
    by_cases hg0 : gL = 0
    · rw [fgW_nil (h := hg0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hg0
      have : grp = [] := List.eq_nil_of_length_eq_zero (by simpa using hgl.symm)
      subst this
      exact ⟨[], rfl, hS, IWGrow.refl _, by simpa using hP, by simpa using hN, by simpa using hNb⟩
    rw [fgW_cons (h := hg0)] at h
    obtain ⟨⟨c, ty⟩, grp', rfl⟩ : ∃ x grp', grp = x :: grp' := by
      cases grp with
      | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hgl)) hg0
      | cons x grp' => exact ⟨x, grp', rfl⟩
    simp only [List.length_cons] at hgl hgb
    obtain ⟨w, cw, tw, hrw, hw1, hrc, hcH, hcd, -, -, -⟩ := hgrp.head (by omega) htop
    rw [UInt64.ofNat_toNat] at hrw
    rw [hrw, hrc] at h
    -- the key
    rcases hk : posRecW m [cw, us, dO, dL] with _ | ⟨key, m1⟩ <;> rw [hk] at h; · simp [fgK1] at h
    rw [fgK1_some] at h
    obtain ⟨hS1, hg1, hkq, ht1, hget1⟩ := posRecW_stage hk hS (by simp)
    simp only [List.length_cons, List.length_nil] at ht1
    have hds1 := DecB.grow (OMono.decHL _ _) hg1 hds
    have hK : DecB (fun m => decNK m key.toNat) m1 ⟨decI cw, decI us, ds⟩ :=
      pos2_key_rec hcH hus (by omega) hget1 hds1
    -- the former's binder count
    have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.iw.iw hS1.iw.iwSize
    obtain ⟨w', -, tw', hrw', -, -, -, -, hrt', htH', htd'⟩ :=
      (hgrp.grow (by simpa using hgb) hg1).head (by omega) htop1
    rw [UInt64.ofNat_toNat] at hrw'
    rw [hrw', hrt'] at h
    rcases hb : piBW n m1 CWF tw' with _ | ⟨rs, m2⟩ <;> rw [hb] at h; · simp [fgKb] at h
    rw [fgKb_some] at h
    obtain ⟨bs, e, hrunB, hdecB, -, -, hS2, hg2, -⟩ := piBW_cwf hb hS1 htH'
    have hbl : bs.length = (rs.getD 1 0).toNat := decHL_length _ hdecB
    -- the hole
    rcases hh : posRecW m2 [key, hi, rs.getD 1 0] with _ | ⟨hole, m3⟩ <;> rw [hh] at h; · simp [fgK2] at h
    rw [fgK2_some] at h
    obtain ⟨hS3, hg3, hhq, ht3, hget3⟩ := posRecW_stage hh hS2 (by simp)
    simp only [List.length_cons, List.length_nil] at ht3
    have hg23 := hg2.trans hg3
    obtain ⟨hKd, hKin⟩ := pos2_nk_in (DecB.grow (decNK_mono _) hg23 hK)
    obtain ⟨hHd, hHin⟩ := pos2_hole_rec (by omega) hget3 hKd hKin
    have hg13 := hg1.trans hg23
    -- the two snocs
    rcases hs1 : snocW n m3 pO pL hole with _ | ⟨r3, m4⟩ <;> rw [hs1] at h; · simp [fgK3] at h
    rw [fgK3_some] at h
    obtain ⟨hS4, hg4, h30, h31, ht4, hw4, hx4⟩ := snocW_words hs1 hS3 (by have := hg13.iw; have := hP.2.1; omega)
    have hP4 : HSl m4 (r3.headD 0).toNat (r3.tail.headD 0).toNat
        (accP ++ [⟨⟨decI cw, decI us, ds⟩, hi.toNat, (rs.getD 1 0).toNat⟩]) := by
      rw [h30, h31]
      exact pos2_hsl_snoc (hP.grow hg13) hg4 (by omega) hw4 hx4
        (by rw [(hHin.grow hg4).1]; exact hHd) (hHin.grow hg4).2
    rcases hs2 : snocW n m4 nO nL cw with _ | ⟨r4, m5⟩ <;> rw [hs2] at h; · simp [fgK4] at h
    rw [fgK4_some] at h
    have hg14 := hg13.trans hg4
    obtain ⟨hr5, hN5, hg5, -, hl5, ht5⟩ := snocW_decK hs2 hS4.iw.iwSize hS4.iw.ctl (by have := hg14.iw; omega)
      hcH (by rw [decHL_agree (RdS.of_grow hg14) (fun j hj => by omega)]; exact hN)
    have hS5 := snocW_stage hs2 hS4
    have hgO1 : (gO + 1).toNat = gO.toNat + 1 := L.toNat_add_of_lt _ _ (by simp; omega)
    have hgL1 : (gL - 1).toNat = grp'.length := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hg15 := hg14.trans hg5
    obtain ⟨fr, hrun, hS', hg', hP', hN', hNb'⟩ := ih m5 m' a (gO + 1) (gL - 1) _ _ _ _ grp' _ _ r h hS5
      (DecB.grow (OMono.decHL _ _) (hg23.trans (hg4.trans hg5)) hds1) hgL1
      (by rw [hgO1]; have := hg15.iw; omega) (by rw [hgO1]; exact (hgrp.grow (by simpa using hgb) hg15).tail)
      (hP4.grow hg5) (by rw [hr5]; simpa using hN5) (by rw [hr5]; simp; omega)
    refine ⟨⟨⟨decI cw, decI us, ds⟩, hi.toNat, (rs.getD 1 0).toNat⟩ :: fr, ?_, hS', hg15.trans hg', ?_, ?_, hNb'⟩
    · have hty : decI tw' = ty := htd'
      rw [hty] at hrunB
      rw [← hbl, hcd]
      simp only [List.mapM_cons, frEntryT, StateT.run_bind, hrunB, except_ok_bind, StateT.run_pure]
      rw [show (pure _ : Except ConRon.Arena.CheckError _) = Except.ok _ from rfl, except_ok_bind]
      simp only [hrun]
      rfl
    · simpa [hcd] using hP'
    · simpa [hcd] using hN'

end L.Ind

namespace L.Ind

open L.Arena

section arms
variable (n : Nat) (m m1 : Mem) (hi gO gL aO aL v : Word) (r : List Word)
theorem fhW_ovf (h : ¬ gL = 0) (h1 : hi + 1 = 0) : fhW (n + 1) m hi gO gL aO aL = none := by simp [fhW, h, h1]
theorem fhK1_big (h : 4294967296 ≤ v) : fhK1 n hi gO gL aO aL (some (v, m1)) = none := by simp [fhK1, h]
end arms
attribute [ind_grind] fhW_ovf fhK1_big

end L.Ind

namespace L.Ind

open L.Arena

theorem pos2_zipIdx_holes (hi : Nat) : ∀ (grp : List (NIdx × EIdx)) (k : Nat),
    (grp.zipIdx k).mapM (fun (x : (NIdx × EIdx) × Nat) => internFVarE (hi + x.2) x.1.2) =
      pos2FhT (hi + k) grp
  | [], k => rfl
  | x :: g, k => by
    simp only [List.zipIdx_cons, List.mapM_cons, pos2FhT, pos2_zipIdx_holes hi g (k + 1), Nat.add_assoc]

/-- **`nest_frame_holes`**: the group's holes from `hi` on, appended to the accumulator. -/
theorem fhW_ok (_dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) : ∀ (n : Nat) (m m' : Mem)
    (a : AState) (hi gO gL aO aL : Word) (grp : List (NIdx × EIdx)) (acc : List EIdx) (r : List Word),
    fhW n m hi gO gL aO aL = some (r, m') → StageR vis fe m a →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp →
    decHL m aO.toNat aL.toNat = some acc → aO.toNat + aL.toNat ≤ iwTop m →
    ∃ vs a', (pos2FhT hi.toNat grp).run a = .ok (vs, a') ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (acc ++ vs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  intro n
  induction n with
  | zero => intro m m' a hi gO gL aO aL grp acc r h; simp [fhW] at h
  | succ n ih =>
    intro m m' a hi gO gL aO aL grp acc r h hS hgl hgb hgrp hA hAb
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
    by_cases hg0 : gL = 0
    · rw [fhW_nil (h := hg0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hg0
      have : grp = [] := List.eq_nil_of_length_eq_zero (by simpa using hgl.symm)
      subst this
      exact ⟨[], a, rfl, hS, IWGrow.refl _, by simpa using hA, by simpa using hAb⟩
    by_cases hov : hi + 1 = 0
    · rw [fhW_ovf (h := hg0) (h1 := hov)] at h; cases h
    rw [fhW_cons (h := hg0) (h1 := hov)] at h
    obtain ⟨⟨c, t⟩, grp', rfl⟩ : ∃ x grp', grp = x :: grp' := by
      cases grp with
      | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hgl)) hg0
      | cons x grp' => exact ⟨x, grp', rfl⟩
    simp only [List.length_cons] at hgl hgb
    obtain ⟨w, cw, tw, hrw, hw1, -, -, -, hrt, htH, htd⟩ := hgrp.head (by omega) htop
    rw [UInt64.ofNat_toNat] at hrw
    rw [hrw, hrt] at h
    rcases hf : fvinternW m hi tw with _ | ⟨v, m1⟩ <;> rw [hf] at h; · simp [fhK1] at h
    by_cases hvb : 4294967296 ≤ v
    · rw [fhK1_big (h := hvb)] at h; cases h
    rw [fhK1_ok (h := hvb)] at h
    obtain ⟨a1, hrun1, hS1, hg1⟩ := internFVar_stage hS hi tw htH hf
    rcases hs : snocW n m1 aO aL v with _ | ⟨r2, m2⟩ <;> rw [hs] at h; · simp [fhK2] at h
    rw [fhK2_some] at h
    have hvH : H v := by
      have : ¬ (4294967296 : Word).toNat ≤ v.toNat := fun h' => hvb (UInt64.le_iff_toNat_le.mpr h')
      simp only [H]; simpa using this
    obtain ⟨hr2, hA2, hg2, -, -, ht2⟩ := snocW_decK hs hS1.iw.iwSize hS1.iw.ctl (by have := hg1.iw; omega)
      hvH (by rw [decHL_agree (RdS.of_grow hg1) (fun j hj => by omega)]; exact hA)
    have hS2 := snocW_stage hs hS1
    have hgO1 : (gO + 1).toNat = gO.toNat + 1 := L.toNat_add_of_lt _ _ (by simp; omega)
    have hgL1 : (gL - 1).toNat = grp'.length := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hhi1 : (hi + 1).toNat = hi.toNat + 1 := by
      rcases Nat.lt_or_ge (hi.toNat + 1) (2 ^ 64) with hl | hl
      · exact L.toNat_add_of_lt _ _ (by simpa using hl)
      · exfalso; apply hov; apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; have := hi.toNat_lt; simp; omega
    have hg12 := hg1.trans hg2
    have hb2 : (gO + 1).toNat + grp'.length ≤ iwTop m2 := by
      rw [hgO1]; have := hg12.iw; omega
    have hgr2 : GrpAt m2 (gO + 1).toNat grp' := by
      rw [hgO1]; exact (hgrp.grow (by simpa using hgb) hg12).tail
    have hA2' : decHL m2 (r2.headD 0).toNat (r2.tail.headD 0).toNat = some (acc ++ [decI v]) := by
      rw [hr2]; simpa using hA2
    have hAb2 : (r2.headD 0).toNat + (r2.tail.headD 0).toNat ≤ iwTop m2 := by
      rw [hr2]; simp only [List.headD_cons, List.tail_cons]; omega
    obtain ⟨vs, a', hrun, hS', hg', hA', hAb'⟩ := ih m2 m' a1 (hi + 1) (gO + 1) (gL - 1) _ _ grp' _ r h hS2
      hgL1 hb2 hgr2 hA2' hAb2
    refine ⟨decI v :: vs, a', ?_, hS', hg12.trans hg', by simpa using hA', hAb'⟩
    rw [hhi1] at hrun
    have htd' : t = decE tw := by simpa [decE_eq] using htd.symm
    subst htd'
    simp only [pos2FhT, internFVarE, StateT.run_bind, hrun1, except_ok_bind, hrun]
    rfl

end L.Ind

namespace L.Ind

open L.Arena

/-- **`nest_cont_new_active`**: the group's keys at `(us, ds)`, appended to the accumulator. -/
theorem caW_ok (_dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (us dO dL : Word)
    (ds : List EIdx) (hus : H us) : ∀ (n : Nat) (m m' : Mem) (a : AState) (gO gL aO aL : Word)
    (grp : List (NIdx × EIdx)) (acc : List NestKey) (r : List Word),
    caW n m us dO dL gO gL aO aL = some (r, m') → StageR vis fe m a →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp →
    KsB m aO.toNat aL.toNat acc → aO.toNat + aL.toNat ≤ iwTop m →
    StageR vis fe m' a ∧ IWGrow m m' ∧
      KsB m' (r.headD 0).toNat (r.tail.headD 0).toNat
        (acc ++ grp.map fun x => (⟨x.1, decI us, ds⟩ : NestKey)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  intro n
  induction n with
  | zero => intro m m' a gO gL aO aL grp acc r h; simp [caW] at h
  | succ n ih =>
    intro m m' a gO gL aO aL grp acc r h hS hds hgl hgb hgrp hA hAb
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
    by_cases hg0 : gL = 0
    · rw [caW_nil (h := hg0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hg0
      have : grp = [] := List.eq_nil_of_length_eq_zero (by simpa using hgl.symm)
      subst this
      exact ⟨hS, IWGrow.refl _, by simpa using hA, by simpa using hAb⟩
    rw [caW_cons (h := hg0)] at h
    obtain ⟨⟨c, t⟩, grp', rfl⟩ : ∃ x grp', grp = x :: grp' := by
      cases grp with
      | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hgl)) hg0
      | cons x grp' => exact ⟨x, grp', rfl⟩
    simp only [List.length_cons] at hgl hgb
    obtain ⟨w, cw, tw, hrw, hw1, hrc, hcH, hcd, -, -, -⟩ := hgrp.head (by omega) htop
    rw [UInt64.ofNat_toNat] at hrw
    rw [hrw, hrc] at h
    rcases hk : posRecW m [cw, us, dO, dL] with _ | ⟨key, m1⟩ <;> rw [hk] at h; · simp [caK1] at h
    rw [caK1_some] at h
    obtain ⟨hS1, hg1, hkq, ht1, hget1⟩ := posRecW_stage hk hS (by simp)
    simp only [List.length_cons, List.length_nil] at ht1
    have hds1 := DecB.grow (OMono.decHL _ _) hg1 hds
    have hK : DecB (fun m => decNK m key.toNat) m1 ⟨decI cw, decI us, ds⟩ :=
      pos2_key_rec hcH hus (by omega) hget1 hds1
    rcases hs : snocW n m1 aO aL key with _ | ⟨r2, m2⟩ <;> rw [hs] at h; · simp [caK2] at h
    rw [caK2_some] at h
    obtain ⟨hS2, hg2, h20, h21, ht2, hw2, hx2⟩ := snocW_words hs hS1 (by have := hg1.iw; omega)
    have hA2 : KsB m2 (r2.headD 0).toNat (r2.tail.headD 0).toNat (acc ++ [⟨decI cw, decI us, ds⟩]) := by
      rw [h20, h21]
      exact pos2_decB_snoc decNK_mono (hA.grow hg1) hg2 (by omega) hw2 hx2 (DecB.grow (decNK_mono _) hg2 hK)
    have hgO1 : (gO + 1).toNat = gO.toNat + 1 := L.toNat_add_of_lt _ _ (by simp; omega)
    have hgL1 : (gL - 1).toNat = grp'.length := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hg12 := hg1.trans hg2
    have hb2 : (gO + 1).toNat + grp'.length ≤ iwTop m2 := by rw [hgO1]; have := hg12.iw; omega
    have hgr2 : GrpAt m2 (gO + 1).toNat grp' := by
      rw [hgO1]; exact (hgrp.grow (by simpa using hgb) hg12).tail
    have hAb2 : (r2.headD 0).toNat + (r2.tail.headD 0).toNat ≤ iwTop m2 := by rw [h20, h21]; omega
    obtain ⟨hS', hg', hA', hAb'⟩ := ih m2 m' a (gO + 1) (gL - 1) _ _ grp' _ r h hS2
      (DecB.grow (OMono.decHL _ _) hg2 hds1) hgL1 hb2 hgr2 hA2 hAb2
    refine ⟨hS', hg12.trans hg', ?_, hAb'⟩
    simpa [hcd] using hA'

end L.Ind

namespace L.Ind

open L.Arena

/-- The twin's per-parameter test of `nestCont`. -/
def pcF (hp : Nat) (x : EIdx) : AM Bool := do
  let bb ← bvarB coreWalkFuel x
  if bb != 0 then pure false
  else do
    let fb ← fvarB coreWalkFuel x
    pure (decide (fb ≤ hp))

end L.Ind

namespace L.Ind

open L.Arena

theorem pos2PinW_ok {m m' : Mem} {a : AState} {i : Word} {r : List Word}
    (h : pos2PinW m i = some (r, m')) (hP : PinsR m a.pins) :
    m' = m ∧ H (r.headD 0) ∧ (pinAt i.toNat).run a = .ok (decI (r.headD 0), a) := by
  unfold pos2PinW at h
  by_cases h0 : pinW m 0 = 0
  · simp [h0] at h
  rw [ite_eq_right h0] at h
  by_cases hi : 52 ≤ i
  · simp [hi] at h
  rw [ite_eq_right hi] at h
  have hF := hP.full h0
  by_cases h51 : i = 51
  · rw [ite_eq_left h51] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    subst h51
    have e : rdW (m.arr64 PINS) 71 = pinW m 71 := by simp only [rdW, pinW]; rfl
    refine ⟨rfl, ?_, ?_⟩ <;> simp only [List.headD_cons] <;> rw [e]
    · exact hF.quotMk_lt
    · exact pinAt_run51 hF
  rw [ite_eq_right h51] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hi' : i.toNat < 51 := by
    have h52 := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hi)
    have : i.toNat ≠ 51 := fun e => h51 (UInt64.toNat_inj.mp (by simpa using e))
    simp at h52; omega
  have e : rdW (m.arr64 PINS) (1 + i) = pinW m (1 + i.toNat) := by
    simp only [rdW, pinW]
    congr 2
    rw [UInt64.toNat_add]; simp; omega
  refine ⟨rfl, ?_, ?_⟩ <;> simp only [List.headD_cons] <;> rw [e]
  · exact hF.names_lt i.toNat hi'
  · exact pinAt_run hF i.toNat hi'

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Memo frames of the `IndPos2` pieces (helper `posmemo`) -/

theorem nagW_mfr : ∀ (n : Nat) (m m' : Mem) (us dO dL gO gL kO kL : Word) (r : List Word),
    nagW n m us dO dL gO gL kO kL = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [nagW.eq_1] at h
  | n + 1, m, m', us, dO, dL, gO, gL, kO, kL, r, h => by
    simp only [nagW.eq_2, nagW.k_rec4.eq_def, nagW.k_nest_keys_contains.eq_def, nagW.k_sl_snoc.eq_def,
      nagW.k_nest_accept_group.eq_def] at h
    mfr_auto h [posRecW_mfr, snocW_mfr, nagW_mfr n _ _ _ _ _ _ _ _ _ _]

theorem matesW_mfr : ∀ (n : Nat) (m m' : Mem) (c off l oO oL : Word) (r : List Word),
    matesW n m c off l oO oL = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, h => by simp [matesW.eq_1] at h
  | n + 1, m, m', c, off, l, oO, oL, r, h => by
    simp only [matesW.eq_2, matesW.k_sl_contains.eq_def, matesW.k_sl_snoc.eq_def,
      matesW.k_nest_frame_mates_go.eq_def] at h
    mfr_auto h [snocW_mfr, matesW_mfr n _ _ _ _ _ _ _ _]

/-- `env_find` reads only. -/
theorem callW_envFind_mem {p : Prog} (hg : p.lookup "env_row_get" = some envRowGetL)
    (hb : p.lookup "base_row_get" = some baseRowGetL) (hp : p.lookup "env_find" = some envFindL)
    {n : Nat} {m m' : Mem} {w vis : Word} {r : List Word}
    (h : callW p n "env_find" [w, vis] m = some (r, m')) : m' = m := by
  obtain ⟨s', rfl, hm, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (envFind_spec p hg hb hp n _ vis w) h
  exact hm

/-- `nest_block_of` reads only. -/
theorem nboW_mem {p : Prog} (hg : p.lookup "env_row_get" = some envRowGetL)
    (hb : p.lookup "base_row_get" = some baseRowGetL) (hp : p.lookup "env_find" = some envFindL)
    {n : Nat} {m m' : Mem} {vis c : Word} {r : List Word} (h : nboW p n m vis c = some (r, m')) : m' = m := by
  rcases n with _ | n
  · simp [nboW] at h
  simp only [nboW] at h
  rcases hc : callW p n "env_find" [c, vis] m with _ | ⟨r1, m1⟩ <;> rw [hc] at h
  · simp [nboW.k_env_find] at h
  have e := callW_envFind_mem hg hb hp hc
  subst e
  simp only [nboW.k_env_find] at h
  split at h
  · cases h; rfl
  split at h <;> cases h <;> rfl

/-- **`nest_frame_mates`, under the stage relation**: the mates as a handle slice below the top. -/
theorem nfmW_ok {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {p : Prog} (L : FmLook p) (hbr : p.lookup "base_row_get" = some baseRowGetL)
    {m m' : Mem} {c : Word} {r : List Word} (h : nfmW p n m vis c = some (r, m')) (hS : StageR vis fe m a)
    (hc : H c) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (nestFrameMates fe (decI c)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  cases n with
  | zero => simp [nfmW.eq_1] at h
  | succ n =>
  rw [nfmW.arm1] at h
  rcases hbo : nboW p n m vis c with _ | ⟨r1, m1⟩ <;> rw [hbo] at h; · rw [nfmW.k_nest_block_of.none] at h; cases h
  have hm1 := nboW_mem L.hg hbr L.hf hbo
  subst hm1
  -- the block slice
  have hsl : hslice? (erA m1) (r1.headD 0).toNat (r1.tail.headD 0).toNat = some (nestBlockOf fe (decI c)) := by
    rcases n with _ | k
    · simp [nboW] at hbo
    simp only [nboW] at hbo
    rcases hcall : callW p k "env_find" [c, vis] m1 with _ | ⟨rf, mf⟩ <;> rw [hcall] at hbo
    · simp [nboW.k_env_find] at hbo
    obtain ⟨s', hs', hmem, -, hfind, hdec⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (envFind_refines p L.hg hbr L.hf k _ vis c hS.check.env hc) hcall
    have hmf : mf = m1 := by rw [← hs', hmem]
    subst hmf
    have key := nestBlockOf_key (rf.headD 0) (rf.tail.headD 0) hfind hdec
    have e : ∀ x : Word, rdW (mf.arr64 (tierA EREC (x >>> 40))) (x &&& 1099511627775) = erRd mf x := fun x => rfl
    simp only [nboW.k_env_find, e] at hbo
    by_cases h0 : rf.headD 0 = 0
    · simp only [h0, ite_true, Option.some.injEq, Prod.mk.injEq] at hbo
      obtain ⟨rfl, -⟩ := hbo
      simp only [ite_eq_left h0, List.headD_cons, List.tail_cons] at key ⊢; exact key
    by_cases h3 : erRd mf (rf.tail.headD 0) = 3
    · simp only [h0, h3, ite_false, ne_eq, not_true_eq_false, Option.some.injEq, Prod.mk.injEq] at hbo
      obtain ⟨rfl, -⟩ := hbo
      simp only [ite_eq_right h0, ite_eq_left h3, List.headD_cons, List.tail_cons] at key ⊢; exact key
    · simp only [h0, h3, ite_false, ne_eq, not_false_eq_true, ite_true, Option.some.injEq, Prod.mk.injEq] at hbo
      obtain ⟨rfl, -⟩ := hbo
      simp only [ite_eq_right h0, ite_eq_right h3, List.headD_cons, List.tail_cons] at key ⊢; exact key
  rw [nfmW.k_nest_block_of.arm1] at h
  rcases hmt : matesW n m1 c (r1.headD 0) (r1.tail.headD 0) 0 0 with _ | ⟨r2, m2⟩ <;> rw [hmt] at h
  · rw [nfmW.k_nest_frame_mates_go.none] at h; cases h
  rw [nfmW.k_nest_frame_mates_go.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨h1, h2, -, h4⟩ := matesW_ok n _ _ c _ _ 0 0 _ [] r2 hmt hS.iw.iwSize hS.iw.ctl hS.iw.erSize hc hsl
    (by simp [decHL, hslice?]) (by simp) (by simp)
  exact ⟨matesW_stage n _ _ _ _ _ _ _ _ hmt hS, h2, by simpa [nestFrameMates] using h1, by simpa using h4⟩

theorem nboW_mfr {p : Prog} (hg : p.lookup "env_row_get" = some envRowGetL)
    (hb : p.lookup "base_row_get" = some baseRowGetL) (hp : p.lookup "env_find" = some envFindL)
    {n : Nat} {m m' : Mem} {vis c : Word} {r : List Word} (h : nboW p n m vis c = some (r, m')) :
    MFr [] [] m m' := by
  rw [nboW_mem hg hb hp h]; exact MFr.refl _ _ _

theorem nfmW_mfr {p : Prog} (hg : p.lookup "env_row_get" = some envRowGetL)
    (hb : p.lookup "base_row_get" = some baseRowGetL) (hp : p.lookup "env_find" = some envFindL)
    {n : Nat} {m m' : Mem} {vis c : Word} {r : List Word} (h : nfmW p n m vis c = some (r, m')) :
    MFr [] [] m m' := by
  cases n with
  | zero => simp [nfmW.eq_1] at h
  | succ n =>
  simp only [nfmW.arm1, nfmW.k_nest_block_of.eq_def, nfmW.k_nest_frame_mates_go.eq_def] at h
  mfr_auto h [nboW_mfr hg hb hp, matesW_mfr _ _ _ _ _ _ _ _ _]

theorem fgW_mfr : ∀ (n : Nat) (m m' : Mem) (hi us dO dL gO gL pO pL nO nL : Word) (r : List Word),
    fgW n m hi us dO dL gO gL pO pL nO nL = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [fgW] at h
  | n + 1, m, m', hi, us, dO, dL, gO, gL, pO, pL, nO, nL, r, h => by
    unfold fgW fgK1 fgKb fgK2 fgK3 fgK4 at h
    mfr_auto h [posRecW_mfr, piBW_mfr _ _ _ _ _ _, snocW_mfr, fgW_mfr n _ _ _ _ _ _ _ _ _ _ _ _ _]

theorem fhW_mfr : ∀ (n : Nat) (m m' : Mem) (hi gO gL aO aL : Word) (r : List Word),
    fhW n m hi gO gL aO aL = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, h => by simp [fhW] at h
  | n + 1, m, m', hi, gO, gL, aO, aL, r, h => by
    unfold fhW fhK1 fhK2 at h
    mfr_auto h [fvinternW_mfr, snocW_mfr, fhW_mfr n _ _ _ _ _ _ _ _]

theorem caW_mfr : ∀ (n : Nat) (m m' : Mem) (us dO dL gO gL aO aL : Word) (r : List Word),
    caW n m us dO dL gO gL aO aL = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [caW] at h
  | n + 1, m, m', us, dO, dL, gO, gL, aO, aL, r, h => by
    unfold caW caK1 caK2 at h
    mfr_auto h [posRecW_mfr, snocW_mfr, caW_mfr n _ _ _ _ _ _ _ _ _ _]

theorem new1W_mfr {m m' : Mem} {x : Word} {r : List Word} (h : new1W m x = some (r, m')) : MFr [] [] m m' :=
  posRecW_mfr (new1W_rec h).1

theorem cpW_mfr : ∀ (n : Nat) (m m' : Mem) (hp dO dL : Word) (r : List Word),
    cpW n m hp dO dL = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, h => by simp [cpW.eq_1] at h
  | n + 1, m, m', hp, dO, dL, r, h => by
    simp only [cpW.eq_2, cpW.k_bvar_b.eq_def, cpW.k_fvar_b.eq_def, cpW.k_nest_cont_params_closed.eq_def] at h
    mfr_auto h [bvbW_mfr, MFr.ofFvbF, cpW_mfr n _ _ _ _ _ _]

end L.Ind

end

end
