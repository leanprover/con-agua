module

public import ConAgua.Arena.IndPartsSpec.IndPartsProg5
import ConAgua.Arena.IndPartsSpec.PartsSliceCopy
public import ConAgua.Arena.IndPartsSpec.PlW
import ConAgua.Arena.IndRealPartsC1
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndPartsSpec.BsW
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.RecClassSpec.CloseLams
import ConRon.Bridge.Grind
public import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.L.WordOff

@[expose] public section

/-!
# BrsW

`resFromW_hit`, `resFromW_01`, `partsResCont`, `partsLpsEq`, `partsResR`, `ipIte01_ne` and the lemmas only they use.
-/

section


/-!
# Refinements of `IndParts`, part 13 (lane `indproofs2`, helper `parts`): `blockShape?`'s pins

The reserved-name and level-parameter pins (`block_shape_pins_formers`/`_recs`/`_ctors`/`_ok`,
pure in the twin: one `Bool`), and the eliminator (`block_shape_large`). Shared pieces: a constant's
level parameters copied by `er_to_iw` (`partsLpsCopy`), `reserved_contains` against the twin's
`reservedBasisNames` (`partsResCont`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `reserved_contains` -/

theorem resFromW_hit (n : Nat) : ∀ (m : Mem) (x j : Word) (b : Word), j.toNat ≤ 16 →
    resFromW n m x j = some b → b ≠ 0 → ∃ i, j.toNat ≤ i ∧ i < 16 ∧ pinW m (55 + i) = x := by
  induction n with
  | zero => intro m x j b _ h; simp [resFromW] at h
  | succ n ih =>
    intro m x j b hj h hb
    rw [resFromW_step] at h
    by_cases h16 : 16 ≤ j
    · rw [ite_eq_left h16] at h; simp at h; exact absurd h.symm hb
    rw [ite_eq_right h16] at h
    have hj16 : j.toNat < 16 := by rw [UInt64.le_iff_toNat_le] at h16; simp at h16; omega
    by_cases he : rdW (m.arr64 PINS) (55 + j) = x
    · refine ⟨j.toNat, Nat.le_refl _, hj16, ?_⟩
      have : (55 + j).toNat = 55 + j.toNat := by rw [UInt64.toNat_add]; simp; omega
      simpa [rdW, pinW, this] using he
    rw [ite_eq_right he] at h
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    obtain ⟨i, hi1, hi2, hi3⟩ := ih m x (j + 1) b (by omega) h hb
    exact ⟨i, by omega, hi2, hi3⟩

theorem resFromW_01 (n : Nat) : ∀ (m : Mem) (x j : Word) (b : Word), resFromW n m x j = some b →
    b = 0 ∨ b = 1 := by
  induction n with
  | zero => intro m x j b h; simp [resFromW] at h
  | succ n ih =>
    intro m x j b h
    rw [resFromW_step] at h
    split at h
    · simp at h; exact Or.inl h.symm
    split at h
    · simp at h; exact Or.inr h.symm
    exact ih _ _ _ _ h

/-- **`reserved_contains` is the twin's `reservedBasisNames.contains`.** -/
theorem partsResCont {m : Mem} {a : AState} {n : Nat} {x b : Word} (hx : x.toNat < 2 ^ 32)
    (h : resContW n m x = some b) (hP : PinsR m a.pins) :
    ∃ R, reservedBasisNames.run a = .ok (R, a) ∧ b = if R.contains (decI x) then 1 else 0 := by
  cases n with
  | zero => simp [resContW] at h
  | succ n =>
  rw [resContW_step] at h
  by_cases h0 : pinW m 0 = 0
  · rw [ite_eq_left h0] at h; simp at h
  rw [ite_eq_right h0] at h
  have hF := hP.full h0
  refine ⟨_, pinReserved_run hF, ?_⟩
  rcases resFromW_01 n m x 0 b h with rfl | rfl
  · have hm := resFromW_miss n m x 0 (by simp) h
    have : ((List.range 16).map fun i => (decI (pinW m (55 + i)) : NIdx)).contains (decI x) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      simp only [List.contains_iff_mem, List.mem_map, List.mem_range] at hc
      obtain ⟨i, hi, e⟩ := hc
      exact hm i (Nat.zero_le _) hi ((decI_eq_iff _ (hF.reserved_lt i hi) _).mp e ▸ decI_word_self x hx)
    rw [this]; rfl
  · obtain ⟨i, -, hi, he⟩ := resFromW_hit n m x 0 1 (by simp) h (by decide)
    have : ((List.range 16).map fun i => (decI (pinW m (55 + i)) : NIdx)).contains (decI x) = true := by
      simp only [List.contains_iff_mem, List.mem_map, List.mem_range]
      exact ⟨i, hi, by rw [he]⟩
    rw [this]; rfl

/-! ## The pins: relations -/

/-- **A constant's level parameters compared with `lps`** (`er_to_iw`, then `sl_eq`). -/
theorem partsLpsEq {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m1 : Mem} {q : Nat} {cv : IConstantVal} {rp : List Word} {lo ll e : Word} {lps : List NIdx}
    (h : erToIwW n m (erRd m (UInt64.ofNat q + 1)) (erRd m (UInt64.ofNat q + 2)) =
      some (rp, m1))
    (he : eqW n m1 (rp.headD 0) (rp.tail.headD 0) lo ll = some e)
    (hS : StageR vis fe m a) (hcv : DecB (fun m => decCVp m q) m cv) (hq : q < 2 ^ 64)
    (hl : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m) :
    StageR vis fe m1 a ∧ IWGrow m m1 ∧ e = if cv.levelParams == lps then 1 else 0 := by
  obtain ⟨hS1, hg1, hd1, ht1⟩ := partsLpsCopy h hS hcv hq
  have hT : iwTop m1 < 2 ^ 64 := (rdW (m1.arr64 CTL) 200).toNat_lt
  obtain ⟨ws1, hs1, hn1, hl1⟩ := slR_of_decHL m1 _ _ _ hd1 (by omega)
  rw [L.ofNat_toNat, L.ofNat_toNat] at hs1
  have hl' : decHL m1 lo.toNat ll.toNat = some lps := by rw [decHL_grow3 hg1 hlb]; exact hl
  obtain ⟨ws2, hs2, hn2, hl2⟩ := slR_of_decHL m1 _ _ _ hl' (by have := hg1.iw; omega)
  rw [L.ofNat_toNat, L.ofNat_toNat] at hs2
  have hres := eqW_ok n m1 _ _ _ _ e ws1 ws2 hs1 hs2 he
  refine ⟨hS1, hg1, ?_⟩
  rw [hn1, hn2, map_decI_beq ws1 ws2 hl1 hl2, hres]
  by_cases hw : ws1 = ws2 <;> simp [hw]

theorem partsResR {a : AState} {R R' : List NIdx} (h : reservedBasisNames.run a = .ok (R, a))
    (h' : reservedBasisNames.run a = .ok (R', a)) : R' = R := by
  rw [h] at h'; simp only [Except.ok.injEq, Prod.mk.injEq] at h'; exact h'.1.symm

theorem ipIte01_ne {c : Bool} {b : Word} (h : b = if c then 1 else 0) : b ≠ 0 ↔ c = true := by
  subst h; cases c <;> simp

theorem ipIte01_eq {c : Bool} {b : Word} (h : b = if c then 1 else 0) : b = 0 ↔ c = false := by
  subst h; cases c <;> simp

/-- **`block_shape_pins_formers`**: no former's name reserved, every former at `lps`. -/
theorem bpfW_ok {vis : Word} {fe : IFEnv} {a : AState} {lo ll : Word}
    {lps R : List NIdx} (hR : reservedBasisNames.run a = .ok (R, a)) (n : Nat) :
    ∀ (m m' : Mem) (cto ctl : Word) (cvTs : List IConstantVal) (r : List Word),
    bpfW n m cto ctl lo ll = some (r, m') → StageR vis fe m a → PSlR decCVp cvTs cto ctl m →
    decHL m lo.toNat ll.toNat = some lps → lo.toNat + ll.toNat ≤ iwTop m →
    StageR vis fe m' a ∧ IWGrow m m' ∧
      r = [if cvTs.all (fun c => !R.contains c.name && c.levelParams == lps) then 1 else 0] := by
  induction n with
  | zero => intro m m' cto ctl cvTs r h; simp [bpfW] at h
  | succ n ih =>
    intro m m' cto ctl cvTs r h hS hts hl hlb
    by_cases hc : ctl = 0
    · rw [bpfW.arm1 n m cto ctl lo ll hc] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hc; rw [partsPSl_nil hts]
      exact ⟨hS, IWGrow.refl _, rfl⟩
    rw [bpfW.arm2 n m cto ctl lo ll hc] at h; simp only [erRd_foldN] at h
    obtain ⟨pc, cv, ts', rfl, hw, hpb, hcv, hts'⟩ := partsPSl_cons hts hc
    rw [hw] at h
    obtain ⟨hnl, hne⟩ := partsCVName (IWGrow.refl m) hcv hpb
    obtain ⟨b, hb, h⟩ := ipK_inv1 h (by simp [bpfW.k_reserved_contains])
    obtain ⟨R', hR', hbv⟩ := partsResCont hnl hb hS.check.pins
    rw [partsResR hR hR', hne] at hbv
    by_cases hb0 : b ≠ 0
    · rw [bpfW.k_reserved_contains.arm1 (hc1 := hb0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : R.contains cv.name = true := (ipIte01_ne hbv).mp hb0
      exact ⟨hS, IWGrow.refl _, by simp only [List.all_cons, this, Bool.not_true, Bool.false_and]; rfl⟩
    rw [bpfW.k_reserved_contains.arm2 (hc1 := Classical.not_not.mp hb0)] at h
    simp only [erRd_foldN] at h
    have hcn : R.contains cv.name = false := Bool.eq_false_iff.mpr (mt (ipIte01_ne hbv).mpr hb0)
    obtain ⟨rp, m1, h1, h⟩ := ipK_inv h (by simp [bpfW.k_er_to_iw])
    rw [bpfW.k_er_to_iw.arm1] at h
    obtain ⟨e, he, h⟩ := ipK_inv1 h (by simp [bpfW.k_sl_eq])
    obtain ⟨hS1, hg1, hev⟩ := partsLpsEq h1 he hS hcv hpb hl hlb
    by_cases he0 : e = 0
    · rw [bpfW.k_sl_eq.arm1 (hc1 := he0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : (cv.levelParams == lps) = false := (ipIte01_eq hev).mp he0
      exact ⟨hS1, hg1, by simp only [List.all_cons, this, Bool.and_false, Bool.false_and]; rfl⟩
    rw [bpfW.k_sl_eq.arm2 (hc1 := he0)] at h
    have heq : (cv.levelParams == lps) = true := by simpa using mt (ipIte01_eq hev).mpr he0
    rcases h2 : bpfW n m1 (cto + 1) (ctl - 1) lo ll with _ | ⟨r2, m2⟩ <;> rw [h2] at h
    · cases h
    rw [bpfW.k_block_shape_pins_formers.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hS2, hg2, hr2⟩ := ih m1 m2 (cto + 1) (ctl - 1) ts' r2 h2 hS1 (hts'.grow (fun _ => OMono.decCVp _) hg1)
      (by rw [decHL_grow3 hg1 hlb]; exact hl) (Nat.le_trans hlb hg1.iw)
    refine ⟨hS2, hg1.trans hg2, ?_⟩
    rw [hr2]; simp only [List.all_cons, hcn, heq, Bool.not_false, Bool.true_and]; rfl

/-- **`block_shape_pins_recs`**: no recursor's name reserved. -/
theorem bprW_ok {vis : Word} {fe : IFEnv} {a : AState}
    {R : List NIdx} (hR : reservedBasisNames.run a = .ok (R, a)) (n : Nat) :
    ∀ (m m' : Mem) (ro rl : Word) (rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule)) (r : List Word),
    bprW n m ro rl = some (r, m') → StageR vis fe m a → PSlR decSR rs ro rl m →
    m' = m ∧ r = [if rs.all (fun r => !R.contains r.1.name) then 1 else 0] := by
  induction n with
  | zero => intro m m' ro rl rs r h; simp [bprW] at h
  | succ n ih =>
    intro m m' ro rl rs r h hS hrs
    by_cases hc : rl = 0
    · rw [bprW.arm1 n m ro rl hc] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hc; rw [partsPSl_nil hrs]
      exact ⟨rfl, rfl⟩
    rw [bprW.arm2 n m ro rl hc] at h; simp only [erRd_foldN] at h
    obtain ⟨pc, ⟨cv, mI, rP, rules⟩, rs', rfl, hw, hpb, hrs0, hrs'⟩ := partsPSl_cons hrs hc
    obtain ⟨⟨cvp, hcvp, hcv⟩, -, -⟩ := decSR_fields (show decSR (truncM m) pc = _ from hrs0)
    obtain ⟨hcw, hcvb, -⟩ := partsIwRd hcvp (UInt64.toNat_ofNat_of_lt' hpb)
    rw [hw, hcw] at h
    obtain ⟨hnl, hne⟩ := partsCVName (IWGrow.refl m) (show DecB (fun m => decCVp m cvp) m cv from hcv) hcvb
    rcases hb : resContW n m (erRd m (UInt64.ofNat cvp)) with _ | b <;> rw [hb] at h
    · simp [bprW.k_reserved_contains] at h
    obtain ⟨R', hR', hbv⟩ := partsResCont hnl hb hS.check.pins
    rw [partsResR hR hR', hne] at hbv
    by_cases hb0 : b ≠ 0
    · rw [bprW.k_reserved_contains.arm1 (hc1 := hb0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : R.contains cv.name = true := (ipIte01_ne hbv).mp hb0
      exact ⟨rfl, by simp only [List.all_cons, this, Bool.not_true, Bool.false_and]; rfl⟩
    rw [bprW.k_reserved_contains.arm2 (hc1 := Classical.not_not.mp hb0)] at h
    have hcn : R.contains cv.name = false := Bool.eq_false_iff.mpr (mt (ipIte01_ne hbv).mpr hb0)
    rcases h2 : bprW n m (ro + 1) (rl - 1) with _ | ⟨r2, m2⟩ <;> rw [h2] at h
    · cases h
    rw [bprW.k_block_shape_pins_recs.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨rfl, hr2⟩ := ih m m2 (ro + 1) (rl - 1) rs' r2 h2 hS hrs'
    refine ⟨rfl, ?_⟩
    rw [hr2]; simp only [List.all_cons, hcn, Bool.not_false, Bool.true_and]; rfl

/-- **`block_shape_pins_ctors`**: every constructor at `nP` and `lps`, no name reserved. -/
theorem bpcW_ok {vis : Word} {fe : IFEnv} {a : AState} {nP lo ll : Word}
    {lps R : List NIdx} (hR : reservedBasisNames.run a = .ok (R, a)) (n : Nat) :
    ∀ (m m' : Mem) (cso csl : Word) (cs : List (IConstantVal × Nat × Nat)) (r : List Word),
    bpcW n m nP cso csl lo ll = some (r, m') → StageR vis fe m a → PSlR decSC cs cso csl m →
    decHL m lo.toNat ll.toNat = some lps → lo.toNat + ll.toNat ≤ iwTop m →
    StageR vis fe m' a ∧ IWGrow m m' ∧
      r = [if cs.all (fun c => c.2.1 == nP.toNat && c.1.levelParams == lps && !R.contains c.1.name)
        then 1 else 0] := by
  induction n with
  | zero => intro m m' cso csl cs r h; simp [bpcW] at h
  | succ n ih =>
    intro m m' cso csl cs r h hS hcs hl hlb
    by_cases hc : csl = 0
    · rw [bpcW.arm1 n m nP cso csl lo ll hc] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hc; rw [partsPSl_nil hcs]
      exact ⟨hS, IWGrow.refl _, rfl⟩
    obtain ⟨pc, ⟨cv0, nP0, nF0⟩, cs', rfl, hw, hpb, hc0, hcs'⟩ := partsPSl_cons hcs hc
    have hd0 : decSC (truncM m) pc = some (cv0, nP0, nF0) := hc0
    simp only [decSC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hd0
    obtain ⟨cvp, hcvp, cv, hcv, nP1, hnP, nF, hnF, e1, e2, e3⟩ := hd0
    subst e1 e2 e3
    have hpw : (UInt64.ofNat pc).toNat = pc := UInt64.toNat_ofNat_of_lt' hpb
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    have hp1 : (UInt64.ofNat pc + 1).toNat = pc + 1 := by
      have := partsIwLt hnP; rw [UInt64.toNat_add, hpw]; simp; omega
    obtain ⟨hcw, hcvb, -⟩ := partsIwRd hcvp hpw
    obtain ⟨hpw1, hnPb, -⟩ := partsIwRd hnP hp1
    have hnpeq : (UInt64.ofNat nP1 = nP) ↔ (nP1 == nP.toNat) = true := by
      simp only [beq_iff_eq]
      constructor
      · intro e; rw [← e, UInt64.toNat_ofNat_of_lt' hnPb]
      · intro e; rw [e, L.ofNat_toNat]
    by_cases hnp : rdW (m.arr64 IW) (rdW (m.arr64 IW) cso + 1) ≠ nP
    · rw [bpcW.arm2 n m nP cso csl lo ll hc hnp] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hw, hpw1] at hnp
      have : (nP1 == nP.toNat) = false := Bool.eq_false_iff.mpr (mt hnpeq.mpr hnp)
      exact ⟨hS, IWGrow.refl _, by simp only [List.all_cons, this, Bool.false_and]; rfl⟩
    rw [bpcW.arm3 n m nP cso csl lo ll hc (Classical.not_not.mp hnp)] at h
    simp only [erRd_foldN] at h
    have hnpt : (nP1 == nP.toNat) = true := by
      rw [hw, hpw1] at hnp; exact hnpeq.mp (by simpa using hnp)
    rw [hw, hcw] at h
    obtain ⟨hnl, hne⟩ := partsCVName (IWGrow.refl m) (show DecB (fun m => decCVp m cvp) m cv from hcv) hcvb
    obtain ⟨b, hb, h⟩ := ipK_inv1 h (by simp [bpcW.k_reserved_contains])
    obtain ⟨R', hR', hbv⟩ := partsResCont hnl hb hS.check.pins
    rw [partsResR hR hR', hne] at hbv
    by_cases hb0 : b ≠ 0
    · rw [bpcW.k_reserved_contains.arm1 (hc1 := hb0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : R.contains cv.name = true := (ipIte01_ne hbv).mp hb0
      exact ⟨hS, IWGrow.refl _, by simp only [List.all_cons, this, Bool.not_true, Bool.and_false, Bool.false_and]; rfl⟩
    rw [bpcW.k_reserved_contains.arm2 (hc1 := Classical.not_not.mp hb0)] at h
    simp only [erRd_foldN] at h
    have hcn : R.contains cv.name = false := Bool.eq_false_iff.mpr (mt (ipIte01_ne hbv).mpr hb0)
    obtain ⟨rp, m1, h1, h⟩ := ipK_inv h (by simp [bpcW.k_er_to_iw])
    rw [bpcW.k_er_to_iw.arm1] at h
    obtain ⟨e, he, h⟩ := ipK_inv1 h (by simp [bpcW.k_sl_eq])
    obtain ⟨hS1, hg1, hev⟩ := partsLpsEq h1 he hS (show DecB (fun m => decCVp m cvp) m cv from hcv) hcvb hl hlb
    by_cases he0 : e = 0
    · rw [bpcW.k_sl_eq.arm1 (hc1 := he0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : (cv.levelParams == lps) = false := (ipIte01_eq hev).mp he0
      exact ⟨hS1, hg1, by simp only [List.all_cons, this, Bool.and_false, Bool.false_and]; rfl⟩
    rw [bpcW.k_sl_eq.arm2 (hc1 := he0)] at h
    have heq : (cv.levelParams == lps) = true := by simpa using mt (ipIte01_eq hev).mpr he0
    rcases h2 : bpcW n m1 nP (cso + 1) (csl - 1) lo ll with _ | ⟨r2, m2⟩ <;> rw [h2] at h
    · cases h
    rw [bpcW.k_block_shape_pins_ctors.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hS2, hg2, hr2⟩ := ih m1 m2 (cso + 1) (csl - 1) cs' r2 h2 hS1 (hcs'.grow decSC_mono hg1)
      (by rw [decHL_grow3 hg1 hlb]; exact hl) (Nat.le_trans hlb hg1.iw)
    refine ⟨hS2, hg1.trans hg2, ?_⟩
    rw [hr2]; simp only [List.all_cons, hcn, heq, hnpt, Bool.not_false, Bool.true_and, Bool.and_true]; rfl

theorem partsW01 {r : List Word} {b : Bool} (h : r = [if b then 1 else 0]) : (r.headD 0 = 0) ↔ b = false := by
  subst h; cases b <;> simp

/-- **`block_shape_pins_ok`**: the three pins, the twin's conjunction. -/
theorem bpoW_ok {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {nP cto ctl lo ll ro rl cso csl : Word} {r : List Word} {cvTs : List IConstantVal}
    {rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule)} {cs : List (IConstantVal × Nat × Nat)}
    {lps R : List NIdx} (hR : reservedBasisNames.run a = .ok (R, a))
    (h : bpoW n m nP cto ctl lo ll ro rl cso csl = some (r, m')) (hS : StageR vis fe m a)
    (hts : PSlR decCVp cvTs cto ctl m) (hrs : PSlR decSR rs ro rl m) (hcs : PSlR decSC cs cso csl m)
    (hl : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      r = [if ((cvTs.all fun c => !R.contains c.name && c.levelParams == lps) &&
          (rs.all fun r => !R.contains r.1.name) &&
          (cs.all fun c => c.2.1 == nP.toNat && c.1.levelParams == lps && !R.contains c.1.name))
        then 1 else 0] := by
  simp only [bpoW, bpoW.k_block_shape_pins_formers.eq_def, bpoW.k_block_shape_pins_recs.eq_def,
    bpoW.k_block_shape_pins_ctors.eq_def] at h
  rcases h1 : bpfW n m cto ctl lo ll with _ | ⟨ra, m1⟩ <;> rw [h1] at h
  · cases h
  simp only at h
  obtain ⟨hS1, hg1, hra⟩ := bpfW_ok hR n m m1 cto ctl cvTs ra h1 hS hts hl hlb
  by_cases ha : ra.headD 0 = 0
  · rw [ite_eq_left ha] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [(partsW01 hra).mp ha]
    exact ⟨hS1, hg1, rfl⟩
  rw [ite_eq_right ha] at h
  have hat : (cvTs.all fun c => !R.contains c.name && c.levelParams == lps) = true := by
    simpa using mt (partsW01 hra).mpr ha
  rcases h2 : bprW n m1 ro rl with _ | ⟨rb, m2⟩ <;> rw [h2] at h
  · cases h
  simp only at h
  obtain ⟨hm2, hrb⟩ := bprW_ok hR n m1 m2 ro rl rs rb h2 hS1 (hrs.grow decSR_mono hg1)
  rw [hm2] at h
  by_cases hb : rb.headD 0 = 0
  · rw [ite_eq_left hb] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [hat, (partsW01 hrb).mp hb]
    exact ⟨hS1, hg1, rfl⟩
  rw [ite_eq_right hb] at h
  have hbt : (rs.all fun r => !R.contains r.1.name) = true := by
    simpa only [Bool.not_eq_false] using mt (partsW01 hrb).mpr hb
  rcases h3 : bpcW n m1 nP cso csl lo ll with _ | ⟨rc, m3⟩ <;> rw [h3] at h
  · cases h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS3, hg3, hrc⟩ := bpcW_ok hR n m1 m3 cso csl cs rc h3 hS1 (hcs.grow decSC_mono hg1)
    (by rw [decHL_grow3 hg1 hlb]; exact hl) (Nat.le_trans hlb hg1.iw)
  refine ⟨hS3, hg1.trans hg3, ?_⟩
  rw [hat, hbt, hrc]; simp only [Bool.true_and]; rfl

/-! ## `block_shape_large` -/

/-- The twin's eliminator choice. -/
def largeOf (lps : List NIdx) (cv : IConstantVal) : Option NIdx :=
  match cv.levelParams with
  | [] => none
  | elim :: relps => if relps == lps && !lps.contains elim then some elim else none

/-- `block_shape_large`'s `(ok, elim)` against the twin's `Option`. -/
def LargeR : Option NIdx → List Word → Prop
  | none, r => r.headD 0 = 0
  | some e, r => r.headD 0 = 1 ∧ H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = e

/-- **`block_shape_large`**: the twin's eliminator choice. -/
theorem bslW_ok {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {cvR0 lo ll : Word} {r : List Word} {cv : IConstantVal} {lps : List NIdx}
    (h : bslW n m cvR0 lo ll = some (r, m')) (hS : StageR vis fe m a)
    (hcv : DecB (fun m => decCVp m cvR0.toNat) m cv)
    (hl : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ LargeR (largeOf lps cv) r := by
  have hcv' : decCV (erA (truncM m)) cvR0.toNat = some cv := hcv
  simp only [decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcv'
  obtain ⟨nm, -, lv, hlv, ce, -, hcvT⟩ := hcv'
  have hlvE : cv.levelParams = lv := by rw [← hcvT]
  simp only [hlist?, bind, Option.bind_eq_some_iff] at hlv
  obtain ⟨o', ho, l', hlw, hsl⟩ := hlv
  have hq2lt : cvR0.toNat + 1 + 1 < 2 ^ 64 := by
    have h' := hlw; simp only [nat?, Option.map_eq_some_iff] at h'
    obtain ⟨_, e, -⟩ := h'; exact erecP_lt64 (truncM_er_get e)
  obtain ⟨w1, hw1b⟩ := partsErRd (IWGrow.refl m) ho (w := cvR0 + 1) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨w2, hw2b⟩ := partsErRd (IWGrow.refl m) hlw (w := cvR0 + 2) (by rw [UInt64.toNat_add]; simp; omega)
  rcases n with _ | n
  · simp [bslW] at h
  have w1' : rdW (m.arr64 (tierA EREC ((cvR0 + 1) >>> 40))) ((cvR0 + 1) &&& 1099511627775) = _ := w1
  have w2' : rdW (m.arr64 (tierA EREC ((cvR0 + 2) >>> 40))) ((cvR0 + 2) &&& 1099511627775) = _ := w2
  rw [bslW.eq_2, w1', w2'] at h
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  by_cases h0 : l' = 0
  · subst h0
    rw [ite_eq_left (show (UInt64.ofNat 0 : Word) = 0 from rfl)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : lv = [] := by simpa [hslice?] using hsl.symm
    refine ⟨hS, IWGrow.refl _, ?_⟩
    simp only [largeOf, hlvE, this, LargeR]; rfl
  rw [ite_eq_right (by intro e; apply h0; have := congrArg UInt64.toNat e; rwa [UInt64.toNat_ofNat_of_lt' hw2b] at this)] at h
  obtain ⟨L, rfl⟩ : ∃ L, l' = L + 1 := ⟨l' - 1, by omega⟩
  rw [hslice?_succ] at hsl
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hsl
  obtain ⟨e, he, relps, hrel, rfl⟩ := hsl
  obtain ⟨w, hw, hwl, hwe⟩ := hd?_some he
  have hw' := truncM_er_get hw
  have hrdw : erRd m (UInt64.ofNat o') = w := erRd_of_erA (by rw [UInt64.toNat_ofNat_of_lt' hw1b]; exact hw')
  have hrdw' : rdW (m.arr64 (tierA EREC (UInt64.ofNat o' >>> 40))) (UInt64.ofNat o' &&& 1099511627775) = w :=
    hrdw
  rw [hrdw'] at h
  have hrel' : hslice? (erA (truncM m)) (UInt64.ofNat o' + 1).toNat L = some relps := by
    rcases L with _ | L
    · simpa [hslice?] using hrel
    · have h' := hrel
      rw [hslice?_succ] at h'
      simp only [bind, Option.bind_eq_some_iff] at h'
      obtain ⟨_, hx, -⟩ := h'
      obtain ⟨w0, hw0, -⟩ := hd?_some hx
      have := erecP_lt64 (truncM_er_get hw0)
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hw1b]; simp only [UInt64.toNat_one]
      rw [Nat.mod_eq_of_lt (by omega)]; exact hrel
  have hl1 : (UInt64.ofNat (L + 1) - 1).toNat = L := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hw2b]; simp)]
    rw [UInt64.toNat_ofNat_of_lt' hw2b]; simp
  rcases h1 : erToIwW n m (UInt64.ofNat o' + 1) (UInt64.ofNat (L + 1) - 1) with _ | ⟨rp, m1⟩ <;> rw [h1] at h
  · rw [bslW.k_er_to_iw.none] at h; cases h
  rw [bslW.k_er_to_iw.arm1] at h
  obtain ⟨hS1, hg1, hd1, ht1⟩ := partsSliceCopy h1 hS (by rw [hl1]; exact hrel')
  rcases he1 : eqW n m1 (rp.headD 0) (rp.tail.headD 0) lo ll with _ | ev <;> rw [he1] at h
  · rw [bslW.k_sl_eq.none] at h; cases h
  rw [bslW.k_sl_eq.eq_2] at h
  have hT1 : iwTop m1 < 2 ^ 64 := (rdW (m1.arr64 CTL) 200).toNat_lt
  obtain ⟨ws1, hs1, hn1, hl1'⟩ := slR_of_decHL m1 _ _ _ hd1 (by omega)
  rw [L.ofNat_toNat, L.ofNat_toNat] at hs1
  have hl' : decHL m1 lo.toNat ll.toNat = some lps := by rw [decHL_grow3 hg1 hlb]; exact hl
  obtain ⟨ws2, hs2, hn2, hl2⟩ := slR_of_decHL m1 _ _ _ hl' (by have := hg1.iw; omega)
  rw [L.ofNat_toNat, L.ofNat_toNat] at hs2
  have hres := eqW_ok n m1 _ _ _ _ ev ws1 ws2 hs1 hs2 he1
  have hbeq : (relps == lps) = decide (ws1 = ws2) := by rw [hn1, hn2, map_decI_beq ws1 ws2 hl1' hl2]
  by_cases hev : ev = 0
  · rw [ite_eq_left hev] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : (relps == lps) = false := by
      rw [hbeq]; by_cases hw12 : ws1 = ws2
      · rw [hres, ite_eq_left hw12] at hev; exact absurd hev (by decide)
      · simp [hw12]
    refine ⟨hS1, hg1, ?_⟩
    simp only [largeOf, hlvE, this, Bool.false_and, LargeR]; rfl
  rw [ite_eq_right hev] at h
  have hrt : (relps == lps) = true := by
    rw [hbeq]; by_cases hw12 : ws1 = ws2
    · simp [hw12]
    · rw [hres, ite_eq_right hw12] at hev; exact absurd rfl hev
  rcases hc : containsW n m1 lo ll w with _ | hsv <;> rw [hc] at h
  · rw [bslW.k_sl_contains.none] at h; cases h
  rw [bslW.k_sl_contains.eq_2] at h
  have hcv2 := containsW_ok n m1 lo ll w hsv ws2 hs2 hc
  have hcont : lps.contains e = ws2.contains w := by rw [hn2, hwe]; exact contains_map_decI w hwl ws2 hl2
  by_cases hh : hsv ≠ 0
  · rw [ite_eq_left hh] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : lps.contains e = true := by rw [hcont]; exact (ipIte01_ne hcv2).mp hh
    refine ⟨hS1, hg1, ?_⟩
    simp only [largeOf, hlvE, hrt, this, Bool.not_true, Bool.and_false, LargeR]; rfl
  rw [ite_eq_right hh] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have : lps.contains e = false := by rw [hcont]; exact Bool.eq_false_iff.mpr (mt (ipIte01_ne hcv2).mpr hh)
  refine ⟨hS1, hg1, ?_⟩
  simp only [largeOf, hlvE, hrt, this, Bool.not_false, Bool.and_true, LargeR, ite_true]
  exact ⟨rfl, hwl, hwe.symm⟩

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

/-! ## The relations -/

/-- **`block_shape_names_of`**: the formers' names. -/
theorem bsnW_ok {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (cto ctl : Word) (cvTs : List IConstantVal) (r : List Word),
    bsnW n m cto ctl = some (r, m') → StageR vis fe m a → PSlR decCVp cvTs cto ctl m →
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (cvTs.map (·.name)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  induction n with
  | zero => intro m m' a cto ctl cvTs r h; simp [bsnW] at h
  | succ n ih =>
    intro m m' a cto ctl cvTs r h hS hts
    by_cases hl : ctl = 0
    · rw [bsnW_nil n m cto ctl hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl; rw [partsPSl_nil hts]
      exact ⟨hS, IWGrow.refl _, by simp [decHL, hslice?], by simp⟩
    rw [bsnW_cons n m cto ctl hl] at h
    obtain ⟨pc, cv0, ts', rfl, hw, hpb, hcv0, hts'⟩ := partsPSl_cons hts hl
    obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (by simp [bsnW.bsnK])
    rw [bsnK_some] at h
    obtain ⟨hS1, hg1, hd1, hb1⟩ := ih m m1 a (cto + 1) (ctl - 1) ts' r1 h1 hS hts'
    have hctolt : cto.toNat < iwTop m := by have := hts.2; have : ctl.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega
    rw [rdW_iw_grow hg1 hctolt, hw] at h
    obtain ⟨hnl, hne⟩ := partsCVName hg1 hcv0 hpb
    rcases h2 : consW n m1 (erRd m1 (UInt64.ofNat pc)) (r1.headD 0) (r1.tail.headD 0) with _ | ⟨r2, m2⟩ <;> rw [h2] at h
    · cases h
    rw [bgoK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hS2, hg2, hd2, ht2⟩ := consW_stage h2 hS1 hb1 hnl hd1
    refine ⟨hS2, hg1.trans hg2, ?_, by simp only [List.headD_cons, List.tail_cons]; omega⟩
    simp only [List.headD_cons, List.tail_cons, List.map_cons]
    rw [← hne]; exact hd2

/-- A fresh record's `IW` word `j`, decoded below the new top. -/
theorem partsFreshN {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m'))
    (hS : StageR vis fe m a) (hl : ws.length < 2 ^ 64) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      ∀ j (hj : j < ws.length), iwN (truncM m') (q.toNat + j) = some (ws[j]).toNat := by
  obtain ⟨h1, h2, -, -, h5⟩ := partsFresh h hS hl
  exact ⟨h1, h2, h5⟩

/-- **`block_shape_ctors_of`**: the constructors as `[cv, nF]`. -/
theorem bctW_ok {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (cso csl : Word) (cs : List (IConstantVal × Nat × Nat)) (r : List Word),
    bctW n m cso csl = some (r, m') → StageR vis fe m a → PSlR decSC cs cso csl m →
    StageR vis fe m' a ∧ IWGrow m m' ∧
      PSlR decCN (cs.map fun c => (c.1, c.2.2)) (r.headD 0) (r.tail.headD 0) m' := by
  induction n with
  | zero => intro m m' a cso csl cs r h; simp [bctW] at h
  | succ n ih =>
    intro m m' a cso csl cs r h hS hcs
    by_cases hl : csl = 0
    · rw [bctW.arm1 n m cso csl hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl; rw [partsPSl_nil hcs]
      exact ⟨hS, IWGrow.refl _, PSlR.nil _ _⟩
    rw [bctW.arm2 n m cso csl hl] at h
    obtain ⟨pc, ⟨cv0, nP0, nF0⟩, cs', rfl, hw, hpb, hc0, hcs'⟩ := partsPSl_cons hcs hl
    rw [hw] at h
    have hd0 : decSC (truncM m) pc = some (cv0, nP0, nF0) := hc0
    simp only [decSC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hd0
    obtain ⟨cvp, hcvp, cv, hcv, nP, hnP, nF, hnF, e1, e2, e3⟩ := hd0
    subst e1 e2 e3
    have hpw : (UInt64.ofNat pc).toNat = pc := UInt64.toNat_ofNat_of_lt' hpb
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    have hp2 : (UInt64.ofNat pc + 2).toNat = pc + 2 := by
      have := partsIwLt hnF; rw [UInt64.toNat_add, hpw]; simp; omega
    obtain ⟨hcw, hcvb, hclt⟩ := partsIwRd hcvp hpw
    obtain ⟨hfw, hfb, hflt⟩ := partsIwRd hnF hp2
    obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (by simp [bctW.k_block_shape_ctors_of])
    rw [bctW.k_block_shape_ctors_of.arm1] at h
    obtain ⟨hS1, hg1, hR1⟩ := ih m m1 a (cso + 1) (csl - 1) cs' r1 h1 hS hcs'
    rw [rdW_iw_grow hg1 (by rw [hpw]; exact hclt), hcw, rdW_iw_grow hg1 (by rw [hp2]; exact hflt),
      hfw] at h
    rcases h2 : posRecW m1 [UInt64.ofNat cvp, UInt64.ofNat nF] with _ | ⟨e, m2⟩ <;> rw [h2] at h
    · simp [bctW.k_rec2] at h
    rw [bctW.k_rec2.arm1] at h
    obtain ⟨hS2, hg2, hget⟩ := partsFreshN h2 hS1 (by simp)
    have g0 := hget 0 (by simp); have g1 := hget 1 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ,
      UInt64.toNat_ofNat_of_lt' hcvb, UInt64.toNat_ofNat_of_lt' hfb] at g0 g1
    have hg02 := hg1.trans hg2
    have hdec : DecB (fun m => decCN m e.toNat) m2 (cv, nF) := by
      show decCN (truncM m2) e.toNat = _
      have hcv2 : decCVp (truncM m2) cvp = some cv :=
        (show DecB (fun m => decCVp m cvp) m cv from hcv).grow (OMono.decCVp _) hg02
      simp only [decCN, g0, g1, hcv2, bind, Option.bind_some, pure]
    rcases h3 : consW n m2 e (r1.headD 0) (r1.tail.headD 0) with _ | ⟨r3, m3⟩ <;> rw [h3] at h
    · simp [bctW.k_sl_cons] at h
    rw [bctW.k_sl_cons.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hR2 := hR1.grow decCN_mono hg2
    obtain ⟨hS3, hg3, hd3, ht3⟩ := partsConsPL decCN_mono h3 hS2 hR2.2 hR2.1 hdec
    exact ⟨hS3, hg02.trans hg3, hd3, Nat.le_of_eq ht3⟩

/-- A number slice's head and tail, below the tops. -/
theorem partsNL_cons {ns : List Nat} {o l : Word} {m : Mem} (h : DecB (fun m => decNL m o.toNat l.toNat) m ns)
    (hb : o.toNat + l.toNat ≤ iwTop m) (hl : l ≠ 0) :
    ∃ x xs, ns = x :: xs ∧ rdW (m.arr64 IW) o = UInt64.ofNat x ∧ x < 2 ^ 64 ∧
      DecB (fun m => decNL m (o + 1).toNat (l - 1).toNat) m xs ∧ (o + 1).toNat + (l - 1).toNat ≤ iwTop m := by
  obtain ⟨L, hL⟩ : ∃ L, l.toNat = L + 1 :=
    ⟨l.toNat - 1, by have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hd : decNL (truncM m) o.toNat (L + 1) = some ns := by have := h; simp only [DecB, hL] at this; exact this
  rw [decNL_succ] at hd
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hd
  obtain ⟨x, hx, xs, hxs, rfl⟩ := hd
  obtain ⟨hw, hxb, holt⟩ := partsIwRd hx rfl
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  refine ⟨x, xs, rfl, hw, hxb, ?_, by rw [ho1, partsPred_of hL]; omega⟩
  show decNL _ _ _ = _; rw [ho1, partsPred_of hL]; exact hxs

/-- **`block_shape_members_of`**: the members, the twin's `zip`s. -/
theorem bmoW_ok {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (cto ctl io go : Word) (cvTs : List IConstantVal) (ns : List Nat)
      (gss : List (List (IConstantVal × Nat))) (r : List Word),
    bmoW n m cto ctl io go = some (r, m') → StageR vis fe m a → PSlR decCVp cvTs cto ctl m →
    DecB (fun m => decNL m io.toNat ctl.toNat) m ns → io.toNat + ctl.toNat ≤ iwTop m →
    PSlR decGH gss go ctl m →
    StageR vis fe m' a ∧ IWGrow m m' ∧
      PSlR decMSB (((cvTs.zip ns).zip gss).map fun a => (⟨a.1.1, a.1.1, a.1.2, a.2⟩ : MemberShape))
        (r.headD 0) (r.tail.headD 0) m' := by
  induction n with
  | zero => intro m m' a cto ctl io go cvTs ns gss r h; simp [bmoW] at h
  | succ n ih =>
    intro m m' a cto ctl io go cvTs ns gss r h hS hts hns hnb hgs
    by_cases hl : ctl = 0
    · rw [bmoW.arm1 n m cto ctl io go hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl; rw [partsPSl_nil hts]
      exact ⟨hS, IWGrow.refl _, PSlR.nil _ _⟩
    rw [bmoW.arm2 n m cto ctl io go hl] at h
    obtain ⟨pc, cv, ts', rfl, hw, hpb, hcv, hts'⟩ := partsPSl_cons hts hl
    obtain ⟨n0, ns', rfl, hnw, hn0b, hns', hnb'⟩ := partsNL_cons hns hnb hl
    obtain ⟨gp, g, gss', rfl, hgw, hgpb, hg0, hgs'⟩ := partsPSl_cons hgs hl
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    have hcl0 : ctl.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
    have hd0 : decGH (truncM m) gp = some g := hg0
    simp only [decGH, decAt, bind, Option.bind_eq_some_iff, decPLB] at hd0
    obtain ⟨goff, hgoff, glen, hglen, hgd⟩ := hd0
    have hgsz : goff + glen ≤ ((truncM m).arr64 IW).size := by
      split at hgd
      · assumption
      · cases hgd
    rw [ite_eq_left hgsz] at hgd
    have hgpw : (UInt64.ofNat gp).toNat = gp := UInt64.toNat_ofNat_of_lt' hgpb
    have hgp1 : (UInt64.ofNat gp + 1).toNat = gp + 1 := by
      have := partsIwLt hglen; rw [UInt64.toNat_add, hgpw]; simp; omega
    obtain ⟨hgow, hgob, hgolt⟩ := partsIwRd hgoff hgpw
    obtain ⟨hglw, hglb, hgllt⟩ := partsIwRd hglen hgp1
    obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (by simp [bmoW.k_block_shape_members_of])
    rw [bmoW.k_block_shape_members_of.arm1] at h
    obtain ⟨hS1, hg1, hR1⟩ := ih m m1 a (cto + 1) (ctl - 1) (io + 1) (go + 1) ts' ns' gss' r1 h1 hS hts'
      hns' hnb' hgs'
    have l1 : cto.toNat < iwTop m := by have := hts.2; omega
    have l2 : io.toNat < iwTop m := by omega
    have l3 : go.toNat < iwTop m := by have := hgs.2; omega
    rw [rdW_iw_grow hg1 l1, hw, rdW_iw_grow hg1 l2, hnw, rdW_iw_grow hg1 l3, hgw,
      rdW_iw_grow hg1 (by rw [hgpw]; exact hgolt), hgow, rdW_iw_grow hg1 (by rw [hgp1]; exact hgllt),
      hglw] at h
    rcases h2 : posRecW m1 [UInt64.ofNat pc, UInt64.ofNat n0, UInt64.ofNat goff, UInt64.ofNat glen,
        UInt64.ofNat pc] with _ | ⟨e, m2⟩ <;> rw [h2] at h
    · simp [bmoW.k_rec5] at h
    rw [bmoW.k_rec5.arm1] at h
    obtain ⟨hS2, hg2, hget⟩ := partsFreshN h2 hS1 (by simp)
    have g0 := hget 0 (by simp); have g1 := hget 1 (by simp); have g2 := hget 2 (by simp)
    have g3 := hget 3 (by simp); have g4 := hget 4 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ, UInt64.toNat_ofNat_of_lt' hpb,
      UInt64.toNat_ofNat_of_lt' hn0b, UInt64.toNat_ofNat_of_lt' hgob, UInt64.toNat_ofNat_of_lt' hglb] at g0 g1 g2 g3 g4
    have hg02 := hg1.trans hg2
    have hdec0 : DecB (fun m => decMS m e.toNat) m2 ⟨cv, cv, n0, g⟩ := by
      show decMS (truncM m2) e.toNat = _
      have hcv2 : decCVp (truncM m2) pc = some cv := hcv.grow (OMono.decCVp _) hg02
      have hgd2 : decPL (truncM m2) (decCN (truncM m2)) goff glen = some g :=
        (show DecB (fun m => decPL m (decCN m) goff glen) m g from hgd).grow (OMono.decPL decCN_mono _ _) hg02
      simp only [decMS, decAt, g0, g1, g4, hcv2, bind, Option.bind_some, pure, Nat.add_assoc,
        show 2 + 1 = 3 from rfl, g2, g3, hgd2]
    have hdec : DecB (fun m => decMSB m e.toNat) m2 ⟨cv, cv, n0, g⟩ := by
      exact decMSB_of hdec0 g2 g3 (le_iwA_truncM_size
        (Nat.le_trans (Nat.le_trans hgsz (iwA_truncM_size_le m)) hg02.iw) hS2.iw.1)
    rcases h3 : consW n m2 e (r1.headD 0) (r1.tail.headD 0) with _ | ⟨r3, m3⟩ <;> rw [h3] at h
    · simp [bmoW.k_sl_cons] at h
    rw [bmoW.k_sl_cons.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hR2 := hR1.grow decMSB_mono hg2
    obtain ⟨hS3, hg3, hd3, ht3⟩ := partsConsPL decMSB_mono h3 hS2 hR2.2 hR2.1 hdec
    exact ⟨hS3, hg02.trans hg3, hd3, Nat.le_of_eq ht3⟩

theorem decSR_fields2 {m : Mem} {p : Nat} {cv : IConstantVal} {mI rP : Nat} {isK : Bool}
    {rules : List IRecRule} (h : decSR m p = some (cv, mI, rP, isK, rules)) :
    ∃ o l, iwN m (p + 3) = some o ∧ iwN m (p + 4) = some l ∧ decRules (erA m) o l = some rules ∧
      iwB m (p + 5) = some isK := by
  simp only [decSR, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, c, hc, d, hd, k, hk, e, he, f, hf, g, hg, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
  exact ⟨e, f, he, hf, hg, hk⟩

/-- A `Bool` word of `IW` read below the top. -/
theorem partsIwB {m : Mem} {i : Nat} {b : Bool} (h : iwB (truncM m) i = some b) {w : Word} (hw : w.toNat = i) :
    (rdW (m.arr64 IW) w != 0) = b ∧ i < iwTop m := by
  simp only [iwB, bool?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨hi, hx'⟩ := truncM_iw_get hx
  simp only [iwA, aread_apply] at hx'
  exact ⟨by rw [rdW_of_get? hw.symm hx'], hi⟩

/-- The recursor shape of a split recursor (the twin's `rs.mapM` body). -/
def brsF (names : List NIdx) (r : IConstantVal × Nat × Nat × Bool × List IRecRule) : AM RecShape := do
  let tgt ← ConRon.Arena.recTargetOf names r.2.1 r.1.type
  pure ⟨r.1, r.2.2.1, r.2.1, tgt, r.2.2.2.2, r.2.2.2.1⟩

/-- **`block_shape_recs_of`'s model refines the twin's `rs.mapM`.** -/
theorem brsW_sim {vis : Word} {fe : IFEnv} {no nl : Word}
    {names : List NIdx} (n : Nat) :
    ∀ (m : Mem) (a : AState) (ro rl : Word) (rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule)),
    StageR vis fe m a → PSlR decSR rs ro rl m →
    DecB (fun m => decHL m no.toNat nl.toNat) m names → no.toNat + nl.toNat ≤ iwTop m →
    Sim (brsW n m no nl ro rl) (rs.mapM (brsF names)) a
      (fun r xs m' a' => PSlR decRS xs (r.headD 0) (r.tail.headD 0) m' ∧ StageR vis fe m' a' ∧
        IWGrow m m') := by
  induction n with
  | zero => intro m a ro rl rs _ _ _ _ r m' e; rw [brsW.eq_1] at e; cases e
  | succ n ih =>
    intro m a ro rl rs hS hrs hnm hnb
    by_cases hl : rl = 0
    · rw [brsW.arm1 n m no nl ro rl hl]
      subst hl; rw [partsPSl_nil hrs]
      exact Sim.ret ⟨PSlR.nil _ _, hS, IWGrow.refl _⟩
    rw [brsW.arm2 n m no nl ro rl hl]
    simp only [erRd_foldN]
    obtain ⟨pc, ⟨cv, mI, rP, isK, rules⟩, rs', rfl, hw, hpb, hrs0, hrs'⟩ := partsPSl_cons hrs hl
    obtain ⟨⟨cvp, hcvp, hcv⟩, hmI, hrP⟩ := decSR_fields (show decSR (truncM m) pc = _ from hrs0)
    obtain ⟨ro', rl', hro', hrl', hru, hisK⟩ := decSR_fields2 (show decSR (truncM m) pc = _ from hrs0)
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    have hpw : (UInt64.ofNat pc).toNat = pc := UInt64.toNat_ofNat_of_lt' hpb
    have hpk : ∀ k : Nat, k ≤ 5 → pc + k < iwTop m → (UInt64.ofNat pc + UInt64.ofNat k).toNat = pc + k := by
      intro k hk hlt; rw [UInt64.toNat_add, hpw, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]; omega
    have hp1 : (UInt64.ofNat pc + 1).toNat = pc + 1 := hpk 1 (by omega) (partsIwLt hmI)
    have hp2 : (UInt64.ofNat pc + 2).toNat = pc + 2 := hpk 2 (by omega) (partsIwLt hrP)
    have hp3 : (UInt64.ofNat pc + 3).toNat = pc + 3 := hpk 3 (by omega) (partsIwLt hro')
    have hp4 : (UInt64.ofNat pc + 4).toNat = pc + 4 := hpk 4 (by omega) (partsIwLt hrl')
    have hp5' : pc + 5 < iwTop m := by
      simp only [iwB, bool?, Option.map_eq_some_iff] at hisK
      obtain ⟨x, hx, -⟩ := hisK; exact (truncM_iw_get hx).1
    have hp5 : (UInt64.ofNat pc + 5).toNat = pc + 5 := hpk 5 (by omega) hp5'
    obtain ⟨hcw, hcvb, hclt⟩ := partsIwRd hcvp hpw
    obtain ⟨hmw, hmb, hmlt⟩ := partsIwRd hmI hp1
    obtain ⟨hrw, hrb, hrlt⟩ := partsIwRd hrP hp2
    obtain ⟨how, hob, holt⟩ := partsIwRd hro' hp3
    obtain ⟨hlw, hlb, hllt⟩ := partsIwRd hrl' hp4
    obtain ⟨hkw, hklt⟩ := partsIwB hisK hp5
    obtain ⟨htyl, htye⟩ := partsCVType hcv (UInt64.toNat_ofNat_of_lt' hcvb)
    rw [hw, hcw, hmw]
    rw [List.mapM_cons]
    simp only [brsF, bind_assoc, pure_bind]
    have hnames : decHL m no.toNat nl.toNat = some names := hnm.get (OMono.decHL _ _)
    refine Sim.bindK (brsW.k_rec_target_of.none ..) (fun _ _ => brsW.k_rec_target_of.arm1 ..)
      (Q := fun r t m1 a1 => r = [UInt64.ofNat t] ∧ t ≤ names.length ∧ StageR vis fe m1 a1 ∧ IWGrow m m1)
      ?_ ?_
    · intro r1 m1 e
      obtain ⟨t, a1, hrun, hr, hS1, hg1⟩ := recTW_ok n (fun _ => none) fe vis m m1 a no nl _ _ r1 names e hS htyl
        hnames (by omega) hnb
      rw [UInt64.toNat_ofNat_of_lt' hmb, htye] at hrun
      exact ⟨t, a1, hrun, hr, partsRecTarget_le hrun, hS1, hg1⟩
    rintro r1 t m1 a1 ⟨rfl, htl, hS1, hg1⟩
    simp only [List.headD_cons]
    intro r m' e
    rw [rdW_iw_grow hg1 (by rw [hpw]; exact hclt), hcw, rdW_iw_grow hg1 (by rw [hp2]; exact hrlt), hrw,
      rdW_iw_grow hg1 (by rw [hp1]; exact hmlt), hmw, rdW_iw_grow hg1 (by rw [hp3]; exact holt), how,
      rdW_iw_grow hg1 (by rw [hp4]; exact hllt), hlw, rdW_iw_grow hg1 (by rw [hp5]; exact hklt)] at e
    rcases h3 : posRecW m1 [UInt64.ofNat cvp, UInt64.ofNat rP, UInt64.ofNat mI, UInt64.ofNat t,
        UInt64.ofNat ro', UInt64.ofNat rl', rdW (m.arr64 IW) (UInt64.ofNat pc + 5)] with _ | ⟨rc, m3⟩ <;>
      rw [h3] at e
    · rw [brsW.k_rec7.none] at e; cases e
    rw [brsW.k_rec7.arm1] at e
    obtain ⟨hS3, hg3, hget⟩ := partsFreshN h3 hS1 (by simp)
    have hnlen : names.length < 2 ^ 64 := by rw [decHL_length _ hnames]; omega
    have g0 := hget 0 (by simp); have g1 := hget 1 (by simp); have g2 := hget 2 (by simp)
    have g3 := hget 3 (by simp); have g4 := hget 4 (by simp); have g5 := hget 5 (by simp)
    have g6 := iwB_of_iwNW (hget 6 (by simp))
    simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ, UInt64.toNat_ofNat_of_lt' hcvb,
      UInt64.toNat_ofNat_of_lt' hrb, UInt64.toNat_ofNat_of_lt' hmb, UInt64.toNat_ofNat_of_lt' hob,
      UInt64.toNat_ofNat_of_lt' hlb, hkw,
      UInt64.toNat_ofNat_of_lt' (show t < 2 ^ 64 by omega)] at g0 g1 g2 g3 g4 g5 g6
    have hg03 := hg1.trans hg3
    have hdec : DecB (fun m => decRS m rc.toNat) m3 ⟨cv, rP, mI, t, rules, isK⟩ := by
      show decRS (truncM m3) rc.toNat = _
      have hcv3 : decCVp (truncM m3) cvp = some cv :=
        (show DecB (fun m => decCVp m cvp) m cv from hcv).grow (OMono.decCVp _) hg03
      have hru3 : decRules (erA (truncM m3)) ro' rl' = some rules :=
        (show DecB (fun m => decRules (erA m) ro' rl') m rules from hru).grow (partsDecRules_mono _ _) hg03
      simp only [decRS, g0, g1, g2, g3, g4, g5, g6, hcv3, hru3, bind, Option.bind_some, pure]
    revert r m' e
    refine Sim.bindK (brsW.k_block_shape_recs_of.none ..) (fun _ _ => brsW.k_block_shape_recs_of.arm1 ..)
      (ih m3 a1 (ro + 1) (rl - 1) rs' hS3 (hrs'.grow decSR_mono hg03) (hnm.grow (OMono.decHL _ _) hg03)
        (Nat.le_trans hnb hg03.iw)) ?_
    rintro r4 xs m4 a4 ⟨hR4, hS4, hg4⟩
    intro r m' e
    rcases h5 : consW n m4 rc (r4.headD 0) (r4.tail.headD 0) with _ | ⟨r5, m5⟩ <;> rw [h5] at e
    · cases e
    rw [brsW.k_sl_cons.arm1] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨hS5, hg5, hd5, ht5⟩ := partsConsPL decRS_mono h5 hS4 hR4.2 hR4.1 (hdec.grow (decRS_mono _) hg4)
    exact ⟨_, a4, rfl, ⟨hd5, Nat.le_of_eq ht5⟩, hS5, ((hg03.trans hg4).trans hg5)⟩

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

theorem getDW_head {m : Mem} {io il : Word} {ns : List Nat} (h : DecB (fun m => decNL m io.toNat il.toNat) m ns)
    (hb : io.toNat + il.toNat ≤ iwTop m) : (getDW m io il 0 0).toNat = ns.headD 0 := by
  unfold getDW
  by_cases hl : il = 0
  · subst hl
    have : ns = [] := by have := h; simp only [DecB, UInt64.toNat_zero] at this; simpa [decNL] using this.symm
    subst this; simp
  rw [ite_eq_right (by rw [UInt64.le_iff_toNat_le]; simp; intro e; exact hl (UInt64.toNat_inj.mp (by simpa using e)))]
  obtain ⟨x, xs, rfl, hw, hxb, -, -⟩ := partsNL_cons h hb hl
  simp [hw, UInt64.toNat_ofNat_of_lt' hxb]

/-- **`block_shape_result_sort`'s model refines the twin's result sort.** -/
theorem bsoW_sim {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    {nP io il ty : Word} {ns : List Nat} (hS : StageR vis fe m a)
    (hns : DecB (fun m => decNL m io.toNat il.toNat) m ns) (hb : io.toNat + il.toNat ≤ iwTop m)
    (hty : H ty) :
    Sim (bsoW m nP io il ty) (bsoTwin nP.toNat ns (decI ty)) a
      (fun r s m' a' => H (r.headD 0) ∧ decI (r.headD 0) = s ∧ StageR vis fe m' a' ∧ IWGrow m m') := by
  intro r m' e
  unfold bsoW at e
  split at e
  · cases e
  rename_i hov
  have hk : (nP + getDW m io il 0 0).toNat = nP.toNat + ns.headD 0 := by
    rw [L.toNat_add_of_not_lt hov, getDW_head hns hb]
  revert r m' e
  have h1 := partsSimW (stripF_pis_ok vis fe (nP + getDW m io il 0 0) ty hty) hS
  rw [hk] at h1
  unfold bsoTwin
  refine Sim.bindK rfl (fun _ _ => by rw [bsoW.k_strip_pis]) h1 ?_
  rintro r1 x1 m1 a1 ⟨hS1, hg1, hd1⟩
  have hz : ∀ (R : List Word → LIdx → Mem → AState → Prop),
      (∀ z, H z → R [z] (decI z) m1 a1) →
      Sim (bsoW.k_pin_word m1 (pinWordV m1 53)) zeroLevel a1 R := by
    intro R hR r m' e
    rcases hp : pinWordV m1 53 with _ | z
    · rw [hp] at e; cases e
    rw [hp] at e; simp only [bsoW.k_pin_word, Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    obtain ⟨hrun, hzh⟩ := pinZero_stage hS1 hp
    exact ⟨_, a1, hrun, hR z hzh⟩
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hd1
    simp only [h0, ite_true]
    exact hz _ fun z hz' => ⟨hz', rfl, hS1, hg1⟩
  | some q =>
    obtain ⟨l1, e1⟩ := q
    obtain ⟨h1', -, hbl, hbe⟩ := hd1
    rw [L.headD_drop_three] at hbl hbe
    simp only [h1', show (1 : Word) ≠ 0 by decide, ite_false]
    intro r m' e
    split at e
    · cases e
    rename_i hne
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m1 a1 hS1.check.arena.base _ hne
    have hvrun := view_run _ a1 v hv
    rw [show (decE (r1.tail.tail.tail.headD 0)) = e1 from hbe] at hvrun
    simp only [StateT.run_bind, hvrun]
    split at e
    · rename_i h2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
      obtain ⟨u, rfl⟩ := (sort_head_iff m1 _ v hvr).mp h2
      obtain ⟨-, hul, hue⟩ := hvr
      have hgd : ∀ l : List Word, l.getD 1 0 = l.tail.headD 0 := fun l => by
        rcases l with _ | ⟨_, _ | _⟩ <;> rfl
      rw [hgd] at hul hue
      exact ⟨u, a1, rfl, hul, hue, hS1, hg1⟩
    · rename_i h2
      have hns : ∀ u, v ≠ .sort u := fun u hu => h2 ((sort_head_iff m1 _ v hvr).mpr ⟨u, hu⟩)
      have hzz := hz (fun r s m' a' => H (r.headD 0) ∧ decI (r.headD 0) = s ∧ StageR vis fe m' a' ∧
        IWGrow m m') (fun z hz' => ⟨hz', rfl, hS1, hg1⟩) r m' e
      cases v with
      | sort u => exact absurd rfl (hns u)
      | _ => exact hzz

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

/-! ## The twin, cut -/

def finJP (nP : Nat) (cvTs : List IConstantVal) (nIdxs : List Nat) (lps : List NIdx)
    (cs : List (IConstantVal × Nat × Nat)) (rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule))
    (cvR0 : IConstantVal) (s : LIdx) : AM (Option BlockShape) := do
  let z ← zeroLevel
  let eq ← lvlEq? s z
  let isProp : Bool := match eq with
    | some true => true
    | some false => false
    | none => false
  let ctors : List (IConstantVal × Nat) := cs.map fun c => (c.1, c.2.2)
  let lvls ← paramLevels lps
  let groups ← ConRon.Arena.blockGroups (cvTs.map (·.name)) lvls nP cvTs.length ctors
  let members : List MemberShape := ((cvTs.zip nIdxs).zip groups).map fun a => ⟨a.1.1, a.1.1, a.1.2, a.2⟩
  let recsL ← rs.mapM fun r => do
    let tgt ← ConRon.Arena.recTargetOf (cvTs.map (·.name)) r.2.1 r.1.type
    pure (⟨r.1, r.2.2.1, r.2.1, tgt, r.2.2.2.2, r.2.2.2.1⟩ : RecShape)
  let large? : Option NIdx := match cvR0.levelParams with
    | [] => none
    | elim :: relps => if relps == lps && !lps.contains elim then some elim else none
  match large? with
  | some elim => pure (some ⟨members, recsL, nP, elim, s, true, isProp⟩)
  | none => do
    let anon ← internNNode .anonymous
    pure (some ⟨members, recsL, nP, anon, s, false, isProp⟩)

def tailJP {X : Type} (nP : Nat) (nIdxs : List Nat) (ty : EIdx) (jp : LIdx → AM X) : AM X := do
  let x ← stripPis (nP + nIdxs.headD 0) ty
  match x with
  | some q => do
    let v ← view q.2
    match v with
    | .sort s => do
      let s ← pure s
      jp s
    | _ => do
      let s ← zeroLevel
      jp s
  | none => do
    let s ← zeroLevel
    jp s

def pinsOf (nP : Nat) (R : List NIdx) (lps : List NIdx) (cvTs : List IConstantVal)
    (cs : List (IConstantVal × Nat × Nat)) (rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule)) : Bool :=
  (cvTs.all fun c => !R.contains c.name && c.levelParams == lps) &&
    (rs.all fun r => !R.contains r.1.name) &&
    (cs.all fun c => c.2.1 == nP && c.1.levelParams == lps && !R.contains c.1.name)

def buildTwin (nPd : Nat) (cvTs : List IConstantVal) (cvT0 : IConstantVal)
    (cs : List (IConstantVal × Nat × Nat)) (rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule))
    (cvR0 : IConstantVal) : AM (Option BlockShape) := do
  match ← blockMemberCounts? nPd cvTs.length cs.length (cvTs.map (·.name)) rs 0 cvTs with
  | none => pure none
  | some nIdxs =>
    let reserved ← reservedBasisNames
    if pinsOf nPd reserved cvT0.levelParams cvTs cs rs then
      tailJP nPd nIdxs cvT0.type (finJP nPd cvTs nIdxs cvT0.levelParams cs rs cvR0)
    else pure none

theorem blockShape_eq (nPd : Nat) (block : List IConstantInfo) :
    ConRon.Arena.blockShape? nPd block = (match ConRon.Arena.blockSplit block with
      | none => pure none
      | some (cvTs, cs, rs) =>
        match cvTs, rs with
        | cvT0 :: _, (cvR0, _, _, _, _) :: _ => buildTwin nPd cvTs cvT0 cs rs cvR0
        | _, _ => pure none) := by
  unfold ConRon.Arena.blockShape?
  rfl

theorem tailJP_eq {X : Type} (nP : Nat) (nIdxs : List Nat) (ty : EIdx) (jp : LIdx → AM X) :
    tailJP nP nIdxs ty jp = bsoTwin nP nIdxs ty >>= jp := by
  unfold tailJP bsoTwin
  rw [bind_assoc]
  congr 1; funext x
  cases x with
  | none => rfl
  | some q =>
    simp only [bind_assoc]
    congr 1; funext v
    cases v <;> simp

/-- **The packed `BlockShape` record, decoded.** -/
theorem partsPack {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {q mo ml ro rl nP elim s lg ip : Word} {ms : List MemberShape} {recs : List RecShape}
    (h : posRecW m [mo, ml, ro, rl, nP, elim, s, lg, ip] = some (q, m')) (hS : StageR vis fe m a)
    (hmsB : PSlR decMSB ms mo ml m) (hrs : PSlR decRS recs ro rl m) (he : H elim) (hs : H s) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      DecB (fun m => decBS m q.toNat) m' ⟨ms, recs, nP.toNat, decI elim, decI s, lg != 0, ip != 0⟩ ∧
      ShapeSl m' q := by
  have hms : PSlR decMS ms mo ml m := ⟨decPL_decMSB hmsB.dec, hmsB.bound⟩
  obtain ⟨hS', hg, htq, hget⟩ := partsFreshGet h hS (by simp)
  refine ⟨hS', hg, ?_, ?_⟩
  rotate_left
  · have gm : ∀ j (hj : j < 9), iwN m' (q.toNat + j) =
        some ([mo, ml, ro, rl, nP, elim, s, lg, ip][j]'(by simpa using hj)).toNat := fun j hj => by
      have := hget j (by simpa using hj)
      rw [← iwN_truncM (show q.toNat + j < iwTop m' by simp at htq; omega)]
      simp only [iwN, nat?, this]; rfl
    have m0 := gm 0 (by omega); have m1 := gm 1 (by omega); have m2 := gm 2 (by omega)
    have m3 := gm 3 (by omega)
    simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at m0 m1 m2 m3
    refine ⟨fun o l ho hl => ?_, fun o l ho hl => ?_, ms, ?_⟩
    · rw [m0] at ho; rw [m1] at hl; cases ho; cases hl; exact Nat.le_trans hms.bound hg.iw
    · rw [m2] at ho; rw [m3] at hl; cases ho; cases hl; exact Nat.le_trans hrs.bound hg.iw
    · have g0 := hget 0 (by simp); have g1 := hget 1 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at g0 g1
      show decAt (truncM m') _ q.toNat = some ms
      simp only [decAt, iwN, nat?, g0, g1, Option.map_some, Option.bind_some, bind]
      exact (hmsB.grow decMSB_mono hg).1
  have g : ∀ j (hj : j < 9), iwA (truncM m') (q.toNat + j) = some ([mo, ml, ro, rl, nP, elim, s, lg, ip][j]'(by simpa using hj)) :=
    fun j hj => hget j (by simpa using hj)
  have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega); have g3 := g 3 (by omega)
  have g4 := g 4 (by omega); have g5 := g 5 (by omega); have g6 := g 6 (by omega); have g7 := g 7 (by omega)
  have g8 := g 8 (by omega)
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hm2 := (hms.grow decMS_mono hg).1
  have hr2 := (hrs.grow decRS_mono hg).1
  show decBS (truncM m') q.toNat = _
  simp only [decBS, decAt, iwN, iwH, iwB, nat?, hd?, bool?, g0, g1, g2, g3, g4, g5, g6, g7, g8, Nat.add_assoc,
    Option.map_some, Option.bind_some, bind, pure]
  have he' : elim.toNat < 2 ^ 32 := he
  have hs' : s.toNat < 2 ^ 32 := hs
  simp only [show decPL (truncM m') (decMS (truncM m')) mo.toNat ml.toNat = some ms from hm2,
    show decPL (truncM m') (decRS (truncM m')) ro.toNat rl.toNat = some recs from hr2, he', hs', ite_true,
    Option.bind_some]

/-- **`block_shape_seal`'s model refines the twin's last `match large?`.** -/
theorem bsealW_sim {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} {mo ml ro2 rl2 nPd s ip lgw elimw : Word} {ms : List MemberShape} {recs : List RecShape}
    {sv : LIdx} {isProp : Bool} {lg : Option NIdx} (hS : StageR vis fe m a)
    (hms : PSlR decMSB ms mo ml m) (hrs : PSlR decRS recs ro2 rl2 m) (hs : H s) (hsv : decI s = sv)
    (hip : (ip != 0) = isProp) (hlg : LargeR lg [lgw, elimw]) :
    Sim (bsealW m mo ml ro2 rl2 nPd s ip lgw elimw)
      (match lg with
        | some elim => pure (some ⟨ms, recs, nPd.toNat, elim, sv, true, isProp⟩)
        | none => do
          let anon ← internNNode .anonymous
          pure (some ⟨ms, recs, nPd.toNat, anon, sv, false, isProp⟩)) a
      (fun r x m' a' => ShapeR x r m' ∧ StageR vis fe m' a' ∧ IWGrow m m') := by
  intro r m' e
  unfold bsealW at e
  cases lg with
  | some el =>
    obtain ⟨h1, he, hee⟩ := hlg
    simp only [List.headD_cons] at h1
    simp only [List.tail_cons, List.headD_cons] at he hee
    rw [ite_eq_left (by rw [h1]; decide)] at e
    rcases h2 : posRecW m [mo, ml, ro2, rl2, nPd, elimw, s, 1, ip] with _ | ⟨q, m2⟩ <;> rw [h2] at e
    · cases e
    rw [bsealW.k_block_shape_pack.arm1] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨hS2, hg2, hd2, hsl2⟩ := partsPack h2 hS hms hrs he hs
    refine ⟨_, a, rfl, ⟨rfl, ?_, hsl2⟩, hS2, hg2⟩
    rw [← hee, ← hsv, ← hip]; exact hd2
  | none =>
    have h1 : lgw = 0 := hlg
    rw [ite_eq_right (by rw [h1]; decide)] at e
    rcases h3 : naF m [] with _ | ⟨r3, m3⟩ <;> rw [h3] at e
    · cases e
    rw [bsealW.k_intern_nanon.arm1] at e
    obtain ⟨an, a3, hrun3, hS3, hg3, hal, hae⟩ := naF_ok (fun _ => none) vis fe m m3 a r3 h3 hS
    rcases h2 : posRecW m3 [mo, ml, ro2, rl2, nPd, r3.headD 0, s, 0, ip] with _ | ⟨q, m2⟩ <;> rw [h2] at e
    · cases e
    rw [bsealW.k_block_shape_pack.arm1] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨hS2, hg2, hd2, hsl2⟩ := partsPack h2 hS3 (hms.grow decMSB_mono hg3) (hrs.grow decRS_mono hg3) hal hs
    refine ⟨some ⟨ms, recs, nPd.toNat, an, sv, false, isProp⟩, a3,
      by simp only [StateT.run_bind, hrun3]; rfl, ⟨rfl, ?_, hsl2⟩, hS2, hg3.trans hg2⟩
    rw [← hae, ← hsv, ← hip]; exact hd2

/-! ## `block_shape_fin` -/

/-- Re-tupling the two result words. -/
theorem _root_.L.Arena.Sim.k3 {α : Type} {mo : Option (List Word × Mem)} {op : AM α} {a : AState}
    {Q R : List Word → α → Mem → AState → Prop} (h : Sim mo op a Q)
    (hq : ∀ r x m a', Q r x m a' → R [r.headD 0, r.tail.headD 0] x m a') : Sim (bgoK3 mo) op a R := by
  intro r m' e
  rcases hm : mo with _ | ⟨r1, m1⟩ <;> rw [hm] at e
  · cases e
  rw [bgoK3_some] at e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
  obtain ⟨x, a', h1, h2⟩ := h r1 m1 hm
  exact ⟨x, a', h1, hq _ _ _ _ h2⟩

/-- A `Sim` also records the twin's run. -/
theorem _root_.L.Arena.Sim.withRun {β α : Type} {mo : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} (h : Sim mo op a Q) :
    Sim mo op a (fun r x m' a' => Q r x m' a' ∧ op.run a = .ok (x, a')) := by
  intro r m' e; obtain ⟨x, a', h1, h2⟩ := h r m' e; exact ⟨x, a', h1, h2, h1⟩

/-- `finJP` after `isProp`. -/
def finRest (nP : Nat) (cvTs : List IConstantVal) (nIdxs : List Nat) (lps : List NIdx)
    (cs : List (IConstantVal × Nat × Nat)) (rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule))
    (cvR0 : IConstantVal) (s : LIdx) (isProp : Bool) : AM (Option BlockShape) := do
  let ctors : List (IConstantVal × Nat) := cs.map fun c => (c.1, c.2.2)
  let lvls ← paramLevels lps
  let groups ← ConRon.Arena.blockGroups (cvTs.map (·.name)) lvls nP cvTs.length ctors
  let members : List MemberShape := ((cvTs.zip nIdxs).zip groups).map fun a => ⟨a.1.1, a.1.1, a.1.2, a.2⟩
  let recsL ← rs.mapM fun r => do
    let tgt ← ConRon.Arena.recTargetOf (cvTs.map (·.name)) r.2.1 r.1.type
    pure (⟨r.1, r.2.2.1, r.2.1, tgt, r.2.2.2.2, r.2.2.2.1⟩ : RecShape)
  let large? : Option NIdx := match cvR0.levelParams with
    | [] => none
    | elim :: relps => if relps == lps && !lps.contains elim then some elim else none
  match large? with
  | some elim => pure (some ⟨members, recsL, nP, elim, s, true, isProp⟩)
  | none => do
    let anon ← internNNode .anonymous
    pure (some ⟨members, recsL, nP, anon, s, false, isProp⟩)

theorem finJP_eq (nP : Nat) (cvTs : List IConstantVal) (nIdxs : List Nat) (lps : List NIdx)
    (cs : List (IConstantVal × Nat × Nat)) (rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule))
    (cvR0 : IConstantVal) (s : LIdx) :
    finJP nP cvTs nIdxs lps cs rs cvR0 s = (do
      let z ← zeroLevel
      let eq ← lvlEq? s z
      finRest nP cvTs nIdxs lps cs rs cvR0 s (isPropOf eq)) := by
  unfold finJP finRest; congr 1

theorem partsMapM_length {α β : Type} (f : α → AM β) : ∀ (l : List α) (a a' : AState) (ys : List β),
    (l.mapM f).run a = .ok (ys, a') → ys.length = l.length
  | [], a, a', ys, h => by simp [StateT.run, pure, StateT.pure, Except.pure] at h; simp [← h.1]
  | x :: l, a, a', ys, h => by
    rw [List.mapM_cons] at h
    simp only [StateT.run_bind] at h
    obtain ⟨⟨y, a1⟩, -, h⟩ := partsExBind h
    obtain ⟨⟨zs, a2⟩, hz, h⟩ := partsExBind h
    have := partsMapM_length f l a1 a2 zs hz
    simp [StateT.run, pure, StateT.pure, Except.pure] at h
    rw [← h.1]; simp [this]

theorem blockGroups_length {names : List NIdx} {lvls : LsIdx} {nP k : Nat} {cs : List (IConstantVal × Nat)}
    {a a' : AState} {gss : List (List (IConstantVal × Nat))}
    (h : (ConRon.Arena.blockGroups names lvls nP k cs).run a = .ok (gss, a')) : gss.length = k := by
  unfold ConRon.Arena.blockGroups at h
  split at h
  · rename_i hk
    simp [StateT.run, pure, StateT.pure, Except.pure] at h
    rw [← h.1]; simp at hk; simp [hk]
  · rw [partsMapM_length _ _ _ _ _ h]; simp

/-- **`block_shape_fin`'s model refines `finRest`.** -/
theorem bfW_sim {vis : Word} {fe : IFEnv} (n : Nat) {m : Mem} {a : AState}
    {nPd cto ctl cso csl rso rsl no nl io lo ll s ip : Word} {cvTs : List IConstantVal} {nIdxs : List Nat}
    {lps : List NIdx} {cs : List (IConstantVal × Nat × Nat)} {r0 : IConstantVal × Nat × Nat × Bool × List IRecRule}
    {rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule)} {sv : LIdx} {isProp : Bool}
    (hS : StageR vis fe m a) (hts : PSlR decCVp cvTs cto ctl m) (hcs : PSlR decSC cs cso csl m)
    (hrs : PSlR decSR (r0 :: rs) rso rsl m)
    (hnm : DecB (fun m => decHL m no.toNat nl.toNat) m (cvTs.map (·.name))) (hnb : no.toNat + nl.toNat ≤ iwTop m)
    (hns : DecB (fun m => decNL m io.toNat ctl.toNat) m nIdxs) (hnsb : io.toNat + ctl.toNat ≤ iwTop m)
    (hl : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hs : H s) (hsv : decI s = sv) (hip : (ip != 0) = isProp) :
    Sim (bfW n m nPd cto ctl cso csl rso rsl no nl io lo ll s ip)
      (finRest nPd.toNat cvTs nIdxs lps cs (r0 :: rs) r0.1 sv isProp) a
      (fun r x m' a' => ShapeR x r m' ∧ StageR vis fe m' a' ∧ IWGrow m m') := by
  have hctl : cvTs.length = ctl.toNat := decPL_length _ hts.dec
  -- `cvR0`, read first
  have hrl : rsl ≠ 0 := by
    intro e; subst e; exact absurd (partsPSl_nil hrs) (by simp)
  obtain ⟨pc, r0', rs', he, hw, hpb, hr0, -⟩ := partsPSl_cons hrs hrl
  simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
  obtain ⟨⟨cvp, hcvp, hcv⟩, -, -⟩ := decSR_fields (show decSR (truncM m) pc = some (r0.1, r0.2.1, r0.2.2.1, r0.2.2.2.1, r0.2.2.2.2) from hr0)
  obtain ⟨hcw, hcvb, -⟩ := partsIwRd hcvp (UInt64.toNat_ofNat_of_lt' hpb)
  intro r m' e
  unfold bfW at e
  rw [hw, hcw] at e
  -- `block_shape_ctors_of` (model only)
  rcases h1 : bctW (n + 1) m cso csl with _ | ⟨r1, m1⟩ <;> rw [h1] at e
  · cases e
  rw [bbK8_some] at e
  obtain ⟨hS1, hg1, hct⟩ := bctW_ok (n + 1) m m1 a cso csl cs r1 h1 hS hcs
  revert r m' e
  unfold finRest
  -- `param_levels`
  refine Sim.bindK rfl (fun _ _ => by rw [bbK9])
    (plW_sim hS1 (by rw [decHL_grow3 hg1 hlb]; exact hl) (Nat.le_trans hlb hg1.iw)) ?_
  rintro r2 lvls m2 a2 ⟨hlh, hlv, hS2, hg2⟩
  have hg02 := hg1.trans hg2
  -- `block_groups`
  have hgr := bgW_sim (no := no) (nl := nl) (nP := nPd) (k := ctl) hlh n hS2 (hct.grow decCN_mono hg2)
    (hnm.grow (OMono.decHL _ _) hg02) (Nat.le_trans hnb hg02.iw)
  rw [hlv, ← hctl] at hgr
  refine Sim.bindK rfl (fun _ _ => by rw [bbK10]) hgr.withRun ?_
  rintro r3 gss m3 a3 ⟨⟨hgs, hS3, hg3⟩, hgrun⟩
  have hg03 := hg02.trans hg3
  have hgl : (r3.tail.headD 0) = ctl := by
    apply UInt64.toNat_inj.mp
    rw [← decPL_length _ hgs.dec, blockGroups_length hgrun, hctl]
  rw [hgl] at hgs
  -- `block_shape_members_of` (model only)
  intro r m' e
  rcases h4 : bmoW (n + 1) m3 cto ctl io (r3.headD 0) with _ | ⟨r4, m4⟩ <;> rw [h4] at e
  · cases e
  rw [bbK11_some] at e
  obtain ⟨hS4, hg4, hms⟩ := bmoW_ok (n + 1) m3 m4 a3 cto ctl io (r3.headD 0) cvTs nIdxs gss r4 h4 hS3
    (hts.grow (fun _ => OMono.decCVp _) hg03) (hns.grow (OMono.decNL _ _) hg03)
    (Nat.le_trans hnsb hg03.iw) hgs
  have hg04 := hg03.trans hg4
  revert r m' e
  show Sim _ _ a3 _
  -- `block_shape_recs_of`
  refine Sim.bindK rfl (fun _ _ => by rw [bbK12])
    (brsW_sim (n + 1) m4 a3 rso rsl (r0 :: rs) hS4 (hrs.grow decSR_mono hg04) (hnm.grow (OMono.decHL _ _) hg04)
      (Nat.le_trans hnb hg04.iw)) ?_
  rintro r5 recsL m5 a5 ⟨hrsl, hS5, hg5⟩
  have hg05 := hg04.trans hg5
  -- `block_shape_large` (model only)
  intro r m' e
  rcases h6 : bslW (n + 1) m5 (UInt64.ofNat cvp) lo ll with _ | ⟨r6, m6⟩ <;> rw [h6] at e
  · cases e
  simp only [bbK13'] at e
  obtain ⟨hS6, hg6, hlg⟩ := bslW_ok h6 hS5 (by rw [UInt64.toNat_ofNat_of_lt' hcvb]; exact (show DecB (fun m => decCVp m cvp) m r0.1 from hcv).grow (OMono.decCVp _) hg05)
    (by rw [decHL_grow3 hg05 hlb]; exact hl) (Nat.le_trans hlb hg05.iw)
  have hlg' : LargeR (largeOf lps r0.1) [r6.headD 0, r6.tail.headD 0] := by
    cases hx : largeOf lps r0.1 <;> rw [hx] at hlg <;> exact hlg
  revert r m' e
  show Sim _ _ a5 _
  refine Sim.k3 (bsealW_sim hS6 (hms.grow decMSB_mono (hg5.trans hg6)) (hrsl.grow decRS_mono hg6) hs hsv hip hlg') ?_
  rintro r7 x m7 a7 ⟨hR7, hS7, hg7⟩
  refine ⟨?_, hS7, hg05.trans (hg6.trans hg7)⟩
  cases x with
  | none => exact hR7
  | some bs => exact hR7

/-- A `Sim` also records the model's run. -/
theorem _root_.L.Arena.Sim.withEq {β α : Type} {mo : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} (h : Sim mo op a Q) :
    Sim mo op a (fun r x m' a' => Q r x m' a' ∧ mo = some (r, m')) := by
  intro r m' e; obtain ⟨x, a', h1, h2⟩ := h r m' e; exact ⟨x, a', h1, h2, e⟩

/-- **`block_shape_tail`'s model refines the twin's result sort and the rest (`tailJP`).** -/
theorem btW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (c : CallM) (n : Nat) {m : Mem} {a : AState}
    {nPd cto ctl cso csl rso rsl no nl io lo ll : Word} {cvT0 : IConstantVal} {cvTs : List IConstantVal}
    {nIdxs : List Nat} {cs : List (IConstantVal × Nat × Nat)} {r0 : IConstantVal × Nat × Nat × Bool × List IRecRule}
    {rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule)}
    (hS : StageR vis fe m a) (hts : PSlR decCVp (cvT0 :: cvTs) cto ctl m) (hcs : PSlR decSC cs cso csl m)
    (hrs : PSlR decSR (r0 :: rs) rso rsl m)
    (hnm : DecB (fun m => decHL m no.toNat nl.toNat) m ((cvT0 :: cvTs).map (·.name)))
    (hnb : no.toNat + nl.toNat ≤ iwTop m)
    (hns : DecB (fun m => decNL m io.toNat ctl.toNat) m nIdxs) (hnsb : io.toNat + ctl.toNat ≤ iwTop m)
    (hl : decHL m lo.toNat ll.toNat = some cvT0.levelParams) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hc : LvlHyp c n dn vis fe m (fun sv a1 => (bsoTwin nPd.toNat nIdxs cvT0.type).run a = .ok (sv, a1))) :
    Sim (btW c n m nPd cto ctl cso csl rso rsl no nl io ctl lo ll)
      (tailJP nPd.toNat nIdxs cvT0.type
        (finJP nPd.toNat (cvT0 :: cvTs) nIdxs cvT0.levelParams cs (r0 :: rs) r0.1)) a
      (fun r x m' a' => ShapeR x r m' ∧ StageR vis fe m' a' ∧ IWGrow m m') := by
  have hctl : ctl ≠ 0 := by intro e; subst e; exact absurd (partsPSl_nil hts) (by simp)
  obtain ⟨p0, cv0, ts', he, hw, hpb, hcv0, -⟩ := partsPSl_cons hts hctl
  simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
  obtain ⟨htyl, htye⟩ := partsCVType hcv0 (UInt64.toNat_ofNat_of_lt' hpb)
  rw [tailJP_eq]
  unfold btW
  rw [hw]
  refine Sim.bindK rfl (fun _ _ => by rw [btK1])
    (Q := fun r s m' a' => ((H (r.headD 0) ∧ decI (r.headD 0) = s ∧ StageR vis fe m' a' ∧ IWGrow m m') ∧
      (bsoTwin nPd.toNat nIdxs cvT0.type).run a = .ok (s, a')) ∧
      bsoW m nPd io ctl (erRd m (UInt64.ofNat p0 + 3)) = some (r, m')) ?_ ?_
  · have := bsoW_sim (nP := nPd) (ty := erRd m (UInt64.ofNat p0 + 3)) hS hns hnsb htyl
    rw [htye] at this
    exact this.withRun.withEq
  rintro r1 sv m1 a1 ⟨⟨⟨hs, hsv, hS1, hg1⟩, hrun1⟩, he1⟩
  rw [finJP_eq]
  intro r m' e
  rcases hz : pinWordV m1 53 with _ | z <;> rw [hz] at e
  · cases e
  rw [btK2_some] at e
  obtain ⟨hzrun, -⟩ := pinZero_stage hS1 hz
  revert r m' e
  refine Sim.bind_twin hzrun ?_
  refine Sim.bindK rfl (fun _ _ => by rw [btK3])
    (Q := fun r x m' a' => KeepPost vis fe decLvlEq m1 m' a' r x) ?_ ?_
  · exact hc sv a1 (r1.headD 0) z m1 hrun1 (bsoW_afr he1) hS1 hs hsv hz
  rintro r2 x2 m2 a2 ⟨hS2, hg2, hd2⟩
  have hg02 := hg1.trans hg2
  refine Sim.k3 (bfW_sim n hS2 (hts.grow (fun _ => OMono.decCVp _) hg02) (hcs.grow decSC_mono hg02)
    (hrs.grow decSR_mono hg02) (hnm.grow (OMono.decHL _ _) hg02) (Nat.le_trans hnb hg02.iw)
    (hns.grow (OMono.decNL _ _) hg02) (Nat.le_trans hnsb hg02.iw) (by rw [decHL_grow3 hg02 hlb]; exact hl)
    (Nat.le_trans hlb hg02.iw) hs hsv (lvlEq_prop rfl hd2)) ?_
  rintro r x m3 a3 ⟨hR, hS3, hg3⟩
  exact ⟨by cases x <;> exact hR, hS3, hg02.trans hg3⟩

/-! ## `block_shape_build` -/

theorem partsBindOk {α β : Type} {x : AM α} {f : α → AM β} {a a' : AState} {v : β}
    (h : (x >>= f).run a = .ok (v, a')) : ∃ y a1, x.run a = .ok (y, a1) ∧ (f y).run a1 = .ok (v, a') := by
  simp only [StateT.run_bind] at h
  obtain ⟨⟨y, a1⟩, h1, h2⟩ := partsExBind h
  exact ⟨y, a1, h1, h2⟩

theorem bmc_length {nPd k nC : Nat} {names : List NIdx} {rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule)} :
    ∀ (cvTs : List IConstantVal) (mm : Nat) (a a' : AState) (ns : List Nat),
    (ConRon.Arena.blockMemberCounts? nPd k nC names rs mm cvTs).run a = .ok (some ns, a') →
    ns.length = cvTs.length
  | [], mm, a, a', ns, h => by
    simp [ConRon.Arena.blockMemberCounts?, StateT.run, pure, StateT.pure, Except.pure] at h; simp [← h]
  | c :: cs, mm, a, a', ns, h => by
    simp only [ConRon.Arena.blockMemberCounts?] at h
    obtain ⟨q, a1, -, h⟩ := partsBindOk h
    obtain ⟨x, a2, -, h⟩ := partsBindOk h
    cases x with
    | none => simp [StateT.run, pure, StateT.pure, Except.pure] at h
    | some c2 =>
      simp only at h
      obtain ⟨y, a3, hy, h⟩ := partsBindOk h
      cases y with
      | none => simp [StateT.run, pure, StateT.pure, Except.pure] at h
      | some ns' =>
        simp [StateT.run, pure, StateT.pure, Except.pure] at h
        rw [← h.1]; simp [bmc_length cs (mm + 1) a2 a3 ns' hy]

/-- `block_member_counts`' model as a `Sim` (from `blockMemberCounts_refines`' proof). -/
theorem bmcW_sim {vis : Word} {fe : IFEnv} (n : Nat) {m : Mem} {a : AState}
    {nPd k nC no nl ro rl cto ctl : Word} {names : List NIdx} {cvTs : List IConstantVal}
    {rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule)}
    (hS : StageR vis fe m a) (hts : PSlR decCVp cvTs cto ctl m)
    (hrs : PSlR decSR rs ro rl m) (hnm : DecB (fun m => decHL m no.toNat nl.toNat) m names)
    (hnb : no.toNat + nl.toNat ≤ iwTop m) :
    Sim (bmcW n m nPd k nC no nl ro rl cto ctl)
      (ConRon.Arena.blockMemberCounts? nPd.toNat k.toNat nC.toNat names rs 0 cvTs) a
      (fun r x m' a' => NsR x r m' ∧ StageR vis fe m' a' ∧ IWGrow m m') := by
  intro r m' hm
  unfold bmcW at hm
  split at hm
  · cases hm
  rename_i hg
  have b : ∀ w : Word, ¬ 4294967296 ≤ w → w.toNat < 2 ^ 32 := fun w h => by
    rw [UInt64.le_iff_toNat_le] at h; simpa using h
  have hsim := bmgW_sim (b nPd (fun h => hg (Or.inl h))) (b k (fun h => hg (Or.inr (Or.inl h))))
    (b nC (fun h => hg (Or.inr (Or.inr (Or.inl h))))) (b rl (fun h => hg (Or.inr (Or.inr (Or.inr h))))) n
    m a cto ctl 0 cvTs hS hts hrs hnm hnb (by simp; have := hts.bound; omega)
  rcases hb : bmgW n m nPd k nC no nl ro rl cto ctl 0 with _ | ⟨r1, m1⟩ <;> rw [hb] at hm
  · cases hm
  rw [bmcW.k_block_member_counts_go.arm1] at hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
  obtain ⟨x, a', h1, hR, hS', hg'⟩ := hsim r1 m1 hb
  exact ⟨x, a', h1, NsR_three hR, hS', hg'⟩

/-- A pins pass that returned read the reserved names: the pins are ready. -/
theorem bpoW_ready {n : Nat} {m m' : Mem} {nP cto ctl lo ll ro rl cso csl : Word} {r : List Word}
    (h : bpoW n m nP cto ctl lo ll ro rl cso csl = some (r, m')) (hc : ctl ≠ 0) : pinW m 0 ≠ 0 := by
  simp only [bpoW, bpoW.k_block_shape_pins_formers.eq_def, bpoW.k_block_shape_pins_recs.eq_def,
    bpoW.k_block_shape_pins_ctors.eq_def] at h
  rcases h1 : bpfW n m cto ctl lo ll with _ | x
  · rw [h1] at h; cases h
  cases n with
  | zero => simp [bpfW] at h1
  | succ n =>
  rw [bpfW.arm2 n m cto ctl lo ll hc] at h1; simp only [erRd_foldN] at h1
  rcases h2 : resContW n m (erRd m (rdW (m.arr64 IW) cto)) with _ | b
  · rw [h2] at h1; simp [bpfW.k_reserved_contains] at h1
  cases n with
  | zero => simp [resContW] at h2
  | succ n =>
  rw [resContW_step] at h2
  intro h0; rw [ite_eq_left h0] at h2; cases h2

/-- **`block_shape_build`'s model refines `buildTwin`.** -/
theorem bbW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (c : CallM) (n : Nat) {m : Mem} {a : AState}
    {nPd cto ctl cso csl rso rsl : Word} {cvT0 : IConstantVal} {cvTs : List IConstantVal}
    {cs : List (IConstantVal × Nat × Nat)} {r0 : IConstantVal × Nat × Nat × Bool × List IRecRule}
    {rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule)}
    (hS : StageR vis fe m a) (hts : PSlR decCVp (cvT0 :: cvTs) cto ctl m) (hcs : PSlR decSC cs cso csl m)
    (hrs : PSlR decSR (r0 :: rs) rso rsl m)
    (hc : LvlHyp c n dn vis fe m (TbbT nPd.toNat cvT0 (cvT0 :: cvTs) cs (r0 :: rs) a)) :
    Sim (bbW c n m nPd cto ctl cso csl rso rsl) (buildTwin nPd.toNat (cvT0 :: cvTs) cvT0 cs (r0 :: rs) r0.1) a
      (fun r x m' a' => ShapeR x r m' ∧ StageR vis fe m' a' ∧ IWGrow m m') := by
  have hctl : ctl ≠ 0 := by intro e; subst e; exact absurd (partsPSl_nil hts) (by simp)
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨p0, cv0, ts', he, hw, hpb, hcv0, -⟩ := partsPSl_cons hts hctl
  simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
  have hlen : (cvT0 :: cvTs).length = ctl.toNat := decPL_length _ hts.dec
  have hclen : cs.length = csl.toNat := decPL_length _ hcs.dec
  intro r m' e
  unfold bbW at e
  rw [hw] at e
  -- names (model only)
  rcases h1 : bsnW (n + 3) m cto ctl with _ | ⟨r1, m1⟩ <;> rw [h1] at e
  · cases e
  rw [bbH1_some] at e
  obtain ⟨hS1, hg1, hd1, hb1⟩ := bsnW_ok (n + 3) m m1 a cto ctl (cvT0 :: cvTs) r1 h1 hS hts
  revert r m' e
  unfold buildTwin
  -- member counts
  have hmc := bmcW_sim (n + 2) (nPd := nPd) (k := ctl) (nC := csl) hS1 (hts.grow (fun _ => OMono.decCVp _) hg1)
    (hrs.grow decSR_mono hg1) (decHL_decB hd1 hb1) hb1
  rw [← hlen, ← hclen] at hmc
  refine Sim.bindK rfl (fun _ _ => by rw [bbH2]) hmc.withRun.withEq ?_
  rintro r2 x2 m2 a2 ⟨⟨⟨hR2, hS2, hg2⟩, hrun2⟩, he2⟩
  have hg02 := hg1.trans hg2
  cases x2 with
  | none =>
    have h0 : r2.headD 0 = 0 := hR2
    simp only [h0, ite_true]
    exact Sim.ret ⟨rfl, hS2, hg02⟩
  | some nIdxs =>
  obtain ⟨h21, hd2, hb2⟩ := hR2
  simp only [h21, show (1 : Word) ≠ 0 by decide, ite_false]
  -- level parameters (model only)
  intro r m' e
  rcases h3 : erToIwW (n + 3) m2 (erRd m2 (UInt64.ofNat p0 + 1)) (erRd m2 (UInt64.ofNat p0 + 2)) with _ | ⟨r3, m3⟩ <;> rw [h3] at e
  · cases e
  rw [bbH3_some] at e
  obtain ⟨hS3, hg3, hd3, ht3⟩ := partsLpsCopy h3 hS2 (hcv0.grow (OMono.decCVp _) hg02) hpb
  have hg03 := hg02.trans hg3
  -- the pins
  rcases h4 : bpoW (n + 2) m3 nPd cto ctl (r3.headD 0) (r3.tail.headD 0) rso rsl cso csl with _ | ⟨r4, m4⟩ <;> rw [h4] at e
  · cases e
  have h0 := bpoW_ready h4 hctl
  have hRrun := pinReserved_run (hS3.check.pins.full h0)
  obtain ⟨hS4, hg4, hr4⟩ := bpoW_ok hRrun h4 hS3 (hts.grow (fun _ => OMono.decCVp _) hg03)
    (hrs.grow decSR_mono hg03) (hcs.grow decSC_mono hg03) hd3 (Nat.le_of_eq ht3)
  have hg04 := hg03.trans hg4
  have hr4' : r4 = [if pinsOf nPd.toNat ((List.range 16).map fun i => decI (pinW m3 (55 + i)))
      cvT0.levelParams (cvT0 :: cvTs) cs (r0 :: rs) then 1 else 0] := hr4
  revert r m' e
  refine Sim.bind_twin hRrun ?_
  cases hpb : pinsOf nPd.toNat ((List.range 16).map fun i => decI (pinW m3 (55 + i)))
      cvT0.levelParams (cvT0 :: cvTs) cs (r0 :: rs) with
  | false =>
    rw [hpb] at hr4'
    rw [bbH4_fail (h := by rw [hr4']; rfl)]
    exact Sim.ret ⟨rfl, hS4, hg04⟩
  | true =>
  rw [hpb] at hr4'
  rw [bbH4_ok (h := by rw [hr4']; decide)]
  simp only [ite_true]
  have hil : r2.tail.tail.headD 0 = ctl := by
    apply UInt64.toNat_inj.mp
    have e1 := mapM_opt_length _ _ _ (show decNL (truncM m2) _ _ = some nIdxs from hd2)
    simp only [List.length_range] at e1
    rw [← e1, bmc_length _ _ _ _ _ hrun2, hlen]
  rw [hil] at hd2 hb2 ⊢
  refine Sim.k3 (btW_sim c n hS4 (hts.grow (fun _ => OMono.decCVp _) hg04) (hcs.grow decSC_mono hg04)
    (hrs.grow decSR_mono hg04) ((decHL_decB hd1 hb1).grow (OMono.decHL _ _) (hg2.trans (hg3.trans hg4)))
    (Nat.le_trans hb1 (hg2.trans (hg3.trans hg4)).iw) (hd2.grow (OMono.decNL _ _) (hg3.trans hg4))
    (Nat.le_trans hb2 (hg3.trans hg4).iw) (by rw [decHL_grow3 hg4 (Nat.le_of_eq ht3)]; exact hd3)
    (Nat.le_trans (Nat.le_of_eq ht3) hg4.iw)
    (hc.mono ((bsnW_afr _ _ _ _ _ _ h1).trans ((bmcW_afr he2).trans ((erToIwW_afr h3).trans (bpoW_afr h4))))
      (fun sv a1 h => ⟨nIdxs, a2, _, a2, hrun2, hRrun, h⟩))) ?_
  rintro r x m5 a5 ⟨hR, hS5, hg5⟩
  exact ⟨by cases x <;> exact hR, hS5, hg04.trans hg5⟩

theorem partsW0 {α : Type} {f : Mem → Nat → Option α} {xs : List α} {o l : Word} {m : Mem}
    (h : PSlR f xs o l m) : (l = 0) ↔ xs = [] := by
  have := decPL_length _ h.dec
  constructor
  · intro e; subst e; simpa using this
  · intro e; subst e; exact UInt64.toNat_inj.mp (by simpa using this.symm)

/-- **`block_shape`'s model refines `blockShape?`.** -/
theorem bshW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (c : CallM) (n : Nat) {m : Mem}
    {a : AState} {nPd off l : Word} {blk : List IConstantInfo} (hS : StageR vis fe m a)
    (hblk : DecB (fun m => decEBlk dn m off.toNat l.toNat) m blk)
    (hc : LvlHyp c n dn vis fe m (TshT nPd.toNat blk a)) :
    Sim (bshW c n m nPd off l) (ConRon.Arena.blockShape? nPd.toNat blk) a
      (fun r x m' a' => ShapeR x r m' ∧ StageR vis fe m' a' ∧ IWGrow m m') := by
  rw [blockShape_eq]
  intro r m' e
  unfold bshW at e
  rcases h1 : bsW (n + 4) m off l with _ | ⟨r1, m1⟩ <;> rw [h1] at e
  · cases e
  simp only at e
  obtain ⟨hS1, hg1, hR1⟩ := bsW_ok (n + 4) m m1 a off l blk r1 h1 hS hblk
  revert r m' e
  cases hsp : ConRon.Arena.blockSplit blk with
  | none =>
    rw [hsp] at hR1
    have h0 : r1.headD 0 = 0 := hR1
    intro r m' e
    rw [ite_eq_left h0] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    exact ⟨none, a, rfl, rfl, hS1, hg1⟩
  | some t =>
  obtain ⟨cvTs, cs, rs⟩ := t
  rw [hsp] at hR1
  obtain ⟨h01, hq6, hts, hcs, hrs⟩ := hR1
  intro r m' e
  rw [ite_eq_right (by rw [h01]; decide)] at e
  dsimp only
  generalize hq : r1.tail.headD 0 = q at e hq6 hts hcs hrs
  by_cases hz : rdW (m1.arr64 IW) (q + 1) = 0 ∨ rdW (m1.arr64 IW) (q + 5) = 0
  · rw [ite_eq_left hz] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    have : cvTs = [] ∨ rs = [] := by
      rcases hz with hz | hz
      · exact Or.inl ((partsW0 hts).mp hz)
      · exact Or.inr ((partsW0 hrs).mp hz)
    refine ⟨none, a, ?_, rfl, hS1, hg1⟩
    rcases this with rfl | rfl
    · rfl
    · cases cvTs <;> rfl
  rw [ite_eq_right hz] at e
  obtain ⟨cvT0, cvTs', rfl⟩ : ∃ c cs', cvTs = c :: cs' := by
    cases cvTs with
    | nil => exact absurd (Or.inl ((partsW0 hts).mpr rfl)) hz
    | cons c cs' => exact ⟨c, cs', rfl⟩
  obtain ⟨r0, rs', rfl⟩ : ∃ c cs', rs = c :: cs' := by
    cases rs with
    | nil => exact absurd (Or.inr ((partsW0 hrs).mpr rfl)) hz
    | cons c cs' => exact ⟨c, cs', rfl⟩
  revert r m' e
  show Sim _ (buildTwin nPd.toNat (cvT0 :: cvTs') cvT0 cs (r0 :: rs') r0.1) a _
  refine Sim.k3 (bbW_sim c n hS1 hts hcs hrs
    (hc.mono (bsW_afr _ _ _ _ _ _ h1) (fun sv a1 h => ⟨cvT0, cvTs', cs, r0, rs', hsp, h⟩))) ?_
  rintro r x m2 a2 ⟨hR, hS2, hg2⟩
  exact ⟨by cases x <;> exact hR, hS2, hg1.trans hg2⟩

end L.Ind

end

end
