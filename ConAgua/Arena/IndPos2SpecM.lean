import ConAgua.Arena.IndPos2SpecL

/-! # `IndPos2`, the `nestPos` block's leaves, continued (lane `indproofs2`, helper `pos2`): the
walk's state record (`NestState`, decoded below the tops), `nest_cont_new_finish`. -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The walk's state, below the tops -/

/-- A `NestState` record at `p`: decoded below the tops, its three slices below the top. -/
structure NSB (m : Mem) (p : Word) (NS : NestState) : Prop where
  dec : DecB (fun m => decNS m p.toNat) m NS
  b0 : (rdW (m.arr64 IW) p).toNat + (rdW (m.arr64 IW) (p + 1)).toNat ≤ iwTop m
  b2 : (rdW (m.arr64 IW) (p + 2)).toNat + (rdW (m.arr64 IW) (p + 3)).toNat ≤ iwTop m
  b4 : (rdW (m.arr64 IW) (p + 4)).toNat + (rdW (m.arr64 IW) (p + 5)).toNat ≤ iwTop m

/-- A `NestCtorNf` slice decoded below the tops. -/
def NfsB (m : Mem) (o l : Nat) (xs : List NestCtorNf) : Prop := DecB (fun m => decPL m (decNCN m) o l) m xs

theorem NfsB.grow {m m' : Mem} {o l : Nat} {xs : List NestCtorNf} (h : NfsB m o l xs) (hg : IWGrow m m') :
    NfsB m' o l xs := DecB.grow (OMono.decPL decNCN_mono o l) hg h

/-- A word read at `p + i`, with no wrap. -/
theorem pos2_rd_get {m : Mem} {p i v : Word} (h : (m.arr64 IW)[p.toNat + i.toNat]? = some v)
    (hb : p.toNat + i.toNat < 2 ^ 64) : rdW (m.arr64 IW) (p + i) = v := by
  have : (p + i).toNat = p.toNat + i.toNat := by rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt hb
  simp [rdW, this, h]

/-- The words of a decoded `NestState` record lie below the top. -/
theorem nsb_words {m : Mem} {p : Word} {NS : NestState} (h : NSB m p NS) (htop : iwTop m < 2 ^ 64) :
    p.toNat + 6 ≤ iwTop m ∧
    KsB m (rdW (m.arr64 IW) p).toNat (rdW (m.arr64 IW) (p + 1)).toNat NS.keys.toList ∧
    KsB m (rdW (m.arr64 IW) (p + 2)).toNat (rdW (m.arr64 IW) (p + 3)).toNat NS.active ∧
    NfsB m (rdW (m.arr64 IW) (p + 4)).toNat (rdW (m.arr64 IW) (p + 5)).toNat NS.ctorNfs.toList := by
  have h' : decNS (truncM m) p.toNat = some NS := h.dec
  simp only [decNS, decAt, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h'
  obtain ⟨ks, ⟨o0, ho0, l0, hl0, hks⟩, act, ⟨o2, ho2, l2, hl2, hact⟩, nfs, ⟨o4, ho4, l4, hl4, hnfs⟩, hNS⟩ := h'
  cases hNS
  obtain ⟨i0, e0⟩ := pos2_iwN_trunc ho0
  obtain ⟨i1, e1⟩ := pos2_iwN_trunc hl0
  obtain ⟨i2, e2⟩ := pos2_iwN_trunc ho2
  obtain ⟨i3, e3⟩ := pos2_iwN_trunc hl2
  obtain ⟨i4, e4⟩ := pos2_iwN_trunc ho4
  obtain ⟨i5, e5⟩ := pos2_iwN_trunc hl4
  have r0 : (rdW (m.arr64 IW) p).toNat = o0 := by
    have := rd_iwN (m := m) (p := p) (i := 0) (by simpa using e0) (by simp; omega); simpa using this
  rw [r0, rd_iwN (i := 1) (by simpa using e1) (by simp; omega), rd_iwN (i := 2) (by simpa using e2) (by simp; omega),
    rd_iwN (i := 3) (by simpa using e3) (by simp; omega), rd_iwN (i := 4) (by simpa using e4) (by simp; omega),
    rd_iwN (i := 5) (by simpa using e5) (by simp; omega)]
  exact ⟨by omega, by simpa [KsB, DecB] using hks, hact, by simpa [NfsB, DecB] using hnfs⟩

theorem NSB.grow {m m' : Mem} {p : Word} {NS : NestState} (h : NSB m p NS) (hg : IWGrow m m')
    (htop : iwTop m < 2 ^ 64) : NSB m' p NS := by
  have hp := (nsb_words h htop).1
  have e : ∀ i : Word, i.toNat < 6 → rdW (m'.arr64 IW) (p + i) = rdW (m.arr64 IW) (p + i) := by
    intro i hi
    have : (p + i).toNat = p.toNat + i.toNat := word_add_toNat (by omega)
    simp only [rdW, this]; rw [hg.2.2.1 _ (by omega)]
  have e0 : rdW (m'.arr64 IW) p = rdW (m.arr64 IW) p := by simpa using e 0 (by decide)
  refine ⟨DecB.grow (decNS_mono _) hg h.dec, ?_, ?_, ?_⟩
  · rw [e0, e 1 (by decide)]; have := h.b0; have := hg.1; omega
  · rw [e 2 (by decide), e 3 (by decide)]; have := h.b2; have := hg.1; omega
  · rw [e 4 (by decide), e 5 (by decide)]; have := h.b4; have := hg.1; omega

/-- **A fresh `NestState` record** (`rec6` of three slices decoded below the tops). -/
theorem nsb_rec6 {m' : Mem} {q kO kL aO aL nO nL : Word} {keys act : List NestKey} {nfs : List NestCtorNf}
    (hq : q.toNat + 6 ≤ iwTop m') (htop : iwTop m' < 2 ^ 64)
    (hget : ∀ j < [kO, kL, aO, aL, nO, nL].length, (m'.arr64 IW)[q.toNat + j]? = [kO, kL, aO, aL, nO, nL][j]?)
    (hk : KsB m' kO.toNat kL.toNat keys) (hkb : kO.toNat + kL.toNat ≤ iwTop m')
    (ha : KsB m' aO.toNat aL.toNat act) (hab : aO.toNat + aL.toNat ≤ iwTop m')
    (hn : NfsB m' nO.toNat nL.toNat nfs) (hnb : nO.toNat + nL.toNat ≤ iwTop m') :
    NSB m' q ⟨keys.toArray, act, nfs.toArray⟩ := by
  have g : ∀ j < 6, (iwA (truncM m'))[q.toNat + j]? = [kO, kL, aO, aL, nO, nL][j]? := fun j hj => by
    rw [truncM_iw_eq (by omega)]; exact hget j (by simpa using hj)
  have n0 : iwN (truncM m') q.toNat = some kO.toNat := by simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 0 (by omega))
  have n1 : iwN (truncM m') (q.toNat + 1) = some kL.toNat := by simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 1 (by omega))
  have n2 : iwN (truncM m') (q.toNat + 2) = some aO.toNat := by simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 2 (by omega))
  have n3 : iwN (truncM m') (q.toNat + 2 + 1) = some aL.toNat := by simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 3 (by omega))
  have n4 : iwN (truncM m') (q.toNat + 4) = some nO.toNat := by simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 4 (by omega))
  have n5 : iwN (truncM m') (q.toNat + 4 + 1) = some nL.toNat := by simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 5 (by omega))
  have rq : ∀ i : Word, i.toNat < 6 → rdW (m'.arr64 IW) (q + i) = [kO, kL, aO, aL, nO, nL][i.toNat]?.getD 0 := by
    intro i hi
    have : (q + i).toNat = q.toNat + i.toNat := word_add_toNat (by omega)
    simp only [rdW, this]; rw [hget _ (by simpa using hi)]
  have r0 : rdW (m'.arr64 IW) q = kO := by simpa using rq 0 (by decide)
  have r1 : rdW (m'.arr64 IW) (q + 1) = kL := by simpa using rq 1 (by decide)
  have r2 : rdW (m'.arr64 IW) (q + 2) = aO := by simpa using rq 2 (by decide)
  have r3 : rdW (m'.arr64 IW) (q + 3) = aL := by simpa using rq 3 (by decide)
  have r4 : rdW (m'.arr64 IW) (q + 4) = nO := by simpa using rq 4 (by decide)
  have r5 : rdW (m'.arr64 IW) (q + 5) = nL := by simpa using rq 5 (by decide)
  refine ⟨?_, by rw [r0, r1]; exact hkb, by rw [r2, r3]; exact hab, by rw [r4, r5]; exact hnb⟩
  show decNS (truncM m') q.toNat = _
  have hk' : decPL (truncM m') (decNK (truncM m')) kO.toNat kL.toNat = some keys := hk
  have ha' : decPL (truncM m') (decNK (truncM m')) aO.toNat aL.toNat = some act := ha
  have hn' : decPL (truncM m') (decNCN (truncM m')) nO.toNat nL.toNat = some nfs := hn
  simp only [decNS, decAt, n0, n1, n2, n3, n4, n5, hk', ha', hn', Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]

end L.Ind
