module

public import ConAgua.Arena.IotaFrameMotive
import ConAgua.Arena.RecLayout.CIDec
import ConAgua.Arena.ErecRd
import ConAgua.L.WordOff

@[expose] public section

/-!
# `iota_frame` refines `iotaFrame` (lane ronsync8)
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

/-- A stripper that answers `ok` answers the count it was asked for as its length word. -/
theorem stripGoW_len (tg k o : Word) : ∀ (f : Nat) (m m' : Mem) (n h : Word) (r : List Word),
    stripGoW tg k o f m n h = some (r, m') → r.headD 0 ≠ 0 → r.tail.tail.headD 0 = k := by
  intro f
  induction f with
  | zero => intro m m' n h r hs; simp [stripGoW] at hs
  | succ f ih =>
    intro m m' n h r hs hne
    by_cases hn : n < k
    · by_cases hg : tagW h ≠ tg
      · rw [stripGoW_tag tg k o f m n h hn hg] at hs
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hs); simp at hne
      · simp only [stripGoW, ite_eq_left hn, ite_eq_right hg] at hs
        repeat' split at hs
        all_goals first | (simp at hs; done) | exact ih _ _ _ _ _ hs hne
    · rw [stripGoW_ge tg k o f m n h hn] at hs
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hs); rfl

theorem stripF_len {tg : Word} {m m' : Mem} {k e : Word} {r : List Word}
    (hs : stripF tg m [k, e] = some (r, m')) (hne : r.headD 0 ≠ 0) : r.tail.tail.headD 0 = k :=
  stripGoW_len tg k _ _ m m' 0 e r hs hne

theorem headD_drop3 (r : List Word) : (r.drop 3).headD 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> rfl

/-- `iotaFrame`'s answer as `(ok, pre.off, pre.len, doms.off, doms.len, body, u)` (`pre.len` the
count `rP` asked for). -/
def decOF (rP : Word) (m : Mem) (r : List Word) : Option (List EIdx × List EIdx × EIdx × LIdx) → Prop
  | none => r.headD 0 = 0
  | some (pre, doms, body, u) => r.headD 0 = 1 ∧ r.tail.tail.headD 0 = rP ∧
      decRL (fun m => decHL m) 1 m r pre ∧
      decRL (fun m => decHL m) 3 m r doms ∧ HW (r.getD 5 0) ∧ decE (r.getD 5 0) = body ∧
      HW (r.getD 6 0) ∧ decI (r.getD 6 0) = u

/-- **`iota_frame` refines `iotaFrame`**. -/
@[refines ConRon.Arena.iotaFrame]
theorem iotaFrame_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (q mI rP : Word) (cv : IConstantVal) (hmI : mI.toNat < 2 ^ 32) (hrP : rP.toNat < 2 ^ 32) :
    RelW (fun m args => callW p n "iota_frame" args m) [q, mI, rP]
      (fun m a => StageR vis fe m a ∧ decCV (erecP m) q.toNat = some cv)
      (iotaFrame cv mI.toNat rP.toNat) (KeepPost vis fe (decOF rP)) := by
  intro m m' a r hc ⟨hS, hcv⟩
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iotaFrame_specW p P.iota_frame n _ q mI rP) hc
  obtain ⟨-, -, -, -, hty, hw⟩ := decCV_rd (erRdOK m) hcv
  rcases n with _ | n
  · simp [iotaFrameW] at hW
  simp only [iotaFrameW] at hW
  -- the rule prefix
  rcases h1 : callW p n "strip_pis" [rP, erRd m (q + CV.type)] m with _ | ⟨r1, m1⟩
  · rw [h1] at hW; simp [iotaFrameW.k_strip_pis] at hW
  rw [h1] at hW
  have hs1 := stripF_of_callW P.strip h1
  obtain ⟨x1, a1, hrun1, hS1, hg1, hd1⟩ := stripF_pis_ok vis fe rP _ hw m m1 a r1 hs1 hS
  unfold iotaFrame
  rw [hty, StateT.run_bind, hrun1, except_ok_bind]
  simp only [iotaFrameW.k_strip_pis] at hW
  rcases x1 with _ | ⟨pre, rest⟩
  · simp only [decOLE] at hd1
    rw [ite_eq_left hd1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨none, a1, rfl, hS1, hg1, rfl⟩
  obtain ⟨h11, hpre, hrest⟩ := hd1
  rw [ite_eq_right (by rw [h11]; decide)] at hW
  have hpl : r1.tail.tail.headD 0 = rP := stripF_len hs1 (by rw [h11]; decide)
  have hnI : (if mI < rP then (0 : Word) else mI - rP).toNat = mI.toNat - rP.toNat := by
    split
    · rename_i h; rw [UInt64.lt_iff_toNat_lt] at h; simp; omega
    · rename_i h; rw [UInt64.lt_iff_toNat_lt] at h
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
  have hj : iotaFrameW.j1 p n (if mI < rP then 0 else mI - rP) (r1.tail.headD 0) (r1.tail.tail.headD 0)
      (r1.tail.tail.tail.headD 0) m1 = some (r, s'.mem) := by
    split <;> rename_i h <;> simp only [h, ite_true, ite_false] at hW hnI ⊢ <;> exact hW
  generalize hnw : (if mI < rP then (0 : Word) else mI - rP) = nI at hj hnI
  clear hW
  dsimp only
  simp only [iotaFrameW.j1] at hj
  -- the index binders and the major
  have hn1 : (nI + 1).toNat = mI.toNat - rP.toNat + 1 := by
    rw [UInt64.toNat_add, hnI]; simp; omega
  simp only [decW0E, headD_drop3] at hrest
  rcases h2 : callW p n "strip_pis" [nI + 1, r1.tail.tail.tail.headD 0] m1 with _ | ⟨r2, m2⟩
  · rw [h2] at hj; simp [iotaFrameW.k_strip_pis_2] at hj
  rw [h2] at hj
  have hs2 := stripF_of_callW P.strip h2
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := stripF_pis_ok vis fe (nI + 1) _ hrest.1 m1 m2 a1 r2 hs2 hS1
  rw [hn1, hrest.2] at hrun2
  rw [StateT.run_bind, hrun2, except_ok_bind]
  simp only [iotaFrameW.k_strip_pis_2] at hj
  rcases x2 with _ | ⟨doms, body⟩
  · simp only [decOLE] at hd2
    rw [ite_eq_left hd2] at hj
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
    exact ⟨none, a2, rfl, hS2, hg1.trans hg2, rfl⟩
  obtain ⟨h21, hdoms, hbody⟩ := hd2
  rw [ite_eq_right (by rw [h21]; decide)] at hj
  simp only [decW0E, headD_drop3] at hbody
  -- the motive's level
  rcases h3 : callW p n "motive_level" [r1.tail.headD 0, r1.tail.tail.headD 0, nI,
      r2.tail.tail.tail.headD 0] m2 with _ | ⟨r3, m3⟩
  · rw [h3] at hj; simp [iotaFrameW.k_motive_level] at hj
  rw [h3] at hj
  have hp1 : decHL m1 (r1.tail.headD 0).toNat (r1.tail.tail.headD 0).toNat = some pre ∧
      (r1.tail.headD 0).toNat + (r1.tail.tail.headD 0).toNat ≤ iwTop m1 := by
    have := hpre; simp only [decRL, L.getD_one, L.getD_two, Nat.reduceAdd] at this; exact this
  have hpre2 := decHL_grow' hg2 hp1.2 hp1.1
  have htop2 : (r1.tail.headD 0).toNat + (r1.tail.tail.headD 0).toNat ≤ iwTop m2 :=
    Nat.le_trans hp1.2 hg2.iw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := motiveLevel_rel P n vis fe _ _ nI _ pre
    (by rw [hpl]; exact hrP) (by rw [hnI]; omega) hbody.1 m2 m3 a2 r3 h3 ⟨hS2, hpre2, htop2⟩
  rw [hnI, decE_eq, hbody.2] at hrun3
  rw [StateT.run_bind, hrun3, except_ok_bind]
  simp only [iotaFrameW.k_motive_level] at hj
  have hg := hg1.trans (hg2.trans hg3)
  rcases x3 with _ | u
  · simp only [decOL] at hd3
    rw [ite_eq_left hd3] at hj
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
    exact ⟨none, a3, rfl, hS3, hg, rfl⟩
  obtain ⟨h31, hu1, hu2⟩ := hd3
  rw [ite_eq_right (by rw [h31]; decide)] at hj
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
  refine ⟨_, a3, rfl, hS3, hg, rfl, hpl, ?_, ?_, hbody.1, hbody.2, hu1, hu2⟩
  · exact decRL_hl_grow (hg2.trans hg3) (by simpa [decRL] using hpre)
  · exact decRL_hl_grow hg3 (by simpa [decRL] using hdoms)

end L.Ind
