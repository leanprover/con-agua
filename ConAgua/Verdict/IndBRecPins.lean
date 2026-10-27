import ConAgua.Arena.RecCheckSpec24
import ConAgua.Arena.Verdict
import ConAgua.Checker.NoVerdictFns
import ConAgua.Verdict.IndBStream
import ConAgua.Arena.Checker

/-!
# Error refinement of `target_rec_pins` (lane `verdicts-b`, helper `ib`)

Every callee is `closedNV`; the five aborts are the twin's five `fail`s (`trpW_ok`'s tests).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

l_model trpE_spec (p : Prog) (hf : p.lookup "target_rec_pins" = some targetRecPins)
  fns [hf ↦ trpE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

/-! ## The twin's four failing tests -/

theorem fail_run' {γ : Type} (e : CheckError) (a : AState) :
    (ConRon.Arena.fail e : AM γ).run a = .error e := rfl

theorem except_error_bind' {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

theorem trp_fail1 (bs : BlockShape) (blk : List IConstantInfo) (a : AState)
    (h0 : ¬ ConRon.Arena.blockRecLpsOk bs = true) :
    ∃ s, (ConRon.Arena.targetRecPins bs blk).run a = .error (.invalid s) := by
  unfold ConRon.Arena.targetRecPins
  simp [StateT.run_bind, h0, fail_run', except_error_bind']

theorem trp_fail2 (bs : BlockShape) (blk : List IConstantInfo) (a a1 : AState)
    (h0 : ConRon.Arena.blockRecLpsOk bs = true)
    (h1 : (ConRon.Arena.blockRecNamesUnreserved bs.recs).run a = .ok (false, a1)) :
    ∃ s, (ConRon.Arena.targetRecPins bs blk).run a = .error (.invalid s) := by
  unfold ConRon.Arena.targetRecPins
  simp [StateT.run_bind, h0, h1, fail_run', except_error_bind']

theorem trp_fail3 (bs : BlockShape) (blk : List IConstantInfo) (a a1 a2 : AState)
    (h0 : ConRon.Arena.blockRecLpsOk bs = true)
    (h1 : (ConRon.Arena.blockRecNamesUnreserved bs.recs).run a = .ok (true, a1))
    (h2 : (ConRon.Arena.blockRecNameSetOk bs.members (bs.recs.filter fun rc => rc.tgt < bs.k)).run a1 =
      .ok (false, a2)) :
    ∃ s, (ConRon.Arena.targetRecPins bs blk).run a = .error (.invalid s) := by
  unfold ConRon.Arena.targetRecPins
  simp [StateT.run_bind, h0, h1, h2, fail_run', except_error_bind']

theorem trp_fail4 (bs : BlockShape) (blk : List IConstantInfo) (a a1 a2 a3 : AState)
    (h0 : ConRon.Arena.blockRecLpsOk bs = true)
    (h1 : (ConRon.Arena.blockRecNamesUnreserved bs.recs).run a = .ok (true, a1))
    (h2 : (ConRon.Arena.blockRecNameSetOk bs.members (bs.recs.filter fun rc => rc.tgt < bs.k)).run a1 =
      .ok (true, a2))
    (h3 : (namesTwin bs).run a2 = .ok (false, a3)) :
    ∃ s, (ConRon.Arena.targetRecPins bs blk).run a = .error (.invalid s) := by
  unfold namesTwin at h3
  simp only [StateT.run_bind] at h3
  cases hn : (rpN0 bs).run a2 with
  | error e => rw [hn] at h3; cases h3
  | ok x =>
  obtain ⟨n0, a2'⟩ := x
  rw [hn] at h3
  simp only [except_ok_bind] at h3
  cases hw : ((List.range (rpAux bs).length).mapM fun i => internNNode (.str n0 s!"rec_{i + 1}")).run a2' with
  | error e => rw [hw] at h3; cases h3
  | ok y =>
  obtain ⟨want, a2''⟩ := y
  rw [hw] at h3
  simp only [except_ok_bind] at h3
  unfold rpAux at hw
  unfold ConRon.Arena.targetRecPins
  rcases hm : bs.members with _ | ⟨ms0, rest⟩
  · simp only [rpN0, hm] at hn
    rw [hm] at h2
    have hw' : ((List.range (List.filter (fun rc => !decide (rc.tgt < bs.k)) bs.recs).length).mapM
        fun i => internNNode (.str n0 (toString "rec_" ++ (i + 1).repr))).run a2' = .ok (want, a2'') := hw
    by_cases hc : rpSetOk ((List.filter (fun rc => !decide (rc.tgt < bs.k)) bs.recs).map (·.cvR.name)) want = true
    · unfold rpAux at h3
      rw [ite_eq_left hc] at h3
      have hnd : nameNodup (bs.recs.map (·.cvR.name)) = false := by
        change Except.ok (nameNodup (bs.recs.map (·.cvR.name)), a2'') = Except.ok (false, a3) at h3
        simp only [Except.ok.injEq, Prod.mk.injEq] at h3
        exact h3.1
      unfold rpSetOk at hc
      simp [StateT.run_bind, hw', h0, h1, h2, hn]
      rw [ite_eq_left hc]
      simp [hnd, fail_run', except_error_bind']
    · unfold rpAux at h3
      unfold rpSetOk at hc
      simp [StateT.run_bind, hw', h0, h1, h2, hn]
      rw [ite_eq_right hc]
      simp [fail_run', except_error_bind']
  · simp only [rpN0, hm] at hn
    change Except.ok (ms0.cvT.name, a2) = Except.ok (n0, a2') at hn
    simp only [Except.ok.injEq, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    rw [hm] at h2
    have hw' : ((List.range (List.filter (fun rc => !decide (rc.tgt < bs.k)) bs.recs).length).mapM
        fun i => internNNode (.str ms0.cvT.name (toString "rec_" ++ (i + 1).repr))).run a2 = .ok (want, a2'') := hw
    by_cases hc : rpSetOk ((List.filter (fun rc => !decide (rc.tgt < bs.k)) bs.recs).map (·.cvR.name)) want = true
    · unfold rpAux at h3
      rw [ite_eq_left hc] at h3
      have hnd : nameNodup (bs.recs.map (·.cvR.name)) = false := by
        change Except.ok (nameNodup (bs.recs.map (·.cvR.name)), a2'') = Except.ok (false, a3) at h3
        simp only [Except.ok.injEq, Prod.mk.injEq] at h3
        exact h3.1
      unfold rpSetOk at hc
      simp [StateT.run_bind, hw', h0, h1, h2]
      rw [ite_eq_left hc]
      simp [hnd, fail_run', except_error_bind']
    · unfold rpAux at h3
      unfold rpSetOk at hc
      simp [StateT.run_bind, hw', h0, h1, h2]
      rw [ite_eq_right hc]
      simp [fail_run', except_error_bind']

theorem trp_fail5 (bs : BlockShape) (blk : List IConstantInfo) (a a1 a2 a3 : AState)
    (h0 : ConRon.Arena.blockRecLpsOk bs = true)
    (h1 : (ConRon.Arena.blockRecNamesUnreserved bs.recs).run a = .ok (true, a1))
    (h2 : (ConRon.Arena.blockRecNameSetOk bs.members (bs.recs.filter fun rc => rc.tgt < bs.k)).run a1 =
      .ok (true, a2))
    (h3 : (namesTwin bs).run a2 = .ok (true, a3)) (h4 : splitOk bs blk = false) :
    ∃ s, (ConRon.Arena.targetRecPins bs blk).run a = .error (.invalid s) := by
  unfold namesTwin at h3
  simp only [StateT.run_bind] at h3
  cases hn : (rpN0 bs).run a2 with
  | error e => rw [hn] at h3; cases h3
  | ok x =>
  obtain ⟨n0, a2'⟩ := x
  rw [hn] at h3
  simp only [except_ok_bind] at h3
  cases hw : ((List.range (rpAux bs).length).mapM fun i => internNNode (.str n0 s!"rec_{i + 1}")).run a2' with
  | error e => rw [hw] at h3; cases h3
  | ok y =>
  obtain ⟨want, a2''⟩ := y
  rw [hw] at h3
  simp only [except_ok_bind] at h3
  have hc : rpSetOk ((rpAux bs).map (·.cvR.name)) want = true := by
    refine Classical.byContradiction fun hc => ?_; rw [ite_eq_right hc] at h3; cases h3
  rw [ite_eq_left hc] at h3
  have hnd : nameNodup (bs.recs.map (·.cvR.name)) = true := by
    change Except.ok (nameNodup (bs.recs.map (·.cvR.name)), a2'') = Except.ok (true, a3) at h3
    simp only [Except.ok.injEq, Prod.mk.injEq] at h3
    exact h3.1
  unfold rpSetOk at hc
  unfold rpAux at hw hc
  unfold splitOk at h4
  unfold ConRon.Arena.targetRecPins
  rcases hm : bs.members with _ | ⟨ms0, rest⟩
  · simp only [rpN0, hm] at hn
    rw [hm] at h2
    have hw' : ((List.range (List.filter (fun rc => !decide (rc.tgt < bs.k)) bs.recs).length).mapM
        fun i => internNNode (.str n0 (toString "rec_" ++ (i + 1).repr))).run a2' = .ok (want, a2'') := hw
    simp [StateT.run_bind, hw', h0, h1, h2, hn]
    rw [ite_eq_left hc]; simp [hnd]
    rcases hb : ConRon.Arena.blockSplit blk with _ | ⟨cvTs, cs, rs⟩ <;> rw [hb] at h4
    · simp [fail_run']
    · simp at h4
      have hn' : ¬ ((cvTs.length = bs.k ∧ rs.length = bs.recs.length) ∧
          List.map (fun x => x.fst.name) bs.allCtors = List.map (fun x => x.fst.name) cs) :=
        fun ⟨⟨a1', b1'⟩, c1'⟩ => h4 a1' b1' c1'
      dsimp only
      rw [ite_eq_right hn']
      simp [fail_run']
  · simp only [rpN0, hm] at hn
    change Except.ok (ms0.cvT.name, a2) = Except.ok (n0, a2') at hn
    simp only [Except.ok.injEq, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    rw [hm] at h2
    have hw' : ((List.range (List.filter (fun rc => !decide (rc.tgt < bs.k)) bs.recs).length).mapM
        fun i => internNNode (.str ms0.cvT.name (toString "rec_" ++ (i + 1).repr))).run a2 = .ok (want, a2'') := hw
    simp [StateT.run_bind, hw', h0, h1, h2]
    rw [ite_eq_left hc]; simp [hnd]
    rcases hb : ConRon.Arena.blockSplit blk with _ | ⟨cvTs, cs, rs⟩ <;> rw [hb] at h4
    · simp [fail_run']
    · simp at h4
      have hn' : ¬ ((cvTs.length = bs.k ∧ rs.length = bs.recs.length) ∧
          List.map (fun x => x.fst.name) bs.allCtors = List.map (fun x => x.fst.name) cs) :=
        fun ⟨⟨a1', b1'⟩, c1'⟩ => h4 a1' b1' c1'
      dsimp only
      rw [ite_eq_right hn']
      simp [fail_run']

theorem claim_of_fail {α : Type} {T : AM α} {a : AState} {e : Err}
    (h : ∃ s, T.run a = .error (.invalid s)) (hc : e.cls = 1) : ErrClaim T a e := fun _ => by
  obtain ⟨s, hs⟩ := h
  exact ⟨_, hs, by rw [twinCls_invalid, hc]⟩

section sims
variable {p : Prog} (L : RpLook p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
  {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

include L hnv in
/-- **`target_rec_pins`' model error claim** (`trpW_ok`'s hypotheses). -/
theorem trpE_claim (N : Nat) {m : Mem} {a : AState} {pp bo bl : Word} {bs : BlockShape}
    {blk : List IConstantInfo}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs)
    (hblk : DecB (fun m => decEBlk dn m bo.toNat bl.toNat) m blk) :
    ∀ e, trpE p N m pp bo bl = .error e → ErrClaim (ConRon.Arena.targetRecPins bs blk) a e := by
  intro e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  obtain _ | N := N
  · simp only [trpE] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  have hT : ∀ m : Mem, iwTop m < 2 ^ 64 := fun m => (rdW (m.arr64 CTL) 200).toNat_lt
  have hq9 := rpShape9 hq
  obtain ⟨hmem, hrecs, -⟩ := decBS_some (show decBS (truncM m) pp.toNat = some bs from hq)
  obtain ⟨mo, ml, hmo, hml, hmsB, hmb⟩ := partsAt (fun q => decMS_mono q) hmem
  obtain ⟨ro, rl, hro, hrl, hrsB, hrb⟩ := partsAt (fun q => decRS_mono q) hrecs
  have hms : PSlR0 decMS bs.members mo ml m := ⟨hmsB, hmb⟩
  have hrs : PSlR0 decRS bs.recs ro rl m := ⟨hrsB, hrb⟩
  have hk : ml.toNat = bs.k := (decPL_length _ hmsB).symm
  have hrlen : rl.toNat = bs.recs.length := (decPL_length _ hrsB).symm
  have hi : ∀ i, i < 9 → (pp + UInt64.ofNat i).toNat = pp.toNat + i := fun i hi => by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (show i < UInt64.size by rw [UInt64_size_eq]; omega)]
    exact Nat.mod_eq_of_lt (by have := hT m; omega)
  have rd0 : ∀ m', IWGrow m m' → rdW (m'.arr64 IW) pp = mo := fun m' hg => by
    have := (trpRd hg (i := 0) (by simpa using hmo) (by simp)).1
    simpa using this
  have rd1 : ∀ m', IWGrow m m' → rdW (m'.arr64 IW) (pp + 1) = ml := fun m' hg => by
    have := (trpRd hg (i := 1) hml (hi 1 (by omega))).1
    simpa using this
  have rd2 : rdW (m.arr64 IW) (pp + 2) = ro := by
    have := (trpRd (IWGrow.refl m) (i := 2) hro (hi 2 (by omega))).1
    simpa using this
  have rd3 : rdW (m.arr64 IW) (pp + 3) = rl := by
    have := (trpRd (IWGrow.refl m) (i := 3) (by simpa [Nat.add_assoc] using hrl) (hi 3 (by omega))).1
    simpa using this
  rw [trpE.arm1, rd2, rd3] at he
  -- `block_rec_lps_ok`
  cases h1 : callE p N "block_rec_lps_ok" [pp] m with
  | error e1 =>
    rw [h1, trpE.k_block_rec_lps_ok.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (blockRecLpsOk_spec p L.alloc L.erCopy L.erToIw L.slEq L.copy L.cons
    L.lpsOne L.lpsGo L.lps L.lpsOk N ⟨m, Locals.init []⟩ pp) (callW_of_callE h1)
  subst hs1
  obtain ⟨hr1, hS1, hg1⟩ := lokW_stage hW1 hS hq
  by_cases hz1 : r1.headD 0 = 0
  · rw [h1, trpE.k_block_rec_lps_ok.abort1 p N pp bo bl ro rl r1 _ hz1] at he
    cases he
    have hc : ¬ ConRon.Arena.blockRecLpsOk bs = true := by
      intro hc; rw [hr1] at hz1; simp [hc] at hz1
    exact claim_of_fail (trp_fail1 bs blk a hc) (by decide)
  rw [h1, trpE.k_block_rec_lps_ok.arm1 p N pp bo bl ro rl r1 _ hz1] at he
  have hc0 : ConRon.Arena.blockRecLpsOk bs = true := by
    rw [hr1] at hz1
    exact Classical.byContradiction fun hc => by simp [hc] at hz1
  -- `block_rec_names_unreserved`
  cases h2 : callE p N "block_rec_names_unreserved" [ro, rl] s1.mem with
  | error e2 =>
    rw [h2, trpE.k_block_rec_names_unreserved.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, hok2, hr2, hS2, hg2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (blockRecNamesUnreserved_refines p L.unres L.rrn N _ a dn fe vis ro rl bs.recs hS1
      ((hrsB.grow (OMono.decPL (fun q => decRS_mono q) _ _) hg1).stab (OMono.decPL (fun q => decRS_mono q) _ _))
      (by
        rcases hrb with h0 | h0
        · rw [h0]; simpa using ro.toNat_lt
        · have := hT m; omega)) (callW_of_callE h2)
  subst hs2
  dsimp only at hok2 hr2 hS2 hg2
  have hrun1 := partsRunOfOk hok2
  by_cases hz2 : r2.headD 0 = 0
  · rw [h2, trpE.k_block_rec_names_unreserved.abort1 p N pp bo bl ro rl r2 _ hz2] at he
    cases he
    have hc : AM.res (ConRon.Arena.blockRecNamesUnreserved bs.recs) a = false := by
      rw [hr2] at hz2
      exact Classical.byContradiction fun hc => by simp [Bool.not_eq_false] at hc; simp [hc] at hz2
    rw [hc] at hrun1
    exact claim_of_fail (trp_fail2 bs blk a _ hc0 hrun1) (by decide)
  rw [h2, trpE.k_block_rec_names_unreserved.arm1 p N pp bo bl ro rl r2 _ hz2, rd1 _ (hg1.trans hg2)] at he
  have hc1 : AM.res (ConRon.Arena.blockRecNamesUnreserved bs.recs) a = true := by
    rw [hr2] at hz2
    exact Classical.byContradiction fun hc => by simp [hc] at hz2
  rw [hc1] at hrun1
  -- `block_rec_split_own_aux`
  cases h3 : callE p N "block_rec_split_own_aux" [ro, rl, ml] s2.mem with
  | error e3 =>
    rw [h3, trpE.k_block_rec_split_own_aux.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (soa_spec p L.toIndPartsProg L.soa N _ ro rl ml) (callW_of_callE h3)
  subst hs3
  dsimp only at hW3
  have hg12 := hg1.trans hg2
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := by
    cases N with
    | zero => simp [soaW] at hW3
    | succ n => exact ⟨n, rfl⟩
  obtain ⟨hS3, hg3, hown, haux⟩ := soaW_ok0 N' hW3 hS2 (hrs.grow (fun q => decRS_mono q) hg12)
  rw [hk] at hown haux
  rw [h3, trpE.k_block_rec_split_own_aux.arm1, rd0 _ (hg12.trans hg3)] at he
  -- `block_rec_name_set_ok`
  cases h4 : callE p (N' + 1) "block_rec_name_set_ok" [mo, ml, r3.headD 0, r3.tail.headD 0] s3.mem with
  | error e4 =>
    rw [h4, trpE.k_block_rec_name_set_ok.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  have hms3 := hms.grow (fun q => decMS_mono q) (hg12.trans hg3)
  obtain ⟨s4, hs4, -, hok4, hr4, hS4, hg4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (blockRecNameSetOk_refines p L.toIndPartsProg3 N' _ _ dn vis fe mo ml (r3.headD 0) (r3.tail.headD 0)
      bs.members _ hS3 hms3 hown) (callW_mono (callW_of_callE h4) (by omega))
  subst hs4
  dsimp only at hok4 hr4 hS4 hg4
  have hrun2 := partsRunOfOk hok4
  by_cases hz4 : r4.headD 0 = 0
  · rw [h4, trpE.k_block_rec_name_set_ok.abort1 p (N' + 1) pp bo bl ro rl ml _ _ _ r4 _ hz4] at he
    cases he
    have hc : AM.res (ConRon.Arena.blockRecNameSetOk bs.members
        (bs.recs.filter fun rc => decide (rc.tgt < bs.k))) (AM.st (ConRon.Arena.blockRecNamesUnreserved bs.recs) a)
        = false := by
      rw [hr4] at hz4
      exact Classical.byContradiction fun hc => by simp [Bool.not_eq_false] at hc; simp [hc] at hz4
    rw [hc] at hrun2
    exact claim_of_fail (trp_fail3 bs blk a _ _ hc0 hrun1 hrun2) (by decide)
  rw [h4, trpE.k_block_rec_name_set_ok.arm1 p (N' + 1) pp bo bl ro rl ml _ _ _ r4 _ hz4] at he
  have hc2 : AM.res (ConRon.Arena.blockRecNameSetOk bs.members
      (bs.recs.filter fun rc => decide (rc.tgt < bs.k))) (AM.st (ConRon.Arena.blockRecNamesUnreserved bs.recs) a)
      = true := by
    rw [hr4] at hz4
    exact Classical.byContradiction fun hc => by simp [hc] at hz4
  rw [hc2] at hrun2
  -- `target_rec_pins_names`
  cases h5 : callE p (N' + 1) "target_rec_pins_names"
      [mo, ml, ro, rl, r3.tail.tail.headD 0, r3.tail.tail.tail.headD 0] s4.mem with
  | error e5 =>
    rw [h5, trpE.k_target_rec_pins_names.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  obtain ⟨s5, hs5, -, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (tpn_spec p L.names (N' + 1) ⟨s4.mem, Locals.init []⟩ mo ml ro rl (r3.tail.tail.headD 0)
      (r3.tail.tail.tail.headD 0)) (callW_mono (callW_of_callE h5) (by omega))
  subst hs5
  dsimp only at hW5
  have hg14 := (hg12.trans hg3).trans hg4
  obtain ⟨b5, a5, hrun3, hr5, hS5, hg5⟩ := tpnW_sim p L N' s4.mem _ mo ml ro rl _ _ bs hS4
    (hms.grow (fun q => decMS_mono q) hg14) (hrs.grow (fun q => decRS_mono q) hg14)
    (haux.grow (fun q => decRS_mono q) hg4) r5 s5.mem hW5
  by_cases hz5 : r5.headD 0 = 0
  · rw [h5, trpE.k_target_rec_pins_names.abort1 p (N' + 1) pp bo bl rl ml r5 _ hz5] at he
    cases he
    have hb : b5 = false := by
      rw [hr5] at hz5
      exact Classical.byContradiction fun hc => by simp [hc] at hz5
    subst hb
    exact claim_of_fail (trp_fail4 bs blk a _ _ _ hc0 hrun1 hrun2 hrun3) (by decide)
  rw [h5, trpE.k_target_rec_pins_names.arm1 p (N' + 1) pp bo bl rl ml r5 _ hz5] at he
  have hb : b5 = true := by
    rw [hr5] at hz5
    exact Classical.byContradiction fun hc => by simp [hc] at hz5
  subst hb
  -- `target_rec_pins_split`
  cases h6 : callE p (N' + 1) "target_rec_pins_split" [pp, ml, rl, bo, bl] s5.mem with
  | error e6 =>
    rw [h6, trpE.k_target_rec_pins_split.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h6
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  obtain ⟨s6, hs6, -, hW6⟩ := triple_of_callW (s₀ := ⟨s5.mem, Locals.init []⟩)
    (tps_spec p L.psplit (N' + 1) _ pp ml rl bo bl) (callW_mono (callW_of_callE h6) (by omega))
  subst hs6
  dsimp only at hW6
  have hg15 := hg14.trans hg5
  obtain ⟨b6, a6, hrun4, hr6, rfl, hS6, hg6⟩ := tpsW_sim p L N' s5.mem a5 pp ml rl bo bl bs blk hS5
    (hq.grow (decBS_mono _) hg15) (hblk.grow (decEBlk_mono dn _ _) hg15) hk hrlen r6 s6.mem hW6
  by_cases hz6 : r6.headD 0 = 0
  · rw [h6, trpE.k_target_rec_pins_split.abort1 p r6 _ hz6] at he
    cases he
    have hb : b6 = false := by
      rw [hr6] at hz6
      exact Classical.byContradiction fun hc => by simp [hc] at hz6
    subst hb
    have h4' : splitOk bs blk = false := by
      change Except.ok (splitOk bs blk, _) = Except.ok (false, _) at hrun4
      simp only [Except.ok.injEq, Prod.mk.injEq] at hrun4; exact hrun4.1
    exact claim_of_fail (trp_fail5 bs blk a _ _ _ hc0 hrun1 hrun2 (by simpa using hrun3) h4') (by decide)
  rw [h6, trpE.k_target_rec_pins_split.arm1 p r6 _ hz6] at he
  cases he

include L hnv in
/-- **`target_rec_pins`' error claim** (every fuel). -/
theorem targetRecPins_claim (N : Nat) (s₀ : St) (a₀ : AState) (pp bo bl : Word) (bs : BlockShape)
    (blk : List IConstantInfo) (hS : StageR dn vis fe s₀.mem a₀)
    (hq : DecB (fun m => decBS m pp.toNat) s₀.mem bs)
    (hblk : DecB (fun m => decEBlk dn m bo.toNat bl.toNat) s₀.mem blk) :
    CoreSpecE p N "target_rec_pins" [pp, bo, bl] (ConRon.Arena.targetRecPins bs blk) s₀ a₀ :=
  CoreSpecE.of_runs fun e hc => by
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    exact trpE_claim L hnv N hS hq hblk e
      (triple_of_callE_err (trpE_spec p L.pins N s₀ pp bo bl) hc (Err.code_ne_of_cls hk0))

end sims


end L.Ind
