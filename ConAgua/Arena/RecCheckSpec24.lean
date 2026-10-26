import ConAgua.Arena.RecCheckSpec23

/-!
# `RecCheck`: `targetRecPins` itself (lane `indproofs3`, helper `rec2`)

The L code aborts where the twin fails; when it returns, each callee passed, and the twin's run
passes the same tests (`trp_twin`). Hypotheses: the stage relation, the shape and the block decoded
below the tops.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The twin, when every test passes -/

/-- **The twin's `targetRecPins` passes** when its tests do. -/
theorem trp_twin (bs : BlockShape) (blk : List IConstantInfo) (a a1 a2 a3 : AState)
    (h0 : ConRon.Arena.blockRecLpsOk bs = true)
    (h1 : (ConRon.Arena.blockRecNamesUnreserved bs.recs).run a = .ok (true, a1))
    (h2 : (ConRon.Arena.blockRecNameSetOk bs.members (bs.recs.filter fun rc => rc.tgt < bs.k)).run a1 =
      .ok (true, a2))
    (h3 : (namesTwin bs).run a2 = .ok (true, a3)) (h4 : splitOk bs blk = true) :
    (ConRon.Arena.targetRecPins bs blk).run a = .ok ((), a3) := by
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
  have hnd : nameNodup (bs.recs.map (·.cvR.name)) = true ∧ a2'' = a3 := by
    change Except.ok (nameNodup (bs.recs.map (·.cvR.name)), a2'') = Except.ok (true, a3) at h3
    simp only [Except.ok.injEq, Prod.mk.injEq] at h3
    exact ⟨h3.1, h3.2⟩
  obtain ⟨hnd, rfl⟩ := hnd
  unfold rpSetOk at hc
  unfold rpAux at hw hc
  unfold splitOk at h4
  unfold ConRon.Arena.targetRecPins
  rcases hm : bs.members with _ | ⟨ms0, rest⟩
  · simp only [rpN0, hm] at hn
    rcases hb : ConRon.Arena.blockSplit blk with _ | ⟨cvTs, cs, rs⟩ <;> rw [hb] at h4
    · cases h4
    rw [hm] at h2
    have hw' : ((List.range (List.filter (fun rc => !decide (rc.tgt < bs.k)) bs.recs).length).mapM
        fun i => internNNode (.str n0 (toString "rec_" ++ (i + 1).repr))).run a2' = .ok (want, a2'') := hw
    simp [StateT.run_bind, hw', h0, h1, h2, hn, hnd, h4, except_ok_bind]
    rw [ite_eq_left hc]; simp; rfl
  · simp only [rpN0, hm] at hn
    change Except.ok (ms0.cvT.name, a2) = Except.ok (n0, a2') at hn
    simp only [Except.ok.injEq, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    rcases hb : ConRon.Arena.blockSplit blk with _ | ⟨cvTs, cs, rs⟩ <;> rw [hb] at h4
    · cases h4
    rw [hm] at h2
    have hw' : ((List.range (List.filter (fun rc => !decide (rc.tgt < bs.k)) bs.recs).length).mapM
        fun i => internNNode (.str ms0.cvT.name (toString "rec_" ++ (i + 1).repr))).run a2 = .ok (want, a2'') := hw
    simp [StateT.run_bind, hw', h0, h1, h2, hnd, h4, except_ok_bind]
    rw [ite_eq_left hc]; simp; rfl

/-! ## The model -/

def trpK6 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else some ([], m)
def trpK5 (p : Prog) (n : Nat) (pp bo bl k recl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else trpK6 (callW p n "target_rec_pins_split" [pp, k, recl, bo, bl] m)
def trpK4 (p : Prog) (n : Nat) (pp bo bl reco recl k mo : Word) (rs : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else trpK5 p n pp bo bl k recl (callW p n "target_rec_pins_names"
      [mo, k, reco, recl, rs.tail.tail.headD 0, rs.tail.tail.tail.headD 0] m)
def trpK3 (p : Prog) (n : Nat) (pp bo bl reco recl k : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rs, m) => trpK4 p n pp bo bl reco recl k (rdW (m.arr64 IW) pp) rs
      (callW p n "block_rec_name_set_ok" [rdW (m.arr64 IW) pp, k, rs.headD 0, rs.tail.headD 0] m)
def trpK2 (p : Prog) (n : Nat) (pp bo bl reco recl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else trpK3 p n pp bo bl reco recl (rdW (m.arr64 IW) (pp + 1))
      (callW p n "block_rec_split_own_aux" [reco, recl, rdW (m.arr64 IW) (pp + 1)] m)
def trpK1 (p : Prog) (n : Nat) (pp bo bl reco recl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else trpK2 p n pp bo bl reco recl (callW p n "block_rec_names_unreserved" [reco, recl] m)

/-- **The model of `target_rec_pins(p, block.off, block.len)`** (body fuel `n`). -/
def trpW (p : Prog) (n : Nat) (m : Mem) (pp bo bl : Word) : Option (List Word × Mem) :=
  trpK1 p n pp bo bl (rdW (m.arr64 IW) (pp + 2)) (rdW (m.arr64 IW) (pp + 3))
    (callW p n "block_rec_lps_ok" [pp] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (pp bo bl reco recl k mo : Word) (r rs : List Word)
theorem trpK6_zero (h : r.headD 0 = 0) : trpK6 (some (r, m)) = none := by simp only [trpK6]; rw [ite_eq_left h]
theorem trpK6_ok (h : ¬ r.headD 0 = 0) : trpK6 (some (r, m)) = some ([], m) := by
  simp only [trpK6]; rw [ite_eq_right h]
theorem trpK5_zero (h : r.headD 0 = 0) : trpK5 p n pp bo bl k recl (some (r, m)) = none := by
  simp only [trpK5]; rw [ite_eq_left h]
theorem trpK5_ok (h : ¬ r.headD 0 = 0) : trpK5 p n pp bo bl k recl (some (r, m)) =
    trpK6 (callW p n "target_rec_pins_split" [pp, k, recl, bo, bl] m) := by simp only [trpK5]; rw [ite_eq_right h]
theorem trpK4_zero (h : r.headD 0 = 0) : trpK4 p n pp bo bl reco recl k mo rs (some (r, m)) = none := by
  simp only [trpK4]; rw [ite_eq_left h]
theorem trpK4_ok (h : ¬ r.headD 0 = 0) : trpK4 p n pp bo bl reco recl k mo rs (some (r, m)) =
    trpK5 p n pp bo bl k recl (callW p n "target_rec_pins_names"
      [mo, k, reco, recl, rs.tail.tail.headD 0, rs.tail.tail.tail.headD 0] m) := by
  simp only [trpK4]; rw [ite_eq_right h]
theorem trpK3_some : trpK3 p n pp bo bl reco recl k (some (rs, m)) =
    trpK4 p n pp bo bl reco recl k (rdW (m.arr64 IW) pp) rs
      (callW p n "block_rec_name_set_ok" [rdW (m.arr64 IW) pp, k, rs.headD 0, rs.tail.headD 0] m) := rfl
theorem trpK2_zero (h : r.headD 0 = 0) : trpK2 p n pp bo bl reco recl (some (r, m)) = none := by
  simp only [trpK2]; rw [ite_eq_left h]
theorem trpK2_ok (h : ¬ r.headD 0 = 0) : trpK2 p n pp bo bl reco recl (some (r, m)) =
    trpK3 p n pp bo bl reco recl (rdW (m.arr64 IW) (pp + 1))
      (callW p n "block_rec_split_own_aux" [reco, recl, rdW (m.arr64 IW) (pp + 1)] m) := by
  simp only [trpK2]; rw [ite_eq_right h]
theorem trpK1_zero (h : r.headD 0 = 0) : trpK1 p n pp bo bl reco recl (some (r, m)) = none := by
  simp only [trpK1]; rw [ite_eq_left h]
theorem trpK1_ok (h : ¬ r.headD 0 = 0) : trpK1 p n pp bo bl reco recl (some (r, m)) =
    trpK2 p n pp bo bl reco recl (callW p n "block_rec_names_unreserved" [reco, recl] m) := by
  simp only [trpK1]; rw [ite_eq_right h]
end arms
attribute [ind_grind] trpK6_zero trpK6_ok trpK5_zero trpK5_ok trpK4_zero trpK4_ok trpK3_some trpK2_zero
  trpK2_ok trpK1_zero trpK1_ok

set_option maxHeartbeats 1600000 in
theorem trp_spec (p : Prog) (hp : p.lookup "target_rec_pins" = some targetRecPins) (n : Nat)
    (s₀ : St) (pp bo bl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "target_rec_pins" [pp, bo, bl]
    ⦃fun r s' => LocEq s' s₀ ∧ trpW p n s₀.mem pp bo bl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, targetRecPins]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "block_rec_lps_ok", callW_spec p n "block_rec_names_unreserved",
      callW_spec p n "block_rec_split_own_aux", callW_spec p n "block_rec_name_set_ok",
      callW_spec p n "target_rec_pins_names", callW_spec p n "target_rec_pins_split"] <;>
    finish (gen := 40) (instances := 20000) [trpW, rdW_eq]

/-! ## The relational lemma -/

/-- `block_rec_split_own_aux` at a slice below the top unless empty. -/
theorem soaW_ok0 {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat)
    {m m' : Mem} {a : AState} {reco recl k : Word} {recs : List RecShape} {r : List Word}
    (h : soaW (n + 1) m reco recl k = some (r, m')) (hS : StageR dn vis fe m a)
    (hrs : PSlR0 decRS recs reco recl m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      PSlR decRS (recs.filter fun rc => decide (rc.tgt < k.toNat)) (r.headD 0) (r.tail.headD 0) m' ∧
      PSlR decRS (recs.filter fun rc => !decide (rc.tgt < k.toNat)) (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) m' := by
  by_cases hl : recl = 0
  · rw [soaW.arm1 n m reco recl k hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [hrs.nil hl]
    exact ⟨hS, IWGrow.refl _, PSlR.nil _ _, PSlR.nil _ _⟩
  · exact soaW_ok (n + 1) m m' a reco recl k recs r h hS (hrs.pslr hl)

/-- A word of a decoded record below the top, in any memory grown into. -/
theorem trpRd {m m' : Mem} (hg : IWGrow m m') {pp : Word} {i v : Nat} (h : iwN (truncM m) (pp.toNat + i) = some v)
    (hi : (pp + UInt64.ofNat i).toNat = pp.toNat + i) :
    rdW (m'.arr64 IW) (pp + UInt64.ofNat i) = UInt64.ofNat v ∧ v < 2 ^ 64 := by
  obtain ⟨hw, hvb, hlt⟩ := partsIwRd h hi
  exact ⟨by rw [partsRdIW_grow hg (by rw [hi]; exact hlt), hw], hvb⟩

/-- **`target_rec_pins`' model refines `targetRecPins`.** -/
theorem trpW_ok (p : Prog) (L : RpLook p) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} (m m' : Mem) (a : AState) (pp bo bl : Word) (r : List Word) (bs : BlockShape)
    (blk : List IConstantInfo) (e : trpW p (n + 2) m pp bo bl = some (r, m'))
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs)
    (hblk : DecB (fun m => decEBlk dn m bo.toNat bl.toNat) m blk) :
    ∃ a', (ConRon.Arena.targetRecPins bs blk).run a = .ok ((), a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
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
  unfold trpW at e
  rw [rd2, rd3] at e
  -- `block_rec_lps_ok`
  rcases h1 : callW p (n + 2) "block_rec_lps_ok" [pp] m with _ | ⟨r1, m1⟩ <;> rw [h1] at e
  · cases e
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockRecLpsOk_spec p L.alloc L.erCopy L.erToIw L.slEq L.copy L.cons L.lpsOne L.lpsGo L.lps L.lpsOk
      (n + 2) _ pp) h1
  obtain ⟨hr1, hS1, hg1⟩ := lokW_stage hW1 hS hq
  have hc0 : ConRon.Arena.blockRecLpsOk bs = true := by
    refine Classical.byContradiction fun hc => ?_; rw [trpK1_zero _ _ _ _ _ _ _ _ _ (by rw [hr1]; simp [hc])] at e; cases e
  rw [trpK1_ok _ _ _ _ _ _ _ _ _ (by rw [hr1, hc0]; decide)] at e
  -- `block_rec_names_unreserved`
  rcases h2 : callW p (n + 2) "block_rec_names_unreserved" [ro, rl] s1.mem with _ | ⟨r2, m2⟩ <;> rw [h2] at e
  · cases e
  obtain ⟨s2, rfl, -, hok2, hr2, hS2, hg2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (blockRecNamesUnreserved_refines p L.unres L.rrn (n + 2) _ a dn fe vis ro rl bs.recs hS1
      ((hrsB.grow (OMono.decPL (fun q => decRS_mono q) _ _) hg1).stab (OMono.decPL (fun q => decRS_mono q) _ _))
      (by
        rcases hrb with h0 | h0
        · rw [h0]; simpa using ro.toNat_lt
        · have := hT m; omega)) h2
  dsimp only at hok2 hr2 hS2 hg2
  have hc1 : AM.res (ConRon.Arena.blockRecNamesUnreserved bs.recs) a = true := by
    refine Classical.byContradiction fun hc => ?_; rw [trpK2_zero _ _ _ _ _ _ _ _ _ (by rw [hr2]; simp [hc])] at e; cases e
  rw [trpK2_ok _ _ _ _ _ _ _ _ _ (by rw [hr2, hc1]; decide), rd1 _ (hg1.trans hg2)] at e
  have hrun1 := partsRunOfOk hok2
  rw [hc1] at hrun1
  -- `block_rec_split_own_aux`
  rcases h3 : callW p (n + 2) "block_rec_split_own_aux" [ro, rl, ml] s2.mem with _ | ⟨r3, m3⟩ <;> simp only [h3, trpK3, reduceCtorEq] at e
  obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (soa_spec p L.toIndPartsProg L.soa (n + 2) _ ro rl ml) h3
  dsimp only at hW3
  have hg12 := hg1.trans hg2
  obtain ⟨hS3, hg3, hown, haux⟩ := soaW_ok0 (n + 1) hW3 hS2 (hrs.grow (fun q => decRS_mono q) hg12)
  rw [hk] at hown haux
  rw [rd0 _ (hg12.trans hg3)] at e
  -- `block_rec_name_set_ok`
  rcases h4 : callW p (n + 2) "block_rec_name_set_ok" [mo, ml, r3.headD 0, r3.tail.headD 0] s3.mem with _ | ⟨r4, m4⟩ <;> rw [h4] at e
  · cases e
  have hms3 := hms.grow (fun q => decMS_mono q) (hg12.trans hg3)
  obtain ⟨s4, rfl, -, hok4, hr4, hS4, hg4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (blockRecNameSetOk_refines p L.toIndPartsProg3 n _ _ dn vis fe mo ml (r3.headD 0) (r3.tail.headD 0)
      bs.members _ hS3 hms3 hown) h4
  dsimp only at hok4 hr4 hS4 hg4
  have hc2 : AM.res (ConRon.Arena.blockRecNameSetOk bs.members
      (bs.recs.filter fun rc => decide (rc.tgt < bs.k))) (AM.st (ConRon.Arena.blockRecNamesUnreserved bs.recs) a)
      = true := by
    refine Classical.byContradiction fun hc => ?_; rw [trpK4_zero _ _ _ _ _ _ _ _ _ _ _ _ (by rw [hr4]; simp [hc])] at e; cases e
  rw [trpK4_ok _ _ _ _ _ _ _ _ _ _ _ _ (by rw [hr4, hc2]; decide)] at e
  have hrun2 := partsRunOfOk hok4
  rw [hc2] at hrun2
  -- `target_rec_pins_names`
  rcases h5 : callW p (n + 2) "target_rec_pins_names"
      [mo, ml, ro, rl, r3.tail.tail.headD 0, r3.tail.tail.tail.headD 0] s4.mem with _ | ⟨r5, m5⟩ <;> rw [h5] at e
  · cases e
  obtain ⟨s5, rfl, -, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (tpn_spec p L.names (n + 1) _ mo ml ro rl _ _) h5
  dsimp only at hW5
  have hg14 := (hg12.trans hg3).trans hg4
  obtain ⟨b5, a5, hrun3, hr5, hS5, hg5⟩ := tpnW_sim p L n s4.mem _ mo ml ro rl _ _ bs hS4
    (hms.grow (fun q => decMS_mono q) hg14) (hrs.grow (fun q => decRS_mono q) hg14)
    (haux.grow (fun q => decRS_mono q) hg4) r5 s5.mem hW5
  have hc3 : b5 = true := by
    refine Classical.byContradiction fun hc => ?_; rw [trpK5_zero _ _ _ _ _ _ _ _ _ (by rw [hr5]; simp [hc])] at e; cases e
  subst hc3
  rw [trpK5_ok _ _ _ _ _ _ _ _ _ (by rw [hr5]; decide)] at e
  -- `target_rec_pins_split`
  rcases h6 : callW p (n + 2) "target_rec_pins_split" [pp, ml, rl, bo, bl] s5.mem with _ | ⟨r6, m6⟩ <;> rw [h6] at e
  · cases e
  obtain ⟨s6, rfl, -, hW6⟩ := triple_of_callW (s₀ := ⟨s5.mem, Locals.init []⟩)
    (tps_spec p L.psplit (n + 1) _ pp ml rl bo bl) h6
  dsimp only at hW6
  have hg15 := hg14.trans hg5
  obtain ⟨b6, a6, hrun4, hr6, rfl, hS6, hg6⟩ := tpsW_sim p L n s5.mem a5 pp ml rl bo bl bs blk hS5
    (hq.grow (decBS_mono _) hg15) (hblk.grow (decEBlk_mono dn _ _) hg15) hk hrlen r6 s6.mem hW6
  have hc4 : b6 = true := by
    refine Classical.byContradiction fun hc => ?_; rw [trpK6_zero _ _ (by rw [hr6]; simp [hc])] at e; cases e
  subst hc4
  rw [trpK6_ok _ _ (by rw [hr6]; decide)] at e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
  have h4' : splitOk bs blk = true := by
    change Except.ok (splitOk bs blk, _) = Except.ok (true, _) at hrun4
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrun4; exact hrun4.1
  exact ⟨_, trp_twin bs blk a _ _ _ hc0 hrun1 hrun2 hrun3 h4', hS6, hg15.trans hg6⟩

/-- **`target_rec_pins` refines `targetRecPins`** (through the stubs `name_rec`, `name_rec_i`,
`intern_nanon`, the reserved-name tests): the shape and the block decoded below the tops, nothing
else. -/
@[refines ConRon.Arena.targetRecPins]
theorem targetRecPins_refines (p : Prog) (L : RpLook p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (pp bo bl : Word) (bs : BlockShape)
    (blk : List IConstantInfo) (hS : StageR dn vis fe s₀.mem a₀)
    (hq : DecB (fun m => decBS m pp.toNat) s₀.mem bs)
    (hblk : DecB (fun m => decEBlk dn m bo.toNat bl.toNat) s₀.mem blk) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 3)) "target_rec_pins" [pp, bo, bl]
    ⦃fun _r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetRecPins bs blk) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetRecPins bs blk) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (trp_spec p L.pins (n + 2) s₀ pp bo bl) ?_
  rintro _r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hS', hg⟩ := trpW_ok p L n s₀.mem s'.mem a₀ pp bo bl _r bs blk hm hS hq hblk
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg⟩

end L.Ind
