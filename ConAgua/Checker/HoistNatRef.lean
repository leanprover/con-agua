import ConAgua.Checker.HoistClosureL

/-!
# The hoist's `Nat` operation tests refine the twin's name lists (lane `front4`)

`nat_op_record` (`natDivModNames`/`natOpNames` into fresh `IW` slices, `slice_has` on each) against
`isNatOpRecord`'s test, and the call of `nat_op_deps` against `natOpDeps`: the twin succeeds in the
same state, and L's memory only grew the pool.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-! ## Helpers: allocations, slices -/

/-- The pin array survives an allocation frame. -/
theorem AFr.pins {m m' : Mem} (hf : AFr m m') : m'.arr64 PINS = m.arr64 PINS :=
  hf.1.1 PINS (by decide) (by decide)

theorem AFr.pinW_eq {m m' : Mem} (hf : AFr m m') (i : Nat) : pinW m' i = pinW m i := by
  simp only [pinW, hf.pins]

/-- **`alloc k` then `ws` written at the old top** is an allocation frame, with the words
readable at the old top. -/
theorem allocWr_ok {m : Mem} {ws : List Word} {k : Word} (hI : IWOK m) (hk : k.toNat = ws.length)
    (hroom : iwTop m + ws.length ≤ (m.arr64 IW).size) :
    AFr m (wrIW (allocMem m k) (rdW (m.arr64 CTL) 200) ws) ∧
      iwTop (wrIW (allocMem m k) (rdW (m.arr64 CTL) 200) ws) = iwTop m + ws.length ∧
      ∀ j < ws.length, rdW ((wrIW (allocMem m k) (rdW (m.arr64 CTL) 200) ws).arr64 IW)
        (rdW (m.arr64 CTL) 200 + UInt64.ofNat j) = ws[j]! := by
  have hrec := recPost_wr m ws k hk hI hroom
  have hfr : MemFrame [IW] [200] m (wrIW (allocMem m k) (rdW (m.arr64 CTL) 200) ws) :=
    (allocMem_frame m k).trans (wrIW_frame ws _ _)
  obtain ⟨_, hKeep, _, htop, _⟩ := hrec
  obtain ⟨hI1, hE1, hsz, hEs, hct⟩ := hI
  refine ⟨⟨hfr, hKeep.1, ?_⟩, htop, fun j hj => ?_⟩
  · have hE : (wrIW (allocMem m k) (rdW (m.arr64 CTL) 200) ws).arr64 EREC = m.arr64 EREC :=
      hfr.1 EREC (by decide) (by decide)
    have h129 := hfr.2.1 129 (by decide)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [htop, hfr.2.2.1 IW]; exact hroom
    · simp only [erTop, h129, hE]; exact hE1
    · rw [hfr.2.2.1 IW]; exact hsz
    · rw [hE]; exact hEs
    · rw [hfr.2.2.1 CTL]; exact hct
  · have := pw_rec ⟨hI1, hE1, hsz, hEs, hct⟩ (recPost_wr m ws k hk ⟨hI1, hE1, hsz, hEs, hct⟩ hroom) j hj
    simp only [pw] at this
    rw [this, getElem!_pos ws j hj]

theorem iwTop_lt' (m : Mem) : iwTop m < 2 ^ 64 := UInt64.toNat_lt _
theorem iwTop_lt_size (m : Mem) : iwTop m < UInt64.size := UInt64.toNat_lt _

/-- A read below the old top survives pool growth. -/
theorem rdW_grow {m m' : Mem} (hg : IWGrow m m') {x : Word} (hx : x.toNat < iwTop m) :
    rdW (m'.arr64 IW) x = rdW (m.arr64 IW) x := by
  simp only [rdW, hg.2.2.1 _ hx]

/-- **`slice_has`**: `w` is among the slice's words. -/
theorem sliceHas_ok (m : Mem) (o w : Word) : ∀ (ws : List Word) (n : Nat) (l j r : Word),
    l.toNat = j.toNat + ws.length →
    (∀ i < ws.length, rdW (m.arr64 IW) (o + UInt64.ofNat (j.toNat + i)) = ws[i]!) →
    hSliceHasW n m o l w j = some r → (r ≠ 0 ↔ w ∈ ws) := by
  intro ws
  induction ws with
  | nil =>
    intro n l j r hl _ h
    cases n with
    | zero => rw [hSliceHasW.eq_1] at h; cases h
    | succ n =>
      rw [hSliceHasW.arm1 _ _ _ _ _ _ (by rw [UInt64.le_iff_toNat_le]; simp at hl; omega)] at h
      cases h; simp
  | cons x xs ih =>
    intro n l j r hl hr h
    cases n with
    | zero => rw [hSliceHasW.eq_1] at h; cases h
    | succ n =>
      have hlj : ¬ l ≤ j := by rw [UInt64.le_iff_toNat_le]; simp at hl; omega
      have h0 := hr 0 (by simp)
      simp only [Nat.add_zero, UInt64.ofNat_toNat, getElem!_pos (x :: xs) 0 (by simp),
        List.getElem_cons_zero] at h0
      by_cases hx : rdW (m.arr64 IW) (o + j) = w
      · rw [hSliceHasW.arm2 _ _ _ _ _ _ hlj hx] at h
        cases h; simp [← hx, h0]
      · rw [hSliceHasW.arm3 _ _ _ _ _ _ hlj hx] at h
        have hj1 : (j + 1).toNat = j.toNat + 1 := by
          rw [UInt64.toNat_add, UInt64.toNat_one]; have := l.toNat_lt; simp at hl; omega
        have := ih n l (j + 1) r (by rw [hj1]; simp at hl; omega) (fun i hi => by
          have := hr (i + 1) (by simp; omega)
          rw [hj1, show j.toNat + 1 + i = j.toNat + (i + 1) by omega, this]
          simp [getElem!_pos xs i hi, getElem!_pos (x :: xs) (i + 1) (by simp; omega)]) h
        rw [this, List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (rfl | h); · exact absurd h0 hx
          exact h

/-- Membership of a decoded name in decoded words. -/
theorem contains_decI {w : Word} (hw : w.toNat < 2 ^ 32) :
    ∀ (ws : List Word), (∀ x ∈ ws, x.toNat < 2 ^ 32) →
      ((ws.map (decI : Word → NIdx)).contains (decI w) = true ↔ w ∈ ws)
  | [], _ => by simp
  | x :: xs, hl => by
    have ih := contains_decI hw xs (fun y hy => hl y (by simp [hy]))
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_true, ih, List.mem_cons]
    rw [decI_beq_word hw (hl x (by simp))]
    simp

/-- What a name-list call leaves: a fresh slice `[o, |ws|]` of the words `ws`. -/
def NSl (m m' : Mem) (r ws : List Word) : Prop :=
  AFr m m' ∧ r = [r.headD 0, UInt64.ofNat ws.length] ∧ iwTop m ≤ (r.headD 0).toNat ∧
    (r.headD 0).toNat + ws.length = iwTop m' ∧
    ∀ j < ws.length, rdW (m'.arr64 IW) (r.headD 0 + UInt64.ofNat j) = ws[j]!

/-- `nat_div_mod_names` as a fresh slice of its eight pins. -/
theorem natDivModNames_call {p : Prog} (hx : HoistExt p) :
    FRef p "nat_div_mod_names" [] (fun m => IWOK m)
      (fun m m' r => pinW m 0 ≠ 0 ∧ NSl m m' r [pinW m 22, pinW m 23, pinW m 24, pinW m 25,
        pinW m 26, pinW m 27, pinW m 28, pinW m 29]) := by
  refine FRef.of_succ fun k m r m' hI hc => ?_
  have hw := callW_model (M := fun mm => natDivModNamesW p k mm)
    (natDivModNames_specW p (hx.get "nat_div_mod_names") (hx.get "pin_at") k ·) hc
  unfold natDivModNamesW at hw
  by_cases h0 : pinW m 0 = 0
  · rw [if_pos h0] at hw; cases hw
  rw [if_neg h0] at hw
  cases hq : callW p k "iw_alloc" [8] m with
  | none => rw [hq] at hw; simp at hw
  | some qq =>
  obtain ⟨rq, mq⟩ := qq
  rw [hq, bW_some] at hw
  obtain ⟨hq0, hmq, _, hroom, _⟩ := iwAlloc_fref p (hx.get "iw_alloc") 8 k m rq mq hI hq
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  subst hmq
  rw [hq0]
  have echain : (((((((((allocMem m 8).set64 IW (rdW (m.arr64 CTL) 200) (pinW m 22)).set64 IW (rdW (m.arr64 CTL) 200 + 1) (pinW m 23)).set64 IW (rdW (m.arr64 CTL) 200 + 2) (pinW m 24)).set64 IW (rdW (m.arr64 CTL) 200 + 3) (pinW m 25)).set64 IW (rdW (m.arr64 CTL) 200 + 4) (pinW m 26)).set64 IW (rdW (m.arr64 CTL) 200 + 5) (pinW m 27)).set64 IW (rdW (m.arr64 CTL) 200 + 6) (pinW m 28)).set64 IW (rdW (m.arr64 CTL) 200 + 7) (pinW m 29)) = wrIW (allocMem m 8) (rdW (m.arr64 CTL) 200) [pinW m 22, pinW m 23, pinW m 24, pinW m 25, pinW m 26, pinW m 27, pinW m 28, pinW m 29] := by
    simp [wrIW, UInt64.add_assoc]
  rw [echain]
  obtain ⟨hA, htop, hrd⟩ := allocWr_ok hI (k := 8)
    (ws := [pinW m 22, pinW m 23, pinW m 24, pinW m 25, pinW m 26, pinW m 27, pinW m 28, pinW m 29])
    rfl (by simpa [iwTop] using hroom)
  exact ⟨h0, hA, rfl, Nat.le_refl _, by rw [htop]; rfl, hrd⟩

/-- `nat_op_names` as a fresh slice of its seven pins. -/
theorem natOpNames_call {p : Prog} (hx : HoistExt p) :
    FRef p "nat_op_names" [] (fun m => IWOK m)
      (fun m m' r => pinW m 0 ≠ 0 ∧ NSl m m' r [pinW m 15, pinW m 16, pinW m 17, pinW m 18,
        pinW m 19, pinW m 20, pinW m 21]) := by
  refine FRef.of_succ fun k m r m' hI hc => ?_
  have hw := callW_model (M := fun mm => natOpNamesW p k mm)
    (natOpNames_specW p (hx.get "nat_op_names") (hx.get "pin_at") k ·) hc
  unfold natOpNamesW at hw
  by_cases h0 : pinW m 0 = 0
  · rw [if_pos h0] at hw; cases hw
  rw [if_neg h0] at hw
  cases hq : callW p k "iw_alloc" [7] m with
  | none => rw [hq] at hw; simp at hw
  | some qq =>
  obtain ⟨rq, mq⟩ := qq
  rw [hq, bW_some] at hw
  obtain ⟨hq0, hmq, _, hroom, _⟩ := iwAlloc_fref p (hx.get "iw_alloc") 7 k m rq mq hI hq
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  subst hmq
  rw [hq0]
  have echain : ((((((((allocMem m 7).set64 IW (rdW (m.arr64 CTL) 200) (pinW m 15)).set64 IW (rdW (m.arr64 CTL) 200 + 1) (pinW m 16)).set64 IW (rdW (m.arr64 CTL) 200 + 2) (pinW m 17)).set64 IW (rdW (m.arr64 CTL) 200 + 3) (pinW m 18)).set64 IW (rdW (m.arr64 CTL) 200 + 4) (pinW m 19)).set64 IW (rdW (m.arr64 CTL) 200 + 5) (pinW m 20)).set64 IW (rdW (m.arr64 CTL) 200 + 6) (pinW m 21)) = wrIW (allocMem m 7) (rdW (m.arr64 CTL) 200) [pinW m 15, pinW m 16, pinW m 17, pinW m 18, pinW m 19, pinW m 20, pinW m 21] := by
    simp [wrIW, UInt64.add_assoc]
  rw [echain]
  obtain ⟨hA, htop, hrd⟩ := allocWr_ok hI (k := 7)
    (ws := [pinW m 15, pinW m 16, pinW m 17, pinW m 18, pinW m 19, pinW m 20, pinW m 21])
    rfl (by simpa [iwTop] using hroom)
  exact ⟨h0, hA, rfl, Nat.le_refl _, by rw [htop]; rfl, hrd⟩

/-- A slice survives later growth. -/
theorem NSl.grow {m m' m'' : Mem} {r ws : List Word} (h : NSl m m' r ws) (hg : IWGrow m' m'')
    (j : Nat) (hj : j < ws.length) :
    rdW (m''.arr64 IW) (r.headD 0 + UInt64.ofNat j) = ws[j]! := by
  obtain ⟨_, _, _, htop, hrd⟩ := h
  have hj64 : (UInt64.ofNat j).toNat = j :=
    UInt64.toNat_ofNat_of_lt' (by have := iwTop_lt_size m'; omega)
  have hadd : (r.headD 0 + UInt64.ofNat j).toNat = (r.headD 0).toNat + j := by
    rw [UInt64.toNat_add, hj64]; have := iwTop_lt' m'; omega
  rw [rdW_grow hg (by rw [hadd]; omega), hrd j hj]

/-- The name-list membership test over a slice. -/
theorem NSl.has {m m' m'' : Mem} {r ws : List Word} (h : NSl m m' r ws) (hg : IWGrow m' m'')
    {n : Nat} {w b : Word} (hb : hSliceHasW n m'' (r.headD 0) (r.tail.headD 0) w 0 = some b) :
    (b ≠ 0 ↔ w ∈ ws) := by
  have hr := h.2.1
  have hl : (r.tail.headD 0).toNat = ws.length := by
    rw [hr]; simp only [List.tail_cons, List.headD_cons]
    exact UInt64.toNat_ofNat_of_lt' (by have := iwTop_lt_size m'; have := h.2.2.2.1; omega)
  exact sliceHas_ok m'' _ w ws n _ 0 b (by rw [hl]; simp) (fun i hi => by
    simpa using h.grow hg i hi) hb

/-- The pin table survives an allocation. -/
theorem PinsFull.frameA {m m' : Mem} {ps : Pins} (h : PinsFull m ps) (hf : AFr m m') :
    PinsFull m' ps :=
  h.congr hf.pins

theorem pin_lt {m : Mem} {ps : Pins} (hF : PinsFull m ps) (i : Nat) (h1 : 1 ≤ i) (h2 : i ≤ 51) :
    (pinW m i).toNat < 2 ^ 32 := by
  have := hF.names_lt (i - 1) (by omega)
  rwa [show 1 + (i - 1) = i by omega] at this

/-- **`nat_op_record(w)`** is "the name `w` is in `natDivModNames` or `natOpNames`". -/
theorem natOpRec_ok (p : Prog) (hx : HoistExt p) (n : Nat) (m m₁ : Mem) (a : AState) (w op : Word)
    (hI : IWOK m) (hP : pinW m 0 ≠ 0 → PinsFull m a.pins) (hw : w.toNat < 2 ^ 32)
    (h : hNatOpRecW p n m w = some (op, m₁)) :
    PinsFull m a.pins ∧ ∃ L₁ L₂ : List NIdx, natDivModNames.run a = .ok (L₁, a) ∧
      natOpNames.run a = .ok (L₂, a) ∧
      (op ≠ 0 ↔ (L₁.contains (decI w) || L₂.contains (decI w)) = true) ∧ AFr m m₁ := by
  cases n with
  | zero => rw [hNatOpRecW.eq_1] at h; cases h
  | succ k =>
  rw [hNatOpRecW.arm1] at h
  cases h1 : callW p k "nat_div_mod_names" [] m with
  | none => rw [h1] at h; simp [hNatOpRecW.k4] at h
  | some q1 =>
  obtain ⟨r1, ma⟩ := q1
  rw [h1, hNatOpRecW.k4.arm1] at h
  obtain ⟨h0, hS1⟩ := natDivModNames_call hx k m r1 ma hI h1
  have hF := hP h0
  cases h2 : callW p k "nat_op_names" [] ma with
  | none => rw [h2] at h; simp [hNatOpRecW.k3] at h
  | some q2 =>
  obtain ⟨r2, mb⟩ := q2
  rw [h2, hNatOpRecW.k3.arm1] at h
  obtain ⟨_, hS2⟩ := natOpNames_call hx k ma r2 mb hS1.1.2.2 h2
  cases ha : hSliceHasW k mb (r1.headD 0) (r1.tail.headD 0) w 0 with
  | none => rw [ha] at h; simp [hNatOpRecW.k2] at h
  | some av =>
  rw [ha, hNatOpRecW.k2.arm1] at h
  cases hb : hSliceHasW k mb (r2.headD 0) (r2.tail.headD 0) w 0 with
  | none => rw [hb] at h; simp [hNatOpRecW.k1] at h
  | some bv =>
  rw [hb] at h
  have ha' := hS1.has hS2.1.2.1 ha
  have hb' := hS2.has (IWGrow.refl mb) hb
  simp only [hS1.1.pinW_eq] at hb'
  have hc1 := contains_decI hw [pinW m 22, pinW m 23, pinW m 24, pinW m 25, pinW m 26, pinW m 27,
    pinW m 28, pinW m 29] (by
      simp only [List.forall_mem_cons]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩ <;>
        exact pin_lt hF _ (by decide) (by decide))
  have hc2 := contains_decI hw [pinW m 15, pinW m 16, pinW m 17, pinW m 18, pinW m 19, pinW m 20,
    pinW m 21] (by
      simp only [List.forall_mem_cons]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩ <;>
        exact pin_lt hF _ (by decide) (by decide))
  simp only [List.map_cons, List.map_nil] at hc1 hc2
  have hop : op ≠ 0 ↔ (av ≠ 0 ∨ bv ≠ 0) := by
    by_cases hc : av ≠ 0 ∨ bv ≠ 0
    · rw [hNatOpRecW.k1.arm1 _ _ _ _ hc] at h; cases h; simp only [hc, iff_true]; decide
    · rw [hNatOpRecW.k1.arm2 _ _ _ _ hc] at h; cases h; simp only [hc, iff_false]; decide
  refine ⟨hF, _, _, natDivModNames_run hF, natOpNames_run hF, ?_, ?_⟩
  · rw [hop, Bool.or_eq_true, hc1, hc2, ha', hb']
  · have hm : m₁ = mb := by
      by_cases hc : av ≠ 0 ∨ bv ≠ 0
      · rw [hNatOpRecW.k1.arm1 _ _ _ _ hc] at h; cases h; rfl
      · rw [hNatOpRecW.k1.arm2 _ _ _ _ hc] at h; cases h; rfl
    subst hm
    exact hS1.1.trans hS2.1

/-- **The call of `nat_op_deps(w)`** is `natOpDeps (decI w)`: its result `(o, l)` is a slice of
the grounds, above the old pool top unless empty. -/
theorem natOpDepsCall_ok (p : Prog) (hx : HoistExt p) (n : Nat) (m m₂ : Mem) (a : AState) (w : Word)
    (r : List Word) (hI : IWOK m) (hP : PinsFull m a.pins) (hw : w.toNat < 2 ^ 32)
    (h : callW p n "nat_op_deps" [w] m = some (r, m₂)) :
    ∃ gs : List NIdx, (natOpDeps (decI w)).run a = .ok (gs, a) ∧ GrR m₂ (r.headD 0) 0 gs ∧
      (r.tail.headD 0).toNat = gs.length ∧
      (gs ≠ [] → iwTop m ≤ (r.headD 0).toNat ∧ (r.headD 0).toNat + gs.length ≤ iwTop m₂) ∧
      AFr m m₂ := by
  sorry

end L.Checker
