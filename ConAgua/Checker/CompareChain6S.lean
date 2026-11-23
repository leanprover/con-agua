module

public import ConAgua.Checker.CompareChain6
public import ConAgua.Checker.CompareTwinC

@[expose] public section

/-!
# Mode `6`'s stage relation (lane compare)

After the move (`index_to_solution`) the stream index is empty, and the challenge's steps up to its
index build (`cmp_restore`, `prepare_prelude`, `side_records`, `solution_of`) run at the builder's
environment of the empty index (`bEnv {} P 0 0`), as the flat run's do before its build.

* `EnvR.rebaseG`: `EnvR` across the move (to the empty index's environment) and across the
  record pool's growth (the mates).
* `StageR.frameD`: the stage relation across a frame that avoids every array and control word the
  relation reads.
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend

/-! ## The environment across the move and the record pool's growth -/

/-- **`EnvR` at a new base layer, the record pool extended** (`EnvR.rebase` with other writes):
a frame that writes only index rows, the record pool, arrays `EnvR` does not read, `CTL[128]`,
`CTL[129]` and control words `EnvR` does not read, whose record pool extends and whose index rows
are `I`'s. -/
theorem _root_.L.Arena.EnvR.rebaseG {m m' : Mem} {vis : Word} {fe : IFEnv} {I : IStreamIndex} {A : List TieredArray}
    {C : List Word} (h : EnvR m vis fe) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b ∈ IdxA ∨ b = EREC ∨ b ∉ envArrs) (hC : ∀ x ∈ C, x = 128 ∨ x = 129 ∨ x ∉ envCtl)
    (hx : ArrExt (erecP m) (erecP m')) (hI : IndexR m' I) :
    EnvR m' vis (fe.rebase I.base) := by
  have hc : ∀ x ∈ envCtl, x ≠ 128 → x ≠ 129 → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x :=
    fun x hx h1 h2 => hf.ctl x (fun hm => by rcases hC x hm with e | e | e <;> contradiction)
  have ha : ∀ b ∈ envArrs, b ∉ IdxA → b ≠ EREC → m'.arr64 b = m.arr64 b := fun b hb h1 h2 =>
    hf.arr b (fun hm => by rcases hA b hm with e | e | e <;> contradiction)
      (fun e => by subst e; revert hb; decide)
  have hs : stampW m' = stampW m := hc 133 (by decide) (by decide) (by decide)
  have o1 : ∀ g t, tierA (oixArr g) t ∈ envArrs ∧ tierA (oixArr g) t ∉ IdxA ∧ tierA (oixArr g) t ≠ EREC :=
    fun g t => by
      unfold tierA oixArr; generalize (t &&& 1 != 0) = b
      cases b <;> split <;> (try split) <;> decide
  have o2 : ∀ g t, tierA (otxArr g) t ∈ envArrs ∧ tierA (otxArr g) t ∉ IdxA ∧ tierA (otxArr g) t ≠ EREC :=
    fun g t => by
      unfold tierA otxArr; generalize (t &&& 1 != 0) = b
      cases b <;> split <;> (try split) <;> decide
  have hor : ∀ w, ownRow m' w = ownRow m w := fun w => by
    simp only [ownRow, ha _ (o1 _ _).1 (o1 _ _).2.1 (o1 _ _).2.2]
  have hraw : ∀ w, ownRaw m' w = ownRaw m w := fun w => by simp only [ownRaw, hor, hs]
  have hot : ∀ w, ownTbl m' w = ownTbl m w := fun w => by
    simp only [ownTbl, ha _ (o2 _ _).1 (o2 _ _).2.1 (o2 _ _).2.2, hs]
  refine ⟨fun n => ?_, fun n hn => ?_, fun n hn => ?_, fun n n' hn hq => ?_, fun n => ?_,
    fun n hn => ?_, ?_, ?_, fun n => hI.base n, fun n => hI.btbl n, by rw [hs]; exact h.stamp,
    fun w hw => by
      rw [hor, hs, ha _ (o2 _ _).1 (o2 _ _).2.1 (o2 _ _).2.2]; exact h.ownBelow w hw, ?_, ?_, ?_⟩
  · show fe.idx[n]? = _
    rw [h.own n]
    simp only [ownFind, hraw]
    split
    · rename_i hc'
      obtain ⟨ci, hci⟩ := h.own_dec n hc'.1
      rw [hci, hx.decCI hci]
    · rfl
  · rw [hraw] at hn ⊢
    obtain ⟨ci, hci⟩ := h.own_dec n hn
    exact ⟨ci, hx.decCI hci⟩
  · rw [hraw] at hn ⊢; exact h.fresh n hn
  · rw [hraw, hraw] at hq; rw [hraw] at hn; exact h.uniq n n' hn hq
  · show fe.tbls[n]? = _
    rw [h.otbl n, hot]
    split
    · rfl
    · rename_i hc'
      obtain ⟨t, ht⟩ := h.otbl_dec n hc'
      rw [ht, hx.decTbl ht]
  · rw [hot] at hn ⊢
    obtain ⟨t, ht⟩ := h.otbl_dec n hn
    exact ⟨t, hx.decTbl ht⟩
  · rw [hc 134 (by decide) (by decide) (by decide)]; exact h.below
  · rw [hc 135 (by decide) (by decide) (by decide)]; exact h.belowRec
  · rw [hc 160 (by decide) (by decide) (by decide)]; exact h.natLit
  · rw [hc 161 (by decide) (by decide) (by decide)]; exact h.strLit
  · rw [litWords_congr (fun i hi => hc _ (by revert hi; revert i; decide) (by revert hi; revert i; decide)
      (by revert hi; revert i; decide))]
    exact h.lits

/-- **The stage relation across a frame of high arrays and control words** that writes, of what
`EnvR` reads, only the index rows, the record pool and `CTL[128]`, `CTL[129]` (`EnvR.rebaseG`), the
work pool's relation given after it. -/
theorem _root_.L.Ind.StageR.frameG {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} {I : IStreamIndex}
    {A : List TieredArray} {C : List Word} (hS : L.Ind.StageR vis fe m a) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, InHigh b ∧ (b.arr < 96 ∨ 129 ≤ b.arr) ∧ (b ∈ IdxA ∨ b = EREC ∨ b ∉ envArrs))
    (hC : ∀ x ∈ C, 64 ≤ x.toNat ∧ (x.toNat < 96 ∨ 128 ≤ x.toNat) ∧ (x = 128 ∨ x = 129 ∨ x ∉ envCtl))
    (hx : ArrExt (erecP m) (erecP m')) (hI : IndexR m' I) (hiw : L.Ind.IWOK m') :
    L.Ind.StageR vis (fe.rebase I.base) m' a := by
  refine ⟨⟨⟨?_, ?_⟩, hS.check.core.frame (fun b hb => by have := hA b hb; simp only [InHigh] at this; omega)
      (fun x hx => by have := hC x hx; omega) hf,
    hS.check.pins.frame (fun b hb => by have := hA b hb; simp only [InHigh] at this; omega) hf,
    hS.check.env.rebaseG hf (fun b hb => (hA b hb).2.2) (fun x hx => (hC x hx).2.2) hx hI,
    hS.check.mode.frame hf (fun h => by have := hC _ h; simp at this) (fun h => by have := hC _ h; simp at this)⟩,
    hiw⟩
  · exact ArenaR.frame_ext A C (fun b hb => (hA b hb).1) (fun x hx => (hC x hx).1) m m' hf a
      hS.check.arena.base
  · exact DerR.frameM A C m m' hf (fun b hb => by have := hA b hb; simp only [InHigh] at this; omega) a
      hS.check.arena.der

/-! ## After the move -/

theorem envArrs_le : ∀ b ∈ envArrs, b.arr ≤ 148 := by decide

theorem mem_idxA {b : TieredArray} (h0 : b.hi = false) (h1 : 129 ≤ b.arr) (h2 : b.arr ≤ 134) : b ∈ IdxA := by
  obtain ⟨n, hi⟩ := b
  simp only at h0 h1 h2; subst h0
  have : n = 129 ∨ n = 130 ∨ n = 131 ∨ n = 132 ∨ n = 133 ∨ n = 134 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem moveA_facts : ∀ b ∈ moveA, b.hi = false ∧ ((129 ≤ b.arr ∧ b.arr ≤ 134) ∨ (210 ≤ b.arr ∧ b.arr ≤ 215)) := by
  decide

/-- A high array past `EnvR`'s, for `StageR.frameG`. -/
theorem frameG_hi {b : TieredArray} (h0 : b.hi = false) (h1 : 149 ≤ b.arr) :
    InHigh b ∧ (b.arr < 96 ∨ 129 ≤ b.arr) ∧ (b ∈ IdxA ∨ b = EREC ∨ b ∉ envArrs) :=
  ⟨⟨h0, by omega⟩, .inr (by omega), .inr (.inr fun h => by have := envArrs_le b h; omega)⟩

/-- An index row, for `StageR.frameG`. -/
theorem frameG_idx {b : TieredArray} (h0 : b.hi = false) (h1 : 129 ≤ b.arr) (h2 : b.arr ≤ 134) :
    InHigh b ∧ (b.arr < 96 ∨ 129 ≤ b.arr) ∧ (b ∈ IdxA ∨ b = EREC ∨ b ∉ envArrs) :=
  ⟨⟨h0, by omega⟩, .inr h1, .inl (mem_idxA h0 h1 h2)⟩


/-- The builder's environment of the empty index at the pins `P`. -/
abbrev fe0 (P : Pins) : IFEnv := bEnv ({} : IStreamIndex).base P 0 0

/-- **The stage relation after the move**, at the empty index's environment: from the solution's
index build (`FoldOn`), a memory that agrees but in `OUT` (`OutEq`), and the move's frame. -/
theorem stage_moved {b pb : ByteArray} {sz : TieredArray → Nat} {ds : Array IDeclaration}
    {ipins : List INatOpPinSet} {sE : AState} {I : IStreamIndex} {sF : AState} {m₇ m m0 m1 : Mem}
    (hF : FoldOn b pb sz ds ipins sE I sF m₇ m) (hO : OutEq m m0) (hI : IndexR m1 {})
    (hf : MemFrame moveA moveC m0 m1) : L.Ind.StageR 0 (fe0 sF.pins) m1 sF := by
  have hf' : MemFrame (([OUT] : List TieredArray) ++ moveA) moveC m m1 :=
    (hO.memFrame.mono (by simp) (by simp)).trans (hf.mono (fun b hb => List.mem_append_right _ hb) (by simp))
  have hiw : L.Ind.IWOK m1 := IWOK.frame hf' (by decide) (by decide) (by decide) (by decide)
    hF.build.stage.iw (by decide) (by decide)
  have hx : erecP m1 = erecP m :=
    erecP_congr' (hf'.arr _ (by decide) (by decide)) (hf'.arr _ (by decide) (by decide))
      (hf'.ctl _ (by decide)) (hf'.ctl _ (by decide))
  refine hF.build.stage.frameG hf' (fun b hb => ?_) (fun x hx => by
      simp only [moveC, SNEXTC, SCNTC, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide) (by rw [hx]; exact fun _ _ h => h) hI hiw
  rcases List.mem_append.mp hb with h | h
  · simp only [List.mem_singleton] at h; subst h; exact frameG_hi (by decide) (by decide)
  · obtain ⟨h0, h1 | h1⟩ := moveA_facts b h
    · exact frameG_idx h0 h1.1 h1.2
    · exact frameG_hi h0 (by omega)

end L.Checker
