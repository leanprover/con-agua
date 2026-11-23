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
theorem EnvR.rebaseG {m m' : Mem} {vis : Word} {fe : IFEnv} {I : IStreamIndex} {A : List TieredArray}
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

end L.Checker
