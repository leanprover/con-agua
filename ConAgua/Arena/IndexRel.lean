module

public import ConAgua.Arena.Env
public import ConRon.Arena.StreamIndex

@[expose] public section

/-!
# The stream index in L and a job's start

`IndexR m I` relates the stream index's rows (`EIX*`, `TIX*`), `FIRSTS` and the next counter
`CTL[128]` to the twin's `IStreamIndex` (what `build_index` builds). A job (`record_job`) bumps
the stamp above every own row (`OwnBelow`), so the own layer reads empty (`OwnEmpty`), and sets
the view words `CTL[134]`, `CTL[135]`: then `EnvR` holds at `vis = 0` of the twin's
`IStreamIndex.view` (`EnvR.ofIndex`).
-/

namespace L.Arena
open ConRon.Arena

section rel
/-! ### A job's start: the stream index's view and a fresh own layer -/

/-- **The stream index** (`IStreamIndex`, as `build_index` leaves it): the base rows are the
twin's `base.idx`/`base.tbls` (as `EnvR`'s `base`/`btbl`), `FIRSTS` holds `firsts`, `CTL[128]` is
`next`. -/
structure IndexR (m : Mem) (I : IStreamIndex) : Prop where
  base : ∀ n : NIdx,
    (I.base.idx[n]?).map (fun e => (e.1, some e.2)) =
      (if (baseRow m n.word.toUInt64).1 = 0 then none
       else some ((baseRow m n.word.toUInt64).1.toNat - 1,
         decCI (erecP m) (baseRow m n.word.toUInt64).2.toNat))
  btbl : ∀ n : NIdx,
    (I.base.tbls[n]?).map (fun e => (e.1, some e.2)) =
      (if (baseTbl m n.word.toUInt64).1 = 0 then none
       else some ((baseTbl m n.word.toUInt64).1.toNat - 1,
         decTbl (erecP m) (baseTbl m n.word.toUInt64).2.toNat))
  firsts : ∀ i (h : i < I.firsts.size), (rdW (m.arr64 FIRSTS) (UInt64.ofNat i)).toNat = I.firsts[i]
  firstsSize : I.firsts.size ≤ (m.arr64 FIRSTS).size
  next : (rdW (m.arr64 CTL) 128).toNat = I.next

/-- Every own row and own table row carries a stamp at most the current one (what lets a stamp
bump empty the own layer without clearing it). -/
def OwnBelow (m : Mem) : Prop :=
  ∀ w, rowTag w ≤ 2 → ((ownRow m w).1 >>> 32).toNat ≤ (stampW m).toNat ∧
    (rdN (m.arr64 (otxArrT w)) (rowIx w)).toNat ≤ (stampW m).toNat

/-- The own layer is empty. -/
def OwnEmpty (m : Mem) : Prop := ∀ w, (ownRaw m w).1 = 0 ∧ ownTbl m w = 0

/-- **A stamp above every row's empties the own layer.** -/
theorem OwnEmpty.of_below {m : Mem} (h : OwnBelow m) (hlt : ∀ w, rowTag w ≤ 2 →
    ((ownRow m w).1 >>> 32).toNat < (stampW m).toNat ∧
      (rdN (m.arr64 (otxArrT w)) (rowIx w)).toNat < (stampW m).toNat) : OwnEmpty m := by
  intro w
  by_cases ht : rowTag w ≤ 2
  · obtain ⟨a, b⟩ := hlt w ht
    refine ⟨?_, ?_⟩
    · simp only [ownRaw, ht, true_and]
      rw [if_neg (fun e => by rw [e] at a; omega)]
    · rw [ownTbl_eq]; simp only [ht, true_and]
      rw [if_neg (fun e => by rw [e] at b; omega)]
  · exact ⟨by simp [ownRaw, ht], by simp [ownTbl, ht]⟩

/-- **The environment at a job's start**: the stream index at the view of position `k`, an empty
own layer, `vis = 0`. -/
theorem EnvR.ofIndex {m : Mem} {I : IStreamIndex} {k : Nat} (hI : IndexR m I) (hO : OwnEmpty m)
    (hs : (stampW m).toNat < 2 ^ 32) (h134 : (rdW (m.arr64 CTL) 134).toNat = I.firsts.getD k I.next)
    (h135 : (rdW (m.arr64 CTL) 135).toNat = k) : EnvR m 0 (I.view k) := by
  refine ⟨fun n => ?_, fun n hn => absurd (hO _).1 hn, fun n hn => absurd (hO _).1 hn,
    fun n _ hn => absurd (hO _).1 hn, fun n => ?_, fun n hn => absurd (hO _).2 hn, ?_, ?_,
    fun n => hI.base n, fun n => hI.btbl n, hs⟩
  · simp [IStreamIndex.view, ownFind]
  · simp [IStreamIndex.view, (hO _).2]
  · simp only [IStreamIndex.view]; rw [h134]
  · simp only [IStreamIndex.view]; rw [h135]

end rel

end L.Arena
