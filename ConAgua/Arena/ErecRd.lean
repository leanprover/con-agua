module

public import ConAgua.Arena.Env

@[expose] public section

/-!
# Readers and the words L reads

A record decoder reads a reader `R : Nat → Option Word`; L reads words by address. `RdOK R rd`
says that the word function `rd` is what L reads wherever `R` decodes a word (and that `R` decodes
nothing at or above `2^64`, so an address `q + c` does not wrap where `R` decodes at
`q.toNat + c.toNat`). The record pool's instance is `erRdOK`: `erecP` (both tiers) and L's tagged
read `EREC⦃a⦄` (`erRd`); an array's is `RdOK.arr`: `aread b` and `rdW b`.
-/

open ConRon.Arena

namespace L.Arena

/-- `rd` is the word L reads wherever the reader `R` decodes one; `R` decodes below `2^64`. -/
structure RdOK (R : Nat → Option Word) (rd : Word → Word) : Prop where
  rd : ∀ a v, R a.toNat = some v → rd a = v
  lt : ∀ i v, R i = some v → i < 2 ^ 64

theorem RdOK.off {R : Nat → Option Word} {rd : Word → Word} (h : RdOK R rd)
    {q c : Word} {i : Nat} {w : Word} (hb : R i = some w) (hi : q.toNat + c.toNat = i) :
    rd (q + c) = w := by
  have hlt := h.lt _ _ hb
  have : (q + c).toNat = i := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
  exact h.rd _ _ (by rw [this]; exact hb)

/-- The same in `irRdW`'s argument order: the offset `c` read as the number `k`. -/
theorem RdOK.at {R : Nat → Option Word} {rd : Word → Word} (h : RdOK R rd) {q : Word} {w : Word}
    (c : Word) {k : Nat} (hc : c.toNat = k) (hb : R (q.toNat + k) = some w) : rd (q + c) = w :=
  h.off hb (by rw [hc])

/-- The same at a numeral offset `k`. -/
theorem RdOK.offN {R : Nat → Option Word} {rd : Word → Word} (h : RdOK R rd)
    {q : Word} {k : Nat} {w : Word} (hb : R (q.toNat + k) = some w) (hk : k < 2 ^ 64) :
    rd (q + UInt64.ofNat k) = w :=
  h.off hb (by simp; omega)

/-- An array and its plain read. -/
theorem RdOK.arr (b : Array Word) (hsz : b.size ≤ 2 ^ 64) : RdOK (aread b) (rdW b) where
  rd a v h := by simp only [aread_apply] at h; simp [rdW, h]
  lt i v h := by
    simp only [aread_apply] at h
    have := (Array.getElem?_eq_some_iff.mp h).1; omega

theorem erRd_of {m : Mem} (a v : Word) (h : erecP m a.toNat = some v) : erRd m a = v := by
  obtain ⟨-, hget⟩ := erecP_tagRead h
  simp only [erRd, rdW, hget, Option.getD_some]

/-- The record pool and L's tagged read. -/
theorem erRdOK (m : Mem) : RdOK (erecP m) (erRd m) := ⟨erRd_of, fun _ _ hv => erecP_lt64 hv⟩

/-- Two memories with the same record arrays (both tiers) read the same records. -/
theorem erRd_congr {m m' : Mem} (h0 : m'.arr64 EREC = m.arr64 EREC)
    (h1 : m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC)) (x : Word) :
    rdW (m'.arr64 (tierA EREC (x >>> 40))) (x &&& 0xFFFFFFFFFF) = erRd m x := by
  simp only [erRd, tierA]; cases ((x >>> 40) &&& 1 != 0)
  · exact congrArg (rdW · _) h0
  · exact congrArg (rdW · _) h1

/-- **A frame that keeps both record tiers and the record tops** (`CTL[129]`, `CTL[130]`) keeps
the decoded records. -/
theorem erecP_frame {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (EREC : TieredArray) ∉ A) (hA1 : tier1 EREC ∉ A) (hC : (129 : Word) ∉ C)
    (hC1 : (130 : Word) ∉ C) : erecP m' = erecP m := by
  funext i
  simp only [erecP, erTop, erecTop1, hf.arr _ hA (by decide), hf.arr _ hA1 (by decide),
    hf.ctl _ hC, hf.ctl _ hC1]
  rfl

/-- The same frame keeps the tagged reads. -/
theorem erRd_frame {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (EREC : TieredArray) ∉ A) (hA1 : tier1 EREC ∉ A) : erRd m' = erRd m :=
  funext (erRd_congr (hf.arr _ hA (by decide)) (hf.arr _ hA1 (by decide)))

end L.Arena
