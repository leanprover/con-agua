module

public import ConAgua.Rom.PinSets

@[expose] public section

/-!
# The pin variant list across the declaration loop (lane `decls3`)

Lane `romload`'s `PinSetsR m pins` (the 40-word `EREC` records listed at `CTL[150]`, `CTL[151]`
hold the twin's variants) is a fact about `EREC` below its top and two `CTL` words. So it survives
every run that only grows the record pool (`IWGrow`, or `ArrExt` of `erecP` at an in-bounds top)
and leaves `CTL[150]`, `CTL[151]` alone: `PinSetsR.grow`, `PinSetsR.ext`. The declaration loop
carries it (`LoopR`'s `pinsets`), and the definition arm's `Nat.div`-family gate reads it.
-/

open ConRon.Arena

namespace L.Arena

open L.Ind
open L.Rom (PinSetsR PinSetR SliceR HdrR)

theorem toNat_add_small' (c : Word) (k : Nat) (h : c.toNat + k < 2 ^ 64) :
    (c + UInt64.ofNat k).toNat = c.toNat + k := by
  rw [UInt64.toNat_add]; simp; omega


/-- **The record pool only grew**: its top did not go down, and the words below the old top kept. -/
def RecGrow (m m' : Mem) : Prop :=
  erTop m ≤ erTop m' ∧ ∀ i < erTop m, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?

theorem IWGrow.recGrow {m m' : Mem} (h : IWGrow m m') : RecGrow m m' := ⟨h.er, h.erGet⟩

/-- `ArrExt` of the record pools in use, at an in-bounds top, is a `RecGrow`. -/
theorem RecGrow.of_ext {m m' : Mem} (hw : IWOK m) (hx : ArrExt (erecP m) (erecP m')) :
    RecGrow m m' := by
  have key : ∀ i < erTop m, i < erTop m' ∧ (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]? := by
    intro i hi
    have h40 : i < 2 ^ 40 := by have := hw.er; have := hw.erCap; omega
    have hsz : i < (m.arr64 EREC).size := by have := hw.er; omega
    have hd : i / 2 ^ 40 % 2 = 0 := by rw [Nat.div_eq_of_lt h40]
    have hm : erecP m i = some (m.arr64 EREC)[i] := by
      unfold erecP
      rw [ite_eq_left (by omega), ite_eq_left hd, Nat.mod_eq_of_lt h40, ite_eq_left (by exact hi)]
      simp [hsz]
    have hm' := hx _ _ hm
    unfold erecP at hm'
    rw [ite_eq_left (by omega), ite_eq_left hd, Nat.mod_eq_of_lt h40] at hm'
    split at hm'
    · exact ⟨by assumption, by rw [hm']; simp [hsz]⟩
    · cases hm'
  refine ⟨?_, fun i hi => (key i hi).2⟩
  rcases Nat.eq_zero_or_pos (erTop m) with h0 | hpos
  · omega
  · have := (key (erTop m - 1) (by omega)).1
    show erTop m ≤ erTop m'
    omega

theorem RecGrow.of_eq {m m' : Mem} (hE : m'.arr64 EREC = m.arr64 EREC)
    (h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129) : RecGrow m m' := by
  refine ⟨?_, fun i _ => by rw [hE]⟩
  simp only [erTop, h129]; exact Nat.le_refl _

theorem rdW_keep {a a' : Array Word} {T : Nat} (h : ∀ i < T, a'[i]? = a[i]?) {x : Word}
    (hx : x.toNat < T) : rdW a' x = rdW a x := by
  simp only [rdW, h _ hx]

theorem SliceR.grow {m m' : Mem} {o l : Word} {hs : List EIdx} (h : SliceR m o l hs)
    (hg : RecGrow m m') : SliceR m' o l hs := by
  obtain ⟨hb, hl, hw⟩ := h
  obtain ⟨het, hek⟩ := hg
  have het' : erTop m ≤ erTop m' := het
  have e0 : erTop m = erTop m := rfl
  refine ⟨by omega, hl, fun i hi => ?_⟩
  have hlt : (o + UInt64.ofNat i).toNat < erTop m := by
    have : (rdW (m.arr64 CTL) 129).toNat < 2 ^ 64 := UInt64.toNat_lt_size _
    have : erTop m < 2 ^ 64 := this
    rw [toNat_add_small' o i (by omega)]; omega
  rw [rdW_keep hek hlt]; exact hw i hi

theorem PinSetR.grow {m m' : Mem} {r : Word} {ip : INatOpPinSet} (h : PinSetR m r ip)
    (hg : RecGrow m m') : PinSetR m' r ip :=
  L.Rom.PinSetR.keep h ⟨hg.1, hg.2⟩

/-- **The variant list survives a run that grows the pools and leaves `CTL[150]`, `CTL[151]`.** -/
theorem PinSetsR.grow {m m' : Mem} {ips : List INatOpPinSet} (h : PinSetsR m ips)
    (hg : RecGrow m m') (h150 : rdW (m'.arr64 CTL) 150 = rdW (m.arr64 CTL) 150)
    (h151 : rdW (m'.arr64 CTL) 151 = rdW (m.arr64 CTL) 151) : PinSetsR m' ips := by
  obtain ⟨hc, hb, hr⟩ := h
  have het : erTop m ≤ erTop m' := hg.1
  have hek := hg.2
  have e0 : erTop m = erTop m := rfl
  have htop : erTop m < 2 ^ 64 := UInt64.toNat_lt_size _
  refine ⟨by rw [h151]; exact hc, by rw [h150]; omega, fun k hk => ?_⟩
  have ek : (rdW (m.arr64 CTL) 150 + UInt64.ofNat k).toNat = (rdW (m.arr64 CTL) 150).toNat + k :=
    toNat_add_small' _ k (by omega)
  rw [h150, rdW_keep hek (by rw [ek]; omega)]
  exact PinSetR.grow (hr k hk) hg

end L.Arena
